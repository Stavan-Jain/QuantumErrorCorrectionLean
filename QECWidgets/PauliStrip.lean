/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import QECWidgets.PauliEval
import QECWidgets.Style
import ProofWidgets.Component.HtmlDisplay
import ProofWidgets.Presentation.Expr

/-!
# Pauli support strips for the infoview

Renders concrete Pauli objects as colored per-qubit strips:

- `#pauli_strip e` — display `e` below the command, where `e` is an
  `NQubitPauliGroupElement n`, an `NQubitPauliOperator n`, an `Anticommute p q`
  proposition, or an equality between Pauli terms (commutation goals). For the
  proposition shapes the widget shows both operands aligned, rings the qubit
  positions where the single-qubit factors anticommute (resp. differ), and
  states the parity verdict — the visual form of
  `commutes_iff_even_anticommutes`.
- The `Pauli strip` expression presenter: shift-click any such expression in the
  goal panel with `ProofWidgets.SelectionPanel` open (or put
  `ProofWidgets.GoalTypePanel` on a goal of one of the proposition shapes) to
  see the same rendering during a proof.

Card names are interactive (`exprName`): hover for types, click to jump to the
definition. Look and feel comes from `QECWidgets.Style`.
-/

namespace QECWidgets

open Lean Server Meta ProofWidgets Quantum

/-- Display letter for a (possibly unresolved) single-qubit factor. -/
def opLetter : Option PauliOperator → String
  | some .I => "·"
  | some .X => "X"
  | some .Y => "Y"
  | some .Z => "Z"
  | none => "?"

/-- Long name used in cell tooltips. -/
def opName : Option PauliOperator → String
  | some .I => "I"
  | some .X => "X"
  | some .Y => "Y"
  | some .Z => "Z"
  | none => "unresolved"

/-- Cell class per factor (colors and hover states live in the stylesheet). -/
def opClass : Option PauliOperator → String
  | some .I => "qecw-i"
  | some .X => "qecw-x"
  | some .Y => "qecw-y"
  | some .Z => "qecw-z"
  | none => "qecw-stuck"

/-- One qubit cell: the factor letter, a hover tooltip naming the qubit, and
(when `marked`) a purple ring flagging the position. -/
def cellHtml (idx : Nat) (marked : Bool) (o : Option PauliOperator) : Html :=
  cls "span" (s!"qecw-cell {opClass o}" ++ if marked then " qecw-mark" else "")
    #[("title", Json.str s!"qubit {idx}: {opName o}")]
    #[.text (opLetter o)]

/-- Cells per display row; longer strips wrap into indexed rows. -/
def stripRowSize : Nat := 32

/-- Muted label showing the first qubit index of a row. Only rendered when a
strip wraps into several rows — on a single-row strip it would be a lone `0`. -/
private def rowLabel (start : Nat) : Html :=
  cls "span" "qecw-rowlabel" #[] #[.text (toString start)]

/-- Leading phase glyph for a strip: `none` for `+1` (not drawn, as in
handwritten notation), `i` / `−` / `−i` otherwise, `?` when the phase did not
reduce. -/
def phaseGlyph : Option Nat → Option String
  | some 0 => none
  | some 1 => some "i"
  | some 2 => some "−"
  | some 3 => some "−i"
  | some k => some s!"i^{k}"
  | none => some "?"

/-- A phase glyph rendered as a fixed-width leading cell (fixed width so two
strips shown together stay column-aligned even when only one has a glyph). -/
def phaseGlyphHtml (g : String) : Html :=
  cls "span" "qecw-glyph" #[("title", Json.str "global phase")] #[.text g]

/-- The strip proper: rows of qubit cells. Row index labels appear only when the
strip wraps; `marks` (when nonempty) rings the flagged positions; `leading`
(when present) is drawn before the first row's cells. -/
def stripHtml (v : PauliView) (marks : Array Bool := #[])
    (leading : Option Html := none) : Html := Id.run do
  let numRows := (v.numQubits + stripRowSize - 1) / stripRowSize
  let mut rows : Array Html := #[]
  for r in [0:numRows] do
    let start := r * stripRowSize
    let stop := min (start + stripRowSize) v.numQubits
    let mut cells : Array Html := #[]
    if numRows > 1 then
      cells := cells.push (rowLabel start)
    if r == 0 then
      if let some g := leading then
        cells := cells.push g
    for j in [start:stop] do
      cells := cells.push (cellHtml j (marks.getD j false) (v.ops.getD j none))
    rows := rows.push (cls "div" "qecw-strip" #[] cells)
  return el "div" #[] rows

/-- Pretty-print the phase exponent as `+1`, `+i`, `−1`, `−i`. -/
def phaseStr : Option Nat → String
  | some 0 => "+1"
  | some 1 => "+i"
  | some 2 => "−1"
  | some 3 => "−i"
  | some k => s!"i^{k}"
  | none => "?"

/-- Standard header facts for a view: weight, phase (only when the strip wraps
and cannot carry the leading glyph), unresolved count. -/
private def viewFacts (v : PauliView) (showPhase : Bool) : Array Html := Id.run do
  let mut fs : Array Html := #[headerFact s!"wt {v.weight}" "number of non-identity qubits"]
  if showPhase && v.numQubits > stripRowSize then
    fs := fs.push (headerFact (phaseStr v.phasePower) "global phase")
  if v.numStuck > 0 then
    fs := fs.push (headerFact s!"? {v.numStuck}" "cells that did not reduce" (some warnColor))
  return fs

/-- Single-term view: header plus strip. The phase is drawn as a leading glyph
on single-row strips, and as a header fact on wrapped ones (a glyph would
misalign the first row there). -/
def stripCard (name : Html) (v : PauliView) (showPhase : Bool) : Html :=
  let leading :=
    if showPhase && v.numQubits ≤ stripRowSize then (phaseGlyph v.phasePower).map phaseGlyphHtml
    else none
  card #[headerHtml name (viewFacts v showPhase), stripHtml v #[] leading]

/-- Compact text form of a strip: one letter per qubit (`·` for identity, `?`
for unresolved), with a space every 8 qubits. -/
def PauliView.letters (v : PauliView) : String := Id.run do
  let mut s := ""
  for i in [0:v.numQubits] do
    if i > 0 && i % 8 == 0 then s := s.push ' '
    s := s ++ opLetter (v.ops.getD i none)
  return s

/-- Plain-text summary of a single term view (logged by `#pauli_strip`). -/
def termSummary (v : PauliView) (showPhase : Bool) : String :=
  let ph := if showPhase then s!", phase {phaseStr v.phasePower}" else ""
  let stuck := if v.numStuck > 0 then s!", {v.numStuck} unresolved" else ""
  s!"{v.letters}   (n = {v.numQubits}, weight {v.weight}{ph}{stuck})"

/-- Ring marks for the positions where the two sides' factors anticommute. -/
def marksAnticommute (vp vq : PauliView) : Array Bool :=
  (Array.range (max vp.numQubits vq.numQubits)).map fun i =>
    match vp.ops.getD i none, vq.ops.getD i none with
    | some a, some b => anticommutesBool a b
    | _, _ => false

/-- Ring marks for the positions where the two sides' factors differ. -/
def marksDiffer (vp vq : PauliView) : Array Bool :=
  (Array.range (max vp.numQubits vq.numQubits)).map fun i =>
    match vp.ops.getD i none, vq.ops.getD i none with
    | some a, some b => a != b
    | _, _ => false

/-- Count of `true` marks. -/
private def countMarks (marks : Array Bool) : Nat :=
  marks.foldl (fun acc b => if b then acc + 1 else acc) 0

/-- Two aligned strips with shared marks and a verdict line; `accent` colors the
card's state bar. Phase glyphs are drawn on both strips whenever either side has
one, so the columns stay aligned; wrapped strips carry the phase in their header
facts instead. -/
def dualCard (nameP nameQ : Html) (vp vq : PauliView) (marks : Array Bool)
    (verdict : Html) (showPhase : Bool) (accent : Option String := none) : Html :=
  let glyphs : Option Html × Option Html :=
    if showPhase && vp.numQubits ≤ stripRowSize then
      match phaseGlyph vp.phasePower, phaseGlyph vq.phasePower with
      | none, none => (none, none)
      | gp, gq => (some (phaseGlyphHtml (gp.getD "")), some (phaseGlyphHtml (gq.getD "")))
    else (none, none)
  card (accent := accent) #[
    headerHtml nameP (viewFacts vp showPhase),
    stripHtml vp marks glyphs.1,
    styled "div" (json% { height: "6px" }) #[],
    headerHtml nameQ (viewFacts vq showPhase),
    stripHtml vq marks glyphs.2,
    verdict]

/-- `"3 crossings"` / `"1 crossing"` — singular/plural helper for verdicts. -/
private def countNoun (c : Nat) (single : String) (plural : String) : String :=
  s!"{c} {if c == 1 then single else plural}"

/-- Verdict for an `Anticommute p q` proposition, as (color, short, long):
parity of the number of anticommuting positions, as in
`commutes_iff_even_anticommutes`. The short form goes on the card, the long form
into its tooltip and the logged text. -/
def anticommuteVerdictData (vp vq : PauliView) (marks : Array Bool) :
    String × String × String :=
  let c := countMarks marks
  let stuck := vp.numStuck + vq.numStuck
  if stuck > 0 then
    (warnColor, s!"? {countNoun stuck "cell" "cells"} unresolved",
      s!"{countNoun c "anticommuting position" "anticommuting positions"} among resolved \
        cells, but {countNoun stuck "cell" "cells"} did not reduce — parity undetermined.")
  else if c % 2 == 1 then
    (okColor, s!"✓ anticommute — {countNoun c "crossing" "crossings"} (odd)",
      s!"{countNoun c "anticommuting qubit position" "anticommuting qubit positions"} — odd, \
        so the operators anticommute: this Anticommute goal holds (decide closes it).")
  else
    (badColor, s!"✗ commute — {countNoun c "crossing" "crossings"} (even)",
      s!"{countNoun c "anticommuting qubit position" "anticommuting qubit positions"} — even, \
        so the operators commute: this Anticommute goal is false.")

/-- Verdict for an equality between Pauli terms, as (color, short, long):
pointwise comparison plus (for group elements) the phase difference. -/
def eqVerdictData (isElement : Bool) (vp vq : PauliView) (marks : Array Bool) :
    String × String × String :=
  let c := countMarks marks
  let stuck := vp.numStuck + vq.numStuck
  if stuck > 0 then
    (warnColor, s!"? {countNoun stuck "cell" "cells"} unresolved",
      s!"{countNoun c "differing position" "differing positions"} among resolved cells, but \
        {countNoun stuck "cell" "cells"} did not reduce — comparison incomplete.")
  else if c > 0 then
    (badColor, s!"✗ differ at {countNoun c "qubit" "qubits"}",
      s!"the sides differ at {countNoun c "qubit position" "qubit positions"} — not equal.")
  else if !isElement then
    (okColor, "✓ equal", "the sides agree at every qubit — the operators are equal.")
  else
    match vp.phasePower, vq.phasePower with
    | some a, some b =>
      if a == b then
        (okColor, "✓ equal",
          "the sides agree at every qubit and carry the same phase — the elements are equal.")
      else
        (badColor, s!"✗ phases differ — {phaseStr (some a)} vs {phaseStr (some b)}",
          s!"operator parts agree, but the phases differ ({phaseStr (some a)} vs \
            {phaseStr (some b)}) — not equal. (For p * q = q * p goals this phase gap is \
            exactly anticommutation.)")
    | _, _ =>
      (warnColor, "? phase unresolved",
        "the operator parts agree, but a phase did not reduce — comparison incomplete.")

/-- Strips wider than this are refused (each cell costs a reduction). -/
def maxStripQubits : Nat := 512

/-- Render any recognized Pauli shape (term, `Anticommute`, or equality) as HTML
plus a plain-text summary (logged by `#pauli_strip` so terminals see something
too), or `none` when `e` is not one / is not concrete enough. -/
def pauliRender? (e : Expr) : MetaM (Option (Html × String)) := do
  let e ← instantiateMVars e
  match ← pauliShape? e with
  | none => return none
  | some (.term k te) =>
    if k.numQubits > maxStripQubits then return none
    let showPhase := match k with | .element _ => true | .operator _ => false
    let v ← viewOfTerm k te
    return some (stripCard (← exprName te) v showPhase, termSummary v showPhase)
  | some (.anticommute n p q) =>
    if n > maxStripQubits then return none
    let vp ← elementView p n
    let vq ← elementView q n
    let marks := marksAnticommute vp vq
    let (color, short, long) := anticommuteVerdictData vp vq marks
    let html := dualCard (← exprName p) (← exprName q) vp vq marks
      (verdictLine color short long) true (accent := some color)
    return some (html, s!"p = {vp.letters}\nq = {vq.letters}\n{long}")
  | some (.eq k lhs rhs) =>
    if k.numQubits > maxStripQubits then return none
    let vl ← viewOfTerm k lhs
    let vr ← viewOfTerm k rhs
    let marks := marksDiffer vl vr
    let isElement := match k with | .element _ => true | .operator _ => false
    let (color, short, long) := eqVerdictData isElement vl vr marks
    let html := dualCard (← exprName lhs) (← exprName rhs) vl vr marks
      (verdictLine color short long) isElement (accent := some color)
    return some (html, s!"lhs = {vl.letters}\nrhs = {vr.letters}\n{long}")

/-- Presenter entry point: render or fail (failure = "not applicable"). -/
def pauliPresent (e : Expr) : MetaM Html := do
  match ← pauliRender? e with
  | some (h, _) => return h
  | none => throwError "not a concrete Pauli expression"

/-- Infoview presenter for Pauli terms and commutation propositions. With
`ProofWidgets.SelectionPanel` open, shift-click a Pauli expression in the goal
to render it; `ProofWidgets.GoalTypePanel` renders goals of the proposition
shapes directly. -/
@[expr_presenter]
def pauliStripPresenter : ExprPresenter where
  userName := "Pauli strip"
  layoutKind := .block
  present := pauliPresent

/-- `#pauli_strip e` displays a colored per-qubit strip for a concrete Pauli
expression in the infoview. `e` may be an `NQubitPauliGroupElement n`, an
`NQubitPauliOperator n`, an `Anticommute p q` proposition, or an equality
between Pauli terms; the proposition forms render both operands with the
anticommuting (resp. differing) positions ringed and a parity verdict. -/
syntax (name := pauliStripCmd) "#pauli_strip " term : command

open Elab Command in
@[command_elab pauliStripCmd]
def elabPauliStripCmd : CommandElab
  | stx@`(#pauli_strip $t:term) => do
    let (ht, txt) ← liftTermElabM do
      let e ← Term.elabTerm t none
      Term.synthesizeSyntheticMVarsNoPostponing
      match ← pauliRender? (← instantiateMVars e) with
      | some r => pure r
      | none => throwError
          "#pauli_strip: not a recognized concrete Pauli expression. Expected an \
          NQubitPauliGroupElement n or NQubitPauliOperator n with a literal qubit count, an \
          Anticommute proposition, or an equality between Pauli terms."
    logInfoAt stx txt
    liftCoreM <| Widget.savePanelWidgetInfo (hash HtmlDisplayPanel.javascript)
      (return json% { html : $(← rpcEncode ht) }) stx
  | stx => throwError "Unexpected syntax {stx}."

end QECWidgets
