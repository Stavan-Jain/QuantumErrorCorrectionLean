/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrix
import QECWidgets.PauliStrip

/-!
# Check-matrix heatmap

Renders a concrete generator list `L : List (NQubitPauliGroupElement n)` as:

- its binary symplectic check matrix, in the `checkMatrix` column convention
  (first `n` columns the X-components, last `n` the Z-components, X = coral / Z
  = blue); and
- the symplectic Gram matrix: cell `(i, j)` is the symplectic inner product of
  rows `i` and `j` mod 2 — red exactly when generators `i` and `j` anticommute.
  Color marks only that signal: a valid stabilizer generator list shows a quiet
  all-hairline Gram matrix, and the header verdict (plus the card's state bar)
  says so.

Use `#check_matrix gens`, or the `Check matrix` expression presenter via
`ProofWidgets.SelectionPanel`.
-/

namespace QECWidgets

open Lean Server Meta ProofWidgets Quantum

/-- Most rows a check-matrix view will draw. -/
def maxCheckRows : Nat := 64

/-- Walk a list expression into its element expressions by weak-head reduction
(`none` if some spine cell is stuck or the list is longer than `maxLen`). -/
def listElems? (e : Expr) (maxLen : Nat := maxCheckRows) : MetaM (Option (Array Expr)) := do
  let mut cur := e
  let mut out : Array Expr := #[]
  for _ in [0:maxLen + 1] do
    let mut next : Option Expr := none
    let mut done := false
    for c in ← whnfCandidates cur do
      if c.isAppOfArity ``List.cons 3 then
        out := out.push (c.getArg! 1)
        next := some (c.getArg! 2)
        break
      if c.isAppOfArity ``List.nil 1 then
        done := true
        break
    if done then return some out
    match next with
    | some t => cur := t
    | none => return none
  return none

/-- Recognize a generator-list expression: type
`List (NQubitPauliGroupElement n)` with `n` literal. Returns `n`. -/
def genListShape? (e : Expr) : MetaM (Option Nat) := do
  let t ← instantiateMVars (← inferType e)
  if t.isAppOfArity ``List 1 then
    let elemT ← whnfR (t.getArg! 0)
    if elemT.isAppOfArity ``NQubitPauliGroupElement 1 then
      return ← natOfExpr? (elemT.getArg! 0)
  return none

/-- X-component of a single-qubit factor (`toSymplecticSingle.1`). -/
def xBit : PauliOperator → Bool
  | .X => true
  | .Y => true
  | _ => false

/-- Z-component of a single-qubit factor (`toSymplecticSingle.2`). -/
def zBit : PauliOperator → Bool
  | .Z => true
  | .Y => true
  | _ => false

/-- Symplectic inner product of two rows mod 2 (`true` = anticommute), or `none`
when unresolved cells make the parity unknown. -/
def gramBit (vp vq : PauliView) : Option Bool := Id.run do
  if vp.numStuck + vq.numStuck > 0 then return none
  let mut c := 0
  for i in [0:vp.numQubits] do
    match vp.ops.getD i none, vq.ops.getD i none with
    | some a, some b => if anticommutesBool a b then c := c + 1
    | _, _ => pure ()
  return some (c % 2 == 1)

/-- One heatmap cell: a `qecw-bit` with a variant class; sizes other than the
stylesheet's 13 px default are set inline (for wide matrices). -/
private def bitHtml (variant : String) (title : String) (size : Nat := 13) : Html :=
  let attrs := #[("title", Json.str title)] ++
    (if size == 13 then #[]
     else #[("style", json% { width: $(s!"{size}px"), height: $(s!"{size}px") })])
  cls "span" ("qecw-bit " ++ variant) attrs

/-- Leading row-index label for matrix rows. -/
private def rowIdx (i : Nat) : Html :=
  cls "span" "qecw-rowlabel" #[] #[.text (toString i)]

/-- One check-matrix row: leading generator index, X block, gap, Z block. -/
private def matrixRow (size : Nat) (i : Nat) (v : PauliView) : Html := Id.run do
  let mut cells : Array Html := #[rowIdx i]
  let block (isX : Bool) : Array Html := Id.run do
    let mut out : Array Html := #[]
    for q in [0:v.numQubits] do
      let part := if isX then "X" else "Z"
      let cell := match v.ops.getD q none with
        | none => bitHtml "qecw-bit-stuck" s!"g{i}, {part} part, qubit {q}: unresolved" size
        | some p =>
          let bit := if isX then xBit p else zBit p
          let variant := if !bit then "qecw-bit-0"
            else if isX then "qecw-bit-x" else "qecw-bit-z"
          bitHtml variant s!"g{i}, {part} part, qubit {q}: {if bit then 1 else 0}" size
      out := out.push cell
    return out
  cells := cells ++ block true
  cells := cells.push (styled "span" (json% { display: "inline-block", width: "10px" }) #[])
  cells := cells ++ block false
  return styled "div" (json% { display: "flex", alignItems: "center" }) cells

/-- The Gram matrix block: `k × k` commutation parities. Only anticommuting
pairs are colored; commuting pairs stay hairline-quiet. -/
private def gramHtml (size : Nat) (views : Array PauliView) : Html := Id.run do
  let k := views.size
  let mut rows : Array Html := #[]
  for i in [0:k] do
    let mut cells : Array Html := #[rowIdx i]
    for j in [0:k] do
      let cell :=
        if i == j then
          bitHtml "qecw-bit-diag" s!"⟨g{i}, g{i}⟩ = 0" size
        else
          match gramBit (views.getD i default) (views.getD j default) with
          | none => bitHtml "qecw-bit-stuck" s!"⟨g{i}, g{j}⟩ unresolved" size
          | some true => bitHtml "qecw-bit-anti" s!"⟨g{i}, g{j}⟩ = 1 — anticommute!" size
          | some false => bitHtml "qecw-bit-0" s!"⟨g{i}, g{j}⟩ = 0 — commute" size
      cells := cells.push cell
    rows := rows.push (styled "div" (json% { display: "flex", alignItems: "center" }) cells)
  return el "div" #[] rows

/-- Render a generator list as check matrix + Gram matrix, plus a text summary,
or `none` when the expression is not a concrete generator list. -/
def checkMatrixRender? (e : Expr) : MetaM (Option (Html × String)) := do
  let e ← instantiateMVars e
  let some n ← genListShape? e | return none
  if n == 0 || n > maxStripQubits then return none
  let some elems ← listElems? e | return none
  if elems.isEmpty then return none
  let mut views : Array PauliView := #[]
  for g in elems do
    views := views.push (← elementView g n)
  let k := views.size
  -- Gram verdict.
  let mut badPairs := 0
  let mut unknownPairs := 0
  for i in [0:k] do
    for j in [0:k] do
      if i < j then
        match gramBit (views.getD i default) (views.getD j default) with
        | some true => badPairs := badPairs + 1
        | none => unknownPairs := unknownPairs + 1
        | some false => pure ()
  let plural (k : Nat) : String := if k == 1 then "pair" else "pairs"
  let (accent, verdictFact) :=
    if unknownPairs > 0 then
      (warnColor, headerFact s!"? {unknownPairs} {plural unknownPairs} unresolved"
        "some entries did not reduce, so those commutation parities are unknown"
        (some warnColor))
    else if badPairs == 0 then
      (okColor, headerFact "✓ all pairs commute" "valid stabilizer generator list"
        (some okColor))
    else
      (badColor, headerFact s!"✗ {badPairs} anticommuting {plural badPairs}"
        "see the red Gram cells — this list is not mutually commuting" (some badColor))
  let header := headerHtml (← exprName e) #[verdictFact]
  let size : Nat := if n ≤ 32 then 13 else if n ≤ 80 then 9 else 5
  let blockW := n * (size + 2)
  let blockLabel (letter color title : String) : Html :=
    cls "span" "qecw-micro"
      #[("title", Json.str title),
        ("style", json% {
          width: $(s!"{blockW}px"), textAlign: "center", fontWeight: "600",
          color: $(color) })]
      #[.text letter]
  let blockLabels := styled "div" (json% { display: "flex", marginLeft: "37px" })
    #[blockLabel "X" xAccent.hex s!"X components (columns 0–{n - 1} of checkMatrix)",
      styled "span" (json% { width: "12px" }) #[],
      blockLabel "Z" zAccent.hex s!"Z components (columns {n}–{2 * n - 1})"]
  let mut mat : Array Html := #[]
  for i in [0:k] do
    mat := mat.push (matrixRow size i (views.getD i default))
  let matBox := styled "div" (json% { overflowX: "auto", paddingBottom: "2px" }) mat
  let gramLabel := cls "div" "qecw-micro"
    #[("title", Json.str "symplectic Gram matrix — red = the pair anticommutes"),
      ("style", json% { margin: "8px 0 2px 37px" })]
    #[.text "Gram"]
  let html := card (accent := some accent)
    #[header, blockLabels, matBox, gramLabel, gramHtml size views]
  let mut txt := ""
  for i in [0:k] do
    txt := txt ++ s!"g{i}: {(views.getD i default).letters}\n"
  txt := txt ++
    (if unknownPairs > 0 then s!"{unknownPairs} {plural unknownPairs} unresolved"
     else if badPairs == 0 then "all pairs commute — valid stabilizer generator list"
     else s!"{badPairs} anticommuting {plural badPairs} — NOT mutually commuting")
  return some (html, txt)

/-- Presenter entry point: render or fail (failure = "not applicable"). -/
def checkMatrixPresent (e : Expr) : MetaM Html := do
  match ← checkMatrixRender? e with
  | some (h, _) => return h
  | none => throwError "not a concrete Pauli generator list"

/-- Infoview presenter for generator lists: check matrix plus Gram matrix. With
`ProofWidgets.SelectionPanel` open, shift-click a
`List (NQubitPauliGroupElement n)` in the goal to render it. -/
@[expr_presenter]
def checkMatrixPresenter : ExprPresenter where
  userName := "Check matrix"
  layoutKind := .block
  present := checkMatrixPresent

/-- `#check_matrix gens` displays the binary symplectic check matrix of a
concrete `List (NQubitPauliGroupElement n)` (X block then Z block, matching
`checkMatrix`), together with the pairwise commutation (Gram) matrix — red cells
are anticommuting pairs, so a valid stabilizer generator list shows none. -/
syntax (name := checkMatrixCmd) "#check_matrix " term : command

open Elab Command in
@[command_elab checkMatrixCmd]
def elabCheckMatrixCmd : CommandElab
  | stx@`(#check_matrix $t:term) => do
    let (ht, txt) ← liftTermElabM do
      let e ← Term.elabTerm t none
      Term.synthesizeSyntheticMVarsNoPostponing
      match ← checkMatrixRender? (← instantiateMVars e) with
      | some r => pure r
      | none => throwError
          "#check_matrix: not a concrete generator list. Expected a \
          List (NQubitPauliGroupElement n) with a literal qubit count whose spine and \
          entries reduce (at most {maxCheckRows} generators, n ≤ {maxStripQubits})."
    logInfoAt stx txt
    liftCoreM <| Widget.savePanelWidgetInfo (hash HtmlDisplayPanel.javascript)
      (return json% { html : $(← rpcEncode ht) }) stx
  | stx => throwError "Unexpected syntax {stx}."

end QECWidgets
