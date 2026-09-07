/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import QEC.Stabilizer.Codes.Toric.ChainOps
import QECWidgets.PauliStrip

/-!
# Toric lattice view

Draws a concrete toric 1-chain on the `L × L` torus: qubits are edges, edges
carried by the chain are highlighted, and edges that wrap around the torus are
drawn as dotted stubs on both sides. Recognized shapes:

- a term of type `C1 L` (or literally `EdgeIdx L → ZMod 2`) — neutral purple;
- `toricXOperatorOfChain L c` — the chain `c` in X coral;
- `toricZOperatorOfChain L c` — the chain `c` in Z blue.

Use the `#toric_chain e` command, or the `Toric lattice` expression presenter
(via `ProofWidgets.SelectionPanel`) during a proof. Drawing convention matches
`toricBoundary1`: edge `h x y` joins vertex `(x, y)` to `(next x, y)`
(rightward), `v x y` joins `(x, y)` to `(x, next y)` (downward, matching
row-major index order).

Chain strokes are drawn over a background-colored halo (map-style casing) so
loops read cleanly where they cross the grid.
-/

namespace QECWidgets

open Lean Server Meta ProofWidgets Quantum Quantum.Stabilizer.Lattice

/-- An evaluated toric 1-chain: one presence bit per horizontal / vertical edge
(`none` where reduction got stuck). Both arrays are row-major: edge `(x, y)`
sits at index `y * L + x`. -/
structure ChainView where
  /-- Lattice side length. -/
  L : Nat
  /-- Horizontal edges `h x y`. -/
  hEdges : Array (Option Bool)
  /-- Vertical edges `v x y`. -/
  vEdges : Array (Option Bool)

/-- Number of edges carried by the chain (resolved cells only). -/
def ChainView.size (v : ChainView) : Nat :=
  (v.hEdges ++ v.vEdges).foldl (fun acc o => if o == some true then acc + 1 else acc) 0

/-- Number of edges where reduction got stuck. -/
def ChainView.numStuck (v : ChainView) : Nat :=
  (v.hEdges ++ v.vEdges).foldl (fun acc o => if o.isNone then acc + 1 else acc) 0

/-- Reduce a `ZMod 2` value to a `Bool` (is it `1`?). -/
def zmod2OfExpr? (e : Expr) : MetaM (Option Bool) := do
  match ← finValOfExpr? e with
  | some k => return some (k % 2 == 1)
  | none => return none

/-- Evaluate a `C1 L` expression at every edge of the lattice. -/
def chainView (c : Expr) (L : Nat) : MetaM ChainView := do
  let LE := mkNatLit L
  let mut hs : Array (Option Bool) := #[]
  let mut vs : Array (Option Bool) := #[]
  for y in [0:L] do
    for x in [0:L] do
      let xE ← mkFinLit L x
      let yE ← mkFinLit L y
      hs := hs.push (← zmod2OfExpr? (mkApp c (mkApp3 (mkConst ``EdgeIdx.h) LE xE yE)))
      vs := vs.push (← zmod2OfExpr? (mkApp c (mkApp3 (mkConst ``EdgeIdx.v) LE xE yE)))
  return { L := L, hEdges := hs, vEdges := vs }

/-- Which flavor of object the chain came from (fixes the highlight color). -/
inductive ChainFlavor where
  /-- A bare 1-chain. -/
  | plain
  /-- The chain under `toricXOperatorOfChain`. -/
  | xOp
  /-- The chain under `toricZOperatorOfChain`. -/
  | zOp

/-- Highlight color per flavor. -/
def ChainFlavor.color : ChainFlavor → String
  | .plain => markHex
  | .xOp => xAccent.hex
  | .zOp => zAccent.hex

/-- Short label per flavor. -/
def ChainFlavor.label : ChainFlavor → Option String
  | .plain => none
  | .xOp => some "X operator support"
  | .zOp => some "Z operator support"

/-- One-letter header label per flavor (`none` for a bare chain). -/
def ChainFlavor.letter : ChainFlavor → Option String
  | .plain => none
  | .xOp => some "X"
  | .zOp => some "Z"

/-- Lattices larger than this are refused (each edge costs a reduction, and the
drawing stops being readable). -/
def maxToricL : Nat := 16

/-- Recognize a toric-chain-shaped expression: an `toricXOperatorOfChain L c` /
`toricZOperatorOfChain L c` application, or a term whose type is `C1 L` (or
unfolded `EdgeIdx L → ZMod 2`), with `L` literal. Returns the flavor, `L`, and
the chain expression. -/
def toricShape? (e : Expr) : MetaM (Option (ChainFlavor × Nat × Expr)) := do
  if e.isAppOfArity ``toricXOperatorOfChain 2 then
    if let some L ← natOfExpr? (e.getArg! 0) then
      return some (.xOp, L, e.getArg! 1)
  if e.isAppOfArity ``toricZOperatorOfChain 2 then
    if let some L ← natOfExpr? (e.getArg! 0) then
      return some (.zOp, L, e.getArg! 1)
  let t ← instantiateMVars (← inferType e)
  if t.isAppOfArity ``C1 1 then
    if let some L ← natOfExpr? (t.getArg! 0) then
      return some (.plain, L, e)
  if let .forallE _ dom body _ := t then
    if !body.hasLooseBVars && dom.isAppOfArity ``EdgeIdx 1
        && body.isAppOfArity ``ZMod 1 then
      if (← natOfExpr? (body.getArg! 0)) == some 2 then
        if let some L ← natOfExpr? (dom.getArg! 0) then
          return some (.plain, L, e)
  return none

/-- Coordinate attributes for an SVG `line`. -/
private def lineCoords (x1 y1 x2 y2 : Nat) : Array (String × Json) :=
  #[("x1", toJson x1), ("y1", toJson y1), ("x2", toJson x2), ("y2", toJson y2)]

/-- A base-grid line (hairline, crisp, muted via the stylesheet). -/
private def gridLine (x1 y1 x2 y2 : Nat) (dashed : Bool := false) : Html :=
  cls "line" "qecw-svg-grid"
    (lineCoords x1 y1 x2 y2 ++
      if dashed then #[("strokeDasharray", Json.str "2 4")] else #[])

/-- A chain edge: a background-colored halo under a colored stroke, so loops
stay legible where they cross the grid. Wrap stubs are dotted. -/
private def chainSeg (x1 y1 x2 y2 : Nat) (color : String) (dashed : Bool := false) :
    Array Html :=
  let dash : Array (String × Json) :=
    if dashed then #[("strokeDasharray", Json.str "0.1 6")] else #[]
  #[cls "line" "qecw-svg-halo" (lineCoords x1 y1 x2 y2 ++ dash),
    el "line"
      (lineCoords x1 y1 x2 y2 ++ dash ++
        #[("strokeWidth", toJson (2.75 : Float)), ("strokeLinecap", Json.str "round"),
          ("fill", Json.str "none"), ("style", json% { stroke: $(color) })])
      #[]]

/-- Draw the lattice: base grid (with dashed wrap stubs), the chain's edges in
the flavor color over halos, stuck edges in the warning color, vertex dots, and
coordinate labels on small lattices. -/
def latticeSvg (v : ChainView) (flavor : ChainFlavor) : Html := Id.run do
  let L := v.L
  let s : Nat := if L ≤ 6 then 44 else if L ≤ 10 then 30 else 22
  let m : Nat := 30
  let stub := (s * 2) / 5
  let side := m + (L - 1) * s + m
  let px (i : Nat) : Nat := m + i * s
  let mut kids : Array Html := #[]
  -- Base grid: one solid line per row/column, plus dashed wrap stubs.
  for i in [0:L] do
    kids := kids.push (gridLine m (px i) (px (L - 1)) (px i))
    kids := kids.push (gridLine (px i) m (px i) (px (L - 1)))
    kids := kids.push (gridLine (m - stub) (px i) m (px i) true)
    kids := kids.push (gridLine (px (L - 1)) (px i) (px (L - 1) + stub) (px i) true)
    kids := kids.push (gridLine (px i) (m - stub) (px i) m true)
    kids := kids.push (gridLine (px i) (px (L - 1)) (px i) (px (L - 1) + stub) true)
  -- Chain edges (drawn after the grid so they sit on top).
  for y in [0:L] do
    for x in [0:L] do
      let hVal := v.hEdges.getD (y * L + x) none
      if hVal != some false then
        let color := if hVal == none then warnColor else flavor.color
        if x + 1 < L then
          kids := kids ++ chainSeg (px x) (px y) (px (x + 1)) (px y) color
        else
          kids := kids ++ chainSeg (px x) (px y) (px x + stub) (px y) color true
          kids := kids ++ chainSeg (m - stub) (px y) m (px y) color true
      let vVal := v.vEdges.getD (y * L + x) none
      if vVal != some false then
        let color := if vVal == none then warnColor else flavor.color
        if y + 1 < L then
          kids := kids ++ chainSeg (px x) (px y) (px x) (px (y + 1)) color
        else
          kids := kids ++ chainSeg (px x) (px y) (px x) (px y + stub) color true
          kids := kids ++ chainSeg (px x) (m - stub) (px x) m color true
  -- Vertices and coordinate labels.
  for y in [0:L] do
    for x in [0:L] do
      kids := kids.push <| cls "circle" "qecw-svg-dot"
        #[("cx", toJson (px x)), ("cy", toJson (px y)), ("r", toJson (1.75 : Float))]
  if L ≤ 12 then
    for i in [0:L] do
      let lbl (tx ty : Nat) : Html := cls "text" "qecw-svg-label"
        #[("x", toJson tx), ("y", toJson ty), ("textAnchor", Json.str "middle")]
        #[.text (toString i)]
      kids := kids.push (lbl (px i) (m - stub - 4))
      kids := kids.push (lbl (m - stub - 6) (px i + 3))
  let tooltip := el "title" #[]
    #[.text "dotted edges wrap around the torus; grid labels are (x, y) lattice coordinates"]
  return el "svg"
    #[("xmlns", Json.str "http://www.w3.org/2000/svg"),
      ("width", toJson side), ("height", toJson side),
      ("viewBox", Json.str s!"0 0 {side} {side}")]
    (#[tooltip] ++ kids)

/-- List the chain's edges as text, e.g. `v(1,0) v(1,1) …` (for `logInfo`). -/
def ChainView.edgeList (v : ChainView) (maxEdges : Nat := 24) : String := Id.run do
  let mut parts : Array String := #[]
  for y in [0:v.L] do
    for x in [0:v.L] do
      if v.hEdges.getD (y * v.L + x) none == some true then
        parts := parts.push s!"h({x},{y})"
  for y in [0:v.L] do
    for x in [0:v.L] do
      if v.vEdges.getD (y * v.L + x) none == some true then
        parts := parts.push s!"v({x},{y})"
  let shown := " ".intercalate (parts.toList.take maxEdges)
  return if parts.size > maxEdges then shown ++ " …" else shown

/-- Render a recognized toric shape as HTML plus a text summary, or `none`. -/
def toricRender? (e : Expr) : MetaM (Option (Html × String)) := do
  let e ← instantiateMVars e
  let some (flavor, L, c) ← toricShape? e | return none
  if L == 0 || L > maxToricL then return none
  let v ← chainView c L
  let mut facts : Array Html := #[]
  if let some letter := flavor.letter then
    facts := facts.push (headerFact letter ((flavor.label).getD "") (some flavor.color))
  facts := facts.push (headerFact s!"{v.size} edges" "edges carried by the chain")
  if v.numStuck > 0 then
    facts := facts.push
      (headerFact s!"? {v.numStuck}" "edges that did not reduce" (some warnColor))
  let accent := match flavor with
    | .plain => none
    | _ => some flavor.color
  let html := card (accent := accent)
    #[headerHtml (← exprName e) facts, latticeSvg v flavor]
  let txt := s!"{v.edgeList}   ({v.size} edges on the {L} × {L} torus)"
  return some (html, txt)

/-- Presenter entry point: render or fail (failure = "not applicable"). -/
def toricPresent (e : Expr) : MetaM Html := do
  match ← toricRender? e with
  | some (h, _) => return h
  | none => throwError "not a concrete toric chain expression"

/-- Infoview presenter for toric 1-chains and toric chain operators. With
`ProofWidgets.SelectionPanel` open, shift-click a chain (or a
`toric{X,Z}OperatorOfChain` application) in the goal to draw it on the torus. -/
@[expr_presenter]
def toricLatticePresenter : ExprPresenter where
  userName := "Toric lattice"
  layoutKind := .block
  present := toricPresent

/-- `#toric_chain e` draws a concrete toric 1-chain on the `L × L` torus in the
infoview. `e` may be a term of type `C1 L`, or an application
`toricXOperatorOfChain L c` / `toricZOperatorOfChain L c` (colored X coral / Z
blue). Wrap-around edges are drawn as dotted stubs on both sides. -/
syntax (name := toricChainCmd) "#toric_chain " term : command

open Elab Command in
@[command_elab toricChainCmd]
def elabToricChainCmd : CommandElab
  | stx@`(#toric_chain $t:term) => do
    let (ht, txt) ← liftTermElabM do
      let e ← Term.elabTerm t none
      Term.synthesizeSyntheticMVarsNoPostponing
      match ← toricRender? (← instantiateMVars e) with
      | some r => pure r
      | none => throwError
          "#toric_chain: not a recognized concrete toric chain. Expected a term of type \
          C1 L (with L a literal, L ≤ {maxToricL}), or toricXOperatorOfChain / \
          toricZOperatorOfChain applied to one."
    logInfoAt stx txt
    liftCoreM <| Widget.savePanelWidgetInfo (hash HtmlDisplayPanel.javascript)
      (return json% { html : $(← rpcEncode ht) }) stx
  | stx => throwError "Unexpected syntax {stx}."

end QECWidgets
