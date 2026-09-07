/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import QECWidgets.PauliStrip
import ProofWidgets.Component.OfRpcMethod
import ProofWidgets.Component.MakeEditLink

/-!
# `pauli_strip?` — the goal as a strip view, with a `decide` suggestion

A suggestion tactic in the `rw??` style: writing `pauli_strip?` in a proof
renders the current goal's Pauli strip view in the infoview, and — when the
widget's own parity computation says the goal holds — offers a link that
replaces the `pauli_strip?` call with `decide`.

The panel is a server-rendered component (`mk_rpc_widget%`): the RPC method
receives the goals plus the range to replace, so the edit is built against the
live document (`MakeEditLinkProps.ofReplaceRange` needs the current
`DocumentMeta`, which only exists server-side).
-/

namespace QECWidgets

open Lean Server Meta ProofWidgets Quantum

/-- Whether a recognized concrete Pauli proposition holds, by the same
computation the verdicts use (anticommutation parity / pointwise comparison):
`some true` exactly when `decide` should close it, `none` when the proposition
is not recognized or did not fully reduce. -/
def pauliGoalHolds? (e : Expr) : MetaM (Option Bool) := do
  let count (marks : Array Bool) : Nat :=
    marks.foldl (fun acc b => if b then acc + 1 else acc) 0
  match ← pauliShape? e with
  | some (.anticommute n p q) =>
    if n > maxStripQubits then return none
    let vp ← elementView p n
    let vq ← elementView q n
    if vp.numStuck + vq.numStuck > 0 then return none
    return some (count (marksAnticommute vp vq) % 2 == 1)
  | some (.eq k lhs rhs) =>
    if k.numQubits > maxStripQubits then return none
    let vl ← viewOfTerm k lhs
    let vr ← viewOfTerm k rhs
    if vl.numStuck + vr.numStuck > 0 then return none
    if count (marksDiffer vl vr) > 0 then return some false
    match k with
    | .operator _ => return some true
    | .element _ =>
      match vl.phasePower, vr.phasePower with
      | some a, some b => return some (a == b)
      | _, _ => return none
  | _ => return none

/-- Props for `PauliSuggestionPanel`: the panel props the infoview injects, plus
the source range the suggestion link replaces (the `pauli_strip?` call itself,
recorded when the tactic runs). -/
structure PauliSuggestionProps where
  /-- Cursor position in the file. -/
  pos : Lsp.Position
  /-- Current tactic-mode goals. -/
  goals : Array Widget.InteractiveGoal
  /-- The source range the suggestion link replaces. -/
  replaceRange : Lsp.Range
  deriving RpcEncodable

/-- Render the main goal as a Pauli card; when it holds, append the `decide`
suggestion link. -/
private def suggestionBody (docMeta : DocumentMeta) (range : Lsp.Range)
    (goals : Array Widget.InteractiveGoal) : RequestM Html := do
  let some g := goals[0]?
    | return .text "No goals."
  g.ctx.val.runMetaM {} do
    let md ← g.mvarId.getDecl
    Meta.withLCtx md.lctx md.localInstances do
      let ty ← instantiateMVars md.type.consumeMData
      match ← pauliRender? ty with
      | none => return .text "The goal is not a recognized concrete Pauli proposition."
      | some (html, _) =>
        match ← pauliGoalHolds? ty with
        | some true =>
          let link := Html.ofComponent MakeEditLink
            (.ofReplaceRange docMeta range "decide") #[.text "replace with decide"]
          return el "div" #[] #[html,
            cls "div" "qecw-verdict" #[("style", json% { color: $(okColor) })] #[link]]
        | _ => return html

open RequestM in
/-- RPC backing `PauliSuggestionPanel`. -/
@[server_rpc_method]
def PauliSuggestionPanel.rpc (props : PauliSuggestionProps) : RequestM (RequestTask Html) :=
  RequestM.asTask do
    let doc ← RequestM.readDoc
    let inner ← suggestionBody doc.meta props.replaceRange props.goals
    return el "details" #[("open", Json.bool true)]
      #[el "summary" #[("className", Json.str "mv2 pointer")] #[.text "Pauli strip"], inner]

/-- The `pauli_strip?` panel: the goal as a strip view plus, when the parity
verdict says the goal holds, a link that inserts `decide`. -/
@[widget_module]
def PauliSuggestionPanel : Component PauliSuggestionProps :=
  mk_rpc_widget% PauliSuggestionPanel.rpc

/-- `pauli_strip?` renders the current goal's Pauli strip view in the infoview
(put the cursor on the tactic). When the widget's parity computation says the
goal holds, the panel offers a link that replaces this tactic call with
`decide`. The goal is left untouched until then. -/
syntax (name := pauliStripTac) "pauli_strip?" : tactic

open Elab Tactic in
@[tactic pauliStripTac]
def elabPauliStripTac : Tactic := fun stx => do
  let some range := (← getFileMap).lspRangeOfStx? stx
    | throwError "pauli_strip?: could not find the source range of the tactic call"
  Widget.savePanelWidgetInfo (hash PauliSuggestionPanel.javascript)
    (pure <| json% { replaceRange : $(toJson range) }) stx

-- Like every suggestion widget, `pauli_strip?` intentionally leaves the goal
-- unchanged, so register it with the unused-tactic linter's dynamic
-- allowlist. This runs on import, covering every file that can use the
-- tactic; the `#allow_unused_tactic!` command is avoided because a silent
-- `#`-command would itself be flagged by `linter.hashCommand`.
initialize Mathlib.Linter.UnusedTactic.allowedRef.modify (·.insert ``QECWidgets.pauliStripTac)

end QECWidgets
