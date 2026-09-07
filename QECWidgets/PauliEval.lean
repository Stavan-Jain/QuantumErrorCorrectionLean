/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import QEC.Stabilizer.Foundations.PauliGroup

/-!
# Meta-level evaluation of Pauli expressions

Support layer for the QEC infoview widgets: turns an `Expr` denoting a
*concrete* Pauli object (a generator of a specific code, a product of such
generators, a commutation proposition between them, …) into plain meta-level
data (`PauliView`) that the renderers in `QECWidgets.PauliStrip` can draw.

Everything here is display-only meta code. Nothing is trusted: the widgets show
what weak-head reduction finds, and any proof the user writes is still checked
by the kernel as usual.

The reduction strategy matters. `Mul` on `NQubitPauliGroupElement` is
`noncomputable`, so `#eval`-style compilation is unavailable, but the terms
still *reduce* — the same fact that lets `decide` close `Anticommute` goals
through the kernel. We therefore evaluate by weak-head normalization, escalating
through transparency levels and finishing with the kernel evaluator (which
ignores `@[irreducible]` markers, i.e. sees exactly what `decide` sees).
-/

namespace QECWidgets

open Lean Meta Quantum

/-- The weak-head normal forms of `e` to try when looking for a constructor
head: default transparency first (cheap), then `.all`, and finally the kernel
evaluator. Failures are dropped rather than propagated — callers just match
against whichever candidates exist. -/
def whnfCandidates (e : Expr) : MetaM (List Expr) := do
  let mut out : List Expr := []
  try out := out.concat (← whnf e) catch _ => pure ()
  try out := out.concat (← withTransparency .all (whnf e)) catch _ => pure ()
  try
    match Kernel.whnf (← getEnv) (← getLCtx) e with
    | .ok e' => out := out.concat e'
    | .error _ => pure ()
  catch _ => pure ()
  return out

/-- Extract a `Nat` literal from `e`, reducing and unwrapping `OfNat.ofNat` as
needed. -/
partial def natOfExpr? (e : Expr) : MetaM (Option Nat) := do
  if let some k := e.rawNatLit? then return some k
  for e' in ← whnfCandidates e do
    if let some k := e'.rawNatLit? then return some k
    if e'.isAppOfArity ``OfNat.ofNat 3 then
      if let some k ← natOfExpr? (e'.getArg! 1) then return some k
  return none

/-- Extract the value of a `Fin`-like literal (this covers `ZMod (k+1)`, which
reduces to `Fin (k+1)`): reduce to `Fin.mk v _` and read off `v`. -/
def finValOfExpr? (e : Expr) : MetaM (Option Nat) := do
  for e' in ← whnfCandidates e do
    if e'.isAppOfArity ``Fin.mk 3 then
      return ← natOfExpr? (e'.getArg! 1)
  return none

/-- Reduce `e` to a `PauliOperator` constructor, if possible. -/
def pauliOfExpr? (e : Expr) : MetaM (Option PauliOperator) := do
  for e' in ← whnfCandidates e do
    if let some n := e'.constName? then
      if n == ``Quantum.PauliOperator.I then return some .I
      if n == ``Quantum.PauliOperator.X then return some .X
      if n == ``Quantum.PauliOperator.Y then return some .Y
      if n == ``Quantum.PauliOperator.Z then return some .Z
  return none

/-- Build the literal `(⟨i, _⟩ : Fin n)`; the bound proof is produced by
`decide`, so this only works for `i < n` (which is all we ever ask for). -/
def mkFinLit (n i : Nat) : MetaM Expr := do
  let prf ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit i, mkNatLit n])
  mkAppOptM ``Fin.mk #[some (mkNatLit n), some (mkNatLit i), some prf]

/-- The result of evaluating a Pauli expression: an optional phase exponent
(`i^k`; `none` for bare operators or when the phase is stuck) and the per-qubit
factors (`none` where reduction got stuck, e.g. at a variable). -/
structure PauliView where
  /-- Number of qubits. -/
  numQubits : Nat
  /-- Phase exponent `k` in `i^k`, when the expression is a group element whose
phase reduced to a literal. -/
  phasePower : Option Nat := none
  /-- Per-qubit single-qubit factors; `none` where reduction got stuck. -/
  ops : Array (Option PauliOperator)
deriving Inhabited

/-- Number of resolved non-identity cells. -/
def PauliView.weight (v : PauliView) : Nat :=
  v.ops.foldl (fun acc o => if o.isSome && o != some .I then acc + 1 else acc) 0

/-- Number of cells where reduction got stuck. -/
def PauliView.numStuck (v : PauliView) : Nat :=
  v.ops.foldl (fun acc o => if o.isNone then acc + 1 else acc) 0

/-- Evaluate an `NQubitPauliOperator n` expression pointwise at every qubit. -/
def operatorView (ops : Expr) (n : Nat) : MetaM PauliView := do
  let mut cells : Array (Option PauliOperator) := #[]
  for i in [0:n] do
    cells := cells.push (← pauliOfExpr? (mkApp ops (← mkFinLit n i)))
  return { numQubits := n, ops := cells }

/-- Evaluate an `NQubitPauliGroupElement n` expression: phase exponent plus
pointwise operators. -/
def elementView (e : Expr) (n : Nat) : MetaM PauliView := do
  let ph ← finValOfExpr? (← mkAppM ``Quantum.NQubitPauliGroupElement.phasePower #[e])
  let v ← operatorView (← mkAppM ``Quantum.NQubitPauliGroupElement.operators #[e]) n
  return { v with phasePower := ph }

/-- The kinds of Pauli-valued terms the widgets understand. -/
inductive PauliTermKind where
  /-- `e : NQubitPauliGroupElement n` (phase and operators). -/
  | element (n : Nat)
  /-- `e : NQubitPauliOperator n`, or literally `Fin n → PauliOperator`. -/
  | operator (n : Nat)

/-- The number of qubits of a term kind. -/
def PauliTermKind.numQubits : PauliTermKind → Nat
  | .element n => n
  | .operator n => n

/-- Classify a *term* by its type: group element or bare operator, with a
literal qubit count. -/
def pauliTermKind? (e : Expr) : MetaM (Option PauliTermKind) := do
  let t ← instantiateMVars (← inferType e)
  if t.isAppOfArity ``Quantum.NQubitPauliGroupElement 1 then
    if let some n ← natOfExpr? (t.getArg! 0) then
      return some (.element n)
  if t.isAppOfArity ``Quantum.NQubitPauliOperator 1 then
    if let some n ← natOfExpr? (t.getArg! 0) then
      return some (.operator n)
  if let .forallE _ dom body _ := t then
    if !body.hasLooseBVars && body.isConstOf ``Quantum.PauliOperator
        && dom.isAppOfArity ``Fin 1 then
      if let some n ← natOfExpr? (dom.getArg! 0) then
        return some (.operator n)
  return none

/-- Evaluate a term of the given kind to a `PauliView`. -/
def viewOfTerm (k : PauliTermKind) (e : Expr) : MetaM PauliView :=
  match k with
  | .element n => elementView e n
  | .operator n => operatorView e n

/-- The shapes of expressions the Pauli strip widgets can present: Pauli terms,
`Anticommute p q` propositions, and equalities between Pauli terms (the form
commutation goals take). -/
inductive PauliShape where
  /-- A Pauli-valued term. -/
  | term (k : PauliTermKind) (e : Expr)
  /-- The proposition `NQubitPauliGroupElement.Anticommute p q`. -/
  | anticommute (n : Nat) (p q : Expr)
  /-- The proposition `lhs = rhs` between Pauli terms of kind `k`. -/
  | eq (k : PauliTermKind) (lhs rhs : Expr)

/-- Classify an expression for presentation. Propositions are matched on the
expression itself (this is what a goal or a selected goal location gives us);
anything else is classified by its type. -/
def pauliShape? (e : Expr) : MetaM (Option PauliShape) := do
  if e.isAppOfArity ``Quantum.NQubitPauliGroupElement.Anticommute 3 then
    if let some n ← natOfExpr? (e.getArg! 0) then
      return some (.anticommute n (e.getArg! 1) (e.getArg! 2))
  if e.isAppOfArity ``Eq 3 then
    if let some k ← pauliTermKind? (e.getArg! 1) then
      return some (.eq k (e.getArg! 1) (e.getArg! 2))
  if let some k ← pauliTermKind? e then
    return some (.term k e)
  return none

/-- Do two single-qubit Paulis anticommute? (Both non-identity and distinct.) -/
def anticommutesBool : PauliOperator → PauliOperator → Bool
  | .I, _ => false
  | _, .I => false
  | a, b => a != b

end QECWidgets
