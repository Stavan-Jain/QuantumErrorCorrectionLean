import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic
import QEC.Stabilizer.Foundations.BinarySymplectic.Core
import QEC.Stabilizer.Foundations.PauliGroupSingle
import QEC.Stabilizer.Foundations.PauliGroupSingle.Commutation
import QEC.Stabilizer.Foundations.PauliGroup.NQubitOperator
import QEC.Stabilizer.Foundations.PauliGroup.NQubitElement
import QEC.Stabilizer.Foundations.PauliGroup.Commutation

namespace Quantum

open scoped BigOperators

variable {n : ℕ}

/-!
# Symplectic inner product

The symplectic inner product ⟨v,w⟩_s = (X-part of v)·(Z-part of w) + (Z-part of v)·(X-part of w)
in ZMod 2. Two Pauli group elements commute iff their symplectic inner product is 0.
-/

namespace PauliOperator

/-- Single-qubit symplectic product: 0 iff P and Q commute. -/
def symplecticProductSingle (P Q : PauliOperator) : ZMod 2 :=
  P.toSymplecticSingle.1 * Q.toSymplecticSingle.2 + P.toSymplecticSingle.2 * Q.toSymplecticSingle.1

lemma symplecticProductSingle_eq_zero_iff_commute (P Q : PauliOperator) :
    symplecticProductSingle P Q = 0 ↔ P.mulOp Q = Q.mulOp P := by
  cases P <;> cases Q <;>
    simp [symplecticProductSingle]
  rfl

end PauliOperator

namespace NQubitPauliOperator

/-- Symplectic inner product of two n-qubit Pauli operators (sum over qubits, in ZMod 2).
  Zero iff the two operators commute (as n-qubit Pauli group elements). -/
def symplecticInner (op₁ op₂ : NQubitPauliOperator n) : ZMod 2 :=
  (Finset.univ : Finset (Fin n)).sum (fun i =>
    PauliOperator.symplecticProductSingle (op₁ i) (op₂ i))

end NQubitPauliOperator

/-! ## Group-element level: `⟪p, q⟫ₛ` and `symp`

Statements about Pauli group elements read the symplectic form off the operator parts,
`symplecticInner p.operators q.operators`, and the symplectic vector as
`toSymplectic g.operators`. The scoped notation `⟪p, q⟫ₛ` (scope
`Quantum.NQubitPauliGroupElement`: active in that namespace and under
`open NQubitPauliGroupElement` / `open scoped NQubitPauliGroupElement`) is a **macro onto
exactly that operator-level form** — so `commutes_iff_symplectic_inner_zero`,
`unfold NQubitPauliOperator.symplecticInner` and every existing lemma apply verbatim — and
the delaborator prints the form back as `⟪p, q⟫ₛ`. The `ₛ` suffix keeps it clear of
mathlib's inner-product brackets `⟪x, y⟫_𝕜`.

The delaborator is `scoped` with the notation, so `⟪p, q⟫ₛ` only appears in files that can
parse it; elsewhere the operator-level form prints as is. There is deliberately no
group-level definition behind the notation: the operator-level function is the single
normal form every lemma is stated in. -/

namespace NQubitPauliGroupElement

/-- `⟪p, q⟫ₛ` is the symplectic inner product of the operator parts of the Pauli group
elements `p`, `q`: it elaborates to exactly
`NQubitPauliOperator.symplecticInner p.operators q.operators`. Scoped: enable with
`open scoped NQubitPauliGroupElement`. -/
scoped notation:max "⟪" p ", " q "⟫ₛ" =>
  NQubitPauliOperator.symplecticInner (NQubitPauliGroupElement.operators p)
    (NQubitPauliGroupElement.operators q)

open Lean PrettyPrinter Delaborator SubExpr in
/-- Display `NQubitPauliOperator.symplecticInner p.operators q.operators` as `⟪p, q⟫ₛ`;
any other application of `symplecticInner` keeps the default printer. -/
@[scoped app_delab Quantum.NQubitPauliOperator.symplecticInner]
def delabSymplecticInner : Delab :=
  whenPPOption getPPNotation <| whenNotPPOption getPPExplicit do
    let e ← getExpr
    guard (e.isAppOfArity ``Quantum.NQubitPauliOperator.symplecticInner 3)
    guard ((e.getArg! 1).isAppOfArity ``Quantum.NQubitPauliGroupElement.operators 2)
    guard ((e.getArg! 2).isAppOfArity ``Quantum.NQubitPauliGroupElement.operators 2)
    let p ← withNaryArg 1 <| withNaryArg 1 delab
    let q ← withNaryArg 2 <| withNaryArg 1 delab
    `(⟪$p, $q⟫ₛ)

section RoundTrip

example (p q : NQubitPauliGroupElement n) :
    ⟪p, q⟫ₛ = NQubitPauliOperator.symplecticInner p.operators q.operators := rfl

open Lean Elab Command in
/-- Display test: elaborate `stx` and check that its pretty-printed text is `expected`
(`exact := false`: contains `expected`). Run through `run_cmd` so no `#`-command is needed. -/
private def checkDisplay (stx : Syntax) (expected : String) (exact : Bool := true) :
    CommandElabM Unit :=
  liftTermElabM do
    let e ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVarsNoPostponing
    let s := toString (← Meta.ppExpr (← instantiateMVars e))
    unless (if exact then s == expected else (s.splitOn expected).length > 1) do
      throwError "display test failed:{indentD s}\nexpected{indentD expected}"

run_cmd do
  checkDisplay (← `(fun (p q : NQubitPauliGroupElement 3) => ⟪p, q⟫ₛ))
    "⟪p, q⟫ₛ" (exact := false)
-- a bare operator on one side keeps the default printer
run_cmd do
  checkDisplay
    (← `(fun (op : NQubitPauliOperator 3) (q : NQubitPauliGroupElement 3) =>
          NQubitPauliOperator.symplecticInner op q.operators))
    "op.symplecticInner q.operators" (exact := false)

end RoundTrip

end NQubitPauliGroupElement

namespace NQubitPauliOperator

open scoped NQubitPauliGroupElement

/-- The symplectic vector of the product operator is the pointwise sum (in ZMod 2)
  of the two symplectic vectors. -/
lemma toSymplectic_add (p q : NQubitPauliOperator n) (j : Fin (n + n)) :
    toSymplectic (NQubitPauliGroupElement.mulOp p q).operators j = toSymplectic
    p j + toSymplectic q j := by
  simp only [toSymplectic, NQubitPauliGroupElement.mulOp]
  split_ifs with hj
  · exact congr_arg Prod.fst
      (PauliOperator.toSymplecticSingle_add (p ⟨j.val, hj⟩) (q ⟨j.val, hj⟩))
  · exact congr_arg Prod.snd
      (PauliOperator.toSymplecticSingle_add (p ⟨j.val - n, by omega⟩) (q ⟨j.val - n, by omega⟩))

/-- Two n-qubit Pauli group elements commute iff their symplectic inner product (on the
  operator parts) is 0. The equivalence with the existing `commutes_iff_even_anticommutes`
  is proved later. -/
theorem commutes_iff_symplectic_inner_zero (p q : NQubitPauliGroupElement n) :
    p * q = q * p ↔ ⟪p, q⟫ₛ = 0 := by
  rw [NQubitPauliGroupElement.commutes_iff_even_anticommutes]
  unfold NQubitPauliOperator.symplecticInner;
  have h_symplecticProductSingle : ∀ P Q : PauliOperator,
  PauliOperator.symplecticProductSingle P Q =
  if (P.mulOp Q).phasePower = (Q.mulOp P).phasePower + 2 then 1 else 0 := by
    rintro ( P | P | P | P ) ( Q | Q | Q | Q ) <;> simp +decide;
  rw [ Finset.sum_congr rfl fun i _ => h_symplecticProductSingle _ _ ]
  rw [Finset.sum_boole, ZMod.natCast_eq_zero_iff_even]
  congr! 2
  ext; simp [Quantum.NQubitPauliGroupElement.anticommutesAt]

/-- Two n-qubit Pauli group elements anticommute iff their symplectic inner product
  (on the operator parts) is 1. -/
theorem anticommutes_iff_symplectic_inner_one (p q : NQubitPauliGroupElement n) :
    NQubitPauliGroupElement.Anticommute p q ↔ ⟪p, q⟫ₛ = 1 := by
  rw [NQubitPauliGroupElement.anticommutes_iff_odd_anticommutes, Nat.odd_iff]
  unfold symplecticInner
  have h_symplecticProductSingle : ∀ P Q : PauliOperator,
    PauliOperator.symplecticProductSingle P Q =
      if (P.mulOp Q).phasePower = (Q.mulOp P).phasePower + 2 then 1 else 0 := by
    rintro ( P | P | P | P ) ( Q | Q | Q | Q ) <;> simp +decide
  rw [Finset.sum_congr rfl fun i _ => h_symplecticProductSingle _ _]
  classical
  have hsum_eq : (Finset.univ : Finset (Fin n)).sum (fun i =>
      if NQubitPauliGroupElement.anticommutesAt p.operators q.operators i then 1 else 0) =
    (Finset.univ : Finset (Fin n)).sum (fun i =>
      if ((p.operators i).mulOp (q.operators i)).phasePower =
        ((q.operators i).mulOp (p.operators i)).phasePower + 2 then 1 else 0) :=
    Finset.sum_congr rfl fun i _ => by congr 1
  have heq : (Finset.filter (NQubitPauliGroupElement.anticommutesAt p.operators q.operators)
      Finset.univ).card = (Finset.univ : Finset (Fin n)).sum (fun i =>
      if NQubitPauliGroupElement.anticommutesAt p.operators q.operators i then 1 else 0) := by
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
  have hcast : ((Finset.univ : Finset (Fin n)).sum (fun i =>
      if ((p.operators i).mulOp (q.operators i)).phasePower =
        ((q.operators i).mulOp (p.operators i)).phasePower + 2 then 1 else 0) : ZMod 2) =
    (Finset.filter (NQubitPauliGroupElement.anticommutesAt p.operators q.operators)
      Finset.univ).card := by norm_cast; rw [← hsum_eq, heq]
  rw [hcast]
  rw [ZMod.natCast_eq_one_iff_odd, Nat.odd_iff]

/-- The all-X and all-Z n-qubit operators (with phase 0) anticommute when n is odd:
    symplectic inner product is 1 at each qubit, so total is n ≡ 1 (mod 2). -/
theorem allX_allZ_anticommute (n : ℕ) (hn : Odd n) :
    NQubitPauliGroupElement.Anticommute (⟨0, X n⟩ : NQubitPauliGroupElement n)
      (⟨0, Z n⟩ : NQubitPauliGroupElement n) := by
  rw [anticommutes_iff_symplectic_inner_one]
  unfold symplecticInner
  simp only [X, Z, PauliOperator.symplecticProductSingle, PauliOperator.toSymplecticSingle_X,
    PauliOperator.toSymplecticSingle_Z, one_mul, zero_mul, add_zero]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.smul_one_eq_cast,
    ZMod.natCast_eq_one_iff_odd]
  exact hn

end NQubitPauliOperator

/-! ## Closure → span (general set)

The same proof idea as `mem_closure_implies_symp_in_span` in `SymplecticSpan.lean` (for
`S = listToSet L`), but for an arbitrary set `S`. Used by `IndependentEquiv` for
`S = listToSet L \ {g}`. -/

open NQubitPauliOperator Submodule
open scoped NQubitPauliGroupElement

/-- The symplectic vector of the product is the sum of the symplectic vectors. -/
lemma toSymplectic_mul (p q : NQubitPauliGroupElement n) (j : Fin (n + n)) :
    toSymplectic (p * q).operators j = toSymplectic p.operators j + toSymplectic q.operators j := by
  rw [NQubitPauliGroupElement.mul_eq p q]
  exact toSymplectic_add p.operators q.operators j

/-- The symplectic vector of the identity is zero. -/
lemma toSymplectic_one_operators :
    toSymplectic (1 : NQubitPauliGroupElement n).operators = 0 := by
  ext j
  simp only [NQubitPauliGroupElement.one_operators_def, toSymplectic, Pi.zero_apply,
    NQubitPauliOperator.identity, PauliOperator.toSymplecticSingle_I]
  split_ifs <;> rfl

/-- The inverse has the same operator part, so the same symplectic vector. -/
lemma toSymplectic_inv_operators (g : NQubitPauliGroupElement n) :
    toSymplectic (g⁻¹).operators = toSymplectic g.operators := by
  simp only [NQubitPauliGroupElement.inv_eq, NQubitPauliGroupElement.inv]

/-- If an element is in the subgroup closure of a set, its symplectic vector is in the
  span of the symplectic vectors of the set. -/
lemma toSymplectic_mem_span_of_mem_closure {S : Set (NQubitPauliGroupElement n)}
    {x : NQubitPauliGroupElement n} (hx : x ∈ Subgroup.closure S) :
    toSymplectic x.operators ∈ span (ZMod 2) ((fun g => toSymplectic g.operators) '' S) := by
  let sp := span (ZMod 2) ((fun g => toSymplectic g.operators) '' S)
  suffices toSymplectic x.operators ∈ sp by exact this
  refine Subgroup.closure_induction
    (p := fun k _ => toSymplectic k.operators ∈ sp) ?_ ?_ ?_ ?_ hx
  · exact fun g hg => subset_span (Set.mem_image_of_mem _ hg)
  · change toSymplectic (1 : NQubitPauliGroupElement n).operators ∈ sp
    rw [toSymplectic_one_operators]; exact zero_mem sp
  · intro a b _ _ ha hb
    have heq : toSymplectic (a * b).operators = toSymplectic a.operators +
    toSymplectic b.operators :=
      by ext j; exact toSymplectic_mul a b j
    rw [heq]; exact add_mem ha hb
  · intro a _ ha; rw [toSymplectic_inv_operators]; exact ha

end Quantum
