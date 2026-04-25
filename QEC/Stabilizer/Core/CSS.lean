import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Tactic
import QEC.Stabilizer.PauliGroup

namespace Quantum
open scoped BigOperators

/-!
# CSS utilities

This file introduces reusable predicates and closure lemmas for working with **CSS-style**
stabilizer generators:

- Z-type single-qubit operators: `I` or `Z`
- X-type single-qubit operators: `I` or `X`

and their n-qubit liftings, plus “typed element” invariants for `NQubitPauliGroupElement n`
that are stable under subgroup generation (`Subgroup.closure`).

These lemmas are intended to make proofs for Shor/Steane/surface codes modular: you prove
your generators are Z-type or X-type (and phase-0), and then closure induction gives the
same property for the entire generated subgroup.
-/

namespace PauliOperator

/-- Z-type single-qubit Pauli: `I` or `Z`. -/
def IsZType (p : PauliOperator) : Prop :=
  p = PauliOperator.I ∨ p = PauliOperator.Z

/-- X-type single-qubit Pauli: `I` or `X`. -/
def IsXType (p : PauliOperator) : Prop :=
  p = PauliOperator.I ∨ p = PauliOperator.X

/-- The identity `I` is Z-type. -/
lemma IsZType_I : IsZType PauliOperator.I := Or.inl rfl

/-- The Pauli `Z` is Z-type. -/
lemma IsZType_Z : IsZType PauliOperator.Z := Or.inr rfl

/-- The identity `I` is X-type. -/
lemma IsXType_I : IsXType PauliOperator.I := Or.inl rfl

/-- The Pauli `X` is X-type. -/
lemma IsXType_X : IsXType PauliOperator.X := Or.inr rfl

/-- The only single-qubit Pauli that is both Z-type and X-type is `I`. -/
lemma eq_I_of_IsZType_and_IsXType {p : PauliOperator} (hz : IsZType p) (hx : IsXType p) :
    p = PauliOperator.I := by
  match hz, hx with
  | Or.inl hI, Or.inl _ => exact hI
  | Or.inl hI, Or.inr hX => exact absurd (hI.symm.trans hX) (by decide : I ≠ X)
  | Or.inr hZ, Or.inl hI => exact absurd (hZ.symm.trans hI) (by decide : Z ≠ I)
  | Or.inr hZ, Or.inr hX => exact absurd (hZ.symm.trans hX) (by decide : Z ≠ X)

/-!
## Closure of types under single-qubit multiplication (`mulOp`)
-/

/-- Multiplying two Z-type single-qubit Paulis contributes no phase in `mulOp`. -/
lemma mulOp_phasePower_zero_of_IsZType {p q : PauliOperator}
    (hp : IsZType p) (hq : IsZType q) :
    (p.mulOp q).phasePower = 0 := by
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> simp [PauliOperator.mulOp]

/-- Multiplying two Z-type single-qubit Paulis stays Z-type at the operator level. -/
lemma mulOp_operator_IsZType_of_IsZType {p q : PauliOperator}
    (hp : IsZType p) (hq : IsZType q) :
    IsZType (p.mulOp q).operator := by
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> simp [IsZType, PauliOperator.mulOp]

/-- Multiplying two X-type single-qubit Paulis contributes no phase in `mulOp`. -/
lemma mulOp_phasePower_zero_of_IsXType {p q : PauliOperator}
    (hp : IsXType p) (hq : IsXType q) :
    (p.mulOp q).phasePower = 0 := by
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> simp [PauliOperator.mulOp]

/-- Multiplying two X-type single-qubit Paulis stays X-type at the operator level. -/
lemma mulOp_operator_IsXType_of_IsXType {p q : PauliOperator}
    (hp : IsXType p) (hq : IsXType q) :
    IsXType (p.mulOp q).operator := by
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> simp [IsXType, PauliOperator.mulOp]

/-!
## Cross-type fact: Z-type times X-type is `I` iff both are `I`
-/

/-- If `p` is Z-type and `q` is X-type, then `(p.mulOp q)` has operator `I`
iff `p = I` and `q = I` (i.e. no nontrivial cancellation across Z/X types). -/
lemma mulOp_operator_eq_I_iff_of_types {p q : PauliOperator}
    (hp : IsZType p) (hq : IsXType q) :
    (p.mulOp q).operator = PauliOperator.I ↔ p = PauliOperator.I ∧ q = PauliOperator.I := by
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> simp [PauliOperator.mulOp]

end PauliOperator

namespace NQubitPauliOperator

/-- Z-type n-qubit Pauli operator: every component is `I` or `Z`. -/
def IsZType {n : ℕ} (op : NQubitPauliOperator n) : Prop :=
  ∀ i, PauliOperator.IsZType (op i)

/-- X-type n-qubit Pauli operator: every component is `I` or `X`. -/
def IsXType {n : ℕ} (op : NQubitPauliOperator n) : Prop :=
  ∀ i, PauliOperator.IsXType (op i)

/-- The n-qubit identity operator is Z-type (all components are `I`). -/
lemma IsZType_identity {n : ℕ} : IsZType (NQubitPauliOperator.identity n) := by
  intro _; exact PauliOperator.IsZType_I

/-- The n-qubit identity operator is X-type (all components are `I`). -/
lemma IsXType_identity {n : ℕ} : IsXType (NQubitPauliOperator.identity n) := by
  intro _; exact PauliOperator.IsXType_I

/-!
## Cross-type fact at n qubits
-/

/-- If `p` is Z-type and `q` is X-type, then the operator part of `mulOp p q` is the
n-qubit identity iff both `p` and `q` are the n-qubit identity operators. -/
lemma mulOp_operators_eq_identity_iff_of_types {n : ℕ} {p q : NQubitPauliOperator n}
    (hp : IsZType p) (hq : IsXType q) :
    (NQubitPauliGroupElement.mulOp p q).operators = NQubitPauliOperator.identity n ↔
      p = NQubitPauliOperator.identity n ∧ q = NQubitPauliOperator.identity n := by
  constructor
  · intro h
    have hcomp : ∀ i : Fin n, p i = PauliOperator.I ∧ q i = PauliOperator.I := by
      intro i
      have hi :
          ((p i).mulOp (q i)).operator = PauliOperator.I := by
        have := congrArg (fun op => op i) h
        simpa [NQubitPauliGroupElement.mulOp] using this
      exact (PauliOperator.mulOp_operator_eq_I_iff_of_types (hp i) (hq i)).1 hi
    refine ⟨?_, ?_⟩
    · ext i; simpa using (hcomp i).1
    · ext i; simpa using (hcomp i).2
  · rintro ⟨rfl, rfl⟩
    ext i
    simp [NQubitPauliGroupElement.mulOp, NQubitPauliOperator.identity, PauliOperator.mulOp]

end NQubitPauliOperator

namespace NQubitPauliGroupElement

/-!
## Typed elements (phase-0 + typed operators)
-/

/-- Z-type group element: phase 0 and Z-type operator tensor. -/
def IsZTypeElement {n : ℕ} (g : NQubitPauliGroupElement n) : Prop :=
  g.phasePower = 0 ∧ NQubitPauliOperator.IsZType g.operators

/-- X-type group element: phase 0 and X-type operator tensor. -/
def IsXTypeElement {n : ℕ} (g : NQubitPauliGroupElement n) : Prop :=
  g.phasePower = 0 ∧ NQubitPauliOperator.IsXType g.operators

/-!
## Operator-only multiplication preserves Z/X type and contributes zero phase
-/

/-- For Z-type n-qubit operators `p q`, the `mulOp p q` phase contribution is zero. -/
lemma mulOp_phasePower_zero_of_IsZType {n : ℕ} {p q : NQubitPauliOperator n}
    (hp : NQubitPauliOperator.IsZType p) (hq : NQubitPauliOperator.IsZType q) :
    (NQubitPauliGroupElement.mulOp p q).phasePower = 0 := by
  classical
  simp [NQubitPauliGroupElement.mulOp, PauliOperator.mulOp_phasePower_zero_of_IsZType (hp _) (hq _),
    Finset.sum_eq_zero]

/-- For Z-type n-qubit operators `p q`, the operator part of `mulOp p q` is Z-type. -/
lemma mulOp_operators_IsZType_of_IsZType {n : ℕ} {p q : NQubitPauliOperator n}
    (hp : NQubitPauliOperator.IsZType p) (hq : NQubitPauliOperator.IsZType q) :
    NQubitPauliOperator.IsZType (NQubitPauliGroupElement.mulOp p q).operators := by
  intro i
  simp [NQubitPauliGroupElement.mulOp,
    PauliOperator.mulOp_operator_IsZType_of_IsZType (hp i) (hq i)]

/-- For X-type n-qubit operators `p q`, the `mulOp p q` phase contribution is zero. -/
lemma mulOp_phasePower_zero_of_IsXType {n : ℕ} {p q : NQubitPauliOperator n}
    (hp : NQubitPauliOperator.IsXType p) (hq : NQubitPauliOperator.IsXType q) :
    (NQubitPauliGroupElement.mulOp p q).phasePower = 0 := by
  classical
  simp [NQubitPauliGroupElement.mulOp, PauliOperator.mulOp_phasePower_zero_of_IsXType (hp _) (hq _),
    Finset.sum_eq_zero]

/-- For X-type n-qubit operators `p q`, the operator part of `mulOp p q` is X-type. -/
lemma mulOp_operators_IsXType_of_IsXType {n : ℕ} {p q : NQubitPauliOperator n}
    (hp : NQubitPauliOperator.IsXType p) (hq : NQubitPauliOperator.IsXType q) :
    NQubitPauliOperator.IsXType (NQubitPauliGroupElement.mulOp p q).operators := by
  intro i
  simp [NQubitPauliGroupElement.mulOp,
    PauliOperator.mulOp_operator_IsXType_of_IsXType (hp i) (hq i)]

/-!
## Closure of typed elements under group operations
-/

/-- The group identity element is Z-type (phase 0, operator identity). -/
lemma IsZTypeElement_one {n : ℕ} : IsZTypeElement (1 : NQubitPauliGroupElement n) := by
  constructor
  · simp
  · simpa using (NQubitPauliOperator.IsZType_identity (n := n))

/-- The group identity element is X-type (phase 0, operator identity). -/
lemma IsXTypeElement_one {n : ℕ} : IsXTypeElement (1 : NQubitPauliGroupElement n) := by
  constructor
  · simp
  · simpa using (NQubitPauliOperator.IsXType_identity (n := n))

/-- Z-type elements are closed under group multiplication. -/
lemma IsZTypeElement_mul {n : ℕ} {g h : NQubitPauliGroupElement n}
    (hg : IsZTypeElement g) (hh : IsZTypeElement h) :
    IsZTypeElement (g * h) := by
  constructor
  · have hmulOp : (NQubitPauliGroupElement.mulOp g.operators h.operators).phasePower = 0 :=
      mulOp_phasePower_zero_of_IsZType hg.2 hh.2
    simp [NQubitPauliGroupElement.mul, hg.1, hh.1, hmulOp]
  · simpa [NQubitPauliGroupElement.mul] using
      (mulOp_operators_IsZType_of_IsZType (p := g.operators) (q := h.operators) hg.2 hh.2)

/-- X-type elements are closed under group multiplication. -/
lemma IsXTypeElement_mul {n : ℕ} {g h : NQubitPauliGroupElement n}
    (hg : IsXTypeElement g) (hh : IsXTypeElement h) :
    IsXTypeElement (g * h) := by
  constructor
  · have hmulOp : (NQubitPauliGroupElement.mulOp g.operators h.operators).phasePower = 0 :=
      mulOp_phasePower_zero_of_IsXType hg.2 hh.2
    simp [NQubitPauliGroupElement.mul, hg.1, hh.1, hmulOp]
  · simpa [NQubitPauliGroupElement.mul] using
      (mulOp_operators_IsXType_of_IsXType (p := g.operators) (q := h.operators) hg.2 hh.2)

/-- Z-type elements are closed under group inversion. -/
lemma IsZTypeElement_inv {n : ℕ} {g : NQubitPauliGroupElement n}
    (hg : IsZTypeElement g) :
    IsZTypeElement (g⁻¹) := by
  constructor
  · simp [NQubitPauliGroupElement.inv, hg.1]
  · simpa [NQubitPauliGroupElement.inv] using hg.2

/-- X-type elements are closed under group inversion. -/
lemma IsXTypeElement_inv {n : ℕ} {g : NQubitPauliGroupElement n}
    (hg : IsXTypeElement g) :
    IsXTypeElement (g⁻¹) := by
  constructor
  · simp [NQubitPauliGroupElement.inv, hg.1]
  · simpa [NQubitPauliGroupElement.inv] using hg.2

/-!
## Closure induction: generators ⇒ closure
-/

/-- If every generator in `S` is Z-type, then every element of `Subgroup.closure S` is Z-type. -/
theorem IsZTypeElement_of_mem_closure {n : ℕ} {S : Set (NQubitPauliGroupElement n)}
    (hS : ∀ g, g ∈ S → IsZTypeElement g) :
    ∀ g, g ∈ Subgroup.closure S → IsZTypeElement g := by
  intro g hg
  refine Subgroup.closure_induction
    (p := fun g (_ : g ∈ Subgroup.closure S) => IsZTypeElement g)
    (fun x hx => hS x hx)
    (by simpa using (IsZTypeElement_one (n := n)))
    (fun x y _ _ hx hy => IsZTypeElement_mul hx hy)
    (fun x _ hx => IsZTypeElement_inv hx)
    hg

/-- If every generator in `S` is X-type, then every element of `Subgroup.closure S` is X-type. -/
theorem IsXTypeElement_of_mem_closure {n : ℕ} {S : Set (NQubitPauliGroupElement n)}
    (hS : ∀ g, g ∈ S → IsXTypeElement g) :
    ∀ g, g ∈ Subgroup.closure S → IsXTypeElement g := by
  intro g hg
  refine Subgroup.closure_induction
    (p := fun g (_ : g ∈ Subgroup.closure S) => IsXTypeElement g)
    (fun x hx => hS x hx)
    (by simpa using (IsXTypeElement_one (n := n)))
    (fun x y _ _ hx hy => IsXTypeElement_mul hx hy)
    (fun x _ hx => IsXTypeElement_inv hx)
    hg

/-- The only n-qubit Pauli group element that is both Z-type and X-type is the identity.
  Used to show that an X-type logical operator is not in a Z-only stabilizer (and vice versa). -/
theorem eq_one_of_IsZTypeElement_and_IsXTypeElement {n : ℕ} {g : NQubitPauliGroupElement n}
    (hz : IsZTypeElement g) (hx : IsXTypeElement g) : g = 1 := by
  apply NQubitPauliGroupElement.ext g 1
  · simp [hz.1]
  · ext i
    exact PauliOperator.eq_I_of_IsZType_and_IsXType (hz.2 i) (hx.2 i)

/-!
## Identity-operators criterion for a Z*X product

This lemma is the algebraic core used to rule out `negIdentity` in CSS-generated stabilizer groups.
-/

/-- If `z` is Z-type and `x` is X-type and their product has identity operator tensor,
then the whole product is the group identity.

This is the key “no `-I`” step for CSS stabilizer constructions: a Z-part times an X-part
can only have all-`I` operator tensor in the trivial case. -/
lemma z_mul_x_eq_one_of_operators_eq_identity {n : ℕ}
    (z x : NQubitPauliGroupElement n)
    (hz : IsZTypeElement z) (hx : IsXTypeElement x)
    (h_op : (z * x).operators = NQubitPauliOperator.identity n) :
    z * x = 1 := by
  have h_op' :
      (NQubitPauliGroupElement.mulOp z.operators x.operators).operators =
        NQubitPauliOperator.identity n := by
    simpa [NQubitPauliGroupElement.mul] using h_op
  have h_id_ops :
      z.operators = NQubitPauliOperator.identity n ∧
        x.operators = NQubitPauliOperator.identity n := by
    simpa using
      (NQubitPauliOperator.mulOp_operators_eq_identity_iff_of_types
            (p := z.operators) (q := x.operators) hz.2 hx.2).1 h_op'
  have hz1 : z = 1 := by
    apply NQubitPauliGroupElement.ext z 1
    · simp [hz.1]
    · simp [h_id_ops.1]
  have hx1 : x = 1 := by
    apply NQubitPauliGroupElement.ext x 1
    · simp [hx.1]
    · simp [h_id_ops.2]
  simp [hz1, hx1, -NQubitPauliGroupElement.mul_eq]

end NQubitPauliGroupElement

end Quantum
