import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.Complex.Basic
import QEC.Foundations.UniformTransversalGate
import QEC.Foundations.Gates
import QEC.Foundations.GateConjugation
import QEC.Stabilizer.PauliGroup.NQubitOperator
import QEC.Stabilizer.PauliGroup.NQubitElement

namespace Quantum

open Matrix
open scoped BigOperators

variable {n : ℕ}

/-!
Conjugation convention: conjugation by a matrix U means U P U† (adjoint on the right).
So we state and prove equalities of the form U * M * star U = ...
-/

/-- Conjugation by a uniform transversal gate (U P U†) distributes to component-wise
single-qubit conjugation. -/
lemma uniformTransversalGateMatrix_conjugation
    (n : ℕ) (G : OneQubitGate) (op : NQubitPauliOperator n) :
    (uniformTransversalGateMatrix n G) * op.toMatrix *
      star (uniformTransversalGateMatrix n G) =
    fun b₁ b₂ =>
      (Finset.univ : Finset (Fin n)).prod
        (fun i => (G.val * (op i).toMatrix * star G.val) (b₁ i) (b₂ i)) := by
  ext b₁ b₂
  simp +decide [ Matrix.mul_apply ]
  simp +decide [ NQubitPauliOperator.toMatrix, uniformTransversalGateMatrix, mul_assoc,
    Finset.sum_mul ]
  have h_fubini :
      ∑ x : NQubitBasis n, ∑ x_1 : NQubitBasis n,
        (∏ i : Fin n, (G.val (b₁ i) (x_1 i))) *
          ((∏ i : Fin n, (op i).toMatrix (x_1 i) (x i)) *
            ∏ i : Fin n, (starRingEnd ℂ) (G.val (b₂ i) (x i))) =
        ∏ i : Fin n, ∑ x : QubitBasis, ∑ x_1 : QubitBasis,
          (G.val (b₁ i) x_1) * ((op i).toMatrix x_1 x) * (starRingEnd ℂ) (G.val (b₂ i) x) := by
    simp +decide only [← Finset.prod_mul_distrib]
    simp +decide only [Finset.sum_sigma', Finset.prod_sum]
    refine Finset.sum_bij ( fun x _ => fun i _ => ⟨ x.fst i, x.snd i ⟩ ) ?_ ?_ ?_ ?_
    <;> simp +decide
    · simp +decide [ funext_iff ]
      exact fun a₁ a₂ h => by cases a₁; cases a₂; aesop
    · exact fun b =>
        ⟨ fun i => b i ( Finset.mem_univ i ) |>.1, fun i => b i ( Finset.mem_univ i ) |>.2,
          funext fun i => funext fun _ => rfl ⟩
    · exact fun a => Finset.prod_congr rfl fun _ _ => by ring
  rw [ h_fubini ]
  exact Finset.prod_congr rfl fun _ _ => by
    rw [ show ( Finset.univ : Finset QubitBasis ) = { 0, 1 } by decide ]
    simp +decide
    ring

/-- `inv_S` conjugates an operator that is pointwise `Z` or `I` to itself (U P U†). -/
lemma uniformTransversalGateMatrix_inv_S_conj_Z_op (n : ℕ) (op : NQubitPauliOperator n)
    (h : ∀ i, op i = .Z ∨ op i = .I) :
    (uniformTransversalGateMatrix n inv_S) * op.toMatrix *
      star (uniformTransversalGateMatrix n inv_S) = op.toMatrix := by
  rw [uniformTransversalGateMatrix_conjugation]
  have h_inv_S_Z : ∀ i : Fin n, inv_S.val * (op i).toMatrix * star inv_S.val = (op i).toMatrix := by
    intro i
    rcases h i with (hZ | hI)
    · simpa [hZ] using inv_S_conj_Z
    · simp [hI]
  ext b₁ b₂
  simp [NQubitPauliOperator.toMatrix, h_inv_S_Z]

/-- `inv_S` conjugates all-`X` to all-`Y` with global phase `(-1)^n` (U P U†). -/
lemma uniformTransversalGateMatrix_inv_S_conj_allX (n : ℕ) :
    (uniformTransversalGateMatrix n inv_S) * (NQubitPauliOperator.X n).toMatrix *
      star (uniformTransversalGateMatrix n inv_S) =
    ((-1 : ℂ) ^ n) • (NQubitPauliOperator.Y n).toMatrix := by
  rw [uniformTransversalGateMatrix_conjugation]
  ext b₁ b₂
  have h_entry :
      ∀ i : Fin n,
        (inv_S.val * (NQubitPauliOperator.X n i).toMatrix * star inv_S.val) (b₁ i) (b₂ i) =
          (-1 : ℂ) * (NQubitPauliOperator.Y n i).toMatrix (b₁ i) (b₂ i) := by
    intro i
    simpa [inv_S_val, NQubitPauliOperator.X, NQubitPauliOperator.Y, NQubitPauliOperator.toMatrix,
      mul_assoc] using congrArg (fun M => M (b₁ i) (b₂ i)) S_adj_X_S
  calc
    (∏ i : Fin n,
      (inv_S.val * (NQubitPauliOperator.X n i).toMatrix * star inv_S.val) (b₁ i) (b₂ i)) =
        ∏ i : Fin n, ((-1 : ℂ) * (NQubitPauliOperator.Y n i).toMatrix (b₁ i) (b₂ i)) := by
          refine Finset.prod_congr rfl ?_
          intro i _
          exact h_entry i
    _ = (∏ _ : Fin n, (-1 : ℂ)) *
          ∏ i : Fin n, (NQubitPauliOperator.Y n i).toMatrix (b₁ i) (b₂ i) := by
          rw [Finset.prod_mul_distrib]
    _ = ((-1 : ℂ) ^ n) *
          ∏ i : Fin n, (NQubitPauliOperator.Y n i).toMatrix (b₁ i) (b₂ i) := by
          simp
    _ = (((-1 : ℂ) ^ n) • (NQubitPauliOperator.Y n).toMatrix) b₁ b₂ := by
          simp [NQubitPauliOperator.toMatrix]

/-- Pointwise image of an n-qubit Pauli operator under a local Pauli map. -/
def pointwiseImage (F : PauliOperator → PauliOperator) (op : NQubitPauliOperator n) :
    NQubitPauliOperator n :=
  fun i => F (op i)

/-- Product of local scalar contributions over qubits for a given n-qubit Pauli operator. -/
noncomputable def pointwiseScalarProduct (c : PauliOperator → ℂ) (op : NQubitPauliOperator n) : ℂ :=
  (Finset.univ : Finset (Fin n)).prod (fun i => c (op i))

/-- If each local conjugation has shape `U P U† = c(P) • F(P)`, then transversal conjugation has
the same shape with product scalar and pointwise image. -/
lemma uniformTransversalGateMatrix_conj_op_of_localRule
    (n : ℕ) (G : OneQubitGate) (op : NQubitPauliOperator n)
    (F : PauliOperator → PauliOperator) (c : PauliOperator → ℂ)
    (Dom : PauliOperator → Prop)
    (hDom : ∀ i, Dom (op i))
    (h_local : ∀ p : PauliOperator,
      Dom p → G.val * p.toMatrix * star G.val = (c p) • (F p).toMatrix) :
    (uniformTransversalGateMatrix n G) * op.toMatrix *
      star (uniformTransversalGateMatrix n G) =
    (pointwiseScalarProduct c op) • (pointwiseImage F op).toMatrix := by
  rw [uniformTransversalGateMatrix_conjugation]
  ext b₁ b₂
  have h_entry :
      ∀ i : Fin n,
        (G.val * (op i).toMatrix * star G.val) (b₁ i) (b₂ i) =
          (c (op i)) * ((pointwiseImage F op i).toMatrix (b₁ i) (b₂ i)) := by
    intro i
    simpa [pointwiseImage] using
      congrArg (fun M => M (b₁ i) (b₂ i)) (h_local (op i) (hDom i))
  calc
    (∏ i : Fin n, (G.val * (op i).toMatrix * star G.val) (b₁ i) (b₂ i)) =
        ∏ i : Fin n, (c (op i)) * ((pointwiseImage F op i).toMatrix (b₁ i) (b₂ i)) := by
          refine Finset.prod_congr rfl ?_
          intro i _
          exact h_entry i
    _ = (∏ i : Fin n, c (op i)) *
          ∏ i : Fin n, ((pointwiseImage F op i).toMatrix (b₁ i) (b₂ i)) := by
          rw [Finset.prod_mul_distrib]
    _ = (pointwiseScalarProduct c op) *
          ∏ i : Fin n, ((pointwiseImage F op i).toMatrix (b₁ i) (b₂ i)) := by
          simp [pointwiseScalarProduct]
    _ = ((pointwiseScalarProduct c op) • (pointwiseImage F op).toMatrix) b₁ b₂ := by
          simp [NQubitPauliOperator.toMatrix]

/-- Gate-level wrapper of `uniformTransversalGateMatrix_conj_op_of_localRule` for scalar-free
local rules (`c p = 1`). -/
lemma uniformTransversalGate_conj_op_gate_of_localRule
    (n : ℕ) (G : OneQubitGate) (op : NQubitPauliOperator n)
    (F : PauliOperator → PauliOperator)
    (Dom : PauliOperator → Prop)
    (hDom : ∀ i, Dom (op i))
    (h_local : ∀ p : PauliOperator, Dom p → G.val * p.toMatrix * star G.val = (F p).toMatrix) :
    conjByGate (uniformTransversalGate n G) op.toGate =
      (pointwiseImage F op).toGate := by
  apply Subtype.ext
  have hmat :
      (uniformTransversalGateMatrix n G) * op.toMatrix * star (uniformTransversalGateMatrix n G) =
        (pointwiseScalarProduct (fun _ => (1 : ℂ)) op) • (pointwiseImage F op).toMatrix := by
    exact uniformTransversalGateMatrix_conj_op_of_localRule n G op F (fun _ => (1 : ℂ))
      Dom hDom (by
      intro p hp
      simpa using h_local p hp)
  simpa [conjByGate_val, pointwiseScalarProduct]
    using hmat

/-- Pointwise image of an X/I Pauli operator under `inv_S` conjugation:
`X ↦ Y`, `I ↦ I`. -/
def invSConjXIImage (op : NQubitPauliOperator n) : NQubitPauliOperator n :=
  fun i => if op i = .X then .Y else .I

/-- Pointwise scalar contribution of `inv_S` conjugation on an X/I Pauli operator:
`X` contributes `-1`, `I` contributes `1`. -/
noncomputable def invSConjXIScalar (op : NQubitPauliOperator n) : ℂ :=
  (Finset.univ : Finset (Fin n)).prod (fun i => if op i = .X then (-1 : ℂ) else 1)

/-- Support of X positions in an n-qubit Pauli operator. -/
def xSupport (op : NQubitPauliOperator n) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun i => op i = .X)

/-- `invSConjXIScalar` is the product over X-support of `-1`. -/
lemma invSConjXIScalar_eq_prod_xSupport (op : NQubitPauliOperator n) :
    invSConjXIScalar op = (xSupport op).prod (fun _ => (-1 : ℂ)) := by
  simp [invSConjXIScalar, xSupport, Finset.prod_ite]

/-- `invSConjXIScalar` equals `(-1)` to the number of X positions. -/
lemma invSConjXIScalar_eq_negOne_pow_xSupportCard (op : NQubitPauliOperator n) :
    invSConjXIScalar op = ((-1 : ℂ) ^ (xSupport op).card) := by
  rw [invSConjXIScalar_eq_prod_xSupport]
  simp

/-- `inv_S` conjugates an X/I-valued n-qubit Pauli operator to the corresponding Y/I image,
up to the product of local `-1` factors (U P U†). -/
lemma uniformTransversalGateMatrix_inv_S_conj_XI_op (n : ℕ) (op : NQubitPauliOperator n)
    (hXI : ∀ i, op i = .X ∨ op i = .I) :
    (uniformTransversalGateMatrix n inv_S) * op.toMatrix *
      star (uniformTransversalGateMatrix n inv_S) =
    (invSConjXIScalar op) • (invSConjXIImage op).toMatrix := by
  refine uniformTransversalGateMatrix_conj_op_of_localRule n inv_S op
    (fun p => if p = .X then .Y else .I) (fun p => if p = .X then (-1 : ℂ) else 1)
    (fun p => p = .X ∨ p = .I) hXI ?_
  intro p hp
  rcases hp with (hX | hI)
  · simp [hX, inv_S_conj_X]
  · simp [hI]

/-- Gate-level wrapper: transversal `inv_S` fixes Z/I-valued operators. -/
lemma uniformTransversalGate_inv_S_conj_Z_op_gate (n : ℕ) (op : NQubitPauliOperator n)
    (h : ∀ i, op i = .Z ∨ op i = .I) :
    conjByGate (uniformTransversalGate n inv_S) op.toGate = op.toGate := by
  apply Subtype.ext
  simpa [conjByGate_val] using uniformTransversalGateMatrix_inv_S_conj_Z_op n op h

/-- Gate-level wrapper: transversal `inv_S` conjugates an X/I-valued operator to its
pointwise Y/I image up to scalar in matrix form. -/
lemma uniformTransversalGate_inv_S_conj_XI_op_gate
    (n : ℕ) (op : NQubitPauliOperator n) (hXI : ∀ i, op i = .X ∨ op i = .I) :
    (conjByGate (uniformTransversalGate n inv_S) op.toGate).val =
      ((invSConjXIScalar op) • (invSConjXIImage op).toMatrix) := by
  simpa [conjByGate_val] using uniformTransversalGateMatrix_inv_S_conj_XI_op n op hXI

/-- Element-level helper for transversal `inv_S` on phase-0 X/I elements (U P U†). -/
lemma uniformTransversalGateMatrix_inv_S_conj_element_XI_phase0
    (n : ℕ) (g : NQubitPauliGroupElement n)
    (h_phase : g.phasePower = 0)
    (hXI : ∀ i, g.operators i = .X ∨ g.operators i = .I) :
    (uniformTransversalGateMatrix n inv_S) * g.toMatrix *
      star (uniformTransversalGateMatrix n inv_S) =
    (invSConjXIScalar g.operators) •
      (NQubitPauliGroupElement.ofOperator (invSConjXIImage g.operators)).toMatrix := by
  unfold NQubitPauliGroupElement.toMatrix
  simp [h_phase]
  simpa using uniformTransversalGateMatrix_inv_S_conj_XI_op n g.operators hXI

/-- Gate-level matrix-view helper for transversal `inv_S` on phase-0 X/I elements. -/
lemma uniformTransversalGate_inv_S_conj_element_XI_phase0_gate
    (n : ℕ) (g : NQubitPauliGroupElement n)
    (h_phase : g.phasePower = 0)
    (hXI : ∀ i, g.operators i = .X ∨ g.operators i = .I) :
    (conjByGate (uniformTransversalGate n inv_S) g.gate).val =
      (invSConjXIScalar g.operators) •
        (NQubitPauliGroupElement.ofOperator (invSConjXIImage g.operators)).toMatrix := by
  simpa [conjByGate_val, NQubitPauliGroupElement.gate_val] using
    uniformTransversalGateMatrix_inv_S_conj_element_XI_phase0 n g h_phase hXI

/-- Single-qubit: `H P H† = swapXZ(P)` for `P ≠ Y`
(conjugation = adjoint on the right). -/
lemma H_conj_mul_toMatrix_mul_H_adj
    (p : PauliOperator) (h : p ≠ .Y) :
    H.val * p.toMatrix * star H.val = (PauliOperator.swapXZ p).toMatrix := by
  cases p <;> simp_all +decide [PauliOperator.swapXZ]
  · simpa using (Matrix.mem_unitaryGroup_iff.1 H.2)
  · simpa using H_conj_X
  · simpa using H_conj_Z

/-- Conjugation of n-qubit Pauli (no Y) by transversal H equals transversalSwapXZ (U P U†). -/
lemma uniformTransversalGateMatrix_H_conj_op (n : ℕ) (op : NQubitPauliOperator n)
    (h : ∀ i, op i ≠ .Y) :
    (uniformTransversalGateMatrix n H) * op.toMatrix * star (uniformTransversalGateMatrix n H) =
      (NQubitPauliOperator.transversalSwapXZ op).toMatrix := by
  rw [uniformTransversalGateMatrix_conjugation]
  have h_conj : ∀ i,
      (H.val * (op i).toMatrix * star H.val) = (PauliOperator.swapXZ (op i)).toMatrix := by
    intro i
    exact H_conj_mul_toMatrix_mul_H_adj _ (h i)
  aesop

/-- Gate-level wrapper: transversal H conjugates an n-qubit Pauli operator (without Y entries)
to its pointwise `swapXZ` image. -/
lemma uniformTransversalGate_H_conj_op_gate (n : ℕ) (op : NQubitPauliOperator n)
    (h : ∀ i, op i ≠ .Y) :
    conjByGate (uniformTransversalGate n H) op.toGate =
      (NQubitPauliOperator.transversalSwapXZ op).toGate := by
  refine uniformTransversalGate_conj_op_gate_of_localRule n H op PauliOperator.swapXZ
    (fun p => p ≠ .Y) h ?_
  intro p hp
  exact H_conj_mul_toMatrix_mul_H_adj p hp

end Quantum
