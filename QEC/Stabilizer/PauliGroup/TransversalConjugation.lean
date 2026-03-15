import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.Complex.Basic
import QEC.Foundations.UniformTransversalGate
import QEC.Foundations.Gates
import QEC.Foundations.GateConjugation
import QEC.Stabilizer.PauliGroup.NQubitOperator

namespace Quantum

open Matrix
open scoped BigOperators

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
  have h_inv_S_Z :
      ∀ i : Fin n,
        (Quantum.inv_S : OneQubitGate).val * (op i).toMatrix *
            star (Quantum.inv_S : OneQubitGate).val =
          (op i).toMatrix := by
    intro i
    specialize h i
    rcases h with ( h | h ) <;> simp +decide [ h ]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [ Quantum.inv_S, Quantum.Zmat, Matrix.mul_apply, Matrix.adjugate_apply,
        Matrix.det_fin_two ]
    · norm_num [ Complex.ext_iff, Quantum.Smat ]
    · unfold Quantum.Smat
      norm_num [ Complex.ext_iff ]
    · unfold Quantum.Smat
      norm_num [ Complex.ext_iff ]
    · norm_num [ Quantum.Smat ]
  aesop

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

end Quantum
