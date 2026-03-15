import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.LinearAlgebra.UnitaryGroup
import QEC.Foundations.Basic
import QEC.Foundations.Gates

namespace Quantum
open Matrix
open scoped BigOperators

/-!
# Uniform transversal gate

A **uniform transversal** (physical) gate applies the same one-qubit gate `G` to every
physical qubit: the n-qubit unitary is the n-fold tensor product G ⊗ G ⊗ … ⊗ G.
This is the standard "apply G on each qubit" construction used e.g. for transversal
Hadamard and phase in the Steane code.

More general transversal gates (different gates per qubit or block) are not defined here.
-/

/-- Matrix of the uniform transversal gate: apply `G` on each qubit (Kronecker product). -/
noncomputable def uniformTransversalGateMatrix (n : ℕ) (G : OneQubitGate) :
    Matrix (NQubitBasis n) (NQubitBasis n) ℂ :=
  fun b₁ b₂ => (Finset.univ : Finset (Fin n)).prod (fun i => G.val (b₁ i) (b₂ i))

/-- The uniform transversal gate matrix is unitary (G⊗n is unitary when G is). -/
lemma uniformTransversalGateMatrix_mem_unitaryGroup (n : ℕ) (G : OneQubitGate) :
    uniformTransversalGateMatrix n G ∈ Matrix.unitaryGroup (NQubitBasis n) ℂ := by
  constructor
  · ext b₁ b₂; simp +decide [Matrix.mul_apply, Matrix.one_apply]
    have h_unitary :
      ∀ i : Fin n,
        ∑ x : QubitBasis, (starRingEnd ℂ) (G.val x (b₁ i)) * G.val x (b₂ i) =
          if b₁ i = b₂ i then 1 else 0 := by
      intro i
      have h_unitary :
        ∑ x : QubitBasis, (starRingEnd ℂ) (G.val x (b₁ i)) * G.val x (b₂ i) =
          (star G.val * G.val) (b₁ i) (b₂ i) := by
        simp +decide [Matrix.mul_apply]
      have := G.2.2; aesop
    convert Finset.prod_congr rfl fun i _ => h_unitary i using 1
    any_goals exact Finset.univ
    · rw [Finset.prod_sum]
      refine Finset.sum_bij (fun p _ => fun i _ => p i) ?_ ?_ ?_ ?_ <;>
        simp +decide [Finset.mem_univ]
      · simp +decide [funext_iff]
      · exact fun b => ⟨fun i => b i (Finset.mem_univ i), funext fun i => rfl⟩
      · unfold uniformTransversalGateMatrix; simp +decide [Finset.prod_mul_distrib]
    · by_cases h : b₁ = b₂ <;> simp +decide [h]
      rw [Finset.prod_eq_zero (Finset.mem_univ (Classical.choose (Function.ne_iff.mp h)))]
      simp +decide [Classical.choose_spec (Function.ne_iff.mp h)]
  · ext i j; simp +decide [Matrix.mul_apply]
    have h_GG_star :
      ∀ i j : QubitBasis,
        ∑ k : QubitBasis, G.val i k * starRingEnd ℂ (G.val j k) = if i = j then 1 else 0 := by
      have := G.2.2
      intro i j; replace this := congr_fun (congr_fun this i) j
      simp_all +decide [Matrix.mul_apply, Matrix.one_apply]
    have h_prod :
      ∑ x : NQubitBasis n,
          (∏ k : Fin n, G.val (i k) (x k)) *
            (∏ k : Fin n, starRingEnd ℂ (G.val (j k) (x k))) =
        ∏ k : Fin n, ∑ x : QubitBasis, G.val (i k) x * starRingEnd ℂ (G.val (j k) x) := by
      simp +decide only [Finset.prod_sum, Finset.prod_mul_distrib]
      refine Finset.sum_bij (fun x _ => fun k _ => x k) ?_ ?_ ?_ ?_ <;> simp +decide
      · simp +decide [funext_iff]
      · exact fun b => ⟨fun k => b k (Finset.mem_univ k), funext fun k => rfl⟩
    convert h_prod using 1
    · unfold uniformTransversalGateMatrix; simp +decide
    · by_cases hij : i = j <;> simp +decide [hij, h_GG_star]
      · simp +decide [hij, Matrix.one_apply]
      · rw [Finset.prod_eq_zero (Finset.mem_univ (Classical.choose (Function.ne_iff.mp hij)))]
        simp +decide [Classical.choose_spec (Function.ne_iff.mp hij)]

/-- Uniform transversal gate: apply the same one-qubit gate `G` on every physical qubit. -/
noncomputable def uniformTransversalGate (n : ℕ) (G : OneQubitGate) : NQubitGate n :=
  ⟨uniformTransversalGateMatrix n G, uniformTransversalGateMatrix_mem_unitaryGroup n G⟩

end Quantum
