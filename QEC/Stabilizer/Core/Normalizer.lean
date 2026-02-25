import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Group.Subgroup.Basic
import QEC.Foundations.Foundations
import QEC.Stabilizer.Core.StabilizerGroup
import QEC.Stabilizer.PauliGroup

namespace Quantum
namespace StabilizerGroup

variable {n : ℕ}

open Matrix

/-!
# Normalizer of a stabilizer group

The normalizer of a stabilizer group S (in the unitary group) is the subgroup of n-qubit unitaries
U such that conjugation by U sends the stabilizer group to itself on the codespace: for every g ∈ S,
the operator U† g U stabilizes every state in the codespace. These are exactly
the **logical gates**;
see `LogicalGates.lean` for `IsLogicalGate` and the equivalence with the normalizer.
-/

/-- U is in the normalizer of S iff for every g ∈ S, the conjugated operator U† g U
    stabilizes every state in the codespace. -/
def IsInStabilizerNormalizer (U : NQubitGate n) (S : StabilizerGroup n) : Prop :=
  ∀ g ∈ S.toSubgroup, ∀ ψ : NQubitState n,
    IsInCodespace ψ S → (star U.val * g.toMatrix * U.val).mulVec ψ.val = ψ.val

/-- U is in the normalizer of S iff U maps every codespace state into the codespace. -/
lemma mem_normalizer_iff (U : NQubitGate n) (S : StabilizerGroup n) :
  IsInStabilizerNormalizer U S ↔ ∀ ψ, IsInCodespace ψ S → IsInCodespace (U • ψ) S := by
    constructor
    · intro hU ψ hψ g hg
      have h_inv : (star U.val * g.toMatrix * U.val).mulVec ψ.val = ψ.val := by
        exact hU g hg ψ hψ
      have h_stabilize : Matrix.mulVec g.toMatrix (U.val.mulVec ψ.val) = U.val.mulVec ψ.val := by
        convert congr_arg ( fun x => U.val.mulVec x ) h_inv using 1 ; norm_num [ Matrix.mul_assoc ];
        simp +decide [ ← Matrix.mul_assoc, U.2.2 ]
      exact h_stabilize;
    · intro h g hg ψ hψ
      have h_stabilize : g.toMatrix.mulVec (U • ψ).val = (U • ψ).val := by
        exact h ψ hψ g hg
      have h_unitary : star U.val * U.val = 1 := by
        exact U.2.1;
      convert congr_arg (fun x => star U.val |> Matrix.mulVec <| x) h_stabilize using 1 <;>
        simp +decide [Matrix.mul_assoc, h_unitary]

/-- The codespace of S as a submodule of the n-qubit state space: vectors fixed by every
    stabilizer. -/
def codespaceSubmodule (S : StabilizerGroup n) : Submodule ℂ (NQubitVec n) where
  carrier := { v | ∀ g ∈ S.toSubgroup, Matrix.mulVec g.toMatrix v = v }
  add_mem' := by
    intro a b ha hb g hg
    rw [Matrix.mulVec_add, ha g hg, hb g hg]
  zero_mem' := by
    intro g hg
    rw [Matrix.mulVec_zero]
  smul_mem' := by
    intro c x hx g hg
    rw [Matrix.mulVec_smul, hx g hg]

/-- A state is in the codespace of S iff its vector lies in `codespaceSubmodule S`. -/
lemma mem_codespace_iff_mem_submodule (ψ : NQubitState n) (S : StabilizerGroup n) :
  IsInCodespace ψ S ↔ ψ.val ∈ codespaceSubmodule S := by
  simp [IsInCodespace, IsStabilizedBy, IsStabilizedVec, codespaceSubmodule]

/-- If U is in the normalizer of S, then U maps the codespace submodule into itself. -/
lemma maps_to_codespace_of_mem_normalizer (U : NQubitGate n) (S : StabilizerGroup n)
  (h : IsInStabilizerNormalizer U S) :
  ∀ v ∈ codespaceSubmodule S, Matrix.mulVec U.val v ∈ codespaceSubmodule S := by
    intro v hv; contrapose! h; simp_all +decide [Quantum.StabilizerGroup.codespaceSubmodule]
    obtain ⟨g, hg₁, hg₂⟩ := h; intro H; specialize H g hg₁
    simp_all +decide [← Matrix.mulVec_mulVec]
    specialize H ((1 / Real.sqrt (∑ i : Quantum.NQubitBasis n, ‖v i‖ ^ 2)) • v) ?_ ?_ <;>
      simp_all +decide [Matrix.mulVec_smul]
    all_goals norm_num [mul_pow, ← Finset.mul_sum _ _ _, ← Finset.sum_mul,
      Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => sq_nonneg _] at *
    any_goals rw [inv_mul_cancel₀]; contrapose! hg₂; simp_all +decide [← Matrix.mulVec_mulVec]
    any_goals rw [Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _] at hg₂
      <;> simp_all +decide [funext_iff, Matrix.mulVec, dotProduct]
    · intro g hg; specialize hv g hg
      simp only [Quantum.StabilizerGroup.IsStabilizedBy, Quantum.StabilizerGroup.IsStabilizedVec]
      rw [Matrix.mulVec_smul, hv]
    · replace H := congr_arg (fun x => (Real.sqrt (∑ i : Quantum.NQubitBasis n, ‖v i‖ ^ 2)) • x) H
      simp_all +decide
      by_cases h : Real.sqrt (∑ i : Quantum.NQubitBasis n, ‖v i‖ ^ 2) = 0 <;>
        simp_all +decide [← smul_assoc]
      · rw [Real.sqrt_eq_zero (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h
        simp_all +decide [Finset.sum_eq_zero_iff_of_nonneg]
        exact hg₂ (by ext i; simp +decide [h, Matrix.mulVec, dotProduct])
      · apply_fun (fun x => U.val *ᵥ x) at H; simp_all +decide [← Matrix.mul_assoc]

/-- If U is in the normalizer of S, then U⁻¹ is also in the normalizer. -/
lemma inv_isInStabilizerNormalizer (U : NQubitGate n) (S : StabilizerGroup n)
  (h : IsInStabilizerNormalizer U S) : IsInStabilizerNormalizer U⁻¹ S := by
    have h_surjective : ∀ v ∈ codespaceSubmodule S,
        ∃ w ∈ codespaceSubmodule S, Matrix.mulVec U.val w = v := by
      intro v hv
      have h_surjective :
        LinearMap.range (Matrix.mulVecLin U.val |>.comp
          (Submodule.subtype (codespaceSubmodule S))) = codespaceSubmodule S := by
        apply Submodule.eq_of_le_of_finrank_eq
        · exact Set.range_subset_iff.mpr fun x =>
            maps_to_codespace_of_mem_normalizer U S h _ x.2
        · rw [LinearMap.finrank_range_of_inj]
          intro x y hxy
          apply_fun fun z => U.val⁻¹.mulVec z at hxy; aesop
      replace h_surjective := SetLike.ext_iff.mp h_surjective v; aesop
    intro g hg ψ hψ
    have h_inv : Matrix.mulVec (U⁻¹).val ψ.val ∈ codespaceSubmodule S := by
      obtain ⟨w, hw₁, hw₂⟩ := h_surjective ψ.val
        (by simpa [mem_codespace_iff_mem_submodule] using hψ)
      convert hw₁ using 1
      simp +decide [← hw₂, Matrix.mulVec_mulVec]
    have := h_inv g hg; simp_all +decide [← Matrix.mulVec_mulVec]
    have := U.2.2; simp_all +decide

/-- The normalizer of a stabilizer group: the subgroup of the n-qubit unitary group
    consisting of all U such that U† S U acts as S on the codespace. -/
def stabilizerNormalizer (S : StabilizerGroup n) : Subgroup (NQubitGate n) where
  carrier := { U | IsInStabilizerNormalizer U S }
  one_mem' := by
    intro g hg ψ hψ; simp_all +decide
    exact hψ g hg
  mul_mem' := by
    intro a b ha hb
    convert mem_normalizer_iff _ _ |>.2 _ using 1
    intro ψ hψ
    have h_ab : IsInCodespace (b • ψ) S := by
      exact mem_normalizer_iff b S |>.1 hb ψ hψ
    convert mem_normalizer_iff a S |>.1 ha (b • ψ) h_ab using 1
    erw [Subtype.mk_eq_mk]; aesop
  inv_mem' := by
    intros U hU
    apply inv_isInStabilizerNormalizer U S hU

end StabilizerGroup

end Quantum
