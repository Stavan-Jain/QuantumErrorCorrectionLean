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
# Logical gate group

The **logical gate group** for a stabilizer group S is the subgroup of n-qubit unitaries that
map the codespace to itself (i.e. **logical gates**). Equivalently, for every g ∈ S the conjugated
operator U g U† stabilizes every state in the codespace (adjoint on the right).
See `LogicalGates.lean` for `IsLogicalGate`.
-/

/-- Conjugation formulation: for every g ∈ S, U g U† stabilizes every codespace state. -/
private def PreservesCodespaceConjugation (U : NQubitGate n) (S : StabilizerGroup n) : Prop :=
  ∀ g ∈ S.toSubgroup, ∀ ψ : NQubitState n,
    IsInCodespace ψ S → (U.val * g.toMatrix * star U.val).mulVec ψ.val = ψ.val

/-- Conjugation formulation is equivalent to mapping the codespace to itself. -/
private lemma conjugation_iff_maps_codespace (U : NQubitGate n) (S : StabilizerGroup n) :
  PreservesCodespaceConjugation U S ↔ ∀ ψ, IsInCodespace ψ S → IsInCodespace (U • ψ) S := by
  sorry

/-- The codespace of S as a submodule of the n-qubit state space. -/
def codespaceSubmodule (S : StabilizerGroup n) : Submodule ℂ (NQubitVec n) where
  carrier := { v | ∀ g ∈ S.toSubgroup, Matrix.mulVec g.toMatrix v = v }
  add_mem' := by intro a b ha hb g hg; rw [Matrix.mulVec_add, ha g hg, hb g hg]
  zero_mem' := by intro g hg; rw [Matrix.mulVec_zero]
  smul_mem' := by intro c x hx g hg; rw [Matrix.mulVec_smul, hx g hg]

/-- A state is in the codespace iff its vector lies in `codespaceSubmodule S`. -/
lemma mem_codespace_iff_mem_submodule (ψ : NQubitState n) (S : StabilizerGroup n) :
  IsInCodespace ψ S ↔ ψ.val ∈ codespaceSubmodule S := by
  simp [IsInCodespace, IsStabilizedBy, IsStabilizedVec, codespaceSubmodule]

/-- If U preserves the codespace (conjugation formulation),
then U maps the submodule into itself. -/
private lemma maps_to_codespace_of_conjugation (U : NQubitGate n) (S : StabilizerGroup n)
  (h : PreservesCodespaceConjugation U S) :
  ∀ v ∈ codespaceSubmodule S,
    Matrix.mulVec U.val v ∈ codespaceSubmodule S := by
  contrapose! h;
  obtain ⟨v, hv₁, hv₂⟩ := h;
  simp [Quantum.StabilizerGroup.PreservesCodespaceConjugation];
  contrapose! hv₂;
  intro g hg;
  have h_conj : ∀ ψ : NQubitState n, IsInCodespace ψ S → IsInCodespace (U • ψ) S := by
    apply Classical.byContradiction
    intro h_contra;
    push_neg at h_contra;
    obtain ⟨ ψ, hψ₁, hψ₂ ⟩ := h_contra;
    apply hψ₂;
    convert StabilizerGroup.conjugation_iff_maps_codespace U S |>.1 _ ψ hψ₁ using 1;
    convert hv₂ using 1;
    unfold Quantum.StabilizerGroup.PreservesCodespaceConjugation; aesop;
  by_cases hv : ∑ i, ‖v i‖ ^ 2 = 0;
  · simp_all +decide [ Finset.sum_eq_zero_iff_of_nonneg, sq_nonneg ];
    ext i; simp +decide [ hv, Matrix.mulVec, dotProduct ] ;
  · have := h_conj ⟨ ( 1 / Real.sqrt ( ∑ i, ‖v i‖ ^ 2 ) ) • v, ?_ ⟩ ?_ <;> simp_all +decide [ Matrix.mulVec_smul ];
    any_goals simp +decide [ mul_pow, abs_of_nonneg ( Real.sqrt_nonneg _ ), Real.sq_sqrt ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ), hv ];
    any_goals rw [ ← Finset.mul_sum _ _ _, inv_mul_cancel₀ hv ];
    · have := this g hg; simp_all +decide [ Matrix.mulVec_smul, smul_smul ] ;
      convert congr_arg ( fun x : NQubitVec n => ( Real.sqrt ( ∑ i, ‖v i‖ ^ 2 ) ) • x ) this using 1 <;> norm_num [ Matrix.mulVec_smul, smul_smul ];
      · rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.sqrt_pos.mpr ( lt_of_le_of_ne ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ( Ne.symm hv ) ) ) ), one_smul ];
      · rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.sqrt_pos.mpr ( lt_of_le_of_ne ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ( Ne.symm hv ) ) ) ), one_smul ];
    · intro g hg; specialize hv₁ g hg; simp_all +decide [ Matrix.mulVec_smul ] ;
      simp_all +decide [ IsStabilizedBy, IsStabilizedVec ];
      rw [ Matrix.mulVec_smul, hv₁ ]

/-- The logical gate group for S: unitaries that map the codespace to itself. -/
def logicalGateGroup (S : StabilizerGroup n) : Subgroup (NQubitGate n) where
  carrier := { U | PreservesCodespaceConjugation U S }
  one_mem' := by intro g hg ψ hψ; simp; exact hψ g hg
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [conjugation_iff_maps_codespace (a * b) S] at ⊢
    rw [conjugation_iff_maps_codespace a S] at ha
    rw [conjugation_iff_maps_codespace b S] at hb
    intro ψ hψ
    have hbψ : IsInCodespace (b • ψ) S := hb ψ hψ
    have heq : (a * b) • ψ = a • (b • ψ) :=
      Subtype.ext (by simp only [smul_QState_val, gate_mul_val]; rw [mulVec_mulVec])
    rw [heq]
    exact ha (b • ψ) hbψ
  inv_mem' := by
    intro U hU
    simp only [Set.mem_setOf_eq] at hU ⊢
    have h_surjective : ∀ v ∈ codespaceSubmodule S,
        ∃ w ∈ codespaceSubmodule S, Matrix.mulVec U.val w = v := by
      intro v hv
      have h_surjective :
        LinearMap.range (Matrix.mulVecLin U.val |>.comp
          (Submodule.subtype (codespaceSubmodule S))) = codespaceSubmodule S := by
        apply Submodule.eq_of_le_of_finrank_eq
        · exact Set.range_subset_iff.mpr fun x =>
            maps_to_codespace_of_conjugation U S hU _ x.2
        · rw [LinearMap.finrank_range_of_inj]
          intro x y hxy
          apply_fun fun z => U.val⁻¹.mulVec z at hxy; aesop
      replace h_surjective := SetLike.ext_iff.mp h_surjective v; aesop
    rw [conjugation_iff_maps_codespace (U⁻¹) S]
    intro ψ hψ g hg
    have h_inv : Matrix.mulVec (U⁻¹).val ψ.val ∈ codespaceSubmodule S := by
      obtain ⟨w, hw₁, hw₂⟩ := h_surjective ψ.val
        (by simpa [mem_codespace_iff_mem_submodule] using hψ)
      convert hw₁ using 1
      simp +decide [← hw₂, Matrix.mulVec_mulVec]
    have := h_inv g hg
    simp_all only [IsStabilizedBy, IsStabilizedVec, smul_QState_val]


/-- U is in the logical gate group iff U maps every codespace state into the codespace. -/
lemma mem_logicalGateGroup_iff (U : NQubitGate n) (S : StabilizerGroup n) :
  U ∈ logicalGateGroup S ↔ ∀ ψ, IsInCodespace ψ S → IsInCodespace (U • ψ) S := by
  simp only [logicalGateGroup, Subgroup.mem_mk]
  exact conjugation_iff_maps_codespace U S

/-- U is in the logical gate group iff for every g ∈ S, U g U† stabilizes every codespace state. -/
lemma mem_logicalGateGroup_iff_conjugation (U : NQubitGate n) (S : StabilizerGroup n) :
  U ∈ logicalGateGroup S ↔ ∀ g ∈ S.toSubgroup, ∀ ψ : NQubitState n,
    IsInCodespace ψ S → (U.val * g.toMatrix * star U.val).mulVec ψ.val = ψ.val := by
  rfl

end StabilizerGroup

end Quantum
