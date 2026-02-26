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
operator U† g U stabilizes every state in the codespace. See `LogicalGates.lean` for `IsLogicalGate`.
-/

/-- Conjugation formulation: for every g ∈ S, U† g U stabilizes every codespace state. -/
private def PreservesCodespaceConjugation (U : NQubitGate n) (S : StabilizerGroup n) : Prop :=
  ∀ g ∈ S.toSubgroup, ∀ ψ : NQubitState n,
    IsInCodespace ψ S → (star U.val * g.toMatrix * U.val).mulVec ψ.val = ψ.val

/-- Conjugation formulation is equivalent to mapping the codespace to itself. -/
private lemma conjugation_iff_maps_codespace (U : NQubitGate n) (S : StabilizerGroup n) :
  PreservesCodespaceConjugation U S ↔ ∀ ψ, IsInCodespace ψ S → IsInCodespace (U • ψ) S := by
  constructor
  · intro h ψ hψ
    rw [IsInCodespace.iff_all_stabilizers]
    intro g hg
    simp only [IsStabilizedBy, IsStabilizedVec, smul_QState_val]
    have h_conj := h g hg ψ hψ
    have h_unit : U.val * star U.val = 1 := Matrix.mem_unitaryGroup_iff.1 U.2
    calc g.toMatrix.mulVec (U.val.mulVec ψ.val)
        = (g.toMatrix * U.val).mulVec ψ.val := by rw [mulVec_mulVec]
      _ = (U.val * (star U.val) * (g.toMatrix * U.val)).mulVec ψ.val := by
          rw [← Matrix.mul_assoc, h_unit, one_mul]
      _ = U.val.mulVec (((star U.val) * (g.toMatrix * U.val)).mulVec ψ.val) := by
          rw [Matrix.mul_assoc, mulVec_mulVec]
      _ = U.val.mulVec ψ.val := by rw [← Matrix.mul_assoc, h_conj]
  · intro hU g hg ψ hψ
    have hUψ : IsInCodespace (U • ψ) S := hU ψ hψ
    have h_stab := (IsInCodespace.iff_all_stabilizers (U • ψ) S).1 hUψ g hg
    simp only [IsStabilizedBy, IsStabilizedVec, smul_QState_val] at h_stab
    calc (star U.val * g.toMatrix * U.val).mulVec ψ.val
        = (star U.val * (g.toMatrix * U.val)).mulVec ψ.val := by rw [Matrix.mul_assoc]
      _ = (star U.val).mulVec ((g.toMatrix * U.val).mulVec ψ.val) := by
          rw [← mulVec_mulVec ψ.val (star U.val) (g.toMatrix * U.val)]
      _ = (star U.val).mulVec (g.toMatrix.mulVec (U.val.mulVec ψ.val)) := by
          rw [← mulVec_mulVec ψ.val g.toMatrix U.val]
      _ = (star U.val).mulVec (U.val.mulVec ψ.val) := by rw [h_stab]
      _ = ((star U.val) * U.val).mulVec ψ.val := by rw [← mulVec_mulVec ψ.val (star U.val) U.val]
      _ = ψ.val := by
        have h_unit : (star U.val) * U.val = 1 := Matrix.mem_unitaryGroup_iff'.1 U.2
        rw [h_unit, one_mulVec]

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

/-- If U preserves the codespace (conjugation formulation), then U maps the submodule into itself. -/
private lemma maps_to_codespace_of_conjugation (U : NQubitGate n) (S : StabilizerGroup n)
  (h : PreservesCodespaceConjugation U S) :
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

/-- U is in the logical gate group iff for every g ∈ S, U† g U stabilizes every codespace state. -/
lemma mem_logicalGateGroup_iff_conjugation (U : NQubitGate n) (S : StabilizerGroup n) :
  U ∈ logicalGateGroup S ↔ ∀ g ∈ S.toSubgroup, ∀ ψ : NQubitState n,
    IsInCodespace ψ S → (star U.val * g.toMatrix * U.val).mulVec ψ.val = ψ.val := by
  rw [mem_logicalGateGroup_iff]
  constructor
  · intro hU g hg ψ hψ
    have hUψ : IsInCodespace (U • ψ) S := hU ψ hψ
    have h_stab : IsStabilizedBy g (U • ψ) := (IsInCodespace.iff_all_stabilizers (U • ψ) S).1 hUψ g hg
    simp only [IsStabilizedBy, IsStabilizedVec, smul_QState_val] at h_stab
    calc (star U.val * g.toMatrix * U.val).mulVec ψ.val
        = (star U.val * (g.toMatrix * U.val)).mulVec ψ.val := by rw [Matrix.mul_assoc]
      _ = (star U.val).mulVec ((g.toMatrix * U.val).mulVec ψ.val) := by
          rw [← mulVec_mulVec ψ.val (star U.val) (g.toMatrix * U.val)]
      _ = (star U.val).mulVec (g.toMatrix.mulVec (U.val.mulVec ψ.val)) := by
          rw [← mulVec_mulVec ψ.val g.toMatrix U.val]
      _ = (star U.val).mulVec (U.val.mulVec ψ.val) := by rw [h_stab]
      _ = ((star U.val) * U.val).mulVec ψ.val := by rw [← mulVec_mulVec ψ.val (star U.val) U.val]
      _ = ψ.val := by
        have h_unit : (star U.val) * U.val = 1 := Matrix.mem_unitaryGroup_iff'.1 U.2
        rw [h_unit, one_mulVec]
  · intro h ψ hψ
    rw [IsInCodespace.iff_all_stabilizers]
    intro g hg
    simp only [IsStabilizedBy, IsStabilizedVec, smul_QState_val]
    have h_conj := h g hg ψ hψ
    have h_unit : U.val * star U.val = 1 := Matrix.mem_unitaryGroup_iff.1 U.2
    calc g.toMatrix.mulVec (U.val.mulVec ψ.val)
        = (g.toMatrix * U.val).mulVec ψ.val := by rw [mulVec_mulVec]
      _ = (U.val * (star U.val) * (g.toMatrix * U.val)).mulVec ψ.val := by
          rw [← Matrix.mul_assoc, h_unit, one_mul]
      _ = (U.val * ((star U.val) * (g.toMatrix * U.val))).mulVec ψ.val := by rw [Matrix.mul_assoc]
      _ = U.val.mulVec (((star U.val) * (g.toMatrix * U.val)).mulVec ψ.val) := by rw [mulVec_mulVec]
      _ = U.val.mulVec ψ.val := by rw [← Matrix.mul_assoc, h_conj]

end StabilizerGroup

end Quantum
