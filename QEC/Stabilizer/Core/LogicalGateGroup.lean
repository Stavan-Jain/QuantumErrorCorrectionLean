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

/-- Gate-level conjugation formulation: for every g ∈ S, `(conjByGate U g.gate)` stabilizes
every codespace state. -/
private def PreservesCodespaceConjugationGate (U : NQubitGate n) (S : StabilizerGroup n) : Prop :=
  ∀ g ∈ S.toSubgroup, ∀ ψ : NQubitState n,
    IsInCodespace ψ S → ((conjByGate U g.gate).val).mulVec ψ.val = ψ.val

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

/-- Helper: if a property holds for all normalized vectors in codespace,
    it holds for all vectors by linearity. -/
private lemma extend_from_states_to_submodule (M : Matrix (NQubitBasis n) (NQubitBasis n) ℂ)
    (S : StabilizerGroup n)
    (h : ∀ (ψ : NQubitState n), ψ.val ∈ codespaceSubmodule S → M.mulVec ψ.val = ψ.val)
    (v : NQubitVec n) (hv : v ∈ codespaceSubmodule S) : M.mulVec v = v := by
  by_cases hv0 : v = 0; · simp [hv0]
  have hnp : 0 < Quantum.norm v := by
    simp only [Quantum.norm]; apply Real.sqrt_pos.mpr
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
    exact Finset.sum_pos' (fun _ _ => sq_nonneg _)
      ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩
  set c : ℂ := ↑((Quantum.norm v)⁻¹ : ℝ)
  have hc_ne : c ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (inv_pos.mpr hnp))
  have hw_norm : Quantum.norm (c • v) = 1 := by
    simp only [Quantum.norm, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← Finset.mul_sum]
    rw [Real.sqrt_mul (sq_nonneg _)]
    conv_lhs => rw [show √(‖c‖ ^ 2) = ‖c‖ from by
      rw [Real.sqrt_sq_eq_abs]; exact abs_of_nonneg (le_of_lt (by positivity))]
    rw [Complex.norm_real, Real.norm_of_nonneg (le_of_lt (inv_pos.mpr hnp))]
    exact inv_mul_cancel₀ (ne_of_gt hnp)
  have := h ⟨c • v, hw_norm⟩ ((codespaceSubmodule S).smul_mem c hv)
  calc M.mulVec v
      = c⁻¹ • M.mulVec (c • v) := by rw [mulVec_smul]; simp [smul_smul, inv_mul_cancel₀ hc_ne]
    _ = c⁻¹ • (c • v) := by rw [this]
    _ = v := by simp [smul_smul, inv_mul_cancel₀ hc_ne]

/-- Helper: a unitary that maps codespace into itself is surjective on codespace. -/
private lemma unitary_surj_on_codespace (M : NQubitGate n) (S : StabilizerGroup n)
    (hM : ∀ v ∈ codespaceSubmodule S, M.val.mulVec v ∈ codespaceSubmodule S) :
    ∀ v ∈ codespaceSubmodule S, ∃ w ∈ codespaceSubmodule S, M.val.mulVec w = v := by
  intro v hv
  have h_range : LinearMap.range (Matrix.mulVecLin M.val |>.comp
      (Submodule.subtype (codespaceSubmodule S))) = codespaceSubmodule S := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact Set.range_subset_iff.mpr fun x => hM x.val x.2
    · rw [LinearMap.finrank_range_of_inj]; intro x y hxy
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
        Matrix.mulVecLin_apply] at hxy
      ext1; have := congr_arg ((star M.val).mulVec) hxy
      simp only [Matrix.mulVec_mulVec,
        show star M.val * M.val = 1 from mem_unitaryGroup_iff'.1 M.2,
        Matrix.one_mulVec] at this
      exact this
  have := SetLike.ext_iff.mp h_range v
  simp only [LinearMap.mem_range, LinearMap.coe_comp, Function.comp_apply,
    Submodule.coe_subtype, Matrix.mulVecLin_apply] at this
  obtain ⟨⟨w, hw⟩, hwv⟩ := this.mpr hv
  exact ⟨w, hw, hwv⟩

/-- Conjugation formulation is equivalent to mapping the codespace to itself. -/
private lemma conjugation_iff_maps_codespace (U : NQubitGate n) (S : StabilizerGroup n) :
  PreservesCodespaceConjugation U S ↔ ∀ ψ, IsInCodespace ψ S → IsInCodespace (U • ψ) S := by
  constructor
  · -- Forward: (U g U†) stabilizes codespace ⟹ U maps codespace to codespace
    intro h ψ hψ
    simp only [IsInCodespace, IsStabilizedBy, IsStabilizedVec, smul_QState_val] at *
    intro g hg
    -- Step 1: Extend h to all vectors in codespace
    have h_vec : ∀ g' ∈ S.toSubgroup, ∀ v ∈ codespaceSubmodule S,
        (U.val * g'.toMatrix * star U.val).mulVec v = v :=
      fun g' hg' v hv => extend_from_states_to_submodule _ S
        (fun φ hφ => h g' hg' φ ((mem_codespace_iff_mem_submodule φ S).mpr hφ)) v hv
    -- Step 2: U† maps codespace submodule to itself
    have hUadj : ∀ v ∈ codespaceSubmodule S, (star U.val).mulVec v ∈ codespaceSubmodule S := by
      intro v hv g' hg'
      have h1 : U.val.mulVec (g'.toMatrix.mulVec ((star U.val).mulVec v)) = v := by
        rw [mulVec_mulVec, mulVec_mulVec]; exact h_vec g' hg' v hv
      have h2 := congr_arg ((star U.val).mulVec) h1
      rw [mulVec_mulVec, show star U.val * U.val = 1 from mem_unitaryGroup_iff'.1 U.2,
        one_mulVec] at h2
      exact h2
    -- Step 3: U† surjective on codespace ⟹ U maps codespace to codespace
    obtain ⟨w, hw, hUw⟩ := unitary_surj_on_codespace U⁻¹ S (by
      simp only [gate_inv_val]; exact hUadj) ψ.val (fun g' hg' => hψ g' hg')
    -- ψ = U⁻¹ *ᵥ w, so U *ᵥ ψ = U *ᵥ (U⁻¹ *ᵥ w) = w
    have hUψ : U.val.mulVec ψ.val = w := by
      conv_lhs => rw [show ψ.val = (star U.val).mulVec w from by
        rw [← hUw, gate_inv_val]]
      rw [mulVec_mulVec, show U.val * star U.val = 1 from mem_unitaryGroup_iff.1 U.2, one_mulVec]
    rw [hUψ]; exact hw g hg
  · -- Backward: U maps codespace to codespace ⟹ (U g U†) stabilizes codespace
    intro h g hg ψ hψ
    simp only [IsInCodespace, IsStabilizedBy, IsStabilizedVec] at hψ
    -- Step 1: U maps codespace submodule to itself
    have hU_maps : ∀ v ∈ codespaceSubmodule S, U.val.mulVec v ∈ codespaceSubmodule S := by
      intro v hv
      by_cases hv0 : v = 0; · simp [hv0, (codespaceSubmodule S).zero_mem]
      have hnp : 0 < Quantum.norm v := by
        simp only [Quantum.norm]; apply Real.sqrt_pos.mpr
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
        exact Finset.sum_pos' (fun _ _ => sq_nonneg _)
          ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩
      set c : ℂ := ↑((Quantum.norm v)⁻¹ : ℝ)
      have hc_ne : c ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (inv_pos.mpr hnp))
      have hw_norm : Quantum.norm (c • v) = 1 := by
        simp only [Quantum.norm, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← Finset.mul_sum]
        rw [Real.sqrt_mul (sq_nonneg _)]
        conv_lhs => rw [show √(‖c‖ ^ 2) = ‖c‖ from by
          rw [Real.sqrt_sq_eq_abs]; exact abs_of_nonneg (le_of_lt (by positivity))]
        rw [Complex.norm_real, Real.norm_of_nonneg (le_of_lt (inv_pos.mpr hnp))]
        exact inv_mul_cancel₀ (ne_of_gt hnp)
      have hφ := h ⟨c • v, hw_norm⟩
        ((mem_codespace_iff_mem_submodule _ S).mpr ((codespaceSubmodule S).smul_mem c hv))
      intro g' hg'
      have h1 := hφ g' hg'
      simp only [IsStabilizedBy, IsStabilizedVec, smul_QState_val, mulVec_smul] at h1
      exact (isUnit_iff_ne_zero.mpr hc_ne).smul_left_cancel.mp h1
    -- Step 2: U surjective ⟹ U† maps codespace to itself
    obtain ⟨w, hw, hUw⟩ := unitary_surj_on_codespace U S hU_maps ψ.val
      (fun g' hg' => hψ g' hg')
    -- (U g U†) ψ = U (g (U† ψ)) = U (g w) = U w = ψ  (since U† ψ = w ∈ codespace)
    rw [show (U.val * g.toMatrix * star U.val).mulVec ψ.val =
      U.val.mulVec (g.toMatrix.mulVec ((star U.val).mulVec ψ.val)) from by
      rw [mulVec_mulVec, mulVec_mulVec]]
    rw [show (star U.val).mulVec ψ.val = w from by
      rw [← hUw, mulVec_mulVec,
        show star U.val * U.val = 1 from mem_unitaryGroup_iff'.1 U.2, one_mulVec]]
    rw [hw g hg, hUw]

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
  · simp_all +decide [Finset.sum_eq_zero_iff_of_nonneg];
    ext i; simp +decide [ hv, Matrix.mulVec, dotProduct ] ;
  · have := h_conj ⟨(1 / Real.sqrt (∑ i, ‖v i‖ ^ 2)) • v, ?_⟩ ?_ <;> simp_all +decide
    any_goals simp +decide
      [mul_pow, abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    any_goals rw [ ← Finset.mul_sum _ _ _, inv_mul_cancel₀ hv ];
    · have := this g hg
      simp_all +decide
      convert congr_arg (fun x : NQubitVec n => (Real.sqrt (∑ i, ‖v i‖ ^ 2)) • x) this using 1 <;>
        norm_num [Matrix.mulVec_smul, smul_smul]
      · rw
          [mul_inv_cancel₀
            (ne_of_gt
              (Real.sqrt_pos.mpr
                (lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Ne.symm hv)))),
            one_smul]
      · rw
          [mul_inv_cancel₀
            (ne_of_gt
              (Real.sqrt_pos.mpr
                (lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Ne.symm hv)))),
            one_smul]
    · intro g hg
      specialize hv₁ g hg
      simp_all +decide
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

/-- Gate-level conjugation characterization of logical-gate-group membership. -/
lemma mem_logicalGateGroup_iff_conjugation_gate (U : NQubitGate n) (S : StabilizerGroup n) :
  U ∈ logicalGateGroup S ↔ ∀ g ∈ S.toSubgroup, ∀ ψ : NQubitState n,
    IsInCodespace ψ S → ((conjByGate U g.gate).val).mulVec ψ.val = ψ.val := by
  simpa [conjByGate_val, NQubitPauliGroupElement.gate_val] using
    (mem_logicalGateGroup_iff_conjugation U S)

end StabilizerGroup

end Quantum
