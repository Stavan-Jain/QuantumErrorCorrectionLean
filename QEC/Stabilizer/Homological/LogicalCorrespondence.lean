import QEC.Stabilizer.Homological.StabGroup
import QEC.Stabilizer.Core.LogicalOperators

/-!
# §C — Logical correspondence iffs

For a homological CSS code, an X-type chain operator `chainXOperator c` is a
non-trivial logical operator iff its underlying chain `c` is a cycle that is
not a boundary.  Lifted from `ToricLogicalCorrespondenceX/Z.lean`.

This file currently covers the X-side iffs.  The Z-side mirror via the dual
boundary `dualBoundary = transpose ∂₂` is set up but the four mirror theorems
are deferred (the §E toric refactor uses the X-side directly via §D).
-/

namespace Quantum
namespace Stabilizer
namespace Homological

open scoped BigOperators

namespace HomologicalCode

variable (X : HomologicalCode)

/-! ## Dual boundary map (transpose of `∂₂`) -/

/-- The `𝔽₂`-transpose of `∂₂`, written as a finite sum.
`(dualBoundary c) f = ∑ e, c e · ∂₂(δ_f)(e)`. -/
noncomputable def dualBoundary :
    (X.C1 → ZMod 2) →ₗ[ZMod 2] (X.C2 → ZMod 2) where
  toFun c := fun f => ∑ e : X.C1, c e * X.boundary2 (Pi.single f 1) e
  map_add' c d := by
    ext f
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    ext f
    simp [Finset.mul_sum, mul_assoc]

@[simp] theorem dualBoundary_apply (c : X.C1 → ZMod 2) (f : X.C2) :
    X.dualBoundary c f = ∑ e : X.C1, c e * X.boundary2 (Pi.single f 1) e := rfl

/-- Transpose pairing for `∂₂`/`dualBoundary`. -/
theorem boundary2_dualBoundary_transpose
    (f : X.C2 → ZMod 2) (c : X.C1 → ZMod 2) :
    ∑ e : X.C1, X.boundary2 f e * c e =
      ∑ p : X.C2, f p * X.dualBoundary c p := by
  have hf : f = ∑ p : X.C2, f p • (Pi.single p (1 : ZMod 2)) := by
    ext p; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hf]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [dualBoundary_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

/-- Dual cycles: kernel of `dualBoundary`. -/
noncomputable def dualCycles : Submodule (ZMod 2) (X.C1 → ZMod 2) :=
  LinearMap.ker X.dualBoundary

/-- Dual boundaries: range of `cutMap`. -/
noncomputable def dualBoundaries : Submodule (ZMod 2) (X.C1 → ZMod 2) :=
  LinearMap.range X.cutMap

variable {X}

/-- Helper: `ZMod 2` dichotomy. -/
private lemma zmod2_dichotomy_local (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hvalle : a.val ≤ 1 := Nat.le_of_lt_succ a.val_lt
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hvalle with h0 | h1
  · left
    calc a = ((a.val : ZMod 2)) := (ZMod.natCast_zmod_val a).symm
      _ = 0 := by simp [h0]
  · right
    calc a = ((a.val : ZMod 2)) := (ZMod.natCast_zmod_val a).symm
      _ = 1 := by simp [h1]

/-! ## Inner-product specializations -/

/-- `⟨c, cutMap (singleVtx v)⟩ = boundary1 c v`. -/
theorem chainInnerProduct_cutMap_singleVtx_eq_boundary1
    (c : X.C1 → ZMod 2) (v : X.C0) :
    chainInnerProduct c (X.cutMap (X.singleVtx v)) = X.boundary1 c v := by
  unfold chainInnerProduct
  rw [← X.boundary1_cutMap_transpose c (X.singleVtx v)]
  unfold singleVtx
  rw [Finset.sum_eq_single v]
  · simp
  · intros v' _ hne
    rw [Pi.single_eq_of_ne hne]; ring
  · intro hcontra; exact absurd (Finset.mem_univ v) hcontra

/-- `⟨boundary2 (singleFace f), c⟩ = dualBoundary c f`. -/
theorem chainInnerProduct_boundary2_singleFace_eq_dualBoundary
    (c : X.C1 → ZMod 2) (f : X.C2) :
    chainInnerProduct (X.boundary2 (X.singleFace f)) c = X.dualBoundary c f := by
  unfold chainInnerProduct
  rw [boundary2_dualBoundary_transpose]
  unfold singleFace
  rw [Finset.sum_eq_single f]
  · simp
  · intros f' _ hne
    rw [Pi.single_eq_of_ne hne]; ring
  · intro hcontra; exact absurd (Finset.mem_univ f) hcontra

/-! ## X-side commutation criteria -/

/-- `chainXOperator c` commutes with the vertex stab at `v` iff `boundary1 c v = 0`. -/
theorem chainXOperator_commutes_vertexStabOf_iff
    (c : X.C1 → ZMod 2) (v : X.C0) :
    X.chainXOperator c * X.vertexStabOf v = X.vertexStabOf v * X.chainXOperator c
    ↔ X.boundary1 c v = 0 := by
  unfold vertexStabOf
  rw [chainXOperator_commutes_chainZOperator_iff,
      ← chainInnerProduct_cutMap_singleVtx_eq_boundary1]

/-- `chainXOperator c` commutes with every Z-generator iff `c ∈ cycles`. -/
theorem chainXOperator_commutes_ZGenerators_iff_mem_cycles (c : X.C1 → ZMod 2) :
    (∀ z ∈ X.ZGenerators, z * X.chainXOperator c = X.chainXOperator c * z)
    ↔ c ∈ X.cycles := by
  constructor
  · intro h
    rw [show X.cycles = LinearMap.ker X.boundary1 from rfl, LinearMap.mem_ker]
    ext v
    have h_v := h _ ⟨v, rfl⟩
    have := (chainXOperator_commutes_vertexStabOf_iff c v).mp h_v.symm
    simpa using this
  · intro hc z hz
    rcases hz with ⟨v, rfl⟩
    have hbd : X.boundary1 c v = 0 := by
      have h_ker : c ∈ LinearMap.ker X.boundary1 := hc
      rw [LinearMap.mem_ker] at h_ker
      exact congr_fun h_ker v
    exact ((chainXOperator_commutes_vertexStabOf_iff c v).mpr hbd).symm

/-! ## Closure ↔ boundary -/

/-- `chainXOperator (∂₂ (singleFace f)) = faceStabOf f`. -/
@[simp] lemma chainXOperator_boundary2_singleFace (f : X.C2) :
    X.chainXOperator (X.boundary2 (X.singleFace f)) = X.faceStabOf f := rfl

/-- `chainXOperator c` is its own inverse (X*X = I). -/
lemma chainXOperator_inv (c : X.C1 → ZMod 2) :
    (X.chainXOperator c)⁻¹ = X.chainXOperator c := by
  apply NQubitPauliGroupElement.ext
  · -- phase: -0 = 0 in Fin 4
    show (-(0 : Fin 4)) = 0
    decide
  · rfl

/-- Every 2-chain is the sum of its single-face indicators over its support. -/
private lemma c2_eq_sum_singleFace_filter (f : X.C2 → ZMod 2) :
    f = ∑ p ∈ (Finset.univ.filter (fun p : X.C2 => f p = 1)),
      X.singleFace p := by
  ext q
  rw [Finset.sum_apply]
  by_cases hq : f q = 1
  · rw [Finset.sum_eq_single q]
    · simp [singleFace, hq]
    · intros r _ hne
      simp [singleFace, Pi.single_apply, hne.symm]
    · intro hcontra
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ q, hq⟩) hcontra
  · have hq0 : f q = 0 := (zmod2_dichotomy_local (f q)).resolve_right hq
    rw [hq0]
    refine (Finset.sum_eq_zero ?_).symm
    intros r hr
    rw [Finset.mem_filter] at hr
    have hne : r ≠ q := fun heq => hq (heq ▸ hr.2)
    simp [singleFace, Pi.single_apply, hne]

/-- For any 2-chain `f`, `chainXOperator (∂₂ f)` is in the X-closure. -/
lemma chainXOperator_boundary2_mem_XClosure (f : X.C2 → ZMod 2) :
    X.chainXOperator (X.boundary2 f) ∈ Subgroup.closure X.XGenerators := by
  classical
  rw [c2_eq_sum_singleFace_filter f]
  rw [map_sum]  -- pushes ∂₂ through the sum
  -- Goal: chainXOperator (∑ p ∈ filter, ∂₂ (singleFace p)) ∈ closure
  induction (Finset.univ.filter fun p : X.C2 => f p = 1) using Finset.induction with
  | empty => simpa using OneMemClass.one_mem _
  | insert p s hp ih =>
    rw [Finset.sum_insert hp, chainXOperator_add]
    exact Subgroup.mul_mem _
      (Subgroup.subset_closure (Set.mem_range_self _)) ih

/-- `chainXOperator c ∈ closure(XGenerators)` iff `c ∈ boundaries`. -/
theorem chainXOperator_mem_XClosure_iff_mem_boundaries (c : X.C1 → ZMod 2) :
    X.chainXOperator c ∈ Subgroup.closure X.XGenerators ↔ c ∈ X.boundaries := by
  constructor
  · intro hc
    have h_closure :
        ∀ g ∈ Subgroup.closure X.XGenerators,
          ∃ f : X.C2 → ZMod 2,
            X.chainXOperator (X.boundary2 f) = g := by
      intro g hg
      refine Subgroup.closure_induction
        (p := fun y _ => ∃ f : X.C2 → ZMod 2, X.chainXOperator (X.boundary2 f) = y)
        ?_ ?_ ?_ ?_ hg
      · rintro y ⟨p, rfl⟩
        exact ⟨X.singleFace p, rfl⟩
      · exact ⟨0, by simp⟩
      · intros g₁ g₂ _ _ ih1 ih2
        obtain ⟨f₁, hf₁⟩ := ih1
        obtain ⟨f₂, hf₂⟩ := ih2
        refine ⟨f₁ + f₂, ?_⟩
        rw [map_add, chainXOperator_add, hf₁, hf₂]
      · intros g _ ih
        obtain ⟨f, hf⟩ := ih
        refine ⟨f, ?_⟩
        rw [← hf, chainXOperator_inv]
    obtain ⟨f, hf⟩ := h_closure _ hc
    have h_eq : X.boundary2 f = c := by
      have hr := congrArg X.chainOfXOperator hf
      rw [chainOfXOperator_chainXOperator] at hr
      rw [chainOfXOperator_chainXOperator] at hr
      exact hr
    rw [show X.boundaries = LinearMap.range X.boundary2 from rfl]
    exact ⟨f, h_eq⟩
  · rintro ⟨f, rfl⟩
    exact chainXOperator_boundary2_mem_XClosure f

/-! ## CSS decomposition: X-type elements of stabilizer come from X-closure -/

lemma xType_in_stabilizer_implies_in_XClosure
    (g : NQubitPauliGroupElement X.numQubits)
    (hg : g ∈ X.homologicalStabilizerGroup.toSubgroup)
    (hxt : NQubitPauliGroupElement.IsXTypeElement g) :
    g ∈ Subgroup.closure X.XGenerators := by
  have hg_cl :
      g ∈ Subgroup.closure (X.ZGenerators ∪ X.XGenerators) := hg
  obtain ⟨z, hz, x, hx, rfl⟩ :=
    Subgroup.mem_closure_union_exists_mul_of_commute_generators
      ZGenerators_commute_XGenerators g hg_cl
  have hz_zt : NQubitPauliGroupElement.IsZTypeElement z :=
    NQubitPauliGroupElement.IsZTypeElement_of_mem_closure ZGenerators_isZType z hz
  have hx_xt : NQubitPauliGroupElement.IsXTypeElement x :=
    NQubitPauliGroupElement.IsXTypeElement_of_mem_closure XGenerators_isXType x hx
  have hz_xt : NQubitPauliGroupElement.IsXTypeElement z := by
    have hreorder : z = (z * x) * x⁻¹ := (mul_inv_cancel_right z x).symm
    rw [hreorder]
    exact NQubitPauliGroupElement.IsXTypeElement_mul hxt
      (NQubitPauliGroupElement.IsXTypeElement_inv hx_xt)
  have hz_eq : z = 1 :=
    NQubitPauliGroupElement.eq_one_of_IsZTypeElement_and_IsXTypeElement hz_zt hz_xt
  rw [hz_eq, one_mul]
  exact hx

/-! ## Centralizer membership iff cycle -/

/-- An X-type chain operator commutes with all face stabs (X-X case). -/
lemma chainXOperator_commutes_faceStabOf
    (c : X.C1 → ZMod 2) (f : X.C2) :
    X.faceStabOf f * X.chainXOperator c = X.chainXOperator c * X.faceStabOf f :=
  Quantum.StabilizerGroup.CSSCommutationLemmas.XType_commutes
    (faceStabOf_isXType f) (chainXOperator_isXType c)

lemma chainXOperator_mem_centralizer_iff_mem_cycles
    (c : X.C1 → ZMod 2) :
    X.chainXOperator c ∈ Quantum.StabilizerGroup.centralizer X.homologicalStabilizerGroup
    ↔ c ∈ X.cycles := by
  constructor
  · intro h
    apply (chainXOperator_commutes_ZGenerators_iff_mem_cycles c).mp
    intro z hz
    apply h
    exact Subgroup.subset_closure (Set.mem_union_left _ hz)
  · intro hc
    have h_commZ :
        ∀ z ∈ X.ZGenerators, z * X.chainXOperator c = X.chainXOperator c * z :=
      (chainXOperator_commutes_ZGenerators_iff_mem_cycles c).mpr hc
    intro g hg
    refine Subgroup.closure_induction (p := fun y _ => y * X.chainXOperator c =
        X.chainXOperator c * y) ?_ ?_ ?_ ?_ hg
    · rintro y (hy | hy)
      · exact h_commZ y hy
      · rcases hy with ⟨f, rfl⟩
        exact chainXOperator_commutes_faceStabOf c f
    · show (1 : NQubitPauliGroupElement X.numQubits) * X.chainXOperator c =
        X.chainXOperator c * 1
      rw [one_mul, mul_one]
    · intros y₁ y₂ _ _ hy₁ hy₂
      calc (y₁ * y₂) * X.chainXOperator c
          = y₁ * (y₂ * X.chainXOperator c) := mul_assoc _ _ _
        _ = y₁ * (X.chainXOperator c * y₂) := by rw [hy₂]
        _ = (y₁ * X.chainXOperator c) * y₂ := (mul_assoc _ _ _).symm
        _ = (X.chainXOperator c * y₁) * y₂ := by rw [hy₁]
        _ = X.chainXOperator c * (y₁ * y₂) := mul_assoc _ _ _
    · intros y _ hy
      have hcomm : Commute y (X.chainXOperator c) := hy
      exact hcomm.inv_left.eq

/-! ## Stabilizer "same operators" implies the chain is a boundary -/

lemma stabilizer_same_ops_implies_boundary
    (c : X.C1 → ZMod 2)
    (s : NQubitPauliGroupElement X.numQubits)
    (hs : s ∈ X.homologicalStabilizerGroup.toSubgroup)
    (heq : s.operators = (X.chainXOperator c).operators) :
    c ∈ X.boundaries := by
  have hops : ∀ i, s.operators i = PauliOperator.X ∨ s.operators i = PauliOperator.I := by
    intro i
    rw [heq]
    rcases (chainXOperator_isXType c).2 i with h | h
    · right; exact h
    · left; exact h
  -- s has phase 0 and is X-type via CSS decomposition
  have hs_xt : NQubitPauliGroupElement.IsXTypeElement s := by
    have hs_cl : s ∈ Subgroup.closure (X.ZGenerators ∪ X.XGenerators) := hs
    obtain ⟨z, hz, x, hx, hzx⟩ :=
      Subgroup.mem_closure_union_exists_mul_of_commute_generators
        ZGenerators_commute_XGenerators s hs_cl
    have hz_zt : NQubitPauliGroupElement.IsZTypeElement z :=
      NQubitPauliGroupElement.IsZTypeElement_of_mem_closure ZGenerators_isZType z hz
    have hx_xt : NQubitPauliGroupElement.IsXTypeElement x :=
      NQubitPauliGroupElement.IsXTypeElement_of_mem_closure XGenerators_isXType x hx
    have hz_id : z = 1 := by
      have hz_ops_I : ∀ i, z.operators i = PauliOperator.I := by
        intro i
        have hsi := hops i
        rw [hzx] at hsi
        rcases hz_zt.2 i with hz_I | hz_Z
        · exact hz_I
        · exfalso
          rcases hx_xt.2 i with hx_I | hx_X
          · simp [NQubitPauliGroupElement.mul, NQubitPauliGroupElement.mulOp,
              hz_Z, hx_I, PauliOperator.mulOp] at hsi
          · simp [NQubitPauliGroupElement.mul, NQubitPauliGroupElement.mulOp,
              hz_Z, hx_X, PauliOperator.mulOp] at hsi
      exact NQubitPauliGroupElement.ext z 1 hz_zt.1
        (by ext i; simp [NQubitPauliOperator.identity, hz_ops_I i])
    rw [hzx, hz_id, one_mul]
    exact hx_xt
  have hxcl :
      s ∈ Subgroup.closure X.XGenerators :=
    xType_in_stabilizer_implies_in_XClosure s hs hs_xt
  have h_eq : s = X.chainXOperator c := by
    apply NQubitPauliGroupElement.ext
    · rw [hs_xt.1, (chainXOperator_isXType c).1]
    · ext i; exact congrFun heq i
  rw [h_eq] at hxcl
  exact (chainXOperator_mem_XClosure_iff_mem_boundaries c).mp hxcl

/-! ## Main: nontrivial logical iff cycle ∧ ¬ boundary -/

theorem chainXOperator_isNontrivialLogical_iff (c : X.C1 → ZMod 2) :
    Quantum.StabilizerGroup.IsNontrivialLogicalOperator
        (X.chainXOperator c) X.homologicalStabilizerGroup ↔
      c ∈ X.cycles ∧ c ∉ X.boundaries := by
  rw [Quantum.StabilizerGroup.IsNontrivialLogicalOperator_iff]
  constructor
  · rintro ⟨h_centralizer, h_not_stab, _⟩
    refine ⟨?_, ?_⟩
    · exact (chainXOperator_mem_centralizer_iff_mem_cycles c).mp h_centralizer
    · intro hc_b
      have hclosure :
          X.chainXOperator c ∈ Subgroup.closure X.XGenerators :=
        (chainXOperator_mem_XClosure_iff_mem_boundaries c).mpr hc_b
      have h_in_stab :
          X.chainXOperator c ∈ X.homologicalStabilizerGroup.toSubgroup := by
        refine Subgroup.closure_induction
          (p := fun y _ => y ∈ X.homologicalStabilizerGroup.toSubgroup) ?_ ?_ ?_ ?_ hclosure
        · intro y hy
          exact Subgroup.subset_closure (Set.mem_union_right _ hy)
        · exact Subgroup.one_mem _
        · intros y₁ y₂ _ _ hy₁ hy₂
          exact Subgroup.mul_mem _ hy₁ hy₂
        · intros y _ hy
          exact Subgroup.inv_mem _ hy
      exact h_not_stab h_in_stab
  · rintro ⟨hc_c, hc_nb⟩
    refine ⟨?_, ?_, ?_⟩
    · exact (chainXOperator_mem_centralizer_iff_mem_cycles c).mpr hc_c
    · intro hg
      exact hc_nb (stabilizer_same_ops_implies_boundary c (X.chainXOperator c) hg rfl)
    · intro s hs hEq
      exact hc_nb (stabilizer_same_ops_implies_boundary c s hs hEq)

end HomologicalCode

end Homological
end Stabilizer
end Quantum
