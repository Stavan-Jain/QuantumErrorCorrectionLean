/-
# Chain-level X/Z duality for BB chain complexes

For a BB chain complex `bbChainComplex A B` over a finite abelian group `G`,
the block-swap-and-negate equivalence

  `Φ : (g, j) ↦ (-g, swap j)`

exchanges the primal chain data (`cycles`, `boundaries`) with the dual chain
data (`dualCycles`, `dualBoundaries`) while preserving chain weight.  The
upshot (`bb_cycle_bound_iff_dual_bound`) is that any chain-weight lower bound
on the X side transfers verbatim to the Z side: `d_X = d_Z` at the chain
level, for every BB code at once.

## Convention bridge (lab notes → repo)

Repo convention (`BBChainComplex.lean`): `∂₂ f = (A⋆f | B⋆f)` and
`∂₁ c = B⋆c_L + A⋆c_R`, so the cycle condition is `B⋆v_L = A⋆v_R`.
Repo-left = lab-right.  The transpose formulas below follow this convention:

* `dualBoundary c = (reflect A) ⋆ c_L + (reflect B) ⋆ c_R`
* `cutMap s = ((reflect B) ⋆ s | (reflect A) ⋆ s)`

where `reflect a = a ∘ (-·)` implements the `𝔽₂[G]`-antipode (transpose of
convolution-multiplication).
-/

import QEC.Stabilizer.Framework.Homological.Covering
import QEC.Stabilizer.Framework.Homological.LogicalCorrespondence

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open scoped BigOperators

/-! ## The reflection (group antipode) on `ZMod 2`-chains -/

section Reflect

variable {G : Type} [AddCommGroup G]

/-- Reflection of a chain through the group inverse: `(reflect a)(g) = a(-g)`.
This is the `𝔽₂[G]`-antipode; transposing convolution-by-`a` gives
convolution-by-`reflect a`. -/
def reflect (a : G → ZMod 2) : G → ZMod 2 := fun g => a (-g)

@[simp] lemma reflect_apply (a : G → ZMod 2) (g : G) :
    reflect a g = a (-g) := rfl

@[simp] lemma reflect_reflect (a : G → ZMod 2) : reflect (reflect a) = a := by
  funext g
  simp

lemma reflect_eq_zero_iff (a : G → ZMod 2) : reflect a = 0 ↔ a = 0 := by
  constructor
  · intro h
    funext g
    have hg := congrFun h (-g)
    simpa using hg
  · rintro rfl
    funext g
    simp

lemma reflect_conv [Fintype G] (a b : G → ZMod 2) :
    reflect (a ⋆ b) = reflect a ⋆ reflect b := by
  funext g
  simp only [reflect_apply, conv_apply]
  rw [← Equiv.sum_comp (Equiv.neg G) (fun h => a h * b (-g - h))]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [Equiv.neg_apply]
  congr 1
  abel_nf

/-! ## The block-swap-and-negate equivalence Φ -/

/-- The duality equivalence on BB qubits: negate the group coordinate and
swap the L/R block. -/
def blockSwapNeg : (G × Fin 2) ≃ (G × Fin 2) :=
  (Equiv.neg G).prodCongr (Equiv.swap 0 1)

@[simp] lemma blockSwapNeg_apply_zero (g : G) :
    blockSwapNeg (g, (0 : Fin 2)) = (-g, 1) := by
  simp [blockSwapNeg]

@[simp] lemma blockSwapNeg_apply_one (g : G) :
    blockSwapNeg (g, (1 : Fin 2)) = (-g, 0) := by
  simp [blockSwapNeg, Equiv.swap_apply_right]

/-- The chain-level duality map `Φ c := c ∘ blockSwapNeg`. -/
def bbDualFn (c : G × Fin 2 → ZMod 2) : G × Fin 2 → ZMod 2 :=
  c ∘ blockSwapNeg

lemma blockSwapNeg_involutive (p : G × Fin 2) :
    blockSwapNeg (blockSwapNeg p) = p := by
  obtain ⟨g, j⟩ := p
  by_cases hj : j = 0
  · subst hj
    rw [blockSwapNeg_apply_zero, blockSwapNeg_apply_one, neg_neg]
  · have hj1 : j = 1 := by omega
    subst hj1
    rw [blockSwapNeg_apply_one, blockSwapNeg_apply_zero, neg_neg]

@[simp] lemma bbDualFn_bbDualFn (c : G × Fin 2 → ZMod 2) :
    bbDualFn (bbDualFn c) = c := by
  funext p
  change c (blockSwapNeg (blockSwapNeg p)) = c p
  rw [blockSwapNeg_involutive]

lemma bbDualFn_injective :
    Function.Injective (bbDualFn (G := G)) := by
  intro c d h
  have h2 := congrArg bbDualFn h
  rwa [bbDualFn_bbDualFn, bbDualFn_bbDualFn] at h2

lemma leftHalf_bbDualFn (c : G × Fin 2 → ZMod 2) :
    leftHalf (bbDualFn c) = reflect (rightHalf c) := by
  funext g
  change c (blockSwapNeg (g, 0)) = rightHalf c (-g)
  rw [blockSwapNeg_apply_zero]
  rfl

lemma rightHalf_bbDualFn (c : G × Fin 2 → ZMod 2) :
    rightHalf (bbDualFn c) = reflect (leftHalf c) := by
  funext g
  change c (blockSwapNeg (g, 1)) = leftHalf c (-g)
  rw [blockSwapNeg_apply_one]
  rfl

end Reflect

/-! ## Concrete transpose formulas for `dualBoundary` and `cutMap` -/

variable {G : Type} [Fintype G] [AddCommGroup G] [DecidableEq G]
variable (A B : G → ZMod 2)

/-- `∂₂` of a point mass: `∂₂(δ_f)(h, j) = A(h-f)` on the left block,
`B(h-f)` on the right. -/
lemma bbBoundary2Fn_single (f : G) (h : G) (j : Fin 2) :
    bbBoundary2Fn A B (Pi.single f 1) (h, j)
      = if j = 0 then A (h - f) else B (h - f) := by
  by_cases hj : j = 0
  · rw [if_pos hj]
    change (if j = 0 then (A ⋆ Pi.single f 1) h else (B ⋆ Pi.single f 1) h)
      = A (h - f)
    rw [if_pos hj, conv_comm A, conv_single_left_apply]
  · rw [if_neg hj]
    change (if j = 0 then (A ⋆ Pi.single f 1) h else (B ⋆ Pi.single f 1) h)
      = B (h - f)
    rw [if_neg hj, conv_comm B, conv_single_left_apply]

/-- Transpose formula for the dual boundary of the BB complex:
`dualBoundary c = (reflect A) ⋆ c_L + (reflect B) ⋆ c_R`. -/
theorem bb_dualBoundary_eq (c : G × Fin 2 → ZMod 2) :
    (bbChainComplex A B).dualBoundary c
      = fun f => (reflect A ⋆ leftHalf c) f
          + (reflect B ⋆ rightHalf c) f := by
  change (fun f : G =>
      ∑ p : G × Fin 2, c p * bbBoundary2Fn A B (Pi.single f 1) p) = _
  funext f
  have hL : (reflect A ⋆ leftHalf c) f
      = ∑ h : G, c (h, 0) * A (h - f) := by
    rw [conv_apply,
      ← Equiv.sum_comp (Equiv.subLeft f)
        (fun h => reflect A h * leftHalf c (f - h))]
    refine Finset.sum_congr rfl fun h _ => ?_
    simp only [Equiv.subLeft_apply, reflect_apply, neg_sub, sub_sub_cancel]
    rw [mul_comm]
    rfl
  have hR : (reflect B ⋆ rightHalf c) f
      = ∑ h : G, c (h, 1) * B (h - f) := by
    rw [conv_apply,
      ← Equiv.sum_comp (Equiv.subLeft f)
        (fun h => reflect B h * rightHalf c (f - h))]
    refine Finset.sum_congr rfl fun h _ => ?_
    simp only [Equiv.subLeft_apply, reflect_apply, neg_sub, sub_sub_cancel]
    rw [mul_comm]
    rfl
  rw [hL, hR, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Fin.sum_univ_two, bbBoundary2Fn_single, bbBoundary2Fn_single]
  simp

/-- `∂₁` of a left-block point mass: `∂₁(δ_(g,0))(v) = B(v-g)`. -/
lemma bbBoundary1Fn_single_left (g v : G) :
    bbBoundary1Fn A B (Pi.single ((g, 0) : G × Fin 2) 1) v = B (v - g) := by
  have hLhalf : leftHalf (Pi.single ((g, 0) : G × Fin 2) (1 : ZMod 2))
      = Pi.single g 1 := by
    funext h
    rw [leftHalf, Pi.single_apply, Pi.single_apply]
    by_cases hh : h = g
    · simp [hh]
    · simp [hh, Prod.ext_iff]
  have hRhalf : rightHalf (Pi.single ((g, 0) : G × Fin 2) (1 : ZMod 2)) = 0 := by
    funext h
    rw [rightHalf, Pi.single_apply]
    simp [Prod.ext_iff]
  have hzero : (A ⋆ (0 : G → ZMod 2)) v = 0 := by
    simp [conv_apply]
  rw [bbBoundary1Fn, hLhalf, hRhalf, conv_comm B, conv_single_left_apply,
    hzero, add_zero]

/-- `∂₁` of a right-block point mass: `∂₁(δ_(g,1))(v) = A(v-g)`. -/
lemma bbBoundary1Fn_single_right (g v : G) :
    bbBoundary1Fn A B (Pi.single ((g, 1) : G × Fin 2) 1) v = A (v - g) := by
  have hLhalf : leftHalf (Pi.single ((g, 1) : G × Fin 2) (1 : ZMod 2)) = 0 := by
    funext h
    rw [leftHalf, Pi.single_apply]
    simp [Prod.ext_iff]
  have hRhalf : rightHalf (Pi.single ((g, 1) : G × Fin 2) (1 : ZMod 2))
      = Pi.single g 1 := by
    funext h
    rw [rightHalf, Pi.single_apply, Pi.single_apply]
    by_cases hh : h = g
    · simp [hh]
    · simp [hh, Prod.ext_iff]
  have hzero : (B ⋆ (0 : G → ZMod 2)) v = 0 := by
    simp [conv_apply]
  rw [bbBoundary1Fn, hLhalf, hRhalf, conv_comm A, conv_single_left_apply,
    hzero, zero_add]

/-- Transpose formula for the cut map of the BB complex:
`cutMap s = ((reflect B) ⋆ s | (reflect A) ⋆ s)`. -/
theorem bb_cutMap_eq (s : G → ZMod 2) :
    (bbChainComplex A B).cutMap s
      = fun p : G × Fin 2 =>
          if p.2 = 0 then (reflect B ⋆ s) p.1 else (reflect A ⋆ s) p.1 := by
  change (fun e : G × Fin 2 =>
      ∑ v : G, s v * bbBoundary1Fn A B (Pi.single e 1) v) = _
  funext p
  obtain ⟨g, j⟩ := p
  have key : ∀ q : G → ZMod 2,
      (reflect q ⋆ s) g = ∑ v : G, s v * q (v - g) := by
    intro q
    rw [conv_apply,
      ← Equiv.sum_comp (Equiv.subLeft g) (fun h => reflect q h * s (g - h))]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [Equiv.subLeft_apply, reflect_apply, neg_sub, sub_sub_cancel]
    rw [mul_comm]
  by_cases hj : j = 0
  · subst hj
    change ∑ v : G, s v * bbBoundary1Fn A B (Pi.single ((g, 0) : G × Fin 2) 1) v
      = (reflect B ⋆ s) g
    rw [key B]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [bbBoundary1Fn_single_left]
  · have hj1 : j = 1 := by omega
    subst hj1
    change ∑ v : G, s v * bbBoundary1Fn A B (Pi.single ((g, 1) : G × Fin 2) 1) v
      = (reflect A ⋆ s) g
    rw [key A]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [bbBoundary1Fn_single_right]

/-! ## Φ exchanges primal and dual chain data -/

/-- `dualBoundary ∘ Φ = reflect ∘ ∂₁`: the dual boundary of a Φ-image is the
reflected primal boundary. -/
theorem dualBoundary_bbDualFn (c : G × Fin 2 → ZMod 2) :
    (bbChainComplex A B).dualBoundary (bbDualFn c)
      = reflect (bbBoundary1Fn A B c) := by
  rw [bb_dualBoundary_eq]
  funext f
  rw [leftHalf_bbDualFn, rightHalf_bbDualFn, ← reflect_conv, ← reflect_conv]
  simp only [reflect_apply, bbBoundary1Fn]
  ring

/-- `Φ ∘ ∂₂ = cutMap ∘ reflect`: Φ carries primal boundaries to dual
boundaries. -/
theorem bbDualFn_bbBoundary2Fn (f2 : G → ZMod 2) :
    bbDualFn (bbBoundary2Fn A B f2)
      = (bbChainComplex A B).cutMap (reflect (G := G) f2) := by
  rw [bb_cutMap_eq]
  funext p
  obtain ⟨g, j⟩ := p
  have hconv : ∀ q : G → ZMod 2,
      (q ⋆ f2) (-g) = (reflect q ⋆ reflect f2) g := by
    intro q
    have hq := congrFun (reflect_conv q f2) g
    rw [reflect_apply] at hq
    exact hq
  by_cases hj : j = 0
  · subst hj
    change bbBoundary2Fn A B f2 (blockSwapNeg (g, 0))
      = (reflect B ⋆ reflect f2) g
    rw [blockSwapNeg_apply_zero]
    change (B ⋆ f2) (-g) = (reflect B ⋆ reflect f2) g
    exact hconv B
  · have hj1 : j = 1 := by omega
    subst hj1
    change bbBoundary2Fn A B f2 (blockSwapNeg (g, 1))
      = (reflect A ⋆ reflect f2) g
    rw [blockSwapNeg_apply_one]
    change (A ⋆ f2) (-g) = (reflect A ⋆ reflect f2) g
    exact hconv A

/-- Φ carries cycles to dual cycles (and conversely, by involutivity). -/
theorem bbDual_mem_dualCycles_iff (c : G × Fin 2 → ZMod 2) :
    bbDualFn c ∈ (bbChainComplex A B).dualCycles
      ↔ c ∈ (bbChainComplex A B).cycles := by
  have h1 : bbDualFn c ∈ (bbChainComplex A B).dualCycles
      ↔ (bbChainComplex A B).dualBoundary (bbDualFn c) = 0 := Iff.rfl
  have h2 : c ∈ (bbChainComplex A B).cycles
      ↔ bbBoundary1Fn A B c = 0 := Iff.rfl
  rw [h1, h2, dualBoundary_bbDualFn]
  exact reflect_eq_zero_iff (bbBoundary1Fn A B c)

/-- Φ carries boundaries to dual boundaries (and conversely). -/
theorem bbDual_mem_dualBoundaries_iff (c : G × Fin 2 → ZMod 2) :
    bbDualFn c ∈ (bbChainComplex A B).dualBoundaries
      ↔ c ∈ (bbChainComplex A B).boundaries := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨reflect (G := G) s, ?_⟩
    apply bbDualFn_injective
    change bbDualFn (bbBoundary2Fn A B (reflect (G := G) s)) = bbDualFn c
    rw [bbDualFn_bbBoundary2Fn, reflect_reflect]
    exact hs
  · rintro ⟨f2, hf2⟩
    refine ⟨reflect (G := G) f2, ?_⟩
    change (bbChainComplex A B).cutMap (reflect (G := G) f2) = bbDualFn c
    rw [← bbDualFn_bbBoundary2Fn]
    exact congrArg bbDualFn hf2

/-! ## Φ preserves chain weight -/

/-- Filtering through an equivalence preserves the count. -/
lemma card_filter_comp_equiv {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (p : β → Prop) [DecidablePred p] :
    (Finset.univ.filter fun a => p (e a)).card
      = (Finset.univ.filter p).card := by
  apply Finset.card_bij (fun a _ => e a)
  · intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨Finset.mem_univ _, ha.2⟩
  · intro a₁ _ a₂ _ heq
    exact e.injective heq
  · intro b hb
    rw [Finset.mem_filter] at hb
    refine ⟨e.symm b, ?_, by simp⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Equiv.apply_symm_apply]
    exact hb.2

/-- Φ preserves chain weight. -/
theorem bbDual_chainWeight (c : G × Fin 2 → ZMod 2) :
    (bbChainComplex A B).chainWeight (bbDualFn c)
      = (bbChainComplex A B).chainWeight c := by
  unfold HomologicalCode.chainWeight HomologicalCode.chainSupport
  exact card_filter_comp_equiv blockSwapNeg (fun p => c p ≠ 0)

/-! ## Chain-level `d_X = d_Z` -/

/-- A chain-weight lower bound on nontrivial primal cycles holds iff the same
bound holds on nontrivial dual cycles: the chain-level `d_X = d_Z` for BB
codes. -/
theorem bb_cycle_bound_iff_dual_bound (K : ℕ) :
    (∀ c ∈ (bbChainComplex A B).cycles,
        c ∉ (bbChainComplex A B).boundaries →
        K ≤ (bbChainComplex A B).chainWeight c)
      ↔ (∀ c ∈ (bbChainComplex A B).dualCycles,
        c ∉ (bbChainComplex A B).dualBoundaries →
        K ≤ (bbChainComplex A B).chainWeight c) := by
  constructor
  · intro hX c hc hnb
    have hc' : bbDualFn (bbDualFn c) ∈ (bbChainComplex A B).dualCycles := by
      rwa [bbDualFn_bbDualFn]
    have hcyc : bbDualFn c ∈ (bbChainComplex A B).cycles :=
      (bbDual_mem_dualCycles_iff A B (bbDualFn c)).mp hc'
    have hnb' : bbDualFn c ∉ (bbChainComplex A B).boundaries := by
      intro hmem
      apply hnb
      have hdual := (bbDual_mem_dualBoundaries_iff A B (bbDualFn c)).mpr hmem
      rwa [bbDualFn_bbDualFn] at hdual
    have hbound := hX (bbDualFn c) hcyc hnb'
    rwa [bbDual_chainWeight] at hbound
  · intro hZ c hc hnb
    have hcyc : bbDualFn c ∈ (bbChainComplex A B).dualCycles :=
      (bbDual_mem_dualCycles_iff A B c).mpr hc
    have hnb' : bbDualFn c ∉ (bbChainComplex A B).dualBoundaries := by
      intro hmem
      exact hnb ((bbDual_mem_dualBoundaries_iff A B c).mp hmem)
    have hbound := hZ (bbDualFn c) hcyc hnb'
    rwa [bbDual_chainWeight] at hbound

end BB
end Homological
end Stabilizer
end Quantum
