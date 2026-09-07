/-
# Covering / transfer maps for `ZMod 2` chain complexes

Generic machinery for transferring chains along a covering map.  Three layers:

1. **Fiber summation** (`fiberSumFn`, `fiberSum`): the pushforward
   `(p_* u)(j) = ∑_{i ∈ f⁻¹(j)} u(i)` of a `ZMod 2`-chain along an arbitrary
   map `f : I → J` of finite index types.
2. **Convolution transfer** along an `AddMonoidHom` `π : G →+ H`:
   `π_*` intertwines convolution (`fiberSum_conv`), and pulled-back chains
   convolve through `π` (`conv_pullback`).  No injectivity or surjectivity
   hypotheses are needed — the fiber regrouping works unconditionally.
3. **Double covers**: for a 2:1 map `f` with fixed-point-free deck involution
   `σ` (axiomatized by `∀ i i', f i' = f i ↔ i' = i ∨ i' = σ i`), the
   pushforward kills pullbacks (`fiberSumFn_pullback`), is surjective given a
   section (`fiberSumFn_lift0`), has kernel exactly the pullbacks
   (`fiberSumFn_eq_zero_iff`), and satisfies the support-weight identity
   `|supp v| = |supp (p_* v)| + |overlap|` (`card_support_fiberSum_add_overlap`).

Finally, the BB-specific chain-map lemmas: if `π_* A_cov = A_base` and
`π_* B_cov = B_base`, then pushforward and pullback are chain maps between the
two BB chain complexes (`fiberSum_bbBoundary1Fn` / `2Fn`,
`pullback_bbBoundary1Fn` / `2Fn`).

Used by `QEC/Stabilizer/Codes/BivariateBicycle/` to transfer the gross
[[144,12,12]] code down to its [[72,12,6]] base along the `x ↦ x mod 6`
double cover.
-/

import QEC.Stabilizer.Framework.Homological.BBChainComplex

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open scoped BigOperators

/-! ## Fiber summation (pushforward) along a map of finite index types -/

section FiberSum

variable {I J : Type} [Fintype I] [DecidableEq J]

/-- Pushforward (fiber summation) of a `ZMod 2`-chain along `f : I → J`:
`(p_* u)(j) = ∑_{i ∈ f⁻¹(j)} u(i)`. -/
def fiberSumFn (f : I → J) (u : I → ZMod 2) : J → ZMod 2 :=
  fun j => ∑ i : I, if f i = j then u i else 0

@[simp] lemma fiberSumFn_apply (f : I → J) (u : I → ZMod 2) (j : J) :
    fiberSumFn f u j = ∑ i : I, if f i = j then u i else 0 := rfl

lemma fiberSumFn_add (f : I → J) (u v : I → ZMod 2) :
    fiberSumFn f (u + v) = fiberSumFn f u + fiberSumFn f v := by
  funext j
  simp only [fiberSumFn, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : f i = j <;> simp [h]

/-- `fiberSumFn` as a `ZMod 2`-linear map. -/
noncomputable def fiberSum (f : I → J) :
    (I → ZMod 2) →ₗ[ZMod 2] (J → ZMod 2) where
  toFun := fiberSumFn f
  map_add' := fiberSumFn_add f
  map_smul' s u := by
    funext j
    simp only [fiberSumFn, RingHom.id_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : f i = j <;> simp [h]

@[simp] lemma fiberSum_apply (f : I → J) (u : I → ZMod 2) :
    fiberSum f u = fiberSumFn f u := rfl

/-- Fiber summation along `Prod.map f id` acts blockwise: at `(j, b)` it is
fiber summation along `f` of the `b`-slice. -/
lemma fiberSumFn_prodMap {B : Type} [Fintype B] [DecidableEq B]
    (f : I → J) (c : I × B → ZMod 2) (j : J) (b : B) :
    fiberSumFn (Prod.map f id) c (j, b) = fiberSumFn f (fun i => c (i, b)) j := by
  simp only [fiberSumFn]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single b]
  · by_cases h : f i = j
    · simp [Prod.map, h]
    · simp [Prod.map, h]
  · intro b' _ hb'
    simp [hb']
  · intro habs
    exact absurd (Finset.mem_univ b) habs

end FiberSum

/-! ## Convolution transfer along a group homomorphism -/

section ConvTransfer

variable {G H : Type} [Fintype G] [AddCommGroup G]
  [Fintype H] [AddCommGroup H] [DecidableEq H]
variable (π : G →+ H)

/-- Pushforward intertwines convolution: `π_* (a ⋆ b) = (π_* a) ⋆ (π_* b)`.
No injectivity or surjectivity of `π` is needed. -/
lemma fiberSum_conv (a b : G → ZMod 2) :
    fiberSumFn ⇑π (a ⋆ b) = fiberSumFn ⇑π a ⋆ fiberSumFn ⇑π b := by
  funext j
  -- Both sides equal `∑ h, a h * (π_* b) (j - π h)`.
  have lhs_eq : fiberSumFn ⇑π (a ⋆ b) j
      = ∑ h : G, a h * fiberSumFn ⇑π b (j - π h) := by
    have key : ∀ h : G,
        (∑ g : G, if π g = j then a h * b (g - h) else 0)
          = a h * fiberSumFn ⇑π b (j - π h) := by
      intro h
      rw [← Equiv.sum_comp (Equiv.addRight h)
        (fun g => if π g = j then a h * b (g - h) else 0)]
      simp only [Equiv.coe_addRight, add_sub_cancel_right]
      rw [fiberSumFn_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      have hcond : π (m + h) = j ↔ π m = j - π h := by
        rw [map_add, eq_sub_iff_add_eq]
      by_cases hm : π m = j - π h
      · rw [if_pos (hcond.mpr hm), if_pos hm]
      · rw [if_neg (fun hc => hm (hcond.mp hc)), if_neg hm, mul_zero]
    calc fiberSumFn ⇑π (a ⋆ b) j
        = ∑ g : G, if π g = j then (∑ h : G, a h * b (g - h)) else 0 := rfl
      _ = ∑ g : G, ∑ h : G, (if π g = j then a h * b (g - h) else 0) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          by_cases hg : π g = j <;> simp [hg]
      _ = ∑ h : G, ∑ g : G, (if π g = j then a h * b (g - h) else 0) :=
          Finset.sum_comm
      _ = ∑ h : G, a h * fiberSumFn ⇑π b (j - π h) :=
          Finset.sum_congr rfl fun h _ => key h
  have rhs_eq : (fiberSumFn ⇑π a ⋆ fiberSumFn ⇑π b) j
      = ∑ h : G, a h * fiberSumFn ⇑π b (j - π h) := by
    rw [conv_apply]
    have expand : ∀ k : H, fiberSumFn ⇑π a k * fiberSumFn ⇑π b (j - k)
        = ∑ h : G, (if π h = k then a h * fiberSumFn ⇑π b (j - k) else 0) := by
      intro k
      rw [fiberSumFn_apply, Finset.sum_mul]
      exact Finset.sum_congr rfl fun h _ => by rw [ite_mul, zero_mul]
    rw [Finset.sum_congr rfl fun k _ => expand k, Finset.sum_comm]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.sum_ite_eq Finset.univ (π h)
      (fun k => a h * fiberSumFn ⇑π b (j - k))]
    simp
  rw [lhs_eq, rhs_eq]

/-- Convolving against a pulled-back chain pushes the left factor forward:
`a ⋆ (u ∘ π) = ((π_* a) ⋆ u) ∘ π`.  No injectivity hypothesis is needed —
the fiber regrouping works unconditionally. -/
lemma conv_pullback (a : G → ZMod 2) (u : H → ZMod 2) :
    a ⋆ (u ∘ ⇑π) = (fiberSumFn ⇑π a ⋆ u) ∘ ⇑π := by
  funext g
  simp only [Function.comp_apply, conv_apply]
  have lhs_eq : ∀ h : G, a h * u (π (g - h)) = a h * u (π g - π h) := by
    intro h
    rw [map_sub]
  rw [Finset.sum_congr rfl fun h _ => lhs_eq h]
  have expand : ∀ k : H, fiberSumFn ⇑π a k * u (π g - k)
      = ∑ h : G, (if π h = k then a h * u (π g - k) else 0) := by
    intro k
    rw [fiberSumFn_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun h _ => by rw [ite_mul, zero_mul]
  rw [Finset.sum_congr rfl fun k _ => expand k, Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_ite_eq Finset.univ (π h) (fun k => a h * u (π g - k))]
  simp

end ConvTransfer

/-! ## Double covers: 2:1 maps with a fixed-point-free deck involution

We axiomatize a double cover by a map `f : I → J` together with `σ : I → I`
such that `σ` has no fixed points and the fibers of `f` are exactly the
`σ`-orbits: `f i' = f i ↔ i' = i ∨ i' = σ i`.  (That `σ` is an involution
follows; see `sigma_involutive`.) -/

section DoubleCover

variable {I J : Type} {f : I → J} {σ : I → I}

/-- The deck map of a double cover is an involution (derived, not assumed). -/
lemma sigma_involutive (hσne : ∀ i, σ i ≠ i)
    (hfiber : ∀ i i', f i' = f i ↔ i' = i ∨ i' = σ i) (i : I) :
    σ (σ i) = i := by
  have h1 : f (σ i) = f i := (hfiber i (σ i)).mpr (Or.inr rfl)
  rcases (hfiber (σ i) i).mp h1.symm with h | h
  · exact absurd h.symm (hσne i)
  · exact h.symm

/-- The fiber of `f` through `i`, as a `Finset`, is the pair `{i, σ i}`. -/
lemma fiber_filter_eq [Fintype I] [DecidableEq I] [DecidableEq J]
    (hfiber : ∀ i i', f i' = f i ↔ i' = i ∨ i' = σ i) (i : I) :
    Finset.univ.filter (fun i' => f i' = f i) = {i, σ i} := by
  ext i'
  simp [hfiber i i']

/-- Two-point fiber formula: `(p_* v)(f i) = v i + v (σ i)`. -/
lemma fiberSumFn_pair [Fintype I] [DecidableEq J] (hσne : ∀ i, σ i ≠ i)
    (hfiber : ∀ i i', f i' = f i ↔ i' = i ∨ i' = σ i)
    (v : I → ZMod 2) (i : I) :
    fiberSumFn f v (f i) = v i + v (σ i) := by
  classical
  rw [fiberSumFn_apply, ← Finset.sum_filter, fiber_filter_eq hfiber i,
    Finset.sum_pair (Ne.symm (hσne i))]

/-- Pushforward annihilates pullbacks: `p_* (u ∘ f) = 0` (each fiber
contributes `u j + u j = 0` in characteristic 2). -/
lemma fiberSumFn_pullback [Fintype I] [DecidableEq J] (hσne : ∀ i, σ i ≠ i)
    (hfiber : ∀ i i', f i' = f i ↔ i' = i ∨ i' = σ i)
    (u : J → ZMod 2) :
    fiberSumFn f (u ∘ f) = 0 := by
  funext j
  by_cases hj : ∃ i, f i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [fiberSumFn_pair hσne hfiber, Function.comp_apply, Function.comp_apply,
      (hfiber i (σ i)).mpr (Or.inr rfl)]
    exact CharTwo.add_self_eq_zero _
  · rw [fiberSumFn_apply, Pi.zero_apply]
    exact Finset.sum_eq_zero fun i _ => if_neg (fun h => hj ⟨i, h⟩)

/-- Canonical lift of a base chain along a chosen section: supported on the
section's image, with the base values. -/
def lift0 [DecidableEq I] (f : I → J) (sec : J → I) (u : J → ZMod 2) :
    I → ZMod 2 :=
  fun i => if i = sec (f i) then u (f i) else 0

/-- The pushforward of the canonical lift recovers the base chain; in
particular `fiberSumFn f` is surjective whenever `f` has a section. -/
lemma fiberSumFn_lift0 [Fintype I] [DecidableEq I] [DecidableEq J]
    {sec : J → I} (hsec : ∀ j, f (sec j) = j)
    (u : J → ZMod 2) :
    fiberSumFn f (lift0 f sec u) = u := by
  funext j
  rw [fiberSumFn_apply, Finset.sum_eq_single (sec j)]
  · simp [lift0, hsec j]
  · intro i _ hne
    by_cases hfi : f i = j
    · rw [if_pos hfi, lift0, if_neg (by rw [hfi]; exact hne)]
    · rw [if_neg hfi]
  · intro habs
    exact absurd (Finset.mem_univ _) habs

/-- Exactness at the middle: the kernel of the pushforward is exactly the
image of the pullback (deck-invariant chains descend). -/
lemma fiberSumFn_eq_zero_iff [Fintype I] [DecidableEq J] (hσne : ∀ i, σ i ≠ i)
    (hfiber : ∀ i i', f i' = f i ↔ i' = i ∨ i' = σ i)
    {sec : J → I} (hsec : ∀ j, f (sec j) = j)
    (v : I → ZMod 2) :
    fiberSumFn f v = 0 ↔ ∃ u : J → ZMod 2, v = u ∘ f := by
  constructor
  · intro h0
    refine ⟨v ∘ sec, ?_⟩
    funext i
    have hpair : v i + v (σ i) = 0 := by
      have hi := congrFun h0 (f i)
      rwa [fiberSumFn_pair hσne hfiber, Pi.zero_apply] at hi
    have hconst : v (σ i) = v i := by
      have h2 : v i = v (σ i) := by
        rwa [CharTwo.add_eq_zero] at hpair
      exact h2.symm
    rcases (hfiber i (sec (f i))).mp (hsec (f i)) with h | h
    · rw [Function.comp_apply, Function.comp_apply, h]
    · rw [Function.comp_apply, Function.comp_apply, h, hconst]
  · rintro ⟨u, rfl⟩
    exact fiberSumFn_pullback hσne hfiber u

/-! ### The support-weight identity

For a double cover, `|supp v| = |supp (p_* v)| + |overlap|`, where the
overlap filter counts the points of `supp v` whose deck partner is also in
`supp v` (this double-counts the doubly-covered fibers, matching the
informal `2 · overlap`). -/

/-- Support-weight identity for a double cover. -/
theorem card_support_fiberSum_add_overlap [Fintype I] [Fintype J] [DecidableEq J]
    (hσne : ∀ i, σ i ≠ i)
    (hfiber : ∀ i i', f i' = f i ↔ i' = i ∨ i' = σ i)
    (v : I → ZMod 2) :
    (Finset.univ.filter fun i => v i ≠ 0).card
      = (Finset.univ.filter fun j => fiberSumFn f v j ≠ 0).card
        + (Finset.univ.filter fun i => v i ≠ 0 ∧ v (σ i) ≠ 0).card := by
  classical
  have hσσ := sigma_involutive hσne hfiber
  have hz : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  -- Split the support by whether the deck partner is also in the support.
  have hsplit :
      (Finset.univ.filter fun i => v i ≠ 0).card
        = (Finset.univ.filter fun i => v i ≠ 0 ∧ v (σ i) = 0).card
          + (Finset.univ.filter fun i => v i ≠ 0 ∧ v (σ i) ≠ 0).card := by
    have h1 := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter fun i : I => v i ≠ 0)
      (p := fun i => v (σ i) = 0)
    rw [Finset.filter_filter, Finset.filter_filter] at h1
    exact h1.symm
  -- The lonely part of the support biject with the support downstairs.
  have hbij :
      (Finset.univ.filter fun i => v i ≠ 0 ∧ v (σ i) = 0).card
        = (Finset.univ.filter fun j => fiberSumFn f v j ≠ 0).card := by
    apply Finset.card_bij (fun i _ => f i)
    · intro i hi
      rw [Finset.mem_filter] at hi
      obtain ⟨-, hvi, hvσ⟩ := hi
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [fiberSumFn_pair hσne hfiber, hvσ, add_zero]
      exact hvi
    · intro i₁ h₁ i₂ h₂ heq
      rw [Finset.mem_filter] at h₁ h₂
      rcases (hfiber i₁ i₂).mp heq.symm with h | h
      · exact h.symm
      · exfalso
        rw [h] at h₂
        exact h₂.2.1 h₁.2.2
    · intro j hj
      rw [Finset.mem_filter] at hj
      obtain ⟨-, hj0⟩ := hj
      have hex : ∃ i, f i = j := by
        by_contra hempty
        push Not at hempty
        apply hj0
        rw [fiberSumFn_apply]
        exact Finset.sum_eq_zero fun i _ => if_neg (hempty i)
      obtain ⟨g, rfl⟩ := hex
      rw [fiberSumFn_pair hσne hfiber] at hj0
      by_cases hg : v g ≠ 0
      · have hσg : v (σ g) = 0 := by
          by_contra hσg
          apply hj0
          rw [hz _ hg, hz _ hσg]
          decide
        exact ⟨g, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg, hσg⟩, rfl⟩
      · push Not at hg
        have hσg : v (σ g) ≠ 0 := by
          intro h0
          apply hj0
          rw [hg, h0, add_zero]
        refine ⟨σ g, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσg, ?_⟩, ?_⟩
        · rw [hσσ g]
          exact hg
        · exact (hfiber g (σ g)).mpr (Or.inr rfl)
  rw [hsplit, hbij]

/-- Pushing forward along a double cover can only shrink the support. -/
theorem card_support_fiberSum_le [Fintype I] [Fintype J] [DecidableEq J]
    (hσne : ∀ i, σ i ≠ i)
    (hfiber : ∀ i i', f i' = f i ↔ i' = i ∨ i' = σ i)
    (v : I → ZMod 2) :
    (Finset.univ.filter fun j => fiberSumFn f v j ≠ 0).card
      ≤ (Finset.univ.filter fun i => v i ≠ 0).card := by
  rw [card_support_fiberSum_add_overlap hσne hfiber v]
  exact Nat.le_add_right _ _

/-- The deck-overlap set upstairs has exactly twice the cardinality of the
overlapping fibers downstairs: overlap points come in deck pairs. -/
theorem card_overlap_eq_two_mul [Fintype I] [Fintype J]
    (hσne : ∀ i, σ i ≠ i)
    (hfiber : ∀ i i', f i' = f i ↔ i' = i ∨ i' = σ i)
    {sec : J → I} (hsec : ∀ j, f (sec j) = j)
    (v : I → ZMod 2) :
    (Finset.univ.filter fun i => v i ≠ 0 ∧ v (σ i) ≠ 0).card
      = 2 * (Finset.univ.filter fun j =>
          v (sec j) ≠ 0 ∧ v (σ (sec j)) ≠ 0).card := by
  classical
  have hσσ := sigma_involutive hσne hfiber
  have hmem_im : ∀ j, ∀ i ∈ ({sec j, σ (sec j)} : Finset I), f i = j := by
    intro j i hi
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · exact hsec j
    · rw [Finset.mem_singleton] at hi'
      subst hi'
      rw [(hfiber (sec j) (σ (sec j))).mpr (Or.inr rfl)]
      exact hsec j
  have hbiUnion : (Finset.univ.filter fun i => v i ≠ 0 ∧ v (σ i) ≠ 0)
      = (Finset.univ.filter fun j => v (sec j) ≠ 0 ∧ v (σ (sec j)) ≠ 0).biUnion
          (fun j => {sec j, σ (sec j)}) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hi, hσi⟩
      refine ⟨f i, ?_, ?_⟩
      · have h1 : f i = f (sec (f i)) := (hsec (f i)).symm
        rcases (hfiber (sec (f i)) i).mp h1 with h | h
        · rw [← h]
          exact ⟨hi, hσi⟩
        · constructor
          · rw [← hσσ (sec (f i)), ← h]
            exact hσi
          · rw [← h]
            exact hi
      · have h1 : f i = f (sec (f i)) := (hsec (f i)).symm
        rcases (hfiber (sec (f i)) i).mp h1 with h | h
        · exact Finset.mem_insert.mpr (Or.inl h)
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h))
    · rintro ⟨j, ⟨hj0, hj1⟩, hij⟩
      rcases Finset.mem_insert.mp hij with rfl | hi'
      · exact ⟨hj0, hj1⟩
      · rw [Finset.mem_singleton] at hi'
        subst hi'
        refine ⟨hj1, ?_⟩
        rw [hσσ (sec j)]
        exact hj0
  have hdisj : ∀ j₁ ∈ (Finset.univ.filter fun j =>
        v (sec j) ≠ 0 ∧ v (σ (sec j)) ≠ 0),
      ∀ j₂ ∈ (Finset.univ.filter fun j =>
        v (sec j) ≠ 0 ∧ v (σ (sec j)) ≠ 0), j₁ ≠ j₂ →
      Disjoint ({sec j₁, σ (sec j₁)} : Finset I) {sec j₂, σ (sec j₂)} := by
    intro j₁ _ j₂ _ hne
    refine Finset.disjoint_left.mpr fun i hi₁ hi₂ => ?_
    exact hne ((hmem_im j₁ i hi₁).symm.trans (hmem_im j₂ i hi₂))
  rw [hbiUnion, Finset.card_biUnion hdisj]
  have hcard : ∀ j, ({sec j, σ (sec j)} : Finset I).card = 2 := fun j =>
    Finset.card_pair (Ne.symm (hσne (sec j)))
  rw [Finset.sum_congr rfl fun j _ => hcard j, Finset.sum_const, smul_eq_mul,
    mul_comm]

/-- The support of a pullback along a double cover is exactly twice the base
support: each base point in the support contributes its full two-point
fiber. -/
theorem card_support_pullback [Fintype I] [Fintype J]
    (hσne : ∀ i, σ i ≠ i)
    (hfiber : ∀ i i', f i' = f i ↔ i' = i ∨ i' = σ i)
    {sec : J → I} (hsec : ∀ j, f (sec j) = j)
    (u : J → ZMod 2) :
    (Finset.univ.filter fun i => u (f i) ≠ 0).card
      = 2 * (Finset.univ.filter fun j => u j ≠ 0).card := by
  classical
  -- Every member of the fiber pair `{sec j, σ (sec j)}` maps to `j`.
  have hmem_im : ∀ j, ∀ i ∈ ({sec j, σ (sec j)} : Finset I), f i = j := by
    intro j i hi
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · exact hsec j
    · rw [Finset.mem_singleton] at hi'
      subst hi'
      rw [(hfiber (sec j) (σ (sec j))).mpr (Or.inr rfl)]
      exact hsec j
  -- The pullback support is the disjoint union of the fiber pairs over the
  -- base support.
  have hbiUnion : (Finset.univ.filter fun i => u (f i) ≠ 0)
      = (Finset.univ.filter fun j => u j ≠ 0).biUnion
          (fun j => {sec j, σ (sec j)}) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · intro hi
      refine ⟨f i, hi, ?_⟩
      have h1 : f i = f (sec (f i)) := (hsec (f i)).symm
      rcases (hfiber (sec (f i)) i).mp h1 with h | h
      · exact Finset.mem_insert.mpr (Or.inl h)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h))
    · rintro ⟨j, hj, hij⟩
      rw [hmem_im j i hij]
      exact hj
  have hdisj : ∀ j₁ ∈ (Finset.univ.filter fun j => u j ≠ 0),
      ∀ j₂ ∈ (Finset.univ.filter fun j => u j ≠ 0), j₁ ≠ j₂ →
      Disjoint ({sec j₁, σ (sec j₁)} : Finset I) {sec j₂, σ (sec j₂)} := by
    intro j₁ _ j₂ _ hne
    refine Finset.disjoint_left.mpr fun i hi₁ hi₂ => ?_
    exact hne ((hmem_im j₁ i hi₁).symm.trans (hmem_im j₂ i hi₂))
  rw [hbiUnion, Finset.card_biUnion hdisj]
  have hcard : ∀ j, ({sec j, σ (sec j)} : Finset I).card = 2 := fun j =>
    Finset.card_pair (Ne.symm (hσne (sec j)))
  rw [Finset.sum_congr rfl fun j _ => hcard j, Finset.sum_const, smul_eq_mul,
    mul_comm]

end DoubleCover

/-! ## BB chain-map lemmas

Given `π : G →+ H` with `π_* A_cov = A_base` and `π_* B_cov = B_base`, the
pushforward (`fiberSum` along `π` on `C0`/`C2` and along `Prod.map π id` on
`C1`) and the pullback (`· ∘ π`) are chain maps between the corresponding BB
chain complexes. -/

section BBChainMaps

variable {G H : Type} [Fintype G] [AddCommGroup G]
  [Fintype H] [AddCommGroup H] [DecidableEq H]
variable (π : G →+ H) (Ac Bc : G → ZMod 2) (Ab Bb : H → ZMod 2)

omit [Fintype H] in
/-- Pushforward on 1-chains acts on the left half by pushforward on `G`. -/
lemma leftHalf_fiberSumFn_prodMap (c : G × Fin 2 → ZMod 2) :
    leftHalf (fiberSumFn (Prod.map ⇑π id) c) = fiberSumFn ⇑π (leftHalf c) := by
  funext j
  exact fiberSumFn_prodMap ⇑π c j 0

omit [Fintype H] in
/-- Pushforward on 1-chains acts on the right half by pushforward on `G`. -/
lemma rightHalf_fiberSumFn_prodMap (c : G × Fin 2 → ZMod 2) :
    rightHalf (fiberSumFn (Prod.map ⇑π id) c) = fiberSumFn ⇑π (rightHalf c) := by
  funext j
  exact fiberSumFn_prodMap ⇑π c j 1

omit [Fintype G] [Fintype H] [DecidableEq H] in
/-- Pullback on 1-chains acts on the left half by pullback on `G`. -/
lemma leftHalf_pullback_prodMap (u : H × Fin 2 → ZMod 2) :
    leftHalf (u ∘ Prod.map ⇑π id) = (leftHalf u) ∘ ⇑π := rfl

omit [Fintype G] [Fintype H] [DecidableEq H] in
/-- Pullback on 1-chains acts on the right half by pullback on `G`. -/
lemma rightHalf_pullback_prodMap (u : H × Fin 2 → ZMod 2) :
    rightHalf (u ∘ Prod.map ⇑π id) = (rightHalf u) ∘ ⇑π := rfl

/-- The pushforward is a chain map at level 1: `p₀ ∘ ∂₁ = ∂₁ ∘ p₁`. -/
lemma fiberSum_bbBoundary1Fn
    (hA : fiberSumFn ⇑π Ac = Ab) (hB : fiberSumFn ⇑π Bc = Bb)
    (c : G × Fin 2 → ZMod 2) :
    fiberSumFn ⇑π (bbBoundary1Fn Ac Bc c)
      = bbBoundary1Fn Ab Bb (fiberSumFn (Prod.map ⇑π id) c) := by
  have hsum : bbBoundary1Fn Ac Bc c
      = Bc ⋆ leftHalf c + Ac ⋆ rightHalf c := rfl
  rw [hsum, fiberSumFn_add, fiberSum_conv π Bc (leftHalf c),
    fiberSum_conv π Ac (rightHalf c), hA, hB]
  funext j
  rw [bbBoundary1Fn, leftHalf_fiberSumFn_prodMap, rightHalf_fiberSumFn_prodMap,
    Pi.add_apply]

/-- The pushforward is a chain map at level 2: `p₁ ∘ ∂₂ = ∂₂ ∘ p₂`. -/
lemma fiberSum_bbBoundary2Fn
    (hA : fiberSumFn ⇑π Ac = Ab) (hB : fiberSumFn ⇑π Bc = Bb)
    (f2 : G → ZMod 2) :
    fiberSumFn (Prod.map ⇑π id) (bbBoundary2Fn Ac Bc f2)
      = bbBoundary2Fn Ab Bb (fiberSumFn ⇑π f2) := by
  funext p
  obtain ⟨j, b⟩ := p
  rw [fiberSumFn_prodMap ⇑π (bbBoundary2Fn Ac Bc f2) j b]
  by_cases hb : b = 0
  · subst hb
    have hslice : (fun h => bbBoundary2Fn Ac Bc f2 (h, (0 : Fin 2)))
        = Ac ⋆ f2 := by
      funext h
      simp [bbBoundary2Fn]
    rw [hslice, fiberSum_conv π Ac f2, hA]
    simp [bbBoundary2Fn]
  · have hb1 : b = 1 := by omega
    subst hb1
    have hslice : (fun h => bbBoundary2Fn Ac Bc f2 (h, (1 : Fin 2)))
        = Bc ⋆ f2 := by
      funext h
      simp [bbBoundary2Fn]
    rw [hslice, fiberSum_conv π Bc f2, hB]
    simp [bbBoundary2Fn]

/-- The pullback is a chain map at level 1: `∂₁ ∘ τ₁ = τ₀ ∘ ∂₁`. -/
lemma pullback_bbBoundary1Fn
    (hA : fiberSumFn ⇑π Ac = Ab) (hB : fiberSumFn ⇑π Bc = Bb)
    (u : H × Fin 2 → ZMod 2) :
    bbBoundary1Fn Ac Bc (u ∘ Prod.map ⇑π id)
      = (bbBoundary1Fn Ab Bb u) ∘ ⇑π := by
  have hL : Bc ⋆ ((leftHalf u) ∘ ⇑π) = (Bb ⋆ leftHalf u) ∘ ⇑π := by
    rw [conv_pullback π Bc (leftHalf u), hB]
  have hR : Ac ⋆ ((rightHalf u) ∘ ⇑π) = (Ab ⋆ rightHalf u) ∘ ⇑π := by
    rw [conv_pullback π Ac (rightHalf u), hA]
  funext g
  rw [bbBoundary1Fn, leftHalf_pullback_prodMap, rightHalf_pullback_prodMap,
    hL, hR]
  rfl

/-- The pullback is a chain map at level 2: `∂₂ ∘ τ₂ = τ₁ ∘ ∂₂`. -/
lemma pullback_bbBoundary2Fn
    (hA : fiberSumFn ⇑π Ac = Ab) (hB : fiberSumFn ⇑π Bc = Bb)
    (f2 : H → ZMod 2) :
    bbBoundary2Fn Ac Bc (f2 ∘ ⇑π)
      = (bbBoundary2Fn Ab Bb f2) ∘ Prod.map ⇑π id := by
  have hA' : Ac ⋆ (f2 ∘ ⇑π) = (Ab ⋆ f2) ∘ ⇑π := by
    rw [conv_pullback π Ac f2, hA]
  have hB' : Bc ⋆ (f2 ∘ ⇑π) = (Bb ⋆ f2) ∘ ⇑π := by
    rw [conv_pullback π Bc f2, hB]
  funext p
  obtain ⟨g, b⟩ := p
  fin_cases b
  · change (Ac ⋆ (f2 ∘ ⇑π)) g = bbBoundary2Fn Ab Bb f2 (π g, 0)
    rw [hA']
    rfl
  · change (Bc ⋆ (f2 ∘ ⇑π)) g = bbBoundary2Fn Ab Bb f2 (π g, 1)
    rw [hB']
    rfl

end BBChainMaps

end BB
end Homological
end Stabilizer
end Quantum
