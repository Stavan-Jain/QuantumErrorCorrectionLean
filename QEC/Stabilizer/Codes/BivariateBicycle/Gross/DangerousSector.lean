/-
# Phase 3: the dangerous sector — (M) modulo the light-stabilizer classification

The dangerous-sector bound (`DangerousSectorGe12`, A4 Theorem C) reduced to a
single named hypothesis, `LightStabilizerClassification` (A4 §6.3: every
nonzero base boundary of weight ≤ 11 is a hexagon `∂₂δ_g` or a D-pair
`∂₂(δ_g + δ_{g+d})`, `d ∈ pairDirections`).  Everything else is proven here:

* the **sheet decomposition** of cover chains (`sheet0`, `sheet1`) and the
  refined slice identity `|v| = |b| + 2·|supp(sheet0 v) ∖ supp b|`
  (`gross_chainWeight_sheet_eq`);
* the **m-rungs** (A4 §6.4), from the small-cycle theorem:
  - `m(hexagon) ≥ 3` — a dangerous cycle over a hexagon with ≤ 2 off-support
    qubits descends (after subtracting the lifted stabilizer) to a base cycle
    that, after an `u ↦ u + b` flip, has weight ≤ 5, hence vanishes —
    trivializing `v`;
  - `m(D-pair) ≥ 1` — over a D-pair with zero off-support overlap, the
    descended cycle lives in the 11-qubit union; its four translates by
    `{0, b₁, b₂, b₁+b₂}` have total weight `2·11 = 22 < 4·6`, so one of them
    is a small cycle, again trivializing `v`;
* the assembly `dangerous_sector_of_classification`.

## Convention bridge (lab notes → repo)

Repo convention: `∂₂ f = (A⋆f | B⋆f)`, `∂₁ c = B⋆c_L + A⋆c_R`.
**Repo-left = lab-right.**  Sheet 0 = the `coverSec` image (`x ∈ {0..5}`).
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Gross.BaseDistance

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open scoped BigOperators

-- Defeq checks through `coverPush1`/`coverPull1` and the lifted-stabilizer
-- bridges unfold deep `Prod`/`ZMod` instance chains (same as
-- `CoverTransfer.lean`).
set_option maxRecDepth 4096

/-! ## Sheet decomposition of cover 1-chains -/

/-- Sheet-0 restriction of a cover 1-chain (via the section `coverSec1`). -/
def sheet0 (v : GrossGroup × Fin 2 → ZMod 2) : BaseGroup × Fin 2 → ZMod 2 :=
  fun q => v (coverSec1 q)

/-- Sheet-1 restriction of a cover 1-chain (deck partner of sheet 0). -/
def sheet1 (v : GrossGroup × Fin 2 → ZMod 2) : BaseGroup × Fin 2 → ZMod 2 :=
  fun q => v (deckSigma1 (coverSec1 q))

@[simp] lemma sheet0_apply (v : GrossGroup × Fin 2 → ZMod 2)
    (q : BaseGroup × Fin 2) : sheet0 v q = v (coverSec1 q) := rfl

@[simp] lemma sheet1_apply (v : GrossGroup × Fin 2 → ZMod 2)
    (q : BaseGroup × Fin 2) : sheet1 v q = v (deckSigma1 (coverSec1 q)) := rfl

lemma sheet0_add (v w : GrossGroup × Fin 2 → ZMod 2) :
    sheet0 (v + w) = sheet0 v + sheet0 w := rfl

lemma sheet1_add (v w : GrossGroup × Fin 2 → ZMod 2) :
    sheet1 (v + w) = sheet1 v + sheet1 w := rfl

/-- The two sheets sum to the pushforward. -/
lemma sheet0_add_sheet1 (v : GrossGroup × Fin 2 → ZMod 2)
    (j : BaseGroup × Fin 2) :
    sheet0 v j + sheet1 v j = coverPush1 v j := by
  have h := fiberSumFn_pair deckSigma1_ne coverPi_prodMap_fiber v (coverSec1 j)
  rw [coverPi_prodMap_coverSec1 j] at h
  exact h.symm

/-- Sheet-0 restriction inverts the pullback. -/
lemma sheet0_coverPull1 (u : BaseGroup × Fin 2 → ZMod 2) :
    sheet0 (coverPull1 u) = u := by
  funext q
  change u (Prod.map ⇑coverPi id (coverSec1 q)) = u q
  rw [coverPi_prodMap_coverSec1 q]

/-! ## The refined slice identity -/

/-- The deck-overlap of `v` counts twice the overlapping fibers. -/
lemma overlapCount_eq_two_mul_sheets (v : GrossGroup × Fin 2 → ZMod 2) :
    overlapCount v
      = 2 * (Finset.univ.filter fun j =>
          sheet0 v j ≠ 0 ∧ sheet1 v j ≠ 0).card := by
  exact card_overlap_eq_two_mul deckSigma1_ne coverPi_prodMap_fiber
    coverPi_prodMap_coverSec1 v

/-- **Refined slice identity**: `|v| = |p(v)| + 2·|supp(sheet0 v) ∖ supp p(v)|`.
-/
theorem gross_chainWeight_sheet_eq (v : GrossGroup × Fin 2 → ZMod 2) :
    grossComplex.chainWeight v
      = bb72Complex.chainWeight (coverPush1 v)
        + 2 * (Finset.univ.filter fun j =>
            sheet0 v j ≠ 0 ∧ coverPush1 v j = 0).card := by
  rw [gross_chainWeight_eq v, overlapCount_eq_two_mul_sheets]
  have hfilter : (Finset.univ.filter fun j => sheet0 v j ≠ 0 ∧ sheet1 v j ≠ 0)
      = Finset.univ.filter fun j =>
          sheet0 v j ≠ 0 ∧ coverPush1 v j = 0 := by
    apply Finset.filter_congr
    intro j _
    have key : ∀ a b c : ZMod 2, a + b = c →
        ((a ≠ 0 ∧ b ≠ 0) ↔ (a ≠ 0 ∧ c = 0)) := by decide
    exact key _ _ _ (sheet0_add_sheet1 v j)
  rw [hfilter]

/-! ## The lifted stabilizer -/

/-- Sheet-0 lift of a base 2-chain to the cover. -/
def liftC2 (ξ : BaseGroup → ZMod 2) : GrossGroup → ZMod 2 :=
  lift0 ⇑coverPi coverSec ξ

lemma coverPush0_liftC2 (ξ : BaseGroup → ZMod 2) :
    fiberSumFn ⇑coverPi (liftC2 ξ) = ξ :=
  fiberSumFn_lift0 coverPi_coverSec ξ

/-- The lifted stabilizer of a base 2-chain: `∂₂(gross) (lift ξ)`. -/
def liftStab (ξ : BaseGroup → ZMod 2) : GrossGroup × Fin 2 → ZMod 2 :=
  bbBoundary2Fn grossA grossB (liftC2 ξ)

lemma liftStab_mem_boundaries (ξ : BaseGroup → ZMod 2) :
    liftStab ξ ∈ grossComplex.boundaries :=
  ⟨liftC2 ξ, rfl⟩

/-- The lifted stabilizer pushes forward to the base stabilizer. -/
lemma coverPush1_liftStab (ξ : BaseGroup → ZMod 2) :
    coverPush1 (liftStab ξ) = bbBoundary2Fn baseA baseB ξ := by
  change fiberSumFn (Prod.map ⇑coverPi id) (bbBoundary2Fn grossA grossB (liftC2 ξ))
    = bbBoundary2Fn baseA baseB ξ
  rw [fiberSum_bbBoundary2Fn coverPi grossA grossB baseA baseB
    coverPush_grossA coverPush_grossB (liftC2 ξ), coverPush0_liftC2]

/-! ## Plumbing for the rung proofs -/

/-- The descended chain of a dangerous normalization is a base cycle. -/
lemma descend_cycle {u : BaseGroup × Fin 2 → ZMod 2}
    (h : coverPull1 u ∈ grossComplex.cycles) :
    bbBoundary1Fn baseA baseB u = 0 := by
  have h1 : grossComplex.boundary1 (coverPull1 u) = 0 := h
  rw [coverPull_boundary1_comm] at h1
  apply coverPull0_injective
  change coverPull0 (bb72Complex.boundary1 u) = coverPull0 0
  rw [h1]
  exact (map_zero coverPull0).symm

/-- Support split of a chain by an indicator set: `|u| = |u on s| + |u off s|`
for any decidable predicate `s`. -/
lemma card_filter_split {I : Type} [Fintype I] (u : I → ZMod 2)
    (P : I → Prop) [DecidablePred P] :
    (Finset.univ.filter fun j => u j ≠ 0).card
      = ((Finset.univ.filter fun j => u j ≠ 0).filter P).card
        + ((Finset.univ.filter fun j => u j ≠ 0).filter fun j => ¬ P j).card :=
  (Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun j => u j ≠ 0) (p := P)).symm

/-! ### Pointwise `∂₂` plumbing (kernel-decide support)

The rung side conditions below are finite checks over `∂₂` of point masses.
Evaluating the convolution sums inside a kernel `decide` is too slow, so each
check is first reduced to the pointwise form
`∂₂(δ_c)(h, j) = if j = 0 then A (h - c) else B (h - c)`
(`bbBoundary2Fn_single_pt`), the lifted stabilizer of a point mass to a gross
point mass at the section (`liftC2_single`), and the D-pair statements to their
`g = 0` translates (`card_filter_comp_equiv`); only the reduced forms are swept
by `decide +kernel`. -/

/-- Pair-argument form of `bbBoundary2Fn_single`. -/
private lemma bbBoundary2Fn_single_pt {G : Type} [Fintype G] [AddCommGroup G]
    [DecidableEq G] (A B : G → ZMod 2) (c : G) (p : G × Fin 2) :
    bbBoundary2Fn A B (Pi.single c 1) p
      = if p.2 = 0 then A (p.1 - c) else B (p.1 - c) := by
  obtain ⟨h, j⟩ := p
  exact bbBoundary2Fn_single A B c h j

/-- Sheet-0 lift of a base point mass is the gross point mass at the section
point. -/
private lemma liftC2_single : ∀ g : BaseGroup,
    liftC2 (Pi.single g 1) = Pi.single (coverSec g) 1 := by
  decide +kernel

private lemma liftC2_add (f f' : BaseGroup → ZMod 2) :
    liftC2 (f + f') = liftC2 f + liftC2 f' := by
  funext i
  show (if i = coverSec (coverPi i) then (f + f') (coverPi i) else 0)
    = (if i = coverSec (coverPi i) then f (coverPi i) else 0)
      + (if i = coverSec (coverPi i) then f' (coverPi i) else 0)
  by_cases h : i = coverSec (coverPi i)
  · rw [if_pos h, if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h, if_neg h, add_zero]

/-! ## The hexagon rung (`m(hexagon) ≥ 3`) -/

private lemma hexagon_weight_check : ∀ g : BaseGroup,
    (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
      (if j.2 = 0 then baseA (j.1 - g) else baseB (j.1 - g)) ≠ 0).card = 6 := by
  decide +kernel

/-- Hexagons have weight 6. -/
lemma hexagon_weight : ∀ g : BaseGroup,
    (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
      bbBoundary2Fn baseA baseB (Pi.single g 1) j ≠ 0).card = 6 := by
  intro g
  have hfil : (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
      bbBoundary2Fn baseA baseB (Pi.single g 1) j ≠ 0)
      = Finset.univ.filter fun j : BaseGroup × Fin 2 =>
          (if j.2 = 0 then baseA (j.1 - g) else baseB (j.1 - g)) ≠ 0 := by
    apply Finset.filter_congr
    intro j _
    rw [bbBoundary2Fn_single_pt]
  rw [hfil]
  exact hexagon_weight_check g

private lemma hexagon_seam_check : ∀ g : BaseGroup, ∀ j : BaseGroup × Fin 2,
    (if j.2 = 0 then grossA (coverSec j.1 - coverSec g)
      else grossB (coverSec j.1 - coverSec g)) ≠ 0 →
    (if j.2 = 0 then baseA (j.1 - g) else baseB (j.1 - g)) ≠ 0 := by
  decide +kernel

/-- The sheet-0 seam part of a lifted hexagon is supported in the hexagon. -/
lemma hexagon_seam_subset : ∀ g : BaseGroup, ∀ j : BaseGroup × Fin 2,
    sheet0 (liftStab (Pi.single g 1)) j ≠ 0 →
    bbBoundary2Fn baseA baseB (Pi.single g 1) j ≠ 0 := by
  intro g j hne
  have e1 : sheet0 (liftStab (Pi.single g 1)) j
      = if j.2 = 0 then grossA (coverSec j.1 - coverSec g)
        else grossB (coverSec j.1 - coverSec g) := by
    show bbBoundary2Fn grossA grossB (liftC2 (Pi.single g 1)) (coverSec1 j) = _
    rw [liftC2_single g, bbBoundary2Fn_single_pt]
    rfl
  rw [e1] at hne
  rw [bbBoundary2Fn_single_pt]
  exact hexagon_seam_check g j hne

/-- **The hexagon rung**: a nontrivial dangerous cycle over a hexagon has weight
≥ 12. -/
theorem dangerous_hexagon_bound (g : BaseGroup)
    {v : GrossGroup × Fin 2 → ZMod 2}
    (hv : v ∈ grossComplex.cycles) (hnb : v ∉ grossComplex.boundaries)
    (hb : coverPush1 v = bbBoundary2Fn baseA baseB (Pi.single g 1)) :
    12 ≤ grossComplex.chainWeight v := by
  classical
  set b : BaseGroup × Fin 2 → ZMod 2 :=
    bbBoundary2Fn baseA baseB (Pi.single g 1) with hbdef
  -- the off-support count
  by_cases hoff : 3 ≤ (Finset.univ.filter fun j =>
      sheet0 v j ≠ 0 ∧ coverPush1 v j = 0).card
  · -- |v| = 6 + 2·off ≥ 12
    rw [gross_chainWeight_sheet_eq, hb, bb72Complex_chainWeight_eq,
      hexagon_weight g]
    rw [hb] at hoff
    omega
  · push Not at hoff
    exfalso
    -- normalize: subtract the lifted stabilizer
    have hpush : coverPush1 (v + liftStab (Pi.single g 1)) = 0 := by
      rw [map_add, hb, coverPush1_liftStab]
      funext j
      exact CharTwo.add_self_eq_zero _
    obtain ⟨u, hu⟩ := (coverPush1_eq_zero_iff _).mp hpush
    -- u is a base cycle
    have hvtilde_cyc : coverPull1 u ∈ grossComplex.cycles := by
      rw [← hu]
      have h1 : bbBoundary1Fn grossA grossB (v + liftStab (Pi.single g 1))
          = 0 := by
        have hv0 : bbBoundary1Fn grossA grossB v = 0 := hv
        have hs0 : bbBoundary1Fn grossA grossB (liftStab (Pi.single g 1)) = 0 :=
          bbBoundaryFn_comp grossA grossB (liftC2 (Pi.single g 1))
        rw [bbBoundary1Fn_add, hv0, hs0, add_zero]
      exact h1
    have hu_cyc : bbBoundary1Fn baseA baseB u = 0 := descend_cycle hvtilde_cyc
    -- u = sheet0 v + seam part
    have hu_eq : u = sheet0 v + sheet0 (liftStab (Pi.single g 1)) := by
      have := congrArg sheet0 hu
      rw [sheet0_coverPull1] at this
      rw [← this]
      rfl
    -- off-hexagon support of u is small
    have hu_off : ((Finset.univ.filter fun j => u j ≠ 0).filter
        fun j => ¬ b j ≠ 0).card ≤ 2 := by
      have hsub : (Finset.univ.filter fun j => u j ≠ 0).filter
          (fun j => ¬ b j ≠ 0)
          ⊆ Finset.univ.filter fun j => sheet0 v j ≠ 0 ∧ coverPush1 v j = 0 := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        obtain ⟨hju, hjb⟩ := hj
        push Not at hjb
        have hseam : liftStab (Pi.single g 1) (coverSec1 j) = 0 := by
          by_contra hcon
          exact (hexagon_seam_subset g j hcon) hjb
        constructor
        · rw [hu_eq] at hju
          simpa [Pi.add_apply, hseam] using hju
        · rw [hb]
          exact hjb
      have := Finset.card_le_card hsub
      omega
    -- the two candidate small chains: u and u + b
    have hsplit_b : ((Finset.univ.filter fun j => u j ≠ 0).filter
          fun j => b j ≠ 0).card
        + ((Finset.univ.filter fun j => (u + b) j ≠ 0).filter
          fun j => b j ≠ 0).card = 6 := by
      have h1 : ((Finset.univ.filter fun j => b j ≠ 0).filter
            fun j => u j ≠ 0).card
          + ((Finset.univ.filter fun j => b j ≠ 0).filter
            fun j => ¬ u j ≠ 0).card = 6 := by
        rw [Finset.card_filter_add_card_filter_not, hexagon_weight g]
      have e1 : (Finset.univ.filter fun j => b j ≠ 0).filter
            (fun j => u j ≠ 0)
          = (Finset.univ.filter fun j => u j ≠ 0).filter fun j => b j ≠ 0 := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact and_comm
      have e2 : (Finset.univ.filter fun j => b j ≠ 0).filter
            (fun j => ¬ u j ≠ 0)
          = (Finset.univ.filter fun j => (u + b) j ≠ 0).filter
            fun j => b j ≠ 0 := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply]
        have key : ∀ a c : ZMod 2, ((c ≠ 0 ∧ ¬ a ≠ 0) ↔ (a + c ≠ 0 ∧ c ≠ 0)) := by
          decide
        exact key (u j) (b j)
      rw [e1, e2] at h1
      exact h1
    have hoff_ub : ((Finset.univ.filter fun j => (u + b) j ≠ 0).filter
        fun j => ¬ b j ≠ 0).card ≤ 2 := by
      have e3 : (Finset.univ.filter fun j => (u + b) j ≠ 0).filter
            (fun j => ¬ b j ≠ 0)
          = (Finset.univ.filter fun j => u j ≠ 0).filter
            fun j => ¬ b j ≠ 0 := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply]
        have key : ∀ a c : ZMod 2, ((a + c ≠ 0 ∧ ¬ c ≠ 0) ↔ (a ≠ 0 ∧ ¬ c ≠ 0)) := by
          decide
        exact key (u j) (b j)
      rw [e3]
      exact hu_off
    -- choose the lighter of u, u + b
    have hsmall : ∃ u'' : BaseGroup × Fin 2 → ZMod 2,
        bbBoundary1Fn baseA baseB u'' = 0 ∧
        (Finset.univ.filter fun j => u'' j ≠ 0).card ≤ 5 ∧
        (u'' = u ∨ u'' = u + b) := by
      have hb_cyc : bbBoundary1Fn baseA baseB b = 0 :=
        bbBoundaryFn_comp baseA baseB (Pi.single g 1)
      by_cases hcase : ((Finset.univ.filter fun j => u j ≠ 0).filter
          fun j => b j ≠ 0).card ≤ 3
      · refine ⟨u, hu_cyc, ?_, Or.inl rfl⟩
        rw [card_filter_split u fun j => b j ≠ 0]
        omega
      · refine ⟨u + b, ?_, ?_, Or.inr rfl⟩
        · rw [bbBoundary1Fn_add, hu_cyc, hb_cyc, add_zero]
        · rw [card_filter_split (u + b) fun j => b j ≠ 0]
          omega
    obtain ⟨u'', hu''_cyc, hu''_card, hu''_form⟩ := hsmall
    -- small-cycle theorem: u'' = 0
    have hu''_zero : u'' = 0 := by
      by_contra hne
      have := base_cycle_weight_ge_6 u'' hu''_cyc hne
      omega
    -- either way v is a boundary — contradiction
    have hb_bd : b ∈ bb72Complex.boundaries := ⟨Pi.single g 1, rfl⟩
    have hu_bd : u ∈ bb72Complex.boundaries := by
      rcases hu''_form with hform | hform
      · rw [← hform, hu''_zero]
        exact zero_mem _
      · have hu_eq2 : u = u'' + b := by
          rw [hform]
          funext j
          rw [Pi.add_apply, Pi.add_apply]
          have key : ∀ a c : ZMod 2, a = a + c + c := by decide
          exact key (u j) (b j)
        rw [hu_eq2, hu''_zero, zero_add]
        exact hb_bd
    apply hnb
    have hvt_bd : coverPull1 u ∈ grossComplex.boundaries :=
      coverPull1_mem_boundaries hu_bd
    have hvform : v = coverPull1 u + liftStab (Pi.single g 1) := by
      rw [← hu]
      funext p
      have key : ∀ a c : ZMod 2, a = a + c + c := by decide
      exact key (v p) (liftStab (Pi.single g 1) p)
    rw [hvform]
    exact add_mem hvt_bd (liftStab_mem_boundaries _)

/-! ## The D-pair rung (`m(D-pair) ≥ 1`) -/

/-- The twelve D-pair directions `dA ∪ dB`. -/
def pairDirections : Finset BaseGroup :=
  {(0, 1), (0, 5), (3, 1), (3, 2), (3, 4), (3, 5),
   (1, 0), (1, 3), (2, 3), (4, 3), (5, 0), (5, 3)}

private lemma dpair_weight_check : ∀ d ∈ pairDirections,
    (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
      (if j.2 = 0 then baseA j.1 + baseA (j.1 - d)
        else baseB j.1 + baseB (j.1 - d)) ≠ 0).card = 10 := by
  decide +kernel

/-- D-pairs have weight 10. -/
lemma dpair_weight : ∀ g : BaseGroup, ∀ d ∈ pairDirections,
    (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
      bbBoundary2Fn baseA baseB
        (Pi.single g 1 + Pi.single (g + d) 1) j ≠ 0).card = 10 := by
  intro g d hd
  have hfil : (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
      bbBoundary2Fn baseA baseB (Pi.single g 1 + Pi.single (g + d) 1) j ≠ 0)
      = Finset.univ.filter fun j : BaseGroup × Fin 2 =>
          (if j.2 = 0 then baseA (j.1 - g) + baseA (j.1 - g - d)
            else baseB (j.1 - g) + baseB (j.1 - g - d)) ≠ 0 := by
    apply Finset.filter_congr
    intro j _
    rw [bbBoundary2Fn_add, Pi.add_apply, bbBoundary2Fn_single_pt,
      bbBoundary2Fn_single_pt, sub_add_eq_sub_sub]
    by_cases hj : j.2 = 0
    · rw [if_pos hj, if_pos hj, if_pos hj]
    · rw [if_neg hj, if_neg hj, if_neg hj]
  have htrans : (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
      (if j.2 = 0 then baseA (j.1 - g) + baseA (j.1 - g - d)
        else baseB (j.1 - g) + baseB (j.1 - g - d)) ≠ 0).card
      = (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
          (if j.2 = 0 then baseA j.1 + baseA (j.1 - d)
            else baseB j.1 + baseB (j.1 - d)) ≠ 0).card :=
    card_filter_comp_equiv ((Equiv.subRight g).prodCongr (Equiv.refl (Fin 2)))
      (fun j : BaseGroup × Fin 2 =>
        (if j.2 = 0 then baseA j.1 + baseA (j.1 - d)
          else baseB j.1 + baseB (j.1 - d)) ≠ 0)
  rw [hfil, htrans]
  exact dpair_weight_check d hd

private lemma dpair_union_check : ∀ d ∈ pairDirections,
    (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
      (if j.2 = 0 then baseA j.1 else baseB j.1) ≠ 0 ∨
      (if j.2 = 0 then baseA (j.1 - d) else baseB (j.1 - d)) ≠ 0).card
      ≤ 11 := by
  decide +kernel

/-- The 11-qubit union: the two hexagons of a D-pair overlap. -/
lemma dpair_union_card : ∀ g : BaseGroup, ∀ d ∈ pairDirections,
    (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
      bbBoundary2Fn baseA baseB (Pi.single g 1) j ≠ 0 ∨
      bbBoundary2Fn baseA baseB (Pi.single (g + d) 1) j ≠ 0).card ≤ 11 := by
  intro g d hd
  have hfil : (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
      bbBoundary2Fn baseA baseB (Pi.single g 1) j ≠ 0 ∨
      bbBoundary2Fn baseA baseB (Pi.single (g + d) 1) j ≠ 0)
      = Finset.univ.filter fun j : BaseGroup × Fin 2 =>
          (if j.2 = 0 then baseA (j.1 - g) else baseB (j.1 - g)) ≠ 0 ∨
          (if j.2 = 0 then baseA (j.1 - g - d)
            else baseB (j.1 - g - d)) ≠ 0 := by
    apply Finset.filter_congr
    intro j _
    rw [bbBoundary2Fn_single_pt, bbBoundary2Fn_single_pt, sub_add_eq_sub_sub]
  have htrans : (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
      (if j.2 = 0 then baseA (j.1 - g) else baseB (j.1 - g)) ≠ 0 ∨
      (if j.2 = 0 then baseA (j.1 - g - d)
        else baseB (j.1 - g - d)) ≠ 0).card
      = (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
          (if j.2 = 0 then baseA j.1 else baseB j.1) ≠ 0 ∨
          (if j.2 = 0 then baseA (j.1 - d) else baseB (j.1 - d)) ≠ 0).card :=
    card_filter_comp_equiv ((Equiv.subRight g).prodCongr (Equiv.refl (Fin 2)))
      (fun j : BaseGroup × Fin 2 =>
        (if j.2 = 0 then baseA j.1 else baseB j.1) ≠ 0 ∨
        (if j.2 = 0 then baseA (j.1 - d) else baseB (j.1 - d)) ≠ 0)
  rw [hfil, htrans]
  exact dpair_union_check d hd

/-- The sheet-0 seam part of a lifted D-pair is supported in the union
(analytic: the lifted stabilizer is additive, and a nonzero `ZMod 2` sum has a
nonzero summand, so the hexagon seam lemma applies to each half). -/
lemma dpair_seam_subset : ∀ g : BaseGroup, ∀ d ∈ pairDirections,
    ∀ j : BaseGroup × Fin 2,
    sheet0 (liftStab (Pi.single g 1 + Pi.single (g + d) 1)) j ≠ 0 →
    (bbBoundary2Fn baseA baseB (Pi.single g 1) j ≠ 0 ∨
     bbBoundary2Fn baseA baseB (Pi.single (g + d) 1) j ≠ 0) := by
  intro g d _hd j hne
  have hsplit : liftStab (Pi.single g 1 + Pi.single (g + d) 1)
      = liftStab (Pi.single g 1) + liftStab (Pi.single (g + d) 1) := by
    unfold liftStab
    rw [liftC2_add, bbBoundary2Fn_add]
  rw [hsplit, sheet0_add] at hne
  have hcases : sheet0 (liftStab (Pi.single g 1)) j ≠ 0 ∨
      sheet0 (liftStab (Pi.single (g + d) 1)) j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    rw [Pi.add_apply, hcon.1, hcon.2, add_zero] at hne
    exact hne rfl
  rcases hcases with h | h
  · exact Or.inl (hexagon_seam_subset g j h)
  · exact Or.inr (hexagon_seam_subset (g + d) j h)

/-- **The D-pair rung**: a nontrivial dangerous cycle over a D-pair has weight ≥
12. -/
theorem dangerous_dpair_bound (g d : BaseGroup) (hd : d ∈ pairDirections)
    {v : GrossGroup × Fin 2 → ZMod 2}
    (hv : v ∈ grossComplex.cycles) (hnb : v ∉ grossComplex.boundaries)
    (hb : coverPush1 v
      = bbBoundary2Fn baseA baseB (Pi.single g 1 + Pi.single (g + d) 1)) :
    12 ≤ grossComplex.chainWeight v := by
  classical
  set f : BaseGroup → ZMod 2 := Pi.single g 1 + Pi.single (g + d) 1 with hfdef
  set b₁ : BaseGroup × Fin 2 → ZMod 2 :=
    bbBoundary2Fn baseA baseB (Pi.single g 1) with hb₁def
  set b₂ : BaseGroup × Fin 2 → ZMod 2 :=
    bbBoundary2Fn baseA baseB (Pi.single (g + d) 1) with hb₂def
  have hb12 : bbBoundary2Fn baseA baseB f = b₁ + b₂ := by
    rw [hfdef, bbBoundary2Fn_add]
  by_cases hoff : 1 ≤ (Finset.univ.filter fun j =>
      sheet0 v j ≠ 0 ∧ coverPush1 v j = 0).card
  · -- |v| = 10 + 2·off ≥ 12
    rw [gross_chainWeight_sheet_eq, hb, bb72Complex_chainWeight_eq,
      dpair_weight g d hd]
    rw [hb] at hoff
    omega
  · push Not at hoff
    exfalso
    -- normalize
    have hpush : coverPush1 (v + liftStab f) = 0 := by
      rw [map_add, hb, coverPush1_liftStab]
      funext j
      exact CharTwo.add_self_eq_zero _
    obtain ⟨u, hu⟩ := (coverPush1_eq_zero_iff _).mp hpush
    have hvtilde_cyc : coverPull1 u ∈ grossComplex.cycles := by
      rw [← hu]
      have h1 : bbBoundary1Fn grossA grossB (v + liftStab f) = 0 := by
        have hv0 : bbBoundary1Fn grossA grossB v = 0 := hv
        have hs0 : bbBoundary1Fn grossA grossB (liftStab f) = 0 :=
          bbBoundaryFn_comp grossA grossB (liftC2 f)
        rw [bbBoundary1Fn_add, hv0, hs0, add_zero]
      exact h1
    have hu_cyc : bbBoundary1Fn baseA baseB u = 0 := descend_cycle hvtilde_cyc
    have hu_eq : u = sheet0 v + sheet0 (liftStab f) := by
      have h2 := congrArg sheet0 hu
      rw [sheet0_coverPull1] at h2
      rw [← h2]
      rfl
    -- supp u ⊆ U (the 11-qubit union)
    have hU : ∀ j, u j ≠ 0 → (b₁ j ≠ 0 ∨ b₂ j ≠ 0) := by
      intro j hju
      by_contra hcon
      push Not at hcon
      obtain ⟨h1, h2⟩ := hcon
      -- j is off both hexagons, hence off b and off the seam
      have hbj : coverPush1 v j = 0 := by
        rw [hb, hb12]
        simp only [Pi.add_apply, h1, h2, add_zero]
      have hseam : liftStab f (coverSec1 j) = 0 := by
        by_contra hcon2
        rcases dpair_seam_subset g d hd j hcon2 with h | h
        · exact h h1
        · exact h h2
      have hsheet : sheet0 v j ≠ 0 := by
        rw [hu_eq] at hju
        simpa [Pi.add_apply, hseam] using hju
      have hmem : j ∈ Finset.univ.filter fun j =>
          sheet0 v j ≠ 0 ∧ coverPush1 v j = 0 :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsheet, hbj⟩
      have := Finset.card_pos.mpr ⟨j, hmem⟩
      omega
    -- counting over the four translates
    have hcount : (Finset.univ.filter fun j => u j ≠ 0).card
        + (Finset.univ.filter fun j => (u + b₁) j ≠ 0).card
        + (Finset.univ.filter fun j => (u + b₂) j ≠ 0).card
        + (Finset.univ.filter fun j => (u + b₁ + b₂) j ≠ 0).card ≤ 22 := by
      -- pointwise: at most two of the four translates are supported at any
      -- point, and none off the 11-qubit union
      have hpt : ∀ j : BaseGroup × Fin 2,
          ((if u j ≠ 0 then 1 else 0) : ℕ)
            + (if (u + b₁) j ≠ 0 then 1 else 0)
            + (if (u + b₂) j ≠ 0 then 1 else 0)
            + (if (u + b₁ + b₂) j ≠ 0 then 1 else 0)
          ≤ 2 * (if b₁ j ≠ 0 ∨ b₂ j ≠ 0 then 1 else 0) := by
        intro j
        by_cases hUj : b₁ j ≠ 0 ∨ b₂ j ≠ 0
        · rw [if_pos hUj]
          simp only [Pi.add_apply]
          have key : ∀ a β₁ β₂ : ZMod 2, (β₁ ≠ 0 ∨ β₂ ≠ 0) →
              ((if a ≠ 0 then 1 else 0) : ℕ)
                + (if a + β₁ ≠ 0 then 1 else 0)
                + (if a + β₂ ≠ 0 then 1 else 0)
                + (if a + β₁ + β₂ ≠ 0 then 1 else 0) = 2 := by decide
          rw [key (u j) (b₁ j) (b₂ j) hUj]
        · push Not at hUj
          have hju : u j = 0 := by
            by_contra hju
            rcases hU j hju with h | h
            · exact h hUj.1
            · exact h hUj.2
          simp [Pi.add_apply, hju, hUj.1, hUj.2]
      calc (Finset.univ.filter fun j => u j ≠ 0).card
            + (Finset.univ.filter fun j => (u + b₁) j ≠ 0).card
            + (Finset.univ.filter fun j => (u + b₂) j ≠ 0).card
            + (Finset.univ.filter fun j => (u + b₁ + b₂) j ≠ 0).card
          = ∑ j : BaseGroup × Fin 2,
              (((if u j ≠ 0 then 1 else 0) : ℕ)
                + (if (u + b₁) j ≠ 0 then 1 else 0)
                + (if (u + b₂) j ≠ 0 then 1 else 0)
                + (if (u + b₁ + b₂) j ≠ 0 then 1 else 0)) := by
            simp only [Finset.sum_add_distrib, Finset.card_filter]
        _ ≤ ∑ j : BaseGroup × Fin 2,
              2 * (if b₁ j ≠ 0 ∨ b₂ j ≠ 0 then 1 else 0) :=
            Finset.sum_le_sum fun j _ => hpt j
        _ = 2 * (Finset.univ.filter fun j => b₁ j ≠ 0 ∨ b₂ j ≠ 0).card := by
            rw [← Finset.mul_sum, ← Finset.card_filter]
        _ ≤ 22 := by
            have hcard := dpair_union_card g d hd
            rw [hb₁def, hb₂def]
            omega
    -- one of the four translates is a small cycle
    have hb₁_cyc : bbBoundary1Fn baseA baseB b₁ = 0 :=
      bbBoundaryFn_comp baseA baseB (Pi.single g 1)
    have hb₂_cyc : bbBoundary1Fn baseA baseB b₂ = 0 :=
      bbBoundaryFn_comp baseA baseB (Pi.single (g + d) 1)
    have hsmall : ∃ r : BaseGroup × Fin 2 → ZMod 2,
        bbBoundary1Fn baseA baseB r = 0 ∧
        (Finset.univ.filter fun j => r j ≠ 0).card ≤ 5 ∧
        (u = r ∨ u = r + b₁ ∨ u = r + b₂ ∨ u = r + b₁ + b₂) := by
      have hflip : ∀ a c : ZMod 2, a = a + c + c := by decide
      by_cases h0 : (Finset.univ.filter fun j => u j ≠ 0).card ≤ 5
      · exact ⟨u, hu_cyc, h0, Or.inl rfl⟩
      by_cases h1 : (Finset.univ.filter fun j => (u + b₁) j ≠ 0).card ≤ 5
      · refine ⟨u + b₁, ?_, h1, Or.inr (Or.inl ?_)⟩
        · rw [bbBoundary1Fn_add, hu_cyc, hb₁_cyc, add_zero]
        · funext j
          exact hflip (u j) (b₁ j)
      by_cases h2 : (Finset.univ.filter fun j => (u + b₂) j ≠ 0).card ≤ 5
      · refine ⟨u + b₂, ?_, h2, Or.inr (Or.inr (Or.inl ?_))⟩
        · rw [bbBoundary1Fn_add, hu_cyc, hb₂_cyc, add_zero]
        · funext j
          exact hflip (u j) (b₂ j)
      · refine ⟨u + b₁ + b₂, ?_, by omega, Or.inr (Or.inr (Or.inr ?_))⟩
        · rw [bbBoundary1Fn_add, bbBoundary1Fn_add, hu_cyc, hb₁_cyc, hb₂_cyc,
            add_zero, add_zero]
        · funext j
          simp only [Pi.add_apply]
          have key5 : ∀ a c e : ZMod 2, a = a + c + e + c + e := by decide
          exact key5 (u j) (b₁ j) (b₂ j)
    obtain ⟨r, hr_cyc, hr_card, hr_form⟩ := hsmall
    have hr_zero : r = 0 := by
      by_contra hne
      have := base_cycle_weight_ge_6 r hr_cyc hne
      omega
    -- u is a base boundary in every case
    have hb₁_bd : b₁ ∈ bb72Complex.boundaries := ⟨Pi.single g 1, rfl⟩
    have hb₂_bd : b₂ ∈ bb72Complex.boundaries := ⟨Pi.single (g + d) 1, rfl⟩
    have hu_bd : u ∈ bb72Complex.boundaries := by
      rcases hr_form with rfl | rfl | rfl | rfl
      · rw [hr_zero] at *
        exact zero_mem _
      · rw [hr_zero, zero_add]
        exact hb₁_bd
      · rw [hr_zero, zero_add]
        exact hb₂_bd
      · rw [hr_zero, zero_add]
        exact add_mem hb₁_bd hb₂_bd
    apply hnb
    have hvform : v = coverPull1 u + liftStab f := by
      rw [← hu]
      funext p
      have key : ∀ a c : ZMod 2, a = a + c + c := by decide
      exact key (v p) (liftStab f p)
    rw [hvform]
    exact add_mem (coverPull1_mem_boundaries hu_bd) (liftStab_mem_boundaries f)

/-! ## The classification hypothesis and the assembly -/

/-- **The light-stabilizer classification** (A4 §6.3, Theorem "light
stabilizers"): every nonzero base boundary of weight ≤ 11 is a hexagon or a
D-pair. This is the single remaining analytic input for the dangerous sector;
its paper proof is the CRT-engine analysis of A4 §§6.2–6.3. -/
def LightStabilizerClassification : Prop :=
  ∀ f : BaseGroup → ZMod 2,
    bbBoundary2Fn baseA baseB f ≠ 0 →
    (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
      bbBoundary2Fn baseA baseB f j ≠ 0).card ≤ 11 →
    (∃ g : BaseGroup, bbBoundary2Fn baseA baseB f
        = bbBoundary2Fn baseA baseB (Pi.single g 1)) ∨
    (∃ g : BaseGroup, ∃ d ∈ pairDirections, bbBoundary2Fn baseA baseB f
        = bbBoundary2Fn baseA baseB (Pi.single g 1 + Pi.single (g + d) 1))

/-- **The dangerous sector, conditional only on the classification**: (M) holds,
i.e. `DangerousSectorGe12`. -/
theorem dangerous_sector_of_classification
    (hC : LightStabilizerClassification) : DangerousSectorGe12 := by
  intro v hv hnb hbmem hbne
  obtain ⟨f, hf⟩ := hbmem
  have hf' : bbBoundary2Fn baseA baseB f = coverPush1 v := hf
  by_cases hw : 12 ≤ bb72Complex.chainWeight (coverPush1 v)
  · exact le_trans hw (chainWeight_coverPush_le v)
  · push Not at hw
    have hne : bbBoundary2Fn baseA baseB f ≠ 0 := by
      rw [hf']
      exact hbne
    have hle : (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
        bbBoundary2Fn baseA baseB f j ≠ 0).card ≤ 11 := by
      have heq : (Finset.univ.filter fun j : BaseGroup × Fin 2 =>
          bbBoundary2Fn baseA baseB f j ≠ 0).card
          = bb72Complex.chainWeight (coverPush1 v) := by
        rw [bb72Complex_chainWeight_eq, hf']
      omega
    rcases hC f hne hle with ⟨g, hg⟩ | ⟨g, d, hd, hgd⟩
    · exact dangerous_hexagon_bound g hv hnb (by rw [← hf', hg])
    · exact dangerous_dpair_bound g d hd hv hnb (by rw [← hf', hgd])

end BB
end Homological
end Stabilizer
end Quantum
