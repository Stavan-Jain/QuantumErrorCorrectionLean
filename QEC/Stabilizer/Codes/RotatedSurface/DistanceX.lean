import Mathlib.Tactic
import QEC.Stabilizer.Codes.RotatedSurface.StabilizerCode

/-!
# Rotated-surface-code X-distance — Stage 5 foundations

For the parametric rotated surface code (L odd, L ≥ 3), the eventual goal
is to prove that every non-trivial X-type logical has weight ≥ L (lower
bound), witnessed exactly by the middle-column X-string `logicalX L`.

This file currently establishes the **row-parity invariant** infrastructure:
the `rowParity` linear functional, its key value on `middleColChain` (= 1
for every row), and the linearity properties that anchor the eventual
proof that `rowParity` vanishes on boundaries and is constant in `y` on
cycles.

The full lower bound `weight g ≥ L` for non-trivial X-logicals, plus the
witness packaging `HasCodeDistance`, will follow from:

* `rowParity (∂₂ f) y = 0` for every X-face 2-chain `f` and row `y`
  (each `xSupport xf` projected to any row has even cardinality —
   proven by direct case analysis on the three face types).
* `rowParity c y` is constant in `y` on cycles `c` (summing the relevant
  interior + boundary Z-face constraints between adjacent rows).
* `dim H₁ = 1` (Stage 3) ⟹ any non-trivial cycle is homologous to
  `middleColChain`, so `rowParity c y = 1` for all `y`.
* Each row contributes ≥ 1 qubit to the support of `c`, giving weight ≥ L.

These remaining steps require substantial Finset bookkeeping over the
six cases (interior × Z-face, top/bottom-bdy × Z-face) and are deferred
to follow-up commits.
-/

namespace Quantum
namespace StabilizerGroup
namespace RotatedSurfaceCodeN

open scoped BigOperators
open scoped Homology
open scoped RotatedSurfaceChain
open NQubitPauliGroupElement
open Stabilizer.Lattice

variable (L : ℕ) [Fact (Odd L)] [Fact (3 ≤ L)]

/-! ## §A — Row parity functional -/

/-- The row-parity functional at row `y`: parity of `c (x, y)` over `x`. -/
def rowParity (c : RotatedSurface.VtxIdx L → ZMod 2) (y : Fin L) : ZMod 2 :=
  ∑ x : Fin L, c (x, y)

omit [Fact (Odd L)] [Fact (3 ≤ L)] in
@[simp] lemma rowParity_add (c c' : RotatedSurface.VtxIdx L → ZMod 2) (y : Fin L) :
    rowParity L (c + c') y = rowParity L c y + rowParity L c' y := by
  unfold rowParity
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intros; simp [Pi.add_apply]

omit [Fact (Odd L)] [Fact (3 ≤ L)] in
@[simp] lemma rowParity_zero (y : Fin L) :
    rowParity L (0 : RotatedSurface.VtxIdx L → ZMod 2) y = 0 := by
  unfold rowParity
  apply Finset.sum_eq_zero
  intros; rfl

omit [Fact (Odd L)] [Fact (3 ≤ L)] in
lemma rowParity_smul (a : ZMod 2) (c : RotatedSurface.VtxIdx L → ZMod 2)
    (y : Fin L) :
    rowParity L (a • c) y = a * rowParity L c y := by
  unfold rowParity
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros; simp [Pi.smul_apply, smul_eq_mul]

/-! ## §B — Row parity of `middleColChain` is `1`

The middle column intersects each row in exactly one qubit (at `x = mid`),
so the row parity is `1` for every row.  This is the non-zero side of the
eventual `H₁ → ZMod 2` functional.
-/

omit [Fact (Odd L)] in
theorem rowParity_middleColChain (y : Fin L) :
    rowParity L (middleColChain L) y = 1 := by
  classical
  unfold rowParity
  -- ∑ x, middleColChain (x, y) = if x = mid then 1 else 0 summed → 1.
  rw [Finset.sum_eq_single (midIdx L)]
  · unfold middleColChain
    simp
  · intro x _ hne
    unfold middleColChain
    rw [if_neg]
    intro hx
    apply hne
    apply Fin.ext
    show x.val = (midIdx L).val
    rw [midIdx_val]
    exact hx
  · intro hcontra; exact absurd (Finset.mem_univ _) hcontra

/-! ## §C — Row parity vanishes on boundaries -/

omit [Fact (Odd L)] [Fact (3 ≤ L)] in
/-- A Finset that is empty or a 2-element set has card 0 in `ZMod 2`. -/
private lemma card_empty_or_pair_zmod2_zero {α : Type*} [DecidableEq α] (s : Finset α)
    (h : s = ∅ ∨ ∃ a b : α, a ≠ b ∧ s = {a, b}) :
    (s.card : ZMod 2) = 0 := by
  rcases h with hempty | ⟨a, b, hne, heq⟩
  · rw [hempty, Finset.card_empty]; rfl
  · rw [heq, Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
    decide

omit [Fact (Odd L)] in
/-- Per-row intersection of `xSupport xf` with row `y` is either empty or a
2-element set, hence its card cast to `ZMod 2` is `0`. -/
private lemma rowFilter_xSupport_card_even
    (xf : RotatedSurface.XFaceIdx L) (y : Fin L) :
    (((Finset.univ : Finset (Fin L)).filter
        (fun x : Fin L => (x, y) ∈ RotatedSurface.xSupport xf)).card : ZMod 2) = 0 := by
  classical
  apply card_empty_or_pair_zmod2_zero
  cases xf with
  | interior xc =>
    by_cases hyMatch : y.val = xc.val.2.val ∨ y.val = xc.val.2.val + 1
    · right
      refine ⟨RotatedSurface.cornerLo xc.val.1, RotatedSurface.cornerHi xc.val.1, ?_, ?_⟩
      · intro h; have := congrArg Fin.val h
        simp [RotatedSurface.cornerLo, RotatedSurface.cornerHi] at this
      · ext x
        rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        rw [RotatedSurface.mem_xSupport_interior_iff]
        simp only [Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hx, _⟩
          rcases hx with h1 | h1
          · left; exact Fin.ext h1
          · right; exact Fin.ext h1
        · rintro (rfl | rfl)
          · refine ⟨Or.inl ?_, hyMatch⟩
            simp [RotatedSurface.cornerLo]
          · refine ⟨Or.inr ?_, hyMatch⟩
            simp [RotatedSurface.cornerHi]
    · left
      push Not at hyMatch
      rw [Finset.filter_eq_empty_iff]
      intro x _
      rw [RotatedSurface.mem_xSupport_interior_iff]
      rintro ⟨_, hy⟩
      rcases hy with h | h
      · exact hyMatch.1 h
      · exact hyMatch.2 h
  | topBdy k =>
    by_cases hy : y.val = 0
    · right
      have h2k : 2 * k.val < L := by
        have := k.isLt; have h3 : 3 ≤ L := Fact.out; omega
      have h2k1 : 2 * k.val + 1 < L := by
        have := k.isLt; have h3 : 3 ≤ L := Fact.out; omega
      refine ⟨⟨2 * k.val, h2k⟩, ⟨2 * k.val + 1, h2k1⟩, ?_, ?_⟩
      · intro h; have := congrArg Fin.val h
        simp at this
      · ext x
        rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        rw [RotatedSurface.mem_xSupport_topBdy_iff]
        simp only [Finset.mem_univ, true_and]
        constructor
        · rintro ⟨_, hx⟩
          rcases hx with h | h
          · left; exact Fin.ext h
          · right; exact Fin.ext h
        · rintro (rfl | rfl)
          · exact ⟨hy, Or.inl rfl⟩
          · exact ⟨hy, Or.inr rfl⟩
    · left
      rw [Finset.filter_eq_empty_iff]
      intro x _
      rw [RotatedSurface.mem_xSupport_topBdy_iff]
      rintro ⟨hyz, _⟩
      exact hy hyz
  | bottomBdy k =>
    by_cases hy : y.val = L - 1
    · right
      have h2k1 : 2 * k.val + 1 < L := by
        have := k.isLt; have h3 : 3 ≤ L := Fact.out; omega
      have h2k2 : 2 * k.val + 2 < L := by
        have := k.isLt; have h3 : 3 ≤ L := Fact.out; omega
      refine ⟨⟨2 * k.val + 1, h2k1⟩, ⟨2 * k.val + 2, h2k2⟩, ?_, ?_⟩
      · intro h; have := congrArg Fin.val h
        simp at this
      · ext x
        rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        rw [RotatedSurface.mem_xSupport_bottomBdy_iff]
        simp only [Finset.mem_univ, true_and]
        constructor
        · rintro ⟨_, hx⟩
          rcases hx with h | h
          · left; exact Fin.ext h
          · right; exact Fin.ext h
        · rintro (rfl | rfl)
          · exact ⟨hy, Or.inl rfl⟩
          · exact ⟨hy, Or.inr rfl⟩
    · left
      rw [Finset.filter_eq_empty_iff]
      intro x _
      rw [RotatedSurface.mem_xSupport_bottomBdy_iff]
      rintro ⟨hyL, _⟩
      exact hy hyL

/-- `rowParity (rscBoundary2 (Pi.single xf 1)) y = 0`. -/
private lemma rowParity_boundary2_single (xf : RotatedSurface.XFaceIdx L) (y : Fin L) :
    rowParity L (∂₂ L (Pi.single xf 1)) y = 0 := by
  classical
  unfold rowParity
  rw [show (fun x : Fin L => ∂₂ L (Pi.single xf 1) (x, y)) =
      (fun x : Fin L => if (x, y) ∈ RotatedSurface.xSupport xf then (1 : ZMod 2) else 0) by
    funext x
    exact boundary2_singleFace_apply L xf (x, y)]
  rw [Finset.sum_boole]
  exact rowFilter_xSupport_card_even L xf y

/-- `rowParity (rscBoundary2 f) y = 0` for every X-face chain `f`. -/
theorem rowParity_rscBoundary2
    (f : RotatedSurface.XFaceIdx L → ZMod 2) (y : Fin L) :
    rowParity L (∂₂ L f) y = 0 := by
  classical
  have hf : f = ∑ xf : RotatedSurface.XFaceIdx L, f xf • (Pi.single xf (1 : ZMod 2)) := by
    funext xf
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hf]
  rw [map_sum]
  unfold rowParity
  -- ∑ x, (∑ xf, ∂₂(f xf • δ_xf))(x, y) = ∑ xf, f xf * (∑ x, ∂₂(δ_xf)(x, y)) = 0
  rw [show (fun x : Fin L =>
      (∑ xf : RotatedSurface.XFaceIdx L,
        ∂₂ L (f xf • Pi.single xf 1)) (x, y)) =
      (fun x : Fin L =>
        ∑ xf : RotatedSurface.XFaceIdx L,
          ∂₂ L (f xf • Pi.single xf 1) (x, y)) by
    funext x; rw [Finset.sum_apply]]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro xf _
  have h_smul : ∀ x : Fin L,
      ∂₂ L (f xf • Pi.single xf 1) (x, y) =
        f xf * ∂₂ L (Pi.single xf 1) (x, y) := fun x => by
    rw [LinearMap.map_smul]
    simp [Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun x _ => h_smul x)]
  rw [← Finset.mul_sum]
  rw [show ∑ x : Fin L, ∂₂ L (Pi.single xf 1) (x, y) =
      rowParity L (∂₂ L (Pi.single xf 1)) y from rfl]
  rw [rowParity_boundary2_single]
  ring

/-- `rowParity` vanishes on the boundary submodule. -/
theorem rowParity_eq_zero_of_mem_boundaries
    {c : RotatedSurface.VtxIdx L → ZMod 2}
    (hc : c ∈ B₁ L) (y : Fin L) :
    rowParity L c y = 0 := by
  rcases hc with ⟨f, rfl⟩
  exact rowParity_rscBoundary2 L f y

/-! ## §D — `middleColChain ∉ boundaries` and homology characterization

Since `rowParity middleColChain y = 1` (§B) but `rowParity (boundary) y = 0` (§C),
`middleColChain` cannot be a boundary.  Combined with `dim H₁ = 1` (Stage 3),
this means every non-trivial cycle is congruent to `middleColChain` modulo
the boundary submodule.
-/

/-- `middleColChain` is not a boundary. -/
theorem middleColChain_not_mem_boundaries :
    middleColChain L ∉ B₁ L := by
  intro h
  -- rowParity middleColChain 0 = 1 (§B) ≠ 0 (= rowParity of boundary, §C)
  have h1 : rowParity L (middleColChain L) ⟨0, by have h3 : 3 ≤ L := Fact.out; omega⟩ = 1 :=
    rowParity_middleColChain L _
  have h0 : rowParity L (middleColChain L) ⟨0, by have h3 : 3 ≤ L := Fact.out; omega⟩ = 0 :=
    rowParity_eq_zero_of_mem_boundaries L h _
  rw [h1] at h0
  exact (by decide : (1 : ZMod 2) ≠ 0) h0

/-- The class of `middleColChain` in `H₁ L` is non-zero. -/
private lemma middleColChain_class_ne_zero :
    (Submodule.Quotient.mk
      (⟨middleColChain L, middleColChain_mem_cycles L⟩ :
        Z₁ L) :
      H₁ L) ≠ 0 := by
  intro h
  -- Submodule.Quotient.mk x = 0 ↔ x ∈ S.  Here S is the comap into cycles.
  rw [Submodule.Quotient.mk_eq_zero] at h
  -- h : ⟨middleColChain, _⟩ ∈ Submodule.comap (cycles.subtype) boundaries
  -- which unfolds to: middleColChain ∈ boundaries
  exact middleColChain_not_mem_boundaries L h

/-- Every cycle is `0` or `middleColChain` modulo boundaries (since `dim H₁ = 1`). -/
theorem cycle_sub_middleColChain_mem_boundaries
    {c : RotatedSurface.VtxIdx L → ZMod 2}
    (hc_cycle : c ∈ Z₁ L)
    (hc_nontrivial : c ∉ B₁ L) :
    c - middleColChain L ∈ B₁ L := by
  have h_dim : dim₂ (H₁ L) = 1 :=
    RotatedSurface.rsc_finrank_H1_eq_one (L := L)
  -- By dim = 1: every element is a scalar multiple of [middleColChain].
  have h_spans :
      ∀ w : H₁ L,
        ∃ a : ZMod 2, a • (Submodule.Quotient.mk
          (⟨middleColChain L, middleColChain_mem_cycles L⟩ :
            Z₁ L)) = w :=
    (finrank_eq_one_iff_of_nonzero' _ (middleColChain_class_ne_zero L)).mp h_dim
  -- Apply to [c].
  let cCycle : Z₁ L := ⟨c, hc_cycle⟩
  obtain ⟨a, ha⟩ := h_spans (Submodule.Quotient.mk cCycle)
  -- a is 0 or 1 in ZMod 2.
  have ha_dichot : a = 0 ∨ a = 1 := by
    rcases Fin.exists_fin_two.mp ⟨a, rfl⟩ with h | h
    · left; exact h
    · right; exact h
  rcases ha_dichot with ha0 | ha1
  · -- a = 0: 0 • [middleColChain] = 0 = [c], so c ∈ boundaries.  Contradiction.
    exfalso
    rw [ha0, zero_smul] at ha
    rw [eq_comm, Submodule.Quotient.mk_eq_zero] at ha
    -- ha : cCycle ∈ Submodule.comap _ boundaries; unfolds to c ∈ boundaries
    exact hc_nontrivial ha
  · -- a = 1: [middleColChain] = [c], so c - middleColChain ∈ boundaries.
    rw [ha1, one_smul] at ha
    have h_eq : (Submodule.Quotient.mk cCycle : H₁ L) =
        Submodule.Quotient.mk
          (⟨middleColChain L, middleColChain_mem_cycles L⟩ :
            Z₁ L) := ha.symm
    rw [Submodule.Quotient.eq] at h_eq
    -- h_eq : cCycle - ⟨middleColChain, _⟩ ∈ Submodule.comap _ boundaries
    -- which unfolds to: c - middleColChain ∈ boundaries
    exact h_eq

/-- For any non-trivial cycle `c`, `rowParity c y = 1` for every row `y`. -/
theorem rowParity_eq_one_of_nontrivial
    {c : RotatedSurface.VtxIdx L → ZMod 2}
    (hc_cycle : c ∈ Z₁ L)
    (hc_nontrivial : c ∉ B₁ L) (y : Fin L) :
    rowParity L c y = 1 := by
  -- c = middleColChain + (c - middleColChain); the second is a boundary.
  have h_diff_boundary :=
    cycle_sub_middleColChain_mem_boundaries L hc_cycle hc_nontrivial
  have h_eq : c = middleColChain L + (c - middleColChain L) := by abel
  rw [h_eq, rowParity_add]
  rw [rowParity_middleColChain]
  rw [rowParity_eq_zero_of_mem_boundaries L h_diff_boundary y]
  ring

/-! ## §E — Weight ≥ L for non-trivial X-cycles

The row-parity invariant from §A–D gives a per-row lower bound of 1 on the
chain support, hence the abstract `chainWeight` (from
`Stabilizer.Homological.Distance`) is ≥ L for every non-trivial cycle. -/

open Quantum.Stabilizer.Homological.HomologicalCode

omit [Fact (Odd L)] [Fact (3 ≤ L)] in
/-- `rowParity c y = (#{x : c (x, y) ≠ 0} mod 2)`.

Equivalent to the count of `c (x, y) = 1` for `ZMod 2`-valued `c`, stated in
terms of `≠ 0` so it dovetails with the generic
`HomologicalCode.chainSupport` predicate. -/
private lemma rowParity_eq_row_card_cast
    (c : RotatedSurface.VtxIdx L → ZMod 2) (y : Fin L) :
    rowParity L c y =
      (((Finset.univ : Finset (Fin L)).filter (fun x => c (x, y) ≠ 0)).card : ZMod 2) := by
  classical
  unfold rowParity
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hxy : c (x, y) = 0
  · rw [hxy]; simp
  · have h1 : c (x, y) = 1 := by
      rcases Fin.exists_fin_two.mp ⟨c (x, y), rfl⟩ with h | h
      · exact absurd h hxy
      · exact h
    rw [h1]; simp

/-- The generic chain support card decomposes row by row. -/
private lemma chainSupport_card_eq_sum_row_card
    (c : RotatedSurface.VtxIdx L → ZMod 2) :
    ((RotatedSurface.rotatedSurfaceHomologicalCode L).chainSupport c).card =
      ∑ y : Fin L, ((Finset.univ : Finset (Fin L)).filter (fun x => c (x, y) ≠ 0)).card := by
  classical
  change (Finset.univ.filter (fun v : RotatedSurface.VtxIdx L => c v ≠ 0)).card = _
  rw [Finset.card_filter]
  -- ∑ v : VtxIdx L, if c v ≠ 0 then 1 else 0 — split prod and swap.
  rw [show ∑ v : RotatedSurface.VtxIdx L, (if c v ≠ 0 then (1 : ℕ) else 0) =
      ∑ x : Fin L, ∑ y : Fin L, (if c (x, y) ≠ 0 then (1 : ℕ) else 0)
    from Fintype.sum_prod_type (fun v : RotatedSurface.VtxIdx L =>
      (if c v ≠ 0 then (1 : ℕ) else 0))]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.card_filter]

/-- For any non-trivial X-cycle `c`, the abstract `chainWeight` is ≥ L. -/
theorem chainWeight_ge_L_of_nontrivial
    {c : RotatedSurface.VtxIdx L → ZMod 2}
    (hc_cycle : c ∈ Z₁ L)
    (hc_nontrivial : c ∉ B₁ L) :
    L ≤ (RotatedSurface.rotatedSurfaceHomologicalCode L).chainWeight c := by
  -- chainWeight c = (chainSupport c).card; the row decomposition + per-row ≥ 1.
  change L ≤ ((RotatedSurface.rotatedSurfaceHomologicalCode L).chainSupport c).card
  rw [chainSupport_card_eq_sum_row_card]
  have h_each_row : ∀ y : Fin L,
      1 ≤ ((Finset.univ : Finset (Fin L)).filter (fun x => c (x, y) ≠ 0)).card := by
    intro y
    -- rowParity c y = 1 (§D, since c is non-trivial)
    have h_rp := rowParity_eq_one_of_nontrivial L hc_cycle hc_nontrivial y
    rw [rowParity_eq_row_card_cast] at h_rp
    -- Hence the row-filter card is odd, so ≥ 1.
    by_contra h_lt
    push Not at h_lt
    interval_cases (((Finset.univ : Finset (Fin L)).filter (fun x => c (x, y) ≠ 0)).card)
    rw [Nat.cast_zero] at h_rp
    exact (by decide : (1 : ZMod 2) ≠ 0) h_rp.symm
  calc L = ∑ _ : Fin L, 1 := by simp
    _ ≤ ∑ y : Fin L,
        ((Finset.univ : Finset (Fin L)).filter (fun x => c (x, y) ≠ 0)).card :=
      Finset.sum_le_sum (fun y _ => h_each_row y)

/-! ## §F — X-type logical operators have weight ≥ L

The abstract CSS bridge in `Stabilizer.Homological.Distance` provides
`weight_ge_chainWeight_xChainOf`, `xChainOf_mem_cycles_of_centralizer`, and
`not_both_boundary_of_nontrivial`. For an X-type `g`, `zChainOf g = 0`
(no Z- or Y-components), which is trivially in `dualBoundaries`, so the
bridge forces `xChainOf g ∉ boundaries`. Combine with the surface-specific
`chainWeight_ge_L_of_nontrivial` and the weight ≥ chainWeight bridge. -/

/-- Any non-trivial X-type logical of the rotated surface stabilizer code has weight ≥ L. -/
theorem weight_ge_L_of_nontrivial_X_logical
    {g : NQubitPauliGroupElement (numQubits L)}
    (hgX : NQubitPauliGroupElement.IsXTypeElement g)
    (hgLogical : Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
      (rotatedSurfaceStabilizerCode L).toStabilizerGroup) :
    L ≤ NQubitPauliGroupElement.weight g := by
  -- Translate the non-trivial-logical predicate to the homological group.
  have h_subg_eq := rotatedSurfaceStabilizerCode_subgroup_eq_homological L
  have hg_hom : Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
      (RotatedSurface.rotatedSurfaceHomologicalCode L).homologicalStabilizerGroup :=
    (Quantum.StabilizerGroup.IsNontrivialLogicalOperator_of_toSubgroup_eq g
      h_subg_eq).mp hgLogical
  have hg_cent_hom : g ∈ Quantum.StabilizerGroup.centralizer
      (RotatedSurface.rotatedSurfaceHomologicalCode L).homologicalStabilizerGroup :=
    ((Quantum.StabilizerGroup.IsNontrivialLogicalOperator_iff g _).mp hg_hom).1
  -- Generic: `xChainOf g` is a 1-cycle.
  have hx_cyc :
      (RotatedSurface.rotatedSurfaceHomologicalCode L).xChainOf g ∈
        (RotatedSurface.rotatedSurfaceHomologicalCode L).cycles :=
    xChainOf_mem_cycles_of_centralizer
      (X := RotatedSurface.rotatedSurfaceHomologicalCode L) g hg_cent_hom
  -- For X-type `g`, `zChainOf g = 0` everywhere, hence ∈ dualBoundaries.
  have hz_zero :
      (RotatedSurface.rotatedSurfaceHomologicalCode L).zChainOf g = 0 := by
    funext e
    simp only [Quantum.Stabilizer.Homological.HomologicalCode.zChainOf, Pi.zero_apply]
    rcases hgX.2 ((RotatedSurface.rotatedSurfaceHomologicalCode L).edgeEquiv e) with hI | hX
    · simp [hI]
    · simp [hX]
  have hz_bnd :
      (RotatedSurface.rotatedSurfaceHomologicalCode L).zChainOf g ∈
        (RotatedSurface.rotatedSurfaceHomologicalCode L).dualBoundaries := by
    rw [hz_zero]; exact Submodule.zero_mem _
  -- CSS bridge: ¬ (X-chain ∈ boundaries ∧ Z-chain ∈ dualBoundaries).
  have h_not_both :=
    not_both_boundary_of_nontrivial
      (X := RotatedSurface.rotatedSurfaceHomologicalCode L) g hg_hom
  have hx_not_bnd :
      (RotatedSurface.rotatedSurfaceHomologicalCode L).xChainOf g ∉
        (RotatedSurface.rotatedSurfaceHomologicalCode L).boundaries :=
    fun h => h_not_both ⟨h, hz_bnd⟩
  -- Surface-specific weight bound on the X-chain + generic weight ≥ chainWeight.
  have h_chain : L ≤
      (RotatedSurface.rotatedSurfaceHomologicalCode L).chainWeight
        ((RotatedSurface.rotatedSurfaceHomologicalCode L).xChainOf g) :=
    chainWeight_ge_L_of_nontrivial L hx_cyc hx_not_bnd
  have h_weight :=
    weight_ge_chainWeight_xChainOf
      (X := RotatedSurface.rotatedSurfaceHomologicalCode L) g
  exact h_chain.trans h_weight

/-- The logical X has weight exactly `L`. -/
theorem logicalX_weight_eq_L :
    NQubitPauliGroupElement.weight (logicalX L) = L := by
  -- `logicalX L = chainXOperator (middleColChain L)`; reduce weight to chainWeight.
  change NQubitPauliGroupElement.weight
    ((RotatedSurface.rotatedSurfaceHomologicalCode L).chainXOperator (middleColChain L)) = L
  rw [weight_chainXOperator]
  -- Direct count: chainSupport (middleColChain L) ≃ Fin L via y ↦ (midIdx L, y).
  change (Finset.univ.filter (fun v : RotatedSurface.VtxIdx L =>
      middleColChain L v ≠ 0)).card = L
  rw [show (Finset.univ.filter (fun v : RotatedSurface.VtxIdx L =>
      middleColChain L v ≠ 0)) =
      (Finset.univ : Finset (Fin L)).image (fun y : Fin L => (midIdx L, y)) by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    rcases v with ⟨vx, vy⟩
    constructor
    · intro hv
      unfold middleColChain at hv
      simp at hv
      refine ⟨vy, ?_⟩
      apply Prod.mk_inj.mpr
      refine ⟨?_, rfl⟩
      apply Fin.ext
      rw [midIdx_val]
      exact hv.symm
    · rintro ⟨y, hxy⟩
      have := Prod.mk_inj.mp hxy
      obtain ⟨h1, h2⟩ := this
      unfold middleColChain
      rw [← h1, ← h2, midIdx_val]
      simp]
  rw [Finset.card_image_of_injective _ (by
    intros y1 y2 hy
    have := Prod.mk_inj.mp hy
    exact this.2)]
  simp

end RotatedSurfaceCodeN
end StabilizerGroup
end Quantum
