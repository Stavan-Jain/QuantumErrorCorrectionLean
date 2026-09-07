import Mathlib.Tactic
import QEC.Stabilizer.Codes.RotatedSurface.DistanceX

/-!
# Rotated-surface-code Z-distance ≥ L

The Z-distance mirror of [RotatedSurfaceCodeNDistanceX](RotatedSurfaceCodeNDistanceX.lean).
Every non-trivial Z-type logical of `rotatedSurfaceStabilizerCode L` has Pauli
weight ≥ L, witnessed exactly by `logicalZ L` (the middle-row Z-string).

## Strategy — column-parity invariant (dual side)

Mirroring the row-parity argument: for a 1-chain `c : VtxIdx L → ZMod 2`, define

  `colParity c x := ∑ y, c (x, y) : ZMod 2`.

Three key facts:

* `colParity (rscZCutMap s) x = 0` for every Z-face 0-chain `s` and column `x`
  (each `zSupport zf` projected to any column has even cardinality).
* `colParity middleRowChain x = 1` for every column `x`.
* `dim (dualCycles / dualBoundaries) = 1` (proved here via the transpose-rank
  bridge to `rsc_rank_boundary2` from Stage 3).

Combining these: for any non-trivial dual cycle `c`, `colParity c x = 1`
for all `x`, so each column contributes ≥ 1 qubit to the support, giving
total weight ≥ L.
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

/-! ## §A — Column parity functional -/

/-- The column-parity functional at column `x`: parity of `c (x, y)` over `y`. -/
def colParity (c : RotatedSurface.VtxIdx L → ZMod 2) (x : Fin L) : ZMod 2 :=
  ∑ y : Fin L, c (x, y)

omit [Fact (Odd L)] [Fact (3 ≤ L)] in
@[simp] lemma colParity_add (c c' : RotatedSurface.VtxIdx L → ZMod 2) (x : Fin L) :
    colParity L (c + c') x = colParity L c x + colParity L c' x := by
  unfold colParity
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intros; simp [Pi.add_apply]

omit [Fact (Odd L)] [Fact (3 ≤ L)] in
@[simp] lemma colParity_zero (x : Fin L) :
    colParity L (0 : RotatedSurface.VtxIdx L → ZMod 2) x = 0 := by
  unfold colParity
  apply Finset.sum_eq_zero
  intros; rfl

/-! ## §B — Column parity of `middleRowChain` is `1` -/

omit [Fact (Odd L)] in
theorem colParity_middleRowChain (x : Fin L) :
    colParity L (middleRowChain L) x = 1 := by
  classical
  unfold colParity
  rw [Finset.sum_eq_single (midIdx L)]
  · unfold middleRowChain
    simp
  · intro y _ hne
    unfold middleRowChain
    rw [if_neg]
    intro hy
    apply hne
    apply Fin.ext
    show y.val = (midIdx L).val
    rw [midIdx_val]
    exact hy
  · intro hcontra; exact absurd (Finset.mem_univ _) hcontra

/-! ## §C — Column parity vanishes on dual boundaries

`dualBoundaries = range rscZCutMap`.  We show that `colParity (rscZCutMap s) x = 0`
for every Z-face chain `s`, by case analysis on each Z-face type.
-/

omit [Fact (Odd L)] [Fact (3 ≤ L)] in
/-- A Finset that is empty or a 2-element set has card 0 in `ZMod 2`. -/
private lemma card_empty_or_pair_zmod2_zero' {α : Type*} [DecidableEq α] (s : Finset α)
    (h : s = ∅ ∨ ∃ a b : α, a ≠ b ∧ s = {a, b}) :
    (s.card : ZMod 2) = 0 := by
  rcases h with hempty | ⟨a, b, hne, heq⟩
  · rw [hempty, Finset.card_empty]; rfl
  · rw [heq, Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
    decide

omit [Fact (Odd L)] in
/-- Per-column intersection of `zSupport zf` with column `x` is either empty
or a 2-element set. -/
private lemma colFilter_zSupport_card_even
    (zf : RotatedSurface.ZFaceIdx L) (x : Fin L) :
    (((Finset.univ : Finset (Fin L)).filter
        (fun y : Fin L => (x, y) ∈ RotatedSurface.zSupport zf)).card : ZMod 2) = 0 := by
  classical
  apply card_empty_or_pair_zmod2_zero'
  cases zf with
  | interior zc =>
    by_cases hxMatch : x.val = zc.val.1.val ∨ x.val = zc.val.1.val + 1
    · right
      refine ⟨RotatedSurface.cornerLo zc.val.2, RotatedSurface.cornerHi zc.val.2, ?_, ?_⟩
      · intro h; have := congrArg Fin.val h
        simp [RotatedSurface.cornerLo, RotatedSurface.cornerHi] at this
      · ext y
        rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        rw [RotatedSurface.mem_zSupport_interior_iff]
        simp only [Finset.mem_univ, true_and]
        constructor
        · rintro ⟨_, hy⟩
          rcases hy with h | h
          · left; exact Fin.ext h
          · right; exact Fin.ext h
        · rintro (rfl | rfl)
          · refine ⟨hxMatch, Or.inl ?_⟩
            simp [RotatedSurface.cornerLo]
          · refine ⟨hxMatch, Or.inr ?_⟩
            simp [RotatedSurface.cornerHi]
    · left
      push Not at hxMatch
      rw [Finset.filter_eq_empty_iff]
      intro y _
      rw [RotatedSurface.mem_zSupport_interior_iff]
      rintro ⟨hx, _⟩
      rcases hx with h | h
      · exact hxMatch.1 h
      · exact hxMatch.2 h
  | leftBdy k =>
    by_cases hx : x.val = 0
    · right
      have h2k1 : 2 * k.val + 1 < L := by
        have := k.isLt; have h3 : 3 ≤ L := Fact.out; omega
      have h2k2 : 2 * k.val + 2 < L := by
        have := k.isLt; have h3 : 3 ≤ L := Fact.out; omega
      refine ⟨⟨2 * k.val + 1, h2k1⟩, ⟨2 * k.val + 2, h2k2⟩, ?_, ?_⟩
      · intro h; have := congrArg Fin.val h
        simp at this
      · ext y
        rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        rw [RotatedSurface.mem_zSupport_leftBdy_iff]
        simp only [Finset.mem_univ, true_and]
        constructor
        · rintro ⟨_, hy⟩
          rcases hy with h | h
          · left; exact Fin.ext h
          · right; exact Fin.ext h
        · rintro (rfl | rfl)
          · exact ⟨hx, Or.inl rfl⟩
          · exact ⟨hx, Or.inr rfl⟩
    · left
      rw [Finset.filter_eq_empty_iff]
      intro y _
      rw [RotatedSurface.mem_zSupport_leftBdy_iff]
      rintro ⟨hxz, _⟩
      exact hx hxz
  | rightBdy k =>
    by_cases hx : x.val = L - 1
    · right
      have h2k : 2 * k.val < L := by
        have := k.isLt; have h3 : 3 ≤ L := Fact.out; omega
      have h2k1 : 2 * k.val + 1 < L := by
        have := k.isLt; have h3 : 3 ≤ L := Fact.out; omega
      refine ⟨⟨2 * k.val, h2k⟩, ⟨2 * k.val + 1, h2k1⟩, ?_, ?_⟩
      · intro h; have := congrArg Fin.val h
        simp at this
      · ext y
        rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        rw [RotatedSurface.mem_zSupport_rightBdy_iff]
        simp only [Finset.mem_univ, true_and]
        constructor
        · rintro ⟨_, hy⟩
          rcases hy with h | h
          · left; exact Fin.ext h
          · right; exact Fin.ext h
        · rintro (rfl | rfl)
          · exact ⟨hx, Or.inl rfl⟩
          · exact ⟨hx, Or.inr rfl⟩
    · left
      rw [Finset.filter_eq_empty_iff]
      intro y _
      rw [RotatedSurface.mem_zSupport_rightBdy_iff]
      rintro ⟨hxL, _⟩
      exact hx hxL

omit [Fact (Odd L)] in
/-- `colParity (rscZCutMap (Pi.single zf 1)) x = 0`. -/
private lemma colParity_zCutMap_single (zf : RotatedSurface.ZFaceIdx L) (x : Fin L) :
    colParity L (δ⁰ L (Pi.single zf 1)) x = 0 := by
  classical
  unfold colParity
  -- (rscZCutMap (Pi.single zf 1)) v = 1[v ∈ zSupport zf]
  rw [show (fun y : Fin L => δ⁰ L (Pi.single zf 1) (x, y)) =
      (fun y : Fin L => if (x, y) ∈ RotatedSurface.zSupport zf then (1 : ZMod 2) else 0) by
    funext y
    rw [RotatedSurface.rscZCutMap_apply]
    rw [Finset.sum_eq_single zf]
    · rw [show (Pi.single zf 1 : RotatedSurface.ZFaceIdx L → ZMod 2) zf = 1 from
        Pi.single_eq_same _ _]
      ring
    · intro zf' _ hne
      have h0 : (Pi.single zf 1 : RotatedSurface.ZFaceIdx L → ZMod 2) zf' = 0 := by
        rw [Pi.single_apply, if_neg hne]
      rw [h0]; ring
    · intro hcontra; exact absurd (Finset.mem_univ zf) hcontra]
  rw [Finset.sum_boole]
  exact colFilter_zSupport_card_even L zf x

omit [Fact (Odd L)] in
/-- `colParity (rscZCutMap s) x = 0` for every Z-face chain `s`. -/
theorem colParity_rscZCutMap
    (s : RotatedSurface.ZFaceIdx L → ZMod 2) (x : Fin L) :
    colParity L (δ⁰ L s) x = 0 := by
  classical
  have hs : s = ∑ zf : RotatedSurface.ZFaceIdx L, s zf • (Pi.single zf (1 : ZMod 2)) := by
    funext zf
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hs]
  rw [map_sum]
  unfold colParity
  rw [show (fun y : Fin L =>
      (∑ zf : RotatedSurface.ZFaceIdx L,
        δ⁰ L (s zf • Pi.single zf 1)) (x, y)) =
      (fun y : Fin L =>
        ∑ zf : RotatedSurface.ZFaceIdx L,
          δ⁰ L (s zf • Pi.single zf 1) (x, y)) by
    funext y; rw [Finset.sum_apply]]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro zf _
  have h_smul : ∀ y : Fin L,
      δ⁰ L (s zf • Pi.single zf 1) (x, y) =
        s zf * δ⁰ L (Pi.single zf 1) (x, y) := fun y => by
    rw [LinearMap.map_smul]
    simp [Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun y _ => h_smul y)]
  rw [← Finset.mul_sum]
  rw [show ∑ y : Fin L, δ⁰ L (Pi.single zf 1) (x, y) =
      colParity L (δ⁰ L (Pi.single zf 1)) x from rfl]
  rw [colParity_zCutMap_single]
  ring

omit [Fact (Odd L)] in
/-- `colParity` vanishes on the dual-boundaries submodule (range of `rscZCutMap`). -/
theorem colParity_eq_zero_of_mem_dualBoundaries
    {c : RotatedSurface.VtxIdx L → ZMod 2}
    (hc : c ∈ LinearMap.range (δ⁰ L)) (x : Fin L) :
    colParity L c x = 0 := by
  rcases hc with ⟨s, rfl⟩
  exact colParity_rscZCutMap L s x

/-! ## §D — `dim (dualCycles / dualBoundaries) = 1`

We need two rank computations:

* `dim dualCycles = L*L − card XFaceIdx`, via rank-nullity on the abstract
  `dualBoundary`, whose rank matches `rank rscBoundary2 = card XFaceIdx`
  (Stage 3) by `Matrix.rank_transpose`.

* `dim dualBoundaries = card ZFaceIdx`, via the bridge
  `cutMap = rscZCutMap` and Stage 3's `rsc_rank_zCutMap`.

The dual chain-complex law `dualBoundary ∘ cutMap = 0` (which gives
`dualBoundaries ≤ dualCycles`) is the transpose of `∂₁ ∘ ∂₂ = 0`.
-/

omit [Fact (Odd L)] [Fact (3 ≤ L)] in
/-- The X-stab incidence matrix: entry `(xf, v)` is `1` iff `v ∈ xSupport xf`. -/
def stabXMatrix : Matrix (RotatedSurface.XFaceIdx L) (RotatedSurface.VtxIdx L) (ZMod 2) :=
  fun xf v => if v ∈ RotatedSurface.xSupport xf then 1 else 0

omit [Fact (Odd L)] [Fact (3 ≤ L)] in
lemma rscBoundary2_eq_transpose_mulVecLin :
    ∂₂ L = (stabXMatrix L).transpose.mulVecLin := by
  apply LinearMap.ext
  intro c
  funext v
  rw [RotatedSurface.rscBoundary2_apply, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
  simp only [stabXMatrix, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro xf _
  ring

lemma dualBoundary_apply_eq_mulVec (c : RotatedSurface.VtxIdx L → ZMod 2)
    (xf : RotatedSurface.XFaceIdx L) :
    (RotatedSurface.rotatedSurfaceHomologicalCode L).dualBoundary c xf =
      (stabXMatrix L).mulVec c xf := by
  rw [dualBoundary_apply_eq_sum]
  -- LHS: ∑ v ∈ xSupport xf, c v
  -- RHS: (stabXMatrix L).mulVec c xf = ∑ v, (stabXMatrix L) xf v * c v
  rw [Matrix.mulVec, dotProduct]
  simp only [stabXMatrix]
  rw [show (fun v : RotatedSurface.VtxIdx L =>
        (if v ∈ RotatedSurface.xSupport xf then (1 : ZMod 2) else 0) * c v) =
      (fun v => if v ∈ RotatedSurface.xSupport xf then c v else 0) from
    funext fun v => by split_ifs <;> simp]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext v; simp

lemma dualBoundary_eq_mulVecLin :
    (RotatedSurface.rotatedSurfaceHomologicalCode L).dualBoundary =
      Matrix.mulVecLin (stabXMatrix L) := by
  apply LinearMap.ext
  intro c
  funext xf
  rw [dualBoundary_apply_eq_mulVec]
  rfl

/-- `rank(dualBoundary) = card (XFaceIdx L)`. -/
theorem rsc_rank_dualBoundary :
    dim₂
        (LinearMap.range (RotatedSurface.rotatedSurfaceHomologicalCode L).dualBoundary) =
      Fintype.card (RotatedSurface.XFaceIdx L) := by
  have h_eq_rank :
      dim₂
          (LinearMap.range (RotatedSurface.rotatedSurfaceHomologicalCode L).dualBoundary) =
        dim₂ (LinearMap.range (∂₂ L)) := by
    rw [dualBoundary_eq_mulVecLin, rscBoundary2_eq_transpose_mulVecLin]
    change Matrix.rank (stabXMatrix L) = Matrix.rank (stabXMatrix L).transpose
    rw [Matrix.rank_transpose]
  rw [h_eq_rank]
  exact RotatedSurface.rsc_rank_boundary2 (L := L)

/-- `dim dualCycles = L*L − card XFaceIdx`. -/
theorem rsc_finrank_dualCycles :
    dim₂
        (RotatedSurface.rotatedSurfaceHomologicalCode L).dualCycles =
      L * L - Fintype.card (RotatedSurface.XFaceIdx L) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker
    (RotatedSurface.rotatedSurfaceHomologicalCode L).dualBoundary
  rw [rsc_rank_dualBoundary] at hrn
  -- dim C₁ = L*L (via Fintype card of VtxIdx).
  have h_C1 : dim₂
      ((RotatedSurface.rotatedSurfaceHomologicalCode L).C1 → ZMod 2) = L * L := by
    rw [Module.finrank_fintype_fun_eq_card]
    change Fintype.card (RotatedSurface.VtxIdx L) = L * L
    simp [Fintype.card_prod, Fintype.card_fin]
  rw [h_C1] at hrn
  change dim₂
    (LinearMap.ker (RotatedSurface.rotatedSurfaceHomologicalCode L).dualBoundary) = _
  omega

omit [Fact (Odd L)] [Fact (3 ≤ L)] in
/-- Helper: `rscBoundary1 (Pi.single v 1) zf = 1[v ∈ zSupport zf]`. -/
private lemma rscBoundary1_pi_single
    (v : RotatedSurface.VtxIdx L) (zf : RotatedSurface.ZFaceIdx L) :
    ∂₁ L (Pi.single v 1) zf =
      (if v ∈ RotatedSurface.zSupport zf then (1 : ZMod 2) else 0) := by
  classical
  rw [RotatedSurface.rscBoundary1_apply]
  by_cases hv : v ∈ RotatedSurface.zSupport zf
  · rw [if_pos hv, Finset.sum_eq_single_of_mem v hv]
    · simp
    · intro u _ hne
      simp [hne]
  · rw [if_neg hv]
    apply Finset.sum_eq_zero
    intro u hu
    have hne : u ≠ v := fun heq => hv (heq ▸ hu)
    simp [hne]

/-- Bridge: the abstract `cutMap` equals the lattice-side `rscZCutMap`. -/
lemma cutMap_eq_rscZCutMap :
    (RotatedSurface.rotatedSurfaceHomologicalCode L).cutMap =
      δ⁰ L := by
  apply LinearMap.ext
  intro s
  funext v
  change ∑ zf : RotatedSurface.ZFaceIdx L,
      s zf * ∂₁ L (Pi.single v 1) zf = _
  change _ = ∑ zf : RotatedSurface.ZFaceIdx L,
      s zf * (if v ∈ RotatedSurface.zSupport zf then (1 : ZMod 2) else 0)
  apply Finset.sum_congr rfl
  intro zf _
  congr 1
  exact rscBoundary1_pi_single L v zf

/-- `dim dualBoundaries = card ZFaceIdx`. -/
theorem rsc_finrank_dualBoundaries :
    dim₂
        (RotatedSurface.rotatedSurfaceHomologicalCode L).dualBoundaries =
      Fintype.card (RotatedSurface.ZFaceIdx L) := by
  change dim₂
    (LinearMap.range (RotatedSurface.rotatedSurfaceHomologicalCode L).cutMap) = _
  rw [cutMap_eq_rscZCutMap]
  exact RotatedSurface.rsc_rank_zCutMap (L := L)

/-- `dualBoundaries ≤ dualCycles` (dual chain-complex law). -/
theorem dualBoundaries_le_dualCycles :
    (RotatedSurface.rotatedSurfaceHomologicalCode L).dualBoundaries ≤
      (RotatedSurface.rotatedSurfaceHomologicalCode L).dualCycles := by
  intro c hc
  rcases hc with ⟨s, rfl⟩
  -- Goal: cutMap s ∈ dualCycles = ker dualBoundary.
  change (RotatedSurface.rotatedSurfaceHomologicalCode L).cutMap s ∈
      LinearMap.ker (RotatedSurface.rotatedSurfaceHomologicalCode L).dualBoundary
  rw [LinearMap.mem_ker]
  funext xf
  rw [Pi.zero_apply]
  -- Use boundary2_dualBoundary_transpose specialized to Pi.single xf 1.
  have h_pair := Quantum.Stabilizer.Homological.HomologicalCode.boundary2_dualBoundary_transpose
    (X := RotatedSurface.rotatedSurfaceHomologicalCode L) (Pi.single xf 1)
    ((RotatedSurface.rotatedSurfaceHomologicalCode L).cutMap s)
  -- h_pair: ∑ e, boundary2 (δ_xf) e * cutMap s e = ∑ p, δ_xf p * dualBoundary (cutMap s) p
  -- RHS: only the xf term survives.
  -- Use: ∑ p, Pi.single xf 1 p * g p = g xf for any g.
  have h_eq : ∀ p : RotatedSurface.XFaceIdx L,
      (Pi.single xf (1 : ZMod 2) : RotatedSurface.XFaceIdx L → ZMod 2) p *
        (RotatedSurface.rotatedSurfaceHomologicalCode L).dualBoundary
          ((RotatedSurface.rotatedSurfaceHomologicalCode L).cutMap s) p =
      (Pi.single xf
          ((RotatedSurface.rotatedSurfaceHomologicalCode L).dualBoundary
            ((RotatedSurface.rotatedSurfaceHomologicalCode L).cutMap s) xf) :
        RotatedSurface.XFaceIdx L → ZMod 2) p := by
    intro p
    by_cases hp : p = xf
    · subst hp
      rw [Pi.single_eq_same, Pi.single_eq_same, _root_.one_mul]
    · rw [Pi.single_apply, if_neg hp, Pi.single_apply, if_neg hp, MulZeroClass.zero_mul]
  have h_RHS : (∑ p : RotatedSurface.XFaceIdx L,
      (Pi.single xf 1 : RotatedSurface.XFaceIdx L → ZMod 2) p *
        (RotatedSurface.rotatedSurfaceHomologicalCode L).dualBoundary
          ((RotatedSurface.rotatedSurfaceHomologicalCode L).cutMap s) p) =
      (RotatedSurface.rotatedSurfaceHomologicalCode L).dualBoundary
        ((RotatedSurface.rotatedSurfaceHomologicalCode L).cutMap s) xf := by
    rw [Finset.sum_congr rfl (fun p _ => h_eq p)]
    exact Fintype.sum_pi_single' xf _
  -- Combine h_pair (transpose pairing) and h_RHS (RHS reduction) into a direct equation.
  have h_eq2 : (∑ e : RotatedSurface.VtxIdx L,
      (RotatedSurface.rotatedSurfaceHomologicalCode L).boundary2 (Pi.single xf 1) e *
        (RotatedSurface.rotatedSurfaceHomologicalCode L).cutMap s e) =
      (RotatedSurface.rotatedSurfaceHomologicalCode L).dualBoundary
        ((RotatedSurface.rotatedSurfaceHomologicalCode L).cutMap s) xf := h_pair.trans h_RHS
  -- The LHS = chainInnerProduct = 0.
  rw [← h_eq2]
  exact Quantum.Stabilizer.Homological.HomologicalCode.chainInnerProduct_boundary2_cutMap_eq_zero
    (X := RotatedSurface.rotatedSurfaceHomologicalCode L) (Pi.single xf 1) s

/-- `dim (dualCycles / dualBoundaries) = 1` for the rotated surface code. -/
theorem rsc_finrank_dualH1_eq_one :
    dim₂
      ((RotatedSurface.rotatedSurfaceHomologicalCode L).dualCycles ⧸
        Submodule.comap
          (RotatedSurface.rotatedSurfaceHomologicalCode L).dualCycles.subtype
          (RotatedSurface.rotatedSurfaceHomologicalCode L).dualBoundaries) = 1 := by
  have h_le := dualBoundaries_le_dualCycles L
  have h_quot := Submodule.finrank_quotient_add_finrank (R := ZMod 2)
    (Submodule.comap (RotatedSurface.rotatedSurfaceHomologicalCode L).dualCycles.subtype
      (RotatedSurface.rotatedSurfaceHomologicalCode L).dualBoundaries)
  have h_comap : dim₂
      (Submodule.comap (RotatedSurface.rotatedSurfaceHomologicalCode L).dualCycles.subtype
        (RotatedSurface.rotatedSurfaceHomologicalCode L).dualBoundaries) =
      dim₂
        (RotatedSurface.rotatedSurfaceHomologicalCode L).dualBoundaries :=
    (Submodule.comapSubtypeEquivOfLe h_le).finrank_eq
  rw [h_comap, rsc_finrank_dualBoundaries, rsc_finrank_dualCycles] at h_quot
  have hcard := RotatedSurface.card_ZFaceIdx_add_card_XFaceIdx (L := L)
  have h3 : 3 ≤ L := Fact.out
  have hLL : 1 ≤ L * L := by nlinarith
  omega

/-! ## §E — `middleRowChain ∉ dualBoundaries` and homology characterization -/

/-- `middleRowChain` is not a dual boundary. -/
theorem middleRowChain_not_mem_dualBoundaries :
    middleRowChain L ∉
      (RotatedSurface.rotatedSurfaceHomologicalCode L).dualBoundaries := by
  intro h
  have h_rsc : middleRowChain L ∈ LinearMap.range (δ⁰ L) := by
    rw [← cutMap_eq_rscZCutMap]
    exact h
  have h1 : colParity L (middleRowChain L)
      ⟨0, by have h3 : 3 ≤ L := Fact.out; omega⟩ = 1 :=
    colParity_middleRowChain L _
  have h0 : colParity L (middleRowChain L)
      ⟨0, by have h3 : 3 ≤ L := Fact.out; omega⟩ = 0 :=
    colParity_eq_zero_of_mem_dualBoundaries L h_rsc _
  rw [h1] at h0
  exact (by decide : (1 : ZMod 2) ≠ 0) h0

/-- The class of `middleRowChain` in `dualCycles / dualBoundaries` is non-zero. -/
private lemma middleRowChain_dual_class_ne_zero :
    (Submodule.Quotient.mk
      (⟨middleRowChain L, by
        -- middleRowChain ∈ dualCycles, proved in Stage 4 as middleRowChain_mem_dualCycles
        exact middleRowChain_mem_dualCycles L⟩ :
        (RotatedSurface.rotatedSurfaceHomologicalCode L).dualCycles) :
      (RotatedSurface.rotatedSurfaceHomologicalCode L).dualCycles ⧸
        Submodule.comap
          (RotatedSurface.rotatedSurfaceHomologicalCode L).dualCycles.subtype
          (RotatedSurface.rotatedSurfaceHomologicalCode L).dualBoundaries) ≠ 0 := by
  intro h
  rw [Submodule.Quotient.mk_eq_zero] at h
  exact middleRowChain_not_mem_dualBoundaries L h

/-- For non-trivial dual cycle `c`, `c - middleRowChain ∈ dualBoundaries`. -/
theorem dualCycle_sub_middleRowChain_mem_dualBoundaries
    {c : RotatedSurface.VtxIdx L → ZMod 2}
    (hc_cycle : c ∈ (RotatedSurface.rotatedSurfaceHomologicalCode L).dualCycles)
    (hc_nontrivial : c ∉ (RotatedSurface.rotatedSurfaceHomologicalCode L).dualBoundaries) :
    c - middleRowChain L ∈ (RotatedSurface.rotatedSurfaceHomologicalCode L).dualBoundaries := by
  have h_dim := rsc_finrank_dualH1_eq_one L
  have h_spans :
      ∀ w : (RotatedSurface.rotatedSurfaceHomologicalCode L).dualCycles ⧸
              Submodule.comap _ (RotatedSurface.rotatedSurfaceHomologicalCode L).dualBoundaries,
        ∃ a : ZMod 2, a • (Submodule.Quotient.mk
          (⟨middleRowChain L, middleRowChain_mem_dualCycles L⟩ :
            (RotatedSurface.rotatedSurfaceHomologicalCode L).dualCycles)) = w :=
    (finrank_eq_one_iff_of_nonzero' _ (middleRowChain_dual_class_ne_zero L)).mp h_dim
  let cCycle : (RotatedSurface.rotatedSurfaceHomologicalCode L).dualCycles := ⟨c, hc_cycle⟩
  obtain ⟨a, ha⟩ := h_spans (Submodule.Quotient.mk cCycle)
  have ha_dichot : a = 0 ∨ a = 1 := by
    rcases Fin.exists_fin_two.mp ⟨a, rfl⟩ with h | h
    · left; exact h
    · right; exact h
  rcases ha_dichot with ha0 | ha1
  · exfalso
    rw [ha0, zero_smul] at ha
    rw [eq_comm, Submodule.Quotient.mk_eq_zero] at ha
    exact hc_nontrivial ha
  · rw [ha1, one_smul] at ha
    have h_eq : (Submodule.Quotient.mk cCycle :
        (RotatedSurface.rotatedSurfaceHomologicalCode L).dualCycles ⧸ _) =
        Submodule.Quotient.mk
          (⟨middleRowChain L, middleRowChain_mem_dualCycles L⟩ :
            (RotatedSurface.rotatedSurfaceHomologicalCode L).dualCycles) := ha.symm
    rw [Submodule.Quotient.eq] at h_eq
    exact h_eq

/-- For non-trivial dual cycle `c`, `colParity c x = 1` for every column `x`. -/
theorem colParity_eq_one_of_nontrivial
    {c : RotatedSurface.VtxIdx L → ZMod 2}
    (hc_cycle : c ∈ (RotatedSurface.rotatedSurfaceHomologicalCode L).dualCycles)
    (hc_nontrivial : c ∉ (RotatedSurface.rotatedSurfaceHomologicalCode L).dualBoundaries)
    (x : Fin L) :
    colParity L c x = 1 := by
  have h_diff_boundary :=
    dualCycle_sub_middleRowChain_mem_dualBoundaries L hc_cycle hc_nontrivial
  have h_eq : c = middleRowChain L + (c - middleRowChain L) := by abel
  rw [h_eq, colParity_add]
  rw [colParity_middleRowChain]
  -- dualBoundaries unfolds to range cutMap; convert h_diff_boundary to range rscZCutMap.
  have h_diff_rsc : c - middleRowChain L ∈
      LinearMap.range (δ⁰ L) := by
    rw [← cutMap_eq_rscZCutMap]
    exact h_diff_boundary
  rw [colParity_eq_zero_of_mem_dualBoundaries L h_diff_rsc x]
  ring

/-! ## §F — Weight ≥ L for non-trivial Z-cycles

The col-parity invariant from §A–E gives a per-column lower bound of 1 on the
dual chain support, hence the abstract `chainWeight` (from
`Stabilizer.Homological.Distance`) is ≥ L for every non-trivial dual cycle. -/

open Quantum.Stabilizer.Homological.HomologicalCode

omit [Fact (Odd L)] [Fact (3 ≤ L)] in
/-- `colParity c x = (#{y : c (x, y) ≠ 0} mod 2)`.

Equivalent to the count of `c (x, y) = 1` for `ZMod 2`-valued `c`, stated in
terms of `≠ 0` so it dovetails with the generic
`HomologicalCode.chainSupport` predicate. -/
private lemma colParity_eq_col_card_cast
    (c : RotatedSurface.VtxIdx L → ZMod 2) (x : Fin L) :
    colParity L c x =
      (((Finset.univ : Finset (Fin L)).filter (fun y => c (x, y) ≠ 0)).card : ZMod 2) := by
  classical
  unfold colParity
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hxy : c (x, y) = 0
  · rw [hxy]; simp
  · have h1 : c (x, y) = 1 := by
      rcases Fin.exists_fin_two.mp ⟨c (x, y), rfl⟩ with h | h
      · exact absurd h hxy
      · exact h
    rw [h1]; simp

/-- The generic chain support card decomposes column by column. -/
private lemma chainSupport_card_eq_sum_col_card
    (c : RotatedSurface.VtxIdx L → ZMod 2) :
    ((RotatedSurface.rotatedSurfaceHomologicalCode L).chainSupport c).card =
      ∑ x : Fin L, ((Finset.univ : Finset (Fin L)).filter (fun y => c (x, y) ≠ 0)).card := by
  classical
  change (Finset.univ.filter (fun v : RotatedSurface.VtxIdx L => c v ≠ 0)).card = _
  rw [Finset.card_filter]
  -- ∑ v : VtxIdx L, if c v ≠ 0 then 1 else 0 — split prod (column-first this time).
  rw [show ∑ v : RotatedSurface.VtxIdx L, (if c v ≠ 0 then (1 : ℕ) else 0) =
      ∑ x : Fin L, ∑ y : Fin L, (if c (x, y) ≠ 0 then (1 : ℕ) else 0)
    from Fintype.sum_prod_type (fun v : RotatedSurface.VtxIdx L =>
      (if c v ≠ 0 then (1 : ℕ) else 0))]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.card_filter]

/-- For non-trivial dual cycle `c`, the abstract `chainWeight` is ≥ L. -/
theorem dual_chainWeight_ge_L_of_nontrivial
    {c : RotatedSurface.VtxIdx L → ZMod 2}
    (hc_cycle : c ∈ (RotatedSurface.rotatedSurfaceHomologicalCode L).dualCycles)
    (hc_nontrivial : c ∉ (RotatedSurface.rotatedSurfaceHomologicalCode L).dualBoundaries) :
    L ≤ (RotatedSurface.rotatedSurfaceHomologicalCode L).chainWeight c := by
  -- chainWeight c = (chainSupport c).card; column decomposition + per-column ≥ 1.
  change L ≤ ((RotatedSurface.rotatedSurfaceHomologicalCode L).chainSupport c).card
  rw [chainSupport_card_eq_sum_col_card]
  have h_each_col : ∀ x : Fin L,
      1 ≤ ((Finset.univ : Finset (Fin L)).filter (fun y => c (x, y) ≠ 0)).card := by
    intro x
    -- colParity c x = 1 (§E, since c is non-trivial)
    have h_cp := colParity_eq_one_of_nontrivial L hc_cycle hc_nontrivial x
    rw [colParity_eq_col_card_cast] at h_cp
    by_contra h_lt
    push Not at h_lt
    interval_cases (((Finset.univ : Finset (Fin L)).filter (fun y => c (x, y) ≠ 0)).card)
    rw [Nat.cast_zero] at h_cp
    exact (by decide : (1 : ZMod 2) ≠ 0) h_cp.symm
  calc L = ∑ _ : Fin L, 1 := by simp
    _ ≤ ∑ x : Fin L,
        ((Finset.univ : Finset (Fin L)).filter (fun y => c (x, y) ≠ 0)).card :=
      Finset.sum_le_sum (fun x _ => h_each_col x)

/-! Z-mirror of the X-side proof in `RotatedSurfaceCodeNDistanceX`:
`weight_ge_chainWeight_zChainOf`, `zChainOf_mem_dualCycles_of_centralizer`, and
`not_both_boundary_of_nontrivial` from the abstract CSS bridge. For a Z-type
`g`, `xChainOf g = 0` (no X- or Y-components), trivially in `boundaries`, so
the bridge forces `zChainOf g ∉ dualBoundaries`. -/

/-- Any non-trivial Z-type logical of the rotated surface stabilizer code has weight ≥ L. -/
theorem weight_ge_L_of_nontrivial_Z_logical
    {g : NQubitPauliGroupElement (numQubits L)}
    (hgZ : NQubitPauliGroupElement.IsZTypeElement g)
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
  -- Generic: `zChainOf g` is a dual 1-cycle.
  have hz_cyc :
      (RotatedSurface.rotatedSurfaceHomologicalCode L).zChainOf g ∈
        (RotatedSurface.rotatedSurfaceHomologicalCode L).dualCycles :=
    zChainOf_mem_dualCycles_of_centralizer
      (X := RotatedSurface.rotatedSurfaceHomologicalCode L) g hg_cent_hom
  -- For Z-type `g`, `xChainOf g = 0` everywhere, hence ∈ boundaries.
  have hx_zero :
      (RotatedSurface.rotatedSurfaceHomologicalCode L).xChainOf g = 0 := by
    funext e
    simp only [Quantum.Stabilizer.Homological.HomologicalCode.xChainOf, Pi.zero_apply]
    rcases hgZ.2 ((RotatedSurface.rotatedSurfaceHomologicalCode L).edgeEquiv e) with hI | hZ
    · simp [hI]
    · simp [hZ]
  have hx_bnd :
      (RotatedSurface.rotatedSurfaceHomologicalCode L).xChainOf g ∈
        (RotatedSurface.rotatedSurfaceHomologicalCode L).boundaries := by
    rw [hx_zero]; exact Submodule.zero_mem _
  -- CSS bridge: ¬ (X-chain ∈ boundaries ∧ Z-chain ∈ dualBoundaries).
  have h_not_both :=
    not_both_boundary_of_nontrivial
      (X := RotatedSurface.rotatedSurfaceHomologicalCode L) g hg_hom
  have hz_not_bnd :
      (RotatedSurface.rotatedSurfaceHomologicalCode L).zChainOf g ∉
        (RotatedSurface.rotatedSurfaceHomologicalCode L).dualBoundaries :=
    fun h => h_not_both ⟨hx_bnd, h⟩
  -- Surface-specific weight bound on the Z-chain + generic weight ≥ chainWeight.
  have h_chain : L ≤
      (RotatedSurface.rotatedSurfaceHomologicalCode L).chainWeight
        ((RotatedSurface.rotatedSurfaceHomologicalCode L).zChainOf g) :=
    dual_chainWeight_ge_L_of_nontrivial L hz_cyc hz_not_bnd
  have h_weight :=
    weight_ge_chainWeight_zChainOf
      (X := RotatedSurface.rotatedSurfaceHomologicalCode L) g
  exact h_chain.trans h_weight

/-- The logical Z has weight exactly `L`. -/
theorem logicalZ_weight_eq_L :
    NQubitPauliGroupElement.weight (logicalZ L) = L := by
  -- `logicalZ L = chainZOperator (middleRowChain L)`; reduce weight to chainWeight.
  change NQubitPauliGroupElement.weight
    ((RotatedSurface.rotatedSurfaceHomologicalCode L).chainZOperator (middleRowChain L)) = L
  rw [weight_chainZOperator]
  -- Direct count: chainSupport (middleRowChain L) ≃ Fin L via x ↦ (x, midIdx L).
  change (Finset.univ.filter (fun v : RotatedSurface.VtxIdx L =>
      middleRowChain L v ≠ 0)).card = L
  rw [show (Finset.univ.filter (fun v : RotatedSurface.VtxIdx L =>
      middleRowChain L v ≠ 0)) =
      (Finset.univ : Finset (Fin L)).image (fun x : Fin L => (x, midIdx L)) by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    rcases v with ⟨vx, vy⟩
    constructor
    · intro hv
      unfold middleRowChain at hv
      simp at hv
      refine ⟨vx, ?_⟩
      apply Prod.mk_inj.mpr
      refine ⟨rfl, ?_⟩
      apply Fin.ext
      rw [midIdx_val]
      exact hv.symm
    · rintro ⟨x, hxy⟩
      have := Prod.mk_inj.mp hxy
      obtain ⟨h1, h2⟩ := this
      unfold middleRowChain
      rw [← h1, ← h2, midIdx_val]
      simp]
  rw [Finset.card_image_of_injective _ (by
    intros x1 x2 hx
    have := Prod.mk_inj.mp hx
    exact this.1)]
  simp

end RotatedSurfaceCodeN
end StabilizerGroup
end Quantum
