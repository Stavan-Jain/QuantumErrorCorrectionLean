import Mathlib.Tactic
import QEC.Stabilizer.Codes.RotatedSurface.CellComplex

/-!
# Rotated-surface-code boundary maps

The boundary maps `∂₂ : C₂ → C₁` and `∂₁ : C₁ → C₀` for the rotated surface
code, plus the chain-complex law `∂₁ ∘ ∂₂ = 0`.

The chain-complex law unwinds to: for every `(zf, xf)` pair, the cardinality
`|zSupport zf ∩ xSupport xf|` is even. Since all supports have size `2` or `4`
and the colours alternate, each intersection is either empty or shares a single
2-qubit edge. We prove this case-by-case (3 × 3 = 9 cases) via `Nat`-level
membership characterisations and `omega`.
-/

namespace Quantum
namespace Stabilizer
namespace Lattice
namespace RotatedSurface

open scoped BigOperators

/-! ## Membership characterisations (ℕ-coordinate level) -/

lemma mem_faceQubits_iff {L : ℕ} (c : FaceCornerIdx L) (v : VtxIdx L) :
    v ∈ faceQubits c ↔
      (v.1.val = c.1.val ∨ v.1.val = c.1.val + 1) ∧
      (v.2.val = c.2.val ∨ v.2.val = c.2.val + 1) := by
  obtain ⟨v1, v2⟩ := v
  simp_all [faceQubits, cornerLo, cornerHi, Finset.mem_insert,
    Finset.mem_singleton, Fin.ext_iff]
  tauto

lemma mem_zSupport_interior_iff {L : ℕ}
    (c : ZInteriorCornerIdx L) (v : VtxIdx L) :
    v ∈ zSupport (.interior c) ↔
      (v.1.val = c.val.1.val ∨ v.1.val = c.val.1.val + 1) ∧
      (v.2.val = c.val.2.val ∨ v.2.val = c.val.2.val + 1) := by
  rw [zSupport_interior]; exact mem_faceQubits_iff _ _

lemma mem_xSupport_interior_iff {L : ℕ}
    (c : XInteriorCornerIdx L) (v : VtxIdx L) :
    v ∈ xSupport (.interior c) ↔
      (v.1.val = c.val.1.val ∨ v.1.val = c.val.1.val + 1) ∧
      (v.2.val = c.val.2.val ∨ v.2.val = c.val.2.val + 1) := by
  rw [xSupport_interior]; exact mem_faceQubits_iff _ _

lemma mem_zSupport_leftBdy_iff {L : ℕ} (k : RscBdyIdx L) (v : VtxIdx L) :
    v ∈ zSupport (.leftBdy k) ↔
      v.1.val = 0 ∧ (v.2.val = 2 * k.val + 1 ∨ v.2.val = 2 * k.val + 2) := by
  obtain ⟨v1, v2⟩ := v
  simp_all [zSupport, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  tauto

lemma mem_zSupport_rightBdy_iff {L : ℕ} (k : RscBdyIdx L) (v : VtxIdx L) :
    v ∈ zSupport (.rightBdy k) ↔
      v.1.val = L - 1 ∧ (v.2.val = 2 * k.val ∨ v.2.val = 2 * k.val + 1) := by
  obtain ⟨v1, v2⟩ := v
  simp_all [zSupport, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  tauto

lemma mem_xSupport_topBdy_iff {L : ℕ} (k : RscBdyIdx L) (v : VtxIdx L) :
    v ∈ xSupport (.topBdy k) ↔
      v.2.val = 0 ∧ (v.1.val = 2 * k.val ∨ v.1.val = 2 * k.val + 1) := by
  obtain ⟨v1, v2⟩ := v
  simp_all [xSupport, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  tauto

lemma mem_xSupport_bottomBdy_iff {L : ℕ} (k : RscBdyIdx L) (v : VtxIdx L) :
    v ∈ xSupport (.bottomBdy k) ↔
      v.2.val = L - 1 ∧ (v.1.val = 2 * k.val + 1 ∨ v.1.val = 2 * k.val + 2) := by
  obtain ⟨v1, v2⟩ := v
  simp_all [xSupport, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  tauto

/-! ## Cardinalities of the boundary supports -/

lemma xSupport_topBdy_card {L : ℕ} (k : RscBdyIdx L) :
    (xSupport (.topBdy k)).card = 2 := by
  unfold xSupport
  rw [Finset.card_insert_of_notMem, Finset.card_singleton]
  rw [Finset.mem_singleton]
  intro h
  have h := congrArg (fun p : VtxIdx L => p.1.val) h
  simp at h

lemma xSupport_bottomBdy_card {L : ℕ} (k : RscBdyIdx L) :
    (xSupport (.bottomBdy k)).card = 2 := by
  unfold xSupport
  rw [Finset.card_insert_of_notMem, Finset.card_singleton]
  rw [Finset.mem_singleton]
  intro h
  have h := congrArg (fun p : VtxIdx L => p.1.val) h
  simp at h

lemma zSupport_leftBdy_card {L : ℕ} (k : RscBdyIdx L) :
    (zSupport (.leftBdy k)).card = 2 := by
  unfold zSupport
  rw [Finset.card_insert_of_notMem, Finset.card_singleton]
  rw [Finset.mem_singleton]
  intro h
  have h := congrArg (fun p : VtxIdx L => p.2.val) h
  simp at h

lemma zSupport_rightBdy_card {L : ℕ} (k : RscBdyIdx L) :
    (zSupport (.rightBdy k)).card = 2 := by
  unfold zSupport
  rw [Finset.card_insert_of_notMem, Finset.card_singleton]
  rw [Finset.mem_singleton]
  intro h
  have h := congrArg (fun p : VtxIdx L => p.2.val) h
  simp at h

/-! ## Boundary maps -/

/-- `∂₂ : C₂ → C₁` for the rotated surface code. -/
def rscBoundary2 (L : ℕ) :
    (XFaceIdx L → ZMod 2) →ₗ[ZMod 2] (VtxIdx L → ZMod 2) where
  toFun c v := ∑ xf : XFaceIdx L, c xf * (if v ∈ xSupport xf then 1 else 0)
  map_add' c d := by
    funext v
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    funext v
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      mul_assoc]

/-- `∂₁ : C₁ → C₀` for the rotated surface code. -/
def rscBoundary1 (L : ℕ) :
    (VtxIdx L → ZMod 2) →ₗ[ZMod 2] (ZFaceIdx L → ZMod 2) where
  toFun c zf := ∑ v ∈ zSupport zf, c v
  map_add' c d := by
    funext zf
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' a c := by
    funext zf
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

/-!
## Notation

The scoped `RotatedSurfaceChain` notation renders the rotated-surface boundary
maps as `∂₂ L c`, `∂₁ L c` (and `δ⁰ L s` for the Z-side cut map, declared next
to it in `H1Dimension.lean`), mirroring the toric `ToricChain` scope. The
lattice size stays an explicit argument, exactly as for the underlying
constants, so the conversion is purely notational: `rscBoundary1` is still the
declaration name for `simp [rscBoundary1]`, `unfold`, and lemma names. Enable
with `open scoped RotatedSurfaceChain`.
-/

/-- `∂₂` is the rotated-surface face-boundary map `rscBoundary2 L`. Scoped:
`open scoped RotatedSurfaceChain`. -/
scoped[RotatedSurfaceChain] notation "∂₂" =>
  Quantum.Stabilizer.Lattice.RotatedSurface.rscBoundary2

/-- `∂₁` is the rotated-surface edge-boundary map `rscBoundary1 L`. Scoped:
`open scoped RotatedSurfaceChain`. -/
scoped[RotatedSurfaceChain] notation "∂₁" =>
  Quantum.Stabilizer.Lattice.RotatedSurface.rscBoundary1

open scoped RotatedSurfaceChain

@[simp] theorem rscBoundary2_apply (L : ℕ) (c : XFaceIdx L → ZMod 2)
    (v : VtxIdx L) :
    ∂₂ L c v =
      ∑ xf : XFaceIdx L, c xf * (if v ∈ xSupport xf then 1 else 0) := rfl

@[simp] theorem rscBoundary1_apply (L : ℕ) (c : VtxIdx L → ZMod 2)
    (zf : ZFaceIdx L) :
    ∂₁ L c zf = ∑ v ∈ zSupport zf, c v := rfl

/-! ## Intersection-cardinality lemmas -/

section InterCard
variable {L : ℕ}

/-- Indicator-sum equals cardinality of intersection (cast into `ZMod 2`). -/
private lemma sum_indicator_eq_inter_card (zf : ZFaceIdx L) (xf : XFaceIdx L) :
    (∑ v ∈ zSupport zf, (if v ∈ xSupport xf then (1 : ZMod 2) else 0)) =
      ((zSupport zf ∩ xSupport xf).card : ZMod 2) := by
  rw [Finset.sum_boole]; rfl

private lemma cast_card_zero_of_eq_empty {α : Type*}
    {s : Finset α} (h : s = ∅) : (s.card : ZMod 2) = 0 := by simp [h]

private lemma cast_card_two_zmod : ((2 : ℕ) : ZMod 2) = 0 := by decide

/-- If `s = {v0, v1}` with `v0 ≠ v1`, then the cardinality cast to `ZMod 2` is
`0`. -/
private lemma cast_card_zero_of_eq_pair {α : Type*} [DecidableEq α]
    {s : Finset α} {v0 v1 : α} (h_eq : s = {v0, v1}) (hne : v0 ≠ v1) :
    (s.card : ZMod 2) = 0 := by
  rw [h_eq, Finset.card_insert_of_notMem (by simpa using hne),
    Finset.card_singleton]
  decide

/-! ### Boundary × boundary — empty in all 4 cases. -/

private lemma inter_leftBdy_topBdy_empty (k k' : RscBdyIdx L) :
    zSupport (.leftBdy k) ∩ xSupport (.topBdy k') = ∅ := by
  rw [← Finset.not_nonempty_iff_eq_empty]
  rintro ⟨v, hv⟩
  rw [Finset.mem_inter, mem_zSupport_leftBdy_iff, mem_xSupport_topBdy_iff] at hv
  omega

private lemma inter_leftBdy_bottomBdy_empty (k k' : RscBdyIdx L) :
    zSupport (.leftBdy k) ∩ xSupport (.bottomBdy k') = ∅ := by
  rw [← Finset.not_nonempty_iff_eq_empty]
  rintro ⟨v, hv⟩
  rw [Finset.mem_inter, mem_zSupport_leftBdy_iff, mem_xSupport_bottomBdy_iff] at hv
  have := k'.isLt; omega

private lemma inter_rightBdy_topBdy_empty (k k' : RscBdyIdx L) :
    zSupport (.rightBdy k) ∩ xSupport (.topBdy k') = ∅ := by
  rw [← Finset.not_nonempty_iff_eq_empty]
  rintro ⟨v, hv⟩
  rw [Finset.mem_inter, mem_zSupport_rightBdy_iff, mem_xSupport_topBdy_iff] at hv
  have := k'.isLt; omega

private lemma inter_rightBdy_bottomBdy_empty (k k' : RscBdyIdx L) :
    zSupport (.rightBdy k) ∩ xSupport (.bottomBdy k') = ∅ := by
  rw [← Finset.not_nonempty_iff_eq_empty]
  rintro ⟨v, hv⟩
  rw [Finset.mem_inter, mem_zSupport_rightBdy_iff, mem_xSupport_bottomBdy_iff] at hv
  have hk := k.isLt
  have hk' := k'.isLt
  omega

/-! ### Interior × boundary

In each case the intersection is *either* empty *or* equals the boundary stab's
support. We dispatch the nonempty branch via `Finset.inter_eq_right` /
`Finset.inter_eq_left`. -/

private lemma inter_interior_topBdy_card_even
    (zc : ZInteriorCornerIdx L) (k : RscBdyIdx L) :
    ((zSupport (.interior zc) ∩ xSupport (.topBdy k)).card : ZMod 2) = 0 := by
  have hpar : (zc.val.1.val + zc.val.2.val) % 2 = 0 := zc.property
  by_cases hb_eq : zc.val.2.val = 0
  · by_cases ha_eq : zc.val.1.val = 2 * k.val
    · have h_eq : zSupport (.interior zc) ∩ xSupport (.topBdy k) =
          xSupport (.topBdy k) := by
        rw [Finset.inter_eq_right]
        intro w hw
        rw [mem_xSupport_topBdy_iff] at hw
        rw [mem_zSupport_interior_iff]
        obtain ⟨hw2, hw1⟩ := hw
        refine ⟨?_, Or.inl ?_⟩
        · rcases hw1 with h | h
          · left; omega
          · right; omega
        · omega
      rw [h_eq, xSupport_topBdy_card]
      exact cast_card_two_zmod
    · apply cast_card_zero_of_eq_empty
      rw [← Finset.not_nonempty_iff_eq_empty]
      rintro ⟨w, hw⟩
      rw [Finset.mem_inter, mem_zSupport_interior_iff,
        mem_xSupport_topBdy_iff] at hw
      obtain ⟨⟨hwz1, _⟩, _, hwx1⟩ := hw
      rcases hwz1 with h | h <;> rcases hwx1 with h' | h' <;> omega
  · apply cast_card_zero_of_eq_empty
    rw [← Finset.not_nonempty_iff_eq_empty]
    rintro ⟨w, hw⟩
    rw [Finset.mem_inter, mem_zSupport_interior_iff,
      mem_xSupport_topBdy_iff] at hw
    obtain ⟨⟨_, hwz2⟩, hwx2, _⟩ := hw
    rcases hwz2 with h | h <;> omega

private lemma inter_interior_bottomBdy_card_even [Fact (Odd L)]
    (zc : ZInteriorCornerIdx L) (k : RscBdyIdx L) :
    ((zSupport (.interior zc) ∩ xSupport (.bottomBdy k)).card : ZMod 2) = 0 := by
  have hpar : (zc.val.1.val + zc.val.2.val) % 2 = 0 := zc.property
  have hL_odd : L % 2 = 1 := Nat.odd_iff.mp Fact.out
  have hkLt : 2 * k.val + 2 < L := by have := k.isLt; omega
  by_cases hb_eq : zc.val.2.val + 1 = L - 1
  · by_cases ha_eq : zc.val.1.val = 2 * k.val + 1
    · have h_eq : zSupport (.interior zc) ∩ xSupport (.bottomBdy k) =
          xSupport (.bottomBdy k) := by
        rw [Finset.inter_eq_right]
        intro w hw
        rw [mem_xSupport_bottomBdy_iff] at hw
        rw [mem_zSupport_interior_iff]
        obtain ⟨hw2, hw1⟩ := hw
        refine ⟨?_, Or.inr ?_⟩
        · rcases hw1 with h | h
          · left; omega
          · right; omega
        · omega
      rw [h_eq, xSupport_bottomBdy_card]
      exact cast_card_two_zmod
    · apply cast_card_zero_of_eq_empty
      rw [← Finset.not_nonempty_iff_eq_empty]
      rintro ⟨w, hw⟩
      rw [Finset.mem_inter, mem_zSupport_interior_iff,
        mem_xSupport_bottomBdy_iff] at hw
      obtain ⟨⟨hwz1, _⟩, _, hwx1⟩ := hw
      rcases hwz1 with h | h <;> rcases hwx1 with h' | h' <;> omega
  · apply cast_card_zero_of_eq_empty
    rw [← Finset.not_nonempty_iff_eq_empty]
    rintro ⟨w, hw⟩
    rw [Finset.mem_inter, mem_zSupport_interior_iff,
      mem_xSupport_bottomBdy_iff] at hw
    obtain ⟨⟨_, hwz2⟩, hwx2, _⟩ := hw
    rcases hwz2 with h | h <;> omega

private lemma inter_leftBdy_interior_card_even
    (k : RscBdyIdx L) (xc : XInteriorCornerIdx L) :
    ((zSupport (.leftBdy k) ∩ xSupport (.interior xc)).card : ZMod 2) = 0 := by
  have hpar : (xc.val.1.val + xc.val.2.val) % 2 = 1 := xc.property
  have hkLt : 2 * k.val + 2 < L := by have := k.isLt; omega
  by_cases ha_eq : xc.val.1.val = 0
  · by_cases hb_eq : xc.val.2.val = 2 * k.val + 1
    · have h_eq : zSupport (.leftBdy k) ∩ xSupport (.interior xc) =
          zSupport (.leftBdy k) := by
        rw [Finset.inter_eq_left]
        intro w hw
        rw [mem_zSupport_leftBdy_iff] at hw
        rw [mem_xSupport_interior_iff]
        obtain ⟨hw1, hw2⟩ := hw
        refine ⟨Or.inl ?_, ?_⟩
        · omega
        · rcases hw2 with h | h
          · left; omega
          · right; omega
      rw [h_eq, zSupport_leftBdy_card]
      exact cast_card_two_zmod
    · apply cast_card_zero_of_eq_empty
      rw [← Finset.not_nonempty_iff_eq_empty]
      rintro ⟨w, hw⟩
      rw [Finset.mem_inter, mem_zSupport_leftBdy_iff,
        mem_xSupport_interior_iff] at hw
      obtain ⟨⟨_, hwz2⟩, _, hwx2⟩ := hw
      rcases hwz2 with h | h <;> rcases hwx2 with h' | h' <;> omega
  · apply cast_card_zero_of_eq_empty
    rw [← Finset.not_nonempty_iff_eq_empty]
    rintro ⟨w, hw⟩
    rw [Finset.mem_inter, mem_zSupport_leftBdy_iff,
      mem_xSupport_interior_iff] at hw
    obtain ⟨⟨hwz1, _⟩, hwx1, _⟩ := hw
    rcases hwx1 with h | h <;> omega

private lemma inter_rightBdy_interior_card_even [Fact (Odd L)]
    (k : RscBdyIdx L) (xc : XInteriorCornerIdx L) :
    ((zSupport (.rightBdy k) ∩ xSupport (.interior xc)).card : ZMod 2) = 0 := by
  have hpar : (xc.val.1.val + xc.val.2.val) % 2 = 1 := xc.property
  have hL_odd : L % 2 = 1 := Nat.odd_iff.mp Fact.out
  have hkLt : 2 * k.val + 1 < L := by have := k.isLt; omega
  by_cases ha_eq : xc.val.1.val + 1 = L - 1
  · by_cases hb_eq : xc.val.2.val = 2 * k.val
    · have h_eq : zSupport (.rightBdy k) ∩ xSupport (.interior xc) =
          zSupport (.rightBdy k) := by
        rw [Finset.inter_eq_left]
        intro w hw
        rw [mem_zSupport_rightBdy_iff] at hw
        rw [mem_xSupport_interior_iff]
        obtain ⟨hw1, hw2⟩ := hw
        refine ⟨Or.inr ?_, ?_⟩
        · omega
        · rcases hw2 with h | h
          · left; omega
          · right; omega
      rw [h_eq, zSupport_rightBdy_card]
      exact cast_card_two_zmod
    · apply cast_card_zero_of_eq_empty
      rw [← Finset.not_nonempty_iff_eq_empty]
      rintro ⟨w, hw⟩
      rw [Finset.mem_inter, mem_zSupport_rightBdy_iff,
        mem_xSupport_interior_iff] at hw
      obtain ⟨⟨_, hwz2⟩, _, hwx2⟩ := hw
      rcases hwz2 with h | h <;> rcases hwx2 with h' | h' <;> omega
  · apply cast_card_zero_of_eq_empty
    rw [← Finset.not_nonempty_iff_eq_empty]
    rintro ⟨w, hw⟩
    rw [Finset.mem_inter, mem_zSupport_rightBdy_iff,
      mem_xSupport_interior_iff] at hw
    obtain ⟨⟨hwz1, _⟩, hwx1, _⟩ := hw
    rcases hwx1 with h | h <;> omega

/-! ### Interior × interior

For two opposite-parity 2×2 faces the intersection is either empty (anchors
farther than `1` apart) or exactly a 2-qubit shared edge. We case-split on
`Δa, Δb ∈ {0, ±1}` and dispatch each via `Finset.ext` to an explicit two-element
finset. -/

/-- Helper: the intersection of the face supports collapses to a 2-qubit edge
whenever both anchors are within distance `1` (column-wise and row-wise). Used
inside the interior-interior proof. -/
private lemma inter_inter_two_card
    {α : Type*} [DecidableEq α] {s : Finset α} {q0 q1 : α}
    (h_eq : s = ({q0, q1} : Finset α)) (hne : q0 ≠ q1) :
    (s.card : ZMod 2) = 0 :=
  cast_card_zero_of_eq_pair h_eq hne

private lemma inter_interior_interior_card_even
    (zc : ZInteriorCornerIdx L) (xc : XInteriorCornerIdx L) :
    ((zSupport (.interior zc) ∩ xSupport (.interior xc)).card : ZMod 2) = 0 := by
  have hpz : (zc.val.1.val + zc.val.2.val) % 2 = 0 := zc.property
  have hpx : (xc.val.1.val + xc.val.2.val) % 2 = 1 := xc.property
  have hza : zc.val.1.val + 1 < L := by have := zc.val.1.isLt; omega
  have hzb : zc.val.2.val + 1 < L := by have := zc.val.2.isLt; omega
  have hxa : xc.val.1.val + 1 < L := by have := xc.val.1.isLt; omega
  have hxb : xc.val.2.val + 1 < L := by have := xc.val.2.isLt; omega
  have hzaLo : zc.val.1.val < L := by omega
  have hzbLo : zc.val.2.val < L := by omega
  by_cases hcol_far : zc.val.1.val + 2 ≤ xc.val.1.val ∨
                       xc.val.1.val + 2 ≤ zc.val.1.val
  · apply cast_card_zero_of_eq_empty
    rw [← Finset.not_nonempty_iff_eq_empty]
    rintro ⟨w, hw⟩
    rw [Finset.mem_inter, mem_zSupport_interior_iff,
      mem_xSupport_interior_iff] at hw
    obtain ⟨⟨hwz1, _⟩, hwx1, _⟩ := hw
    rcases hwz1 with h | h <;> rcases hwx1 with h' | h' <;> omega
  · push Not at hcol_far
    by_cases hrow_far : zc.val.2.val + 2 ≤ xc.val.2.val ∨
                         xc.val.2.val + 2 ≤ zc.val.2.val
    · apply cast_card_zero_of_eq_empty
      rw [← Finset.not_nonempty_iff_eq_empty]
      rintro ⟨w, hw⟩
      rw [Finset.mem_inter, mem_zSupport_interior_iff,
        mem_xSupport_interior_iff] at hw
      obtain ⟨⟨_, hwz2⟩, _, hwx2⟩ := hw
      rcases hwz2 with h | h <;> rcases hwx2 with h' | h' <;> omega
    · push Not at hrow_far
      have hΔa : zc.val.1.val = xc.val.1.val ∨
                 zc.val.1.val + 1 = xc.val.1.val ∨
                 zc.val.1.val = xc.val.1.val + 1 := by omega
      have hΔb : zc.val.2.val = xc.val.2.val ∨
                 zc.val.2.val + 1 = xc.val.2.val ∨
                 zc.val.2.val = xc.val.2.val + 1 := by omega
      rcases hΔa with hda | hda | hda <;>
        rcases hΔb with hdb | hdb | hdb
      -- Parity-excluded: (=, =), and (±1, ±1).
      -- Valid:           (=, +1), (=, -1), (+1, =), (-1, =).
      all_goals first
        | (exfalso; omega)
        | skip
      -- (Δa, Δb) = (=, +1):  edge at row xc.b = zc.b + 1
      · -- hda : zc.1.val = xc.1.val, hdb : zc.2.val + 1 = xc.2.val
        refine cast_card_zero_of_eq_pair (v0 :=
          ((⟨zc.val.1.val, hzaLo⟩ : Fin L), (⟨zc.val.2.val + 1, hzb⟩ : Fin L)))
          (v1 :=
          ((⟨zc.val.1.val + 1, hza⟩ : Fin L), (⟨zc.val.2.val + 1, hzb⟩ : Fin L)))
          ?_ ?_
        · ext w
          obtain ⟨w1, w2⟩ := w
          simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
            mem_zSupport_interior_iff, mem_xSupport_interior_iff,
            Prod.mk.injEq, Fin.ext_iff]
          constructor
          · rintro ⟨⟨h1, h2⟩, h1', h2'⟩
            rcases h2 with hyL | hyL <;>
              rcases h2' with hyR | hyR <;>
              rcases h1 with hxL | hxL <;>
              first
                | (left; exact ⟨by omega, by omega⟩)
                | (right; exact ⟨by omega, by omega⟩)
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
              refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> omega
        · intro h
          have : zc.val.1.val = zc.val.1.val + 1 := by
            have hh := congrArg (fun p : VtxIdx L => p.1.val) h
            simp at hh
          omega
      -- (Δa, Δb) = (=, -1):  edge at row zc.b = xc.b + 1
      · -- hda : zc.1.val = xc.1.val, hdb : zc.2.val = xc.2.val + 1
        refine cast_card_zero_of_eq_pair (v0 :=
          ((⟨zc.val.1.val, hzaLo⟩ : Fin L), (⟨zc.val.2.val, hzbLo⟩ : Fin L)))
          (v1 :=
          ((⟨zc.val.1.val + 1, hza⟩ : Fin L), (⟨zc.val.2.val, hzbLo⟩ : Fin L)))
          ?_ ?_
        · ext w
          obtain ⟨w1, w2⟩ := w
          simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
            mem_zSupport_interior_iff, mem_xSupport_interior_iff,
            Prod.mk.injEq, Fin.ext_iff]
          constructor
          · rintro ⟨⟨h1, h2⟩, h1', h2'⟩
            rcases h2 with hyL | hyL <;>
              rcases h2' with hyR | hyR <;>
              rcases h1 with hxL | hxL <;>
              first
                | (left; exact ⟨by omega, by omega⟩)
                | (right; exact ⟨by omega, by omega⟩)
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
              refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> omega
        · intro h
          have : zc.val.1.val = zc.val.1.val + 1 := by
            have hh := congrArg (fun p : VtxIdx L => p.1.val) h
            simp at hh
          omega
      -- (Δa, Δb) = (+1, =):  edge at column xc.a = zc.a + 1
      · -- hda : zc.1.val + 1 = xc.1.val, hdb : zc.2.val = xc.2.val
        refine cast_card_zero_of_eq_pair (v0 :=
          ((⟨zc.val.1.val + 1, hza⟩ : Fin L), (⟨zc.val.2.val, hzbLo⟩ : Fin L)))
          (v1 :=
          ((⟨zc.val.1.val + 1, hza⟩ : Fin L), (⟨zc.val.2.val + 1, hzb⟩ : Fin L)))
          ?_ ?_
        · ext w
          obtain ⟨w1, w2⟩ := w
          simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
            mem_zSupport_interior_iff, mem_xSupport_interior_iff,
            Prod.mk.injEq, Fin.ext_iff]
          constructor
          · rintro ⟨⟨h1, h2⟩, h1', h2'⟩
            rcases h1 with hxL | hxL <;>
              rcases h1' with hxR | hxR <;>
              rcases h2 with hyL | hyL <;>
              first
                | (left; exact ⟨by omega, by omega⟩)
                | (right; exact ⟨by omega, by omega⟩)
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
              refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> omega
        · intro h
          have : zc.val.2.val = zc.val.2.val + 1 := by
            have hh := congrArg (fun p : VtxIdx L => p.2.val) h
            simp at hh
          omega
      -- (Δa, Δb) = (-1, =):  edge at column zc.a = xc.a + 1
      · -- hda : zc.1.val = xc.1.val + 1, hdb : zc.2.val = xc.2.val
        refine cast_card_zero_of_eq_pair (v0 :=
          ((⟨zc.val.1.val, hzaLo⟩ : Fin L), (⟨zc.val.2.val, hzbLo⟩ : Fin L)))
          (v1 :=
          ((⟨zc.val.1.val, hzaLo⟩ : Fin L), (⟨zc.val.2.val + 1, hzb⟩ : Fin L)))
          ?_ ?_
        · ext w
          obtain ⟨w1, w2⟩ := w
          simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
            mem_zSupport_interior_iff, mem_xSupport_interior_iff,
            Prod.mk.injEq, Fin.ext_iff]
          constructor
          · rintro ⟨⟨h1, h2⟩, h1', h2'⟩
            rcases h1 with hxL | hxL <;>
              rcases h1' with hxR | hxR <;>
              rcases h2 with hyL | hyL <;>
              first
                | (left; exact ⟨by omega, by omega⟩)
                | (right; exact ⟨by omega, by omega⟩)
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
              refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> omega
        · intro h
          have : zc.val.2.val = zc.val.2.val + 1 := by
            have hh := congrArg (fun p : VtxIdx L => p.2.val) h
            simp at hh
          omega

end InterCard

/-! ## Main chain-complex law -/

/-- For every `(zf, xf)` pair the intersection has even cardinality in `ZMod 2`.
Dispatches to the 9 per-case lemmas above. -/
private lemma inter_card_even {L : ℕ} [Fact (Odd L)]
    (zf : ZFaceIdx L) (xf : XFaceIdx L) :
    ((zSupport zf ∩ xSupport xf).card : ZMod 2) = 0 := by
  cases zf with
  | interior zc => cases xf with
    | interior xc => exact inter_interior_interior_card_even zc xc
    | topBdy k => exact inter_interior_topBdy_card_even zc k
    | bottomBdy k => exact inter_interior_bottomBdy_card_even zc k
  | leftBdy k => cases xf with
    | interior xc => exact inter_leftBdy_interior_card_even k xc
    | topBdy k' =>
        exact cast_card_zero_of_eq_empty (inter_leftBdy_topBdy_empty k k')
    | bottomBdy k' =>
        exact cast_card_zero_of_eq_empty (inter_leftBdy_bottomBdy_empty k k')
  | rightBdy k => cases xf with
    | interior xc => exact inter_rightBdy_interior_card_even k xc
    | topBdy k' =>
        exact cast_card_zero_of_eq_empty (inter_rightBdy_topBdy_empty k k')
    | bottomBdy k' =>
        exact cast_card_zero_of_eq_empty (inter_rightBdy_bottomBdy_empty k k')

/-- Chain-complex law: `∂₁ ∘ ∂₂ = 0`. -/
theorem rscBoundary_comp_zero (L : ℕ) [Fact (Odd L)] :
    (∂₁ L).comp (∂₂ L) = 0 := by
  ext c zf
  simp only [LinearMap.comp_apply, rscBoundary1_apply, rscBoundary2_apply,
    LinearMap.zero_apply, Pi.zero_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero ?_
  intro xf _
  rw [← Finset.mul_sum, sum_indicator_eq_inter_card, inter_card_even, mul_zero]

/-- Pointwise corollary of `rscBoundary_comp_zero`. -/
theorem rscBoundary_comp_zero_apply (L : ℕ) [Fact (Odd L)]
    (c : XFaceIdx L → ZMod 2) :
    ∂₁ L (∂₂ L c) = 0 := by
  have h := congrArg (fun T => T c) (rscBoundary_comp_zero L)
  simpa using h

end RotatedSurface
end Lattice
end Stabilizer
end Quantum
