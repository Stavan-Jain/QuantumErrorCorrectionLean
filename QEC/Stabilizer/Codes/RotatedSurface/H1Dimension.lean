import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import QEC.Stabilizer.Codes.RotatedSurface.ChainComplex

/-!
# `dim H₁ = 1` for the rotated surface code

The rotated surface code at `L × L` (odd `L ≥ 3`) has `dim H₁ = 1` — one
logical qubit.  The proof rests on the *anchor-qubit* trick:

* Each X-stabiliser has a unique "anchor" qubit (its row-major minimum)
  that no other X-stabiliser covers.  Hence the X-stab indicator family
  is linearly independent — `ker rscBoundary2 = ⊥`.
* The same argument for Z-stabs gives `ker cutMap = ⊥`.
* Combined with the cardinality identity `|X-stabs| + |Z-stabs| = L² − 1`
  (for `L` odd) and the abstract rank-nullity from `HomologicalCode`,
  we conclude `dim H₁ = 1`.
-/

namespace Quantum
namespace Stabilizer
namespace Lattice
namespace RotatedSurface

open scoped BigOperators
open scoped Homology
open scoped RotatedSurfaceChain

/-! ## Basic ambient facts -/

variable {L : ℕ}

private lemma rsc_facts [Fact (Odd L)] [Fact (3 ≤ L)] :
    (3 ≤ L) ∧ (L % 2 = 1) ∧ (0 < L) ∧ ((L - 1) % 2 = 0) := by
  have hLodd : L % 2 = 1 := Nat.odd_iff.mp Fact.out
  have hLge : 3 ≤ L := Fact.out
  refine ⟨hLge, hLodd, by omega, ?_⟩
  omega

/-- `2 * ((L − 1) / 2) = L − 1` when `L` is odd. -/
private lemma two_mul_half_pred [Fact (Odd L)] : 2 * ((L - 1) / 2) = L - 1 := by
  have hLodd : L % 2 = 1 := Nat.odd_iff.mp Fact.out
  have h_pos : 1 ≤ L := by
    rcases (Fact.out : Odd L) with ⟨m, hm⟩
    omega
  have h4 : (L - 1) % 2 = 0 := by omega
  have hdvd : 2 ∣ (L - 1) := Nat.dvd_of_mod_eq_zero h4
  rw [Nat.mul_comm]
  exact Nat.div_mul_cancel hdvd

/-- `2 * k.val + 2 ≤ L − 1` for any boundary index `k`. -/
private lemma rsc_bdy_idx_lt [Fact (Odd L)] [Fact (3 ≤ L)] (k : RscBdyIdx L) :
    2 * k.val + 2 ≤ L - 1 := by
  have hk : k.val < (L - 1) / 2 := k.isLt
  have h2div : 2 * ((L - 1) / 2) = L - 1 := two_mul_half_pred
  omega

/-! ## Cardinalities -/

section Cardinality

/-- The Z- and X-interior corner subtypes partition `Fin (L-1) × Fin (L-1)`. -/
lemma card_ZInteriorCornerIdx_add_card_XInteriorCornerIdx :
    Fintype.card (ZInteriorCornerIdx L) +
      Fintype.card (XInteriorCornerIdx L) = (L - 1) ^ 2 := by
  classical
  have hz : Fintype.card (ZInteriorCornerIdx L) =
      (Finset.univ.filter
        (fun c : Fin (L - 1) × Fin (L - 1) => (c.1.val + c.2.val) % 2 = 0)).card := by
    simp [ZInteriorCornerIdx, Fintype.card_subtype]
  have hx : Fintype.card (XInteriorCornerIdx L) =
      (Finset.univ.filter
        (fun c : Fin (L - 1) × Fin (L - 1) => (c.1.val + c.2.val) % 2 = 1)).card := by
    simp [XInteriorCornerIdx, Fintype.card_subtype]
  rw [hz, hx]
  have h_compl :
      (Finset.univ.filter
          (fun c : Fin (L - 1) × Fin (L - 1) => (c.1.val + c.2.val) % 2 = 1)) =
        (Finset.univ.filter
          (fun c : Fin (L - 1) × Fin (L - 1) => ¬ (c.1.val + c.2.val) % 2 = 0)) := by
    apply Finset.filter_congr
    intro c _
    omega
  rw [h_compl, Finset.card_filter_add_card_filter_not]
  simp [Fintype.card_prod, Fintype.card_fin, sq]

lemma card_RscBdyIdx : Fintype.card (RscBdyIdx L) = (L - 1) / 2 := by simp [RscBdyIdx]

lemma card_ZFaceIdx_via_equiv :
    Fintype.card (ZFaceIdx L) =
      Fintype.card (ZInteriorCornerIdx L) + 2 * ((L - 1) / 2) := by
  rw [Fintype.card_congr (zFaceIdxEquivSum L), Fintype.card_sum, Fintype.card_sum,
    card_RscBdyIdx]
  ring

lemma card_XFaceIdx_via_equiv :
    Fintype.card (XFaceIdx L) =
      Fintype.card (XInteriorCornerIdx L) + 2 * ((L - 1) / 2) := by
  rw [Fintype.card_congr (xFaceIdxEquivSum L), Fintype.card_sum, Fintype.card_sum,
    card_RscBdyIdx]
  ring

/-- For `L` odd, `|ZFaceIdx L| + |XFaceIdx L| = L² − 1`. -/
lemma card_ZFaceIdx_add_card_XFaceIdx [Fact (Odd L)] :
    Fintype.card (ZFaceIdx L) + Fintype.card (XFaceIdx L) = L * L - 1 := by
  have hL_odd : L % 2 = 1 := Nat.odd_iff.mp Fact.out
  have hL_pos : 1 ≤ L := by
    have : Odd L := Fact.out
    rcases this with ⟨m, hm⟩
    omega
  rw [card_ZFaceIdx_via_equiv, card_XFaceIdx_via_equiv]
  have hsum :
      Fintype.card (ZInteriorCornerIdx L) +
        Fintype.card (XInteriorCornerIdx L) = (L - 1) ^ 2 :=
    card_ZInteriorCornerIdx_add_card_XInteriorCornerIdx
  have h_half : 2 * ((L - 1) / 2) = L - 1 := two_mul_half_pred
  have hL2 : 1 ≤ L * L := by nlinarith [hL_pos]
  have hexpand : (L - 1) ^ 2 + 2 * (L - 1) = L * L - 1 := by
    zify [hL_pos, hL2]; ring
  have hcombine :
      (Fintype.card (ZInteriorCornerIdx L) + 2 * ((L - 1) / 2)) +
        (Fintype.card (XInteriorCornerIdx L) + 2 * ((L - 1) / 2)) =
      (L - 1) ^ 2 + 2 * (L - 1) := by
    rw [h_half]; linarith
  rw [hcombine, hexpand]

end Cardinality

/-! ## Finrank of chain spaces -/

lemma rsc_finrank_C1 (L : ℕ) :
    dim₂ (VtxIdx L → ZMod 2) = L * L := by
  rw [Module.finrank_fintype_fun_eq_card]
  simp [VtxIdx, Fintype.card_prod, Fintype.card_fin]

lemma rsc_finrank_C0 (L : ℕ) :
    dim₂ (ZFaceIdx L → ZMod 2) = Fintype.card (ZFaceIdx L) := by
  rw [Module.finrank_fintype_fun_eq_card]

lemma rsc_finrank_C2 (L : ℕ) :
    dim₂ (XFaceIdx L → ZMod 2) = Fintype.card (XFaceIdx L) := by
  rw [Module.finrank_fintype_fun_eq_card]

/-! ## Anchor-qubit framework

For each X- (resp. Z-) stabilizer we assign a unique "anchor" qubit:
its lex-minimum supported qubit.  The argument shows that distinct
stabilisers of the same colour have distinct anchors, each anchor is in
the corresponding support, and each anchor is the lex-min of its
support.  This gives a row-echelon decomposition forcing linear
independence within each colour. -/

/-- Row-major qubit index. -/
@[reducible] def qubitIdx (v : VtxIdx L) : ℕ := v.2.val * L + v.1.val

lemma qubitIdx_def (v : VtxIdx L) : qubitIdx v = v.2.val * L + v.1.val := rfl

/-- "Anchor" qubit index of an X-stabilizer. -/
def xAnchorIdx : XFaceIdx L → ℕ
  | .interior c => c.val.2.val * L + c.val.1.val
  | .topBdy k => 2 * k.val
  | .bottomBdy k => (L - 1) * L + 2 * k.val + 1

@[simp] lemma xAnchorIdx_interior (c : XInteriorCornerIdx L) :
    xAnchorIdx (XFaceIdx.interior c) = c.val.2.val * L + c.val.1.val := rfl

@[simp] lemma xAnchorIdx_topBdy (k : RscBdyIdx L) :
    xAnchorIdx (XFaceIdx.topBdy k) = 2 * k.val := rfl

@[simp] lemma xAnchorIdx_bottomBdy (k : RscBdyIdx L) :
    xAnchorIdx (XFaceIdx.bottomBdy k) = (L - 1) * L + 2 * k.val + 1 := rfl

/-- "Anchor" qubit index of a Z-stabilizer. -/
def zAnchorIdx : ZFaceIdx L → ℕ
  | .interior c => c.val.2.val * L + c.val.1.val
  | .leftBdy k => (2 * k.val + 1) * L
  | .rightBdy k => 2 * k.val * L + (L - 1)

@[simp] lemma zAnchorIdx_interior (c : ZInteriorCornerIdx L) :
    zAnchorIdx (ZFaceIdx.interior c) = c.val.2.val * L + c.val.1.val := rfl

@[simp] lemma zAnchorIdx_leftBdy (k : RscBdyIdx L) :
    zAnchorIdx (ZFaceIdx.leftBdy k) = (2 * k.val + 1) * L := rfl

@[simp] lemma zAnchorIdx_rightBdy (k : RscBdyIdx L) :
    zAnchorIdx (ZFaceIdx.rightBdy k) = 2 * k.val * L + (L - 1) := rfl

/-! ### X-anchor properties -/

variable [Fact (Odd L)] [Fact (3 ≤ L)]

/-- The qubit at `xAnchorIdx xf` is in `xSupport xf`. -/
lemma xAnchor_mem_xSupport (xf : XFaceIdx L) :
    ∃ v : VtxIdx L, v ∈ xSupport xf ∧ qubitIdx v = xAnchorIdx xf := by
  have ⟨h1, h2, h3, h4⟩ := rsc_facts (L := L)
  cases xf with
  | interior c =>
      have h_a : c.val.1.val < L := by have := c.val.1.isLt; omega
      have h_b : c.val.2.val < L := by have := c.val.2.isLt; omega
      refine ⟨(⟨c.val.1.val, h_a⟩, ⟨c.val.2.val, h_b⟩), ?_, ?_⟩
      · rw [xSupport_interior]
        unfold faceQubits cornerLo cornerHi
        simp [Finset.mem_insert]
      · simp [qubitIdx]
  | topBdy k =>
      have hk := rsc_bdy_idx_lt k
      refine ⟨(⟨2 * k.val, by omega⟩, ⟨0, h3⟩), ?_, ?_⟩
      · rw [mem_xSupport_topBdy_iff]; exact ⟨rfl, Or.inl rfl⟩
      · simp [qubitIdx]
  | bottomBdy k =>
      have hk := rsc_bdy_idx_lt k
      refine ⟨(⟨2 * k.val + 1, by omega⟩, ⟨L - 1, by omega⟩), ?_, ?_⟩
      · rw [mem_xSupport_bottomBdy_iff]; exact ⟨rfl, Or.inl rfl⟩
      · simp [qubitIdx]; ring

/-- Every qubit in `xSupport xf` has `qubitIdx ≥ xAnchorIdx xf`. -/
lemma xAnchor_le_qubitIdx_of_mem (xf : XFaceIdx L) (v : VtxIdx L)
    (hv : v ∈ xSupport xf) : xAnchorIdx xf ≤ qubitIdx v := by
  have ⟨h1, h2, h3, h4⟩ := rsc_facts (L := L)
  cases xf with
  | interior c =>
      rw [xSupport_interior, mem_faceQubits_iff] at hv
      obtain ⟨hx, hy⟩ := hv
      simp only [xAnchorIdx_interior, qubitIdx_def]
      rcases hx with hx | hx <;> rcases hy with hy | hy <;> nlinarith
  | topBdy k =>
      rw [mem_xSupport_topBdy_iff] at hv
      obtain ⟨h_y, h_x⟩ := hv
      simp only [xAnchorIdx_topBdy, qubitIdx_def]
      rcases h_x with h | h <;> omega
  | bottomBdy k =>
      rw [mem_xSupport_bottomBdy_iff] at hv
      obtain ⟨h_y, h_x⟩ := hv
      simp only [xAnchorIdx_bottomBdy, qubitIdx_def]
      rcases h_x with h | h <;> nlinarith

/-- Distinct X-stabs have distinct anchors. -/
lemma xAnchorIdx_injective : Function.Injective (xAnchorIdx : XFaceIdx L → ℕ) := by
  have ⟨h1, h2, h3, h4⟩ := rsc_facts (L := L)
  intro xf xf' heq
  cases xf with
  | interior c => cases xf' with
    | interior c' =>
        simp only [xAnchorIdx_interior] at heq
        have h_a : c.val.1.val < L := by have := c.val.1.isLt; omega
        have h_a' : c'.val.1.val < L := by have := c'.val.1.isLt; omega
        -- y*L + x = y'*L + x' with x, x' < L → x = x' ∧ y = y'.
        have hx_eq : c.val.1.val = c'.val.1.val := by
          have hmod : (c.val.2.val * L + c.val.1.val) % L =
              (c'.val.2.val * L + c'.val.1.val) % L := by rw [heq]
          rw [Nat.add_comm (c.val.2.val * L) c.val.1.val,
              Nat.add_comm (c'.val.2.val * L) c'.val.1.val,
              Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right,
              Nat.mod_eq_of_lt h_a, Nat.mod_eq_of_lt h_a'] at hmod
          exact hmod
        have hy_eq : c.val.2.val = c'.val.2.val := by
          have : c.val.2.val * L = c'.val.2.val * L := by linarith
          exact Nat.eq_of_mul_eq_mul_right h3 this
        congr 1
        refine Subtype.ext ?_
        refine Prod.ext ?_ ?_
        · exact Fin.ext hx_eq
        · exact Fin.ext hy_eq
    | topBdy k =>
        exfalso
        simp only [xAnchorIdx_interior, xAnchorIdx_topBdy] at heq
        have hp : (c.val.1.val + c.val.2.val) % 2 = 1 := c.property
        have h_a := c.val.1.isLt
        have h_b := c.val.2.isLt
        have hk := rsc_bdy_idx_lt k
        -- Case-split on y = 0 or y ≥ 1.
        rcases Nat.eq_zero_or_pos c.val.2.val with hy | hy
        · -- y = 0: x = 2k from heq. Parity hp: x odd. 2k even. ⊥.
          rw [hy] at heq; simp at heq; omega
        · -- y ≥ 1: y * L ≥ L > 2k.
          have h_prod : L ≤ c.val.2.val * L := by
            calc L = 1 * L := (one_mul L).symm
              _ ≤ c.val.2.val * L := Nat.mul_le_mul_right L hy
          omega
    | bottomBdy k =>
        exfalso
        simp only [xAnchorIdx_interior, xAnchorIdx_bottomBdy] at heq
        have h_a := c.val.1.isLt
        have h_b := c.val.2.isLt
        have hk := rsc_bdy_idx_lt k
        -- LHS < (L - 1) * L ≤ RHS, contradicts heq.
        have h_lhs_bound : c.val.2.val * L + c.val.1.val < (L - 1) * L := by
          calc c.val.2.val * L + c.val.1.val
              < c.val.2.val * L + L := by omega
            _ = (c.val.2.val + 1) * L := by ring
            _ ≤ (L - 1) * L := Nat.mul_le_mul_right L (by omega)
        omega
  | topBdy k => cases xf' with
    | interior c' =>
        exfalso
        simp only [xAnchorIdx_topBdy, xAnchorIdx_interior] at heq
        have hp : (c'.val.1.val + c'.val.2.val) % 2 = 1 := c'.property
        have h_a := c'.val.1.isLt
        have h_b := c'.val.2.isLt
        have hk := rsc_bdy_idx_lt k
        rcases Nat.eq_zero_or_pos c'.val.2.val with hy | hy
        · rw [hy] at heq; simp at heq; omega
        · have h_prod : L ≤ c'.val.2.val * L := by
            calc L = 1 * L := (one_mul L).symm
              _ ≤ c'.val.2.val * L := Nat.mul_le_mul_right L hy
          omega
    | topBdy k' =>
        simp only [xAnchorIdx_topBdy] at heq
        congr 1
        ext
        omega
    | bottomBdy k' =>
        exfalso
        simp only [xAnchorIdx_topBdy, xAnchorIdx_bottomBdy] at heq
        have hk := rsc_bdy_idx_lt k
        have hk' := rsc_bdy_idx_lt k'
        -- top idx = 2k < L, but bottom idx = (L-1)*L + ... ≥ (L-1)*L ≥ L.
        have h_prod : L ≤ (L - 1) * L := by
          have := Nat.mul_le_mul_right L (show 1 ≤ L - 1 from by omega)
          linarith
        omega
  | bottomBdy k => cases xf' with
    | interior c' =>
        exfalso
        simp only [xAnchorIdx_bottomBdy, xAnchorIdx_interior] at heq
        have h_a := c'.val.1.isLt
        have h_b := c'.val.2.isLt
        have hk := rsc_bdy_idx_lt k
        have h_rhs_bound : c'.val.2.val * L + c'.val.1.val < (L - 1) * L := by
          calc c'.val.2.val * L + c'.val.1.val
              < c'.val.2.val * L + L := by omega
            _ = (c'.val.2.val + 1) * L := by ring
            _ ≤ (L - 1) * L := Nat.mul_le_mul_right L (by omega)
        omega
    | topBdy k' =>
        exfalso
        simp only [xAnchorIdx_bottomBdy, xAnchorIdx_topBdy] at heq
        have hk := rsc_bdy_idx_lt k
        have hk' := rsc_bdy_idx_lt k'
        have h_prod : L ≤ (L - 1) * L := by
          have := Nat.mul_le_mul_right L (show 1 ≤ L - 1 from by omega)
          linarith
        omega
    | bottomBdy k' =>
        simp only [xAnchorIdx_bottomBdy] at heq
        congr 1
        ext
        omega

/-! ### Z-anchor properties -/

lemma zAnchor_mem_zSupport (zf : ZFaceIdx L) :
    ∃ v : VtxIdx L, v ∈ zSupport zf ∧ qubitIdx v = zAnchorIdx zf := by
  have ⟨h1, h2, h3, h4⟩ := rsc_facts (L := L)
  cases zf with
  | interior c =>
      have h_a : c.val.1.val < L := by have := c.val.1.isLt; omega
      have h_b : c.val.2.val < L := by have := c.val.2.isLt; omega
      refine ⟨(⟨c.val.1.val, h_a⟩, ⟨c.val.2.val, h_b⟩), ?_, ?_⟩
      · rw [zSupport_interior]
        unfold faceQubits cornerLo cornerHi
        simp [Finset.mem_insert]
      · simp [qubitIdx]
  | leftBdy k =>
      have hk := rsc_bdy_idx_lt k
      refine ⟨(⟨0, h3⟩, ⟨2 * k.val + 1, by omega⟩), ?_, ?_⟩
      · rw [mem_zSupport_leftBdy_iff]; exact ⟨rfl, Or.inl rfl⟩
      · simp [qubitIdx]
  | rightBdy k =>
      have hk := rsc_bdy_idx_lt k
      refine ⟨(⟨L - 1, by omega⟩, ⟨2 * k.val, by omega⟩), ?_, ?_⟩
      · rw [mem_zSupport_rightBdy_iff]; exact ⟨rfl, Or.inl rfl⟩
      · simp [qubitIdx]

lemma zAnchor_le_qubitIdx_of_mem (zf : ZFaceIdx L) (v : VtxIdx L)
    (hv : v ∈ zSupport zf) : zAnchorIdx zf ≤ qubitIdx v := by
  have ⟨h1, h2, h3, h4⟩ := rsc_facts (L := L)
  cases zf with
  | interior c =>
      rw [zSupport_interior, mem_faceQubits_iff] at hv
      obtain ⟨hx, hy⟩ := hv
      simp only [zAnchorIdx_interior, qubitIdx_def]
      rcases hx with hx | hx <;> rcases hy with hy | hy <;> nlinarith
  | leftBdy k =>
      rw [mem_zSupport_leftBdy_iff] at hv
      obtain ⟨h_x, h_y⟩ := hv
      simp only [zAnchorIdx_leftBdy, qubitIdx_def]
      rcases h_y with h | h <;> nlinarith
  | rightBdy k =>
      rw [mem_zSupport_rightBdy_iff] at hv
      obtain ⟨h_x, h_y⟩ := hv
      simp only [zAnchorIdx_rightBdy, qubitIdx_def]
      rcases h_y with h | h <;> nlinarith

lemma zAnchorIdx_injective : Function.Injective (zAnchorIdx : ZFaceIdx L → ℕ) := by
  have ⟨h1, h2, h3, h4⟩ := rsc_facts (L := L)
  intro zf zf' heq
  cases zf with
  | interior c => cases zf' with
    | interior c' =>
        simp only [zAnchorIdx_interior] at heq
        have h_a : c.val.1.val < L := by have := c.val.1.isLt; omega
        have h_a' : c'.val.1.val < L := by have := c'.val.1.isLt; omega
        have hx_eq : c.val.1.val = c'.val.1.val := by
          have hmod : (c.val.2.val * L + c.val.1.val) % L =
              (c'.val.2.val * L + c'.val.1.val) % L := by rw [heq]
          rw [Nat.add_comm (c.val.2.val * L) c.val.1.val,
              Nat.add_comm (c'.val.2.val * L) c'.val.1.val,
              Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right,
              Nat.mod_eq_of_lt h_a, Nat.mod_eq_of_lt h_a'] at hmod
          exact hmod
        have hy_eq : c.val.2.val = c'.val.2.val := by
          have : c.val.2.val * L = c'.val.2.val * L := by linarith
          exact Nat.eq_of_mul_eq_mul_right h3 this
        congr 1
        refine Subtype.ext ?_
        refine Prod.ext ?_ ?_
        · exact Fin.ext hx_eq
        · exact Fin.ext hy_eq
    | leftBdy k =>
        -- interior z (parity even): y*L + x.  leftBdy: (2k+1)*L.
        -- For equal: y*L + x = (2k+1)*L. So x = (2k+1-y)*L. With x < L,
        -- need 2k+1 = y (so x = 0). Then y odd. But interior z has x+y even,
        -- so x = 0 and y odd gives x+y odd. Contradiction.
        exfalso
        simp only [zAnchorIdx_interior, zAnchorIdx_leftBdy] at heq
        have hp : (c.val.1.val + c.val.2.val) % 2 = 0 := c.property
        have h_a := c.val.1.isLt
        have h_b := c.val.2.isLt
        have hk := rsc_bdy_idx_lt k
        -- Case: c.val.1.val = 0 or > 0.
        rcases Nat.eq_zero_or_pos c.val.1.val with hx | hx
        · -- x = 0: heq says y*L = (2k+1)*L, so y = 2k+1. Parity: x+y = 2k+1 odd. ⊥.
          rw [hx] at heq
          have : c.val.2.val = 2 * k.val + 1 := by
            have hy_eq : c.val.2.val * L = (2 * k.val + 1) * L := by linarith
            exact Nat.eq_of_mul_eq_mul_right h3 hy_eq
          omega
        · -- x ≥ 1: y*L + x ≠ (2k+1)*L (multiple of L) since x < L.
          have hmod : (c.val.2.val * L + c.val.1.val) % L = ((2 * k.val + 1) * L) % L := by
            rw [heq]
          rw [Nat.add_comm (c.val.2.val * L) c.val.1.val,
              Nat.add_mul_mod_self_right, Nat.mul_mod_left,
              Nat.mod_eq_of_lt (by omega : c.val.1.val < L)] at hmod
          omega
    | rightBdy k =>
        -- interior z: y*L + x.  rightBdy: 2k*L + (L-1).
        -- mod L: x = L-1. But x ∈ Fin (L-1), x < L-1.
        exfalso
        simp only [zAnchorIdx_interior, zAnchorIdx_rightBdy] at heq
        have h_a := c.val.1.isLt
        have hk := rsc_bdy_idx_lt k
        have hmod : (c.val.2.val * L + c.val.1.val) % L =
            (2 * k.val * L + (L - 1)) % L := by rw [heq]
        rw [Nat.add_comm (c.val.2.val * L) c.val.1.val,
            Nat.add_mul_mod_self_right, Nat.add_comm (2 * k.val * L) (L - 1),
            Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega : c.val.1.val < L),
            Nat.mod_eq_of_lt (by omega : L - 1 < L)] at hmod
        omega
  | leftBdy k => cases zf' with
    | interior c' =>
        exfalso
        simp only [zAnchorIdx_leftBdy, zAnchorIdx_interior] at heq
        have hp : (c'.val.1.val + c'.val.2.val) % 2 = 0 := c'.property
        have h_a := c'.val.1.isLt
        have h_b := c'.val.2.isLt
        have hk := rsc_bdy_idx_lt k
        rcases Nat.eq_zero_or_pos c'.val.1.val with hx | hx
        · rw [hx] at heq
          have : c'.val.2.val = 2 * k.val + 1 := by
            have hy_eq : (2 * k.val + 1) * L = c'.val.2.val * L := by linarith
            exact Nat.eq_of_mul_eq_mul_right h3 hy_eq.symm
          omega
        · have hmod : ((2 * k.val + 1) * L) % L =
              (c'.val.2.val * L + c'.val.1.val) % L := by rw [heq]
          rw [Nat.add_comm (c'.val.2.val * L) c'.val.1.val,
              Nat.add_mul_mod_self_right, Nat.mul_mod_left,
              Nat.mod_eq_of_lt (by omega : c'.val.1.val < L)] at hmod
          omega
    | leftBdy k' =>
        simp only [zAnchorIdx_leftBdy] at heq
        have : 2 * k.val + 1 = 2 * k'.val + 1 :=
          Nat.eq_of_mul_eq_mul_right h3 heq
        congr 1
        ext
        omega
    | rightBdy k' =>
        -- leftBdy: (2k+1)*L mod L = 0. rightBdy: 2k'*L + L-1 mod L = L-1 ≠ 0.
        exfalso
        simp only [zAnchorIdx_leftBdy, zAnchorIdx_rightBdy] at heq
        have hk := rsc_bdy_idx_lt k
        have hk' := rsc_bdy_idx_lt k'
        have hmod : ((2 * k.val + 1) * L) % L =
            (2 * k'.val * L + (L - 1)) % L := by rw [heq]
        rw [show ((2 * k.val + 1) * L : ℕ) = 0 + (2 * k.val + 1) * L from by ring,
            Nat.add_mul_mod_self_right, Nat.zero_mod,
            Nat.add_comm (2 * k'.val * L) (L - 1),
            Nat.add_mul_mod_self_right,
            Nat.mod_eq_of_lt (by omega : L - 1 < L)] at hmod
        omega
  | rightBdy k => cases zf' with
    | interior c' =>
        exfalso
        simp only [zAnchorIdx_rightBdy, zAnchorIdx_interior] at heq
        have h_a := c'.val.1.isLt
        have hk := rsc_bdy_idx_lt k
        have hmod : (2 * k.val * L + (L - 1)) % L =
            (c'.val.2.val * L + c'.val.1.val) % L := by rw [heq]
        rw [Nat.add_comm (2 * k.val * L) (L - 1), Nat.add_mul_mod_self_right,
            Nat.add_comm (c'.val.2.val * L) c'.val.1.val,
            Nat.add_mul_mod_self_right,
            Nat.mod_eq_of_lt (by omega : L - 1 < L),
            Nat.mod_eq_of_lt (by omega : c'.val.1.val < L)] at hmod
        omega
    | leftBdy k' =>
        exfalso
        simp only [zAnchorIdx_rightBdy, zAnchorIdx_leftBdy] at heq
        have hk := rsc_bdy_idx_lt k
        have hk' := rsc_bdy_idx_lt k'
        have hmod : (2 * k.val * L + (L - 1)) % L =
            ((2 * k'.val + 1) * L) % L := by rw [heq]
        rw [Nat.add_comm (2 * k.val * L) (L - 1), Nat.add_mul_mod_self_right,
            show ((2 * k'.val + 1) * L : ℕ) = 0 + (2 * k'.val + 1) * L from by ring,
            Nat.add_mul_mod_self_right, Nat.zero_mod,
            Nat.mod_eq_of_lt (by omega : L - 1 < L)] at hmod
        omega
    | rightBdy k' =>
        simp only [zAnchorIdx_rightBdy] at heq
        have : 2 * k.val * L = 2 * k'.val * L := by linarith
        have h_kk : 2 * k.val = 2 * k'.val := Nat.eq_of_mul_eq_mul_right h3 this
        congr 1
        ext
        omega

/-! ## ker(`rscBoundary2`) = ⊥

Combining the X-anchor properties, the indicator family of X-stabs is
linearly independent, so the boundary map `∂₂` is injective. -/

theorem rscBoundary2_injective : Function.Injective (∂₂ L) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro f hf
  simp only [LinearMap.mem_ker] at hf
  funext xf
  by_contra hne
  let S : Finset (XFaceIdx L) := Finset.univ.filter (fun xf' => f xf' ≠ 0)
  have hS_ne : S.Nonempty := ⟨xf, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩⟩
  obtain ⟨xf_min, hxf_min_mem, hxf_min_min⟩ :=
    S.exists_min_image xAnchorIdx hS_ne
  have hxf_min_ne : f xf_min ≠ 0 := (Finset.mem_filter.mp hxf_min_mem).2
  obtain ⟨v_min, hv_min_supp, hv_min_idx⟩ := xAnchor_mem_xSupport xf_min
  have hval : (∂₂ L f) v_min = f xf_min := by
    rw [rscBoundary2_apply, Finset.sum_eq_single xf_min]
    · simp [hv_min_supp]
    · intro xf' _ hne'
      by_cases hf' : f xf' = 0
      · simp [hf']
      · have hxf'_in : xf' ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf'⟩
        have hge := hxf_min_min xf' hxf'_in
        have hlt : xAnchorIdx xf_min < xAnchorIdx xf' := by
          apply lt_of_le_of_ne hge
          intro h
          exact hne' (xAnchorIdx_injective h.symm)
        have hnotin : v_min ∉ xSupport xf' := by
          intro hv_in
          have := xAnchor_le_qubitIdx_of_mem xf' v_min hv_in
          omega
        simp [hnotin]
    · intro h; exact absurd (Finset.mem_univ xf_min) h
  have : (∂₂ L f) v_min = 0 := by rw [hf]; rfl
  rw [hval] at this
  exact hxf_min_ne this

/-- The kernel of `rscBoundary2` is `⊥`. -/
theorem rscBoundary2_ker_eq_bot :
    LinearMap.ker (∂₂ L) = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  exact rscBoundary2_injective

/-- `rank(∂₂) = |XFaceIdx L|`. -/
theorem rsc_rank_boundary2 :
    dim₂ (LinearMap.range (∂₂ L)) =
      Fintype.card (XFaceIdx L) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (∂₂ L)
  rw [show dim₂ (LinearMap.ker (∂₂ L)) = 0 from ?_] at hrn
  · rw [rsc_finrank_C2] at hrn
    omega
  · rw [rscBoundary2_ker_eq_bot]
    exact finrank_bot (ZMod 2) (XFaceIdx L → ZMod 2)

/-! ## The Z-side cut map and its kernel

The map `rscZCutMap`: `s : ZFaceIdx → ZMod 2` ↦ `(v : VtxIdx) ↦ ∑_{zf ∋ v} s zf`.
This is the indicator-combination map for Z-stabilisers, dual to `rscBoundary1`
in the transpose sense. -/

/-- The Z-stab indicator combination map. -/
def rscZCutMap (L : ℕ) :
    (ZFaceIdx L → ZMod 2) →ₗ[ZMod 2] (VtxIdx L → ZMod 2) where
  toFun s v := ∑ zf : ZFaceIdx L, s zf * (if v ∈ zSupport zf then 1 else 0)
  map_add' s t := by
    funext v
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a s := by
    funext v
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- `δ⁰` is the rotated-surface Z-side cut map `rscZCutMap L` (the transpose of `∂₁`,
i.e. the coboundary `C⁰ → C¹`). Scoped: `open scoped RotatedSurfaceChain`. -/
scoped[RotatedSurfaceChain] notation "δ⁰" =>
  Quantum.Stabilizer.Lattice.RotatedSurface.rscZCutMap

@[simp] theorem rscZCutMap_apply (L : ℕ) (s : ZFaceIdx L → ZMod 2) (v : VtxIdx L) :
    δ⁰ L s v =
      ∑ zf : ZFaceIdx L, s zf * (if v ∈ zSupport zf then 1 else 0) := rfl

theorem rscZCutMap_injective : Function.Injective (δ⁰ L) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro s hs
  simp only [LinearMap.mem_ker] at hs
  funext zf
  by_contra hne
  let S : Finset (ZFaceIdx L) := Finset.univ.filter (fun zf' => s zf' ≠ 0)
  have hS_ne : S.Nonempty := ⟨zf, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩⟩
  obtain ⟨zf_min, hzf_min_mem, hzf_min_min⟩ :=
    S.exists_min_image zAnchorIdx hS_ne
  have hzf_min_ne : s zf_min ≠ 0 := (Finset.mem_filter.mp hzf_min_mem).2
  obtain ⟨v_min, hv_min_supp, hv_min_idx⟩ := zAnchor_mem_zSupport zf_min
  have hval : (δ⁰ L s) v_min = s zf_min := by
    rw [rscZCutMap_apply, Finset.sum_eq_single zf_min]
    · simp [hv_min_supp]
    · intro zf' _ hne'
      by_cases hs' : s zf' = 0
      · simp [hs']
      · have hzf'_in : zf' ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs'⟩
        have hge := hzf_min_min zf' hzf'_in
        have hlt : zAnchorIdx zf_min < zAnchorIdx zf' := by
          apply lt_of_le_of_ne hge
          intro h
          exact hne' (zAnchorIdx_injective h.symm)
        have hnotin : v_min ∉ zSupport zf' := by
          intro hv_in
          have := zAnchor_le_qubitIdx_of_mem zf' v_min hv_in
          omega
        simp [hnotin]
    · intro h; exact absurd (Finset.mem_univ zf_min) h
  have : (δ⁰ L s) v_min = 0 := by rw [hs]; rfl
  rw [hval] at this
  exact hzf_min_ne this

theorem rscZCutMap_ker_eq_bot : LinearMap.ker (δ⁰ L) = ⊥ := by
  rw [LinearMap.ker_eq_bot]; exact rscZCutMap_injective

/-- `rank(rscZCutMap) = |ZFaceIdx L|`. -/
theorem rsc_rank_zCutMap :
    dim₂ (LinearMap.range (δ⁰ L)) =
      Fintype.card (ZFaceIdx L) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (δ⁰ L)
  rw [show dim₂ (LinearMap.ker (δ⁰ L)) = 0 from ?_] at hrn
  · rw [rsc_finrank_C0] at hrn
    omega
  · rw [rscZCutMap_ker_eq_bot]
    exact finrank_bot (ZMod 2) (ZFaceIdx L → ZMod 2)

/-! ## Transpose pairing of `rscBoundary1` and `rscZCutMap`

The standard pairing `⟨∂₁ c, s⟩ = ⟨c, rscZCutMap s⟩` identifies the two
maps as mutual transposes, so they share the same rank. -/

theorem rscBoundary1_rscZCutMap_transpose
    (c : VtxIdx L → ZMod 2) (s : ZFaceIdx L → ZMod 2) :
    ∑ zf : ZFaceIdx L, ∂₁ L c zf * s zf =
      ∑ v : VtxIdx L, c v * δ⁰ L s v := by
  simp only [rscBoundary1_apply, rscZCutMap_apply]
  -- Helper: ∑ v ∈ zSupport zf, c v * s zf = ∑ v, if v ∈ zSupport zf then c v * s zf else 0.
  have hsplit : ∀ zf : ZFaceIdx L,
      (∑ v ∈ zSupport zf, c v * s zf) =
        ∑ v : VtxIdx L, (if v ∈ zSupport zf then c v * s zf else 0) := by
    intro zf
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext v
    simp
  -- Convert both to a common form: ∑ v, ∑ zf, (if v ∈ zSupport zf then c v * s zf else 0).
  trans (∑ v : VtxIdx L, ∑ zf : ZFaceIdx L,
      (if v ∈ zSupport zf then c v * s zf else (0 : ZMod 2)))
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro zf _
    rw [Finset.sum_mul, hsplit]
  · refine Finset.sum_congr rfl ?_
    intro v _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro zf _
    split_ifs <;> ring

/-! ## Rank equality via the Z-stab incidence matrix

`rscBoundary1` and `rscZCutMap` are mutual transposes (the indicator
matrix of Z-stabs).  Using `Matrix.rank_transpose` we get the rank
equality `rank ∂₁ = rank rscZCutMap`. -/

/-- The Z-stab incidence matrix: entry `(zf, v)` is `1` iff `v ∈ zSupport zf`. -/
def stabZMatrix (L : ℕ) : Matrix (ZFaceIdx L) (VtxIdx L) (ZMod 2) :=
  fun zf v => if v ∈ zSupport zf then 1 else 0

lemma rscBoundary1_eq_mulVecLin :
    ∂₁ L = (stabZMatrix L).mulVecLin := by
  apply LinearMap.ext
  intro c
  funext zf
  rw [rscBoundary1_apply, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
  simp only [stabZMatrix]
  -- Goal: ∑ v ∈ zSupport zf, c v = ∑ v, (if v ∈ zSupport zf then 1 else 0) * c v
  rw [show (fun v : VtxIdx L => (if v ∈ zSupport zf then (1 : ZMod 2) else 0) * c v) =
        (fun v => if v ∈ zSupport zf then c v else 0) from
    funext fun v => by split_ifs <;> simp]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext v; simp

lemma rscZCutMap_eq_transpose_mulVecLin :
    δ⁰ L = (stabZMatrix L).transpose.mulVecLin := by
  apply LinearMap.ext
  intro s
  funext v
  rw [rscZCutMap_apply, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
  simp only [stabZMatrix, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro zf _
  ring

/-- `rank(∂₁) = rank(rscZCutMap)` via matrix transpose-rank. -/
theorem rsc_rank_boundary1_eq_rank_zCutMap :
    dim₂ (LinearMap.range (∂₁ L)) =
      dim₂ (LinearMap.range (δ⁰ L)) := by
  rw [rscBoundary1_eq_mulVecLin, rscZCutMap_eq_transpose_mulVecLin]
  show Matrix.rank (stabZMatrix L) = Matrix.rank (stabZMatrix L).transpose
  rw [Matrix.rank_transpose]

/-- `rank(∂₁) = |ZFaceIdx L|`. -/
theorem rsc_rank_boundary1 :
    dim₂ (LinearMap.range (∂₁ L)) =
      Fintype.card (ZFaceIdx L) := by
  rw [rsc_rank_boundary1_eq_rank_zCutMap, rsc_rank_zCutMap]

/-! ## The dim H₁ = 1 theorem -/

/-- `dim(cycles) = L * L − |ZFaceIdx L|`. -/
theorem rsc_finrank_cycles :
    dim₂ (Z₁ L) =
      L * L - Fintype.card (ZFaceIdx L) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (∂₁ L)
  rw [rsc_finrank_C1, rsc_rank_boundary1] at hrn
  -- finrank C1 (= L*L) = rank(∂₁) + dim ker = |ZFaceIdx| + dim ker
  -- dim Z₁ = dim ker (rscBoundary1) = L*L - |ZFaceIdx|
  have hrange_le : Fintype.card (ZFaceIdx L) ≤ L * L := by
    have := card_ZFaceIdx_add_card_XFaceIdx (L := L)
    have hLpos : 1 ≤ L := by
      rcases (Fact.out : Odd L) with ⟨m, hm⟩
      omega
    have hLL : 1 ≤ L * L := by nlinarith
    omega
  -- rscCycles = ker rscBoundary1
  show dim₂ (LinearMap.ker (∂₁ L)) = _
  omega

/-- `dim(boundaries) = |XFaceIdx L|`. -/
theorem rsc_finrank_boundaries :
    dim₂ (B₁ L) = Fintype.card (XFaceIdx L) := by
  show dim₂ (LinearMap.range (∂₂ L)) = _
  exact rsc_rank_boundary2

/-- `dim(H₁) = 1` for the rotated surface code. -/
theorem rsc_finrank_H1_eq_one :
    dim₂ (H₁ L) = 1 := by
  -- The generic quotient-dimension formula on the HomologicalCode side.
  have hquot := (rotatedSurfaceHomologicalCode L).finrank_H1_eq_cycles_sub_boundaries
  -- Convert from generic cycles/boundaries to lattice-specific via the rfl-bridges.
  have hC : dim₂ ((rotatedSurfaceHomologicalCode L).cycles) =
      L * L - Fintype.card (ZFaceIdx L) := by
    show dim₂ (Z₁ L) = _
    exact rsc_finrank_cycles
  have hB : dim₂ ((rotatedSurfaceHomologicalCode L).boundaries) =
      Fintype.card (XFaceIdx L) := by
    show dim₂ (B₁ L) = _
    exact rsc_finrank_boundaries
  rw [hC, hB] at hquot
  -- The two finrank forms (lattice vs generic) agree by defeq.
  have h_targ : dim₂ (H₁ L) =
      @Module.finrank (ZMod 2) (rotatedSurfaceHomologicalCode L).H1 _
        (Submodule.Quotient.addCommGroup
          (rotatedSurfaceHomologicalCode L).boundarySubmoduleInCycles).toAddCommMonoid
        (Submodule.Quotient.module
          (rotatedSurfaceHomologicalCode L).boundarySubmoduleInCycles) := rfl
  rw [h_targ, hquot]
  have hcard := card_ZFaceIdx_add_card_XFaceIdx (L := L)
  have hLpos : 1 ≤ L := by
    rcases (Fact.out : Odd L) with ⟨m, hm⟩
    omega
  have hLL : 1 ≤ L * L := by nlinarith
  omega

end RotatedSurface
end Lattice
end Stabilizer
end Quantum
