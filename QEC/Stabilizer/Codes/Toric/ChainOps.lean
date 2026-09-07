import Mathlib.Tactic
import QEC.Stabilizer.Codes.Toric.OperatorChains
import QEC.Stabilizer.Codes.Toric.H1Dimension
import QEC.Stabilizer.Codes.Toric.CodeN

/-!
# Toric chain-operator machinery (below the iff layer)

This file collects the lattice-specific chain ↔ Pauli-element bridges that the
generic `HomologicalCode`-instance for the toric code needs. Placing them here
(between `ToricH1Dimension` / `ToricCodeN` and the X/Z logical correspondence
iff files) avoids a circular import:

  `ToricChainComplex` imports this file → defines `toricHomologicalCode` and the
  generator-set bridges → `ToricLogicalCorrespondenceX/Z` import
  `ToricChainComplex` and delegate their iff theorems to the generic
  `HomologicalCode` correspondence.

Specifically, this file contains:

* `toricZOperatorOfChain` — Z-flavored mirror of `toricXOperatorOfChain`.
* `chainOfZOperator` and the round-trip lemma `chainOfZOperator_*`.
* `toricXOperatorOfChain_zero` / `_add` and Z analogues.
* `toricXOperatorOfChain_boundary_singleFace` — identifies the encoded chain
  `toricBoundary2 (singleFace (x, y))` with the lattice `faceStab L x y`.
* `toricZOperatorOfChain_cutMap_singleVtx` — same for the vertex side.
-/

namespace Quantum
namespace Stabilizer
namespace Lattice

open scoped BigOperators
open scoped ToricChain

-- ---------------------------------------------------------------------------
-- Z-operator encoding (mirror of `toricXOperatorOfChain`)
-- ---------------------------------------------------------------------------

/-- Build a Z-type Pauli element from a 1-chain (dual to
`toricXOperatorOfChain`). -/
def toricZOperatorOfChain (L : ℕ) (c : C1 L) :
    NQubitPauliGroupElement (toricNumQubits L) :=
  ⟨0, fun q =>
    if ∃ e : EdgeIdx L, edgeToQubitIdx L e = q ∧ c e = 1
    then PauliOperator.Z else PauliOperator.I⟩

/-- Recover a 1-chain from a Z-type Pauli element. -/
def chainOfZOperator (L : ℕ) (g : NQubitPauliGroupElement (toricNumQubits L)) : C1 L :=
  fun e => if g.operators (edgeToQubitIdx L e) = PauliOperator.Z then 1 else 0

/-- Roundtrip: chain → Z-operator → chain. -/
theorem chainOfZOperator_toricZOperatorOfChain (L : ℕ) (c : C1 L) :
    chainOfZOperator L (toricZOperatorOfChain L c) = c := by
  by_cases hL : 0 < L
  · letI : Fact (0 < L) := ⟨hL⟩
    ext e
    by_cases hce : c e = 1
    · have hex : ∃ e' : EdgeIdx L, edgeToQubitIdx L e' = edgeToQubitIdx L e ∧ c e' = 1 :=
        ⟨e, rfl, hce⟩
      simp [chainOfZOperator, toricZOperatorOfChain, hex, hce]
    · have hnot :
          ¬ ∃ e' : EdgeIdx L, edgeToQubitIdx L e' = edgeToQubitIdx L e ∧ c e' = 1 := by
        intro hx
        rcases hx with ⟨e', heq, he1⟩
        exact hce ((edgeToQubitIdx_injective (L := L) heq) ▸ he1)
      have hce0 : c e = 0 := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp
            (Nat.le_of_lt_succ (c e).val_lt) with h0 | h1
        · calc c e = ((c e).val : ZMod 2) := (ZMod.natCast_zmod_val (c e)).symm
               _ = 0 := by simp [h0]
        · exact absurd (by calc
              c e = ((c e).val : ZMod 2) := (ZMod.natCast_zmod_val (c e)).symm
              _ = 1 := by simp [h1]) hce
      simp [chainOfZOperator, toricZOperatorOfChain, hnot, hce0]
  · have hL0 : L = 0 := Nat.eq_zero_of_not_pos hL
    subst hL0
    ext e
    cases e with
    | h x y => exact (Fin.elim0 x)
    | v x y => exact (Fin.elim0 x)

/-- Support membership of `toricZOperatorOfChain` at an indexed edge qubit. -/
lemma mem_support_toricZOperatorOfChain_edgeToQubitIdx_iff
    (L : ℕ) [Fact (0 < L)] (c : C1 L) (e : EdgeIdx L) :
    edgeToQubitIdx L e ∈ (toricZOperatorOfChain L c).operators.support ↔ c e = 1 := by
  constructor
  · intro hmem
    by_contra hne
    have hnot :
        ¬ ∃ e' : EdgeIdx L, edgeToQubitIdx L e' = edgeToQubitIdx L e ∧ c e' = 1 := by
      intro hex
      rcases hex with ⟨e', heq, he1⟩
      have he' : e' = e := edgeToQubitIdx_injective L heq
      exact hne (he' ▸ he1)
    have hI : (toricZOperatorOfChain L c).operators (edgeToQubitIdx L e) = PauliOperator.I := by
      simp [toricZOperatorOfChain, hnot]
    have hneqI : (toricZOperatorOfChain L c).operators (edgeToQubitIdx L e) ≠ PauliOperator.I := by
      simpa [NQubitPauliOperator.support] using hmem
    exact hneqI hI
  · intro he1
    have hex : ∃ e' : EdgeIdx L, edgeToQubitIdx L e' = edgeToQubitIdx L e ∧ c e' = 1 :=
      ⟨e, rfl, he1⟩
    have hZ : (toricZOperatorOfChain L c).operators (edgeToQubitIdx L e) = PauliOperator.Z := by
      simp [toricZOperatorOfChain, hex]
    simp [NQubitPauliOperator.support, hZ]

/-- The Z-operator-of-chain at qubit `q` is `Z` if some edge mapping to `q` has
`c e = 1`, else `I`. -/
lemma toricZOperatorOfChain_op_at (L : ℕ) (c : C1 L) (q : Fin (toricNumQubits L)) :
    (toricZOperatorOfChain L c).operators q =
      if ∃ e, edgeToQubitIdx L e = q ∧ c e = 1
        then PauliOperator.Z else PauliOperator.I := rfl

-- ---------------------------------------------------------------------------
-- Homomorphism lemmas: `_zero` and `_add` for both X and Z
-- ---------------------------------------------------------------------------

/-- `toricXOperatorOfChain` sends the zero chain to the identity element. -/
lemma toricXOperatorOfChain_zero (L : ℕ) :
    toricXOperatorOfChain L 0 = 1 := by
  unfold toricXOperatorOfChain
  aesop

set_option maxHeartbeats 1000000 in
-- This pointwise-to-global proof unfolds many dependent equalities and case splits.
/-- `toricXOperatorOfChain` maps chain addition to Pauli multiplication. -/
lemma toricXOperatorOfChain_add (L : ℕ) (c c' : C1 L) :
    toricXOperatorOfChain L (c + c') =
      toricXOperatorOfChain L c * toricXOperatorOfChain L c' := by
  simp [toricXOperatorOfChain] at *
  simp +decide [NQubitPauliGroupElement.mul, NQubitPauliGroupElement.mulOp]
  constructor
  · rw [Finset.sum_eq_zero]; aesop
  · ext q
    split_ifs <;> simp_all +decide [Fin.ext_iff, ZMod]
    · rename_i h₁ h₂ h₃
      obtain ⟨e₁, he₁, he₂⟩ := h₁
      obtain ⟨e₂, he₃, he₄⟩ := h₂
      obtain ⟨e₃, he₅, he₆⟩ := h₃
      have h_eq : e₁ = e₂ ∧ e₂ = e₃ := by
        have h_eq :
            ∀ e₁ e₂ : EdgeIdx L, edgeToQubitIdx L e₁ = edgeToQubitIdx L e₂ → e₁ = e₂ := by
          intros e₁ e₂ h_eq
          have h_eq' : edgeToQubitIdx L e₁ = edgeToQubitIdx L e₂ := h_eq
          simp [edgeToQubitIdx] at h_eq'
          rcases e₁ with (_ | _) <;> rcases e₂ with (_ | _) <;> norm_num at h_eq' ⊢
          · rename_i a b c d
            have h_eq' : b = d := by
              exact Fin.ext (by nlinarith [Fin.is_lt a, Fin.is_lt b, Fin.is_lt c, Fin.is_lt d])
            aesop
          · rename_i a b c d
            exact absurd h_eq'
              (by nlinarith only [Fin.is_lt a, Fin.is_lt b, Fin.is_lt c, Fin.is_lt d])
          · rename_i a b c d
            exact absurd h_eq'
              (by nlinarith [Fin.is_lt a, Fin.is_lt b, Fin.is_lt c, Fin.is_lt d])
          · rename_i a b c d
            have h_eq' : b = d := by
              exact Fin.ext (by nlinarith [Fin.is_lt a, Fin.is_lt b, Fin.is_lt c, Fin.is_lt d])
            aesop
        exact ⟨h_eq e₁ e₂ (Fin.ext <| by aesop), h_eq e₂ e₃ (Fin.ext <| by aesop)⟩
      grind
    · grind
    · grind
    · grind

/-- `toricZOperatorOfChain` maps the zero chain to the identity element. -/
lemma toricZOperatorOfChain_zero (L : ℕ) :
    toricZOperatorOfChain L 0 = 1 := by
  unfold toricZOperatorOfChain
  aesop

set_option maxHeartbeats 1000000 in
-- maxHeartbeats bumped: chain → Pauli homomorphism unfolding produces a goal with
-- per-qubit case splits over `PauliOperator.mulOp`.
/-- `toricZOperatorOfChain` maps chain addition to Pauli multiplication. -/
lemma toricZOperatorOfChain_add (L : ℕ) (c c' : C1 L) :
    toricZOperatorOfChain L (c + c') =
      toricZOperatorOfChain L c * toricZOperatorOfChain L c' := by
  simp [toricZOperatorOfChain] at *
  simp +decide [NQubitPauliGroupElement.mul, NQubitPauliGroupElement.mulOp]
  constructor
  · rw [Finset.sum_eq_zero]; aesop
  · ext q
    split_ifs <;> simp_all +decide [Fin.ext_iff, ZMod]
    · rename_i h₁ h₂ h₃
      obtain ⟨e₁, he₁, he₂⟩ := h₁
      obtain ⟨e₂, he₃, he₄⟩ := h₂
      obtain ⟨e₃, he₅, he₆⟩ := h₃
      have h_eq : e₁ = e₂ ∧ e₂ = e₃ := by
        have h_eq :
            ∀ e₁ e₂ : EdgeIdx L, edgeToQubitIdx L e₁ = edgeToQubitIdx L e₂ → e₁ = e₂ := by
          intros e₁ e₂ h_eq
          have h_eq' : edgeToQubitIdx L e₁ = edgeToQubitIdx L e₂ := h_eq
          simp [edgeToQubitIdx] at h_eq'
          rcases e₁ with (_ | _) <;> rcases e₂ with (_ | _) <;> norm_num at h_eq' ⊢
          · rename_i a b c d
            have h_eq' : b = d := by
              exact Fin.ext (by nlinarith [Fin.is_lt a, Fin.is_lt b, Fin.is_lt c, Fin.is_lt d])
            aesop
          · rename_i a b c d
            exact absurd h_eq'
              (by nlinarith only [Fin.is_lt a, Fin.is_lt b, Fin.is_lt c, Fin.is_lt d])
          · rename_i a b c d
            exact absurd h_eq'
              (by nlinarith [Fin.is_lt a, Fin.is_lt b, Fin.is_lt c, Fin.is_lt d])
          · rename_i a b c d
            have h_eq' : b = d := by
              exact Fin.ext (by nlinarith [Fin.is_lt a, Fin.is_lt b, Fin.is_lt c, Fin.is_lt d])
            aesop
        exact ⟨h_eq e₁ e₂ (Fin.ext <| by aesop), h_eq e₂ e₃ (Fin.ext <| by aesop)⟩
      grind
    · grind
    · grind
    · grind

-- ---------------------------------------------------------------------------
-- Generator bridges: face stab via X-chain on ∂₂(singleFace),
-- vertex stab via Z-chain on cutMap(singleVtx).
-- ---------------------------------------------------------------------------

/-- `toricXOperatorOfChain` maps the boundary of a single face to the
corresponding face stabilizer. -/
lemma toricXOperatorOfChain_boundary_singleFace (L : ℕ) [Fact (2 ≤ L)] (x y : Fin L) :
    toricXOperatorOfChain L (∂₂ (L := L) (singleFace (x, y))) =
      StabilizerGroup.ToricCodeN.faceStab L x y := by
  unfold toricXOperatorOfChain StabilizerGroup.ToricCodeN.faceStab
  congr with q
  split_ifs <;> simp_all +decide [NQubitPauliOperator.set]
  · rename_i h
    obtain ⟨e, rfl, he⟩ := h
    rcases e with (_ | _) <;> simp_all +decide [toricBoundary2, singleFace]
    · unfold edgeToQubitIdx; split_ifs at he <;> simp_all +decide [Fin.ext_iff]
    · split_ifs at he <;> simp_all +decide [Fin.ext_iff, StabilizerGroup.ToricCodeN.next]
  · split_ifs <;> simp_all +decide [toricNumQubits]
    · rename_i h₁ h₂
      contrapose! h₁
      use EdgeIdx.v (StabilizerGroup.ToricCodeN.next L x) y
      unfold edgeToQubitIdx; simp +decide [StabilizerGroup.ToricCodeN.next]
      constructor
      · exact rfl
      · exact next_ne_self L x
    · rename_i h₁ h₂ h₃
      contrapose! h₁
      use EdgeIdx.v x y
      unfold edgeToQubitIdx; simp +decide [StabilizerGroup.ToricCodeN.vEdge]
      grind
    · rename_i h₁ h₂ h₃ h₄
      contrapose! h₁
      use EdgeIdx.h x (StabilizerGroup.ToricCodeN.next L y); simp +decide [edgeToQubitIdx]
      unfold StabilizerGroup.ToricCodeN.next; simp +decide [Fin.ext_iff]
      by_cases hy : y.val = L - 1
      · rcases L with (_ | _ | L) <;> simp_all +decide
        exact absurd (Fact.out (p := 2 ≤ 0 + 1)) (by decide)
      · rw [Nat.mod_eq_of_lt] <;> omega
    · rename_i h₁ h₂ h₃ h₄ h₅
      contrapose! h₁
      use EdgeIdx.h x y
      unfold toricBoundary2; simp +decide [singleFace]
      exact
        Decidable.not_imp_iff_and_not.mp fun a ↦
          h₄ (congrArg (StabilizerGroup.ToricCodeN.hEdge L x) (a rfl))
    · unfold NQubitPauliOperator.identity; aesop

set_option maxHeartbeats 800000 in
-- maxHeartbeats bumped: equality on n-qubit Pauli elements after unfolding the cut map
-- and the singleVtx indicator across 2·L² edges.
/-- `toricZOperatorOfChain` applied to `toricVertexCutMap (singleVtx (xv, yv))`
    equals the vertex stabilizer at `(xv, yv)`. -/
lemma toricZOperatorOfChain_cutMap_singleVtx (L : ℕ) [Fact (2 ≤ L)]
    (xv yv : Fin L) :
    toricZOperatorOfChain L (δ⁰ (L := L) (singleVtx (xv, yv))) =
      StabilizerGroup.ToricCodeN.vertexStab L xv yv := by
  have hL0 : 0 < L := Nat.lt_of_lt_of_le (by decide : 0 < 2) (Fact.out : 2 ≤ L)
  haveI : Fact (0 < L) := ⟨hL0⟩
  unfold toricZOperatorOfChain StabilizerGroup.ToricCodeN.vertexStab
  congr with q
  split_ifs <;> simp_all +decide [NQubitPauliOperator.set]
  · rename_i h
    obtain ⟨e, rfl, he⟩ := h
    rcases e with ⟨ex, ey⟩ | ⟨ex, ey⟩
    · -- h-edge case
      simp only [toricVertexCutMap] at he
      have hxL : (xv : ℕ) < L := xv.isLt
      have hyL : (yv : ℕ) < L := yv.isLt
      have hexL : (ex : ℕ) < L := ex.isLt
      have heyL : (ey : ℕ) < L := ey.isLt
      by_cases h1 : (ex, ey) = (xv, yv)
      · obtain ⟨hex, hey⟩ := Prod.mk_inj.mp h1
        subst hex; subst hey
        unfold edgeToQubitIdx
        simp_all +decide [Fin.ext_iff, StabilizerGroup.ToricCodeN.hEdge,
          StabilizerGroup.ToricCodeN.vEdge, StabilizerGroup.ToricCodeN.prev,
          NQubitPauliOperator.identity]
      · by_cases h2 : (StabilizerGroup.ToricCodeN.next L ex, ey) = (xv, yv)
        · obtain ⟨hnex, hey⟩ := Prod.mk_inj.mp h2
          subst hey
          have hex_eq : ex = StabilizerGroup.ToricCodeN.prev L xv :=
            (Stabilizer.Lattice.eq_prev_iff_next_eq L ex xv).mpr hnex
          subst hex_eq
          unfold edgeToQubitIdx
          simp_all +decide [Fin.ext_iff, StabilizerGroup.ToricCodeN.hEdge,
            StabilizerGroup.ToricCodeN.vEdge, StabilizerGroup.ToricCodeN.prev,
            NQubitPauliOperator.identity]
        · exfalso
          simp [h1, h2] at he
    · -- v-edge case
      simp only [toricVertexCutMap] at he
      have hxL : (xv : ℕ) < L := xv.isLt
      have hyL : (yv : ℕ) < L := yv.isLt
      have hexL : (ex : ℕ) < L := ex.isLt
      have heyL : (ey : ℕ) < L := ey.isLt
      by_cases h1 : (ex, ey) = (xv, yv)
      · obtain ⟨hex, hey⟩ := Prod.mk_inj.mp h1
        subst hex; subst hey
        unfold edgeToQubitIdx
        simp_all +decide [Fin.ext_iff, StabilizerGroup.ToricCodeN.hEdge,
          StabilizerGroup.ToricCodeN.vEdge, StabilizerGroup.ToricCodeN.prev,
          NQubitPauliOperator.identity]
      · by_cases h2 : (ex, StabilizerGroup.ToricCodeN.next L ey) = (xv, yv)
        · obtain ⟨hex, hney⟩ := Prod.mk_inj.mp h2
          subst hex
          have hey_eq : ey = StabilizerGroup.ToricCodeN.prev L yv :=
            (Stabilizer.Lattice.eq_prev_iff_next_eq L ey yv).mpr hney
          subst hey_eq
          unfold edgeToQubitIdx
          simp_all +decide [Fin.ext_iff, StabilizerGroup.ToricCodeN.hEdge,
            StabilizerGroup.ToricCodeN.vEdge, StabilizerGroup.ToricCodeN.prev,
            NQubitPauliOperator.identity]
        · exfalso
          simp [h1, h2] at he
  · -- neg case: q not in support of cutMap(singleVtx), must show vertexStab q = I
    split_ifs <;> simp_all +decide [toricNumQubits]
    · rename_i h₁ h₂
      contrapose! h₁
      refine ⟨EdgeIdx.v xv (StabilizerGroup.ToricCodeN.prev L yv), ?_, ?_⟩
      · rfl
      · have hne : (StabilizerGroup.ToricCodeN.prev L yv) ≠ yv :=
          Stabilizer.Lattice.prev_ne_self L yv
        simp [toricVertexCutMap, singleVtx, StabilizerGroup.ToricCodeN.prev,
          Stabilizer.Lattice.next_prev, hne]
    · rename_i h₁ h₂ h₃
      contrapose! h₁
      refine ⟨EdgeIdx.v xv yv, ?_, ?_⟩
      · rfl
      · have hne : StabilizerGroup.ToricCodeN.next L yv ≠ yv :=
          Stabilizer.Lattice.next_ne_self L yv
        simp [toricVertexCutMap, singleVtx, hne]
    · rename_i h₁ h₂ h₃ h₄
      contrapose! h₁
      refine ⟨EdgeIdx.h (StabilizerGroup.ToricCodeN.prev L xv) yv, ?_, ?_⟩
      · rfl
      · have hne : (StabilizerGroup.ToricCodeN.prev L xv) ≠ xv :=
          Stabilizer.Lattice.prev_ne_self L xv
        simp [toricVertexCutMap, singleVtx, StabilizerGroup.ToricCodeN.prev,
          Stabilizer.Lattice.next_prev, hne]
    · rename_i h₁ h₂ h₃ h₄ h₅
      contrapose! h₁
      refine ⟨EdgeIdx.h xv yv, ?_, ?_⟩
      · rfl
      · have hne : StabilizerGroup.ToricCodeN.next L xv ≠ xv :=
          Stabilizer.Lattice.next_ne_self L xv
        simp [toricVertexCutMap, singleVtx, hne]
    · unfold NQubitPauliOperator.identity; aesop

end Lattice
end Stabilizer
end Quantum
