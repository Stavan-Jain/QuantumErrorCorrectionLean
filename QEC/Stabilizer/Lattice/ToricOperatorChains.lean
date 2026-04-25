import Mathlib.Tactic
import QEC.Stabilizer.Lattice.ToricChains
import QEC.Stabilizer.Lattice.GridIndexing
import QEC.Stabilizer.PauliGroup
import QEC.Stabilizer.PauliGroup.NQubitOperator

namespace Quantum
namespace Stabilizer
namespace Lattice

open scoped BigOperators

/-- Number of edge qubits for an `L × L` toric lattice. -/
abbrev toricNumQubits (L : ℕ) : ℕ := 2 * L * L

/-- Encode an edge index as the corresponding qubit index in `[0, 2L²)`. -/
def edgeToQubitIdx (L : ℕ) : EdgeIdx L → Fin (toricNumQubits L)
  | EdgeIdx.h x y =>
      ⟨y.val * L + x.val, by
        have hx := x.isLt
        have hy := y.isLt
        dsimp [toricNumQubits]
        nlinarith⟩
  | EdgeIdx.v x y =>
      ⟨L * L + y.val * L + x.val, by
        have hx := x.isLt
        have hy := y.isLt
        dsimp [toricNumQubits]
        nlinarith⟩

@[simp] lemma edgeToQubitIdx_h_val (L : ℕ) (x y : Fin L) :
    (edgeToQubitIdx L (EdgeIdx.h x y)).val = y.val * L + x.val := rfl

@[simp] lemma edgeToQubitIdx_v_val (L : ℕ) (x y : Fin L) :
    (edgeToQubitIdx L (EdgeIdx.v x y)).val = L * L + y.val * L + x.val := rfl

/-- Horizontal edge encodings land below `L²`. -/
lemma edgeToQubitIdx_h_lt_sq (L : ℕ) (x y : Fin L) :
    (edgeToQubitIdx L (EdgeIdx.h x y)).val < L * L := by
  simp [edgeToQubitIdx_h_val]
  have hx := x.isLt
  have hy := y.isLt
  nlinarith

/-- Vertical edge encodings land at or above `L²`. -/
lemma edgeToQubitIdx_v_ge_sq (L : ℕ) (x y : Fin L) :
    L * L ≤ (edgeToQubitIdx L (EdgeIdx.v x y)).val := by
  simp [edgeToQubitIdx_v_val]
  omega

/-- Edge-to-qubit encoding is injective for positive lattice size. -/
lemma edgeToQubitIdx_injective (L : ℕ) [Fact (0 < L)] :
    Function.Injective (edgeToQubitIdx L) := by
  intro e₁ e₂ h
  cases e₁ with
  | h x₁ y₁ =>
      cases e₂ with
      | h x₂ y₂ =>
          have hp : (x₁, y₁) = (x₂, y₂) := by
            apply rowMajor_injective (L := L)
            exact congrArg Fin.val h
          cases hp
          rfl
      | v x₂ y₂ =>
          exfalso
          exact fin_ne_of_val_lt_offset_le
            (edgeToQubitIdx_h_lt_sq L x₁ y₁) (edgeToQubitIdx_v_ge_sq L x₂ y₂) h
  | v x₁ y₁ =>
      cases e₂ with
      | h x₂ y₂ =>
          exfalso
          exact fin_ne_of_val_lt_offset_le
            (edgeToQubitIdx_h_lt_sq L x₂ y₂) (edgeToQubitIdx_v_ge_sq L x₁ y₁) h.symm
      | v x₂ y₂ =>
          have hsum : y₁.val * L + x₁.val = y₂.val * L + x₂.val := by
            have hval : (edgeToQubitIdx L (EdgeIdx.v x₁ y₁)).val =
                (edgeToQubitIdx L (EdgeIdx.v x₂ y₂)).val := congrArg Fin.val h
            have hval' : L * L + (y₁.val * L + x₁.val) = L * L + (y₂.val * L + x₂.val) := by
              simpa [edgeToQubitIdx_v_val, Nat.add_assoc, Nat.add_left_comm,
              Nat.add_comm] using hval
            exact Nat.add_left_cancel hval'
          have hp : (x₁, y₁) = (x₂, y₂) := (rowMajor_injective (L := L)) hsum
          cases hp
          rfl

/-- Build an X-type Pauli group element from a 1-chain (support encoding). -/
def toricXOperatorOfChain (L : ℕ) (c : C1 L) :
    NQubitPauliGroupElement (toricNumQubits L) :=
  ⟨0, fun q =>
    if ∃ e : EdgeIdx L, edgeToQubitIdx L e = q ∧ c e = 1
    then PauliOperator.X else PauliOperator.I⟩

/-- Recover an edge 1-chain from an X-support Pauli element. -/
def chainOfXOperator (L : ℕ) (g : NQubitPauliGroupElement (toricNumQubits L)) : C1 L :=
  fun e => if g.operators (edgeToQubitIdx L e) = PauliOperator.X then 1 else 0

/-- Roundtrip (`chain -> operator -> chain`) on this encoding. -/
theorem chainOfXOperator_toricXOperatorOfChain (L : ℕ) (c : C1 L) :
    chainOfXOperator L (toricXOperatorOfChain L c) = c := by
  by_cases hL : 0 < L
  · letI : Fact (0 < L) := ⟨hL⟩
    ext e
    by_cases hce : c e = 1
    · have hex : ∃ e' : EdgeIdx L, edgeToQubitIdx L e' = edgeToQubitIdx L e ∧ c e' = 1 := by
        exact ⟨e, rfl, hce⟩
      simp [chainOfXOperator, toricXOperatorOfChain, hex, hce]
    · have hnot :
          ¬ ∃ e' : EdgeIdx L, edgeToQubitIdx L e' = edgeToQubitIdx L e ∧ c e' = 1 := by
        intro hx
        rcases hx with ⟨e', heq, he1⟩
        have he' : e' = e := edgeToQubitIdx_injective (L := L) heq
        exact hce (he' ▸ he1)
      have hce0 : c e = 0 := by
        have hvalle : (c e).val ≤ 1 := Nat.le_of_lt_succ (c e).val_lt
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hvalle with h0 | h1
        · calc
            c e = ((c e).val : ZMod 2) := by symm; exact ZMod.natCast_zmod_val (c e)
            _ = 0 := by simp [h0]
        · exfalso
          exact hce (by
            calc
              c e = ((c e).val : ZMod 2) := by symm; exact ZMod.natCast_zmod_val (c e)
              _ = 1 := by simp [h1])
      simp [chainOfXOperator, toricXOperatorOfChain, hnot, hce0]
  · have hL0 : L = 0 := Nat.eq_zero_of_not_pos hL
    subst hL0
    ext e
    cases e with
    | h x y => exact (Fin.elim0 x)
    | v x y => exact (Fin.elim0 x)

/-- Support/weight compatibility placeholder for future distance proofs. -/
theorem edgeWeight_eq_operatorSupportWeight (L : ℕ) (c : C1 L) :
    edgeWeight (L := L) c =
      (NQubitPauliOperator.support (toricXOperatorOfChain L c).operators).card := by
  by_cases hL : 0 < L
  · letI : Fact (0 < L) := ⟨hL⟩
    have hidxinj : Function.Injective (edgeToQubitIdx L) := edgeToQubitIdx_injective (L := L)
    have hsupport_eq :
        NQubitPauliOperator.support (toricXOperatorOfChain L c).operators =
          (edgeSupport (L := L) c).image (edgeToQubitIdx L) := by
      ext q
      constructor
      · intro hq
        have hneq : (toricXOperatorOfChain L c).operators q ≠ PauliOperator.I := by
          simpa [NQubitPauliOperator.support] using hq
        have hex : ∃ e : EdgeIdx L, edgeToQubitIdx L e = q ∧ c e = 1 := by
          by_contra hnot
          apply hneq
          simp [toricXOperatorOfChain, hnot]
        rcases hex with ⟨e, heq, he1⟩
        refine Finset.mem_image.mpr ?_
        refine ⟨e, ?_, heq⟩
        simp [edgeSupport, he1]
      · intro hq
        rcases Finset.mem_image.mp hq with ⟨e, heSupp, heq⟩
        have hce_nonzero : c e ≠ 0 := by
          simpa [edgeSupport] using heSupp
        have hce1 : c e = 1 := by
          let z : ZMod 2 := c e
          have hz : z = c e := rfl
          have hvalle : z.val ≤ 1 := Nat.le_of_lt_succ z.val_lt
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hvalle with h0 | h1
          · exfalso
            apply hce_nonzero
            calc
              c e = z := hz.symm
              _ = (z.val : ZMod 2) := by symm; exact ZMod.natCast_zmod_val z
              _ = 0 := by simp [h0]
          · calc
              c e = z := hz.symm
              _ = (z.val : ZMod 2) := by symm; exact ZMod.natCast_zmod_val z
              _ = 1 := by simp [h1]
        have hex : ∃ e' : EdgeIdx L, edgeToQubitIdx L e' = q ∧ c e' = 1 := ⟨e, heq, hce1⟩
        have hop : (toricXOperatorOfChain L c).operators q = PauliOperator.X := by
          simp [toricXOperatorOfChain, hex]
        simp [NQubitPauliOperator.support, hop]
    calc
      edgeWeight (L := L) c = (edgeSupport (L := L) c).card := rfl
      _ = ((edgeSupport (L := L) c).image (edgeToQubitIdx L)).card := by
        symm
        exact Finset.card_image_of_injective (s := edgeSupport (L := L) c) (f := edgeToQubitIdx L)
          (by intro a b hab; exact hidxinj hab)
      _ = (NQubitPauliOperator.support (toricXOperatorOfChain L c).operators).card := by
        rw [hsupport_eq]
  · have hL0 : L = 0 := Nat.eq_zero_of_not_pos hL
    subst hL0
    have hedgeSupport : edgeSupport (L := 0) c = ∅ := by
      ext e
      cases e with
      | h x y => exact Fin.elim0 x
      | v x y => exact Fin.elim0 x
    have hsupport : NQubitPauliOperator.support (toricXOperatorOfChain 0 c).operators = ∅ := by
      ext q
      exact Fin.elim0 q
    simp [edgeWeight, hedgeSupport, hsupport]

end Lattice
end Stabilizer
end Quantum
