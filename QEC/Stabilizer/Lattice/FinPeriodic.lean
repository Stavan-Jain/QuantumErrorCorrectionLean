import Mathlib.Tactic


namespace Quantum
namespace Stabilizer
namespace Lattice

/-- Convert the nondegeneracy assumption `2 ≤ L` into positivity `0 < L`. -/
instance factPosOfTwoLE (L : ℕ) [Fact (2 ≤ L)] : Fact (0 < L) := ⟨by
  have h2 : 0 < 2 := by decide
  exact lt_of_lt_of_le h2 Fact.out⟩

/-- Useful base instance for concrete `L = 2` specializations. -/
instance factPosTwo : Fact (0 < 2) := ⟨by decide⟩

/-- Successor modulo `L` on `Fin L`. -/
def next (L : ℕ) [Fact (0 < L)] (i : Fin L) : Fin L :=
  ⟨(i.val + 1) % L, Nat.mod_lt _ Fact.out⟩

/-- Predecessor modulo `L` on `Fin L`. -/
def prev (L : ℕ) [Fact (0 < L)] (i : Fin L) : Fin L :=
  ⟨(i.val + (L - 1)) % L, Nat.mod_lt _ Fact.out⟩

@[simp] lemma next_val (L : ℕ) [Fact (0 < L)] (i : Fin L) :
    (next L i).val = (i.val + 1) % L := rfl

@[simp] lemma prev_val (L : ℕ) [Fact (0 < L)] (i : Fin L) :
    (prev L i).val = (i.val + (L - 1)) % L := rfl

/-- `next` and `prev` are inverses on `Fin L` (left inverse direction). -/
@[simp] lemma next_prev (L : ℕ) [Fact (0 < L)] (i : Fin L) :
    next L (prev L i) = i := by
  apply Fin.ext
  by_cases h0 : i.val = 0
  · have hL : 0 < L := Fact.out
    have hmod : (((0 + (L - 1)) % L + 1) % L) = 0 := by
      have hm1 : L - 1 < L := by omega
      simp [Nat.mod_eq_of_lt hm1]
      have : (L - 1) + 1 = L := by omega
      rw [this, Nat.mod_self]
    simpa [next, prev, h0] using hmod
  · have hL : 0 < L := Fact.out
    have hpos : 0 < i.val := Nat.pos_of_ne_zero h0
    have hmod1 : ((i.val + (L - 1)) % L) = i.val - 1 := by
      have hsum : i.val + (L - 1) = L + (i.val - 1) := by omega
      rw [hsum, Nat.add_mod_left]
      have hlt' : i.val - 1 < L := by omega
      exact Nat.mod_eq_of_lt hlt'
    have hmod2 : (((i.val + (L - 1)) % L + 1) % L) = i.val := by
      rw [hmod1]
      have : i.val - 1 + 1 = i.val := by omega
      rw [this, Nat.mod_eq_of_lt i.isLt]
    simpa [next, prev] using hmod2

/-- `next` and `prev` are inverses on `Fin L` (right inverse direction). -/
@[simp] lemma prev_next (L : ℕ) [Fact (0 < L)] (i : Fin L) :
    prev L (next L i) = i := by
  apply Fin.ext
  have hL : 0 < L := Fact.out
  by_cases hlast : i.val + 1 = L
  · have hmod0 : (i.val + 1) % L = 0 := by simp [hlast]
    have hi : i.val = L - 1 := by omega
    have hm1 : L - 1 < L := by omega
    have hcalc : (((i.val + 1) % L + (L - 1)) % L) = i.val := by
      rw [hmod0, Nat.zero_add, Nat.mod_eq_of_lt hm1, hi]
    simpa [prev, next] using hcalc
  · have hlt : i.val + 1 < L := by
      have hle : i.val + 1 ≤ L := Nat.succ_le_of_lt i.isLt
      exact Nat.lt_of_le_of_ne hle hlast
    have hmod : (i.val + 1) % L = i.val + 1 := Nat.mod_eq_of_lt hlt
    have hcalc : (((i.val + 1) % L + (L - 1)) % L) = i.val := by
      rw [hmod]
      have hsum : i.val + 1 + (L - 1) = L + i.val := by omega
      rw [hsum, Nat.add_mod_left, Nat.mod_eq_of_lt i.isLt]
    simpa [prev, next] using hcalc

/-- Rewriting `prev a = b` as `a = next b`. -/
@[simp] lemma prev_eq_iff_eq_next (L : ℕ) [Fact (0 < L)] (a b : Fin L) :
    prev L a = b ↔ a = next L b := by
  constructor
  · intro h
    calc
      a = next L (prev L a) := by simp
      _ = next L b := by simp [h]
  · intro h
    calc
      prev L a = prev L (next L b) := by simp [h]
      _ = b := by simp

/-- Rewriting `a = prev b` as `next a = b`. -/
@[simp] lemma eq_prev_iff_next_eq (L : ℕ) [Fact (0 < L)] (a b : Fin L) :
    a = prev L b ↔ next L a = b := by
  constructor
  · intro h
    calc
      next L a = next L (prev L b) := by simp [h]
      _ = b := by simp
  · intro h
    calc
      a = prev L (next L a) := by simp
      _ = prev L b := by simp [h]

/-- On nontrivial cyclic indices (`2 ≤ L`), `next` has no fixed points. -/
lemma next_ne_self (L : ℕ) [Fact (2 ≤ L)] (i : Fin L) : next L i ≠ i := by
  intro h
  have hL : 0 < L := (factPosOfTwoLE L).out
  have h2 : 2 ≤ L := Fact.out
  have hval : (i.val + 1) % L = i.val := congrArg Fin.val h
  by_cases htop : i.val + 1 = L
  · have hmod : (i.val + 1) % L = 0 := by simp [htop]
    have hi0 : i.val = 0 := by simpa [hmod] using hval.symm
    have hiLast : i.val = L - 1 := by omega
    omega
  · have hle : i.val + 1 ≤ L := Nat.succ_le_of_lt i.isLt
    have hlt : i.val + 1 < L := Nat.lt_of_le_of_ne hle htop
    have hmod : (i.val + 1) % L = i.val + 1 := Nat.mod_eq_of_lt hlt
    rw [hmod] at hval
    omega

/-- On nontrivial cyclic indices (`2 ≤ L`), `prev` has no fixed points. -/
lemma prev_ne_self (L : ℕ) [Fact (2 ≤ L)] (i : Fin L) : prev L i ≠ i := by
  intro h
  have hnext : next L (prev L i) = next L i := congrArg (next L) h
  have hi : i = next L i := by simpa using hnext
  exact next_ne_self L i hi.symm

end Lattice
end Stabilizer
end Quantum

