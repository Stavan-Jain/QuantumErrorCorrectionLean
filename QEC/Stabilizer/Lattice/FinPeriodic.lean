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
  sorry

/-- `next` and `prev` are inverses on `Fin L` (right inverse direction). -/
@[simp] lemma prev_next (L : ℕ) [Fact (0 < L)] (i : Fin L) :
    prev L (next L i) = i := by
  sorry

end Lattice
end Stabilizer
end Quantum

