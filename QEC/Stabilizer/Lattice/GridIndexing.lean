import Mathlib.Tactic

namespace Quantum
namespace Stabilizer
namespace Lattice

/-- If one index lies below an offset and another is at least the offset, they differ. -/
lemma ne_of_lt_offset_le {a b offset : ℕ} (ha : a < offset) (hb : offset ≤ b) : a ≠ b := by
  intro hab
  omega

/-- Fin-indexed variant of `ne_of_lt_offset_le` for values in the same ambient `Fin n`. -/
lemma fin_ne_of_val_lt_offset_le {n offset : ℕ} {i j : Fin n}
    (hi : i.val < offset) (hj : offset ≤ j.val) : i ≠ j := by
  intro hij
  exact ne_of_lt_offset_le hi (hij ▸ hj) rfl

end Lattice
end Stabilizer
end Quantum

