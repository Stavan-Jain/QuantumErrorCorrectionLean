import Mathlib.Tactic


namespace Quantum
namespace Stabilizer
namespace Lattice

/-- Row-major encoding `(x,y) ↦ y*L + x` is injective on `Fin L × Fin L` for `L > 0`. -/
lemma rowMajor_injective (L : ℕ) [Fact (0 < L)] :
    Function.Injective (fun p : Fin L × Fin L => p.2.val * L + p.1.val) := by
  intro p q hpq
  rcases p with ⟨x₁, y₁⟩
  rcases q with ⟨x₂, y₂⟩
  have hxval : x₁.val = x₂.val := by
    have hmod : (y₁.val * L + x₁.val) % L = (y₂.val * L + x₂.val) % L :=
      congrArg (fun n => n % L) hpq
    simpa [Nat.add_mod, Nat.mul_mod_right, Nat.mod_eq_of_lt x₁.isLt,
      Nat.mod_eq_of_lt x₂.isLt] using hmod
  have hyval : y₁.val = y₂.val := by
    have hdiv : (y₁.val * L + x₁.val) / L = (y₂.val * L + x₂.val) / L :=
      congrArg (fun n => n / L) hpq
    have hy1 : (y₁.val * L + x₁.val) / L = y₁.val := by
      rw [Nat.add_comm, Nat.add_mul_div_right]
      simp [Nat.div_eq_of_lt x₁.isLt]
      exact Fact.out
    have hy2 : (y₂.val * L + x₂.val) / L = y₂.val := by
      rw [Nat.add_comm, Nat.add_mul_div_right]
      simp [Nat.div_eq_of_lt x₂.isLt]
      exact Fact.out
    rw [hy1, hy2] at hdiv
    exact hdiv
  exact Prod.ext (Fin.ext hxval) (Fin.ext hyval)

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
