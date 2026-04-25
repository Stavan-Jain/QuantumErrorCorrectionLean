import Mathlib.Tactic
import QEC.Stabilizer.PauliGroup.NQubitOperator

namespace Quantum
namespace NQubitPauliOperator

variable {n : ℕ}

/-- `set` writes the requested Pauli at the target index. -/
@[simp] lemma set_apply_eq (op : NQubitPauliOperator n) (i : Fin n) (p : PauliOperator) :
    set op i p i = p := by
  simp [set]

/-- `set` leaves all other indices unchanged. -/
@[simp] lemma set_apply_ne (op : NQubitPauliOperator n) (i j : Fin n) (p : PauliOperator)
    (h : j ≠ i) :
    set op i p j = op j := by
  simp [set, h]

/-- Membership in the support of `set op i p` at the edited index. -/
@[simp] lemma mem_support_set_same_iff
    (op : NQubitPauliOperator n) (i : Fin n) (p : PauliOperator) :
    i ∈ support (set op i p) ↔ p ≠ PauliOperator.I := by
  simp [support, set]

/-- Membership in the support of `set op i p` at any other index. -/
@[simp] lemma mem_support_set_ne_iff
    (op : NQubitPauliOperator n) (i j : Fin n) (p : PauliOperator) (h : j ≠ i) :
    j ∈ support (set op i p) ↔ j ∈ support op := by
  simp [support, set, h]

/-- The support of `set op i p` is contained in `insert i (support op)`. -/
lemma support_set_subset_insert (op : NQubitPauliOperator n) (i : Fin n) (p : PauliOperator) :
    support (set op i p) ⊆ insert i (support op) := by
  intro j hj
  by_cases hji : j = i
  · exact Finset.mem_insert.mpr (Or.inl hji)
  · exact Finset.mem_insert.mpr (Or.inr ((mem_support_set_ne_iff op i j p hji).1 hj))

end NQubitPauliOperator
end Quantum

