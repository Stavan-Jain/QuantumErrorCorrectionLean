import Mathlib.Tactic
import QEC.Stabilizer.PauliGroup.NQubitOperator
import QEC.Stabilizer.Core.CSS
import QEC.Stabilizer.PauliGroup.Commutation

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

/-- Setting a Z-type single-qubit operator preserves n-qubit Z-type. -/
lemma IsZType_set_of_IsZType (op : NQubitPauliOperator n) (i : Fin n) (p : PauliOperator)
    (hop : IsZType op) (hp : PauliOperator.IsZType p) :
    IsZType (set op i p) := by
  intro j
  by_cases hji : j = i
  · subst hji
    simpa [set] using hp
  · simpa [set, hji] using hop j

/-- Setting an X-type single-qubit operator preserves n-qubit X-type. -/
lemma IsXType_set_of_IsXType (op : NQubitPauliOperator n) (i : Fin n) (p : PauliOperator)
    (hop : IsXType op) (hp : PauliOperator.IsXType p) :
    IsXType (set op i p) := by
  intro j
  by_cases hji : j = i
  · subst hji
    simpa [set] using hp
  · simpa [set, hji] using hop j

/-- Setting a `Z` preserves n-qubit Z-type. -/
lemma IsZType_set_Z_of_IsZType (op : NQubitPauliOperator n) (i : Fin n) (hop : IsZType op) :
    IsZType (set op i PauliOperator.Z) :=
  IsZType_set_of_IsZType op i PauliOperator.Z hop PauliOperator.IsZType_Z

/-- Setting an `X` preserves n-qubit X-type. -/
lemma IsXType_set_X_of_IsXType (op : NQubitPauliOperator n) (i : Fin n) (hop : IsXType op) :
    IsXType (set op i PauliOperator.X) :=
  IsXType_set_of_IsXType op i PauliOperator.X hop PauliOperator.IsXType_X

end NQubitPauliOperator

namespace NQubitPauliGroupElement

variable {n : ℕ}

/-- For Z/X-typed operator tensors, `anticommutesAt` is equivalent to both positions being in support. -/
lemma anticommutesAt_iff_mem_support_both_of_ZXType
    {p q : NQubitPauliOperator n}
    (hp : NQubitPauliOperator.IsZType p)
    (hq : NQubitPauliOperator.IsXType q)
    (i : Fin n) :
    anticommutesAt (n := n) p q i ↔ i ∈ p.support ∧ i ∈ q.support := by
  have hp' : p i = PauliOperator.I ∨ p i = PauliOperator.Z := hp i
  have hq' : q i = PauliOperator.I ∨ q i = PauliOperator.X := hq i
  rcases hp' with hpI | hpZ
  · rcases hq' with hqI | hqX
    · simp [anticommutesAt, NQubitPauliOperator.support, hpI, hqI]
    · simp [anticommutesAt, NQubitPauliOperator.support, hpI, hqX]
  · rcases hq' with hqI | hqX
    · simp [anticommutesAt, NQubitPauliOperator.support, hpZ, hqI]
    · simp [anticommutesAt, NQubitPauliOperator.support, hpZ, hqX]

end NQubitPauliGroupElement
end Quantum

