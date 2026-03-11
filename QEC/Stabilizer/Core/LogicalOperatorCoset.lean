import QEC.Stabilizer.Core.StabilizerGroup
import QEC.Stabilizer.Core.Centralizer
import QEC.Stabilizer.PauliGroup.NQubitOperator

namespace Quantum
namespace StabilizerGroup

variable {n : ℕ}

/-!
# Logical operators as cosets

Logical operators (as mathematical objects) are **cosets of S in the group of Pauli logical
operators** (the centralizer of S). Two Pauli elements represent the same logical operator iff
they lie in the same coset (differ by an element of S).

For **code distance**, we only count cosets that are "nontrivial": not the identity coset and
not a "phase-only" coset. A phase-only coset is one where every representative has the same
operator part as some stabilizer element (i.e. the coset is φ·S for some phase φ). Excluding
these ensures that e.g. -Z for Z ∈ S does not lower the distance.

This file defines `RepresentsNontrivialCoset g S` (element-level predicate) and relates it to
the coset notion. The quotient type (centralizer S) ⧸ S is not constructed here; the
element-level API suffices for `HasCodeDistance` and call sites.
-/

open NQubitPauliGroupElement

/-- A Pauli element g **represents a nontrivial coset** (for code distance) iff g is in the
    centralizer of S, not in S, and no element of S has the same operator part as g.
    Equivalently: g represents a coset that is not the identity coset and not a phase-only
    coset (φ·S). -/
def RepresentsNontrivialCoset (g : NQubitPauliGroupElement n) (S : StabilizerGroup n) : Prop :=
  g ∈ centralizer S ∧ g ∉ S.toSubgroup ∧
  ∀ s ∈ S.toSubgroup, s.operators ≠ g.operators

/-- If g represents a nontrivial coset, then g is in the centralizer. -/
lemma RepresentsNontrivialCoset.mem_centralizer {g : NQubitPauliGroupElement n}
    {S : StabilizerGroup n} (h : RepresentsNontrivialCoset g S) : g ∈ centralizer S :=
  h.1

/-- If g represents a nontrivial coset, then g is not in the stabilizer. -/
lemma RepresentsNontrivialCoset.not_mem {g : NQubitPauliGroupElement n} {S : StabilizerGroup n}
    (h : RepresentsNontrivialCoset g S) : g ∉ S.toSubgroup :=
  h.2.1

/-- If g represents a nontrivial coset, then no stabilizer element has the same
    operator part as g. -/
lemma RepresentsNontrivialCoset.operators_ne_of_mem {g : NQubitPauliGroupElement n}
    {S : StabilizerGroup n} (h : RepresentsNontrivialCoset g S) (s : NQubitPauliGroupElement n)
    (hs : s ∈ S.toSubgroup) : s.operators ≠ g.operators :=
  h.2.2 s hs

/-- RepresentsNontrivialCoset is unchanged when the stabilizer has the same subgroup. -/
theorem RepresentsNontrivialCoset_of_toSubgroup_eq (g : NQubitPauliGroupElement n)
    {S T : StabilizerGroup n} (h : S.toSubgroup = T.toSubgroup) :
    (RepresentsNontrivialCoset g S ↔ RepresentsNontrivialCoset g T) := by
  rw [RepresentsNontrivialCoset, RepresentsNontrivialCoset]
  rw [centralizer_eq_of_toSubgroup_eq S T h, h]

/-- If g is in the centralizer and has the same operator part as some s ∈ S, then g is in the
    coset φ·S (phase-only): g differs from s only by phase, so g ∈ (phase factor)·S. Hence g
    does not represent a nontrivial coset. -/
lemma not_RepresentsNontrivialCoset_of_same_operators_as_stabilizer
    (g : NQubitPauliGroupElement n) (S : StabilizerGroup n) (_ : g ∈ centralizer S)
    (s : NQubitPauliGroupElement n) (hs : s ∈ S.toSubgroup) (heq : s.operators = g.operators) :
    ¬RepresentsNontrivialCoset g S := by
  intro h
  exact h.2.2 s hs heq

end StabilizerGroup
end Quantum
