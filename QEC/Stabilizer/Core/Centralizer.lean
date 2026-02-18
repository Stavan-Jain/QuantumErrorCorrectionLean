import Mathlib.GroupTheory.Subgroup.Centralizer
import QEC.Stabilizer.Core.StabilizerGroup
import QEC.Stabilizer.PauliGroup
import QEC.Stabilizer.PauliGroup.Commutation

namespace Quantum
namespace StabilizerGroup

variable {n : ℕ}

/-!
# Centralizer of a stabilizer group

The centralizer of a stabilizer group S is the subgroup of the n-qubit Pauli group
consisting of all elements that commute with every element of S. These are exactly
the operators that preserve the codespace (map the codespace to itself). For Pauli
stabilizer groups (no -I), the centralizer coincides with the normalizer.
-/

/-- The centralizer of a stabilizer group: all Pauli elements that commute with
    every element of S. Equivalently, operators that preserve the codespace. -/
def centralizer (S : StabilizerGroup n) : Subgroup (NQubitPauliGroupElement n) :=
  Subgroup.centralizer (S.toSubgroup : Set (NQubitPauliGroupElement n))

/-- Membership in the centralizer is equivalent to commuting with every element
    of the stabilizer group. -/
lemma mem_centralizer_iff (g : NQubitPauliGroupElement n) (S : StabilizerGroup n) :
    g ∈ centralizer S ↔ ∀ h ∈ S.toSubgroup, h * g = g * h :=
  Subgroup.mem_centralizer_iff

/-- Every element of the stabilizer group lies in its centralizer (S is abelian). -/
theorem stabilizer_le_centralizer (S : StabilizerGroup n) :
    S.toSubgroup ≤ centralizer S := by
  intro g hg
  rw [mem_centralizer_iff]
  intro h hh
  exact (S.is_abelian g h hg hh).symm

/-!
## Proving an operator is not in the stabilizer via a centralizer witness

If a Pauli operator Q is in the centralizer (commutes with the whole stabilizer) and
anticommutes with P, then P cannot lie in the stabilizer: the stabilizer is abelian,
so every element would commute with Q, contradicting P * Q = -Q * P.
This gives a uniform, code-agnostic way to show e.g. that logical X and Z are not
in the stabilizer, by taking Q = logical Z and Q = logical X respectively.
-/

/-- If P and Q anticommute and Q commutes with every element of the stabilizer,
    then P is not in the stabilizer group. -/
theorem not_mem_stabilizer_of_anticommutes_centralizer (S : StabilizerGroup n)
    (P Q : NQubitPauliGroupElement n) (hQ_cent : Q ∈ centralizer S)
    (h_anticomm : NQubitPauliGroupElement.Anticommute P Q) :
    P ∉ S.toSubgroup := by
  intro hP
  rw [mem_centralizer_iff] at hQ_cent
  have hQP : Q * P = P * Q := (hQ_cent P hP).symm
  unfold NQubitPauliGroupElement.Anticommute at h_anticomm
  rw [hQP] at h_anticomm
  rw [← negIdentity_eq_minusOne n] at h_anticomm
  have h_eq : (1 : NQubitPauliGroupElement n) = negIdentity n := by
    calc (1 : NQubitPauliGroupElement n) = (P * Q) * (P * Q)⁻¹ := by rw [mul_inv_cancel]
      _ = (negIdentity n * (P * Q)) * (P * Q)⁻¹ := by rw [← h_anticomm]
      _ = negIdentity n * ((P * Q) * (P * Q)⁻¹) := by rw [mul_assoc]
      _ = negIdentity n * 1 := by rw [mul_inv_cancel]
      _ = negIdentity n := by rw [mul_one]
  exact negIdentity_ne_one n h_eq.symm

end StabilizerGroup
end Quantum
