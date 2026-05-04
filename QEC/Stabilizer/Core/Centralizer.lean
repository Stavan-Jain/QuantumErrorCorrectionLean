import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer
import QEC.Stabilizer.Core.StabilizerGroup
import QEC.Stabilizer.Core.SubgroupLemmas
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
noncomputable def centralizer (S : StabilizerGroup n) : Subgroup (NQubitPauliGroupElement n) :=
  Subgroup.centralizer (S.toSubgroup : Set (NQubitPauliGroupElement n))

/-- The centralizer depends only on the underlying subgroup. -/
lemma centralizer_eq_of_toSubgroup_eq (S T : StabilizerGroup n) (h : S.toSubgroup = T.toSubgroup) :
    centralizer S = centralizer T := by
  rw [centralizer, centralizer, h]

/-- The normalizer of S in the n-qubit Pauli group: Pauli elements g such that
    conjugation sends S to itself (g⁻¹ * s * g ∈ S for all s ∈ S). -/
noncomputable def pauliNormalizer (S : StabilizerGroup n) : Subgroup (NQubitPauliGroupElement n) :=
  Subgroup.normalizer S.toSubgroup

/-- For a stabilizer group (abelian, no -I), the normalizer of S in the Pauli group
    equals the centralizer of S in the Pauli group. -/
theorem pauliNormalizer_eq_centralizer (S : StabilizerGroup n) :
    pauliNormalizer S = centralizer S := by
  ext g
  constructor
  · intro hg
    rw [centralizer, Subgroup.mem_centralizer_iff]
    intro s hs
    rw [pauliNormalizer, Subgroup.mem_normalizer_iff] at hg
    have h_conj := (hg s).1 hs
    have h_comm_or_anti := NQubitPauliGroupElement.commute_or_anticommute g s
    cases h_comm_or_anti with
    | inl h_comm => exact h_comm.symm
    | inr h_anti =>
        have h_conj_eq : g * s * g⁻¹ = negIdentity n * s := by
          unfold NQubitPauliGroupElement.Anticommute at h_anti
          calc g * s * g⁻¹ = (NQubitPauliGroupElement.minusOne n * (s * g)) *
          g⁻¹ := by rw [← h_anti]
            _ = NQubitPauliGroupElement.minusOne n * ((s * g) * g⁻¹) := by rw [mul_assoc]
            _ = NQubitPauliGroupElement.minusOne n * (s * (g * g⁻¹)) := by rw [mul_assoc]
            _ = NQubitPauliGroupElement.minusOne n * (s * 1) := by rw [mul_inv_cancel]
            _ = negIdentity n * s := by rw [mul_one, negIdentity_eq_minusOne n]
        rw [h_conj_eq] at h_conj
        have h_neg_mem : negIdentity n ∈ S.toSubgroup := by
          have H : (negIdentity n * s) * s⁻¹ = negIdentity n := by group
          rw [← H]
          exact S.toSubgroup.mul_mem h_conj (S.toSubgroup.inv_mem hs)
        exact absurd h_neg_mem S.neg_identity_not_mem
  · intro hg
    rw [pauliNormalizer, Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · intro hs
      rw [centralizer, Subgroup.mem_centralizer_iff] at hg
      have h_comm := hg s hs
      have H : g * s * g⁻¹ = s := by
        calc g * s * g⁻¹ = (s * g) * g⁻¹ := by rw [← h_comm]
          _ = s * (g * g⁻¹) := by rw [mul_assoc]
          _ = s * 1 := by rw [mul_inv_cancel]
          _ = s := by rw [mul_one]
      rw [H]
      exact hs
    · intro hs'
      rw [centralizer, Subgroup.mem_centralizer_iff] at hg
      have h_comm := hg (g * s * g⁻¹) hs'
      have H_eq : g⁻¹ * (g * s * g⁻¹) * g = g * s * g⁻¹ := by
        calc g⁻¹ * (g * s * g⁻¹) * g = g⁻¹ * ((g * s * g⁻¹) * g) := by rw [mul_assoc]
          _ = g⁻¹ * (g * (g * s * g⁻¹)) := by rw [h_comm]
          _ = (g⁻¹ * g) * (g * s * g⁻¹) := by rw [← mul_assoc]
          _ = g * s * g⁻¹ := by rw [inv_mul_cancel, one_mul]
      have H : s = g * s * g⁻¹ := by
        calc s = g⁻¹ * (g * s) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
          _ = g⁻¹ * (g * s * 1) := by rw [mul_one]
          _ = g⁻¹ * (g * s * (g⁻¹ * g)) := by rw [inv_mul_cancel]
          _ = g⁻¹ * ((g * s * g⁻¹) * g) := by simp only [mul_assoc]
          _ = g⁻¹ * (g * (g * s * g⁻¹)) := by rw [h_comm]
          _ = (g⁻¹ * g) * (g * s * g⁻¹) := by rw [← mul_assoc]
          _ = g * s * g⁻¹ := by rw [inv_mul_cancel, one_mul]
      rw [H]
      exact hs'

/-- Membership in the centralizer is equivalent to commuting with every element
    of the stabilizer group. -/
lemma mem_centralizer_iff (g : NQubitPauliGroupElement n) (S : StabilizerGroup n) :
    g ∈ centralizer S ↔ ∀ h ∈ S.toSubgroup, h * g = g * h :=
  Subgroup.mem_centralizer_iff

/-- When the stabilizer subgroup is the closure of a set of generators,
membership in the centralizer reduces to commuting with each generator. -/
lemma mem_centralizer_iff_closure (g : NQubitPauliGroupElement n) (S : StabilizerGroup n)
    (genSet : Set (NQubitPauliGroupElement n)) (h_closure : S.toSubgroup =
    Subgroup.closure genSet) :
    g ∈ centralizer S ↔ ∀ s ∈ genSet, s * g = g * s := by
  rw [mem_centralizer_iff, h_closure]
  exact Subgroup.forall_comm_closure_iff g genSet

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
