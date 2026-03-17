import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import QEC.Foundations.Foundations
import QEC.Stabilizer.Core.StabilizerGroup
import QEC.Stabilizer.Core.Centralizer
import QEC.Stabilizer.Core.LogicalGateGroup
import QEC.Stabilizer.PauliGroup

namespace Quantum
namespace StabilizerGroup

variable {n : ℕ}

open Matrix

/-!
# Logical gates

A **logical gate** is a unitary operator that maps the codespace to itself. We define
`IsLogicalGate U S` as membership in the **logical gate group** `logicalGateGroup S` (see
`LogicalGateGroup.lean`). Equivalently, for every g ∈ S the conjugated operator U g U† stabilizes
every codespace state (adjoint on the right). Pauli logical operators are those
Paulis whose gate is a logical gate;
see `LogicalOperators.lean`. For Pauli operators, this coincides with the centralizer.
-/

/-- A unitary gate is a logical gate for S iff it lies in the logical gate group (unitaries
    that map the codespace to itself). -/
def IsLogicalGate (U : NQubitGate n) (S : StabilizerGroup n) : Prop :=
  U ∈ logicalGateGroup S

/-- IsLogicalGate is equivalent to mapping every codespace state into the codespace. -/
theorem isLogicalGate_iff (U : NQubitGate n) (S : StabilizerGroup n) :
    IsLogicalGate U S ↔ ∀ ψ, IsInCodespace ψ S → IsInCodespace (U • ψ) S :=
  mem_logicalGateGroup_iff U S

/-- IsLogicalGate is equivalent to gate-level conjugation fixing every codespace state. -/
theorem isLogicalGate_iff_conjugation (U : NQubitGate n) (S : StabilizerGroup n) :
    IsLogicalGate U S ↔ ∀ g ∈ S.toSubgroup, ∀ ψ : NQubitState n,
      IsInCodespace ψ S → (conjByGate U g.gate) • ψ = ψ := by
  constructor
  · intro h g hg ψ hψ
    apply Subtype.ext
    have hmul := (mem_logicalGateGroup_iff_conjugation_gate U S).1 h g hg ψ hψ
    simpa [smul_QState_val] using hmul
  · intro h
    refine (mem_logicalGateGroup_iff_conjugation_gate U S).2 ?_
    intro g hg ψ hψ
    have hEq : (conjByGate U g.gate) • ψ = ψ := h g hg ψ hψ
    simpa [smul_QState_val] using congrArg Subtype.val hEq

/-- MulVec bridge version of `isLogicalGate_iff_conjugation`. -/
theorem isLogicalGate_iff_conjugation_mulVec (U : NQubitGate n) (S : StabilizerGroup n) :
    IsLogicalGate U S ↔ ∀ g ∈ S.toSubgroup, ∀ ψ : NQubitState n,
      IsInCodespace ψ S → ((conjByGate U g.gate).val).mulVec ψ.val = ψ.val :=
  mem_logicalGateGroup_iff_conjugation_gate U S

/-- Matrix-bridge version of `isLogicalGate_iff_conjugation`. -/
theorem isLogicalGate_iff_conjugation_matrix (U : NQubitGate n) (S : StabilizerGroup n) :
    IsLogicalGate U S ↔ ∀ g ∈ S.toSubgroup, ∀ ψ : NQubitState n,
      IsInCodespace ψ S → (U.val * g.toMatrix * star U.val).mulVec ψ.val = ψ.val := by
  simpa [conjByGate_val, NQubitPauliGroupElement.gate_val] using
    (isLogicalGate_iff_conjugation_mulVec U S)

/-- Logical gate depends only on the underlying stabilizer subgroup. -/
theorem isLogicalGate_iff_toSubgroup_eq (U : NQubitGate n) (S T : StabilizerGroup n)
    (h : S.toSubgroup = T.toSubgroup) : IsLogicalGate U S ↔ IsLogicalGate U T := by
  unfold IsLogicalGate
  rw [mem_logicalGateGroup_iff, mem_logicalGateGroup_iff]
  constructor
  · intro hL ψ hψT
    have hψS : IsInCodespace ψ S := by
      rw [IsInCodespace.iff_all_stabilizers]
      intro g hg
      exact (IsInCodespace.iff_all_stabilizers ψ T).1 hψT g (h.symm ▸ hg)
    have hUψS : IsInCodespace (U • ψ) S := hL ψ hψS
    rw [IsInCodespace.iff_all_stabilizers]
    intro g hg
    exact (IsInCodespace.iff_all_stabilizers (U • ψ) S).1 hUψS g (h ▸ hg)
  · intro hL ψ hψS
    have hψT : IsInCodespace ψ T := by
      rw [IsInCodespace.iff_all_stabilizers]
      intro g hg
      exact (IsInCodespace.iff_all_stabilizers ψ S).1 hψS g (h.symm ▸ hg)
    have hUψT : IsInCodespace (U • ψ) T := hL ψ hψT
    rw [IsInCodespace.iff_all_stabilizers]
    intro g hg
    exact (IsInCodespace.iff_all_stabilizers (U • ψ) T).1 hUψT g (h ▸ hg)

/-- If every generator in `T` conjugates into `closure T`, then every element of `closure T`
does too (gate-level form). -/
lemma conjugates_mem_closure_of_set_conjugates
    (U : NQubitGate n) (T : Set (NQubitPauliGroupElement n))
    (hgen : ∀ g ∈ T, ∃ g' ∈ Subgroup.closure T, conjByGate U g.toGate = g'.toGate) :
    ∀ g ∈ Subgroup.closure T, ∃ g' ∈ Subgroup.closure T, conjByGate U g.toGate = g'.toGate := by
  intro g hg
  refine
    Subgroup.closure_induction
      (p := fun g (_ : g ∈ Subgroup.closure T) =>
        ∃ g' ∈ Subgroup.closure T, conjByGate U g.toGate = g'.toGate)
      ?_ ?_ ?_ ?_ hg
  · intro x hx
    exact hgen x hx
  · refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [NQubitPauliGroupElement.toGate_one (n := n)]
    exact (conjByGate_one (U := U))
  · intro x y _ _ hx hy
    rcases hx with ⟨x', hx', hcx⟩
    rcases hy with ⟨y', hy', hcy⟩
    refine ⟨x' * y', Subgroup.mul_mem _ hx' hy', ?_⟩
    change conjByGate U ((x * y).toGate) = ((x' * y').toGate)
    rw [NQubitPauliGroupElement.toGate_mul, conjByGate_mul, hcx, hcy,
      ← NQubitPauliGroupElement.toGate_mul]
  · intro x _ hx
    rcases hx with ⟨x', hx', hcx⟩
    refine ⟨x'⁻¹, Subgroup.inv_mem _ hx', ?_⟩
    change conjByGate U ((x⁻¹).toGate) = ((x'⁻¹).toGate)
    rw [NQubitPauliGroupElement.toGate_inv, conjByGate_inv, hcx,
      ← NQubitPauliGroupElement.toGate_inv]

/-- If conjugation by `U` maps each stabilizer in `S` to some stabilizer in `S`, then `U` is a
logical gate for `S` (gate-level premise). -/
lemma isLogicalGate_of_conjugates_toSubgroup
    (U : NQubitGate n) (S : StabilizerGroup n)
    (hconj : ∀ g ∈ S.toSubgroup, ∃ g' ∈ S.toSubgroup, conjByGate U g.toGate = g'.toGate) :
    IsLogicalGate U S := by
  rw [isLogicalGate_iff_conjugation]
  intro g hg ψ hψ
  obtain ⟨g', hg', hgg'⟩ := hconj g hg
  have hstab : g'.gate • ψ = ψ := by
    apply Subtype.ext
    simpa [smul_QState_val, NQubitPauliGroupElement.gate_val] using hψ g' hg'
  have hconjψ : (conjByGate U g.gate) • ψ = g'.gate • ψ := by
    simpa [NQubitPauliGroupElement.gate_eq_toGate] using congrArg (fun V => V • ψ) hgg'
  calc
    (conjByGate U g.gate) • ψ = g'.gate • ψ := hconjψ
    _ = ψ := hstab

/-- If every generator in `T` conjugates into the stabilizer subgroup and
`S.toSubgroup = closure T`, then `U` is a logical gate for `S`. -/
lemma isLogicalGate_of_generator_set_conjugation
    (U : NQubitGate n) (S : StabilizerGroup n) (T : Set (NQubitPauliGroupElement n))
    (hS : S.toSubgroup = Subgroup.closure T)
    (hgen : ∀ g ∈ T, ∃ g' ∈ S.toSubgroup, conjByGate U g.toGate = g'.toGate) :
    IsLogicalGate U S := by
  apply isLogicalGate_of_conjugates_toSubgroup U S
  intro g hg
  have hg' : g ∈ Subgroup.closure T := by
    simpa [hS] using hg
  obtain ⟨g', hg', hgg'⟩ :=
    conjugates_mem_closure_of_set_conjugates U T (by
      intro x hx
      obtain ⟨x', hx', hxx'⟩ := hgen x hx
      exact ⟨x', by simpa [hS] using hx', hxx'⟩) g hg'
  exact ⟨g', by simpa [hS] using hg', hgg'⟩

end StabilizerGroup
end Quantum
