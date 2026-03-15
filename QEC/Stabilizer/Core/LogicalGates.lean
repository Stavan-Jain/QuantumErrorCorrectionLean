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
every codespace state (adjoint on the right). Pauli logical operators are those Paulis whose gate is a logical gate;
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

/-- IsLogicalGate is equivalent to the conjugation characterization (U g U† fixes codespace). -/
theorem isLogicalGate_iff_conjugation (U : NQubitGate n) (S : StabilizerGroup n) :
    IsLogicalGate U S ↔ ∀ g ∈ S.toSubgroup, ∀ ψ : NQubitState n,
      IsInCodespace ψ S → (U.val * g.toMatrix * star U.val).mulVec ψ.val = ψ.val :=
  mem_logicalGateGroup_iff_conjugation U S

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

end StabilizerGroup
end Quantum
