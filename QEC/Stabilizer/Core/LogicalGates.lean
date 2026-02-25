import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import QEC.Foundations.Foundations
import QEC.Stabilizer.Core.StabilizerGroup
import QEC.Stabilizer.Core.Centralizer
import QEC.Stabilizer.Core.Normalizer
import QEC.Stabilizer.PauliGroup

namespace Quantum
namespace StabilizerGroup

variable {n : ℕ}

open Matrix

/-!
# Logical gates

A **logical gate** is a unitary operator that maps the codespace to itself. This file defines
logical gates and proves that a unitary is a logical gate for a stabilizer
group if and only if it lies in the
**normalizer** of the stabilizer group (i.e. conjugation by the gate sends the stabilizer group
to itself). Pauli logical operators are those Paulis whose gate is a logical gate; see
`LogicalOperators.lean`. For Pauli operators, this coincides with the centralizer.
-/

/-- A unitary gate is a logical gate for S if it maps every state in the codespace
    into the codespace. -/
def IsLogicalGate (U : NQubitGate n) (S : StabilizerGroup n) : Prop :=
  ∀ ψ : NQubitState n, IsInCodespace ψ S → IsInCodespace (U • ψ) S

/-!
A unitary U is a logical gate if and only if it maps the stabilizer group to itself under
conjugation (i.e. U ∈ normalizer of S).
-/

/-- If `U` is a logical gate for `S`, then `U` lies in the normalizer of `S`:
conjugating any stabilizer by `U` yields a stabilizer. -/
theorem IsInStabilizerNormalizer.of_logicalGate (U : NQubitGate n) (S : StabilizerGroup n)
    (h : IsLogicalGate U S) : IsInStabilizerNormalizer U S := by
  intro g hg ψ hψ
  have hUψ : IsInCodespace (U • ψ) S := h ψ hψ
  rw [IsInCodespace.iff_all_stabilizers] at hUψ
  have h_stab : IsStabilizedBy g (U • ψ) := hUψ g hg
  simp only [IsStabilizedBy, IsStabilizedVec, smul_QState_val] at h_stab
  have h_conj : (star U.val * g.toMatrix * U.val).mulVec ψ.val = ψ.val := by
    calc (star U.val * g.toMatrix * U.val).mulVec ψ.val
        = (star U.val * (g.toMatrix * U.val)).mulVec ψ.val := by rw [Matrix.mul_assoc]
      _ = (star U.val).mulVec ((g.toMatrix * U.val).mulVec ψ.val) := by
          rw [← mulVec_mulVec ψ.val (star U.val) (g.toMatrix * U.val)]
      _ = (star U.val).mulVec (g.toMatrix.mulVec (U.val.mulVec ψ.val)) := by
          rw [← mulVec_mulVec ψ.val g.toMatrix U.val]
      _ = (star U.val).mulVec (U.val.mulVec ψ.val) := by rw [h_stab]
      _ = ((star U.val) * U.val).mulVec ψ.val := by
          rw [← mulVec_mulVec ψ.val (star U.val) U.val]
      _ = ψ.val := by
        have h_unit : (star U.val) * U.val = 1 := Matrix.mem_unitaryGroup_iff'.1 U.2
        rw [h_unit, one_mulVec]
  exact h_conj

/-- If U is in the normalizer of S then
    U maps the codespace to itself and is therefore a logical gate. -/
theorem IsLogicalGate.of_normalizer (U : NQubitGate n) (S : StabilizerGroup n)
    (h : IsInStabilizerNormalizer U S) : IsLogicalGate U S := by
  intro ψ hψ
  rw [IsInCodespace.iff_all_stabilizers]
  intro g hg
  simp only [IsStabilizedBy, IsStabilizedVec, smul_QState_val]
  have h_conj := h g hg ψ hψ
  calc g.toMatrix.mulVec (U.val.mulVec ψ.val)
      = (g.toMatrix * U.val).mulVec ψ.val := by rw [mulVec_mulVec]
    _ = (U.val * (star U.val) * (g.toMatrix * U.val)).mulVec ψ.val := by
      have h_unit : U.val * star U.val = 1 := Matrix.mem_unitaryGroup_iff.1 U.2
      rw [← Matrix.mul_assoc, h_unit, one_mul]
    _ = (U.val * ((star U.val) * (g.toMatrix * U.val))).mulVec ψ.val := by rw [Matrix.mul_assoc]
    _ = U.val.mulVec (((star U.val) * (g.toMatrix * U.val)).mulVec ψ.val) := by rw [mulVec_mulVec]
    _ = U.val.mulVec ψ.val := by rw [← Matrix.mul_assoc, h_conj]

/-- A unitary is a logical gate if and only if it is in the normalizer
    of the stabilizer group (as a predicate). -/
theorem isLogicalGate_iff_isInStabilizerNormalizer (U : NQubitGate n) (S : StabilizerGroup n) :
    IsLogicalGate U S ↔ IsInStabilizerNormalizer U S :=
  ⟨IsInStabilizerNormalizer.of_logicalGate U S, IsLogicalGate.of_normalizer U S⟩

/-- A unitary is a logical gate if and only if it
    lies in the normalizer subgroup `stabilizerNormalizer S`. -/
theorem isLogicalGate_iff_mem_stabilizerNormalizer (U : NQubitGate n) (S : StabilizerGroup n) :
    IsLogicalGate U S ↔ U ∈ stabilizerNormalizer S := by
  rw [isLogicalGate_iff_isInStabilizerNormalizer]
  rfl

/-- Logical gate depends only on the underlying stabilizer subgroup. -/
theorem isLogicalGate_iff_toSubgroup_eq (U : NQubitGate n) (S T : StabilizerGroup n)
    (h : S.toSubgroup = T.toSubgroup) : IsLogicalGate U S ↔ IsLogicalGate U T := by
  unfold IsLogicalGate
  congr! 1
  ext ψ
  simp only [IsInCodespace]
  congr! 1
  ext g
  rw [h]

end StabilizerGroup
end Quantum
