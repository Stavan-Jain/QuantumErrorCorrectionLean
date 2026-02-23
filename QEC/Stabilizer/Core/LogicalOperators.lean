import QEC.Stabilizer.Core.StabilizerGroup
import QEC.Stabilizer.Core.Centralizer
import QEC.Stabilizer.PauliGroup

namespace Quantum
namespace StabilizerGroup

variable {n : ℕ}

/-!
# Logical operators

Logical operators are Pauli group elements that preserve the codespace: they commute
with every element of the stabilizer (i.e. lie in the centralizer). Nontrivial logical
operators are those in the centralizer but not in the stabilizer. Two operators that
differ by a stabilizer element act the same on the codespace (same logical operator).
-/

/-- A nontrivial logical operator commutes with S but is not in S; it acts nontrivially
    on the logical qubits. -/
def IsNontrivialLogicalOperator (g : NQubitPauliGroupElement n) (S : StabilizerGroup n) : Prop :=
  g ∈ centralizer S ∧ g ∉ S.toSubgroup

/-- Nontrivial logical operator is unchanged when the stabilizer has the same subgroup. -/
theorem IsNontrivialLogicalOperator_of_toSubgroup_eq (g : NQubitPauliGroupElement n)
    {S T : StabilizerGroup n} (h : S.toSubgroup = T.toSubgroup) :
    (IsNontrivialLogicalOperator g S ↔ IsNontrivialLogicalOperator g T) := by
  rw [IsNontrivialLogicalOperator, IsNontrivialLogicalOperator,
    centralizer_eq_of_toSubgroup_eq S T h, h]

/-- Data for one logical qubit: a pair of logical X and Z operators that commute with
    the stabilizer and anticommute with each other. -/
structure LogicalQubitOps (n : ℕ) (S : StabilizerGroup n) where
  /-- Logical X operator. -/
  xOp : NQubitPauliGroupElement n
  /-- Logical Z operator. -/
  zOp : NQubitPauliGroupElement n
  /-- Logical X is in the centralizer of S. -/
  x_mem_centralizer : xOp ∈ centralizer S
  /-- Logical Z is in the centralizer of S. -/
  z_mem_centralizer : zOp ∈ centralizer S
  /-- X̄ and Z̄ anticommute. -/
  anticommute : NQubitPauliGroupElement.Anticommute xOp zOp

namespace LogicalQubitOps

/-- The logical X operator is not in the stabilizer. -/
theorem xOp_not_mem {S : StabilizerGroup n} (ops : LogicalQubitOps n S) :
    ops.xOp ∉ S.toSubgroup :=
  not_mem_stabilizer_of_anticommutes_centralizer S ops.xOp ops.zOp ops.z_mem_centralizer
    ops.anticommute

/-- The logical Z operator is not in the stabilizer. -/
theorem zOp_not_mem {S : StabilizerGroup n} (ops : LogicalQubitOps n S) :
    ops.zOp ∉ S.toSubgroup :=
  not_mem_stabilizer_of_anticommutes_centralizer S ops.zOp ops.xOp ops.x_mem_centralizer
    (NQubitPauliGroupElement.anticommute_symm ops.xOp ops.zOp ops.anticommute)

/-- The logical X operator is a nontrivial logical operator. -/
theorem xOp_nontrivial {S : StabilizerGroup n} (ops : LogicalQubitOps n S) :
    IsNontrivialLogicalOperator ops.xOp S := ⟨ops.x_mem_centralizer, ops.xOp_not_mem⟩

/-- The logical Z operator is a nontrivial logical operator. -/
theorem zOp_nontrivial {S : StabilizerGroup n} (ops : LogicalQubitOps n S) :
    IsNontrivialLogicalOperator ops.zOp S := ⟨ops.z_mem_centralizer, ops.zOp_not_mem⟩

end LogicalQubitOps

/-- Two Pauli elements represent the same logical operator if they differ by an element
    of the stabilizer (same coset of S in the centralizer). -/
def SameLogicalOperator (L L' : NQubitPauliGroupElement n) (S : StabilizerGroup n) : Prop :=
  L⁻¹ * L' ∈ S.toSubgroup

namespace SameLogicalOperator

theorem refl (L : NQubitPauliGroupElement n) (S : StabilizerGroup n) :
    SameLogicalOperator L L S := by
  simp only [SameLogicalOperator]
  rw [inv_mul_cancel]
  exact S.one_mem

theorem symm (S : StabilizerGroup n) {L L' : NQubitPauliGroupElement n}
    (h : SameLogicalOperator L L' S) : SameLogicalOperator L' L S := by
  simp only [SameLogicalOperator] at h ⊢
  suffices L'⁻¹ * L = (L⁻¹ * L')⁻¹ by rw [this]; exact S.inv_mem h
  rw [mul_inv_rev, inv_inv]

theorem trans (S : StabilizerGroup n) {L L' L'' : NQubitPauliGroupElement n}
    (h₁ : SameLogicalOperator L L' S) (h₂ : SameLogicalOperator L' L'' S) :
    SameLogicalOperator L L'' S := by
  simp only [SameLogicalOperator] at h₁ h₂ ⊢
  have : L⁻¹ * L'' = (L⁻¹ * L') * (L'⁻¹ * L'') := by group
  rw [this]
  exact S.mul_mem h₁ h₂

instance (S : StabilizerGroup n) : Equivalence (fun L L' => SameLogicalOperator L L' S) where
  refl L := refl L S
  symm := symm S
  trans := trans S

end SameLogicalOperator

end StabilizerGroup
end Quantum
