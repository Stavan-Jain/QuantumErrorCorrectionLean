import QEC.Stabilizer.Core.StabilizerGroup
import QEC.Stabilizer.Core.Centralizer
import QEC.Stabilizer.Core.LogicalOperators
import QEC.Stabilizer.PauliGroup.Commutation

namespace Quantum
namespace StabilizerGroup

variable {n : ℕ}

/-!
# Stabilizer codes (one logical qubit)

A **stabilizer code** bundles a stabilizer group with a choice of logical X and logical Z
operators and proofs that they behave like a logical qubit: both commute with the stabilizer
(hence preserve the codespace), anticommute with each other, and are not in the stabilizer
subgroup.

This structure captures the common pattern used in Steane7, RepetitionCode3, etc., and
allows generic lemmas about logical operators to be stated once.
-/

/-- A stabilizer code encoding one logical qubit: a stabilizer group plus logical X and Z
    with correctness proofs.

    The logical operators satisfy:
    - They lie in the centralizer (commute with every stabilizer element).
    - They anticommute with each other (so they define a logical qubit algebra).
    - Neither is in the stabilizer subgroup (so they act nontrivially on the code space).
-/
structure StabilizerCode (n : ℕ) where
  /-- The underlying stabilizer group. -/
  toStabilizerGroup : StabilizerGroup n
  /-- Logical X operator. -/
  logicalX : NQubitPauliGroupElement n
  /-- Logical Z operator. -/
  logicalZ : NQubitPauliGroupElement n
  /-- Logical X commutes with every element of the stabilizer. -/
  logicalX_mem_centralizer : logicalX ∈ centralizer toStabilizerGroup
  /-- Logical Z commutes with every element of the stabilizer. -/
  logicalZ_mem_centralizer : logicalZ ∈ centralizer toStabilizerGroup
  /-- Logical X and logical Z anticommute. -/
  logicalX_anticommutes_logicalZ : NQubitPauliGroupElement.Anticommute logicalX logicalZ

namespace StabilizerCode

/-- Coerce a stabilizer code to its underlying stabilizer group. -/
instance : Coe (StabilizerCode n) (StabilizerGroup n) :=
  ⟨toStabilizerGroup⟩

/-- Logical X is not in the stabilizer subgroup (witness: logical Z is in the centralizer
    and anticommutes with logical X). -/
theorem logicalX_not_mem_subgroup (C : StabilizerCode n) :
    C.logicalX ∉ C.toStabilizerGroup.toSubgroup :=
  not_mem_stabilizer_of_anticommutes_centralizer C.toStabilizerGroup C.logicalX C.logicalZ
    C.logicalZ_mem_centralizer C.logicalX_anticommutes_logicalZ

/-- Logical Z is not in the stabilizer subgroup (witness: logical X is in the centralizer
    and anticommutes with logical Z). -/
theorem logicalZ_not_mem_subgroup (C : StabilizerCode n) :
    C.logicalZ ∉ C.toStabilizerGroup.toSubgroup :=
  not_mem_stabilizer_of_anticommutes_centralizer C.toStabilizerGroup C.logicalZ C.logicalX
    C.logicalX_mem_centralizer (NQubitPauliGroupElement.anticommute_symm C.logicalX C.logicalZ
      C.logicalX_anticommutes_logicalZ)

/-- Logical X is a nontrivial logical operator (in centralizer, not in stabilizer). -/
theorem logicalX_nontrivial (C : StabilizerCode n) :
    IsNontrivialLogicalOperator C.logicalX C.toStabilizerGroup :=
  ⟨C.logicalX_mem_centralizer, C.logicalX_not_mem_subgroup⟩

/-- Logical Z is a nontrivial logical operator (in centralizer, not in stabilizer). -/
theorem logicalZ_nontrivial (C : StabilizerCode n) :
    IsNontrivialLogicalOperator C.logicalZ C.toStabilizerGroup :=
  ⟨C.logicalZ_mem_centralizer, C.logicalZ_not_mem_subgroup⟩

end StabilizerCode

end StabilizerGroup
end Quantum
