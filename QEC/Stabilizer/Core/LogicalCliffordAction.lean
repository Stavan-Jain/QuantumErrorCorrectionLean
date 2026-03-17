import QEC.Stabilizer.Core.LogicalOperators

namespace Quantum
namespace StabilizerGroup

variable {n : ℕ}

namespace LogicalQubitOps

/-- A gate acts as a logical Hadamard on a chosen logical qubit pair `(X̄, Z̄)` if it is a
logical gate and conjugates `X̄` to `Z̄` and `Z̄` to `X̄`. Conjugation convention is `U P U†`
(adjoint on the right). -/
def IsLogicalHadamard {S : StabilizerGroup n}
    (ops : LogicalQubitOps n S) (U : NQubitGate n) : Prop :=
  IsLogicalGate U S ∧
    conjByGate U ops.xOp.gate = ops.zOp.gate ∧
    conjByGate U ops.zOp.gate = ops.xOp.gate

/-- Matrix-bridge formulation of `IsLogicalHadamard` for compatibility with matrix-level proofs. -/
theorem isLogicalHadamard_iff_matrix {S : StabilizerGroup n}
    (ops : LogicalQubitOps n S) (U : NQubitGate n) :
    IsLogicalHadamard ops U ↔
      IsLogicalGate U S ∧
        U * ops.xOp.toMatrix * star U = ops.zOp.toMatrix ∧
        U * ops.zOp.toMatrix * star U = ops.xOp.toMatrix := by
  constructor
  · rintro ⟨hL, hx, hz⟩
    refine ⟨hL, ?_, ?_⟩
    · simpa [NQubitPauliGroupElement.gate_val] using congrArg Subtype.val hx
    · simpa [NQubitPauliGroupElement.gate_val] using congrArg Subtype.val hz
  · rintro ⟨hL, hx, hz⟩
    refine ⟨hL, ?_, ?_⟩
    · apply Subtype.ext
      simpa [NQubitPauliGroupElement.gate_val] using hx
    · apply Subtype.ext
      simpa [NQubitPauliGroupElement.gate_val] using hz

/-- Forgetting the Pauli-action equations, logical Hadamard implies logical gate. -/
theorem IsLogicalHadamard.isLogicalGate {S : StabilizerGroup n}
    {ops : LogicalQubitOps n S} {U : NQubitGate n} :
    IsLogicalHadamard ops U → IsLogicalGate U S :=
  fun h => h.1

/-- Derived logical Y from a chosen logical pair `(X̄, Z̄)`, using the convention
`Ȳ := i X̄ Z̄`. -/
noncomputable def logicalY {S : StabilizerGroup n} (ops : LogicalQubitOps n S) :
    NQubitPauliGroupElement n :=
  NQubitPauliGroupElement.phaseI n * (ops.xOp * ops.zOp)

/-- Derived `-Ȳ` from a chosen logical pair `(X̄, Z̄)`, using `-Ȳ = -i X̄ Z̄`. -/
noncomputable def logicalNegY {S : StabilizerGroup n} (ops : LogicalQubitOps n S) :
    NQubitPauliGroupElement n :=
  NQubitPauliGroupElement.phaseNegI n * (ops.xOp * ops.zOp)

/-- A gate acts as a logical phase gate `S` on a chosen logical qubit pair `(X̄, Z̄)` if it is a
logical gate, fixes `Z̄`, and sends `X̄` to `Ȳ := i X̄ Z̄`.
Conjugation convention is `U P U†` (adjoint on the right). -/
def IsLogicalS {S : StabilizerGroup n}
    (ops : LogicalQubitOps n S) (U : NQubitGate n) : Prop :=
  IsLogicalGate U S ∧
    conjByGate U ops.zOp.gate = ops.zOp.gate ∧
    conjByGate U ops.xOp.gate = (logicalY ops).gate

/-- Matrix-bridge formulation of `IsLogicalS` for compatibility with matrix-level proofs. -/
theorem isLogicalS_iff_matrix {S : StabilizerGroup n}
    (ops : LogicalQubitOps n S) (U : NQubitGate n) :
    IsLogicalS ops U ↔
      IsLogicalGate U S ∧
        U * ops.zOp.toMatrix * star U = ops.zOp.toMatrix ∧
        U * ops.xOp.toMatrix * star U = (logicalY ops).toMatrix := by
  constructor
  · rintro ⟨hL, hz, hx⟩
    refine ⟨hL, ?_, ?_⟩
    · simpa [NQubitPauliGroupElement.gate_val] using congrArg Subtype.val hz
    · simpa [NQubitPauliGroupElement.gate_val] using congrArg Subtype.val hx
  · rintro ⟨hL, hz, hx⟩
    refine ⟨hL, ?_, ?_⟩
    · apply Subtype.ext
      simpa [NQubitPauliGroupElement.gate_val] using hz
    · apply Subtype.ext
      simpa [NQubitPauliGroupElement.gate_val] using hx

/-- Forgetting the Pauli-action equations, logical `S` implies logical gate. -/
theorem IsLogicalS.isLogicalGate {S : StabilizerGroup n}
    {ops : LogicalQubitOps n S} {U : NQubitGate n} :
    IsLogicalS ops U → IsLogicalGate U S :=
  fun h => h.1

/-- A gate acts as logical inverse-phase `S†` on a chosen logical qubit pair `(X̄, Z̄)` if it is a
logical gate, fixes `Z̄`, and sends `X̄` to `-Ȳ = -i X̄ Z̄`.
Conjugation convention is `U P U†` (adjoint on the right). -/
def IsLogicalSAdjoint {S : StabilizerGroup n}
    (ops : LogicalQubitOps n S) (U : NQubitGate n) : Prop :=
  IsLogicalGate U S ∧
    conjByGate U ops.zOp.gate = ops.zOp.gate ∧
    conjByGate U ops.xOp.gate = (logicalNegY ops).gate

/-- Matrix-bridge formulation of `IsLogicalSAdjoint` for compatibility with matrix-level proofs. -/
theorem isLogicalSAdjoint_iff_matrix {S : StabilizerGroup n}
    (ops : LogicalQubitOps n S) (U : NQubitGate n) :
    IsLogicalSAdjoint ops U ↔
      IsLogicalGate U S ∧
        U.val * ops.zOp.toMatrix * star U.val = ops.zOp.toMatrix ∧
        U.val * ops.xOp.toMatrix * star U.val = (logicalNegY ops).toMatrix := by
  constructor
  · rintro ⟨hL, hz, hx⟩
    refine ⟨hL, ?_, ?_⟩
    · simpa [NQubitPauliGroupElement.gate_val] using congrArg Subtype.val hz
    · simpa [NQubitPauliGroupElement.gate_val] using congrArg Subtype.val hx
  · rintro ⟨hL, hz, hx⟩
    refine ⟨hL, ?_, ?_⟩
    · apply Subtype.ext
      simpa [NQubitPauliGroupElement.gate_val] using hz
    · apply Subtype.ext
      simpa [NQubitPauliGroupElement.gate_val] using hx

/-- Forgetting the Pauli-action equations, logical `S†` implies logical gate. -/
theorem IsLogicalSAdjoint.isLogicalGate {S : StabilizerGroup n}
    {ops : LogicalQubitOps n S} {U : NQubitGate n} :
    IsLogicalSAdjoint ops U → IsLogicalGate U S :=
  fun h => h.1

end LogicalQubitOps

end StabilizerGroup
end Quantum
