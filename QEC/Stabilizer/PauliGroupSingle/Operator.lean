import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import QEC.Foundations.Foundations
import QEC.Stabilizer.PauliGroupSingle.Core

namespace Quantum
open Matrix
open scoped BigOperators

namespace PauliOperator

/-!
# Pauli Operators: Gates, Matrices, and Multiplication
-/

/-- Convert a Pauli operator to a quantum gate.

Maps I → I, X → X, Y → Y, Z → Z (the gates defined in Foundations.Gates).
This is the primary representation for operators.
-/
noncomputable def toGate : PauliOperator → OneQubitGate
  | .I => Quantum.I
  | .X => Quantum.X
  | .Y => Quantum.Y
  | .Z => Quantum.Z

/-- Convert a Pauli operator to its corresponding matrix representation.

This is derived from `toGate` by taking the underlying matrix.
-/
noncomputable def toMatrix : PauliOperator → Matrix QubitBasis QubitBasis ℂ
  | .I => 1
  | .X => Xmat
  | .Y => Ymat
  | .Z => Zmat

/-- Connection between `toGate` and `toMatrix` for operators. -/
@[simp] lemma toGate_val (P : PauliOperator) : (P.toGate).val = P.toMatrix := by
  cases P <;> simp [toGate, toMatrix, Quantum.coe_I, Quantum.coe_X
  , Quantum.coe_Y, Quantum.coe_Z, Imat]

/-- The identity operator's matrix is the identity matrix. -/
@[simp] lemma toMatrix_I : PauliOperator.I.toMatrix = (1 : Matrix QubitBasis QubitBasis ℂ) := rfl
@[simp] lemma toMatrix_X : PauliOperator.X.toMatrix = Xmat := rfl
@[simp] lemma toMatrix_Y : PauliOperator.Y.toMatrix = Ymat := rfl
@[simp] lemma toMatrix_Z : PauliOperator.Z.toMatrix = Zmat := rfl

@[simp] lemma toGate_I : PauliOperator.I.toGate = (Quantum.I : OneQubitGate) := rfl
@[simp] lemma toGate_X : PauliOperator.X.toGate = (Quantum.X : OneQubitGate) := rfl
@[simp] lemma toGate_Y : PauliOperator.Y.toGate = (Quantum.Y : OneQubitGate) := rfl
@[simp] lemma toGate_Z : PauliOperator.Z.toGate = (Quantum.Z : OneQubitGate) := rfl

/-- Multiplication of Pauli operators, returning a Pauli group element. -/
noncomputable def mulOp : PauliOperator → PauliOperator → PauliGroupElement
  | .I, q => ⟨0, q⟩
  | p, .I => ⟨0, p⟩
  | .X, .X => ⟨0, .I⟩
  | .Y, .Y => ⟨0, .I⟩
  | .Z, .Z => ⟨0, .I⟩
  | .X, .Y => ⟨1, .Z⟩  -- X * Y = iZ
  | .Y, .X => ⟨3, .Z⟩  -- Y * X = -iZ
  | .Y, .Z => ⟨1, .X⟩  -- Y * Z = iX
  | .Z, .Y => ⟨3, .X⟩  -- Z * Y = -iX
  | .Z, .X => ⟨1, .Y⟩  -- Z * X = iY
  | .X, .Z => ⟨3, .Y⟩  -- X * Z = -iY

@[simp] lemma mulOp_I_I : PauliOperator.I.mulOp PauliOperator.I = ⟨0, PauliOperator.I⟩ := rfl
@[simp] lemma mulOp_I_X : PauliOperator.I.mulOp PauliOperator.X = ⟨0, PauliOperator.X⟩ := rfl
@[simp] lemma mulOp_I_Y : PauliOperator.I.mulOp PauliOperator.Y = ⟨0, PauliOperator.Y⟩ := rfl
@[simp] lemma mulOp_I_Z : PauliOperator.I.mulOp PauliOperator.Z = ⟨0, PauliOperator.Z⟩ := rfl
@[simp] lemma mulOp_X_I : PauliOperator.X.mulOp PauliOperator.I = ⟨0, PauliOperator.X⟩ := rfl
@[simp] lemma mulOp_X_X : PauliOperator.X.mulOp PauliOperator.X = ⟨0, PauliOperator.I⟩ := rfl
@[simp] lemma mulOp_X_Y : PauliOperator.X.mulOp PauliOperator.Y = ⟨1, PauliOperator.Z⟩ := rfl
@[simp] lemma mulOp_X_Z : PauliOperator.X.mulOp PauliOperator.Z = ⟨3, PauliOperator.Y⟩ := rfl
@[simp] lemma mulOp_Y_I : PauliOperator.Y.mulOp PauliOperator.I = ⟨0, PauliOperator.Y⟩ := rfl
@[simp] lemma mulOp_Y_X : PauliOperator.Y.mulOp PauliOperator.X = ⟨3, PauliOperator.Z⟩ := rfl
@[simp] lemma mulOp_Y_Y : PauliOperator.Y.mulOp PauliOperator.Y = ⟨0, PauliOperator.I⟩ := rfl
@[simp] lemma mulOp_Y_Z : PauliOperator.Y.mulOp PauliOperator.Z = ⟨1, PauliOperator.X⟩ := rfl
@[simp] lemma mulOp_Z_I : PauliOperator.Z.mulOp PauliOperator.I = ⟨0, PauliOperator.Z⟩ := rfl
@[simp] lemma mulOp_Z_X : PauliOperator.Z.mulOp PauliOperator.X = ⟨1, PauliOperator.Y⟩ := rfl
@[simp] lemma mulOp_Z_Y : PauliOperator.Z.mulOp PauliOperator.Y = ⟨3, PauliOperator.X⟩ := rfl
@[simp] lemma mulOp_Z_Z : PauliOperator.Z.mulOp PauliOperator.Z = ⟨0, PauliOperator.I⟩ := rfl

/-- The *operator* part of `mulOp` is commutative (the phase power may differ). -/
lemma mulOp_operator_comm (P Q : PauliOperator) :
    (P.mulOp Q).operator = (Q.mulOp P).operator := by
  cases P <;> cases Q <;> simp

/-- Swap X and Z, leave I and Y unchanged. Used for conjugation by Hadamard. -/
def swapXZ : PauliOperator → PauliOperator
  | .X => .Z
  | .Z => .X
  | p => p

end PauliOperator

end Quantum
