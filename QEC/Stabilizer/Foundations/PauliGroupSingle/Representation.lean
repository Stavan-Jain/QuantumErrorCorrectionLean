import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Star.Basic
import QEC.Foundations.Foundations
import QEC.Stabilizer.Foundations.PauliGroupSingle.Core
import QEC.Stabilizer.Foundations.PauliGroupSingle.Operator
import QEC.Stabilizer.Foundations.PauliGroupSingle.Phase
import QEC.Stabilizer.Foundations.PauliGroupSingle.Element

namespace Quantum
open Matrix
open scoped BigOperators

namespace PauliGroupElement

/-!
# Matrix/Gate Representation
-/

/-- Matrix multiplication of Pauli operators matches their group multiplication.

For Pauli operators P and Q, if P.mulOp Q = ⟨p, R⟩, then P.toMatrix * Q.toMatrix
= phasePowerToComplex p • R.toMatrix.
-/
lemma PauliOperator.toMatrix_mul (P Q : PauliOperator) :
  P.toMatrix * Q.toMatrix =
  phasePowerToComplex (P.mulOp Q).phasePower • (P.mulOp Q).operator.toMatrix := by
  cases P <;> cases Q <;> simp
  · exact Xmat_mul_Ymat
  · simp only [Xmat_mul_Zmat, neg_smul]
  · simp only [Ymat_mul_Xmat, neg_smul]
  · simp only [Ymat_mul_Zmat]
  · simp only [Zmat_mul_Xmat]
  · simp only [Zmat_mul_Ymat, neg_smul]

/-- Convert a Pauli group element to a quantum gate. -/
noncomputable def toGate (p : PauliGroupElement) : OneQubitGate :=
  phasePowerToUnitComplex p.phasePower • (PauliOperator.toGate p.operator)

/-- Convert a Pauli group element to its matrix representation. -/
@[simp] noncomputable def toMatrix (p : PauliGroupElement) : Matrix QubitBasis QubitBasis ℂ :=
  (toGate p).val

/-- Connection between `toGate` and `toMatrix`. -/
lemma toGate_val (p : PauliGroupElement) : (toGate p).val = toMatrix p := rfl

/-- The identity group element maps to the identity matrix. -/
@[simp] lemma toMatrix_one : toMatrix (1 : PauliGroupElement) = 1 := by
  simp [toMatrix, toGate,
  one_def, PauliOperator.toGate, phasePowerToComplex_0, Quantum.coe_I, Imat]

/-- All Pauli group element matrices are unitary. -/
lemma toMatrix_mem_unitaryGroup (p : PauliGroupElement) :
  toMatrix p ∈ Matrix.unitaryGroup QubitBasis ℂ :=
  (toGate p).property

/-- The identity Pauli group element maps to the identity gate. -/
@[simp] lemma toGate_one : toGate (1 : PauliGroupElement) = (1 : OneQubitGate) := by
  apply Subtype.ext
  rw [toGate_val, toMatrix_one]
  rfl

/-- Group multiplication corresponds to matrix multiplication. -/
lemma toMatrix_mul (p q : PauliGroupElement) :
  toMatrix (p * q) = toMatrix p * toMatrix q := by
  simp only [toMatrix, toGate]
  simp [smul_smul, mul]
  rw [PauliOperator.toMatrix_mul]
  simp [smul_smul, mul_comm (phasePowerToComplex q.phasePower)]
  rw [phasePowerToComplex_add3]

/-- `toGate` is a group homomorphism. -/
lemma toGate_mul (p q : PauliGroupElement) : toGate (p * q) = toGate p * toGate q := by
  ext
  rw [toGate_val]
  have h_mul_val : (toGate p * toGate q).val = (toGate p).val * (toGate q).val := rfl
  rw [h_mul_val, toGate_val, toGate_val]
  exact congrFun (congrFun (toMatrix_mul p q) _) _

/-- `toGate` preserves inverse. -/
lemma toGate_inv (p : PauliGroupElement) : toGate (p⁻¹) = (toGate p)⁻¹ := by
  apply Subtype.ext
  rw [toGate_val, gate_inv_val (toGate p), toGate_val]
  simp only [toMatrix, toGate, smul_UnitComplex_gate_val, phasePowerToUnitComplex_coe, inv_operator]
  simp [inv]
  conv_rhs => arg 1; rw [starRingEnd_apply, phasePowerToComplex_star p.phasePower]
  congr 1
  cases p.operator <;>
  rw [PauliOperator.toMatrix, star_eq_conjTranspose] <;>
  matrix_expand [Xmat, Ymat, Zmat]

/-- Group inverse corresponds to matrix inverse. -/
lemma toMatrix_inv (p : PauliGroupElement) :
  toMatrix (p⁻¹) = (toMatrix p)⁻¹ := by
  have h_gate : toGate (p⁻¹) = (toGate p)⁻¹ := toGate_inv p
  have h_val : (toGate (p⁻¹)).val = ((toGate p)⁻¹).val := by rw [h_gate]
  rw [toGate_val, gate_inv_val (toGate p), toGate_val] at h_val
  rw [h_val, ← toGate_val, ← gate_val_inv (toGate p), toGate_val]

end PauliGroupElement

end Quantum

