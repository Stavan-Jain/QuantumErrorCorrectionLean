import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic
import QEC.Stabilizer.Foundations.PauliGroupSingle.Core
import QEC.Stabilizer.Foundations.PauliGroupSingle.Operator

namespace Quantum

namespace PauliGroupElement

/-!
# The Single-Qubit Pauli Group (Abstract Structure)

This file defines the group structure on `PauliGroupElement` (one, mul, inv,
group laws).
-/

/-- The identity element of the Pauli group: I with phase 1. -/
def one : PauliGroupElement := ⟨0, PauliOperator.I⟩

/-- The Pauli operator X with phase 1. -/
def X : PauliGroupElement := ⟨0, PauliOperator.X⟩

/-- The Pauli operator Y with phase 1. -/
def Y : PauliGroupElement := ⟨0, PauliOperator.Y⟩

/-- The Pauli operator Z with phase 1. -/
def Z : PauliGroupElement := ⟨0, PauliOperator.Z⟩

/-- Multiplication in the Pauli group. -/
noncomputable def mul (p q : PauliGroupElement) : PauliGroupElement :=
  ⟨p.phasePower + q.phasePower + (p.operator.mulOp q.operator).phasePower,
   (p.operator.mulOp q.operator).operator⟩

/-- The inverse of a Pauli group element. -/
noncomputable def inv (p : PauliGroupElement) : PauliGroupElement :=
  ⟨-p.phasePower, p.operator⟩

noncomputable instance : Mul PauliGroupElement := ⟨mul⟩
noncomputable instance : Inv PauliGroupElement := ⟨inv⟩
instance : One PauliGroupElement := ⟨one⟩

@[simp] lemma mul_eq (p q : PauliGroupElement) : p * q = mul p q := rfl
@[simp] lemma inv_eq (p : PauliGroupElement) : p⁻¹ = inv p := rfl
@[simp] lemma inv_operator (p : PauliGroupElement) : (p⁻¹).operator = p.operator := rfl
@[simp] lemma one_def : (1 : PauliGroupElement) = ⟨0, PauliOperator.I⟩ := rfl
@[simp] lemma X_def : X = ⟨0, PauliOperator.X⟩ := rfl
@[simp] lemma Y_def : Y = ⟨0, PauliOperator.Y⟩ := rfl
@[simp] lemma Z_def : Z = ⟨0, PauliOperator.Z⟩ := rfl

/-- The identity element acts as identity on the right. -/
@[simp] lemma mul_one (p : PauliGroupElement) : p * 1 = p := by
  rcases p with ⟨k, op⟩
  cases op <;> simp [mul]

/-- The identity element acts as identity on the left. -/
@[simp] lemma one_mul (p : PauliGroupElement) : 1 * p = p := by
  rcases p with ⟨k, op⟩
  cases op <;> simp [mul]

/-- Right inverse property: p * p⁻¹ = 1. -/
@[simp] lemma mul_right_inv (p : PauliGroupElement) : p * p⁻¹ = 1 := by
  rcases p with ⟨k, op⟩
  cases op <;> simp [mul, inv]

/-- Left inverse property: p⁻¹ * p = 1. -/
@[simp] lemma mul_left_inv (p : PauliGroupElement) : p⁻¹ * p = 1 := by
  rcases p with ⟨k, op⟩
  cases op <;> simp [mul, inv]

/-- Associativity of Pauli operator multiplication (operator part only). -/
private lemma PauliOperator.mul_assoc_op (P Q R : PauliOperator) :
  ((P.mulOp Q).operator.mulOp R).operator = (P.mulOp (Q.mulOp R).operator).operator := by
  cases P <;> cases Q <;> cases R <;> simp

/-- Associativity of multiplication in the Pauli group. -/
theorem mul_assoc (p q r : PauliGroupElement) : (p * q) * r = p * (q * r) := by
  have h_op : ((p.operator.mulOp q.operator).operator.mulOp r.operator).operator =
              (p.operator.mulOp (q.operator.mulOp r.operator).operator).operator :=
    PauliOperator.mul_assoc_op p.operator q.operator r.operator
  have h_phase : ((p.phasePower + q.phasePower + (p.operator.mulOp q.operator).phasePower) +
                  r.phasePower +
                  ((p.operator.mulOp q.operator).operator.mulOp r.operator).phasePower) =
                 (p.phasePower +
                 (q.phasePower + r.phasePower + (q.operator.mulOp r.operator).phasePower) +
                  (p.operator.mulOp (q.operator.mulOp r.operator).operator).phasePower) := by
    simp [add_assoc, add_comm, add_left_comm]
    cases p.operator <;> cases q.operator <;> cases r.operator <;> simp
  apply PauliGroupElement.ext
  · exact h_phase
  · exact h_op

/-- The Pauli group forms a group under multiplication. -/
noncomputable instance : Group PauliGroupElement where
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  inv_mul_cancel := mul_left_inv

end PauliGroupElement

end Quantum

