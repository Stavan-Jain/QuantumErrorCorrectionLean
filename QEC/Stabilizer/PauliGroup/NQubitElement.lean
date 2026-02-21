import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Group.Defs
import QEC.Foundations.Foundations
import QEC.Stabilizer.PauliGroupSingle
import QEC.Stabilizer.PauliGroup.NQubitOperator

namespace Quantum
open Matrix
open scoped BigOperators

/-!
# The N-Qubit Pauli Group Element

An n-qubit Pauli group element consists of a global phase and an n-qubit Pauli operator.
This extends the single-qubit Pauli group to n-qubit systems.
-/

variable {n : ℕ}

/-- An element of the n-qubit Pauli group.

The n-qubit Pauli group consists of elements of the form `i^k * (P₀ ⊗ P₁ ⊗ ... ⊗ P_{n-1})` where:
- `phasePower : Fin 4` represents the global phase:
  - k=0 → phase = 1
  - k=1 → phase = i
  - k=2 → phase = -1
  - k=3 → phase = -i
- `operators : NQubitPauliOperator n` assigns a single-qubit Pauli operator to each qubit

For n qubits, this gives 4 phases × 4^n operators = 4^(n+1) total elements.
-/
structure NQubitPauliGroupElement (n : ℕ) where
  phasePower : Fin 4  -- 0 → 1, 1 → i, 2 → -1, 3 → -i
  operators : NQubitPauliOperator n

/-- Extensionality for NQubitPauliGroupElement. -/
@[ext] theorem NQubitPauliGroupElement.ext {n : ℕ} (p q : NQubitPauliGroupElement n)
  (h_phase : p.phasePower = q.phasePower)
  (h_ops : p.operators = q.operators) : p = q := by
  cases p; cases q; congr

namespace NQubitPauliGroupElement

/-- Convert an n-qubit Pauli group element to its matrix representation.

This multiplies the global phase by the tensor product of the individual Pauli matrices.
The matrix representation is a group homomorphism: `(p * q).toMatrix = p.toMatrix * q.toMatrix`.
Derived from `toGate` by taking the underlying matrix.
-/
noncomputable def toMatrix (p : NQubitPauliGroupElement n) :
  Matrix (NQubitBasis n) (NQubitBasis n) ℂ :=
  PauliGroupElement.phasePowerToComplex p.phasePower • p.operators.toMatrix

/-- Convert an n-qubit Pauli group element to its underlying gate.

This is the primary representation connecting the Stabilizer layer to Foundations.
For `⟨k, op⟩` representing `i^k * (P₀ ⊗ ... ⊗ P_{n-1})`, we scale the base gate
`op.toGate` by the unit complex `phasePowerToUnitComplex k`.
-/
noncomputable def toGate (p : NQubitPauliGroupElement n) : QuantumGate (NQubitBasis n) :=
  PauliGroupElement.phasePowerToUnitComplex p.phasePower • (p.operators.toGate)

/-- Connection between `toGate` and `toMatrix`. -/
lemma toGate_val (p : NQubitPauliGroupElement n) : (toGate p).val = toMatrix p :=
  by simp [toMatrix, toGate, smul_UnitComplex_gate_val, NQubitPauliOperator.toGate_val,
    PauliGroupElement.phasePowerToUnitComplex_coe]

/-- The identity element of the n-qubit Pauli group: I ⊗ I ⊗ ... ⊗ I with phase 1. -/
def one (n : ℕ) : NQubitPauliGroupElement n :=
  ⟨0, NQubitPauliOperator.identity n⟩

/-- The central element `-1` of the n-qubit Pauli group: phase -1 with identity operators. -/
def minusOne (n : ℕ) : NQubitPauliGroupElement n :=
  ⟨2, NQubitPauliOperator.identity n⟩

/-- Extract the global phase power. -/
def phase (p : NQubitPauliGroupElement n) : Fin 4 := p.phasePower

/-- Extract the n-qubit Pauli operator. -/
def ops (p : NQubitPauliGroupElement n) : NQubitPauliOperator n := p.operators

/-- Construct an n-qubit Pauli group element from an operator with phase 0 (i.e., no phase). -/
def ofOperator (op : NQubitPauliOperator n) : NQubitPauliGroupElement n :=
  ⟨0, op⟩

@[simp] lemma ofOperator_phasePower (op : NQubitPauliOperator n) :
  (ofOperator op).phasePower = 0 := rfl

@[simp] lemma ofOperator_operators (op : NQubitPauliOperator n) :
  (ofOperator op).operators = op := rfl

-- Simp lemmas for the identity element
@[simp] lemma one_phasePower (n : ℕ) : (one n).phasePower = 0 := rfl
@[simp] lemma one_operators (n : ℕ) : (one n).operators = NQubitPauliOperator.identity n := rfl

-- Simp lemmas for minusOne
@[simp] lemma minusOne_phasePower (n : ℕ) : (minusOne n).phasePower = 2 := rfl
@[simp] lemma minusOne_operators (n : ℕ) : (minusOne n).operators = 
NQubitPauliOperator.identity n := rfl

/-- Get the Pauli operator at a specific qubit position. -/
def getOp (p : NQubitPauliGroupElement n) (i : Fin n) : PauliOperator :=
  p.operators i

/-- Multiplication of n-qubit Pauli operators (operator part only).

This multiplies operators qubit-by-qubit and returns:
- The total phase contribution from all qubit multiplications (mod 4)
- The resulting n-qubit operator (function mapping each qubit to its result operator)
-/
noncomputable def mulOp (p q : NQubitPauliOperator n) : NQubitPauliGroupElement n :=
  -- Multiply qubit-by-qubit
  let results : Fin n → PauliGroupElement :=
    fun i => (p i).mulOp (q i)
  -- Sum all phase contributions using Fin 4 addition
  let totalPhase := (Finset.univ : Finset (Fin n)).sum (fun i => (results i).phasePower)
  -- Construct result operator
  let resultOp : NQubitPauliOperator n := fun i => (results i).operator
  ⟨totalPhase, resultOp⟩

-- Notation for more readable proof states
/-- Notation for operator multiplication: `p *ₚ q` means `mulOp p q`. -/
infixl:70 " *ₚ " => mulOp

/-- Multiplication in the n-qubit Pauli group.

If we have `i^k * (P₀ ⊗ P₁ ⊗ ... ⊗ P_{n-1})` and `i^m * (Q₀ ⊗ Q₁ ⊗ ... ⊗ Q_{n-1})`,
their product is computed qubit-by-qubit:
- For each qubit i: P_i * Q_i = i^{p_i} * R_i
- Total phase: k + m + (sum of p_i) mod 4
- Result operator: R₀ ⊗ R₁ ⊗ ... ⊗ R_{n-1}
-/
noncomputable def mul (p q : NQubitPauliGroupElement n) : NQubitPauliGroupElement n :=
  ⟨p.phasePower + q.phasePower + (mulOp p.operators q.operators).phasePower,
  (mulOp p.operators q.operators).operators⟩

/-- The inverse of an n-qubit Pauli group element.

For `i^k * (P₀ ⊗ P₁ ⊗ ... ⊗ P_{n-1})`, the inverse is `i^(4-k mod 4) * (P₀ ⊗ P₁ ⊗ ... ⊗ P_{n-1})`
since each P_i * P_i = I for Pauli operators, so the operators remain the same and only
the phase is inverted.
-/
noncomputable def inv (p : NQubitPauliGroupElement n) : NQubitPauliGroupElement n :=
  ⟨-p.phasePower, p.operators⟩

/-- Multiplication in the n-qubit Pauli group. -/
noncomputable instance : Mul (NQubitPauliGroupElement n) := ⟨mul⟩

@[simp] lemma mul_eq (p q : NQubitPauliGroupElement n) : p * q = mul p q := rfl

/-- Inverse in the n-qubit Pauli group. -/
noncomputable instance : Inv (NQubitPauliGroupElement n) := ⟨inv⟩

@[simp] lemma inv_eq (p : NQubitPauliGroupElement n) : p⁻¹ = inv p := rfl

/-- The central element -1 is its own inverse (phase 2 satisfies 2 + 2 = 0 in Fin 4). -/
@[simp] lemma minusOne_inv (n : ℕ) : (minusOne n)⁻¹ = minusOne n := by
  ext <;> simp [inv_eq, inv, minusOne]
  decide

/-- One element of the n-qubit Pauli group. -/
noncomputable instance : One (NQubitPauliGroupElement n) := ⟨one n⟩

-- Simp lemmas for n-qubit Pauli group element definitions
@[simp] lemma one_def : (1 : NQubitPauliGroupElement n) = ⟨0, NQubitPauliOperator.identity n⟩ := rfl
@[simp] lemma one_phasePower_def (n : ℕ) : (1 : NQubitPauliGroupElement n).phasePower = 0 := rfl
@[simp] lemma one_operators_def (n : ℕ) :
(1 : NQubitPauliGroupElement n).operators = NQubitPauliOperator.identity n := rfl

/-- Helper: multiplication with identity operator gives no phase contribution. -/
lemma mulOp_identity_right_phase (op : NQubitPauliOperator n) :
  (mulOp op (NQubitPauliOperator.identity n)).phasePower = 0 := by
  unfold mulOp NQubitPauliOperator.identity
  have h : ∀ i, ((op i).mulOp PauliOperator.I).phasePower = 0 := by
    intro i
    cases op i <;> simp
  have hsum : (Finset.univ : Finset (Fin n)).sum (fun i => ((op i).mulOp
  PauliOperator.I).phasePower) = 0 := by
    rw [Finset.sum_congr rfl (fun i _ => h i)]
    simp
  simp [hsum]

/-- Helper: multiplication with identity operator on the left gives no phase contribution. -/
lemma mulOp_identity_left_phase (op : NQubitPauliOperator n) :
  (mulOp (NQubitPauliOperator.identity n) op).phasePower = 0 := by
  unfold mulOp NQubitPauliOperator.identity
  have h : ∀ i, (PauliOperator.I.mulOp (op i)).phasePower = 0 := by
    intro i
    cases op i <;> simp
  have hsum : (Finset.univ : Finset (Fin n)).sum (fun i =>
  (PauliOperator.I.mulOp (op i)).phasePower) = 0 := by
    rw [Finset.sum_congr rfl (fun i _ => h i)]
    simp
  simp [hsum]

/-- Helper: multiplication with identity operator gives same operator. -/
lemma mulOp_identity_right_op (op : NQubitPauliOperator n) :
  (mulOp op ((one n).operators)).operators = op := by
  unfold mulOp one NQubitPauliOperator.identity
  ext i
  simp
  cases op i <;> simp

/-- Helper: multiplication with identity operator on the left gives same operator. -/
lemma mulOp_identity_left_op (op : NQubitPauliOperator n) :
  (mulOp (NQubitPauliOperator.identity n) op).operators = op := by
  unfold mulOp NQubitPauliOperator.identity
  ext i
  simp
  cases op i <;> simp

/-- The identity element acts as identity on the right. -/
@[simp] lemma mul_one (p : NQubitPauliGroupElement n) : p * 1 = p := by
  have h_phase : (mulOp p.operators (NQubitPauliOperator.identity n)).phasePower = 0 :=
    mulOp_identity_right_phase p.operators
  have h_op : (mulOp p.operators (NQubitPauliOperator.identity n)).operators = p.operators :=
    mulOp_identity_right_op p.operators
  ext i
  · simp [mul, h_phase]
  · simp [mul, h_op]

/-- The identity element acts as identity on the left. -/
@[simp] lemma one_mul (p : NQubitPauliGroupElement n) : 1 * p = p := by
  have h_phase : (mulOp (NQubitPauliOperator.identity n) p.operators).phasePower = 0 :=
    mulOp_identity_left_phase p.operators
  have h_op : (mulOp (NQubitPauliOperator.identity n) p.operators).operators = p.operators :=
    mulOp_identity_left_op p.operators
  ext i
  · simp [mul, h_phase]
  · simp [mul, h_op]

/-- Helper: self-inverse property for operators. -/
private lemma mulOp_self_inv (op : NQubitPauliOperator n) :
  (mulOp op op).phasePower = 0 ∧ (mulOp op op).operators = NQubitPauliOperator.identity n := by
  constructor
  · unfold mulOp
    have h : ∀ i, ((op i).mulOp (op i)).phasePower = 0 := by
      intro i
      cases op i <;> simp
    have hsum : (Finset.univ : Finset (Fin n)).sum
      (fun i => ((op i).mulOp (op i)).phasePower) = 0 := by
      rw [Finset.sum_congr rfl (fun i _ => h i)]
      simp
    simp [hsum]
  · unfold mulOp NQubitPauliOperator.identity
    ext i
    cases h : op i <;> simp [h]

/-- Right inverse property: p * p⁻¹ = 1. -/
@[simp] lemma mul_right_inv (p : NQubitPauliGroupElement n) : p * p⁻¹ = 1 := by
  simp [mul, inv, mulOp_self_inv]

/-- Left inverse property: p⁻¹ * p = 1. -/
@[simp] lemma mul_left_inv (p : NQubitPauliGroupElement n) : p⁻¹ * p = 1 := by
  simp [mul, inv, mulOp_self_inv]

/-- Helper: associativity of n-qubit operator multiplication (operator part only). -/
private lemma mulOp_assoc_op (p q r : NQubitPauliOperator n) :
  (mulOp (mulOp p q).operators r).operators = (mulOp p (mulOp q r).operators).operators := by
  ext i
  cases h1 : (p i) <;> cases h2 : (q i) <;> cases h3 : (r i) <;> simp [mulOp, h1, h2, h3]

/-- Associativity of multiplication in the n-qubit Pauli group. -/
theorem mul_assoc (p q r : NQubitPauliGroupElement n) : (p * q) * r = p * (q * r) := by
  simp only [mul_eq, mul, mk.injEq]
  have h_op : ((p.operators *ₚ q.operators).operators *ₚ r.operators).operators =
              (p.operators *ₚ (q.operators *ₚ r.operators).operators).operators :=
    mulOp_assoc_op p.operators q.operators r.operators
  have h_phase : ((p.phasePower + q.phasePower + (p.operators *ₚ q.operators).phasePower) +
                  r.phasePower +
                  ((p.operators *ₚ q.operators).operators *ₚ r.operators).phasePower) =
                 (p.phasePower +
                 (q.phasePower + r.phasePower + (q.operators *ₚ r.operators).phasePower) +
                  (p.operators *ₚ (q.operators *ₚ r.operators).operators).phasePower) := by
    simp [add_assoc, add_comm, add_left_comm]
    simp [mulOp]
    rw [← Finset.sum_add_distrib]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    cases h : (p.operators i) <;> cases h' : (q.operators i)
    <;> cases h'' : (r.operators i) <;> simp
  constructor
  · exact h_phase
  · exact h_op

/-- The n-qubit Pauli group forms a group under multiplication. -/
noncomputable instance : Group (NQubitPauliGroupElement n) where
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  inv_mul_cancel := mul_left_inv

/-!
## Pauli weight and support

The **support** and **weight** of a group element are those of its operator part; the phase
does not affect them.
-/

/-- The support of an n-qubit Pauli group element: qubits where the operator is not I. -/
def support (p : NQubitPauliGroupElement n) : Finset (Fin n) :=
  NQubitPauliOperator.support p.operators

/-- The Pauli weight: number of qubits on which the element acts nontrivially (not I). -/
def weight (p : NQubitPauliGroupElement n) : ℕ :=
  NQubitPauliOperator.weight p.operators

/-- Support is determined by the operator part only. -/
@[simp] lemma support_ofOperator (op : NQubitPauliOperator n) :
    support (ofOperator op) = NQubitPauliOperator.support op := rfl

/-- Weight is determined by the operator part only. -/
@[simp] lemma weight_ofOperator (op : NQubitPauliOperator n) :
    weight (ofOperator op) = NQubitPauliOperator.weight op := rfl

/-- The identity element has empty support. -/
@[simp] lemma support_one (n : ℕ) : support (1 : NQubitPauliGroupElement n) = ∅ := by
  simp [support, one_def, NQubitPauliOperator.support_identity]

/-- The identity element has weight zero. -/
@[simp] lemma weight_one (n : ℕ) : weight (1 : NQubitPauliGroupElement n) = 0 := by
  simp [weight, one_def, NQubitPauliOperator.weight_identity]

/-- A qubit is in the support iff the operator at that qubit is not I. -/
lemma mem_support (p : NQubitPauliGroupElement n) (i : Fin n) :
    i ∈ support p ↔ p.operators i ≠ PauliOperator.I :=
  NQubitPauliOperator.mem_support p.operators i

/-- Weight is zero iff the operator part is the identity. (Phase is irrelevant to weight.) -/
lemma weight_eq_zero_iff (p : NQubitPauliGroupElement n) :
    weight p = 0 ↔ p.operators = NQubitPauliOperator.identity n := by
  simp [weight, NQubitPauliOperator.weight_eq_zero_iff]

end NQubitPauliGroupElement

end Quantum
