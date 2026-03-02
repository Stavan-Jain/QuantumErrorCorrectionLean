import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Quantum
open Matrix

variable {α : Type*} [Fintype α] [DecidableEq α]
abbrev Vector (α : Type*) [Fintype α] [DecidableEq α] := α → ℂ

noncomputable def norm (v : Vector α) :=
  Real.sqrt (∑ i, ‖v i‖^2)

@[simp] lemma norm_def {v : Vector α} : norm v = Real.sqrt (∑ i, ‖v i‖^2) := rfl

/-- The norm is always non-negative. -/
lemma norm_nonneg {v : Vector α} : 0 ≤ norm v := by
  simp only [norm]
  exact Real.sqrt_nonneg _

/-- The norm of the zero vector is zero. -/
lemma norm_zero : norm (0 : Vector α) = 0 := by
  rw [norm_def]
  have h_sum : (∑ i, ‖(0 : Vector α) i‖^2) = 0 := Finset.sum_eq_zero (fun i _ => by simp)
  rw [h_sum, Real.sqrt_zero]

/-- The square of the norm equals the sum of squared magnitudes. -/
lemma norm_sq_def {v : Vector α} : (norm v)^2 = ∑ i, ‖v i‖^2 := by
  simp [norm]
  rw [Real.sq_sqrt]
  apply Finset.sum_nonneg
  intro i _
  apply sq_nonneg

/-- Two vectors have equal norms if and only if their norm squares are equal. -/
lemma norm_eq_iff_norm_sq_eq {v w : Vector α} :
  norm v = norm w ↔ (norm v)^2 = (norm w)^2 := by
  constructor
  · intro h; rw [h]
  · intro h
    have hvn : 0 ≤ norm v := norm_nonneg
    have hwn : 0 ≤ norm w := norm_nonneg
    rw [norm_sq_def, norm_sq_def] at h
    have hsqrt_eq : Real.sqrt (∑ i, ‖v i‖^2) = Real.sqrt (∑ i, ‖w i‖^2) := by
      rw [h]
    rw [← norm_def, ← norm_def] at hsqrt_eq
    exact hsqrt_eq

/-- Scaling a vector by a scalar scales its norm by the magnitude of the scalar. -/
lemma norm_smul (c : ℂ) (v : Vector α) : norm (c • v) = ‖c‖ * norm v := by
  simp [norm]
  have h_factor : ∑ x : α, (‖c‖ * ‖v x‖)^2 = ‖c‖^2 * ∑ x : α, ‖v x‖^2 := by
    simp [mul_pow, Finset.mul_sum]
  rw [h_factor, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

abbrev QuantumState (α : Type*) [Fintype α] [DecidableEq α] :=
  { v : Vector α // norm v = 1 }

-- Coerce a quantum state to its underlying vector
instance : CoeTC (QuantumState α) (Vector α) := ⟨Subtype.val⟩

/-- The coercion of a quantum state to a vector is its `.val`. -/
lemma QuantumState.coe_val (ψ : QuantumState α) : (ψ : Vector α) = ψ.val := rfl

abbrev QubitBasis : Type := Fin 2

abbrev Qubit := QuantumState QubitBasis
abbrev QubitVec := QubitBasis → ℂ

def ket0 : Qubit := ⟨![1, 0], by simp⟩

def ket1 : Qubit := ⟨![0, 1], by simp⟩

/-- Basis type for 2-qubit systems using tuple representation.

This is isomorphic to `NQubitBasis 2` but uses tuples for convenience with
pattern matching and tensor products. Use `TwoQubitBasis.toNQubitBasis` to convert.
-/
abbrev TwoQubitBasis : Type := QubitBasis × QubitBasis
abbrev TwoQubitState : Type := QuantumState TwoQubitBasis

/-- Basis type for 3-qubit systems using tuple representation.

This is isomorphic to `NQubitBasis 3` but uses tuples for convenience with
pattern matching and tensor products. Use `ThreeQubitBasis.toNQubitBasis` to convert.
-/
abbrev ThreeQubitBasis := QubitBasis × QubitBasis × QubitBasis
abbrev ThreeQubitVec := ThreeQubitBasis → ℂ
abbrev ThreeQubitState := QuantumState ThreeQubitBasis

/-!
# N-Qubit Basis Types

Generic basis types for n-qubit systems, extending the pattern of `TwoQubitBasis` and
`ThreeQubitBasis` to arbitrary n.
-/

/-- The basis type for an n-qubit system.

This represents the computational basis states as functions from qubit positions
to individual qubit basis states. For n qubits, there are 2^n basis states.

**When to use:**
- Use `NQubitBasis n` for generic n-qubit operations (e.g., n-qubit Pauli groups)
- Use `TwoQubitBasis` / `ThreeQubitBasis` for small fixed n
  (better pattern matching, works with `tensorGate`)

**Relationship:**
- `NQubitBasis 2` is isomorphic to `TwoQubitBasis` (use conversion functions)
- `NQubitBasis 3` is isomorphic to `ThreeQubitBasis` (use conversion functions)

Example: For n=2, this is isomorphic to `TwoQubitBasis`:
- `fun i => if i = 0 then 0 else 0` represents |00⟩
- `fun i => if i = 0 then 1 else 0` represents |10⟩
- etc.
-/
abbrev NQubitBasis (n : ℕ) : Type := Fin n → QubitBasis

/-- Vector type for n-qubit systems. -/
abbrev NQubitVec (n : ℕ) : Type := Vector (NQubitBasis n)

/-- Quantum state type for n-qubit systems. -/
abbrev NQubitState (n : ℕ) : Type := QuantumState (NQubitBasis n)

/-- Construct an n-qubit basis state from a function specifying each qubit's state.

This is a convenience constructor that makes it easier to work with n-qubit basis states.
-/
def nQubitBasisOf (n : ℕ) (f : Fin n → QubitBasis) : NQubitBasis n := f

/-- Convert a tuple representation to function representation for small n.

For n=2, converts `(a, b) : QubitBasis × QubitBasis` to `NQubitBasis 2`.
For n=3, converts `(a, b, c) : QubitBasis × QubitBasis × QubitBasis` to `NQubitBasis 3`.

These are useful for connecting the existing tuple-based basis types with
the new function-based n-qubit basis type.
-/
def TwoQubitBasis.toNQubitBasis (b : TwoQubitBasis) : NQubitBasis 2 :=
  fun i => if i = 0 then b.1 else b.2

def ThreeQubitBasis.toNQubitBasis (b : ThreeQubitBasis) : NQubitBasis 3 :=
  fun i => if i = 0 then b.1 else if i = 1 then b.2.1 else b.2.2

/-- Convert from function representation back to tuple for n=2. -/
def NQubitBasis.toTwoQubitBasis (b : NQubitBasis 2) : TwoQubitBasis :=
  (b 0, b 1)

/-- Convert from function representation back to tuple for n=3. -/
def NQubitBasis.toThreeQubitBasis (b : NQubitBasis 3) : ThreeQubitBasis :=
  (b 0, b 1, b 2)

/-- Helper to construct an n-qubit basis state where all qubits are in the same state.

Useful for creating states like |00...0⟩ or |11...1⟩.
-/
def nQubitBasisAll (n : ℕ) (q : QubitBasis) : NQubitBasis n :=
  fun _ => q

/-- The all-zeros basis state |00...0⟩ for n qubits. -/
def nQubitBasisZeros (n : ℕ) : NQubitBasis n :=
  nQubitBasisAll n 0

/-- The all-ones basis state |11...1⟩ for n qubits. -/
def nQubitBasisOnes (n : ℕ) : NQubitBasis n :=
  nQubitBasisAll n 1

-- The "constructor" for basis vectors
noncomputable def basisVec (i0 : α) : Vector α :=
  fun i => if i = i0 then (1 : ℂ) else 0

@[simp] lemma basisVec_apply {α : Type*} [DecidableEq α] [Fintype α] (a x : α) :
  basisVec a x = (if x = a then 1 else 0) :=
by simp[basisVec]

@[simp] lemma dot_basisVec_left
  {α} [Fintype α] [DecidableEq α] (v : α → ℂ) (i : α) :
  (v ⬝ᵥ basisVec i) = v i := by
  classical
  simp [dotProduct, basisVec]


open scoped BigOperators

lemma norm_basisVec {α : Type*} [Fintype α] [DecidableEq α] (i0 : α) :
  norm (basisVec i0 : α → ℂ) = 1 := by
  classical
  have hsum : (∑ x : α, ‖(basisVec i0 : α → ℂ) x‖ ^ 2 : ℝ) = 1 := by
    have hstep : (∑ x : α, ‖(basisVec i0 : α → ℂ) x‖ ^ 2 : ℝ) =
                 ∑ x : α, (if x = i0 then (1 : ℝ) else 0) := by
      refine Finset.sum_congr rfl ?_
      intro x _
      by_cases h : x = i0
      · subst h; simp [basisVec]
      · simp [basisVec, h]
    rw [hstep]
    simp [Finset.mem_univ]
  rw [norm, hsum, Real.sqrt_one]

/-- Construct a basis vector for an n-qubit system.

This is a specialization of `basisVec` for n-qubit systems, using the n-qubit basis type.
-/
noncomputable def nQubitBasisVec (n : ℕ) (b : NQubitBasis n) : NQubitVec n :=
  basisVec b

/-- Construct a normalized basis state for an n-qubit system.

This creates a quantum state corresponding to a computational basis vector.
-/
noncomputable def nQubitKet (n : ℕ) (b : NQubitBasis n) : NQubitState n :=
  ⟨nQubitBasisVec n b, by simpa using norm_basisVec b⟩

noncomputable def ket00 : TwoQubitState :=
  ⟨ basisVec ((0, 0) : TwoQubitBasis),
    by simpa using norm_basisVec ((0, 0) : TwoQubitBasis) ⟩

noncomputable def ket01 : TwoQubitState :=
  ⟨ basisVec ((0, 1) : TwoQubitBasis),
    by simpa using norm_basisVec ((0, 1) : TwoQubitBasis) ⟩

noncomputable def ket10 : TwoQubitState :=
  ⟨ basisVec ((1, 0) : TwoQubitBasis),
    by simpa using norm_basisVec ((1, 0) : TwoQubitBasis) ⟩

noncomputable def ket11 : TwoQubitState :=
  ⟨ basisVec ((1, 1) : TwoQubitBasis),
    by simpa using norm_basisVec ((1, 1) : TwoQubitBasis) ⟩

lemma ketPlusNorm1 : norm (![1 / (Real.sqrt 2), 1 / (Real.sqrt 2)]) = 1 := by
  have h : (2⁻¹ : ℝ) + 2⁻¹ = 1 := by norm_num
  simp
  exact h

noncomputable def ketPlus : Qubit := ⟨(![1 / (Real.sqrt 2), 1 / (Real.sqrt 2)]), ketPlusNorm1⟩

noncomputable def ket000 : ThreeQubitState :=
  ⟨basisVec (0, 0, 0), by
    simpa using
      (norm_basisVec (α := ThreeQubitBasis) (i0 := (0, 0, 0)))⟩

noncomputable def ket001 : ThreeQubitState :=
  ⟨basisVec (0, 0, 1), by
    simpa using
      (norm_basisVec (α := ThreeQubitBasis) (i0 := (0, 0, 1)))⟩

noncomputable def ket010 : ThreeQubitState :=
  ⟨basisVec (0, 1, 0), by
    simpa using
      (norm_basisVec (α := ThreeQubitBasis) (i0 := (0, 1, 0)))⟩

noncomputable def ket011 : ThreeQubitState :=
  ⟨basisVec (0, 1, 1), by
    simpa using
      (norm_basisVec (α := ThreeQubitBasis) (i0 := (0, 1, 1)))⟩

noncomputable def ket100 : ThreeQubitState :=
  ⟨basisVec (1, 0, 0), by
    simpa using
      (norm_basisVec (α := ThreeQubitBasis) (i0 := (1, 0, 0)))⟩

noncomputable def ket101 : ThreeQubitState :=
  ⟨basisVec (1, 0, 1), by
    simpa using
      (norm_basisVec (α := ThreeQubitBasis) (i0 := (1, 0, 1)))⟩

noncomputable def ket110 : ThreeQubitState :=
  ⟨basisVec (1, 1, 0), by
    simpa using
      (norm_basisVec (α := ThreeQubitBasis) (i0 := (1, 1, 0)))⟩

noncomputable def ket111 : ThreeQubitState :=
  ⟨basisVec (1, 1, 1), by
    simpa using
      (norm_basisVec (α := ThreeQubitBasis) (i0 := (1, 1, 1)))⟩

@[simp] lemma ket000_val : (ket000 : ThreeQubitVec) = basisVec (0, 0, 0) := rfl
@[simp] lemma ket001_val : (ket001 : ThreeQubitVec) = basisVec (0, 0, 1) := rfl
@[simp] lemma ket010_val : (ket010 : ThreeQubitVec) = basisVec (0, 1, 0) := rfl
@[simp] lemma ket011_val : (ket011 : ThreeQubitVec) = basisVec (0, 1, 1) := rfl
@[simp] lemma ket100_val : (ket100 : ThreeQubitVec) = basisVec (1, 0, 0) := rfl
@[simp] lemma ket101_val : (ket101 : ThreeQubitVec) = basisVec (1, 0, 1) := rfl
@[simp] lemma ket110_val : (ket110 : ThreeQubitVec) = basisVec (1, 1, 0) := rfl
@[simp] lemma ket111_val : (ket111 : ThreeQubitVec) = basisVec (1, 1, 1) := rfl

end Quantum
