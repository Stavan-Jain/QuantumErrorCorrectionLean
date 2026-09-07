import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Quantum
open Matrix

/-!
# Vectors, norms, and quantum states

This file is the **linear-algebra foundation** for the QEC library: complex amplitude
vectors indexed by a finite basis, the Euclidean norm, and normalized **quantum states**
as a subtype.

## Core types

- **`Vector α`**: `α → ℂ` — not necessarily normalized; used for amplitudes and intermediates.
- **`norm`**: `√(∑ᵢ |v i|²)` — standard finite-dimensional norm; lemmas show positivity,
  scaling, and `norm_zero`.
- **`QuantumState α`**: `{ v : Vector α // norm v = 1 }` — normalized vectors only.
  Coerced to `Vector α` via `CoeTC` for convenient use in sums and matrix-vector products.

## Basis bundles

- **`QubitBasis`** (= `Fin 2`): one qubit.
- **`TwoQubitBasis`**, **`ThreeQubitBasis`**: tuple bases for 2- and 3-qubit systems
  (convenient for repetition code indexing).
- **`NQubitBasis n`**: function type `Fin n → QubitBasis` for generic n-qubit systems
  (used with stabilizer / Pauli formalism).

Standard kets **`ket0`**, **`ket1`** and basis vectors are defined here, with the scoped
Dirac notation `|0⟩`, `|01⟩`, `|0101⟩`, … (see the end of the file); `Gates.lean`
builds unitary matrices on these spaces.
-/

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Complex amplitude vector over basis `α` (not necessarily normalized). -/
abbrev Vector (α : Type*) [Fintype α] [DecidableEq α] := α → ℂ

/-- Euclidean norm of an amplitude vector: `√(∑ᵢ ‖v i‖²)`. -/
noncomputable def norm (v : Vector α) :=
  Real.sqrt (∑ i, ‖v i‖^2)

/-- Unfold `norm` into the square root of the sum of squared magnitudes. -/
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
  simp only [norm_def]
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
  simp only [norm_def, Pi.smul_apply, smul_eq_mul, Complex.norm_mul]
  have h_factor : ∑ x : α, (‖c‖ * ‖v x‖)^2 = ‖c‖^2 * ∑ x : α, ‖v x‖^2 := by
    simp [mul_pow, Finset.mul_sum]
  rw [h_factor, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-- Normalized vector: unit norm in the `norm` above (quantum state in Dirac notation). -/
abbrev QuantumState (α : Type*) [Fintype α] [DecidableEq α] :=
  { v : Vector α // norm v = 1 }

/-- The coercion of a quantum state to a vector is its `.val`. -/
lemma QuantumState.coe_val (ψ : QuantumState α) : (ψ : Vector α) = ψ.val := rfl

/-- Computational basis index for one qubit (`0` and `1`). -/
abbrev QubitBasis : Type := Fin 2

/-- Normalized 1-qubit state. -/
abbrev Qubit := QuantumState QubitBasis

/-- Unnormalized 1-qubit amplitudes (same as `Vector QubitBasis`). -/
abbrev QubitVec := QubitBasis → ℂ

/-- Computational basis ket |0⟩ = (1, 0). -/
def ket0 : Qubit := ⟨![1, 0], by simp⟩

/-- Computational basis ket |1⟩ = (0, 1). -/
def ket1 : Qubit := ⟨![0, 1], by simp⟩

/-- Basis type for 2-qubit systems using tuple representation.

This is isomorphic to `NQubitBasis 2` but uses tuples for convenience with
pattern matching and tensor products. Use `TwoQubitBasis.toNQubitBasis` to convert.
-/
abbrev TwoQubitBasis : Type := QubitBasis × QubitBasis

/-- Normalized 2-qubit state. -/
abbrev TwoQubitState : Type := QuantumState TwoQubitBasis

/-- Basis type for 3-qubit systems using tuple representation.

This is isomorphic to `NQubitBasis 3` but uses tuples for convenience with
pattern matching and tensor products. Use `ThreeQubitBasis.toNQubitBasis` to convert.
-/
abbrev ThreeQubitBasis := QubitBasis × QubitBasis × QubitBasis

/-- Unnormalized 3-qubit amplitudes (same as `Vector ThreeQubitBasis`). -/
abbrev ThreeQubitVec := ThreeQubitBasis → ℂ

/-- Normalized 3-qubit state. -/
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

/-- Convert the tuple representation `(a, b) : QubitBasis × QubitBasis` to the
function representation `NQubitBasis 2`.

Useful for connecting the tuple-based basis types with the function-based
n-qubit basis type.
-/
def TwoQubitBasis.toNQubitBasis (b : TwoQubitBasis) : NQubitBasis 2 :=
  fun i => if i = 0 then b.1 else b.2

/-- Convert the tuple representation
`(a, b, c) : QubitBasis × QubitBasis × QubitBasis` to the function
representation `NQubitBasis 3`.
-/
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

/-- The computational basis vector concentrated at `i0`: amplitude `1` at `i0`
and `0` elsewhere. -/
noncomputable def basisVec (i0 : α) : Vector α :=
  fun i => if i = i0 then (1 : ℂ) else 0

/-- Pointwise value of a basis vector. -/
@[simp] lemma basisVec_apply {α : Type*} [DecidableEq α] [Fintype α] (a x : α) :
  basisVec a x = (if x = a then 1 else 0) :=
by simp[basisVec]

/-- Dotting a vector against a basis vector reads off the corresponding component. -/
@[simp] lemma dot_basisVec_left
  {α} [Fintype α] [DecidableEq α] (v : α → ℂ) (i : α) :
  (v ⬝ᵥ basisVec i) = v i := by
  classical
  simp [dotProduct, basisVec]


open scoped BigOperators

/-- Basis vectors are normalized. -/
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
  ⟨nQubitBasisVec n b, norm_basisVec b⟩

/-- Two-qubit computational basis state |00⟩. -/
noncomputable def ket00 : TwoQubitState :=
  ⟨ basisVec ((0, 0) : TwoQubitBasis),
    norm_basisVec ((0, 0) : TwoQubitBasis) ⟩

/-- Two-qubit computational basis state |01⟩. -/
noncomputable def ket01 : TwoQubitState :=
  ⟨ basisVec ((0, 1) : TwoQubitBasis),
    norm_basisVec ((0, 1) : TwoQubitBasis) ⟩

/-- Two-qubit computational basis state |10⟩. -/
noncomputable def ket10 : TwoQubitState :=
  ⟨ basisVec ((1, 0) : TwoQubitBasis),
    norm_basisVec ((1, 0) : TwoQubitBasis) ⟩

/-- Two-qubit computational basis state |11⟩. -/
noncomputable def ket11 : TwoQubitState :=
  ⟨ basisVec ((1, 1) : TwoQubitBasis),
    norm_basisVec ((1, 1) : TwoQubitBasis) ⟩

/-- The `|+⟩` amplitude vector `(1/√2, 1/√2)` has unit norm. -/
lemma ketPlusNorm1 : norm (![1 / (Real.sqrt 2), 1 / (Real.sqrt 2)]) = 1 := by
  have h : (2⁻¹ : ℝ) + 2⁻¹ = 1 := by norm_num
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, one_div, norm_def, Fin.sum_univ_two,
    cons_val_zero, norm_inv, Complex.norm_real, Real.norm_eq_abs, inv_pow, sq_abs, Nat.ofNat_nonneg,
    Real.sq_sqrt, cons_val_one, cons_val_fin_one, Real.sqrt_eq_one]
  exact h

/-- Hadamard-basis ket |+⟩ = (|0⟩ + |1⟩)/√2. -/
noncomputable def ketPlus : Qubit := ⟨(![1 / (Real.sqrt 2), 1 / (Real.sqrt 2)]), ketPlusNorm1⟩

/-- The `|−⟩` amplitude vector `(1/√2, -1/√2)` has unit norm. -/
lemma ketMinusNorm1 : norm (![1 / (Real.sqrt 2), -(1 / (Real.sqrt 2))]) = 1 := by
  norm_num [norm_def, Fin.sum_univ_two]

/-- Hadamard-basis ket |−⟩ = (|0⟩ − |1⟩)/√2. -/
noncomputable def ketMinus : Qubit :=
  ⟨(![1 / (Real.sqrt 2), -(1 / (Real.sqrt 2))]), ketMinusNorm1⟩

/-- Three-qubit computational basis state |000⟩. -/
noncomputable def ket000 : ThreeQubitState :=
  ⟨basisVec (0, 0, 0), by
    simpa using
      (norm_basisVec (α := ThreeQubitBasis) (i0 := (0, 0, 0)))⟩

/-- Three-qubit computational basis state |001⟩. -/
noncomputable def ket001 : ThreeQubitState :=
  ⟨basisVec (0, 0, 1), by
    simpa using
      (norm_basisVec (α := ThreeQubitBasis) (i0 := (0, 0, 1)))⟩

/-- Three-qubit computational basis state |010⟩. -/
noncomputable def ket010 : ThreeQubitState :=
  ⟨basisVec (0, 1, 0), by
    simpa using
      (norm_basisVec (α := ThreeQubitBasis) (i0 := (0, 1, 0)))⟩

/-- Three-qubit computational basis state |011⟩. -/
noncomputable def ket011 : ThreeQubitState :=
  ⟨basisVec (0, 1, 1), by
    simpa using
      (norm_basisVec (α := ThreeQubitBasis) (i0 := (0, 1, 1)))⟩

/-- Three-qubit computational basis state |100⟩. -/
noncomputable def ket100 : ThreeQubitState :=
  ⟨basisVec (1, 0, 0), by
    simpa using
      (norm_basisVec (α := ThreeQubitBasis) (i0 := (1, 0, 0)))⟩

/-- Three-qubit computational basis state |101⟩. -/
noncomputable def ket101 : ThreeQubitState :=
  ⟨basisVec (1, 0, 1), by
    simpa using
      (norm_basisVec (α := ThreeQubitBasis) (i0 := (1, 0, 1)))⟩

/-- Three-qubit computational basis state |110⟩. -/
noncomputable def ket110 : ThreeQubitState :=
  ⟨basisVec (1, 1, 0), by
    simpa using
      (norm_basisVec (α := ThreeQubitBasis) (i0 := (1, 1, 0)))⟩

/-- Three-qubit computational basis state |111⟩. -/
noncomputable def ket111 : ThreeQubitState :=
  ⟨basisVec (1, 1, 1), by
    simpa using
      (norm_basisVec (α := ThreeQubitBasis) (i0 := (1, 1, 1)))⟩

/-- Amplitude vector underlying `ket000`. -/
@[simp] lemma ket000_val : (ket000 : ThreeQubitVec) = basisVec (0, 0, 0) := rfl
/-- Amplitude vector underlying `ket001`. -/
@[simp] lemma ket001_val : (ket001 : ThreeQubitVec) = basisVec (0, 0, 1) := rfl
/-- Amplitude vector underlying `ket010`. -/
@[simp] lemma ket010_val : (ket010 : ThreeQubitVec) = basisVec (0, 1, 0) := rfl
/-- Amplitude vector underlying `ket011`. -/
@[simp] lemma ket011_val : (ket011 : ThreeQubitVec) = basisVec (0, 1, 1) := rfl
/-- Amplitude vector underlying `ket100`. -/
@[simp] lemma ket100_val : (ket100 : ThreeQubitVec) = basisVec (1, 0, 0) := rfl
/-- Amplitude vector underlying `ket101`. -/
@[simp] lemma ket101_val : (ket101 : ThreeQubitVec) = basisVec (1, 0, 1) := rfl
/-- Amplitude vector underlying `ket110`. -/
@[simp] lemma ket110_val : (ket110 : ThreeQubitVec) = basisVec (1, 1, 0) := rfl
/-- Amplitude vector underlying `ket111`. -/
@[simp] lemma ket111_val : (ket111 : ThreeQubitVec) = basisVec (1, 1, 1) := rfl

/-!
## Dirac ket notation

Scoped notation for the computational-basis kets, so proofs and statements can be written
the way they are on paper: `|0⟩`, `|+⟩`, `|01⟩`, `|0101⟩`, …

`|b⟩` for a bitstring `b` of length `n ≥ 1` is the standard basis state of the
corresponding `n`-qubit state type, i.e. exactly the pre-existing term for it:

| length  | elaborates to                   | type              |
|---------|---------------------------------|-------------------|
| 1       | `ket0`, `ket1`                  | `Qubit`           |
| 2       | `ket00`, …, `ket11`             | `TwoQubitState`   |
| 3       | `ket000`, …, `ket111`           | `ThreeQubitState` |
| `n ≥ 4` | `nQubitKet n ![b₀, …, bₙ₋₁]`    | `NQubitState n`   |

The tuple-indexed state types stop at three qubits, so from four qubits on the only
`n`-qubit state type is `NQubitState n`. `|+⟩` and `|-⟩` are the Hadamard-basis kets
`ketPlus` and `ketMinus`.

**Parsing.** The bitstring lexes as a single numeral token (`0101` is one `num`
literal), and the macro reads that token's *source text* — `"0101"`, leading zeros
included, where the literal's numeric value would lose them — accepting only the digits
`0` and `1`. No new token is introduced: `|` and `⟩` are the ordinary bar and
right-angle tokens, and the whole form is `atomic`, so `|x|` (absolute value) and
`{x | p x}` (set-builder) parse exactly as before.

Bring the notation into scope with `open scoped Quantum` (or `open Quantum`). It is
`scoped` deliberately, like the rest of this file's notation, so that files which never
mention kets do not get a term-level parser on the bar token. Each ket displays back as
`|…⟩` in goals while the scope is open (`set_option pp.notation false` recovers the
names).
-/

section KetNotation

open Lean

/-- `|b⟩` for a bitstring `b` (e.g. `|0⟩`, `|01⟩`, `|0101⟩`): the computational basis
state of the `n`-qubit state type, `n` the length of `b` — `ket0`/`ket1` for one qubit,
`ket00`…`ket11` for two, `ket000`…`ket111` for three, and `nQubitKet n ![b₀, …, bₙ₋₁]`
from four qubits on. Scoped: `open scoped Quantum`. -/
scoped syntax:max (name := ketLit) atomic("|" noWs num noWs "⟩") : term

/-- The bit `0`/`1` as a numeral term (for the `![…]` of an `n ≥ 4` ket). -/
private def bitLit (c : Char) : Term :=
  ⟨(Syntax.mkNumLit (if c == '1' then "1" else "0")).raw⟩

macro_rules
  | `(|$b:num⟩) => do
    let some s := b.raw.isLit? numLitKind
      | Macro.throwErrorAt b "expected a bitstring of 0s and 1s"
    unless s.all fun c => c == '0' || c == '1' do
      Macro.throwErrorAt b s!"invalid ket bitstring '{s}': expected the digits 0 and 1 only"
    match s with
    | "0" => `(ket0)
    | "1" => `(ket1)
    | "00" => `(ket00)
    | "01" => `(ket01)
    | "10" => `(ket10)
    | "11" => `(ket11)
    | "000" => `(ket000)
    | "001" => `(ket001)
    | "010" => `(ket010)
    | "011" => `(ket011)
    | "100" => `(ket100)
    | "101" => `(ket101)
    | "110" => `(ket110)
    | "111" => `(ket111)
    | _ =>
      let bits : Syntax.TSepArray `term "," := .ofElems (s.toList.toArray.map bitLit)
      `(nQubitKet $(quote s.length) ![$bits,*])

/-- Hadamard-basis ket `|+⟩ = (|0⟩ + |1⟩)/√2`, i.e. `ketPlus`. -/
scoped notation "|+⟩" => ketPlus

/-- Hadamard-basis ket `|−⟩ = (|0⟩ − |1⟩)/√2`, i.e. `ketMinus`. -/
scoped notation "|-⟩" => ketMinus

/-! ### Display

The named kets display back as `|…⟩` (one unexpander each), and an `n ≥ 4` ket
`nQubitKet n ![b₀, …, bₙ₋₁]` with literal `n` and literal bits displays as
`|b₀…bₙ₋₁⟩`. All of these are scoped with the notation. -/

/-- `ket0` displays as `|0⟩`. -/
@[scoped app_unexpander Quantum.ket0] def unexpandKet0 : PrettyPrinter.Unexpander
  | `($_:ident) => `(|0⟩)
  | _ => throw ()

/-- `ket1` displays as `|1⟩`. -/
@[scoped app_unexpander Quantum.ket1] def unexpandKet1 : PrettyPrinter.Unexpander
  | `($_:ident) => `(|1⟩)
  | _ => throw ()

/-- `ket00` displays as `|00⟩`. -/
@[scoped app_unexpander Quantum.ket00] def unexpandKet00 : PrettyPrinter.Unexpander
  | `($_:ident) => `(|00⟩)
  | _ => throw ()

/-- `ket01` displays as `|01⟩`. -/
@[scoped app_unexpander Quantum.ket01] def unexpandKet01 : PrettyPrinter.Unexpander
  | `($_:ident) => `(|01⟩)
  | _ => throw ()

/-- `ket10` displays as `|10⟩`. -/
@[scoped app_unexpander Quantum.ket10] def unexpandKet10 : PrettyPrinter.Unexpander
  | `($_:ident) => `(|10⟩)
  | _ => throw ()

/-- `ket11` displays as `|11⟩`. -/
@[scoped app_unexpander Quantum.ket11] def unexpandKet11 : PrettyPrinter.Unexpander
  | `($_:ident) => `(|11⟩)
  | _ => throw ()

/-- `ket000` displays as `|000⟩`. -/
@[scoped app_unexpander Quantum.ket000] def unexpandKet000 : PrettyPrinter.Unexpander
  | `($_:ident) => `(|000⟩)
  | _ => throw ()

/-- `ket001` displays as `|001⟩`. -/
@[scoped app_unexpander Quantum.ket001] def unexpandKet001 : PrettyPrinter.Unexpander
  | `($_:ident) => `(|001⟩)
  | _ => throw ()

/-- `ket010` displays as `|010⟩`. -/
@[scoped app_unexpander Quantum.ket010] def unexpandKet010 : PrettyPrinter.Unexpander
  | `($_:ident) => `(|010⟩)
  | _ => throw ()

/-- `ket011` displays as `|011⟩`. -/
@[scoped app_unexpander Quantum.ket011] def unexpandKet011 : PrettyPrinter.Unexpander
  | `($_:ident) => `(|011⟩)
  | _ => throw ()

/-- `ket100` displays as `|100⟩`. -/
@[scoped app_unexpander Quantum.ket100] def unexpandKet100 : PrettyPrinter.Unexpander
  | `($_:ident) => `(|100⟩)
  | _ => throw ()

/-- `ket101` displays as `|101⟩`. -/
@[scoped app_unexpander Quantum.ket101] def unexpandKet101 : PrettyPrinter.Unexpander
  | `($_:ident) => `(|101⟩)
  | _ => throw ()

/-- `ket110` displays as `|110⟩`. -/
@[scoped app_unexpander Quantum.ket110] def unexpandKet110 : PrettyPrinter.Unexpander
  | `($_:ident) => `(|110⟩)
  | _ => throw ()

/-- `ket111` displays as `|111⟩`. -/
@[scoped app_unexpander Quantum.ket111] def unexpandKet111 : PrettyPrinter.Unexpander
  | `($_:ident) => `(|111⟩)
  | _ => throw ()

/-- A literal natural: a raw `Nat` literal or `OfNat.ofNat` of one. -/
private def natLit? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal k) => some k
  | _ =>
    if e.isAppOfArity ``OfNat.ofNat 3 then
      match e.getArg! 1 with
      | .lit (.natVal k) => some k
      | _ => none
    else none

/-- The literal bits of a `![b₀, …, bₙ₋₁]` vector (a `Matrix.vecCons` chain ending in
`Matrix.vecEmpty`), each a literal `0` or `1`; `none` on any other shape. -/
private partial def vecBits? (e : Expr) (acc : Array Nat := #[]) : Option (Array Nat) :=
  if e.isAppOfArity ``Matrix.vecCons 4 then do
    let b ← natLit? (e.getArg! 2)
    guard (b == 0 || b == 1)
    vecBits? (e.getArg! 3) (acc.push b)
  else if e.isAppOfArity ``Matrix.vecEmpty 1 then
    some acc
  else none

open PrettyPrinter Delaborator SubExpr in
/-- Delaborate `nQubitKet n ![b₀, …, bₙ₋₁]` with literal `n ≥ 4` and literal bits back to
`|b₀…bₙ₋₁⟩`. Stays silent on any other shape, and on `n ≤ 3` (where `|…⟩` denotes the
tuple-indexed kets, so displaying it would not round-trip). -/
@[scoped app_delab Quantum.nQubitKet] def delabNQubitKet : Delab :=
  whenPPOption getPPNotation <| whenNotPPOption getPPExplicit do
    let e ← getExpr
    unless e.isAppOfArity ``Quantum.nQubitKet 2 do failure
    let some n := natLit? (e.getArg! 0) | failure
    let some bits := vecBits? (e.getArg! 1) | failure
    unless bits.size == n && 4 ≤ n do failure
    let s := String.ofList (bits.toList.map fun b => if b == 1 then '1' else '0')
    `(|$(Syntax.mkNumLit s)⟩)

end KetNotation

/-!
### Round-trip tests

Each ket literal elaborates to exactly the pre-existing term.
-/

section KetRoundTrip

example : |0⟩ = ket0 := rfl
example : |1⟩ = ket1 := rfl
example : |00⟩ = ket00 := rfl
example : |01⟩ = ket01 := rfl
example : |10⟩ = ket10 := rfl
example : |11⟩ = ket11 := rfl
example : |000⟩ = ket000 := rfl
example : |101⟩ = ket101 := rfl
example : |111⟩ = ket111 := rfl
example : |0101⟩ = nQubitKet 4 ![0, 1, 0, 1] := rfl
example : |1000000⟩ = nQubitKet 7 ![1, 0, 0, 0, 0, 0, 0] := rfl
example : (|0110⟩ : NQubitState 4).val = basisVec ![0, 1, 1, 0] := rfl
example : |+⟩ = ketPlus := rfl
example : |-⟩ = ketMinus := rfl

end KetRoundTrip

end Quantum
