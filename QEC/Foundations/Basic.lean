import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Quantum
open Matrix

/-!
# Vectors, norms, and quantum states

This file is the **linear-algebra foundation** for the QEC library: complex
amplitude vectors over a finite index type, the Euclidean norm, and normalized
**quantum states** as a subtype.

## Reading the index type `α`

Every state space in this library is `Vector α = α → ℂ` for a finite `α`. The
point to internalize is that

> `α` is *not* the state space — it **indexes the computational basis**
> of the state space.

`Vector α` is the free complex vector space on `α`, of dimension `|α|`. An
element is the tuple of amplitudes of a state *in that basis*: `v i` is the
amplitude on basis ket `i`. Each index `i : α` names one basis vector,
`basisVec i`, and these are orthonormal — `norm_basisVec` for unit length,
`dot_basisVec_left` for coordinate extraction.

Elements of `α` carry no structure beyond their identity, so choosing `α`
amounts to choosing *how to label* the `2 ^ n` computational basis states of an
`n`-qubit register. That is what the basis bundles below are: different
labelings of the same space, picked for ergonomics rather than for mathematical
content.

## Core types

- **`Vector α`** = `α → ℂ` — amplitudes, not necessarily normalized. Used for
  intermediates, and for the image of a state under a map not yet known to be
  unitary.
- **`norm v`** = `√(∑ᵢ ‖v i‖²)` — the Euclidean (L²) norm. Note this is
  deliberately *not* mathlib's `‖·‖` on `α → ℂ`, which is the **sup** norm
  (`Pi.norm_def`); mathlib puts the L² norm on the type synonym
  `EuclideanSpace ℂ α`, which this library does not use. Lemmas below give
  non-negativity, `norm_zero`, homogeneity (`norm_smul`), and the bridges
  between `norm` and `norm ^ 2`.
- **`QuantumState α`** = `{ v : Vector α // norm v = 1 }` — the unit sphere of
  `Vector α`. Global phase is *not* quotiented out: `ψ` and `-ψ` are distinct
  terms. Recover the amplitudes with the subtype coercion `(ψ : Vector α)`,
  which `QuantumState.coe_val` identifies with `ψ.val`.

## Basis bundles

Concrete choices of `α`, each of size `2 ^ n`, hence all giving the same ambient
space up to isomorphism. They differ only in how convenient they are to compute
with:

- **`QubitBasis`** = `Fin 2`, size `2` — a single qubit.
- **`TwoQubitBasis`** = `QubitBasis × QubitBasis`, size `4` — pattern matching,
  and `tensorGate` in `Tensor.lean`.
- **`ThreeQubitBasis`** = `QubitBasis × QubitBasis × QubitBasis`, size `8` — the
  same, e.g. for indexing the 3-qubit repetition code.
- **`NQubitBasis n`** = `Fin n → QubitBasis`, size `2 ^ n` — generic `n`, and
  the only bundle that indexes *by qubit position*, which is what the Pauli /
  stabilizer layer needs.

The tuple bundles stop at three qubits, which is where writing them out stops
paying; from four on, `NQubitBasis n` is the only option. The isomorphisms
between the two styles are witnessed by `TwoQubitBasis.toNQubitBasis` and
`ThreeQubitBasis.toNQubitBasis`, with inverses `NQubitBasis.toTwoQubitBasis` and
`NQubitBasis.toThreeQubitBasis`.

Each bundle comes with abbreviations for its vector and state types: `QubitVec`
/ `Qubit`, `TwoQubitState`, `ThreeQubitVec` / `ThreeQubitState`, and
`NQubitVec n` / `NQubitState n`. (There is no `TwoQubitVec`; spell it
`Vector TwoQubitBasis`.)

## Kets

`basisVec i` is the standard basis vector at index `i`, and `nQubitKet n b`
packages it as a `QuantumState`. The named kets are the concrete cases: `ket0`,
`ket1` for one qubit, `ket00`–`ket11` for two, `ket000`–`ket111` for three, plus
the Hadamard-basis `ketPlus` and `ketMinus`. The scoped Dirac notation for all
of them (`|0⟩`, `|01⟩`, `|0101⟩`, …) lives in `KetNotation.lean`; `Gates.lean`
builds the unitary matrices that act on these spaces.
-/
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Complex amplitude vector whose computational basis is indexed by `α`: the
free `ℂ`-vector space on `α`, of dimension `|α|`. `v i` is the amplitude on
basis ket `i`. Not necessarily normalized — see `QuantumState` for the unit-norm
subtype. -/
abbrev Vector (α : Type*) [Fintype α] [DecidableEq α] := α → ℂ

/-- Euclidean (L²) norm of an amplitude vector: `√(∑ᵢ ‖v i‖²)`.

Defined here rather than taken from mathlib because `Vector α` is a plain Pi
type, and mathlib's `‖·‖` on `α → ℂ` is the **sup** norm, not this one. See the
module docstring. -/
noncomputable def norm (v : Vector α) :=
  Real.sqrt (∑ i, ‖v i‖^2)

/-- Definitional unfolding of `norm`, as a `simp` lemma:
`norm v = √(∑ᵢ ‖v i‖²)`. -/
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

/-- Squaring cancels the square root: `(norm v) ^ 2 = ∑ᵢ ‖v i‖²`. The usual way
to discharge a norm goal without reasoning about `Real.sqrt`. -/
lemma norm_sq_def {v : Vector α} : (norm v)^2 = ∑ i, ‖v i‖^2 := by
  simp only [norm_def]
  rw [Real.sq_sqrt]
  apply Finset.sum_nonneg
  intro i _
  apply sq_nonneg

/-- Norms may be compared through their squares:
`norm v = norm w ↔ (norm v)² = (norm w)²`. Sound in both directions because
`norm` is non-negative (`norm_nonneg`). -/
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

/-- Absolute homogeneity: `norm (c • v) = ‖c‖ * norm v` for a complex scalar
`c`. This is what makes `(norm v)⁻¹ • v` a unit vector for `v ≠ 0`. -/
lemma norm_smul (c : ℂ) (v : Vector α) : norm (c • v) = ‖c‖ * norm v := by
  simp only [norm_def, Pi.smul_apply, smul_eq_mul, Complex.norm_mul]
  have h_factor : ∑ x : α, (‖c‖ * ‖v x‖)^2 = ‖c‖^2 * ∑ x : α, ‖v x‖^2 := by
    simp [mul_pow, Finset.mul_sum]
  rw [h_factor, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-- A quantum state over the basis indexed by `α`: an amplitude vector of unit
`norm`, i.e. a point of the unit sphere of `Vector α`, bundled with its
normalization proof.

Global phase is not quotiented out — `ψ` and `-ψ` are distinct terms of this
type. -/
abbrev QuantumState (α : Type*) [Fintype α] [DecidableEq α] :=
  { v : Vector α // norm v = 1 }

/-- The subtype coercion `(ψ : Vector α)` is just the underlying amplitude
vector `ψ.val`. There is no bespoke `Coe` instance; this lemma exists so that
goals stated with the coercion and goals stated with `.val` can be rewritten
into one another. -/
lemma QuantumState.coe_val (ψ : QuantumState α) : (ψ : Vector α) = ψ.val := rfl

/-- Index type for the computational basis of a single qubit: the two indices
`0` and `1` name the basis kets `|0⟩` and `|1⟩`. -/
abbrev QubitBasis : Type := Fin 2

/-- Normalized 1-qubit state. -/
abbrev Qubit := QuantumState QubitBasis

/-- Unnormalized 1-qubit amplitudes. Definitionally `Vector QubitBasis`, spelled
out here so that the arrow is visible at use sites. -/
abbrev QubitVec := QubitBasis → ℂ

/-- Computational basis ket `|0⟩`, amplitudes `(1, 0)`. -/
def ket0 : Qubit := ⟨![1, 0], by simp⟩

/-- Computational basis ket `|1⟩`, amplitudes `(0, 1)`. -/
def ket1 : Qubit := ⟨![0, 1], by simp⟩

/-- Index type for the computational basis of a 2-qubit system, labelling the
four basis kets by pairs: `(0, 0)` names `|00⟩`, `(1, 0)` names `|10⟩`, and so
on.

Isomorphic to `NQubitBasis 2`, but the tuple shape pattern-matches and composes
with `tensorGate` more readily. Convert with `TwoQubitBasis.toNQubitBasis` and
back with `NQubitBasis.toTwoQubitBasis`.
-/
abbrev TwoQubitBasis : Type := QubitBasis × QubitBasis

/-- Normalized 2-qubit state. -/
abbrev TwoQubitState : Type := QuantumState TwoQubitBasis

/-- Index type for the computational basis of a 3-qubit system, labelling the
eight basis kets by triples: `(0, 0, 1)` names `|001⟩`, and so on.

Isomorphic to `NQubitBasis 3`, with the same trade-off as `TwoQubitBasis`.
Convert with `ThreeQubitBasis.toNQubitBasis` and back with
`NQubitBasis.toThreeQubitBasis`.
-/
abbrev ThreeQubitBasis := QubitBasis × QubitBasis × QubitBasis

/-- Unnormalized 3-qubit amplitudes. Definitionally `Vector ThreeQubitBasis`. -/
abbrev ThreeQubitVec := ThreeQubitBasis → ℂ

/-- Normalized 3-qubit state. -/
abbrev ThreeQubitState := QuantumState ThreeQubitBasis

/-!
## `n`-qubit basis types

The generic bundle, extending `TwoQubitBasis` / `ThreeQubitBasis` to arbitrary
`n` by labelling basis kets with *functions from qubit position to bit* rather
than tuples. This is the labeling the stabilizer layer uses, because a Pauli
operator acts qubit-wise and so wants its index to be addressable by position.
-/

/-- Index type for the computational basis of an `n`-qubit system: a basis ket
is labelled by the bitstring naming it, presented as a function from qubit
position to bit. So `b : NQubitBasis n` is the ket `|b 0 , b 1 , … , b (n-1)⟩`,
and there are `2 ^ n` of them. `basisVec b` is the corresponding vector,
`nQubitKet n b` the corresponding state.

For `n = 2` the bitstrings are the four `Fin 2 → Fin 2` literals: `![0, 0]`
labels `|00⟩`, `![1, 0]` labels `|10⟩`, `![0, 1]` labels `|01⟩`, `![1, 1]`
labels `|11⟩`.

**When to use this rather than a tuple bundle:**
- `NQubitBasis n` for generic `n`, and whenever an index must be read *by qubit
  position* — everything in the Pauli / stabilizer layer.
- `TwoQubitBasis` / `ThreeQubitBasis` for small fixed `n`, where tuples
  pattern-match more directly and interoperate with `tensorGate`.

The two styles agree where both apply: `NQubitBasis 2 ≃ TwoQubitBasis` and
`NQubitBasis 3 ≃ ThreeQubitBasis`, via the four conversion functions below.
-/
abbrev NQubitBasis (n : ℕ) : Type := Fin n → QubitBasis

/-- Unnormalized amplitudes of an `n`-qubit system: `2 ^ n` complex numbers,
indexed by `NQubitBasis n`. -/
abbrev NQubitVec (n : ℕ) : Type := Vector (NQubitBasis n)

/-- A normalized `n`-qubit state: an `NQubitVec n` of unit `norm`. -/
abbrev NQubitState (n : ℕ) : Type := QuantumState (NQubitBasis n)

/-- Name a basis index by giving each qubit's bit. Definitionally the identity
on `Fin n → QubitBasis`; it exists only to mark intent at call sites, where a
bare lambda would not say which of the two roles the function is playing.
-/
def nQubitBasisOf (n : ℕ) (f : Fin n → QubitBasis) : NQubitBasis n := f

/-- Relabel a 2-qubit basis index from the tuple form to the by-position form:
`(a, b) ↦ ![a, b]`. Inverse to `NQubitBasis.toTwoQubitBasis`.
-/
def TwoQubitBasis.toNQubitBasis (b : TwoQubitBasis) : NQubitBasis 2 :=
  fun i => if i = 0 then b.1 else b.2

/-- Relabel a 3-qubit basis index from the tuple form to the by-position form:
`(a, b, c) ↦ ![a, b, c]`. Inverse to `NQubitBasis.toThreeQubitBasis`.
-/
def ThreeQubitBasis.toNQubitBasis (b : ThreeQubitBasis) : NQubitBasis 3 :=
  fun i => if i = 0 then b.1 else if i = 1 then b.2.1 else b.2.2

/-- Relabel a 2-qubit basis index back to tuple form: `b ↦ (b 0, b 1)`. Inverse
to `TwoQubitBasis.toNQubitBasis`. -/
def NQubitBasis.toTwoQubitBasis (b : NQubitBasis 2) : TwoQubitBasis :=
  (b 0, b 1)

/-- Relabel a 3-qubit basis index back to tuple form: `b ↦ (b 0, b 1, b 2)`.
Inverse to `ThreeQubitBasis.toNQubitBasis`. -/
def NQubitBasis.toThreeQubitBasis (b : NQubitBasis 3) : ThreeQubitBasis :=
  (b 0, b 1, b 2)

/-- The constant bitstring: the basis index labelling `|q q … q⟩`, every qubit
carrying the same bit `q`. Specialized below to `nQubitBasisZeros` and
`nQubitBasisOnes`.
-/
def nQubitBasisAll (n : ℕ) (q : QubitBasis) : NQubitBasis n :=
  fun _ => q

/-- The all-zeros basis index, labelling `|00…0⟩` on `n` qubits. -/
def nQubitBasisZeros (n : ℕ) : NQubitBasis n :=
  nQubitBasisAll n 0

/-- The all-ones basis index, labelling `|11…1⟩` on `n` qubits. -/
def nQubitBasisOnes (n : ℕ) : NQubitBasis n :=
  nQubitBasisAll n 1

/-- The standard basis vector `e_{i0}`: amplitude `1` on basis ket `i0`, `0` on
every other. As `i0` ranges over `α` these form an orthonormal basis of
`Vector α` — unit length by `norm_basisVec`, and orthonormal by
`dot_basisVec_left`. -/
noncomputable def basisVec (i0 : α) : Vector α :=
  fun i => if i = i0 then (1 : ℂ) else 0

/-- Amplitude of the basis vector `basisVec a` on basis ket `x`: `1` when
`x = a`, else `0`. Note the equality is oriented `x = a`, query index on the
left. -/
@[simp] lemma basisVec_apply {α : Type*} [DecidableEq α] [Fintype α] (a x : α) :
  basisVec a x = (if x = a then 1 else 0) :=
by simp[basisVec]

/-- `v ⬝ᵥ basisVec i = v i`: pairing a vector with the `i`-th standard basis
vector extracts its `i`-th amplitude. Equivalently, `basisVec i` represents the
`i`-th coordinate functional.

A caveat worth stating explicitly in a quantum setting: `⬝ᵥ` is
`Matrix.dotProduct`, defined as the **bilinear** form `∑ⱼ v j * w j`. It takes
no complex conjugate, so it is *not* the Hermitian inner product
`⟪v, w⟫ = ∑ⱼ conj (v j) * w j`. The two happen to agree here only because
`basisVec i` has real entries. -/
@[simp] lemma dot_basisVec_left
  {α} [Fintype α] [DecidableEq α] (v : α → ℂ) (i : α) :
  (v ⬝ᵥ basisVec i) = v i := by
  classical
  simp [dotProduct, basisVec]


open scoped BigOperators

/-- Every standard basis vector has unit length, so it is a legitimate
`QuantumState`. This is the normalization proof carried by `nQubitKet` and by
each named ket below. -/
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

/-- `basisVec` at the `n`-qubit basis type: the amplitude vector of the
computational basis ket labelled by the bitstring `b`.
-/
noncomputable def nQubitBasisVec (n : ℕ) (b : NQubitBasis n) : NQubitVec n :=
  basisVec b

/-- The computational basis ket `|b 0 , b 1 , … , b (n-1)⟩` as a normalized
state: `nQubitBasisVec n b` paired with its unit-norm proof from
`norm_basisVec`.

This is what the Dirac notation in `KetNotation.lean` elaborates to for `n ≥ 4`.
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

end Quantum
