import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.LinearAlgebra.UnitaryGroup
import QEC.Foundations.Basic

namespace Quantum
open Matrix

/-!
# Unitary gates as matrices

This file builds the **gate** layer on top of `Basic.lean`: unitary matrices acting on
finite-dimensional complex Hilbert spaces indexed by a basis type `α`.

## Main idea

- A **`QuantumGate α`** is an element of `Matrix.unitaryGroup α ℂ`: a matrix `U` with
  `Uᴴ U = 1` (stored as a subtype with the unitary proof).
- **Composition** is matrix multiplication; **inverse** is conjugate transpose (`star`),
  see lemmas `gate_inv_val`, `gate_val_inv`, `gate_mul_val`.
- Fixed sizes use the basis types from `Basic`: `QubitBasis` (Fin 2), `TwoQubitBasis`,
  `ThreeQubitBasis`, and parametric `NQubitBasis n` for `NQubitGate n`.

## Contents

- Abbreviations `OneQubitGate`, `TwoQubitGate`, `ThreeQubitGate`, `NQubitGate n`.
- `UnitComplex` and phase factors for controlled/phase gates.
- Concrete gates (Pauli, Hadamard, CNOT, etc.) and tensor-product style combinators
  used by the repetition code and stabilizer formalism.

Depends on `Basic.lean` for `QubitBasis`, `NQubitBasis`, and state types.
-/

/-- A unitary gate on basis `α`: matrix `U` with `Uᴴ U = 1`. -/
abbrev QuantumGate (α : Type*) [DecidableEq α] [Fintype α] :=
  Matrix.unitaryGroup α ℂ

/-- Single-qubit gates: 2×2 unitaries in the computational basis. -/
abbrev OneQubitGate : Type :=
  QuantumGate QubitBasis

/-- Two-qubit gates: unitaries on `QubitBasis × QubitBasis`. -/
abbrev TwoQubitGate : Type := QuantumGate TwoQubitBasis

/-- Three-qubit gates: unitaries on `ThreeQubitBasis` (product of three qubit bases). -/
abbrev ThreeQubitGate : Type := QuantumGate ThreeQubitBasis

/-- Gate type for n-qubit systems (indexed by NQubitBasis n). -/
abbrev NQubitGate (n : ℕ) : Type := QuantumGate (NQubitBasis n)

/-- The matrix underlying the inverse of a gate is the conjugate transpose. -/
@[simp] lemma gate_inv_val
  {α : Type*} [Fintype α] [DecidableEq α]
  (G : QuantumGate α) :
  (G⁻¹ : QuantumGate α).val = star G.val := by
  rfl

/-- The matrix inverse of a unitary gate's matrix is its conjugate transpose. -/
@[simp] lemma gate_val_inv
  {α : Type*} [Fintype α] [DecidableEq α]
  (G : QuantumGate α) :
  (G.val)⁻¹ = star G.val := by
  have h_unit := Matrix.UnitaryGroup.det_isUnit G
  have h_star_mul := Matrix.mem_unitaryGroup_iff.1 G.2
  calc (G.val)⁻¹
      = (G.val)⁻¹ * 1 := by rw [mul_one]
    _ = (G.val)⁻¹ * (G.val * star G.val) := by rw [← h_star_mul]
    _ = ((G.val)⁻¹ * G.val) * star G.val := by rw [Matrix.mul_assoc]
    _ = 1 * star G.val := by rw [nonsing_inv_mul _ h_unit]
    _ = star G.val := by rw [one_mul]

/-- A gate times its inverse is the identity matrix. -/
@[simp] lemma gate_val_mul_inv
  {α : Type*} [Fintype α] [DecidableEq α]
  (G : QuantumGate α) :
  G.val * (G⁻¹ : QuantumGate α).val = (1 : Matrix α α ℂ) := by
  rw [gate_inv_val]
  exact Matrix.mem_unitaryGroup_iff.1 G.2

/-- A gate's inverse times the gate is the identity matrix. -/
@[simp] lemma gate_val_inv_mul
  {α : Type*} [Fintype α] [DecidableEq α]
  (G : QuantumGate α) :
  (G⁻¹ : QuantumGate α).val * G.val = (1 : Matrix α α ℂ) := by
  rw [gate_inv_val]
  exact Matrix.mem_unitaryGroup_iff'.1 G.2

/-- Gate multiplication corresponds to matrix multiplication. -/
@[simp] lemma gate_mul_val
  {α : Type*} [Fintype α] [DecidableEq α]
  (G₁ G₂ : QuantumGate α) :
  (G₁ * G₂).val = G₁.val * G₂.val := rfl

/-- The matrix underlying the identity gate is the identity matrix. -/
@[simp] lemma gate_one_val
{α : Type*} [Fintype α] [DecidableEq α] :
  (1 : QuantumGate α).val = (1 : Matrix α α ℂ) := rfl

/--
Conjugation of a matrix by a gate.

This is the matrix-level helper `U M U†`, intended as a bridge for proofs that still work
directly with matrix expressions.
-/
noncomputable def conjBy
  {α : Type*} [Fintype α] [DecidableEq α]
  (U : QuantumGate α) (M : Matrix α α ℂ) : Matrix α α ℂ :=
  U.val * M * star U.val

/-- `U ⊳ M` is the conjugation `conjBy U M = U M U†` of a matrix by a gate. Scoped to
`Quantum` (active throughout the library's namespace). Precedence `70`, like `*`; the
result is a matrix, so `U ⊳ M = N` needs no parentheses and `(U ⊳ M) i j` does. -/
scoped notation:70 U:71 " ⊳ " M:71 => conjBy U M

/-- Definitional expansion of `conjBy`. -/
@[simp] lemma conjBy_def
  {α : Type*} [Fintype α] [DecidableEq α]
  (U : QuantumGate α) (M : Matrix α α ℂ) :
  conjBy U M = U.val * M * star U.val := rfl

/-- Conjugation by any gate fixes the identity matrix. -/
@[simp] lemma conjBy_one
  {α : Type*} [Fintype α] [DecidableEq α]
  (U : QuantumGate α) :
  conjBy U (1 : Matrix α α ℂ) = 1 := by
  unfold conjBy
  rw [Matrix.mul_assoc, one_mul]
  exact gate_val_mul_inv U

/-- Reassociation form of `conjBy` on a matrix product. -/
lemma conjBy_mul
  {α : Type*} [Fintype α] [DecidableEq α]
  (U : QuantumGate α) (M N : Matrix α α ℂ) :
  conjBy U (M * N) = U.val * M * (N * star U.val) := by
  unfold conjBy
  simp [Matrix.mul_assoc]

/--
Gate-level conjugation.

`conjByGate U G` is `U * G * U⁻¹`, i.e. conjugation in the unitary group.
-/
def conjByGate
  {α : Type*} [Fintype α] [DecidableEq α]
  (U G : QuantumGate α) : QuantumGate α :=
  U * G * U⁻¹

/-- Definitional expansion of `conjByGate` in the gate group. -/
@[simp] lemma conjByGate_def
  {α : Type*} [Fintype α] [DecidableEq α]
  (U G : QuantumGate α) :
  conjByGate U G = U * G * U⁻¹ := rfl

/-- Matrix view of gate-level conjugation. -/
@[simp] lemma conjByGate_val
  {α : Type*} [Fintype α] [DecidableEq α]
  (U G : QuantumGate α) :
  (conjByGate U G).val = U.val * G.val * star U.val := by
  simp [conjByGate, Matrix.mul_assoc]

/-- Gate-level conjugation agrees with matrix-level `conjBy`. -/
@[simp] lemma conjByGate_eq_conjBy
  {α : Type*} [Fintype α] [DecidableEq α]
  (U G : QuantumGate α) :
  (conjByGate U G).val = conjBy U G.val := by
  simp [conjBy]

/-- Conjugation by any gate fixes the identity gate. -/
@[simp] lemma conjByGate_one
  {α : Type*} [Fintype α] [DecidableEq α]
  (U : QuantumGate α) :
  conjByGate U 1 = 1 := by
  simp [conjByGate]

/-- Conjugation by identity is the identity map on gates. -/
@[simp] lemma one_conjByGate
  {α : Type*} [Fintype α] [DecidableEq α]
  (G : QuantumGate α) :
  conjByGate (1 : QuantumGate α) G = G := by
  simp [conjByGate]

/-- Conjugation by a fixed gate preserves gate multiplication. -/
@[simp] lemma conjByGate_mul
  {α : Type*} [Fintype α] [DecidableEq α]
  (U G₁ G₂ : QuantumGate α) :
  conjByGate U (G₁ * G₂) = conjByGate U G₁ * conjByGate U G₂ := by
  simp [conjByGate, mul_assoc]

/-- Conjugation commutes with taking inverses. -/
@[simp] lemma conjByGate_inv
  {α : Type*} [Fintype α] [DecidableEq α]
  (U G : QuantumGate α) :
  conjByGate U G⁻¹ = (conjByGate U G)⁻¹ := by
  simp [conjByGate, mul_assoc]

/-- The type of unit complex numbers (those with absolute value 1). -/
def UnitComplex : Type := {z : ℂ // z * star z = 1}

/-- Coerce a unit complex number to its underlying complex number. -/
instance : Coe UnitComplex ℂ := ⟨Subtype.val⟩

/-- Construct a unit complex number from a complex number and a proof that it
has absolute value 1. -/
def UnitComplex.mk (z : ℂ) (h : z * star z = 1) : UnitComplex := ⟨z, h⟩

/-- The complex number `i` as a unit complex number. -/
def UnitComplex.I : UnitComplex := ⟨Complex.I, by simp [Complex.conj_I, Complex.I_mul_I]⟩

/-- The complex number `-i` as a unit complex number. -/
def UnitComplex.negI : UnitComplex := ⟨-Complex.I, by simp [Complex.conj_I, Complex.I_mul_I]⟩

/-- The complex number `1` as a unit complex number. -/
def UnitComplex.one : UnitComplex := ⟨1, by simp⟩

/-- The complex number `-1` as a unit complex number. -/
def UnitComplex.negOne : UnitComplex := ⟨-1, by simp⟩

/-- `UnitComplex.one` coerces to the complex number `1`. -/
@[simp] lemma UnitComplex.one_coe : (UnitComplex.one : ℂ) = 1 := rfl
/-- `UnitComplex.negOne` coerces to the complex number `-1`. -/
@[simp] lemma UnitComplex.negOne_coe : (UnitComplex.negOne : ℂ) = -1 := rfl
/-- `UnitComplex.I` coerces to the complex number `i`. -/
@[simp] lemma UnitComplex.I_coe : (UnitComplex.I : ℂ) = Complex.I := rfl
/-- `UnitComplex.negI` coerces to the complex number `-i`. -/
@[simp] lemma UnitComplex.negI_coe : (UnitComplex.negI : ℂ) = -Complex.I := rfl

/-- Scalar multiplication of a gate by a unit complex number.

This preserves unitarity: if `G` is unitary and `c` is a unit complex number,
then `c • G` is also unitary. -/
noncomputable instance smul_UnitComplex_QuantumGate
  {α : Type*} [Fintype α] [DecidableEq α] :
  SMul UnitComplex (QuantumGate α) :=
{ smul := fun c G => by
    classical
    refine ⟨(c : ℂ) • G.val, ?_⟩
    rw [Matrix.mem_unitaryGroup_iff]
    have h_unit : (c : ℂ) * star (c : ℂ) = 1 := c.property
    have h_G : G.val * star G.val = 1 := Matrix.mem_unitaryGroup_iff.1 G.2
    simp only [Matrix.smul_mul, star_smul]
    rw [Matrix.mul_smul]
    simp only [smul_smul]
    simp only [h_unit, h_G, one_smul]
    }

/-- The matrix underlying a phase-scaled gate is the scaled matrix. -/
@[simp] lemma smul_UnitComplex_gate_val
  {α : Type*} [Fintype α] [DecidableEq α]
  (c : UnitComplex) (G : QuantumGate α) :
  (c • G).val = (c : ℂ) • G.val := rfl

open Lean.Parser.Tactic in
open Lean in
/--
Proves goals equating small matrices by expanding out products and simpliying
standard Real arithmetic.
-/
syntax (name := matrix_expand) "matrix_expand"
  (" [" ((simpStar <|> simpErase <|> simpLemma),*,?) "]")?
  (" with " rcasesPat+)? : tactic

macro_rules
  | `(tactic| matrix_expand $[[$rules,*]]? $[with $withArg*]?) => do
    let id1 := (withArg.getD ⟨[]⟩).getD 0 (← `(rcasesPat| _))
    let id2 := (withArg.getD ⟨[]⟩).getD 1 (← `(rcasesPat| _))
    let rules' := rules.getD ⟨#[]⟩
    `(tactic| (
      ext i j
      repeat rcases (i : Prod _ _) with ⟨i, $id1⟩
      repeat rcases (j : Prod _ _) with ⟨j, $id2⟩
      fin_cases i
      <;> fin_cases j
      <;> simp [Complex.ext_iff,
        Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, field,
        $rules',* ]
      <;> norm_num
      <;> try field_simp
      <;> try ring_nf
      ))

open Lean.Parser.Tactic in
open Lean in
/--
`vec_expand`:
- turns equality between vectors (functions) into pointwise goals with `ext`,
- case-splits on small index types (`Fin n`, products like `QubitBasis × k`).

It does *not* call `simp` itself; it just prepares the goals for you.
-/
syntax (name := vec_expand) "vec_expand" : tactic

macro_rules
  | `(tactic| vec_expand) => `(
    tactic| (
      ext i
      first
        | (rcases i with ⟨i₁, i₂⟩
           <;> fin_cases i₁
           <;> fin_cases i₂)
        | (fin_cases i)
    ))
open Lean.Parser.Tactic in
open Lean in
/--
`vec_expand_simp [rules]`:

Proves goals equating `QuantumState`s by calling `vec_expand` and
then solving each goal with `simp[rules]`
-/
syntax (name := vec_expand_simp) "vec_expand_simp"
  (" [" ((simpStar <|> simpErase <|> simpLemma),*,?) "]")? : tactic

macro_rules
  | `(tactic| vec_expand_simp $[[$rules,*]]?) => do
    let rules' := rules.getD ⟨#[]⟩
    `(tactic| (
      vec_expand
      all_goals
        simp [$rules',*]
    ))


/-- Apply a matrix to a raw function `α → ℂ` (matrix-vector product). -/
noncomputable abbrev applyMatrixVec' {α : Type*}
  [Fintype α] [DecidableEq α] :
  Matrix α α ℂ → (α → ℂ) → (α → ℂ) :=
  Matrix.mulVec

/-- Apply a matrix to an amplitude `Vector α` (matrix-vector product). -/
noncomputable abbrev applyMatrixVec
  {α : Type*} [Fintype α] [DecidableEq α] :
  Matrix α α ℂ → Vector α → Vector α :=
  Matrix.mulVec


/-- Unitary gates are norm-preserving: `‖Uv‖ = ‖v‖` for every amplitude vector `v`. -/
lemma gate_preserves_norm
  {α : Type*} [Fintype α] [DecidableEq α]
  (G : QuantumGate α) :
  ∀ v : Vector α, norm (Matrix.mulVec (G.val) v) = norm v :=
by
  have h_unitary : ∀ (v : Quantum.Vector α), (star G.val).mulVec (G.val.mulVec v) = v := by
    have h_unitary : (star G.val) * G.val = 1 := by
      convert mul_eq_one_comm.mp ( G.2.2 ) using 1;
    exact fun v => by rw [ Matrix.mulVec_mulVec, h_unitary, Matrix.one_mulVec ] ;
  have h_norm_sq : ∀ (v : Quantum.Vector α),
      (Quantum.norm (G.val.mulVec v))^2 =
      ∑ i, (G.val.mulVec v i) * star (G.val.mulVec v i) := by
    simp +decide [ Quantum.norm, Complex.mul_conj, Complex.normSq_eq_norm_sq ];
    norm_cast ; norm_num [ Real.sq_sqrt ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ];
  have h_inner : ∀ (v : Quantum.Vector α),
      ∑ i, (G.val.mulVec v i) * star (G.val.mulVec v i) =
      ∑ i, v i * star (v i) := by
    intro v
    have h_inner : ∑ i, (G.val.mulVec v i) * star (G.val.mulVec v i) =
        ∑ i, (star (G.val)).mulVec (G.val.mulVec v) i * star (v i) := by
      simp +decide [ Matrix.mulVec, dotProduct, mul_assoc, mul_comm, mul_left_comm,
        Finset.mul_sum _ _ _, Finset.sum_mul ];
      exact Finset.sum_comm.trans (
        Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => by ring )
    generalize_proofs at *; (
    rw [ h_inner, h_unitary ]);
  intros v
  have := h_norm_sq v
  have := h_inner v
  simp_all +decide [ Complex.normSq, Complex.sq_norm ];
  simp_all +decide [ Complex.ext_iff, Finset.sum_add_distrib, mul_comm ]

/-- Apply a gate to a quantum state, producing a quantum state (unitarity keeps
the result normalized). -/
noncomputable def applyGate
  {α : Type*} [Fintype α] [DecidableEq α]
  (G : QuantumGate α) (ψ : QuantumState α) :
  QuantumState α :=
by
  refine
    { val := applyMatrixVec (G.val) ψ.val
    , property := ?_ }
  have h := gate_preserves_norm G ψ.val
  rw [ψ.property] at h
  exact h

/-- The amplitude vector of `applyGate G ψ` is the matrix-vector product `G ψ`. -/
@[simp] lemma applyGate_val
  {α : Type*} [Fintype α] [DecidableEq α]
  (G : QuantumGate α) (ψ : QuantumState α) :
  (applyGate G ψ).val = Matrix.mulVec (G.val) ψ.val := rfl

/-- Coercion form of `applyGate_val`. -/
@[simp] lemma applyGate_coe
  {α : Type*} [Fintype α] [DecidableEq α]
  (G : QuantumGate α) (ψ : QuantumState α) :
  (applyGate G ψ : Vector α) = Matrix.mulVec (G.val) ψ := rfl

/-- Gates act on amplitude vectors by matrix-vector multiplication. -/
noncomputable instance smul_Vector_by_QuantumGate
  {α : Type*} [Fintype α] [DecidableEq α] :
  SMul (QuantumGate α) (Vector α) :=
{ smul := fun U v => Matrix.mulVec (U.val) v }

/-- Gates act on quantum states via `applyGate`. -/
noncomputable instance smul_QuantumState_by_QuantumGate
  {α : Type*} [Fintype α] [DecidableEq α] :
  SMul (QuantumGate α) (QuantumState α) :=
{ smul := applyGate }

/-- The vector coercion of `G • ψ` is the matrix-vector product `G ψ`. -/
@[simp] lemma smul_val
  {α} [Fintype α] [DecidableEq α]
  (G : QuantumGate α) (ψ : QuantumState α) :
  (G • ψ : Vector α) = Matrix.mulVec (G.val) ψ := rfl

/-- The `.val` field of `G • ψ` is the matrix-vector product `G ψ`. -/
@[simp] lemma smul_QState_val
  {α : Type*} [Fintype α] [DecidableEq α]
  (G : QuantumGate α) (ψ : QuantumState α) :
  (G • ψ).val = Matrix.mulVec (G.val) ψ.val := rfl

/-- A matrix is Hermitian when it equals its own conjugate transpose. -/
def Hermitian {α : Type*} [DecidableEq α] [Fintype α] (M : Matrix α α ℂ) : Prop :=
  Mᴴ = M

/-- Unfold `Hermitian` to the equation `Mᴴ = M`. -/
@[simp] lemma Hermitian_def {α : Type*} [DecidableEq α] [Fintype α] (M : Matrix α α ℂ) :
  Hermitian M ↔ Mᴴ = M := Iff.rfl

/-- A matrix is involutary when it squares to the identity. -/
def Involutary {α : Type*} [Fintype α] [DecidableEq α] (M : Matrix α α ℂ) : Prop :=
  M * M = 1

/-- Unfold `Involutary` to the equation `M * M = 1`. -/
@[simp] lemma Involutary_def {α : Type*} [DecidableEq α] [Fintype α] (M : Matrix α α ℂ) :
  Involutary M ↔ M * M = 1 := Iff.rfl

/-- An involutary matrix is its own inverse. -/
lemma involutary_inv_eq
  {α : Type*} [Fintype α] [DecidableEq α]
  {M : Matrix α α ℂ} (h : Involutary M) :
  M⁻¹ = M := by
  have h_mul : M * M = 1 := h
  have h_unit : IsUnit M.det :=
    (Matrix.isUnit_iff_isUnit_det M).1 (IsUnit.of_mul_eq_one M h_mul)
  calc M⁻¹
      = M⁻¹ * 1 := by rw [mul_one]
    _ = M⁻¹ * (M * M) := by rw [← h_mul]
    _ = (M⁻¹ * M) * M := by rw [Matrix.mul_assoc]
    _ = 1 * M := by rw [nonsing_inv_mul _ h_unit]
    _ = M := by rw [one_mul]

/-- If a matrix is Hermitian and involutary, then it is unitary (in the sense U
Uᴴ = 1 and Uᴴ U = 1). -/
lemma unitary_of_hermitian_involutary
  {α : Type*} [Fintype α] [DecidableEq α]
  {U : Matrix α α ℂ}
  (hH : Hermitian U) (hI : Involutary U) :
  (U * Uᴴ = 1) ∧ (Uᴴ * U = 1) := by
  have hH' : Uᴴ = U := hH
  refine ⟨?left, ?right⟩
  · simpa [hH'] using hI
  · simpa [hH'] using hI

/-- Identity matrix on the qubit basis. -/
def Imat : Matrix QubitBasis QubitBasis ℂ := 1

/-- The identity matrix is Hermitian. -/
lemma Imat_hermitian : Hermitian Imat := by
  rw [Hermitian_def, Imat, conjTranspose_one]

/-- The identity matrix is involutary. -/
lemma Imat_involutary : Involutary Imat := by
  rw [Involutary_def, Imat, mul_one]

/-- `Imat` squares to the identity. -/
@[simp] lemma Imat_sq : Imat * Imat = 1 := Imat_involutary

/-- The identity matrix is unitary. -/
lemma Imat_mem_unitaryGroup :
  Imat ∈ Matrix.unitaryGroup QubitBasis ℂ := by
  have h := unitary_of_hermitian_involutary Imat_hermitian Imat_involutary
  exact Matrix.mem_unitaryGroup_iff.mpr h.1

/-- Identity as a one-qubit gate. -/
noncomputable def I : OneQubitGate :=
  ⟨Imat, Imat_mem_unitaryGroup⟩

/-- Pauli X matrix, indexed by the qubit basis `Fin 2`. -/
def Xmat : Matrix QubitBasis QubitBasis ℂ := !![0, 1; 1, 0]

/-- The Pauli X matrix is Hermitian. -/
lemma Xmat_hermitian : Hermitian Xmat := by matrix_expand[Xmat]

/-- The Pauli X matrix is involutary. -/
lemma Xmat_involutary : Involutary Xmat := by matrix_expand[Xmat]

/-- `Xmat` squares to the identity. -/
@[simp] lemma Xmat_sq : Xmat * Xmat = 1 := Xmat_involutary

/-- The Pauli X matrix is unitary. -/
lemma Xmat_mem_unitaryGroup :
  Xmat ∈ Matrix.unitaryGroup QubitBasis ℂ :=
by
  have h := unitary_of_hermitian_involutary Xmat_hermitian Xmat_involutary
  have hU : Xmat * Xmatᴴ = 1 := h.1
  exact (Matrix.mem_unitaryGroup_iff.mpr hU)

/-- Pauli X as a one-qubit gate. -/
noncomputable def X : OneQubitGate :=
{ val      := Xmat
, property := Xmat_mem_unitaryGroup }

/-- Pauli Y matrix, indexed by the qubit basis `Fin 2`. -/
def Ymat : Matrix QubitBasis QubitBasis ℂ :=
  !![0, -Complex.I; Complex.I, 0]

/-- The Pauli Y matrix is Hermitian. -/
lemma Ymat_hermitian : Hermitian Ymat := by matrix_expand[Ymat]

/-- The Pauli Y matrix is involutary. -/
lemma Ymat_involutary : Involutary Ymat := by matrix_expand[Ymat]

/-- `Ymat` squares to the identity. -/
@[simp] lemma Ymat_sq : Ymat * Ymat = 1 := Ymat_involutary

/-- The Pauli Y matrix is unitary. -/
lemma Ymat_mem_unitaryGroup :
  Ymat ∈ Matrix.unitaryGroup QubitBasis ℂ :=
by
  have h := unitary_of_hermitian_involutary
              Ymat_hermitian Ymat_involutary
  exact (Matrix.mem_unitaryGroup_iff.mpr h.1)

/-- Pauli Y as a one-qubit gate. -/
noncomputable def Y : OneQubitGate :=
{ val := Ymat
, property := Ymat_mem_unitaryGroup }

/-- Pauli Z matrix, indexed by the qubit basis `Fin 2`. -/
def Zmat : Matrix QubitBasis QubitBasis ℂ :=
  !![1, 0; 0, -1]

/-- The Pauli Z matrix is Hermitian. -/
lemma Zmat_hermitian : Hermitian Zmat := by matrix_expand[Zmat]

/-- The Pauli Z matrix is involutary. -/
lemma Zmat_involutary : Involutary Zmat := by matrix_expand[Zmat]

/-- `Zmat` squares to the identity. -/
@[simp] lemma Zmat_sq : Zmat * Zmat = 1 := Zmat_involutary

/-- Pauli matrix cross products: X * Y = iZ -/
lemma Xmat_mul_Ymat : Xmat * Ymat = Complex.I • Zmat := by matrix_expand[Xmat, Ymat, Zmat]

/-- Pauli matrix cross products: Y * X = -iZ -/
lemma Ymat_mul_Xmat : Ymat * Xmat = -Complex.I • Zmat := by matrix_expand[Xmat, Ymat, Zmat]

/-- Pauli matrix cross products: Y * Z = iX -/
lemma Ymat_mul_Zmat : Ymat * Zmat = Complex.I • Xmat := by matrix_expand[Xmat, Ymat, Zmat]

/-- Pauli matrix cross products: Z * Y = -iX -/
lemma Zmat_mul_Ymat : Zmat * Ymat = -Complex.I • Xmat := by matrix_expand[Xmat, Ymat, Zmat]

/-- Pauli matrix cross products: Z * X = iY -/
lemma Zmat_mul_Xmat : Zmat * Xmat = Complex.I • Ymat := by matrix_expand[Xmat, Ymat, Zmat]

/-- Pauli matrix cross products: X * Z = -iY -/
lemma Xmat_mul_Zmat : Xmat * Zmat = -Complex.I • Ymat := by matrix_expand[Xmat, Ymat, Zmat]

/-- The Pauli Z matrix is unitary. -/
lemma Zmat_mem_unitaryGroup :
  Zmat ∈ Matrix.unitaryGroup QubitBasis ℂ :=
by
  have h := unitary_of_hermitian_involutary
              Zmat_hermitian Zmat_involutary
  exact (Matrix.mem_unitaryGroup_iff.mpr h.1)

/-- Hadamard gate matrix. -/
noncomputable def Hmat : Matrix QubitBasis QubitBasis ℂ :=
  (1 / Real.sqrt 2) • !![1, 1; 1, -1]

/-- The Hadamard matrix is Hermitian. -/
lemma Hmat_hermitian : Hermitian Hmat := by matrix_expand[Hmat]

/-- The Hadamard matrix is involutary. -/
lemma Hmat_involutary : Involutary Hmat := by matrix_expand[Hmat]

/-- `Hmat` squares to the identity. -/
@[simp] lemma Hmat_sq : Hmat * Hmat = 1 := Hmat_involutary

/-- The Hadamard matrix is unitary. -/
lemma Hmat_mem_unitaryGroup :
  Hmat ∈ Matrix.unitaryGroup QubitBasis ℂ :=
by
  have h := unitary_of_hermitian_involutary Hmat_hermitian Hmat_involutary
  have hU : Hmat * Hmatᴴ = 1 := h.1
  exact (Matrix.mem_unitaryGroup_iff.mpr hU)

/-- Hadamard gate as a one-qubit gate. -/
noncomputable def H : OneQubitGate :=
{ val      := Hmat
, property := Hmat_mem_unitaryGroup }


/-- Pauli Z as a one-qubit gate. -/
noncomputable def Z : OneQubitGate :=
{ val := Zmat
, property := Zmat_mem_unitaryGroup }

/-- The matrix underlying the gate `I` is `Imat`. -/
@[simp] lemma coe_I : (I : Matrix QubitBasis QubitBasis ℂ) = Imat := rfl
/-- The matrix underlying the gate `X` is `Xmat`. -/
@[simp] lemma coe_X : (X : Matrix QubitBasis QubitBasis ℂ) = Xmat := rfl
/-- The matrix underlying the gate `Y` is `Ymat`. -/
@[simp] lemma coe_Y : (Y : Matrix QubitBasis QubitBasis ℂ) = Ymat := rfl
/-- The matrix underlying the gate `Z` is `Zmat`. -/
@[simp] lemma coe_Z : (Z : Matrix QubitBasis QubitBasis ℂ) = Zmat := rfl
/-- The matrix underlying the gate `H` is `Hmat`. -/
@[simp] lemma coe_H : (H : Matrix QubitBasis QubitBasis ℂ) = Hmat := rfl

/-- Pauli gate cross products: X * Y = iZ -/
@[simp] lemma X_mul_Y : X * Y = UnitComplex.I • Z :=
  Subtype.ext (by
    simp only [gate_mul_val, smul_UnitComplex_gate_val, coe_X, coe_Y, coe_Z,
      UnitComplex.I_coe]
    exact Xmat_mul_Ymat)

/-- Pauli gate cross products: Y * X = -iZ -/
@[simp] lemma Y_mul_X : Y * X = UnitComplex.negI • Z :=
  Subtype.ext (by
    simp only [gate_mul_val, smul_UnitComplex_gate_val, coe_X, coe_Y, coe_Z,
      UnitComplex.negI_coe]
    exact Ymat_mul_Xmat)

/-- Pauli gate cross products: Y * Z = iX -/
@[simp] lemma Y_mul_Z : Y * Z = UnitComplex.I • X :=
  Subtype.ext (by
    simp only [gate_mul_val, smul_UnitComplex_gate_val, coe_X, coe_Y, coe_Z,
      UnitComplex.I_coe]
    exact Ymat_mul_Zmat)

/-- Pauli gate cross products: Z * Y = -iX -/
@[simp] lemma Z_mul_Y : Z * Y = UnitComplex.negI • X :=
  Subtype.ext (by
    simp only [gate_mul_val, smul_UnitComplex_gate_val, coe_X, coe_Y, coe_Z,
      UnitComplex.negI_coe]
    exact Zmat_mul_Ymat)

/-- Pauli gate cross products: Z * X = iY -/
@[simp] lemma Z_mul_X : Z * X = UnitComplex.I • Y :=
  Subtype.ext (by
    simp only [gate_mul_val, smul_UnitComplex_gate_val, coe_X, coe_Y, coe_Z,
      UnitComplex.I_coe]
    exact Zmat_mul_Xmat)

/-- Pauli gate cross products: X * Z = -iY -/
@[simp] lemma X_mul_Z : X * Z = UnitComplex.negI • Y :=
  Subtype.ext (by
    simp only [gate_mul_val, smul_UnitComplex_gate_val, coe_X, coe_Y, coe_Z,
      UnitComplex.negI_coe]
    exact Xmat_mul_Zmat)

/-- `I` is self-inverse (it is Hermitian and involutary). -/
@[simp] lemma inv_I : I⁻¹ = I := by
  ext
  rw [gate_inv_val, coe_I, star_eq_conjTranspose, (Hermitian_def Imat).1 Imat_hermitian]

/-- `X` is self-inverse (it is Hermitian and involutary). -/
@[simp] lemma inv_X : X⁻¹ = X := by
  ext
  rw [gate_inv_val, coe_X, star_eq_conjTranspose, (Hermitian_def Xmat).1 Xmat_hermitian]

/-- `Y` is self-inverse (it is Hermitian and involutary). -/
@[simp] lemma inv_Y : Y⁻¹ = Y := by
  ext
  rw [gate_inv_val, coe_Y, star_eq_conjTranspose, (Hermitian_def Ymat).1 Ymat_hermitian]

/-- `Z` is self-inverse (it is Hermitian and involutary). -/
@[simp] lemma inv_Z : Z⁻¹ = Z := by
  ext
  rw [gate_inv_val, coe_Z, star_eq_conjTranspose, (Hermitian_def Zmat).1 Zmat_hermitian]

/-- `H` is self-inverse (it is Hermitian and involutary). -/
@[simp] lemma inv_H : H⁻¹ = H := by
  ext
  rw [gate_inv_val, coe_H, star_eq_conjTranspose, (Hermitian_def Hmat).1 Hmat_hermitian]

/-- Phase gate S (√Z) matrix: |1⟩ gets phase i. -/
noncomputable def Smat : Matrix QubitBasis QubitBasis ℂ :=
  !![1, 0; 0, Complex.I]

/-- The phase gate matrix is unitary. -/
lemma Smat_mem_unitaryGroup : Smat ∈ Matrix.unitaryGroup QubitBasis ℂ := by
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Smat, Matrix.mul_apply, Complex.ext_iff]
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Smat, Matrix.vecMul, dotProduct, Complex.ext_iff]

/-- Phase gate S (√Z) as a one-qubit gate. -/
noncomputable def S : OneQubitGate :=
  ⟨Smat, Smat_mem_unitaryGroup⟩

/-- The inverse of the phase gate S (S†). -/
noncomputable def inv_S : OneQubitGate := S⁻¹

/-- The matrix underlying the gate `S` is `Smat`. -/
@[simp] lemma coe_S : (S : Matrix QubitBasis QubitBasis ℂ) = Smat := rfl

/-- The matrix underlying `inv_S` is the conjugate transpose of `Smat`. -/
lemma inv_S_val : inv_S.val = star S.val := by
  rw [inv_S, gate_inv_val]

/-- X flips |0⟩ to |1⟩. -/
@[simp] lemma X_on_ket0 : X • |0⟩ = |1⟩ := by
  vec_expand_simp [Xmat, ket0, ket1]

/-- X flips |1⟩ to |0⟩. -/
@[simp] lemma X_on_ket1 : X • |1⟩ = |0⟩ := by
  vec_expand_simp [Xmat, ket0, ket1]

/-- Controlled version of a gate `g` on `k`, acting on `QubitBasis × k`.

The first factor is the control qubit: on the `|0⟩` block the gate acts as the
identity on `k`, on the `|1⟩` block it acts as `g`, and the off-diagonal blocks
are zero.
-/
noncomputable def controllize
  {k : Type*} [Fintype k] [DecidableEq k]
  (g : QuantumGate k) : QuantumGate (QubitBasis × k) :=
by
  classical
  exact ⟨
    Matrix.of (fun (q₁, t₁) (q₂, t₂) =>
      if (q₁, q₂) = (0, 0) then
        (if t₁ = t₂ then (1 : ℂ) else 0)
      else if (q₁, q₂) = (1, 1) then
        (g : Matrix k k ℂ) t₁ t₂
      else
        0)
    ,
    by
      rw [Matrix.mem_unitaryGroup_iff]
      matrix_expand [-Complex.ext_iff] with ti tj;
      · congr 1
        exact propext eq_comm
      · exact congrFun₂ g.2.2 ti tj
  ⟩
scoped notation "C[" g "]" => controllize g

/-- The block matrix underlying `controllize g`. -/
@[simp] lemma controllize_val
  {k : Type*} [Fintype k] [DecidableEq k]
  (g : QuantumGate k) :
  (controllize g : Matrix (QubitBasis × k) (QubitBasis × k) ℂ) =
    Matrix.of (fun (q₁, t₁) (q₂, t₂) =>
      if (q₁, q₂) = (0, 0) then
        (if t₁ = t₂ then (1 : ℂ) else 0)
      else if (q₁, q₂) = (1, 1) then
        (g : Matrix k k ℂ) t₁ t₂
      else
        0) :=
rfl

/-- CNOT gate on two qubits: control = first, target = second.

This is `controllize X` with `k = QubitBasis`.
-/
noncomputable def CNOT : TwoQubitGate :=
  C[X]

/-- Pointwise amplitudes of the two-qubit basis state `ket00`. -/
@[simp] lemma ket00_apply
  (q : QubitBasis) (t : QubitBasis) :
  (|00⟩ : QuantumState TwoQubitBasis).val (q, t)
    = (if (q, t) = (0, 0) then (1 : ℂ) else 0) :=
by
  simp [ket00]

/-- CNOT maps |00⟩ to |00⟩. -/
lemma CNOT_on_ket00 : CNOT • |00⟩ = |00⟩ := by
  vec_expand_simp [Matrix.mulVec, CNOT, ket00]

/-- CNOT maps |01⟩ to |01⟩. -/
lemma CNOT_on_ket01 : CNOT • |01⟩ = |01⟩ := by
  vec_expand_simp[Matrix.mulVec, CNOT, ket01]

/-- CNOT maps |10⟩ to |11⟩. -/
lemma CNOT_on_ket10 : CNOT • |10⟩ = |11⟩ := by
  vec_expand_simp[Matrix.mulVec, CNOT, ket10, ket11, Xmat]

/-- CNOT maps |11⟩ to |10⟩. -/
lemma CNOT_on_ket11 : CNOT • |11⟩ = |10⟩ := by
  vec_expand_simp[Matrix.mulVec, CNOT, ket10, ket11, Xmat]

end Quantum
