import QEC.Stabilizer.Framework.Core.CSS.CSSDistance
import QEC.Stabilizer.Codes.Small.Steane7

/-!
# The Steane code has distance 3: `[[7, 1, 3]]`

`Steane7.lean` packages the Steane code as a `Code[[7, 1]]`. This file proves
`HasCodeDistance stabilizerCode 3` and bundles the result as
`stabilizerCodeWithDistance : Code[[7, 1, 3]]`.

The argument is the textbook one. The Steane code is the CSS code of the
classical `[7,4,3]` Hamming code, whose parity-check matrix has as columns the
seven nonzero vectors of length three — so no column is zero and no two columns
coincide. By `hasCodeDistance_three_of_columns` that is exactly what is needed
for no Pauli of weight `1` or `2` to commute with every check: a weight-`≤ 2`
error whose `X`-part is a Hamming codeword has no `X`-part at all, and likewise
for its `Z`-part. The upper bound is the explicit weight-3 logical `X̄ · X₁ = X`
on qubits `{3, 5, 6}`, which is a nontrivial logical because it still
anticommutes with `Z̄`.

Every finite check (the column conditions on the three rows, the weight of the
witness, its anticommutation with `Z̄`) is closed by the kernel with `decide`;
the file is `native_decide`-free.
-/

namespace Quantum.StabilizerGroup.Steane7

open NQubitPauliGroupElement
open scoped Pauli

/-! ## The Hamming parity-check rows -/

/-- The three parity-check rows of the classical `[7,4,3]` Hamming code,
`r₁ = {0,1,2,4}`, `r₂ = {0,1,3,5}`, `r₃ = {0,2,3,6}`. Column `i` of the check
matrix is the set of rows containing qubit `i`; the seven columns are the seven
nonzero vectors of `𝔽₂³`. -/
def row : Fin 3 → Finset (Fin 7) := ![{0, 1, 2, 4}, {0, 1, 3, 5}, {0, 2, 3, 6}]

/-- The `Z`-checks are `Z` along the Hamming rows. -/
lemma Z1_eq_zOn : Z1 = zOn {0, 1, 2, 4} :=
  NQubitPauliGroupElement.ext _ _ rfl (funext fun i => by fin_cases i <;> rfl)

lemma Z2_eq_zOn : Z2 = zOn {0, 1, 3, 5} :=
  NQubitPauliGroupElement.ext _ _ rfl (funext fun i => by fin_cases i <;> rfl)

lemma Z3_eq_zOn : Z3 = zOn {0, 2, 3, 6} :=
  NQubitPauliGroupElement.ext _ _ rfl (funext fun i => by fin_cases i <;> rfl)

/-- The `X`-checks are `X` along the same rows (the Steane code is self-dual
CSS). -/
lemma X1_eq_xOn : X1 = xOn {0, 1, 2, 4} :=
  NQubitPauliGroupElement.ext _ _ rfl (funext fun i => by fin_cases i <;> rfl)

lemma X2_eq_xOn : X2 = xOn {0, 1, 3, 5} :=
  NQubitPauliGroupElement.ext _ _ rfl (funext fun i => by fin_cases i <;> rfl)

lemma X3_eq_xOn : X3 = xOn {0, 2, 3, 6} :=
  NQubitPauliGroupElement.ext _ _ rfl (funext fun i => by fin_cases i <;> rfl)

/-- Each `Z`-check along a Hamming row is a Steane generator. -/
lemma zOn_row_mem (r : Fin 3) : zOn (row r) ∈ generators := by
  fin_cases r <;> simp [row, generators, ZGenerators, Z1_eq_zOn, Z2_eq_zOn, Z3_eq_zOn]

/-- Each `X`-check along a Hamming row is a Steane generator. -/
lemma xOn_row_mem (r : Fin 3) : xOn (row r) ∈ generators := by
  fin_cases r <;> simp [row, generators, XGenerators, X1_eq_xOn, X2_eq_xOn, X3_eq_xOn]

/-! ## The Hamming code has distance 3

In terms of the check matrix: no column is zero, and no two columns coincide. -/

/-- Every qubit lies on some Hamming row (no zero column). -/
lemma row_cover : ∀ i : Fin 7, ∃ r, i ∈ row r := by decide

/-- Any two distinct qubits are separated by some Hamming row (distinct
columns). -/
lemma row_separate : ∀ i j : Fin 7, i ≠ j → ∃ r, (i ∈ row r ↔ j ∉ row r) := by decide

/-! ## A weight-3 logical operator

`X̄ = X⊗⁷` times the stabilizer `X₁ = X` on `{0,1,2,4}` is `X` on the
complementary qubits `{3, 5, 6}`: a weight-3 representative of the same logical
operator. -/

/-- `X` on qubits `{3, 5, 6}`, the weight-3 representative `X̄ · X₁` of logical
`X`. -/
def logicalXw3 : NQubitPauliGroupElement 7 := σ[IIIXIXX]

lemma logicalXw3_eq_mul : logicalXw3 = logicalX * X1 :=
  NQubitPauliGroupElement.ext _ _ rfl (funext fun i => by fin_cases i <;> rfl)

lemma logicalXw3_weight : weight logicalXw3 = 3 := by decide

/-- `X` on `{3, 5, 6}` meets `Z̄ = Z⊗⁷` on three qubits, an odd number, so they
anticommute. -/
lemma logicalXw3_anticomm_logicalZ : Anticommute logicalXw3 logicalZ := by
  rw [NQubitPauliOperator.anticommutes_iff_symplectic_inner_one]
  decide

/-- The stabilizer code's subgroup is the closure of the six generators. -/
lemma stabilizerCode_toSubgroup_eq :
    stabilizerCode.toStabilizerGroup.toSubgroup = Subgroup.closure generators :=
  stabilizerGroup_toSubgroup_eq

/-- `X̄ · X₁` commutes with the stabilizer: `X̄` does, and so does the
stabilizer element `X₁`. -/
lemma logicalXw3_mem_centralizer : logicalXw3 ∈ centralizer stabilizerCode.toStabilizerGroup := by
  rw [logicalXw3_eq_mul]
  refine (centralizer _).mul_mem logicalX_mem_centralizer (stabilizer_le_centralizer _ ?_)
  rw [stabilizerCode_toSubgroup_eq]
  exact Subgroup.subset_closure (by simp [generators, XGenerators])

/-- `X̄ · X₁` is a nontrivial logical operator: it lies in the centralizer and
anticommutes with the centralizer element `Z̄`. -/
lemma logicalXw3_isNontrivial :
    IsNontrivialLogicalOperator logicalXw3 stabilizerCode.toStabilizerGroup :=
  isNontrivialLogicalOperator_of_anticommute_centralizer _ logicalXw3_mem_centralizer
    logicalZ_mem_centralizer logicalXw3_anticomm_logicalZ

/-! ## Distance 3 -/

/-- **The Steane code has distance 3.** Both check matrices are the Hamming
matrix, whose columns are nonzero and pairwise distinct, so no Pauli of weight
`1` or `2` is a nontrivial logical; `X` on `{3, 5, 6}` is one of weight `3`. -/
theorem code_has_distance_three : HasCodeDistance stabilizerCode 3 :=
  hasCodeDistance_three_of_columns row row generators stabilizerCode stabilizerCode_toSubgroup_eq
    zOn_row_mem xOn_row_mem row_cover row_cover row_separate row_separate
    ⟨logicalXw3, logicalXw3_isNontrivial, logicalXw3_weight⟩

/-- The Steane code as a `[[7, 1, 3]]` code: `stabilizerCode` packaged with its
distance. -/
noncomputable def stabilizerCodeWithDistance : Code[[7, 1, 3]] where
  toStabilizerCode := stabilizerCode
  hasDistance := code_has_distance_three

end Quantum.StabilizerGroup.Steane7
