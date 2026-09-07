import QEC.Foundations.Gates
import QEC.Foundations.Tensor

/-!
# Clifford conjugation tableau

How the Clifford generators act on the Pauli matrices by conjugation. Together
with multiplicativity (`conjBy_mul`) this table determines the whole Clifford
action, so it is the defining data of the Clifford group rather than an ad-hoc
collection of identities.

## Convention

Everything is stated in the **forward** direction using the `conjBy` notation
from `Gates.lean`:

`U ⊳ P = U P U†`

read as "apply `U`, then `P`, then `U†`". There is deliberately no second family
of lemmas for the other direction, because the other direction is not a separate
axis: `U† P U` is `U⁻¹ ⊳ P`, so it is the *same table read at the inverse gate*.
Concretely,

- `H⁻¹ = H` and `CNOT⁻¹ = CNOT` (both are Hermitian and involutary), so for
  those two gates the two directions coincide — see `H_inv_eq` and
  `CNOT_inv_eq`;
- `S⁻¹` is `inv_S`, definitionally (`Gates.lean`), so the adjoint row for `S`
  *is* the forward row for `inv_S`.

`conjBy_inv_val` is the general bridge from `U⁻¹ ⊳ P` to the longhand
`star U.val * P * U.val`, for call sites that need to `rw` against the raw
matrix product.

## Shape of the table

The single-qubit part is complete: each of `H`, `S`, `inv_S` against each of
`Imat`, `Xmat`, `Ymat`, `Zmat`. The identity column is not written out per gate
— it is `conjBy_Imat`, which holds for *every* gate and so subsumes all of those
cells at once.

For `CNOT` the table is given on the four generators of the two-qubit Pauli
group, `X ⊗ I`, `I ⊗ X`, `Z ⊗ I`, `I ⊗ Z`. That is a generating set, so the
remaining cells follow by `conjBy_mul` and need no separate lemmas; it is also
as far as `Tensor.lean`'s named two-qubit operators reach (it defines no
`Y`-bearing ones).

Definitions of the gates and matrices live in `Gates.lean` and `Tensor.lean`.
-/

namespace Quantum

open Matrix
open Kronecker

/-! ### The identity column, and the two directions -/

/-- Conjugation by any gate fixes the identity matrix. This is the whole `Imat`
column of the tableau, for every gate at once, so no gate needs its own version.
-/
@[simp] lemma conjBy_Imat (U : OneQubitGate) : U ⊳ Imat = Imat := by
  simp [Imat]

/-- Conjugation by the inverse gate, in longhand: `U⁻¹ ⊳ P = U† P U`. This is
the bridge between the forward tableau below and the raw matrix product that
`rw` / `congrArg` call sites work with. -/
lemma conjBy_inv_val
    {α : Type*} [Fintype α] [DecidableEq α]
    (U : QuantumGate α) (M : Matrix α α ℂ) :
    U⁻¹ ⊳ M = star U.val * M * U.val := by
  simp [conjBy]

/-! ### Hadamard

`H` is Hermitian and involutary, so `H⁻¹ = H` and conjugating by `H` in either
direction gives the same answer. -/

/-- `H` is its own inverse, so its adjoint row equals its forward row. -/
lemma H_inv_eq : H⁻¹ = H := by
  ext i j
  simpa [gate_inv_val, H] using congrFun (congrFun Hmat_hermitian i) j

/-- `H X H† = Z`. -/
lemma H_conj_X : H ⊳ Xmat = Zmat := by
  matrix_expand [H, Hmat, Xmat, Zmat]

/-- `H Y H† = -Y`. -/
lemma H_conj_Y : H ⊳ Ymat = -Ymat := by
  matrix_expand [H, Hmat, Ymat]

/-- `H Z H† = X`. -/
lemma H_conj_Z : H ⊳ Zmat = Xmat := by
  matrix_expand [H, Hmat, Xmat, Zmat]

/-! ### Phase gate `S` and its inverse

The adjoint row for `S` is the forward row for `inv_S`, since `inv_S` is `S⁻¹`
by definition. -/

/-- `S X S† = Y`. -/
lemma S_conj_X : S ⊳ Xmat = Ymat := by
  matrix_expand [S, Smat, Xmat, Ymat]

/-- `S Y S† = -X`. -/
lemma S_conj_Y : S ⊳ Ymat = -Xmat := by
  matrix_expand [S, Smat, Xmat, Ymat]

/-- `S Z S† = Z`: `S` commutes with `Z`. -/
lemma S_conj_Z : S ⊳ Zmat = Zmat := by
  matrix_expand [S, Smat, Zmat]

/-- `S† X S = -Y`. -/
lemma inv_S_conj_X : inv_S ⊳ Xmat = -Ymat := by
  matrix_expand [inv_S, S, Smat, Xmat, Ymat]

/-- `S† Y S = X`. -/
lemma inv_S_conj_Y : inv_S ⊳ Ymat = Xmat := by
  matrix_expand [inv_S, S, Smat, Xmat, Ymat]

/-- `S† Z S = Z`. -/
lemma inv_S_conj_Z : inv_S ⊳ Zmat = Zmat := by
  matrix_expand [inv_S, S, Smat, Zmat]

/-! ### CNOT (control = first qubit, target = second)

`CNOT` is Hermitian and involutary, so as with `H` the two conjugation
directions coincide. The four lemmas below cover a generating set of the
two-qubit Pauli group; everything else follows from them by `conjBy_mul`. -/

/-- `CNOT` is its own inverse, so its adjoint row equals its forward row. -/
lemma CNOT_inv_eq : CNOT⁻¹ = CNOT := by
  ext ⟨c₁, t₁⟩ ⟨c₂, t₂⟩
  fin_cases c₁ <;> fin_cases t₁ <;> fin_cases c₂ <;> fin_cases t₂ <;>
    simp [CNOT, controllize_val, coe_X, Xmat]

/-- `CNOT (X ⊗ I) CNOT† = X ⊗ X`. -/
lemma CNOT_conj_X_q1 : CNOT ⊳ X_q1_2.val = XX_2.val := by
  rw [conjBy_def, CNOT, controllize_val, coe_X, X_q1_2, XX_2,
    tensorGate_val X 1, tensorGate_val X X]
  ext ⟨c₁, t₁⟩ ⟨c₂, t₂⟩
  fin_cases c₁ <;> fin_cases t₁ <;> fin_cases c₂ <;> fin_cases t₂ <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Xmat]

/-- `CNOT (I ⊗ X) CNOT† = I ⊗ X`. -/
lemma CNOT_conj_X_q2 : CNOT ⊳ X_q2_2.val = X_q2_2.val := by
  rw [conjBy_def, CNOT, controllize_val, coe_X, X_q2_2, tensorGate_val 1 X]
  ext ⟨c₁, t₁⟩ ⟨c₂, t₂⟩
  fin_cases c₁ <;> fin_cases t₁ <;> fin_cases c₂ <;> fin_cases t₂ <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Xmat]

/-- `CNOT (Z ⊗ I) CNOT† = Z ⊗ I`. -/
lemma CNOT_conj_Z_q1 : CNOT ⊳ Z_q1_2.val = Z_q1_2.val := by
  rw [conjBy_def, CNOT, controllize_val, coe_X, Z_q1_2, tensorGate_val Z 1]
  ext ⟨c₁, t₁⟩ ⟨c₂, t₂⟩
  fin_cases c₁ <;> fin_cases t₁ <;> fin_cases c₂ <;> fin_cases t₂ <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Zmat, Xmat]

/-- `CNOT (I ⊗ Z) CNOT† = Z ⊗ Z`. -/
lemma CNOT_conj_Z_q2 : CNOT ⊳ Z_q2_2.val = ZZ_2.val := by
  rw [conjBy_def, CNOT, controllize_val, coe_X, Z_q2_2, ZZ_2,
    tensorGate_val 1 Z, tensorGate_val Z Z]
  ext ⟨c₁, t₁⟩ ⟨c₂, t₂⟩
  fin_cases c₁ <;> fin_cases t₁ <;> fin_cases c₂ <;> fin_cases t₂ <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Zmat, Xmat]

/-! ### Longhand corollaries

The tableau above is stated with `⊳`. These restate the rows that downstream
`rw` / `congrArg` call sites consume in the raw `star U.val * P * U.val` form;
each is one step from its counterpart above via `conjBy_inv_val`. -/

/-- `H† X H = Z`, longhand. -/
lemma H_adj_X_H : star H.val * Xmat * H.val = Zmat := by
  rw [← conjBy_inv_val, H_inv_eq]; exact H_conj_X

/-- `H† Z H = X`, longhand. -/
lemma H_adj_Z_H : star H.val * Zmat * H.val = Xmat := by
  rw [← conjBy_inv_val, H_inv_eq]; exact H_conj_Z

/-- `S† X S = -Y`, longhand. -/
lemma S_adj_X_S : star S.val * Xmat * S.val = -Ymat := by
  rw [← conjBy_inv_val]; exact inv_S_conj_X

/-- `S† Y S = X`, longhand. -/
lemma S_adj_Y_S : star S.val * Ymat * S.val = Xmat := by
  rw [← conjBy_inv_val]; exact inv_S_conj_Y

/-- `S† Z S = Z`, longhand. -/
lemma S_adj_Z_S : star S.val * Zmat * S.val = Zmat := by
  rw [← conjBy_inv_val]; exact inv_S_conj_Z

end Quantum
