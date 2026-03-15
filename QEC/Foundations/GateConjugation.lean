import QEC.Foundations.Gates
import QEC.Foundations.Tensor

/-!
# Gate conjugation lemmas

Single place for all lemmas of the form U P U† = Q: conjugation of Pauli or tensor-Pauli
operators by unitary gates (gate inverse applied, then P, then gate). Definitions of the gates
and matrices live in `Gates.lean` and `Tensor.lean`.

## Hadamard (H)
## Phase gate (S)
## CNOT (control = first qubit, target = second)
-/

namespace Quantum

open Matrix
open Kronecker

/-! ### Hadamard

Conjugation convention: we state the action as H P H† (H applied, then P, then H†).
So H Z H† = X and H X H† = Z. The `H_adj_*_H` lemmas give H† P H (used when rewriting
conjugation by the transversal gate matrix star U * P * U).
-/

/-- H Z H† = X (Hadamard conjugates Z to X). -/
lemma H_conj_Z : H.val * Zmat * star H.val = Xmat := by
  matrix_expand[Hmat, Zmat, Xmat]

/-- H X H† = Z (Hadamard conjugates X to Z). -/
lemma H_conj_X : H.val * Xmat * star H.val = Zmat := by
  matrix_expand[Hmat, Xmat, Zmat]

/-- H† Z H = X. Used when rewriting conjugation by the adjoint transversal gate. -/
lemma H_adj_Z_H : star H.val * Zmat * H.val = Xmat := by
  matrix_expand[Hmat, Xmat, Zmat]

/-- H† X H = Z. Used when rewriting conjugation by the adjoint transversal gate. -/
lemma H_adj_X_H : star H.val * Xmat * H.val = Zmat := by
  matrix_expand[Hmat, Xmat, Zmat]

/-! ### Phase gate S

Conjugation convention: we state the action of S as S P S† (S applied, then P, then S†).
So S Z S† = Z and S X S† = Y.
-/

/-- S Z S† = Z (S commutes with Z). -/
lemma S_conj_Z : S.val * Zmat * star S.val = Zmat := by
  matrix_expand[Smat, Zmat]

/-- S X S† = Y (S conjugates X to Y). -/
lemma S_conj_X : S.val * Xmat * star S.val = Ymat := by
  matrix_expand[Smat, Xmat, Ymat]

/-- S† Z S = Z. Used when rewriting conjugation by the adjoint transversal gate. -/
lemma S_adj_Z_S : star S.val * Zmat * S.val = Zmat := by
  matrix_expand[Smat, Zmat]

/-- S† X S = -Y. Used when rewriting conjugation by the adjoint transversal gate. -/
lemma S_adj_X_S : star S.val * Xmat * S.val = -Ymat := by
  matrix_expand[Smat, Xmat, Ymat]

/-! ### CNOT (control = first qubit, target = second) -/

/-- CNOT† (X ⊗ I) CNOT = X ⊗ X. -/
lemma CNOT_adj_X_q1_CNOT : star CNOT.val * X_q1_2.val * CNOT.val = XX_2.val := by
  rw [CNOT, controllize_val, coe_X, X_q1_2, XX_2, tensorGate_val X 1, tensorGate_val X X]
  ext ⟨c₁, t₁⟩ ⟨c₂, t₂⟩
  fin_cases c₁ <;> fin_cases t₁ <;> fin_cases c₂ <;> fin_cases t₂ <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Xmat]

/-- CNOT† (I ⊗ X) CNOT = I ⊗ X. -/
lemma CNOT_adj_X_q2_CNOT : star CNOT.val * X_q2_2.val * CNOT.val = X_q2_2.val := by
  rw [CNOT, controllize_val, coe_X, X_q2_2, tensorGate_val 1 X]
  ext ⟨c₁, t₁⟩ ⟨c₂, t₂⟩
  fin_cases c₁ <;> fin_cases t₁ <;> fin_cases c₂ <;> fin_cases t₂ <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Xmat]

/-- CNOT† (Z ⊗ I) CNOT = Z ⊗ I. -/
lemma CNOT_adj_Z_q1_CNOT : star CNOT.val * Z_q1_2.val * CNOT.val = Z_q1_2.val := by
  rw [CNOT, controllize_val, coe_X, Z_q1_2, tensorGate_val Z 1]
  ext ⟨c₁, t₁⟩ ⟨c₂, t₂⟩
  fin_cases c₁ <;> fin_cases t₁ <;> fin_cases c₂ <;> fin_cases t₂ <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Zmat, Xmat]

/-- CNOT† (I ⊗ Z) CNOT = Z ⊗ Z. -/
lemma CNOT_adj_Z_q2_CNOT : star CNOT.val * Z_q2_2.val * CNOT.val = ZZ_2.val := by
  rw [CNOT, controllize_val, coe_X, Z_q2_2, ZZ_2, tensorGate_val 1 Z, tensorGate_val Z Z]
  ext ⟨c₁, t₁⟩ ⟨c₂, t₂⟩
  fin_cases c₁ <;> fin_cases t₁ <;> fin_cases c₂ <;> fin_cases t₂ <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Zmat, Xmat]

end Quantum
