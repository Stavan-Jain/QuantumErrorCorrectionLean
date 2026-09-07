import QEC.Foundations.Basic
import QEC.Foundations.Gates

/-!
# Tensor Products

This file defines tensor products for quantum gates and states, which are fundamental
operations in quantum computing for combining multiple quantum systems.

## Tensor Products of Gates

The tensor product of two quantum gates `G₁ : QuantumGate α` and `G₂ : QuantumGate β`
produces a gate `G₁ ⊗ᵍ G₂ : QuantumGate (α × β)` that acts independently on the two
subsystems. The matrix representation is the Kronecker product of the individual gate matrices.

## Tensor Products of States

The tensor product of two quantum states `ψ : QuantumState α` and `φ : QuantumState β`
produces a state `ψ ⊗ₛ φ : QuantumState (α × β)` representing the joint system.
The vector representation multiplies amplitudes component-wise.

## Key Properties

- Tensor products preserve unitarity (tensor of unitary gates is unitary)
- Tensor products preserve normalization (tensor of normalized states is normalized)
- The Kronecker product satisfies `(A ⊗ B)ᴴ = Aᴴ ⊗ Bᴴ`
-/
namespace Quantum

open Matrix
open Kronecker

/-- The conjugate transpose of a Kronecker product is the Kronecker product of the
conjugate transposes. -/
@[simp]
theorem star_kron
  {α β : Type*}
  (a : Matrix α α ℂ) (b : Matrix β β ℂ) :
  star (a ⊗ₖ b) = (star a) ⊗ₖ (star b) := by
  ext i j
  simp

/--
If `a` and `b` are unitary, then their Kronecker product is unitary.
-/
theorem kron_unitary
  {α β : Type*}
  [DecidableEq α] [Fintype α]
  [DecidableEq β] [Fintype β]
  (a : Matrix.unitaryGroup α ℂ)
  (b : Matrix.unitaryGroup β ℂ) :
  a.val ⊗ₖ b.val ∈ Matrix.unitaryGroup (α × β) ℂ := by
  classical
  simp [Matrix.mem_unitaryGroup_iff, star_kron, ← Matrix.mul_kronecker_mul]

/-- Tensor product of two gates: the Kronecker product of their matrices, acting
independently on the two subsystems. -/
noncomputable def tensorGate
  {α β : Type*}
  [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β]
  (G₁ : QuantumGate α) (G₂ : QuantumGate β) :
  QuantumGate (α × β) :=
by
  classical
  refine ⟨G₁.val ⊗ₖ G₂.val, ?_⟩
  simp [kron_unitary (a := G₁) (b := G₂)]

scoped notation G₁:60 " ⊗ᵍ " G₂:60 => tensorGate G₁ G₂

/-- The matrix underlying `tensorGate G₁ G₂` is the Kronecker product `G₁ ⊗ₖ G₂`. -/
@[simp]
lemma tensorGate_val
  {α β : Type*} [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β]
  (G₁ : QuantumGate α) (G₂ : QuantumGate β) :
  (tensorGate G₁ G₂ : Matrix (α × β) (α × β) ℂ) =
    G₁.val ⊗ₖ G₂.val :=
rfl

open scoped BigOperators

/-- Tensor product of vectors (not yet normalized). -/
noncomputable def tensorVec
  {α β : Type*} [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β]
  (v : Vector α) (w : Vector β) : Vector (α × β) :=
  fun ij => v ij.1 * w ij.2

/-- The norm of a tensor product of normalized states is 1. -/
lemma norm_tensorVec_of_norm1
  {α β : Type*} [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β]
  {v : Vector α} {w : Vector β}
  (hv : norm v = 1) (hw : norm w = 1) :
  norm (tensorVec v w) = 1 :=
by
  unfold Quantum.tensorVec;
  simp [mul_pow]
  erw [ Finset.sum_product ]
  simp_all [ ←Finset.mul_sum]

/-- Tensor product of two quantum states: amplitudes multiply component-wise,
and the result is again normalized. -/
noncomputable def tensorState
  {α β : Type*} [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β]
  (ψ : QuantumState α) (φ : QuantumState β) :
  QuantumState (α × β) :=
by
  refine ⟨tensorVec ψ.val φ.val, ?_⟩
  exact norm_tensorVec_of_norm1 ψ.property φ.property

scoped notation ψ:60 " ⊗ₛ " φ:60 => tensorState ψ φ

/-- X on the first of two qubits (X ⊗ I). -/
noncomputable def X_q1_2 : TwoQubitGate :=
  X ⊗ᵍ 1

/-- X on the second of two qubits (I ⊗ X). -/
noncomputable def X_q2_2 : TwoQubitGate :=
  1 ⊗ᵍ X

/-- Z on the first of two qubits (Z ⊗ I). -/
noncomputable def Z_q1_2 : TwoQubitGate :=
  Z ⊗ᵍ 1

/-- Z on the second of two qubits (I ⊗ Z). -/
noncomputable def Z_q2_2 : TwoQubitGate :=
  1 ⊗ᵍ Z

/-- X on the first qubit and Z on the second (X ⊗ Z). -/
noncomputable def X_q1Z_q2_2 : TwoQubitGate :=
  X ⊗ᵍ Z

/-- X on both qubits (X ⊗ X). -/
noncomputable def XX_2 : TwoQubitGate :=
  X ⊗ᵍ X

/-- Z on both qubits (Z ⊗ Z). -/
noncomputable def ZZ_2 : TwoQubitGate :=
  Z ⊗ᵍ Z

/-- X ⊗ I: |00⟩ ↦ |10⟩. -/
@[simp] lemma X_q1_2_on_ket00 : X_q1_2 • |00⟩ = |10⟩ := by
  vec_expand_simp [X_q1_2, Matrix.mulVec, ket00, ket10, Xmat]

/-- X ⊗ I: |01⟩ ↦ |11⟩. -/
@[simp] lemma X_q1_2_on_ket01 : X_q1_2 • |01⟩ = |11⟩ := by
  vec_expand_simp [X_q1_2,  Matrix.mulVec, ket01, ket11, Xmat]

/-- X ⊗ I: |10⟩ ↦ |00⟩. -/
@[simp] lemma X_q1_2_on_ket10 : X_q1_2 • |10⟩ = |00⟩ := by
  vec_expand_simp [X_q1_2,  Matrix.mulVec, ket10, ket00, Xmat]

/-- X ⊗ I: |11⟩ ↦ |01⟩. -/
@[simp] lemma X_q1_2_on_ket11 : X_q1_2 • |11⟩ = |01⟩ := by
  vec_expand_simp [X_q1_2,  Matrix.mulVec, ket11, ket01, Xmat]

/-- I ⊗ X: |00⟩ ↦ |01⟩. -/
@[simp] lemma X_q2_2_on_ket00 : X_q2_2 • |00⟩ = |01⟩ := by
  vec_expand_simp [X_q2_2,  Matrix.mulVec, ket00, ket01, Xmat]

/-- I ⊗ X: |01⟩ ↦ |00⟩. -/
@[simp] lemma X_q2_2_on_ket01 : X_q2_2 • |01⟩ = |00⟩ := by
  vec_expand_simp [X_q2_2,  Matrix.mulVec, ket01, ket00, Xmat]

/-- I ⊗ X: |10⟩ ↦ |11⟩. -/
@[simp] lemma X_q2_2_on_ket10 : X_q2_2 • |10⟩ = |11⟩ := by
  vec_expand_simp [X_q2_2,  Matrix.mulVec, ket10, ket11, Xmat]

/-- I ⊗ X: |11⟩ ↦ |10⟩. -/
@[simp] lemma X_q2_2_on_ket11 : X_q2_2 • |11⟩ = |10⟩ := by
  vec_expand_simp [X_q2_2,  Matrix.mulVec, ket11, ket10, Xmat]

/-- X on the first of three qubits (X ⊗ I ⊗ I). -/
noncomputable def X_q1_3 : ThreeQubitGate :=
  X ⊗ᵍ 1

/-- X on the second of three qubits (I ⊗ X ⊗ I). -/
noncomputable def X_q2_3 : ThreeQubitGate :=
  1 ⊗ᵍ X ⊗ᵍ 1

/-- X on the third of three qubits (I ⊗ I ⊗ X). -/
noncomputable def X_q3_3 : ThreeQubitGate :=
  1 ⊗ᵍ 1 ⊗ᵍ X

/-- X on all three qubits (X ⊗ X ⊗ X). -/
noncomputable def X_q1q2q3_3 : ThreeQubitGate :=
  X ⊗ᵍ X ⊗ᵍ X

/-- X ⊗ I ⊗ I: |000⟩ ↦ |100⟩. -/
@[simp] lemma X_q1_3_on_ket000 : X_q1_3 • |000⟩ = |100⟩ := by
  vec_expand_simp [X_q1_3, Matrix.mulVec, Xmat]

/-- X ⊗ I ⊗ I: |001⟩ ↦ |101⟩. -/
@[simp] lemma X_q1_3_on_ket001 : X_q1_3 • |001⟩ = |101⟩ := by
  vec_expand_simp [X_q1_3, Matrix.mulVec, Xmat]

/-- X ⊗ I ⊗ I: |010⟩ ↦ |110⟩. -/
@[simp] lemma X_q1_3_on_ket010 : X_q1_3 • |010⟩ = |110⟩ := by
  vec_expand_simp [X_q1_3, Matrix.mulVec, Xmat]

/-- X ⊗ I ⊗ I: |011⟩ ↦ |111⟩. -/
@[simp] lemma X_q1_3_on_ket011 : X_q1_3 • |011⟩ = |111⟩ := by
  vec_expand_simp [X_q1_3, Matrix.mulVec, Xmat]

/-- X ⊗ I ⊗ I: |100⟩ ↦ |000⟩. -/
@[simp] lemma X_q1_3_on_ket100 : X_q1_3 • |100⟩ = |000⟩ := by
  vec_expand_simp [X_q1_3, Matrix.mulVec, Xmat]

/-- X ⊗ I ⊗ I: |101⟩ ↦ |001⟩. -/
@[simp] lemma X_q1_3_on_ket101 : X_q1_3 • |101⟩ = |001⟩ := by
  vec_expand_simp [X_q1_3, Matrix.mulVec, Xmat]

/-- X ⊗ I ⊗ I: |110⟩ ↦ |010⟩. -/
@[simp] lemma X_q1_3_on_ket110 : X_q1_3 • |110⟩ = |010⟩ := by
  vec_expand_simp [X_q1_3, Matrix.mulVec, Xmat]

/-- X ⊗ I ⊗ I: |111⟩ ↦ |011⟩. -/
@[simp] lemma X_q1_3_on_ket111 : X_q1_3 • |111⟩ = |011⟩ := by
  vec_expand_simp [X_q1_3, Matrix.mulVec, Xmat]

/-- X ⊗ X ⊗ X: |000⟩ ↦ |111⟩. -/
@[simp] lemma X_q1q2q3_on_ket000 : X_q1q2q3_3 • |000⟩ = |111⟩ := by
  vec_expand_simp[X_q1q2q3_3, Matrix.mulVec, Xmat]

/-- X ⊗ X ⊗ X: |111⟩ ↦ |000⟩. -/
@[simp] lemma X_q1q2q3_on_ket111 : X_q1q2q3_3 • |111⟩ = |000⟩ := by
  vec_expand_simp[X_q1q2q3_3, Matrix.mulVec, Xmat]

/-! ### `X_q2_3` (I ⊗ X ⊗ I): flips the second bit -/


/-- I ⊗ X ⊗ I: |000⟩ ↦ |010⟩. -/
@[simp] lemma X_q2_3_on_ket000 : X_q2_3 • |000⟩ = |010⟩ := by
  vec_expand_simp [X_q2_3, Matrix.mulVec, Xmat]

/-- I ⊗ X ⊗ I: |001⟩ ↦ |011⟩. -/
@[simp] lemma X_q2_3_on_ket001 : X_q2_3 • |001⟩ = |011⟩ := by
  vec_expand_simp [X_q2_3, Matrix.mulVec, Xmat]

/-- I ⊗ X ⊗ I: |010⟩ ↦ |000⟩. -/
@[simp] lemma X_q2_3_on_ket010 : X_q2_3 • |010⟩ = |000⟩ := by
  vec_expand_simp [X_q2_3, Matrix.mulVec, Xmat]

/-- I ⊗ X ⊗ I: |011⟩ ↦ |001⟩. -/
@[simp] lemma X_q2_3_on_ket011 : X_q2_3 • |011⟩ = |001⟩ := by
  vec_expand_simp [X_q2_3, Matrix.mulVec, Xmat]

/-- I ⊗ X ⊗ I: |100⟩ ↦ |110⟩. -/
@[simp] lemma X_q2_3_on_ket100 : X_q2_3 • |100⟩ = |110⟩ := by
  vec_expand_simp [X_q2_3, Matrix.mulVec, Xmat]

/-- I ⊗ X ⊗ I: |101⟩ ↦ |111⟩. -/
@[simp] lemma X_q2_3_on_ket101 : X_q2_3 • |101⟩ = |111⟩ := by
  vec_expand_simp [X_q2_3, Matrix.mulVec, Xmat]

/-- I ⊗ X ⊗ I: |110⟩ ↦ |100⟩. -/
@[simp] lemma X_q2_3_on_ket110 : X_q2_3 • |110⟩ = |100⟩ := by
  vec_expand_simp [X_q2_3, Matrix.mulVec, Xmat]

/-- I ⊗ X ⊗ I: |111⟩ ↦ |101⟩. -/
@[simp] lemma X_q2_3_on_ket111 : X_q2_3 • |111⟩ = |101⟩ := by
  vec_expand_simp [X_q2_3, Matrix.mulVec, Xmat]


/-! ### `X_q3_3` (I ⊗ I ⊗ X): flips the third bit -/


/-- I ⊗ I ⊗ X: |000⟩ ↦ |001⟩. -/
@[simp] lemma X_q3_3_on_ket000 : X_q3_3 • |000⟩ = |001⟩ := by
  vec_expand_simp [X_q3_3, Matrix.mulVec, Xmat]

/-- I ⊗ I ⊗ X: |001⟩ ↦ |000⟩. -/
@[simp] lemma X_q3_3_on_ket001 : X_q3_3 • |001⟩ = |000⟩ := by
  vec_expand_simp [X_q3_3, Matrix.mulVec, Xmat]

/-- I ⊗ I ⊗ X: |010⟩ ↦ |011⟩. -/
@[simp] lemma X_q3_3_on_ket010 : X_q3_3 • |010⟩ = |011⟩ := by
  vec_expand_simp [X_q3_3, Matrix.mulVec, Xmat]

/-- I ⊗ I ⊗ X: |011⟩ ↦ |010⟩. -/
@[simp] lemma X_q3_3_on_ket011 : X_q3_3 • |011⟩ = |010⟩ := by
  vec_expand_simp [X_q3_3, Matrix.mulVec, Xmat]

/-- I ⊗ I ⊗ X: |100⟩ ↦ |101⟩. -/
@[simp] lemma X_q3_3_on_ket100 : X_q3_3 • |100⟩ = |101⟩ := by
  vec_expand_simp [X_q3_3, Matrix.mulVec, Xmat]

/-- I ⊗ I ⊗ X: |101⟩ ↦ |100⟩. -/
@[simp] lemma X_q3_3_on_ket101 : X_q3_3 • |101⟩ = |100⟩ := by
  vec_expand_simp [X_q3_3, Matrix.mulVec, Xmat]

/-- I ⊗ I ⊗ X: |110⟩ ↦ |111⟩. -/
@[simp] lemma X_q3_3_on_ket110 : X_q3_3 • |110⟩ = |111⟩ := by
  vec_expand_simp [X_q3_3, Matrix.mulVec, Xmat]

/-- I ⊗ I ⊗ X: |111⟩ ↦ |110⟩. -/
@[simp] lemma X_q3_3_on_ket111 : X_q3_3 • |111⟩ = |110⟩ := by
  vec_expand_simp [X_q3_3, Matrix.mulVec, Xmat]

/-- CNOT on qubits 1 (control) and 2 (target) of a 3-qubit register.

The control sits on q1 and the controlled gate on `(q2, q3)` flips q2 only.
-/
noncomputable def CNOT_q1_q2_3 : ThreeQubitGate :=
  controllize (X_q1_2)

/-- CNOT on qubits 1 (control) and 3 (target) of a 3-qubit register.

The control sits on q1 and the controlled gate on `(q2, q3)` flips q3 only.
-/
noncomputable def CNOT_q1_q3_3 : ThreeQubitGate :=
  controllize (X_q2_2)

/-- CNOT on qubits 2 (control) and 3 (target) of a 3-qubit register.

This is the identity on q1 tensored with CNOT on `(q2, q3)`.
-/
noncomputable def CNOT_q2_q3_3 : ThreeQubitGate :=
  (1 : OneQubitGate) ⊗ᵍ CNOT

/-- CNOT with control q2 and target q3: |000⟩ ↦ |000⟩. -/
@[simp] lemma CNOT_q2_q3_3_on_ket000 : CNOT_q2_q3_3 • |000⟩ = |000⟩ := by
  vec_expand_simp [CNOT_q2_q3_3, Matrix.mulVec, CNOT, controllize, Xmat]

/-- CNOT with control q2 and target q3: |001⟩ ↦ |001⟩. -/
@[simp] lemma CNOT_q2_q3_3_on_ket001 : CNOT_q2_q3_3 • |001⟩ = |001⟩ := by
  vec_expand_simp [CNOT_q2_q3_3,  Matrix.mulVec, CNOT, controllize, Xmat]

/-- CNOT with control q2 and target q3: |010⟩ ↦ |011⟩. -/
@[simp] lemma CNOT_q2_q3_3_on_ket010 : CNOT_q2_q3_3 • |010⟩ = |011⟩ := by
  vec_expand_simp [CNOT_q2_q3_3,  Matrix.mulVec, CNOT, controllize, Xmat]

/-- CNOT with control q2 and target q3: |011⟩ ↦ |010⟩. -/
@[simp] lemma CNOT_q2_q3_3_on_ket011 : CNOT_q2_q3_3 • |011⟩ = |010⟩ := by
  vec_expand_simp [CNOT_q2_q3_3,  Matrix.mulVec, CNOT, controllize, Xmat]

/-- CNOT with control q2 and target q3: |100⟩ ↦ |100⟩. -/
@[simp] lemma CNOT_q2_q3_3_on_ket100 : CNOT_q2_q3_3 • |100⟩ = |100⟩ := by
  vec_expand_simp [CNOT_q2_q3_3,  Matrix.mulVec, CNOT, controllize, Xmat]

/-- CNOT with control q2 and target q3: |101⟩ ↦ |101⟩. -/
@[simp] lemma CNOT_q2_q3_3_on_ket101 : CNOT_q2_q3_3 • |101⟩ = |101⟩ := by
  vec_expand_simp [CNOT_q2_q3_3,  Matrix.mulVec, CNOT, controllize, Xmat]

/-- CNOT with control q2 and target q3: |110⟩ ↦ |111⟩. -/
@[simp] lemma CNOT_q2_q3_3_on_ket110 : CNOT_q2_q3_3 • |110⟩ = |111⟩ := by
  vec_expand_simp [CNOT_q2_q3_3,  Matrix.mulVec, CNOT, controllize, Xmat]

/-- CNOT with control q2 and target q3: |111⟩ ↦ |110⟩. -/
@[simp] lemma CNOT_q2_q3_3_on_ket111 : CNOT_q2_q3_3 • |111⟩ = |110⟩ := by
  vec_expand_simp [CNOT_q2_q3_3,  Matrix.mulVec, CNOT, controllize, Xmat]

end Quantum
