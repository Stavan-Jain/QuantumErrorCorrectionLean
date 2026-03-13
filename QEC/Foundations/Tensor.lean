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

@[simp]
theorem star_kron
  {α β : Type*}
  [DecidableEq α] [Fintype α]
  [DecidableEq β] [Fintype β]
  (a : Matrix α α ℂ) (b : Matrix β β ℂ) :
  star (a ⊗ₖ b) = (star a) ⊗ₖ (star b) := by
  classical
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

/-- Tensor product of quantum states. -/
noncomputable def tensorState
  {α β : Type*} [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β]
  (ψ : QuantumState α) (φ : QuantumState β) :
  QuantumState (α × β) :=
by
  refine ⟨tensorVec ψ.val φ.val, ?_⟩
  -- use the norm lemma with hv := ψ.property, hw := φ.property
  exact norm_tensorVec_of_norm1 ψ.property φ.property

scoped notation ψ:60 " ⊗ₛ " φ:60 => tensorState ψ φ

noncomputable def X_q1_2 : TwoQubitGate :=
  tensorGate X 1

noncomputable def X_q2_2 : TwoQubitGate :=
  tensorGate 1 X

noncomputable def Z_q1_2 : TwoQubitGate :=
  tensorGate Z 1

noncomputable def Z_q2_2 : TwoQubitGate :=
  tensorGate 1 Z

noncomputable def X_q1Z_q2_2 : TwoQubitGate :=
  tensorGate X Z

/-- X on both qubits (X ⊗ X). -/
noncomputable def XX_2 : TwoQubitGate :=
  tensorGate X X

/-- Z on both qubits (Z ⊗ Z). -/
noncomputable def ZZ_2 : TwoQubitGate :=
  tensorGate Z Z

@[simp] lemma X_q1_2_on_ket00 : X_q1_2 • ket00 = ket10 := by
  vec_expand_simp [X_q1_2, Matrix.mulVec, ket00, ket10, Xmat]

@[simp] lemma X_q1_2_on_ket01 : X_q1_2 • ket01 = ket11 := by
  vec_expand_simp [X_q1_2,  Matrix.mulVec, ket01, ket11, Xmat]

@[simp] lemma X_q1_2_on_ket10 : X_q1_2 • ket10 = ket00 := by
  vec_expand_simp [X_q1_2,  Matrix.mulVec, ket10, ket00, Xmat]

@[simp] lemma X_q1_2_on_ket11 : X_q1_2 • ket11 = ket01 := by
  vec_expand_simp [X_q1_2,  Matrix.mulVec, ket11, ket01, Xmat]

@[simp] lemma X_q2_2_on_ket00 : X_q2_2 • ket00 = ket01 := by
  vec_expand_simp [X_q2_2,  Matrix.mulVec, ket00, ket01, Xmat]

@[simp] lemma X_q2_2_on_ket01 : X_q2_2 • ket01 = ket00 := by
  vec_expand_simp [X_q2_2,  Matrix.mulVec, ket01, ket00, Xmat]

@[simp] lemma X_q2_2_on_ket10 : X_q2_2 • ket10 = ket11 := by
  vec_expand_simp [X_q2_2,  Matrix.mulVec, ket10, ket11, Xmat]

@[simp] lemma X_q2_2_on_ket11 : X_q2_2 • ket11 = ket10 := by
  vec_expand_simp [X_q2_2,  Matrix.mulVec, ket11, ket10, Xmat]

-- X on first qubit, I on others: X ⊗ I ⊗ I
noncomputable def X_q1_3 : ThreeQubitGate :=
  tensorGate X 1

-- X on second qubit, I elsewhere: I ⊗ X ⊗ I
noncomputable def X_q2_3 : ThreeQubitGate :=
  tensorGate 1 (tensorGate X 1)

-- X on third qubit, I elsewhere: I ⊗ I ⊗ X
noncomputable def X_q3_3 : ThreeQubitGate :=
  tensorGate 1 (tensorGate 1 X)

-- X on qubits 1 2 3 (X ⊗ X ⊗ X)
noncomputable def X_q1q2q3_3 : ThreeQubitGate :=
  tensorGate X (tensorGate X X)

@[simp] lemma X_q1_3_on_ket000 : X_q1_3 • ket000 = ket100 := by
  vec_expand_simp [X_q1_3, Matrix.mulVec, Xmat]

@[simp] lemma X_q1_3_on_ket001 : X_q1_3 • ket001 = ket101 := by
  vec_expand_simp [X_q1_3, Matrix.mulVec, Xmat]

@[simp] lemma X_q1_3_on_ket010 : X_q1_3 • ket010 = ket110 := by
  vec_expand_simp [X_q1_3, Matrix.mulVec, Xmat]

@[simp] lemma X_q1_3_on_ket011 : X_q1_3 • ket011 = ket111 := by
  vec_expand_simp [X_q1_3, Matrix.mulVec, Xmat]

@[simp] lemma X_q1_3_on_ket100 : X_q1_3 • ket100 = ket000 := by
  vec_expand_simp [X_q1_3, Matrix.mulVec, Xmat]

@[simp] lemma X_q1_3_on_ket101 : X_q1_3 • ket101 = ket001 := by
  vec_expand_simp [X_q1_3, Matrix.mulVec, Xmat]

@[simp] lemma X_q1_3_on_ket110 : X_q1_3 • ket110 = ket010 := by
  vec_expand_simp [X_q1_3, Matrix.mulVec, Xmat]

@[simp] lemma X_q1_3_on_ket111 : X_q1_3 • ket111 = ket011 := by
  vec_expand_simp [X_q1_3, Matrix.mulVec, Xmat]

@[simp] lemma X_q1q2q3_on_ket000 : X_q1q2q3_3 • ket000 = ket111 := by
  vec_expand_simp[X_q1q2q3_3, Matrix.mulVec, Xmat]

@[simp] lemma X_q1q2q3_on_ket111 : X_q1q2q3_3 • ket111 = ket000 := by
  vec_expand_simp[X_q1q2q3_3, Matrix.mulVec, Xmat]

/-
  X_q2_3 : I ⊗ X ⊗ I
  Flips the second bit.
-/

@[simp] lemma X_q2_3_on_ket000 : X_q2_3 • ket000 = ket010 := by
  vec_expand_simp [X_q2_3, Matrix.mulVec, Xmat]

@[simp] lemma X_q2_3_on_ket001 : X_q2_3 • ket001 = ket011 := by
  vec_expand_simp [X_q2_3, Matrix.mulVec, Xmat]

@[simp] lemma X_q2_3_on_ket010 : X_q2_3 • ket010 = ket000 := by
  vec_expand_simp [X_q2_3, Matrix.mulVec, Xmat]

@[simp] lemma X_q2_3_on_ket011 : X_q2_3 • ket011 = ket001 := by
  vec_expand_simp [X_q2_3, Matrix.mulVec, Xmat]

@[simp] lemma X_q2_3_on_ket100 : X_q2_3 • ket100 = ket110 := by
  vec_expand_simp [X_q2_3, Matrix.mulVec, Xmat]

@[simp] lemma X_q2_3_on_ket101 : X_q2_3 • ket101 = ket111 := by
  vec_expand_simp [X_q2_3, Matrix.mulVec, Xmat]

@[simp] lemma X_q2_3_on_ket110 : X_q2_3 • ket110 = ket100 := by
  vec_expand_simp [X_q2_3, Matrix.mulVec, Xmat]

@[simp] lemma X_q2_3_on_ket111 : X_q2_3 • ket111 = ket101 := by
  vec_expand_simp [X_q2_3, Matrix.mulVec, Xmat]


/-
  X_q3_3 : I ⊗ I ⊗ X
  Flips the third bit.
-/

@[simp] lemma X_q3_3_on_ket000 : X_q3_3 • ket000 = ket001 := by
  vec_expand_simp [X_q3_3, Matrix.mulVec, Xmat]

@[simp] lemma X_q3_3_on_ket001 : X_q3_3 • ket001 = ket000 := by
  vec_expand_simp [X_q3_3, Matrix.mulVec, Xmat]

@[simp] lemma X_q3_3_on_ket010 : X_q3_3 • ket010 = ket011 := by
  vec_expand_simp [X_q3_3, Matrix.mulVec, Xmat]

@[simp] lemma X_q3_3_on_ket011 : X_q3_3 • ket011 = ket010 := by
  vec_expand_simp [X_q3_3, Matrix.mulVec, Xmat]

@[simp] lemma X_q3_3_on_ket100 : X_q3_3 • ket100 = ket101 := by
  vec_expand_simp [X_q3_3, Matrix.mulVec, Xmat]

@[simp] lemma X_q3_3_on_ket101 : X_q3_3 • ket101 = ket100 := by
  vec_expand_simp [X_q3_3, Matrix.mulVec, Xmat]

@[simp] lemma X_q3_3_on_ket110 : X_q3_3 • ket110 = ket111 := by
  vec_expand_simp [X_q3_3, Matrix.mulVec, Xmat]

@[simp] lemma X_q3_3_on_ket111 : X_q3_3 • ket111 = ket110 := by
  vec_expand_simp [X_q3_3, Matrix.mulVec, Xmat]

/-- CNOT on qubits 1 (control) and 2 (target) of a 3-qubit register. -/
noncomputable def CNOT_q1_q2_3 : ThreeQubitGate :=
  -- control on q1, gate on (q2,q3) flips q2 only
  controllize (X_q1_2)

/-- CNOT on qubits 1 (control) and 3 (target) of a 3-qubit register. -/
noncomputable def CNOT_q1_q3_3 : ThreeQubitGate :=
  -- control on q1, gate on (q2,q3) flips q3 only
  controllize (X_q2_2)

/-- CNOT on qubits 2 (control) and 3 (target) of a 3-qubit register. -/
noncomputable def CNOT_q2_q3_3 : ThreeQubitGate :=
  -- identity on q1, CNOT on (q2,q3)
  tensorGate (1 : OneQubitGate) CNOT

@[simp] lemma CNOT_q2_q3_3_on_ket000 : CNOT_q2_q3_3 • ket000 = ket000 := by
  vec_expand_simp [CNOT_q2_q3_3, Matrix.mulVec, CNOT, controllize, Xmat]

@[simp] lemma CNOT_q2_q3_3_on_ket001 : CNOT_q2_q3_3 • ket001 = ket001 := by
  vec_expand_simp [CNOT_q2_q3_3,  Matrix.mulVec, CNOT, controllize, Xmat]

@[simp] lemma CNOT_q2_q3_3_on_ket010 : CNOT_q2_q3_3 • ket010 = ket011 := by
  vec_expand_simp [CNOT_q2_q3_3,  Matrix.mulVec, CNOT, controllize, Xmat]

@[simp] lemma CNOT_q2_q3_3_on_ket011 : CNOT_q2_q3_3 • ket011 = ket010 := by
  vec_expand_simp [CNOT_q2_q3_3,  Matrix.mulVec, CNOT, controllize, Xmat]

@[simp] lemma CNOT_q2_q3_3_on_ket100 : CNOT_q2_q3_3 • ket100 = ket100 := by
  vec_expand_simp [CNOT_q2_q3_3,  Matrix.mulVec, CNOT, controllize, Xmat]

@[simp] lemma CNOT_q2_q3_3_on_ket101 : CNOT_q2_q3_3 • ket101 = ket101 := by
  vec_expand_simp [CNOT_q2_q3_3,  Matrix.mulVec, CNOT, controllize, Xmat]

@[simp] lemma CNOT_q2_q3_3_on_ket110 : CNOT_q2_q3_3 • ket110 = ket111 := by
  vec_expand_simp [CNOT_q2_q3_3,  Matrix.mulVec, CNOT, controllize, Xmat]

@[simp] lemma CNOT_q2_q3_3_on_ket111 : CNOT_q2_q3_3 • ket111 = ket110 := by
  vec_expand_simp [CNOT_q2_q3_3,  Matrix.mulVec, CNOT, controllize, Xmat]

end Quantum
