import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import QEC.Stabilizer.Foundations.PauliGroupSingle
import QEC.Stabilizer.Foundations.PauliGroupSingle.Operator
import QEC.Stabilizer.Foundations.PauliGroup.NQubitOperator

namespace Quantum

/-!
# Binary symplectic representation: core

Each Pauli operator (ignoring phase) corresponds to a vector over F₂ = ZMod 2:
- Single-qubit: P = X^x Z^z with x,z ∈ {0,1} → (x,z) : ZMod 2 × ZMod 2.
- n-qubit: first n components = X-part, last n = Z-part → Fin (n + n) → ZMod 2.
-/

variable {n : ℕ}

namespace PauliOperator

/-- Binary (x,z) components: P = X^x Z^z with x,z ∈ {0,1}. I → (0,0), X → (1,0),
Y → (1,1), Z → (0,1). -/
def toSymplecticSingle (P : PauliOperator) : ZMod 2 × ZMod 2 :=
  match P with
  | I => (0, 0)
  | X => (1, 0)
  | Y => (1, 1)
  | Z => (0, 1)

@[simp] lemma toSymplecticSingle_I : toSymplecticSingle I = (0, 0) := rfl
@[simp] lemma toSymplecticSingle_X : toSymplecticSingle X = (1, 0) := rfl
@[simp] lemma toSymplecticSingle_Y : toSymplecticSingle Y = (1, 1) := rfl
@[simp] lemma toSymplecticSingle_Z : toSymplecticSingle Z = (0, 1) := rfl

/-- Distinct single-qubit Pauli operators have distinct symplectic (x,z) pairs.
-/
lemma toSymplecticSingle_injective : Function.Injective toSymplecticSingle := by
  rintro a b h
  cases a <;> cases b <;> simp at h <;> rfl

/-- The symplectic (x,z) of the product operator is the sum mod 2 of the two
(x,z) pairs. (The phase of P.mulOp Q does not affect the operator part.) -/
lemma toSymplecticSingle_add (P Q : PauliOperator) :
    ((P.mulOp Q).operator).toSymplecticSingle =
    (P.toSymplecticSingle.1 + Q.toSymplecticSingle.1, P.toSymplecticSingle.2 +
    Q.toSymplecticSingle.2) := by
  cases P <;> cases Q <;> simp [toSymplecticSingle_I, toSymplecticSingle_X,
    toSymplecticSingle_Y, toSymplecticSingle_Z]
  all_goals rfl

end PauliOperator

namespace NQubitPauliOperator

/-- The symplectic vector of an n-qubit Pauli operator: Fin (n + n) → ZMod 2.
Indices 0..n-1 are the X-components, indices n..2n-1 are the Z-components. We
use (n + n) so that Fin.castAdd and Fin.natAdd give valid indices. -/
def toSymplectic (op : NQubitPauliOperator n) (j : Fin (n + n)) : ZMod 2 :=
  if h : j.val < n then
    (op ⟨j.val, h⟩).toSymplecticSingle.1
  else
    (op ⟨j.val - n, by have := j.2; omega⟩).toSymplecticSingle.2

/-- Index `castAdd n i` (in the first n positions) is the X-component of qubit
`i`. -/
lemma toSymplectic_X_part (op : NQubitPauliOperator n) (i : Fin n) :
    toSymplectic op (Fin.castAdd n i) = (op i).toSymplecticSingle.1 := by
  simp only [toSymplectic]
  have hlt : (Fin.castAdd n i).val < n := i.2
  simp

/-- Index `natAdd n i` (in the last n positions) is the Z-component of qubit
`i`. -/
lemma toSymplectic_Z_part (op : NQubitPauliOperator n) (i : Fin n) :
    toSymplectic op (Fin.natAdd n i) = (op i).toSymplecticSingle.2 := by
  simp only [toSymplectic]
  have hge : ¬(Fin.natAdd n i).val < n := by simp [Fin.natAdd]
  simp

/-- The all-X n-qubit operator has X-component 1 at every qubit. -/
lemma toSymplectic_X_one (i : Fin n) :
    toSymplectic (X n) (Fin.castAdd n i) = 1 := by
  rw [toSymplectic_X_part]; simp only [X, PauliOperator.toSymplecticSingle_X]

/-- The all-Z n-qubit operator has Z-component 1 at every qubit. -/
lemma toSymplectic_Z_one (i : Fin n) :
    toSymplectic (Z n) (Fin.natAdd n i) = 1 := by
  rw [toSymplectic_Z_part]; simp only [Z, PauliOperator.toSymplecticSingle_Z]

/-- Extensionality: equal operators give equal symplectic vectors. -/
lemma toSymplectic_congr (op₁ op₂ : NQubitPauliOperator n) (h : op₁ = op₂) (j : Fin (n + n)) :
    toSymplectic op₁ j = toSymplectic op₂ j := by rw [h]

/-- Two n-qubit operators have the same symplectic vector iff they are equal. -/
theorem toSymplectic_injective :
    Function.Injective (toSymplectic : NQubitPauliOperator n → Fin (n + n) → ZMod 2) := by
  intro op₁ op₂ h
  ext i
  have hX : toSymplectic op₁ (Fin.castAdd n i) = toSymplectic op₂ (Fin.castAdd n i) := by rw [h]
  have hZ : toSymplectic op₁ (Fin.natAdd n i) = toSymplectic op₂ (Fin.natAdd n i) := by rw [h]
  rw [toSymplectic_X_part, toSymplectic_X_part] at hX
  rw [toSymplectic_Z_part, toSymplectic_Z_part] at hZ
  have h_single : (op₁ i).toSymplecticSingle = (op₂ i).toSymplecticSingle := by
    ext <;> [exact hX; exact hZ]
  exact PauliOperator.toSymplecticSingle_injective h_single

end NQubitPauliOperator

end Quantum
