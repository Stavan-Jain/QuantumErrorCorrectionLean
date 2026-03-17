import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Group.Defs
import QEC.Foundations.Foundations
import QEC.Stabilizer.PauliGroupSingle
import QEC.Stabilizer.PauliGroup.NQubitElement

namespace Quantum
open Matrix
open scoped BigOperators

variable {n : ℕ}

namespace NQubitPauliGroupElement

/-!
# Matrix and gate representation of n-qubit Pauli group elements

Every `NQubitPauliGroupElement n` has a **matrix** on the computational basis
`NQubitBasis n` and, when the matrix is unitary, a bundled **`QuantumGate`** view.

## What this file provides

- **`toMatrix`**: group element → complex matrix (phase factor × tensor product of
  single-qubit Pauli matrices). Lemmas such as `toMatrix_mul` show multiplication
  in the Pauli group matches matrix multiplication.
- **`toGate`**: same underlying matrix as a `QuantumGate` when unitary (Pauli matrices
  are unitary, so every element gives a gate).
- **Phase handling**: e.g. `minusOne_toMatrix` — phase power 2 (−1) scales the
  identity matrix by −1.
- Bridge lemmas between `toMatrix`, `toGate`, and stabilizer/code constructions that
  conjugate or sum matrices (`stabilizerSum`, logical gates, etc.).

Use this module when you need to relate **abstract Pauli products** to **concrete
matrices** acting on `NQubitState n` or on amplitude vectors.
-/

@[simp] lemma toMatrix_one (n : ℕ) :
  ((1 : NQubitPauliGroupElement n).toMatrix) = (1 : Matrix (NQubitBasis n) (NQubitBasis n) ℂ) := by
  simp [toMatrix, NQubitPauliOperator.identity_toMatrix]

/-- The matrix of -I (phase -1, identity on all qubits) is -1 times the identity matrix. -/
@[simp] lemma minusOne_toMatrix (n : ℕ) :
  (minusOne n).toMatrix = (-1 : ℂ) • (1 : Matrix (NQubitBasis n) (NQubitBasis n) ℂ) := by
  rw [toMatrix, minusOne_operators, minusOne_phasePower, PauliGroupElement.phasePowerToComplex_2,
    NQubitPauliOperator.identity_toMatrix]

/-- The identity n-qubit Pauli group element maps to the identity gate. -/
@[simp] lemma toGate_one (n : ℕ) :
  toGate (1 : NQubitPauliGroupElement n) = (1 : QuantumGate (NQubitBasis n)) := by
  apply Subtype.ext
  rw [toGate_val, toMatrix_one]
  rfl

/-- Group multiplication corresponds to matrix multiplication. -/
lemma toMatrix_mul (p q : NQubitPauliGroupElement n) :
  (p * q).toMatrix = p.toMatrix * q.toMatrix := by
    unfold NQubitPauliGroupElement.toMatrix;
    ext b₁ b₂;
    have h_expand : (p.operators.toMatrix * q.operators.toMatrix) b₁ b₂ =
    ∑ k : Fin n → QubitBasis, (∏ i, (p.operators i).toMatrix (b₁ i) (k i)) *
    (∏ i, (q.operators i).toMatrix (k i) (b₂ i)) := by
      rfl;
    have h_expand_further : ∑ k : Fin n → QubitBasis,
    (∏ i, (p.operators i).toMatrix (b₁ i) (k i)) *
    (∏ i, (q.operators i).toMatrix (k i) (b₂ i)) =
    ∏ i, (∑ k : QubitBasis, (p.operators i).toMatrix (b₁ i) k *
    (q.operators i).toMatrix k (b₂ i)) := by
      simp only [← Finset.prod_mul_distrib];
      exact
        Eq.symm
          (Fintype.prod_sum fun i j ↦
            (p.operators i).toMatrix (b₁ i) j * (q.operators i).toMatrix j (b₂ i));
    have h_expand_single_qubit :
        ∀ i : Fin n,
          (∑ k : QubitBasis,
              (p.operators i).toMatrix (b₁ i) k * (q.operators i).toMatrix k (b₂ i)) =
              PauliGroupElement.phasePowerToComplex
                (PauliOperator.mulOp (p.operators i) (q.operators i)).phasePower *
              (PauliOperator.mulOp (p.operators i) (q.operators i)).operator.toMatrix
                (b₁ i) (b₂ i) := by
      intro i
      have h_single_qubit :
          ∀ (P Q : PauliOperator),
            (P.toMatrix * Q.toMatrix) =
              PauliGroupElement.phasePowerToComplex
                  (PauliOperator.mulOp P Q).phasePower •
                (PauliOperator.mulOp P Q).operator.toMatrix := by
        exact fun P Q ↦ PauliGroupElement.PauliOperator.toMatrix_mul P Q
      convert
        congr_arg (fun m => m (b₁ i) (b₂ i)) (h_single_qubit (p.operators i) (q.operators i))
          using 1
    simp_all +decide [Finset.prod_mul_distrib, Matrix.mul_apply]
    have h_phasePowerToComplex :
        PauliGroupElement.phasePowerToComplex (p.mul q).phasePower =
          PauliGroupElement.phasePowerToComplex p.phasePower *
            PauliGroupElement.phasePowerToComplex q.phasePower *
            (∏ i,
              PauliGroupElement.phasePowerToComplex
                ((p.operators i).mulOp (q.operators i)).phasePower) := by
      have h_phasePowerToComplex :
          ∀ (a b c : Fin 4),
                PauliGroupElement.phasePowerToComplex (a + b + c) =
              PauliGroupElement.phasePowerToComplex a *
                PauliGroupElement.phasePowerToComplex b *
                PauliGroupElement.phasePowerToComplex c := by
        exact fun a b c ↦ Eq.symm (PauliGroupElement.phasePowerToComplex_add3 a b c)
      convert
        h_phasePowerToComplex p.phasePower q.phasePower
            (∑ i : Fin n,
              ((p.operators i).mulOp (q.operators i) |> PauliGroupElement.phasePower))
          using 1
      have h_phasePowerToComplex :
          ∀ (s : Finset (Fin n)),
            (∏ i ∈ s,
                PauliGroupElement.phasePowerToComplex
                  ((p.operators i).mulOp (q.operators i)).phasePower) =
              PauliGroupElement.phasePowerToComplex
                (∑ i ∈ s, ((p.operators i).mulOp (q.operators i)).phasePower) := by
        intro s
        induction s using Finset.induction <;>
          simp_all +decide [Finset.sum_insert, Finset.prod_insert]
        (expose_names;
          exact
            PauliGroupElement.phasePowerToComplex_add
              ((p.operators a).mulOp (q.operators a)).phasePower
              (∑ i ∈ s, ((p.operators i).mulOp (q.operators i)).phasePower))
      rw [h_phasePowerToComplex]
    simp_all +decide [ mul_comm, mul_left_comm ];
    convert
      congr_arg
          (fun x : ℂ =>
            x *
              (PauliGroupElement.phasePowerToComplex p.phasePower *
                PauliGroupElement.phasePowerToComplex q.phasePower))
          h_expand.symm using 1 <;>
      ring_nf
    · simp [ mul_comm, mul_left_comm, NQubitPauliOperator.toMatrix ];
      simp [ NQubitPauliGroupElement.mul ];
      simp [  NQubitPauliGroupElement.mulOp ];
      ring;
    · simp only [mul_comm, Finset.mul_sum];
      ac_rfl

/-- Group inverse corresponds to matrix inverse. -/
lemma toMatrix_inv (p : NQubitPauliGroupElement n) :
  (p⁻¹).toMatrix = (p.toMatrix)⁻¹ := by
  have h_unitary :
      ∀ (p : NQubitPauliGroupElement n), p.toMatrix⁻¹ = p⁻¹.toMatrix := by
    intro p
    rw [Matrix.inv_eq_right_inv]
    have h_unitary :
        ∀ (p : NQubitPauliGroupElement n),
          p.toMatrix * p⁻¹.toMatrix = (p * p⁻¹).toMatrix := by
      exact fun p ↦ Eq.symm (toMatrix_mul p p⁻¹)
    rw [h_unitary, mul_inv_cancel, toMatrix_one]
  exact h_unitary p ▸ rfl

/-- `toGate` is a group homomorphism. -/
lemma toGate_mul (p q : NQubitPauliGroupElement n) : toGate (p * q) = toGate p * toGate q := by
  apply Subtype.ext
  rw [toGate_val, gate_mul_val, toGate_val, toGate_val]
  exact toMatrix_mul p q

/-- `toGate` preserves inverse. -/
lemma toGate_inv (p : NQubitPauliGroupElement n) : toGate (p⁻¹) = (toGate p)⁻¹ := by
  apply Subtype.ext
  rw [toGate_val, toMatrix_inv p, gate_inv_val (toGate p), ← gate_val_inv (toGate p), ← toGate_val]

lemma toMatrix_eq_iff_toGate_eq (p q : NQubitPauliGroupElement n)
 : toMatrix p = toMatrix q ↔ toGate p = toGate q := by
  constructor
  · intro h
    apply Subtype.ext
    simpa [NQubitPauliGroupElement.toGate_val] using h
  · intro h
    simpa [NQubitPauliGroupElement.toGate_val] using congrArg Subtype.val h
/-
The trace of the product of two Pauli matrices is 2 if they are equal, and 0 otherwise.
-/
lemma PauliOperator.trace_mul (p q : PauliOperator) :
  (p.toMatrix * q.toMatrix).trace = if p = q then 2 else 0 := by
    rcases p with ( _ | _ | _ | _ | p ) <;>
    rcases q with ( _ | _ | _ | _ | q ) <;> norm_num [ Matrix.trace ];
    all_goals simp +decide [ Xmat, Ymat, Zmat, Matrix.mul_apply ]

/-
The trace of the product of two n-qubit Pauli operator matrices is the product
of the traces of the individual single-qubit Pauli operator matrix products.
-/
lemma NQubitPauliOperator.trace_matrix_mul (p q : NQubitPauliOperator n) :
  (p.toMatrix * q.toMatrix).trace = ∏ i, ((p i).toMatrix * (q i).toMatrix).trace := by
    -- By Fubini's theorem, we can interchange the order of summation.
    have h_fubini : ∑ b : NQubitBasis n,
    ∑ k : NQubitBasis n, (∏ i : Fin n, (p i).toMatrix (b i) (k i))
    * (∏ i : Fin n, (q i).toMatrix (k i) (b i)) = ∏ i : Fin n, ∑ b : QubitBasis,
     ∑ k : QubitBasis, (p i).toMatrix b k * (q i).toMatrix k b := by
      have h_fubini : ∀ (f : Fin n → QubitBasis → QubitBasis → ℂ),
       (∑ b : NQubitBasis n, ∑ k : NQubitBasis n,
       ∏ i : Fin n, f i (b i) (k i)) = ∏ i : Fin n, ∑ b : QubitBasis,
       ∑ k : QubitBasis, f i b k := by
        intro f
        have h_fubini : ∀ (g : Fin n → QubitBasis → ℂ),
        (∑ b : NQubitBasis n, ∏ i : Fin n, g i (b i)) = ∏ i : Fin n, ∑ b : QubitBasis, g i b := by
          exact fun g ↦ Eq.symm (Fintype.prod_sum g);
        convert h_fubini ( fun i b => ∑ k : QubitBasis, f i b k ) using 1;
        exact Finset.sum_congr rfl fun _ _ => h_fubini _;
      convert h_fubini ( fun i b k =>
      ( p i |> PauliOperator.toMatrix ) b k * ( q i |> PauliOperator.toMatrix ) k b )
      using 3 ; ring_nf
      rw [ Finset.prod_mul_distrib ];
    convert h_fubini using 1


-- Provide decidable equality to state lemmas using `if p = q then ... else ...`.
noncomputable instance : DecidableEq (NQubitPauliOperator n) := Classical.decEq _
/-
The trace of the product of two n-qubit Pauli operator matrices is 2^n if the
operators are equal, and 0 otherwise.
-/
lemma NQubitPauliOperator.trace_mul (p q : NQubitPauliOperator n) :
  (p.toMatrix * q.toMatrix).trace = if p = q then (2 : ℂ)^n else 0 := by
  rw [NQubitPauliOperator.trace_matrix_mul]
  split_ifs with h
  · subst h
    simp only [PauliOperator.trace_mul, ↓reduceIte, Finset.prod_const, Finset.card_fin]
  · have : ∃ i, p i ≠ q i := by
      contrapose! h
      ext i
      exact h i
    obtain ⟨i, hi⟩ := this
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [PauliOperator.trace_mul]
    simp [hi]

/-!
If two `n`-qubit Pauli *group elements* have the same matrix representation, then they are equal.

In other words, the map `NQubitPauliGroupElement.toMatrix` is injective: the matrix uniquely
determines both the underlying Pauli operator tensor (`operators`) and the global phase
(`phasePower`).
-/
lemma toMatrix_inj (p q : NQubitPauliGroupElement n)
(h : toMatrix p = toMatrix q) : p = q := by
  have h_def : p.phasePower = q.phasePower ∧ p.operators = q.operators := by
    have h_phase : PauliGroupElement.phasePowerToComplex p.phasePower * (p.operators.toMatrix
    * p.operators.toMatrix).trace
    = PauliGroupElement.phasePowerToComplex q.phasePower
    * (p.operators.toMatrix * q.operators.toMatrix).trace := by
      have h_trace : (p.toMatrix * p.operators.toMatrix).trace =
      (q.toMatrix * p.operators.toMatrix).trace := by
        rw [h];
      convert h_trace using 1 <;>
      simp [ NQubitPauliGroupElement.toMatrix,
      Matrix.trace_mul_comm ( p.operators.toMatrix ) ];
    by_cases h_eq : p.operators =
    q.operators <;> simp_all [ NQubitPauliOperator.trace_mul ];
    · have h_phase_eq : ∀ (k m : Fin 4),
      PauliGroupElement.phasePowerToComplex k =
      PauliGroupElement.phasePowerToComplex m → k = m := by
        simp [ Fin.forall_fin_succ, PauliGroupElement.phasePowerToComplex ];
        norm_num [ Complex.ext_iff ];
      exact h_phase_eq _ _ h_phase;
    · unfold PauliGroupElement.phasePowerToComplex at h_phase; aesop;
  cases p ; cases q ; simp_all

/-!
If two Pauli group elements induce the same gate (`toGate`), then they are equal.

This is proved by first converting `toGate` equality into `toMatrix` equality (via
`toMatrix_eq_iff_toGate_eq`), and then applying `toMatrix_inj`.
-/
lemma toGate_inj (p q : NQubitPauliGroupElement n) (h : toGate p = toGate q) : p = q := by
  have h_toGate : p.toMatrix = q.toMatrix := by
    exact (toMatrix_eq_iff_toGate_eq p q).mpr h;
  apply NQubitPauliGroupElement.toMatrix_inj p q h_toGate

end NQubitPauliGroupElement

end Quantum
