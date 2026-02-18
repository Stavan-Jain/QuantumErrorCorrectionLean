import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Ring.Parity
import QEC.Foundations.Foundations
import QEC.Stabilizer.PauliGroup.NQubitElement

namespace Quantum
open Matrix
open scoped BigOperators

variable {n : ℕ}

namespace NQubitPauliGroupElement

/-!
# Commutation Properties

Two n-qubit Pauli group elements commute if they commute qubit-wise.
The phase factors don't affect commutation since they're scalars.
-/

/-!
## Helper Lemmas for Commutation Proofs
-/

/-- The operator at qubit i in the result of mulOp is the operator from the
    single-qubit multiplication. -/
private lemma mulOp_operators_at (p q : NQubitPauliOperator n) (i : Fin n) :
  (mulOp p q).operators i = ((p i).mulOp (q i)).operator := rfl

/-- The phase power in mulOp is the sum of phase powers from all qubit multiplications. -/
private lemma mulOp_phasePower (p q : NQubitPauliOperator n) :
  (mulOp p q).phasePower =
    (Finset.univ : Finset (Fin n)).sum (fun i => ((p i).mulOp (q i)).phasePower) := rfl

/-- If two functions are equal pointwise, their sums over Finset.univ are equal. -/
private lemma sum_eq_of_pointwise_eq {α : Type*} [AddCommMonoid α] {f g : Fin n → α}
  (h : ∀ i, f i = g i) :
  (Finset.univ : Finset (Fin n)).sum f = (Finset.univ : Finset (Fin n)).sum g :=
  Finset.sum_congr rfl (fun i _ => h i)

/-- If operators commute qubit-wise, then the phase contributions are equal at each qubit. -/
private lemma phasePower_eq_of_commutes_qubitwise {p q : NQubitPauliOperator n}
  (h : ∀ i : Fin n, (p i).mulOp (q i) = (q i).mulOp (p i)) :
  ∀ i : Fin n, ((p i).mulOp (q i)).phasePower = ((q i).mulOp (p i)).phasePower := by
  intro i
  rw [h i]

/-- If operators commute qubit-wise, then the total phase contributions are equal. -/
private lemma mulOp_phasePower_eq_of_commutes_qubitwise {p q : NQubitPauliOperator n}
  (h : ∀ i : Fin n, (p i).mulOp (q i) = (q i).mulOp (p i)) :
  (mulOp p q).phasePower = (mulOp q p).phasePower := by
  simp [mulOp_phasePower]
  apply sum_eq_of_pointwise_eq
  exact phasePower_eq_of_commutes_qubitwise h

/-- If operators commute qubit-wise, then the operators are equal at each qubit. -/
private lemma mulOp_operators_eq_of_commutes_qubitwise {p q : NQubitPauliOperator n}
  (h : ∀ i : Fin n, (p i).mulOp (q i) = (q i).mulOp (p i)) :
  ∀ i : Fin n, (mulOp p q).operators i = (mulOp q p).operators i := by
  intro i
  simp [mulOp_operators_at]
  rw [h i]

/-- The `operators` part of n-qubit Pauli group multiplication is commutative
(phase factors may differ). -/
lemma operators_mul_comm (p q : NQubitPauliGroupElement n) :
    (p * q).operators = (q * p).operators := by
  ext i
  simp [mul, mul_eq, mulOp_operators_at, PauliOperator.mulOp_operator_comm]

/-- Two n-qubit Pauli group elements commute if they commute at every qubit position. -/
lemma commutes_of_componentwise_commutes (p q : NQubitPauliGroupElement n) :
  (∀ i : Fin n,
  (p.operators i).mulOp (q.operators i) = (q.operators i).mulOp (p.operators i))
  → p * q = q * p := by
    intro h
    ext
    · simp [mul, mul_eq]
      rw [mulOp_phasePower_eq_of_commutes_qubitwise h]
      simp [add_comm]
    · simp [mul, mul_eq]
      rw [mulOp_operators_eq_of_commutes_qubitwise h]

/-- The `operators` field of `p * q` and `q * p` is always the same, so commutation of
n-qubit Pauli group elements reduces to equality of the phase contributed by `mulOp`. -/
lemma commutes_iff_mulOp_phasePower (p q : NQubitPauliGroupElement n) :
  p * q = q * p ↔
  (mulOp p.operators q.operators).phasePower = (mulOp q.operators p.operators).phasePower := by
  constructor
  · intro h
    have h_phase : (p * q).phasePower = (q * p).phasePower := by
      simpa using congrArg (fun r : NQubitPauliGroupElement n => r.phasePower) h
    -- Expand multiplication and cancel the commutative outer phase terms.
    simpa [mul, mul_eq, add_assoc, add_comm, add_left_comm] using h_phase
  · intro h_mulOp_phase
    apply NQubitPauliGroupElement.ext (p * q) (q * p)
    · simp [mul, mul_eq, add_assoc, add_comm, h_mulOp_phase]
    · exact operators_mul_comm p q

/-!
## Parity characterization

Two tensor-product Paulis commute iff an even number of qubit positions anticommute.
We express "anticommute at position i" via the `Fin 4` phase difference in `mulOp`.
-/

/-- At qubit `i`, the single-qubit factors anticommute iff swapping the order flips the
phase contribution by `2` (i.e. multiplies by `-1`). -/
def anticommutesAt (p q : NQubitPauliOperator n) (i : Fin n) : Prop :=
  ((p i).mulOp (q i)).phasePower = ((q i).mulOp (p i)).phasePower + 2

/-- Two n-qubit Pauli group elements commute iff the number of qubit positions where the
corresponding single-qubit factors anticommute is even. -/
lemma commutes_iff_even_anticommutes (p q : NQubitPauliGroupElement n) :
  p * q = q * p ↔
    (by
      classical
      exact Even ((Finset.univ.filter
      (anticommutesAt (n := n) p.operators q.operators)).card)) := by
  constructor;
  · intro h;
    -- By definition of commutation, we know that the phase difference between
    -- `p * q` and `q * p` is zero.
    have h_phase_diff : (mulOp p.operators q.operators).phasePower =
    (mulOp q.operators p.operators).phasePower := by
      exact (commutes_iff_mulOp_phasePower p q).mp h;
    -- Since the phase difference is zero, the number of qubit positions where
    -- the corresponding single-qubit factors anticommute must be even.
    have h_even : (Finset.univ : Finset (Fin n)).sum (fun i =>
    ((p.operators i).mulOp (q.operators i)).phasePower) =
    (Finset.univ : Finset (Fin n)).sum (fun i =>
    ((q.operators i).mulOp (p.operators i)).phasePower) := by
      convert h_phase_diff using 1;
    -- Since the phase difference is zero, the number of qubit positions where
    -- the corresponding single-qubit factors anticommute must be even. We can
    -- use the fact that the sum of the phase differences is zero modulo 4.
    have h_even : (Finset.univ : Finset (Fin n)).sum (fun i =>
    if ((p.operators i).mulOp (q.operators i)).phasePower =
    ((q.operators i).mulOp (p.operators i)).phasePower + 2 then 1 else 0)
    % 2 = 0 := by
      have h_even : (Finset.univ : Finset (Fin n)).sum (fun i =>
      ((p.operators i).mulOp (q.operators i)).phasePower -
      ((q.operators i).mulOp (p.operators i)).phasePower) % 4 = 0 := by
        aesop;
      have h_even : ∀ i : Fin n, ((p.operators i).mulOp (q.operators i)).phasePower -
      ((q.operators i).mulOp (p.operators i)).phasePower =
      if ((p.operators i).mulOp (q.operators i)).phasePower =
      ((q.operators i).mulOp (p.operators i)).phasePower + 2 then 2 else 0 := by
        intro i
        have h_diff : ((p.operators i).mulOp (q.operators i)).phasePower =
        ((q.operators i).mulOp (p.operators i)).phasePower ∨
        ((p.operators i).mulOp (q.operators i)).phasePower =
        ((q.operators i).mulOp (p.operators i)).phasePower + 2 := by
          exact
            PauliGroupElement.PauliOperator.mulOp_phasePower_eq_or_eq_add_two (p.operators i)
              (q.operators i);
        aesop;
      have h_even : (Finset.univ : Finset (Fin n)).sum (fun i =>
      2 * (if ((p.operators i).mulOp (q.operators i)).phasePower =
      ((q.operators i).mulOp (p.operators i)).phasePower + 2 then 1 else 0)) % 4 = 0 := by
        convert ‹ ( ∑ i : Fin n, ( ( ( p.operators i ).mulOp
        ( q.operators i ) ).phasePower -
        ( ( q.operators i ).mulOp ( p.operators i ) ).phasePower ) )
        % 4 = 0 › using 2 ; simp [ h_even ];
        norm_num [ Fin.mod_def ];
        rw [ ← ZMod.val_natCast ] ; norm_num [ Nat.add_mod, Nat.mul_mod ] ;
      rw [ ← Finset.mul_sum _ _ _ ] at h_even; omega;
    convert Nat.even_iff.mpr h_even using 1;
    simp
    congr! 1;
    ext; simp [Quantum.NQubitPauliGroupElement.anticommutesAt];
  · -- If the number of qubits where the operators anticommute is even, then
    -- their total phase contributions will cancel out.
    intro h_even
    have h_cancel : (Finset.univ : Finset (Fin n)).sum (fun i =>
    ((p.operators i).mulOp (q.operators i)).phasePower) =
    (Finset.univ : Finset (Fin n)).sum (fun i =>
     ((q.operators i).mulOp (p.operators i)).phasePower) := by
      -- By definition of `mulOp`, we know that for each qubit `i`, either `((p.
      -- operators i).mulOp (q.operators i)).phasePower = ((q.operators i).
      -- mulOp (p.operators i)).phasePower` or `((p.operators i).mulOp (q.
      --operators i)).phasePower = ((q.operators i).mulOp (p.operators i)).
      --phasePower + 2`.
      have h_phase_diff : ∀ i : Fin n, ((p.operators i).mulOp (q.operators i)).phasePower =
      ((q.operators i).mulOp (p.operators i)).phasePower ∨
      ((p.operators i).mulOp (q.operators i)).phasePower =
      ((q.operators i).mulOp (p.operators i)).phasePower + 2 := by
        exact fun i ↦
          PauliGroupElement.PauliOperator.mulOp_phasePower_eq_or_eq_add_two (p.operators i)
            (q.operators i);
      -- Since the number of qubits where the operators anticommute is even,
      --the total phase difference is zero.
      have h_total_phase_diff :
      (Finset.univ : Finset (Fin n)).sum (fun i =>
      ((p.operators i).mulOp (q.operators i)).phasePower)
      = (Finset.univ : Finset (Fin n)).sum (fun i =>
      ((q.operators i).mulOp (p.operators i)).phasePower) + 2 *
      (Finset.univ : Finset (Fin n)).sum (fun i =>
      if ((p.operators i).mulOp (q.operators i)).phasePower
      = ((q.operators i).mulOp (p.operators i)).phasePower + 2 then 1 else 0) := by
        rw [ Finset.mul_sum _ _ _ ];
        rw [ ← Finset.sum_add_distrib ] ; exact Finset.sum_congr rfl fun i _ =>
        by cases h_phase_diff i <;> simp  [ * ] ;
      simp_all  [ Finset.sum_ite ];
      convert congr_arg ( fun x : ℕ => x • 2 : ℕ → Fin 4 ) h_even.two_dvd.choose_spec using 1;
      · congr! 2;
        ext; simp [Quantum.NQubitPauliGroupElement.anticommutesAt];
      · norm_num [ Fin.ext_iff, Fin.val_add, Fin.val_mul ];
        erw [ Fin.val_mk ];
        induction Exists.choose (even_iff_two_dvd.mp h_even) with
        | zero => simp_all [nsmulRec];
        | succ k ih => simp_all [Nat.mul_succ, nsmulRec];  omega
    exact (commutes_iff_mulOp_phasePower p q).mpr h_cancel

/-!
## Anticommutation

Two n-qubit Pauli group elements anticommute when p * q = (-1) * (q * p), i.e. the number of
qubit positions where the single-qubit factors anticommute is odd.
-/

/-- Two n-qubit Pauli group elements anticommute: p * q = (-1) * (q * p). -/
def Anticommute (p q : NQubitPauliGroupElement n) : Prop :=
  p * q = minusOne n * (q * p)

/-- Anticommutation reduces to the mulOp phase differing by 2 (mod 4). -/
lemma anticommutes_iff_mulOp_phasePower (p q : NQubitPauliGroupElement n) :
  Anticommute p q ↔
  (mulOp p.operators q.operators).phasePower = (mulOp q.operators p.operators).phasePower + 2 := by
  constructor
  · intro h
    have h_phase : (p * q).phasePower = (minusOne n * (q * p)).phasePower :=
      congrArg (fun r : NQubitPauliGroupElement n => r.phasePower) h
    simp only [mul, mul_eq, minusOne_phasePower, minusOne_operators] at h_phase
    rw [mulOp_identity_left_phase] at h_phase
    simpa [add_assoc, add_comm, add_left_comm] using h_phase
  · intro h_mulOp_phase
    apply NQubitPauliGroupElement.ext (p * q) (minusOne n * (q * p))
    · simp only [mul, mul_eq, minusOne_phasePower, minusOne_operators, mulOp_identity_left_phase,
        zero_add, add_assoc, add_comm, add_left_comm, h_mulOp_phase]
    · ext i
      simp only [mul, mul_eq, minusOne_operators, mulOp_operators_at, mulOp_identity_left_op,
        PauliOperator.mulOp_operator_comm]

/-- Two n-qubit Pauli group elements anticommute iff the number of qubit positions where the
corresponding single-qubit factors anticommute is odd. -/
lemma anticommutes_iff_odd_anticommutes (p q : NQubitPauliGroupElement n) :
  Anticommute p q ↔
    (by classical exact Odd ((Finset.univ.filter
      (anticommutesAt (n := n) p.operators q.operators)).card)) := by
  rw [anticommutes_iff_mulOp_phasePower, Nat.odd_iff]
  constructor
  · intro h_phase
    have h_odd : ((Finset.univ.filter (fun i =>
    ((p.operators i).mulOp (q.operators i)).phasePower =
    ((q.operators i).mulOp (p.operators i)).phasePower + 2)).card)
    % 2 = 1 := by
      have h_odd : ((Finset.univ : Finset (Fin n)).sum
      (fun i => ((p.operators i).mulOp (q.operators i)).phasePower -
      ((q.operators i).mulOp (p.operators i)).phasePower)) % 4 = 2 := by
        convert congr_arg ( fun x : Fin 4 => x.val % 4 ) h_phase using 1;
        simp  [ Fin.ext_iff, Fin.val_add, mulOp_phasePower ];
        omega;
      have h_odd : ∀ i : Fin n,
      ((p.operators i).mulOp (q.operators i)).phasePower -
      ((q.operators i).mulOp (p.operators i)).phasePower =
      if ((p.operators i).mulOp (q.operators i)).phasePower =
      ((q.operators i).mulOp (p.operators i)).phasePower + 2 then 2 else 0 := by
        intro i; split_ifs <;> simp_all  [ sub_eq_iff_eq_add ] ;
        have h_comm : ∀ (p q : PauliOperator), (p.mulOp q).phasePower =
        (q.mulOp p).phasePower ∨
        (p.mulOp q).phasePower = (q.mulOp p).phasePower + 2 := by
          exact fun p q ↦ PauliGroupElement.PauliOperator.mulOp_phasePower_eq_or_eq_add_two p q;
        exact Or.resolve_right ( h_comm _ _ ) ‹_›;
      simp_all  [ Finset.sum_ite ];
      rcases Nat.even_or_odd' ( Finset.card (
        Finset.filter ( fun i => ( ( p.operators i ).mulOp
      ( q.operators i ) ).phasePower =
      ( ( q.operators i ).mulOp
      ( p.operators i ) ).phasePower + 2 ) Finset.univ ) ) with ⟨ k, hk | hk ⟩ <;>
      simp_all ;
      erw [ Fin.ext_iff ] at * ; simp_all  [ Fin.val_add ];
      erw [ Fin.val_mk ] at * ; simp_all ;
      erw [ show ( nsmulRec ( 2 * k ) 2 : Fin 4 ) = 0 from
      by exact Nat.recOn k ( by rfl ) fun n ihn => by simp_all
      [ Nat.mul_succ, nsmulRec ] ] at * ;
      simp_all
    convert h_odd using 4
  · intro h_odd
    have h_total_phase_diff : (mulOp p.operators q.operators).phasePower =
      (mulOp q.operators p.operators).phasePower +
      (Finset.univ : Finset (Fin n)).sum
      (fun i => if ((p.operators i).mulOp
      (q.operators i)).phasePower =
      ((q.operators i).mulOp (p.operators i)).phasePower + 2 then
      2 else 0) := by
        have h_total_phase_diff : ∀ i : Fin n, ((p.operators i).mulOp (q.operators i)).phasePower =
          ((q.operators i).mulOp (p.operators i)).phasePower + if ((p.operators i).mulOp
          (q.operators i)).phasePower =
          ((q.operators i).mulOp (p.operators i)).phasePower + 2 then 2 else 0 := by
            unfold PauliOperator.mulOp at *; aesop;
        rw [ mulOp_phasePower, mulOp_phasePower, Finset.sum_congr rfl fun i _ =>
        h_total_phase_diff i, Finset.sum_add_distrib ];
    simp_all  [ Finset.sum_ite ];
    erw [ Finset.card_filter ] at *;
    rw [ ← Nat.mod_add_div ( ∑ i : Fin n, if
    ( ( p.operators i ).mulOp
    ( q.operators i ) ).phasePower =
    ( ( q.operators i ).mulOp ( p.operators i ) ).phasePower +
    2 then 1 else 0 ) 2 ] ; simp_all ;
    simp_all  [ Fin.ext_iff, Quantum.NQubitPauliGroupElement.anticommutesAt ];
    erw [ Fin.val_mk ];
    induction ( Finset.card _ / 2 ) <;> simp_all  [ Nat.mul_succ, nsmulRec ];
    simp_all  [ Fin.val_add]

/-- Symmetry of anticommutation: if P anticommutes with Q, then Q anticommutes with P. -/
lemma anticommute_symm (p q : NQubitPauliGroupElement n) :
    Anticommute p q → Anticommute q p := by
  unfold Anticommute
  intro h
  calc q * p = (minusOne n)⁻¹ * ((minusOne n) * (q * p)) := by rw [inv_mul_cancel_left]
      _ = (minusOne n)⁻¹ * (p * q) := by rw [← h]
      _ = (minusOne n) * (p * q) := by rw [minusOne_inv]

/-- Every element commutes with itself. -/
lemma commutes_refl (p : NQubitPauliGroupElement n) : p * p = p * p := rfl

/-- Symmetry of commutation: if p commutes with q, then q commutes with p. -/
lemma commutes_symm (p q : NQubitPauliGroupElement n) :
  (p * q = q * p) ↔ (q * p = p * q) := by
  constructor
  · intro h; symm; exact h
  · intro h; symm; exact h

/-- The identity element commutes with all elements. -/
lemma commutes_one_left (p : NQubitPauliGroupElement n) : 1 * p = p * 1 := by
  rw [one_mul, mul_one]

/-- All elements commute with the identity. -/
lemma commutes_one_right (p : NQubitPauliGroupElement n) : p * 1 = 1 * p := by
  rw [mul_one, one_mul]

/-- If one element is the identity, they commute. -/
lemma commutes_if_one_identity_left (p : NQubitPauliGroupElement n) :
  (1 : NQubitPauliGroupElement n) * p = p * (1 : NQubitPauliGroupElement n) :=
  commutes_one_left p

/-- If one element is the identity, they commute. -/
lemma commutes_if_one_identity_right (p : NQubitPauliGroupElement n) :
  p * (1 : NQubitPauliGroupElement n) = (1 : NQubitPauliGroupElement n) * p :=
  commutes_one_right p

end NQubitPauliGroupElement

end Quantum
