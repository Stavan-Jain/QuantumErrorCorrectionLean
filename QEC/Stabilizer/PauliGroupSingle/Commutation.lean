import Mathlib.Tactic
import QEC.Stabilizer.PauliGroupSingle.Core
import QEC.Stabilizer.PauliGroupSingle.Operator
import QEC.Stabilizer.PauliGroupSingle.Element

namespace Quantum

namespace PauliGroupElement

/-!
# Commutation Properties

Two Pauli group elements commute if their operators commute (which happens when
the operators are equal or one is the identity). The phase factors don't affect
commutation since they're scalars.
-/

/-- Two single-qubit Pauli operators commute if and only if they are equal or one is I. -/
lemma PauliOperator.commutes_iff (P Q : PauliOperator) :
  P.mulOp Q = Q.mulOp P ↔ (P = Q ∨ P = PauliOperator.I ∨ Q = PauliOperator.I) := by
  cases P <;> cases Q <;> simp

/-- Two Pauli group elements commute if and only if their operators commute. -/
lemma commutes_iff (p q : PauliGroupElement) :
  p * q = q * p ↔ p.operator.mulOp q.operator = q.operator.mulOp p.operator := by
  constructor
  · intro h
    have h_op : (p * q).operator = (q * p).operator := by
      rw [h]
    simp [mul, mul_eq] at h_op
    have h_phase : (p * q).phasePower = (q * p).phasePower := by
      rw [h]
    simp [mul, mul_eq] at h_phase
    ext
    · simp [add_comm] at h_phase
      rw [h_phase]
    · exact h_op
  · intro h
    ext
    · simp [mul, mul_eq]
      have h_phase : (p.operator.mulOp q.operator).phasePower =
                     (q.operator.mulOp p.operator).phasePower := by
        rw [h]
      rw [h_phase, add_comm (p.phasePower) (q.phasePower)]
    · simp [mul, mul_eq]
      have h_op : (p.operator.mulOp q.operator).operator =
                  (q.operator.mulOp p.operator).operator := by
        rw [h]
      exact h_op

/-- The `operator` part of Pauli group multiplication is commutative
(phase factors may differ). -/
lemma operator_mul_comm (p q : PauliGroupElement) :
    (p * q).operator = (q * p).operator := by
  simp [mul, PauliOperator.mulOp_operator_comm]

/-- Two Pauli group elements commute iff the phase contributed by multiplying their
operators is the same in either order.

Since the `operator` field of `p * q` is always equal to that of `q * p` (the
noncommutativity is entirely captured by the phase), commutation reduces to a
statement about `phasePower`. -/
lemma commutes_iff_mulOp_phasePower (p q : PauliGroupElement) :
  p * q = q * p ↔
    (p.operator.mulOp q.operator).phasePower = (q.operator.mulOp p.operator).phasePower := by
  constructor
  · intro h
    have h_phase : (p * q).phasePower = (q * p).phasePower := by
      simpa using congrArg (fun r : PauliGroupElement => r.phasePower) h
    simpa [mul, mul_eq, add_assoc, add_comm, add_left_comm] using h_phase
  · intro h_mulOp_phase
    ext
    · simp [mul, mul_eq, add_assoc, add_comm, h_mulOp_phase]
    · exact operator_mul_comm p q

/-- The central element `-1` of the Pauli group, represented as `i^2 * I`. -/
def minusOne : PauliGroupElement := ⟨2, PauliOperator.I⟩

/-- For Pauli operators, multiplication either commutes (same phase power) or anticommutes
(phase differs by `2`, i.e. a factor of `-1`). -/
lemma PauliOperator.mulOp_phasePower_eq_or_eq_add_two (P Q : PauliOperator) :
    (P.mulOp Q).phasePower = (Q.mulOp P).phasePower ∨
    (P.mulOp Q).phasePower = (Q.mulOp P).phasePower + 2 := by
  cases P <;> cases Q <;> decide

/-- Any two Pauli group elements either commute or anticommute.

Anticommutation is expressed as `p * q = (-1) * (q * p)`, where `-1` is `minusOne`. -/
lemma commute_or_anticommute (p q : PauliGroupElement) :
  p * q = q * p ∨ p * q = minusOne * (q * p) := by
  rcases PauliOperator.mulOp_phasePower_eq_or_eq_add_two p.operator q.operator with h | h
  · exact Or.inl ((commutes_iff_mulOp_phasePower p q).2 h)
  · refine Or.inr ?_
    ext
    · unfold PauliGroupElement.minusOne; simp
      unfold PauliGroupElement.mul; simp  [ h, Fin.val_add]
      unfold PauliOperator.mulOp; simp ; ring_nf
    · simpa only [mul_eq, mul, PauliOperator.mulOp, Fin.isValue, minusOne, add_zero] using
      (operator_mul_comm p q)

/-- Symmetry of commutation: if p commutes with q, then q commutes with p. -/
lemma commutes_symm (p q : PauliGroupElement) :
  (p * q = q * p) ↔ (q * p = p * q) := by
  constructor
  · intro h; symm; exact h
  · intro h; symm; exact h

end PauliGroupElement

end Quantum
