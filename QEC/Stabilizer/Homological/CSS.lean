import Mathlib.Tactic
import QEC.Stabilizer.Homological.Code
import QEC.Stabilizer.PauliGroup
import QEC.Stabilizer.PauliGroup.NQubitOperator
import QEC.Stabilizer.Core

/-!
# Generic CSS construction from a `HomologicalCode`

This file lifts the toric CSS operator-encoding machinery to the abstract
`HomologicalCode` setting.  Given a length-3 chain complex `X`, we encode
1-chains as X-type and Z-type Pauli operators on `Fintype.card X.C1` qubits,
indexed by the canonical `Fintype.equivFin X.C1`.

This file currently covers §B.1 (Pauli-operator encoding).  §B.2 (generators)
and §B.3 (the `StabilizerCode` instance with symplectic-LI lift) follow in
later edits.
-/

namespace Quantum
namespace Stabilizer
namespace Homological

open scoped BigOperators

namespace HomologicalCode

variable (X : HomologicalCode)

-- `numQubits` is now a field of `HomologicalCode` (see `Code.lean`).

/-- Encode a 1-chain as an X-type Pauli element. -/
noncomputable def chainXOperator (c : X.C1 → ZMod 2) :
    NQubitPauliGroupElement X.numQubits :=
  ⟨0, fun q =>
    if ∃ e : X.C1, X.edgeEquiv e = q ∧ c e = 1
    then PauliOperator.X else PauliOperator.I⟩

/-- Encode a 1-chain as a Z-type Pauli element. -/
noncomputable def chainZOperator (c : X.C1 → ZMod 2) :
    NQubitPauliGroupElement X.numQubits :=
  ⟨0, fun q =>
    if ∃ e : X.C1, X.edgeEquiv e = q ∧ c e = 1
    then PauliOperator.Z else PauliOperator.I⟩

/-- Inverse of `chainXOperator`: read back the 1-chain. -/
noncomputable def chainOfXOperator
    (g : NQubitPauliGroupElement X.numQubits) : X.C1 → ZMod 2 :=
  fun e => if g.operators (X.edgeEquiv e) = PauliOperator.X then 1 else 0

/-- Inverse of `chainZOperator`. -/
noncomputable def chainOfZOperator
    (g : NQubitPauliGroupElement X.numQubits) : X.C1 → ZMod 2 :=
  fun e => if g.operators (X.edgeEquiv e) = PauliOperator.Z then 1 else 0

variable {X}

/-- The X-chain operator at qubit `q` (`rfl`-style unfold). -/
lemma chainXOperator_op_at (c : X.C1 → ZMod 2) (q : Fin X.numQubits) :
    (X.chainXOperator c).operators q =
      if ∃ e : X.C1, X.edgeEquiv e = q ∧ c e = 1
      then PauliOperator.X else PauliOperator.I := rfl

/-- The Z-chain operator at qubit `q` (`rfl`-style unfold). -/
lemma chainZOperator_op_at (c : X.C1 → ZMod 2) (q : Fin X.numQubits) :
    (X.chainZOperator c).operators q =
      if ∃ e : X.C1, X.edgeEquiv e = q ∧ c e = 1
      then PauliOperator.Z else PauliOperator.I := rfl

/-- An edge `e` is in the support of `chainXOperator c` iff `c e = 1`. -/
lemma mem_support_chainXOperator_iff (c : X.C1 → ZMod 2) (e : X.C1) :
    X.edgeEquiv e ∈ (X.chainXOperator c).operators.support ↔ c e = 1 := by
  classical
  constructor
  · intro hmem
    by_contra hne
    have hnot :
        ¬ ∃ e' : X.C1, X.edgeEquiv e' = X.edgeEquiv e ∧ c e' = 1 := by
      rintro ⟨e', heq, he1⟩
      exact hne ((X.edgeEquiv.injective heq) ▸ he1)
    have hI :
        (X.chainXOperator c).operators (X.edgeEquiv e) = PauliOperator.I := by
      rw [chainXOperator_op_at]
      exact if_neg hnot
    have hneqI :
        (X.chainXOperator c).operators (X.edgeEquiv e) ≠ PauliOperator.I := by
      simpa [NQubitPauliOperator.support] using hmem
    exact hneqI hI
  · intro he1
    have hex : ∃ e' : X.C1, X.edgeEquiv e' = X.edgeEquiv e ∧ c e' = 1 :=
      ⟨e, rfl, he1⟩
    have hX :
        (X.chainXOperator c).operators (X.edgeEquiv e) = PauliOperator.X := by
      rw [chainXOperator_op_at]
      exact if_pos hex
    simp [NQubitPauliOperator.support, hX]

/-- An edge `e` is in the support of `chainZOperator c` iff `c e = 1`. -/
lemma mem_support_chainZOperator_iff (c : X.C1 → ZMod 2) (e : X.C1) :
    X.edgeEquiv e ∈ (X.chainZOperator c).operators.support ↔ c e = 1 := by
  classical
  constructor
  · intro hmem
    by_contra hne
    have hnot :
        ¬ ∃ e' : X.C1, X.edgeEquiv e' = X.edgeEquiv e ∧ c e' = 1 := by
      rintro ⟨e', heq, he1⟩
      exact hne ((X.edgeEquiv.injective heq) ▸ he1)
    have hI :
        (X.chainZOperator c).operators (X.edgeEquiv e) = PauliOperator.I := by
      rw [chainZOperator_op_at]
      exact if_neg hnot
    have hneqI :
        (X.chainZOperator c).operators (X.edgeEquiv e) ≠ PauliOperator.I := by
      simpa [NQubitPauliOperator.support] using hmem
    exact hneqI hI
  · intro he1
    have hex : ∃ e' : X.C1, X.edgeEquiv e' = X.edgeEquiv e ∧ c e' = 1 :=
      ⟨e, rfl, he1⟩
    have hZ :
        (X.chainZOperator c).operators (X.edgeEquiv e) = PauliOperator.Z := by
      rw [chainZOperator_op_at]
      exact if_pos hex
    simp [NQubitPauliOperator.support, hZ]

/-- Helper: every `ZMod 2` element is `0` or `1`. -/
private lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hvalle : a.val ≤ 1 := Nat.le_of_lt_succ a.val_lt
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hvalle with h0 | h1
  · left
    calc a = ((a.val : ZMod 2)) := (ZMod.natCast_zmod_val a).symm
      _ = 0 := by simp [h0]
  · right
    calc a = ((a.val : ZMod 2)) := (ZMod.natCast_zmod_val a).symm
      _ = 1 := by simp [h1]

/-- Roundtrip: chain → X-operator → chain. -/
theorem chainOfXOperator_chainXOperator (c : X.C1 → ZMod 2) :
    X.chainOfXOperator (X.chainXOperator c) = c := by
  ext e
  by_cases hce : c e = 1
  · have _hex : ∃ e' : X.C1, X.edgeEquiv e' = X.edgeEquiv e ∧ c e' = 1 :=
      ⟨e, rfl, hce⟩
    simp [chainOfXOperator, chainXOperator, hce]
  · have _hnot :
        ¬ ∃ e' : X.C1, X.edgeEquiv e' = X.edgeEquiv e ∧ c e' = 1 := by
      rintro ⟨e', heq, he1⟩
      have he' : e' = e := X.edgeEquiv.injective heq
      exact hce (he' ▸ he1)
    have hce0 : c e = 0 := (zmod2_eq_zero_or_one (c e)).resolve_right hce
    simp [chainOfXOperator, chainXOperator, hce0]

/-- Roundtrip: chain → Z-operator → chain. -/
theorem chainOfZOperator_chainZOperator (c : X.C1 → ZMod 2) :
    X.chainOfZOperator (X.chainZOperator c) = c := by
  ext e
  by_cases hce : c e = 1
  · have _hex : ∃ e' : X.C1, X.edgeEquiv e' = X.edgeEquiv e ∧ c e' = 1 :=
      ⟨e, rfl, hce⟩
    simp [chainOfZOperator, chainZOperator, hce]
  · have _hnot :
        ¬ ∃ e' : X.C1, X.edgeEquiv e' = X.edgeEquiv e ∧ c e' = 1 := by
      rintro ⟨e', heq, he1⟩
      have he' : e' = e := X.edgeEquiv.injective heq
      exact hce (he' ▸ he1)
    have hce0 : c e = 0 := (zmod2_eq_zero_or_one (c e)).resolve_right hce
    simp [chainOfZOperator, chainZOperator, hce0]

/-- The X-chain operator is X-type (phase 0, every operator is `X` or `I`). -/
lemma chainXOperator_isXType (c : X.C1 → ZMod 2) :
    NQubitPauliGroupElement.IsXTypeElement (X.chainXOperator c) := by
  refine ⟨rfl, fun q => ?_⟩
  by_cases h : ∃ e : X.C1, X.edgeEquiv e = q ∧ c e = 1
  · right
    simp [chainXOperator, h]
  · left
    simp [chainXOperator, h]

/-- The Z-chain operator is Z-type (phase 0, every operator is `Z` or `I`). -/
lemma chainZOperator_isZType (c : X.C1 → ZMod 2) :
    NQubitPauliGroupElement.IsZTypeElement (X.chainZOperator c) := by
  refine ⟨rfl, fun q => ?_⟩
  by_cases h : ∃ e : X.C1, X.edgeEquiv e = q ∧ c e = 1
  · right
    simp [chainZOperator, h]
  · left
    simp [chainZOperator, h]

/-- `chainXOperator 0 = 1`. -/
@[simp] lemma chainXOperator_zero :
    X.chainXOperator 0 = 1 := by
  unfold chainXOperator
  aesop

/-- `chainZOperator 0 = 1`. -/
@[simp] lemma chainZOperator_zero :
    X.chainZOperator 0 = 1 := by
  unfold chainZOperator
  aesop

set_option maxHeartbeats 1000000 in
-- This split-`if` over chain-sum cases involves a quadratic case explosion across
-- the three indicator predicates (c, c', c+c'); the extra heartbeats accommodate
-- it without restructuring the proof.
/-- Homomorphism: `chainXOperator (c + c') = chainXOperator c * chainXOperator c'`. -/
theorem chainXOperator_add (c c' : X.C1 → ZMod 2) :
    X.chainXOperator (c + c') = X.chainXOperator c * X.chainXOperator c' := by
  simp [chainXOperator] at *
  simp +decide [NQubitPauliGroupElement.mul, NQubitPauliGroupElement.mulOp]
  refine ⟨?_, ?_⟩
  · rw [Finset.sum_eq_zero]; aesop
  · ext q
    split_ifs <;> simp_all +decide [Fin.ext_iff, ZMod]
    · rename_i h₁ h₂ h₃
      obtain ⟨e₁, he₁, he₂⟩ := h₁
      obtain ⟨e₂, he₃, he₄⟩ := h₂
      obtain ⟨e₃, he₅, he₆⟩ := h₃
      have h_eq : e₁ = e₂ ∧ e₂ = e₃ :=
        ⟨X.edgeEquiv.injective (Fin.ext (he₁.trans he₃.symm)),
         X.edgeEquiv.injective (Fin.ext (he₃.trans he₅.symm))⟩
      grind
    · grind
    · grind
    · grind

set_option maxHeartbeats 1000000 in
-- Same case-explosion as `chainXOperator_add`; see comment there.
/-- Homomorphism: `chainZOperator (c + c') = chainZOperator c * chainZOperator c'`. -/
theorem chainZOperator_add (c c' : X.C1 → ZMod 2) :
    X.chainZOperator (c + c') = X.chainZOperator c * X.chainZOperator c' := by
  simp [chainZOperator] at *
  simp +decide [NQubitPauliGroupElement.mul, NQubitPauliGroupElement.mulOp]
  refine ⟨?_, ?_⟩
  · rw [Finset.sum_eq_zero]; aesop
  · ext q
    split_ifs <;> simp_all +decide [Fin.ext_iff, ZMod]
    · rename_i h₁ h₂ h₃
      obtain ⟨e₁, he₁, he₂⟩ := h₁
      obtain ⟨e₂, he₃, he₄⟩ := h₂
      obtain ⟨e₃, he₅, he₆⟩ := h₃
      have h_eq : e₁ = e₂ ∧ e₂ = e₃ :=
        ⟨X.edgeEquiv.injective (Fin.ext (he₁.trans he₃.symm)),
         X.edgeEquiv.injective (Fin.ext (he₃.trans he₅.symm))⟩
      grind
    · grind
    · grind
    · grind

end HomologicalCode

end Homological
end Stabilizer
end Quantum
