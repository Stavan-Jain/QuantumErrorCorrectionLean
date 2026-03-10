import QEC.RepetitionCode.EncodeDecode
import QEC.Foundations.Foundations

namespace Quantum

/-!
# Logical X for the 3-qubit repetition code

The **logical Pauli X** on the encoded subspace is implemented as a **physical** 3-qubit
unitary `LogicalX` (here `X_q1q2q3_3` — X applied jointly so that the codespace {|000⟩, |111⟩}
is swapped). After encoding a 1-qubit state, applying `LogicalX` and **decoding** should
agree with applying the **single-qubit** `X` gate on the original qubit.

## Main results

- `logicalX_correct_ket0` / `logicalX_correct_ket1`: correctness on |0⟩ and |1⟩.
- `F` packages encode → `LogicalX` → decode as a map `QubitVec → QubitVec`.
- `F_correct` and `logicalX_correct_val` / `logicalX_correct_state`: full linear extension
  to arbitrary 1-qubit vectors/states.

Depends on `EncodeDecode.lean` (`encode_state`, `decode_state`, `encodeVec`, `decodeVec`)
and gate definitions from `Foundations` (e.g. `X`, `Xmat`).
-/

/-- Physical 3-qubit gate realizing logical X on the repetition-code subspace. -/
noncomputable def LogicalX : ThreeQubitGate := X_q1q2q3_3

lemma LogicalX_encode_ket0 : LogicalX • encode_state ket0 = ket111 := by simp[LogicalX]

lemma LogicalX_encode_ket1 : LogicalX • encode_state ket1 = ket000 := by simp[LogicalX]

lemma decode_LogicalX_encode_ket0 : decode_state (LogicalX • encode_state ket0) = ket1.val := by
  rw[LogicalX_encode_ket0]
  exact decode_ket111

lemma decode_LogicalX_encode_ket1 : decode_state (LogicalX • encode_state ket1) = ket0.val := by
  rw[LogicalX_encode_ket1]
  exact decode_ket000

theorem logicalX_correct_ket0 : decode_state (LogicalX • encode_state ket0) = (X • ket0).val := by
  rw [decode_LogicalX_encode_ket0, X_on_ket0]

theorem logicalX_correct_ket1 : decode_state (LogicalX • encode_state ket1) = (X • ket1).val := by
  rw [decode_LogicalX_encode_ket1, X_on_ket1]

lemma qubitVec_eq_lincomb (v : QubitVec) :
  v = (v 0) • basisVec (0 : QubitBasis) + (v 1) • basisVec (1 : QubitBasis) := by
  funext q
  fin_cases q <;> simp [basisVec]

lemma qubit_val_eq_lincomb_kets (ψ : Qubit) :
  (ψ.val : QubitVec) = (ψ.val 0) • (ket0.val) + (ψ.val 1) • (ket1.val) := by
  ext q
  fin_cases q <;>
    -- now q is 0 or 1
    simp [ket0, ket1]

lemma qubitVec_eq_lincomb_kets (v : QubitVec) :
  v = (v 0) • (ket0.val) + (v 1) • (ket1.val) := by
  ext q
  fin_cases q <;> simp [ket0, ket1]

/-- The semantic “logical X pipeline” as a function on 1-qubit vectors. -/
noncomputable def F (v : QubitVec) : QubitVec :=
  decodeVec (Matrix.mulVec (LogicalX.val) (encodeVec v))

lemma F_add (v w : QubitVec) : F (v + w) = F v + F w := by
  -- safe: only linearity lemmas
  simp [F, encodeVec_add, decodeVec_add, Matrix.mulVec_add]

lemma F_smul (a : ℂ) (v : QubitVec) : F (a • v) = a • F v := by
  simp [F, encodeVec_smul, decodeVec_smul, Matrix.mulVec_smul]

/-- Extract the ket0 basis case from the already-proved state theorem. -/
lemma F_ket0 :
  F (ket0.val) = (X • ket0).val := by
  -- use the vector-level correctness theorem (decode_state now returns QubitVec)
  have hval :
      decode_state (LogicalX • encode_state ket0) = (X • ket0).val :=
    logicalX_correct_ket0
  -- rewrite the left side into `F ket0.val` using only definitional simp
  -- (no global simp search)
  -- LHS:
  --   decode_state_def -> decodeVec ( (LogicalX • encode_state ket0).val )
  --   smul_QState_val  -> mulVec LogicalX.val (encode_state ket0).val
  --   encode_state_val -> encodeVec ket0.val
  simpa [F] using (by
    simpa [decode_state_def, smul_QState_val, encode_state_val] using hval)

/-- Extract the ket1 basis case from the already-proved state theorem. -/
lemma F_ket1 :
  F (ket1.val) = (X • ket1).val := by
  have hval :
      decode_state (LogicalX • encode_state ket1) = (X • ket1).val :=
    logicalX_correct_ket1
  simpa [F] using (by
    simpa [decode_state_def, smul_QState_val, encode_state_val] using hval)

/-- The vector-level correctness statement, proved by linearity + basis cases
    *but the basis cases come from state-level theorems*. -/
lemma F_correct (v : QubitVec) :
  F v = (X.val).mulVec v := by
  -- expand `v` in the {ket0, ket1} basis
  have hv : v = (v 0) • ket0.val + (v 1) • ket1.val := by
    simpa using qubitVec_eq_lincomb_kets (v := v)

  calc
    F v
        = F ((v 0) • ket0.val + (v 1) • ket1.val) := by
            -- hv : v = ...
            -- rewrite v on the LHS
            simpa using congrArg F hv
    _   = (v 0) • F (ket0.val) + (v 1) • F (ket1.val) := by
          simp [F_add, F_smul]
    _   = (v 0) • (X • ket0).val + (v 1) • (X • ket1).val := by
          simp [F_ket0, F_ket1]
    _   = (X.val).mulVec ((v 0) • ket0.val + (v 1) • ket1.val) := by
          -- push mulVec through the linear combination and use X action on kets
          simp [Matrix.mulVec_add, Matrix.mulVec_smul]
          have hx0 : Xmat.mulVec (↑ket0 : QubitVec) = (↑ket1 : QubitVec) := by
            vec_expand
            all_goals
              -- only unfold what is necessary; avoid global simp loops
              simp [Matrix.mulVec, Xmat, ket0, ket1]
          have hx1 : Xmat.mulVec (↑ket1 : QubitVec) = (↑ket0 : QubitVec) := by
            vec_expand
            all_goals
              simp [Matrix.mulVec, Xmat, ket0, ket1]
          rw [hx0, hx1]
    _   = (X.val).mulVec v := by exact (congrArg (fun w => (X.val).mulVec w) hv.symm)

/-- Your requested correctness statement (on `.val` fields). -/
lemma logicalX_correct_val (ψ : Qubit) :
  decode_state (LogicalX • encode_state ψ) = (X • ψ).val := by
  simpa [F, decode_state_def, smul_QState_val, encode_state_val] using
    (F_correct (v := ψ.val))

/-- Correctness as an equality of vectors (decode_state now returns QubitVec). -/
lemma logicalX_correct_state (ψ : Qubit) :
  decode_state (LogicalX • encode_state ψ) = (X • ψ).val := by
  exact logicalX_correct_val ψ

end Quantum
