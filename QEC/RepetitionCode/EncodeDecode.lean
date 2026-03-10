import QEC.Foundations.Foundations

namespace Quantum

/-!
# Encode / decode for the 3-qubit repetition code (semantic layer)

This file defines the **semantic** encode and decode maps between **one** qubit and the
**3-qubit** bit-flip repetition code subspace spanned by |000⟩ and |111⟩.

## Layout

- **Codewords**: `zeroL` = |000⟩, `oneL` = |111⟩ (`ket000` / `ket111` from `Foundations`).
- **Encoder** `encodeVec` / `encode_state`: places amplitudes `v 0` and `v 1` only on
  basis labels (0,0,0) and (1,1,1); all other components are zero — so the image lies
  in the 2-dimensional codespace.
- **Decoder** `decodeVec` / `decode_state`: restricts back to the two support points and
  builds a 1-qubit vector/state (normalization handled where needed).

## Related modules

- **`Recovery.lean`**: majority projection onto the same subspace (collapses arbitrary
  3-qubit vectors onto |000⟩/|111⟩ components).
- **`LogicalX.lean`**: logical X implemented as a 3-qubit gate plus decode = single-qubit X.
- Stabilizer generators for this code live in `Stabilizer/Codes/RepetitionCode3.lean`;
  this file stays independent of the Pauli-group stabilizer API.

No syndrome measurement here — only linear maps on amplitude vectors / normalized states.
-/

-- Logical codewords for the 3-bit repetition code (bit-flip code)
noncomputable abbrev zeroL : ThreeQubitState := ket000
noncomputable abbrev oneL : ThreeQubitState := ket111

/-- Semantic encoder on vectors: embed a 1-qubit vector into the span of |000⟩ and |111⟩. -/
noncomputable def encodeVec (v : QubitVec) : ThreeQubitVec :=
  fun ijk =>
    if _ : ijk = (0, 0, 0) then
      v 0
    else if _ : ijk = (1, 1, 1) then
      v 1
    else
      0

/-!
Helper lemmas for proving `encodeVec_norm`.
-/

/-- Sum over a finite type of a one-point indicator function. -/
lemma sum_ite_singleton
  {β : Type*} [Fintype β] [DecidableEq β] (a : β) (r : ℝ) :
  (∑ x : β, (if x = a then r else 0)) = r := by
  classical
  -- `Finset.sum_ite_eq` rewrites the sum to `if a ∈ univ then r else 0`.
  simp

/-- Split a 2-point piecewise definition into a sum of two 1-point indicators. -/
lemma split_two_points
  {β : Type*} [DecidableEq β]
  (x a b : β) (A B : ℝ) (hab : a ≠ b) :
  (if x = a then A else if x = b then B else 0)
    = (if x = a then A else 0) + (if x = b then B else 0) := by
  by_cases hxa : x = a
  · subst hxa
    simp [hab]
  · by_cases hxb : x = b
    · subst hxb
      simp [hxa]
    · simp [hxa, hxb]

/-- The two support points of `encodeVec` are distinct. -/
lemma key_neq : ((0, 0, 0) : ThreeQubitBasis) ≠ (1, 1, 1) := by
  decide

/-- Norm preservation for `encodeVec` . -/
lemma encodeVec_norm (v : QubitVec) :
  norm (encodeVec v) = norm v := by
  classical
  -- Reduce to an equality of the underlying sums inside `Real.sqrt`.
  have hsum :
      (∑ ijk : ThreeQubitBasis, ‖encodeVec v ijk‖ ^ 2)
        = (∑ q : QubitBasis, ‖v q‖ ^ 2) := by
    -- First compute the LHS sum using the fact that `encodeVec` is supported
    -- only on `(0,0,0)` and `(1,1,1)`.
    have hL :
        (∑ ijk : ThreeQubitBasis, ‖encodeVec v ijk‖ ^ 2)
          = (‖v 0‖ ^ 2 + ‖v 1‖ ^ 2) := by
      calc
        (∑ ijk : ThreeQubitBasis, ‖encodeVec v ijk‖ ^ 2)
            =
              ∑ ijk : ThreeQubitBasis,
                (if ijk = (0, 0, 0) then
                    ‖v 0‖ ^ 2
                  else if ijk = (1, 1, 1) then
                    ‖v 1‖ ^ 2
                  else
                    0) := by
              refine Finset.sum_congr rfl ?_
              intro ijk _
              by_cases h0 : ijk = (0, 0, 0)
              · subst h0
                simp [encodeVec]
              · by_cases h1 : ijk = (1, 1, 1)
                · subst h1
                  simp [encodeVec, h0]
                · simp [encodeVec, h0, h1]
        _ =
              ∑ ijk : ThreeQubitBasis,
                ((if ijk = (0, 0, 0) then ‖v 0‖ ^ 2 else 0)
                  + (if ijk = (1, 1, 1) then ‖v 1‖ ^ 2 else 0)) := by
              refine Finset.sum_congr rfl ?_
              intro ijk _
              exact
                (split_two_points
                  (x := ijk)
                  (a := ((0, 0, 0) : ThreeQubitBasis))
                  (b := ((1, 1, 1) : ThreeQubitBasis))
                  (A := ‖v 0‖ ^ 2)
                  (B := ‖v 1‖ ^ 2)
                  key_neq)
        _ =
              (∑ ijk : ThreeQubitBasis, (if ijk = (0, 0, 0) then ‖v 0‖ ^ 2 else 0))
                + (∑ ijk : ThreeQubitBasis, (if ijk = (1, 1, 1) then ‖v 1‖ ^ 2 else 0)) := by
              simp [Finset.sum_add_distrib]
        _ = ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 := by
              simp

    -- Now compute the RHS sum (over `Fin 2`).
    have hR :
        (∑ q : QubitBasis, ‖v q‖ ^ 2) = (‖v 0‖ ^ 2 + ‖v 1‖ ^ 2) := by
      -- `QubitBasis` is `Fin 2`.
      simp [QubitBasis, Fin.sum_univ_two]

    -- Combine.
    linarith [hL, hR]

  -- Finish by unfolding `norm` and rewriting the sum under the square root.
  simp [norm, hsum]

lemma encodeVec_add (v w : QubitVec) :
  encodeVec (v + w) = encodeVec v + encodeVec w := by
  classical
  funext ijk
  by_cases h0 : ijk = (0,0,0)
  · subst h0
    simp [encodeVec]
  · by_cases h1 : ijk = (1,1,1)
    · subst h1
      simp [encodeVec]
    · simp [encodeVec, h0, h1]

lemma encodeVec_smul (a : ℂ) (v : QubitVec) :
  encodeVec (a • v) = a • encodeVec v := by
  funext ijk
  simp [encodeVec, Pi.smul_apply]

/-- Semantic encoder on states: wrap `encodeVec` and use `encodeVec_norm` for normalization. -/
noncomputable def encode_state (ψ : Qubit) : ThreeQubitState :=
  ⟨encodeVec ψ.val, by
    -- here you'd use `encodeVec_norm` and `ψ.property : norm ψ.val = 1`
    have := ψ.property
    rw [encodeVec_norm]
    exact this⟩

/-- Unfolding lemma: value field of `encode_state`. -/
@[simp] lemma encode_state_val (ψ : Qubit) :
  (encode_state ψ).val = encodeVec ψ.val := rfl

@[simp] lemma encode_state_ket0 :
  encode_state ket0 = zeroL := by
  ext b
  simp [encode_state, encodeVec, ket0, zeroL, ket000, basisVec]

@[simp] lemma encode_state_ket1 :
  encode_state ket1 = oneL := by
  ext b
  simp [encode_state, encodeVec, ket1, oneL, ket111, basisVec]
  intro h0
  rw [h0]
  simp only [Prod.mk.injEq, zero_ne_one, and_self, not_false_eq_true]

/-- Semantic decoder on vectors: read off amplitudes of |000⟩ and |111⟩. -/
noncomputable def decodeVec (v : ThreeQubitVec) : QubitVec :=
  fun q =>
    match q with
    | 0 => v (0, 0, 0)
    | 1 => v (1, 1, 1)

/-- On the image of `encodeVec`, `decodeVec` is a left inverse. -/
lemma decodeVec_encodeVec (v : QubitVec) :
  decodeVec (encodeVec v) = v := by
  funext q
  fin_cases q <;> simp [decodeVec, encodeVec]

lemma decodeVec_add (v w : ThreeQubitVec) :
  decodeVec (v + w) = decodeVec v + decodeVec w := by
  funext q
  fin_cases q <;> simp [decodeVec, Pi.add_apply]

lemma decodeVec_smul (a : ℂ) (v : ThreeQubitVec) :
  decodeVec (a • v) = a • decodeVec v := by
  funext q
  fin_cases q <;> simp [decodeVec, Pi.smul_apply]

/-- Semantic decoder on states.

Returns a vector (not necessarily normalized). Only the vector values are used
for most semantic equalities; normalization is not required. -/
noncomputable def decode_state (ψ : ThreeQubitState) : QubitVec :=
  decodeVec ψ.val

@[simp] lemma decode_state_def (ψ : ThreeQubitState) :
  decode_state ψ = decodeVec ψ.val := rfl

@[simp] lemma decode_state_encode_state (ψ : Qubit) :
  decode_state (encode_state ψ) = ψ.val := by
  simp [decode_state, encode_state, decodeVec_encodeVec]

@[simp] lemma decode_ket000 : decode_state ket000 = ket0.val := by
  vec_expand_simp[decode_state, decodeVec, ket0]

@[simp] lemma decode_ket111 : decode_state ket111 = ket1.val := by
  vec_expand_simp[decode_state, decodeVec, ket1]

end Quantum
