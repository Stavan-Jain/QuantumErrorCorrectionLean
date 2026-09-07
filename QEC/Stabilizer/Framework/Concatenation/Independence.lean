import QEC.Stabilizer.Framework.Concatenation.Restriction
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrixDecidable

/-!
# Concatenation: structural generator independence

The constructor `concatenate` (M3) takes generator independence
(`GeneratorsIndependent (n₁ * n₂) concatGeneratorsList`) as a hypothesis, because
the only available decision procedure — `Decidable (rowsLinearIndependent L)` —
enumerates all `2 ^ L.length` coefficient vectors, which is infeasible for the
`n₁ * n₂ - k₂` concatenated generators (e.g. `2 ^ 48` for Steane ⊗ Steane).

This file discharges that hypothesis **structurally**: it derives the symplectic
linear independence of the concatenated generators from

* `hin` — the inner generators *together with the two inner logical
  representatives* `X̄₁, Z̄₁` are symplectically independent
  (`rowsLinearIndependent (Cin.generatorsList ++ [X̄₁, Z̄₁])`), and
* `hout` — the outer generators are symplectically independent
  (`rowsLinearIndependent (outerZ ++ outerX)`).

Both inputs are *small* (Steane: `2 ^ 8` and `2 ^ 6`), so they are
`decide`/`native_decide`-able per instance, unlike the `2 ^ 48` direct check.

## Architecture

The engine is the **block-restriction** linear map `blockRestrictSymp b`, the
symplectic-level analogue of `restrictBlock b`: it reads off block `b`'s
symplectic coordinates. Its key properties:

* `blockRestrictSymp_toSymplectic` — it commutes with `toSymplectic ∘ operators`
  and `restrictBlock b`;
* an embedded inner generator restricts to the generator itself on its own
  block and to `0` elsewhere;
* a promoted outer generator restricts to a combination of `X̄₁, Z̄₁`;
* a vector all of whose block restrictions vanish is itself `0`.

Together with the general `rowsLinearIndependent_append_iff`
(`linearIndependent_sum` reindexed over the list-append split), the inner part
(`s1PerBlockList`, a per-block `flatMap`) is shown independent by induction on
the block list, the promoted part by reassembling block restrictions into an
outer relation, and the two spans are shown disjoint — giving the headline
`rowsLinearIndependent_concat` and its `GeneratorsIndependent` corollary.
-/

namespace Quantum

namespace NQubitPauliGroupElement

open NQubitPauliOperator Submodule

variable {n : ℕ}

/-! ## A general append lemma for `rowsLinearIndependent`

`rowsLinearIndependent (A ++ B)` splits into independence of `A`, of `B`, and
disjointness of their symplectic spans — the list-level form of
`linearIndependent_sum`. -/

/-- The append of two generator lists has linearly independent check-matrix rows iff each
piece does and their symplectic spans are disjoint. (Reindexes the row family along
`Fin A.length ⊕ Fin B.length ≃ Fin (A ++ B).length` and applies `linearIndependent_sum`.) -/
theorem rowsLinearIndependent_append_iff (A B : List (NQubitPauliGroupElement n)) :
    rowsLinearIndependent (A ++ B) ↔
      rowsLinearIndependent A ∧ rowsLinearIndependent B ∧
        Disjoint (sympSpan A) (sympSpan B) := by
  have hlen : A.length + B.length = (A ++ B).length := by rw [List.length_append]
  let e : Fin A.length ⊕ Fin B.length ≃ Fin (A ++ B).length :=
    finSumFinEquiv.trans (finCongr hlen)
  have hgetl : ∀ i : Fin A.length, (A ++ B).get (e (Sum.inl i)) = A.get i := by
    intro i
    have hv : (e (Sum.inl i)).val = i.val := by
      simp [e, Equiv.trans_apply, finSumFinEquiv_apply_left]
    rw [List.get_eq_getElem, List.get_eq_getElem]
    simp only [hv]
    exact List.getElem_append_left i.isLt
  have hgetr : ∀ j : Fin B.length, (A ++ B).get (e (Sum.inr j)) = B.get j := by
    intro j
    have hv : (e (Sum.inr j)).val = A.length + j.val := by
      simp [e, Equiv.trans_apply, finSumFinEquiv_apply_right]
    rw [List.get_eq_getElem, List.get_eq_getElem]
    simp only [hv]
    rw [List.getElem_append_right (Nat.le_add_right _ _)]
    congr 1
    omega
  have key : (fun i => checkMatrix (A ++ B) i) ∘ e = Sum.elim (checkMatrix A) (checkMatrix B) := by
    funext s
    rcases s with i | j
    · funext col
      simp only [Function.comp_apply, checkMatrix, Sum.elim_inl, hgetl i]
    · funext col
      simp only [Function.comp_apply, checkMatrix, Sum.elim_inr, hgetr j]
  rw [rowsLinearIndependent, ← linearIndependent_equiv e, key, linearIndependent_sum]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
  rfl

/-- The empty generator list has (vacuously) linearly independent check-matrix rows. -/
lemma rowsLinearIndependent_nil :
    rowsLinearIndependent ([] : List (NQubitPauliGroupElement n)) := by
  rw [rowsLinearIndependent]
  haveI : IsEmpty (Fin ([] : List (NQubitPauliGroupElement n)).length) := by
    simp only [List.length_nil]; infer_instance
  exact linearIndependent_empty_type

/-- A list member's symplectic vector lies in the list's symplectic span. -/
lemma toSymplectic_mem_sympSpan_of_mem {L : List (NQubitPauliGroupElement n)}
    {g : NQubitPauliGroupElement n} (hg : g ∈ L) :
    NQubitPauliOperator.toSymplectic g.operators ∈ sympSpan L :=
  Submodule.subset_span (mem_listToSet_symp_in_range L g hg)

end NQubitPauliGroupElement

namespace Concatenation

open NQubitPauliGroupElement StabilizerGroup NQubitPauliOperator Submodule

variable {n₁ n₂ k₂ : ℕ} [NeZero n₁]

/-! ## Block restriction at the symplectic level -/

/-- The coordinate map embedding inner symplectic indices (`Fin (n₁ + n₁)`) into block `b`'s
slot of the global symplectic indices (`Fin (n₁*n₂ + n₁*n₂)`): X-coordinate `i` ↦ X-coordinate
`qIdx b i`, Z-coordinate `i` ↦ Z-coordinate `qIdx b i`. -/
def blockEmbedIdx (b : Fin n₂) : Fin (n₁ + n₁) → Fin (n₁ * n₂ + n₁ * n₂) :=
  Fin.addCases (fun i => Fin.castAdd (n₁ * n₂) (qIdx b i))
               (fun i => Fin.natAdd (n₁ * n₂) (qIdx b i))

/-- Block restriction as a linear map on symplectic vectors: read off block `b`'s coordinates.
Built as `LinearMap.funLeft` of `blockEmbedIdx`, so linearity is free. -/
def blockRestrictSymp (b : Fin n₂) :
    (Fin (n₁ * n₂ + n₁ * n₂) → ZMod 2) →ₗ[ZMod 2] (Fin (n₁ + n₁) → ZMod 2) :=
  LinearMap.funLeft (ZMod 2) (ZMod 2) (blockEmbedIdx b)

omit [NeZero n₁] in
@[simp] lemma blockRestrictSymp_castAdd (b : Fin n₂) (w : Fin (n₁ * n₂ + n₁ * n₂) → ZMod 2)
    (i : Fin n₁) :
    blockRestrictSymp b w (Fin.castAdd n₁ i) = w (Fin.castAdd (n₁ * n₂) (qIdx b i)) := by
  simp only [blockRestrictSymp, LinearMap.funLeft_apply, blockEmbedIdx, Fin.addCases_left]

omit [NeZero n₁] in
@[simp] lemma blockRestrictSymp_natAdd (b : Fin n₂) (w : Fin (n₁ * n₂ + n₁ * n₂) → ZMod 2)
    (i : Fin n₁) :
    blockRestrictSymp b w (Fin.natAdd n₁ i) = w (Fin.natAdd (n₁ * n₂) (qIdx b i)) := by
  simp only [blockRestrictSymp, LinearMap.funLeft_apply, blockEmbedIdx, Fin.addCases_right]

omit [NeZero n₁] in
/-- The block-restriction map commutes with `toSymplectic ∘ operators` and `restrictBlock`. -/
lemma blockRestrictSymp_toSymplectic (b : Fin n₂) (x : NQubitPauliGroupElement (n₁ * n₂)) :
    blockRestrictSymp b (toSymplectic x.operators)
      = toSymplectic (restrictBlock b x).operators := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [blockRestrictSymp_castAdd, toSymplectic_X_part, toSymplectic_X_part,
      restrictBlock_operators, restrictBlockOp]
  · rw [blockRestrictSymp_natAdd, toSymplectic_Z_part, toSymplectic_Z_part,
      restrictBlock_operators, restrictBlockOp]

/-- A vector all of whose block restrictions vanish is `0` (each coordinate is recovered by
restricting to the block of its qubit). -/
lemma eq_zero_of_forall_blockRestrictSymp_zero (w : Fin (n₁ * n₂ + n₁ * n₂) → ZMod 2)
    (h : ∀ b : Fin n₂, blockRestrictSymp b w = 0) : w = 0 := by
  funext j
  refine Fin.addCases (fun q => ?_) (fun q => ?_) j
  · have := congrFun (h (blockOf q)) (Fin.castAdd n₁ (posOf q))
    rwa [blockRestrictSymp_castAdd, qIdx_blockOf_posOf, Pi.zero_apply] at this
  · have := congrFun (h (blockOf q)) (Fin.natAdd n₁ (posOf q))
    rwa [blockRestrictSymp_natAdd, qIdx_blockOf_posOf, Pi.zero_apply] at this

/-! ## Operator-level restriction of embedded / promoted generators -/

/-- Restricting an inner generator embedded in block `b` to block `b` recovers it. -/
lemma restrictBlock_embedBlock_self (b : Fin n₂) (g : NQubitPauliGroupElement n₁) :
    (restrictBlock b (embedBlock b g)).operators = g.operators := by
  funext i
  change (embedBlock b g).operators (qIdx b i) = g.operators i
  simp only [embedBlock_operators, embedBlockOp, blockOf_qIdx, posOf_qIdx, if_true]

/-- Restricting an inner generator embedded in block `b'` to a different block `b` gives `I`. -/
lemma restrictBlock_embedBlock_ne {b b' : Fin n₂} (h : b ≠ b') (g : NQubitPauliGroupElement n₁) :
    (restrictBlock b (embedBlock b' g)).operators = NQubitPauliOperator.identity n₁ := by
  funext i
  change (embedBlock b' g).operators (qIdx b i) = NQubitPauliOperator.identity n₁ i
  simp only [embedBlock_operators, embedBlockOp, blockOf_qIdx]
  rw [if_neg h]; simp [NQubitPauliOperator.identity]

/-- Restricting a promoted outer generator to block `b` gives the inner logical class of
`t.operators b` (the `promoteSingle` value). -/
lemma restrictBlock_promoteE (Xbar Zbar : NQubitPauliOperator n₁) (b : Fin n₂)
    (t : NQubitPauliGroupElement n₂) :
    (restrictBlock b (promoteE Xbar Zbar t)).operators
      = promoteSingle Xbar Zbar (t.operators b) := by
  funext i
  change (promoteE Xbar Zbar t).operators (qIdx b i) = promoteSingle Xbar Zbar (t.operators b) i
  simp only [promoteE_operators, promoteOp, blockOf_qIdx, posOf_qIdx]

/-- The all-identity operator has zero symplectic vector. -/
lemma toSymplectic_identity (m : ℕ) :
    toSymplectic (NQubitPauliOperator.identity m) = 0 := by
  rw [← NQubitPauliGroupElement.one_operators_def]; exact toSymplectic_one_operators

omit [NeZero n₁] in
/-- The symplectic vector of a (non-`Y`) promoted single Pauli is the matching combination of
the inner logical symplectic vectors. (`Y` is excluded because `promoteSingle` is lossy there.) -/
lemma toSymplectic_promoteSingle (Xbar Zbar : NQubitPauliOperator n₁) {P : PauliOperator}
    (hP : P ≠ PauliOperator.Y) :
    toSymplectic (promoteSingle Xbar Zbar P)
      = (P.toSymplecticSingle.1) • toSymplectic Xbar
        + (P.toSymplecticSingle.2) • toSymplectic Zbar := by
  cases P
  · simp only [promoteSingle, PauliOperator.toSymplecticSingle_I, toSymplectic_identity,
      zero_smul, add_zero]
  · simp only [promoteSingle, PauliOperator.toSymplecticSingle_X, one_smul, zero_smul, add_zero]
  · exact absurd rfl hP
  · simp only [promoteSingle, PauliOperator.toSymplecticSingle_Z, zero_smul, one_smul, zero_add]

/-! ## Independence of one block's embedded inner generators -/

/-- Embedding an independent inner generator list into a single block preserves symplectic
independence. (Block restriction `blockRestrictSymp b` is a left inverse on block `b`, so the
embedded rows are independent exactly when the originals are.) -/
lemma rowsLinearIndependent_map_embedBlock (b : Fin n₂) (L : List (NQubitPauliGroupElement n₁))
    (hL : rowsLinearIndependent L) :
    rowsLinearIndependent (L.map (embedBlock b)) := by
  have hlen : (L.map (embedBlock b)).length = L.length := by rw [List.length_map]
  let e_map : Fin L.length ≃ Fin (L.map (embedBlock b)).length := finCongr hlen.symm
  rw [rowsLinearIndependent, ← linearIndependent_equiv e_map]
  have hcomp : (fun i => checkMatrix (L.map (embedBlock b)) i) ∘ e_map
      = fun i => toSymplectic (embedBlock b (L.get i)).operators := by
    funext i
    have hget : (L.map (embedBlock b)).get (e_map i) = embedBlock b (L.get i) := by
      rw [List.get_eq_getElem, List.get_eq_getElem]
      have hv : (e_map i).val = i.val := by simp [e_map]
      simp only [hv, List.getElem_map]
    change toSymplectic ((L.map (embedBlock b)).get (e_map i)).operators
        = toSymplectic (embedBlock b (L.get i)).operators
    rw [hget]
  rw [hcomp, Fintype.linearIndependent_iff]
  intro f hf i
  have key : ∑ k, f k • checkMatrix L k = 0 := by
    have h0 : blockRestrictSymp b (∑ k, f k • toSymplectic (embedBlock b (L.get k)).operators)
        = 0 := by rw [hf, map_zero]
    rw [map_sum] at h0
    simp only [map_smul, blockRestrictSymp_toSymplectic, restrictBlock_embedBlock_self] at h0
    exact h0
  exact (Fintype.linearIndependent_iff.mp hL) f key i

/-! ## Independence of the per-block inner generators (`flatMap` over distinct blocks) -/

/-- If every element of `M` is an inner generator embedded into some block **other than** `b'`,
then `blockRestrictSymp b'` annihilates the entire symplectic span of `M`. -/
lemma blockRestrictSymp_eq_zero_of_mem_sympSpan (b' : Fin n₂)
    (M : List (NQubitPauliGroupElement (n₁ * n₂)))
    (hM : ∀ e ∈ M, ∃ (b'' : Fin n₂) (g : NQubitPauliGroupElement n₁),
      b'' ≠ b' ∧ e = embedBlock b'' g)
    {v : Fin (n₁ * n₂ + n₁ * n₂) → ZMod 2} (hv : v ∈ sympSpan M) :
    blockRestrictSymp b' v = 0 := by
  have hle : sympSpan M ≤ LinearMap.ker (blockRestrictSymp b') := by
    rw [sympSpan_eq_span_listToSet, Submodule.span_le]
    rintro x ⟨e, he, rfl⟩
    simp only [listToSet, Set.mem_setOf_eq] at he
    obtain ⟨b'', g, hne, rfl⟩ := hM e he
    rw [SetLike.mem_coe, LinearMap.mem_ker, blockRestrictSymp_toSymplectic,
      restrictBlock_embedBlock_ne (Ne.symm hne), toSymplectic_identity]
  exact hle hv

/-- Embedding an independent inner generator list into each of a list of **distinct** blocks
yields a symplectically independent family (the blocks' supports are disjoint). -/
lemma rowsLinearIndependent_flatMap_embedBlock (L : List (NQubitPauliGroupElement n₁))
    (hL : rowsLinearIndependent L) :
    ∀ bs : List (Fin n₂), bs.Nodup →
      rowsLinearIndependent (bs.flatMap (fun b => L.map (embedBlock b))) := by
  intro bs
  induction bs with
  | nil => intro _; simpa using rowsLinearIndependent_nil
  | cons b bs ih =>
    intro hbs
    rw [List.nodup_cons] at hbs
    obtain ⟨hb_notin, hbs_nodup⟩ := hbs
    rw [List.flatMap_cons, rowsLinearIndependent_append_iff]
    refine ⟨rowsLinearIndependent_map_embedBlock b L hL, ih hbs_nodup, ?_⟩
    rw [Submodule.disjoint_def]
    intro v hv_head hv_tail
    apply eq_zero_of_forall_blockRestrictSymp_zero
    intro b'
    by_cases hb' : b' = b
    · subst hb'
      refine blockRestrictSymp_eq_zero_of_mem_sympSpan b' _ ?_ hv_tail
      intro e he
      obtain ⟨b'', hb''_mem, hb''e⟩ := List.mem_flatMap.mp he
      obtain ⟨g, _, rfl⟩ := List.mem_map.mp hb''e
      exact ⟨b'', g, fun h => hb_notin (h ▸ hb''_mem), rfl⟩
    · refine blockRestrictSymp_eq_zero_of_mem_sympSpan b' _ ?_ hv_head
      intro e he
      obtain ⟨g, _, rfl⟩ := List.mem_map.mp he
      exact ⟨b, g, Ne.symm hb', rfl⟩

namespace ConcatCSSData

variable (D : ConcatCSSData n₁ n₂ k₂)

/-- `blockRestrictSymp b` of a promoted outer generator is the matching combination of the
inner logicals' symplectic vectors (using that outer generators are `Y`-free per block). -/
lemma blockRestrictSymp_promoteE (b : Fin n₂) (t : NQubitPauliGroupElement n₂)
    (hY : t.operators b ≠ PauliOperator.Y) :
    blockRestrictSymp b (toSymplectic (promoteE D.Xbar D.Zbar t).operators)
      = (t.operators b).toSymplecticSingle.1 • toSymplectic D.Xbar
        + (t.operators b).toSymplecticSingle.2 • toSymplectic D.Zbar := by
  rw [blockRestrictSymp_toSymplectic, restrictBlock_promoteE, toSymplectic_promoteSingle _ _ hY]

/-- The promoted outer generators are symplectically independent, given that the inner logicals
are (`hlog`) and the outer generators are (`hout`). Each block restriction is a combination of
`X̄₁, Z̄₁`; `hlog` forces the two aggregated coefficients to vanish at every block, which
reassembles into an outer linear relation killed by `hout`. -/
lemma rowsLinearIndependent_promotedOuterList
    (hlog : rowsLinearIndependent [D.Cin.logicalX 0, D.Cin.logicalZ 0])
    (hout : rowsLinearIndependent (D.outerZ ++ D.outerX)) :
    rowsLinearIndependent D.promotedOuterList := by
  rw [ConcatCSSData.promotedOuterList]
  have hlen : ((D.outerZ ++ D.outerX).map (promoteE D.Xbar D.Zbar)).length
      = (D.outerZ ++ D.outerX).length := by rw [List.length_map]
  let e_map : Fin (D.outerZ ++ D.outerX).length ≃
      Fin ((D.outerZ ++ D.outerX).map (promoteE D.Xbar D.Zbar)).length := finCongr hlen.symm
  rw [rowsLinearIndependent, ← linearIndependent_equiv e_map]
  have hcomp : (fun i => checkMatrix ((D.outerZ ++ D.outerX).map (promoteE D.Xbar D.Zbar)) i)
        ∘ e_map
      = fun i =>
        toSymplectic (promoteE D.Xbar D.Zbar ((D.outerZ ++ D.outerX).get i)).operators := by
    funext i
    have hget : ((D.outerZ ++ D.outerX).map (promoteE D.Xbar D.Zbar)).get (e_map i)
        = promoteE D.Xbar D.Zbar ((D.outerZ ++ D.outerX).get i) := by
      rw [List.get_eq_getElem, List.get_eq_getElem]
      have hv : (e_map i).val = i.val := by simp [e_map]
      simp only [hv, List.getElem_map]
    change toSymplectic
        (((D.outerZ ++ D.outerX).map (promoteE D.Xbar D.Zbar)).get (e_map i)).operators
        = toSymplectic (promoteE D.Xbar D.Zbar ((D.outerZ ++ D.outerX).get i)).operators
    rw [hget]
  rw [hcomp, Fintype.linearIndependent_iff]
  intro f hf t
  have hOY : ∀ i : Fin (D.outerZ ++ D.outerX).length, ∀ b,
      ((D.outerZ ++ D.outerX).get i).operators b ≠ PauliOperator.Y :=
    fun i b => D.outer_gen_noY _ (List.get_mem _ i) b
  -- For each block `b`, both aggregated coefficients vanish.
  have hcoeff : ∀ b : Fin n₂,
      (∑ i, f i • (((D.outerZ ++ D.outerX).get i).operators b).toSymplecticSingle.1 = 0) ∧
      (∑ i, f i • (((D.outerZ ++ D.outerX).get i).operators b).toSymplecticSingle.2 = 0) := by
    intro b
    set c1 := ∑ i, f i • (((D.outerZ ++ D.outerX).get i).operators b).toSymplecticSingle.1
      with hc1
    set c2 := ∑ i, f i • (((D.outerZ ++ D.outerX).get i).operators b).toSymplecticSingle.2
      with hc2
    have h0 : blockRestrictSymp b
        (∑ i, f i • toSymplectic (promoteE D.Xbar D.Zbar ((D.outerZ ++ D.outerX).get i)).operators)
        = 0 := by rw [hf, map_zero]
    rw [map_sum] at h0
    simp only [map_smul, D.blockRestrictSymp_promoteE b _ (hOY _ b)] at h0
    have h1 : c1 • toSymplectic D.Xbar + c2 • toSymplectic D.Zbar = 0 := by
      rw [hc1, hc2, Finset.sum_smul, Finset.sum_smul, ← Finset.sum_add_distrib, ← h0]
      exact Finset.sum_congr rfl fun i _ => by simp only [smul_add, smul_smul, smul_eq_mul]
    -- Use independence of the two inner-logical rows.
    have hlog' := Fintype.linearIndependent_iff.mp hlog ![c1, c2]
    have hsum2 : (∑ j, (![c1, c2]) j
        • checkMatrix [D.Cin.logicalX 0, D.Cin.logicalZ 0] j) = 0 := by
      rw [Fin.sum_univ_two]
      simpa [checkMatrix, ConcatCSSData.Xbar, ConcatCSSData.Zbar] using h1
    exact ⟨by simpa using hlog' hsum2 0, by simpa using hlog' hsum2 1⟩
  -- Reassemble the per-block coefficient vanishing into an outer linear relation.
  have hrelation : ∑ i, f i • checkMatrix (D.outerZ ++ D.outerX) i = 0 := by
    funext col
    rw [Finset.sum_apply, Pi.zero_apply]
    refine Fin.addCases (fun b => ?_) (fun b => ?_) col
    · change ∑ i, f i • toSymplectic ((D.outerZ ++ D.outerX).get i).operators (Fin.castAdd n₂ b) = 0
      simp only [toSymplectic_X_part]
      exact (hcoeff b).1
    · change ∑ i, f i • toSymplectic ((D.outerZ ++ D.outerX).get i).operators (Fin.natAdd n₂ b) = 0
      simp only [toSymplectic_Z_part]
      exact (hcoeff b).2
  exact (Fintype.linearIndependent_iff.mp hout) f hrelation t

/-- The inner stabilizers replicated across all blocks are symplectically independent, given the
inner generators are. -/
lemma rowsLinearIndependent_s1PerBlockList (hCin : rowsLinearIndependent D.Cin.generatorsList) :
    rowsLinearIndependent D.s1PerBlockList := by
  rw [ConcatCSSData.s1PerBlockList]
  exact rowsLinearIndependent_flatMap_embedBlock D.Cin.generatorsList hCin
    (List.finRange n₂) (List.nodup_finRange n₂)

/-! ## Disjointness of the inner and promoted spans -/

/-- Block restriction of the inner-stabilizer span lands in the inner-generator span. -/
lemma blockRestrictSymp_mem_sympSpan_inner (b : Fin n₂)
    {v : Fin (n₁ * n₂ + n₁ * n₂) → ZMod 2} (hv : v ∈ sympSpan D.s1PerBlockList) :
    blockRestrictSymp b v ∈ sympSpan D.Cin.generatorsList := by
  have hle : sympSpan D.s1PerBlockList
      ≤ Submodule.comap (blockRestrictSymp b) (sympSpan D.Cin.generatorsList) := by
    rw [sympSpan_eq_span_listToSet, Submodule.span_le]
    rintro x ⟨e, he, rfl⟩
    simp only [listToSet, Set.mem_setOf_eq, ConcatCSSData.s1PerBlockList] at he
    obtain ⟨b'', _, hb''e⟩ := List.mem_flatMap.mp he
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hb''e
    rw [SetLike.mem_coe, Submodule.mem_comap, blockRestrictSymp_toSymplectic]
    by_cases hbb : b'' = b
    · subst hbb
      rw [restrictBlock_embedBlock_self]
      exact toSymplectic_mem_sympSpan_of_mem hg
    · rw [restrictBlock_embedBlock_ne (Ne.symm hbb), toSymplectic_identity]
      exact Submodule.zero_mem _
  exact hle hv

/-- Block restriction of the promoted-stabilizer span lands in the span of the two inner
logical symplectic vectors. -/
lemma blockRestrictSymp_mem_span_logicals (b : Fin n₂)
    {v : Fin (n₁ * n₂ + n₁ * n₂) → ZMod 2} (hv : v ∈ sympSpan D.promotedOuterList) :
    blockRestrictSymp b v
      ∈ sympSpan [D.Cin.logicalX 0, D.Cin.logicalZ 0] := by
  have hle : sympSpan D.promotedOuterList ≤ Submodule.comap (blockRestrictSymp b)
      (sympSpan [D.Cin.logicalX 0, D.Cin.logicalZ 0]) := by
    rw [sympSpan_eq_span_listToSet, Submodule.span_le]
    rintro x ⟨e, he, rfl⟩
    simp only [listToSet, Set.mem_setOf_eq, ConcatCSSData.promotedOuterList] at he
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp he
    rw [SetLike.mem_coe, Submodule.mem_comap,
      D.blockRestrictSymp_promoteE b t (D.outer_gen_noY t ht b)]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
    · exact toSymplectic_mem_sympSpan_of_mem (by simp)
    · exact toSymplectic_mem_sympSpan_of_mem (by simp)
  exact hle hv

/-- The inner-stabilizer span and the promoted-stabilizer span are disjoint, given the inner
generators are independent from the two inner logicals (`hdisj`). Every block restriction of a
shared vector lies in `sympSpan Cin.gens ⊓ span{X̄₁, Z̄₁} = 0`, so the vector itself is `0`. -/
lemma disjoint_s1_promoted
    (hdisj : Disjoint (sympSpan D.Cin.generatorsList)
      (sympSpan [D.Cin.logicalX 0, D.Cin.logicalZ 0])) :
    Disjoint (sympSpan D.s1PerBlockList) (sympSpan D.promotedOuterList) := by
  rw [Submodule.disjoint_def]
  intro v hv_s1 hv_promo
  apply eq_zero_of_forall_blockRestrictSymp_zero
  intro b
  rw [Submodule.disjoint_def] at hdisj
  exact hdisj (blockRestrictSymp b v)
    (D.blockRestrictSymp_mem_sympSpan_inner b hv_s1)
    (D.blockRestrictSymp_mem_span_logicals b hv_promo)

/-! ## The structural independence theorem -/

/-- **Structural concatenated-generator independence.** The concatenated generators are
symplectically independent, given:

* `hin` — the inner generators together with the two inner logical representatives `X̄₁, Z̄₁`
  are symplectically independent, and
* `hout` — the outer generators are symplectically independent.

Both inputs are small (Steane: `2 ^ 8` and `2 ^ 6`), hence `decide`/`native_decide`-able per
instance — unlike the `2 ^ (n₁ n₂ - k₂)` direct check on the concatenated list. -/
theorem rowsLinearIndependent_concat
    (hin : rowsLinearIndependent (D.Cin.generatorsList ++
      [D.Cin.logicalX 0, D.Cin.logicalZ 0]))
    (hout : rowsLinearIndependent (D.outerZ ++ D.outerX)) :
    rowsLinearIndependent D.concatGeneratorsList := by
  obtain ⟨hCin, hlog, hdisj⟩ := (rowsLinearIndependent_append_iff _ _).mp hin
  rw [ConcatCSSData.concatGeneratorsList, rowsLinearIndependent_append_iff]
  exact ⟨D.rowsLinearIndependent_s1PerBlockList hCin,
    D.rowsLinearIndependent_promotedOuterList hlog hout,
    D.disjoint_s1_promoted hdisj⟩

/-- The `GeneratorsIndependent` corollary, ready to feed `concatenate` and the M7 instances. -/
theorem generatorsIndependent_concat
    (hin : rowsLinearIndependent (D.Cin.generatorsList ++
      [D.Cin.logicalX 0, D.Cin.logicalZ 0]))
    (hout : rowsLinearIndependent (D.outerZ ++ D.outerX)) :
    GeneratorsIndependent (n₁ * n₂) D.concatGeneratorsList :=
  GeneratorsIndependent_of_rowsLinearIndependent _ _ (D.rowsLinearIndependent_concat hin hout)

end ConcatCSSData

end Concatenation

end Quantum
