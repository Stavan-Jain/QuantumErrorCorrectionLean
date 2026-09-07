import QEC.Stabilizer.Framework.Concatenation.Constructor

/-!
# Concatenation, Tier 2a (part 1): the block-restriction calculus

Milestone **M5** of the CSS concatenation plan
(`qec-lab:pipeline/attempts/concat_css_general/plan.md`), first half.

This file provides `restrictBlock b g`: the inner operator obtained by reading
off block `b` of an `n₁ * n₂`-qubit operator `g` (a phase-0 element of the inner
Pauli group `NQubitPauliGroupElement n₁`). It establishes:

* `weight_eq_sum_restrictBlock` — the global weight is the sum of the per-block
  restriction weights (the additivity feeding the M6 distance bound);
* `anticommutesAt_count_restrictBlock` — the anticommuting-position count of `g`
  against an embedded inner operator equals that of the restriction against the
  underlying inner operator (the parity bridge, dual to
  `anticommutesAt_count_eq`);
* `restrictBlock_mem_centralizer` — if `g` centralizes the concatenated
  stabilizer then every block restriction centralizes the inner stabilizer. This
  is what lets M4's `centralizer_classify_of_k1` apply per block.

The companion file `Correspondence.lean` builds the induced outer logical on top
of these.
-/

namespace Quantum.Concatenation

open NQubitPauliGroupElement StabilizerGroup

variable {n₁ n₂ k₂ : ℕ} [NeZero n₁]

/-! ## Block restriction -/

/-- Operator-level restriction: read off block `b` of an `n₁ * n₂`-qubit
operator. -/
def restrictBlockOp (b : Fin n₂) (g : NQubitPauliGroupElement (n₁ * n₂)) :
    NQubitPauliOperator n₁ :=
  fun i => g.operators (qIdx b i)

/-- Group-element restriction (phase 0, per the zero-phase convention). The
phase of `g` is discarded — only the operator part of block `b` is retained,
which is all the commutation / weight arguments consume. -/
def restrictBlock (b : Fin n₂) (g : NQubitPauliGroupElement (n₁ * n₂)) :
    NQubitPauliGroupElement n₁ :=
  ofOperator (restrictBlockOp b g)

omit [NeZero n₁] in
@[simp] lemma restrictBlock_phasePower (b : Fin n₂) (g : NQubitPauliGroupElement (n₁ * n₂)) :
    (restrictBlock b g).phasePower = 0 := rfl

omit [NeZero n₁] in
@[simp] lemma restrictBlock_operators (b : Fin n₂) (g : NQubitPauliGroupElement (n₁ * n₂)) :
    (restrictBlock b g).operators = restrictBlockOp b g := rfl

omit [NeZero n₁] in
@[simp] lemma restrictBlockOp_apply (b : Fin n₂) (g : NQubitPauliGroupElement (n₁ * n₂))
    (i : Fin n₁) : restrictBlockOp b g i = g.operators (qIdx b i) := rfl

/-! ## Weight additivity -/

/-- The block-`b` support of `g` is the image of the restriction's support under
`qIdx b`. -/
lemma image_qIdx_support_restrictBlock (b : Fin n₂) (g : NQubitPauliGroupElement (n₁ * n₂)) :
    (restrictBlock b g).support.image (qIdx b) = g.support.filter (fun q => blockOf q = b) := by
  ext q
  simp only [Finset.mem_image, Finset.mem_filter, NQubitPauliGroupElement.mem_support,
    restrictBlock_operators, restrictBlockOp]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨hi, blockOf_qIdx b i⟩
  · rintro ⟨hq, hb⟩
    refine ⟨posOf q, ?_, ?_⟩
    · rw [show qIdx b (posOf q) = q from by rw [← hb]; exact qIdx_blockOf_posOf q]; exact hq
    · rw [← hb]; exact qIdx_blockOf_posOf q

/-- **(M5.)** The global weight of an `n₁ * n₂`-qubit element is the sum of its
per-block restriction weights. The additivity that, paired with
`inducedOuter_support_eq`, drives the distance lower bound. -/
lemma weight_eq_sum_restrictBlock (g : NQubitPauliGroupElement (n₁ * n₂)) :
    g.weight = ∑ b : Fin n₂, (restrictBlock b g).weight := by
  rw [weight_eq_sum_block_weights]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [show (restrictBlock b g).weight = (restrictBlock b g).support.card from rfl,
    ← image_qIdx_support_restrictBlock b g,
    Finset.card_image_of_injective _ (fun i i' h => (qIdx_injective h).2)]

/-! ## Commutation bridge -/

/-- Per-position reduction: `g` anticommutes with the block-`b` embedding of `s`
at `q` exactly when `q` lies in block `b` and the restriction anticommutes with
`s` at `posOf q`. Dual to `anticommutesAt_embedBlock_iff`. -/
private lemma anticommutesAt_restrictBlock_iff (b : Fin n₂)
    (g : NQubitPauliGroupElement (n₁ * n₂)) (s : NQubitPauliGroupElement n₁)
    (q : Fin (n₁ * n₂)) :
    NQubitPauliGroupElement.anticommutesAt g.operators (embedBlock b s).operators q
      ↔ blockOf q = b ∧
        NQubitPauliGroupElement.anticommutesAt (restrictBlock b g).operators s.operators
          (posOf q) := by
  by_cases hb : blockOf q = b
  · have hg : g.operators q = (restrictBlock b g).operators (posOf q) := by
      change g.operators q = g.operators (qIdx b (posOf q))
      congr 1
      rw [← hb]; exact (qIdx_blockOf_posOf q).symm
    have hs : (embedBlock b s).operators q = s.operators (posOf q) := by
      simp [embedBlock_operators, embedBlockOp, hb]
    simp only [hb, true_and]
    unfold NQubitPauliGroupElement.anticommutesAt
    rw [hg, hs]
  · simp only [hb, false_and, iff_false]
    exact not_anticommutesAt_of_right_I _ _ q (by simp [embedBlock_operators, embedBlockOp, hb])

open Classical in
/-- Parity bridge: the count of physical qubits where `g` anticommutes with the
embedding of an inner operator `s` into block `b` equals the count of in-block
positions where the restriction `restrictBlock b g` anticommutes with `s`. Dual
to `anticommutesAt_count_eq`. -/
lemma anticommutesAt_count_restrictBlock (b : Fin n₂) (g : NQubitPauliGroupElement (n₁ * n₂))
    (s : NQubitPauliGroupElement n₁) :
    (Finset.univ.filter (anticommutesAt g.operators (embedBlock b s).operators)).card
      = (Finset.univ.filter
          (anticommutesAt (restrictBlock b g).operators s.operators)).card := by
  have hinj : Function.Injective (qIdx b : Fin n₁ → Fin (n₁ * n₂)) :=
    fun i i' h => (qIdx_injective h).2
  have heq : (Finset.univ.filter (anticommutesAt g.operators (embedBlock b s).operators))
      = (Finset.univ.filter
          (anticommutesAt (restrictBlock b g).operators s.operators)).image (qIdx b) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      anticommutesAt_restrictBlock_iff]
    constructor
    · rintro ⟨hb, hac⟩
      exact ⟨posOf q, hac, by rw [← hb]; exact qIdx_blockOf_posOf q⟩
    · rintro ⟨i, hac, rfl⟩
      exact ⟨blockOf_qIdx b i, by rw [posOf_qIdx]; exact hac⟩
  rw [heq, Finset.card_image_of_injective _ hinj]

/-- `g` commutes with an embedded inner operator iff its block restriction
commutes with the underlying inner operator (both via the
even-anticommuting-count characterisation). -/
lemma restrictBlock_commute_embed_iff (b : Fin n₂) (g : NQubitPauliGroupElement (n₁ * n₂))
    (s : NQubitPauliGroupElement n₁) :
    g * embedBlock b s = embedBlock b s * g ↔ restrictBlock b g * s = s * restrictBlock b g := by
  rw [commutes_iff_even_anticommutes, commutes_iff_even_anticommutes,
    anticommutesAt_count_restrictBlock]

/-! ## Symplectic gluing (for the M5 coset-injectivity kernel) -/

open NQubitPauliOperator in
/-- An `n₁·n₂`-qubit operator's symplectic vector is the sum of its blocks'
embedded restriction vectors. The blocks have disjoint support, so at each
symplectic coordinate (qubit `q`) only the `blockOf q` summand is nonzero. -/
lemma toSymplectic_eq_sum_embed_restrictBlock (x : NQubitPauliGroupElement (n₁ * n₂)) :
    toSymplectic x.operators
      = ∑ b : Fin n₂, toSymplectic (embedBlock b (restrictBlock b x)).operators := by
  funext j
  rw [Finset.sum_apply]
  have hsingle : ∀ q : Fin (n₁ * n₂),
      (∀ b, b ≠ blockOf q → (embedBlock b (restrictBlock b x)).operators q = PauliOperator.I)
      ∧ (embedBlock (blockOf q) (restrictBlock (blockOf q) x)).operators q = x.operators q := by
    intro q
    refine ⟨fun b hb => ?_, ?_⟩
    · simp only [embedBlock_operators, embedBlockOp]; exact if_neg (Ne.symm hb)
    · simp only [embedBlock_operators, embedBlockOp, restrictBlock_operators,
        restrictBlockOp, if_true, qIdx_blockOf_posOf]
  refine Fin.addCases (fun q => ?_) (fun q => ?_) j
  · rw [toSymplectic_X_part, Finset.sum_eq_single (blockOf q)
        (fun b _ hb => by rw [toSymplectic_X_part, (hsingle q).1 b hb]; rfl)
        (fun h => absurd (Finset.mem_univ _) h), toSymplectic_X_part, (hsingle q).2]
  · rw [toSymplectic_Z_part, Finset.sum_eq_single (blockOf q)
        (fun b _ hb => by rw [toSymplectic_Z_part, (hsingle q).1 b hb]; rfl)
        (fun h => absurd (Finset.mem_univ _) h), toSymplectic_Z_part, (hsingle q).2]

namespace ConcatCSSData

variable (D : ConcatCSSData n₁ n₂ k₂)

/-- An embedded inner generator is one of the concatenated generators. -/
lemma embedBlock_mem_concatGeneratorsList (b : Fin n₂) (s : NQubitPauliGroupElement n₁)
    (hs : s ∈ NQubitPauliGroupElement.listToSet D.Cin.generatorsList) :
    embedBlock b s ∈ NQubitPauliGroupElement.listToSet D.concatGeneratorsList := by
  simp only [NQubitPauliGroupElement.listToSet, Set.mem_setOf_eq] at hs ⊢
  simp only [ConcatCSSData.concatGeneratorsList, ConcatCSSData.s1PerBlockList, List.mem_append,
    List.mem_flatMap, List.mem_map, List.mem_finRange]
  exact Or.inl ⟨b, trivial, s, hs, rfl⟩

open NQubitPauliOperator in
/-- **(M5 kernel infra.)** Embedding into block `b` sends the inner symplectic
span into the concatenated span: if
`toSymplectic s ∈ sympSpan Cin.generatorsList`, then
`toSymplectic (embedBlock b s) ∈ sympSpan concatGeneratorsList`. Proven by
realizing `s`'s operator part with a closure element
(`exists_mem_closure_of_symp_in_span`) and inducting over the closure (embedding
is operator-multiplicative via `mulOp_embedBlockOp_operators`, so its symplectic
vector is additive). -/
lemma toSymplectic_embedBlock_mem_concatSpan (b : Fin n₂) (s : NQubitPauliGroupElement n₁)
    (hs : toSymplectic s.operators ∈ sympSpan D.Cin.generatorsList) :
    toSymplectic (embedBlock b s).operators ∈ sympSpan D.concatGeneratorsList := by
  obtain ⟨s', hs'mem, hs'op⟩ :=
    exists_mem_closure_of_symp_in_span D.Cin.generatorsList s.operators hs
  have hss' : (embedBlock b s).operators = (embedBlock b s').operators := by
    simp only [embedBlock_operators, hs'op]
  rw [hss']
  refine Subgroup.closure_induction
    (p := fun k _ => toSymplectic (embedBlock b k).operators ∈ sympSpan D.concatGeneratorsList)
    ?_ ?_ ?_ ?_ hs'mem
  · intro c hc
    rw [sympSpan_eq_span_listToSet]
    exact Submodule.subset_span
      (Set.mem_image_of_mem _ (D.embedBlock_mem_concatGeneratorsList b c hc))
  · simp only [embedBlock_one, toSymplectic_one_operators]
    exact Submodule.zero_mem _
  · intro a a' _ _ ha ha'
    rw [show toSymplectic (embedBlock b (a * a')).operators
        = toSymplectic (embedBlock b a).operators + toSymplectic (embedBlock b a').operators from by
      have hop : (embedBlock b (a * a')).operators
          = (embedBlock b a * embedBlock b a').operators :=
        (mulOp_embedBlockOp_operators b a.operators a'.operators).symm
      rw [hop]; funext j; exact toSymplectic_mul _ _ j]
    exact Submodule.add_mem _ ha ha'
  · intro a _ ha
    rw [show toSymplectic (embedBlock b a⁻¹).operators
        = toSymplectic (embedBlock b a).operators from rfl]
    exact ha

/-- **(M5.)** If `g` centralizes the concatenated stabilizer, every block
restriction centralizes the inner stabilizer. The hinge that lets M4's
`centralizer_classify_of_k1` apply block by block. -/
lemma restrictBlock_mem_centralizer (g : NQubitPauliGroupElement (n₁ * n₂))
    (hg : g ∈ centralizer D.concatStabGroup) (b : Fin n₂) :
    restrictBlock b g ∈ centralizer D.Cin.toStabilizerGroup := by
  apply CentralizerLemmas.mem_centralizer_of_commutes_list _ _ D.Cin.generatorsList rfl
  intro s hs
  -- `embedBlock b s` is a concatenated generator, hence centralized by `g`.
  have hmem : embedBlock b s ∈ D.concatStabGroup.toSubgroup :=
    Subgroup.subset_closure (D.embedBlock_mem_concatGeneratorsList b s hs)
  have hcomm : embedBlock b s * g = g * embedBlock b s :=
    (mem_centralizer_iff g D.concatStabGroup).mp hg (embedBlock b s) hmem
  exact ((restrictBlock_commute_embed_iff b g s).mp hcomm.symm).symm

end ConcatCSSData

end Quantum.Concatenation
