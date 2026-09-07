import QEC.Stabilizer.Framework.Concatenation.Restriction

/-!
# Concatenation, Tier 2a (part 2): the induced outer logical

Milestone **M5** of the CSS concatenation plan
(`qec-lab:pipeline/attempts/concat_css_general/plan.md`), second half.

For a centralizing element `g` of the concatenated stabilizer, each block
restriction `restrictBlock b g` lies in the inner centralizer (M5 part 1), so by
M4's classification it is either inner-stabilizer-like or a nontrivial inner
logical. The **induced outer operator** `inducedOuter D g` records, per block, the
inner logical *class* of that restriction — read off from how it commutes with the
inner logicals `X̄₁`, `Z̄₁`:

* commutes with both → `I` (stabilizer-like);
* anticommutes with `Z̄₁` only → `X`;
* anticommutes with `X̄₁` only → `Z`;
* anticommutes with both → `Y`.

The key bridge `induced_anticommute_parity` says, for a `Y`-free outer operator
`h`, that `inducedOuter D g` anticommutes with `h` exactly when `g` anticommutes
with the promoted `h` — the dual of the M3 parity core. From it:

* `inducedOuter_support_eq` — block `b` is in the support iff `restrictBlock b g`
  is a nontrivial inner logical (uses M4);
* `inducedOuter_mem_centralizer` — `inducedOuter D g` centralizes the outer
  stabilizer.

(`inducedOuter_not_mem_stabilizer` / `inducedOuter_isNontrivialLogical`, the coset
injectivity of plan risk R7, are developed separately.)
-/

namespace Quantum.Concatenation

open NQubitPauliGroupElement StabilizerGroup

variable {n₁ n₂ k₂ : ℕ} [NeZero n₁]

/-! ## The induced outer operator -/

open Classical in
/-- The inner logical class of block `b`'s restriction, read off from its commutation with
the inner logicals: `I` if it commutes with both, `X`/`Z` for a single anticommutation,
`Y` for both. -/
noncomputable def inducedOuterOp (D : ConcatCSSData n₁ n₂ k₂)
    (g : NQubitPauliGroupElement (n₁ * n₂)) : NQubitPauliOperator n₂ :=
  fun b =>
    if Anticommute (restrictBlock b g) (D.Cin.logicalZ 0) then
      (if Anticommute (restrictBlock b g) (D.Cin.logicalX 0)
        then PauliOperator.Y else PauliOperator.X)
    else
      (if Anticommute (restrictBlock b g) (D.Cin.logicalX 0)
        then PauliOperator.Z else PauliOperator.I)

/-- The induced outer operator as a phase-0 group element. -/
noncomputable def inducedOuter (D : ConcatCSSData n₁ n₂ k₂)
    (g : NQubitPauliGroupElement (n₁ * n₂)) : NQubitPauliGroupElement n₂ :=
  ofOperator (inducedOuterOp D g)

@[simp] lemma inducedOuter_operators (D : ConcatCSSData n₁ n₂ k₂)
    (g : NQubitPauliGroupElement (n₁ * n₂)) :
    (inducedOuter D g).operators = inducedOuterOp D g := rfl

namespace ConcatCSSData

variable (D : ConcatCSSData n₁ n₂ k₂)

/-- The induced class at `b` is `I` exactly when the restriction commutes with both inner
logicals. -/
lemma inducedOuterOp_eq_I_iff (g : NQubitPauliGroupElement (n₁ * n₂)) (b : Fin n₂) :
    inducedOuterOp D g b = PauliOperator.I
      ↔ ¬ Anticommute (restrictBlock b g) (D.Cin.logicalZ 0)
        ∧ ¬ Anticommute (restrictBlock b g) (D.Cin.logicalX 0) := by
  unfold inducedOuterOp
  split_ifs with h1 h2 h3
  · exact iff_of_false (by decide) (fun hc => hc.1 h1)
  · exact iff_of_false (by decide) (fun hc => hc.1 h1)
  · exact iff_of_false (by decide) (fun hc => hc.2 h3)
  · exact iff_of_true rfl ⟨h1, h3⟩

/-- **(Per-block bridge.)** For a `Y`-free entry `h.operators b`, the induced operator
anticommutes with `h` at block `b` exactly when the restriction anticommutes with the
promoted single-qubit Pauli `ofOperator (promoteSingle … (h.operators b))` (= `1`, `X̄₁`, or
`Z̄₁`). The single-block analogue of `cnt_odd_iff`. -/
lemma induced_block_anticommute_iff (g : NQubitPauliGroupElement (n₁ * n₂))
    (h : NQubitPauliGroupElement n₂) (b : Fin n₂)
    (hP : h.operators b ≠ PauliOperator.Y) :
    NQubitPauliGroupElement.anticommutesAt (inducedOuterOp D g) h.operators b
      ↔ Anticommute (restrictBlock b g)
          (ofOperator (promoteSingle D.Xbar D.Zbar (h.operators b))) := by
  rcases hPb : h.operators b with _ | _ | _ | _
  · -- I: both sides false
    refine iff_of_false (not_anticommutesAt_of_right_I _ _ b hPb) ?_
    simp only [promoteSingle, ofOperator_identity]
    exact not_anticommute_one_right _
  · -- X: both sides ↔ anticommuting with X̄₁ (the Z-component bit)
    rw [show ofOperator (promoteSingle D.Xbar D.Zbar PauliOperator.X)
        = (D.Cin.logicalX 0) from by simp only [promoteSingle]; exact D.ofOperator_Xbar]
    simp only [NQubitPauliGroupElement.anticommutesAt, inducedOuterOp, hPb]
    split_ifs with h1 h2 h3 <;>
      first
        | exact iff_of_true (by decide) (by assumption)
        | exact iff_of_false (by decide) (by assumption)
  · exact absurd hPb hP
  · -- Z: both sides ↔ anticommuting with Z̄₁ (the X-component bit)
    rw [show ofOperator (promoteSingle D.Xbar D.Zbar PauliOperator.Z)
        = (D.Cin.logicalZ 0) from by simp only [promoteSingle]; exact D.ofOperator_Zbar]
    simp only [NQubitPauliGroupElement.anticommutesAt, inducedOuterOp, hPb]
    split_ifs with h1 h2 h3 <;>
      first
        | exact iff_of_true (by decide) (by assumption)
        | exact iff_of_false (by decide) (by assumption)

/-- Per-position reduction for the induced bridge: `g` anticommutes with the promoted `h` at
`q` exactly when the restriction anticommutes with the single-qubit promotion of `h.operators b`
at `posOf q` (within block `b = blockOf q`). -/
lemma anticommutesAt_g_promoteE (g : NQubitPauliGroupElement (n₁ * n₂))
    (h : NQubitPauliGroupElement n₂) (b : Fin n₂) (q : Fin (n₁ * n₂)) (hb : blockOf q = b) :
    NQubitPauliGroupElement.anticommutesAt g.operators (promoteE D.Xbar D.Zbar h).operators q
      ↔ NQubitPauliGroupElement.anticommutesAt (restrictBlock b g).operators
          (promoteSingle D.Xbar D.Zbar (h.operators b)) (posOf q) := by
  have hval1 : (promoteE D.Xbar D.Zbar h).operators q
      = promoteSingle D.Xbar D.Zbar (h.operators b) (posOf q) := by
    simp only [promoteE_operators, promoteOp, hb]
  have hval2 : g.operators q = (restrictBlock b g).operators (posOf q) := by
    change g.operators q = g.operators (qIdx b (posOf q))
    congr 1; rw [← hb]; exact (qIdx_blockOf_posOf q).symm
  unfold NQubitPauliGroupElement.anticommutesAt
  rw [hval1, hval2]

open Classical in
/-- Block-decomposition: the anticommuting-position count of `g` against a promoted outer
operator is the sum over blocks of the per-block restriction-vs-promotion counts. The mixed
analogue of `promote_count_eq_sum`. -/
lemma count_promoteE_eq_sum_restrict (g : NQubitPauliGroupElement (n₁ * n₂))
    (h : NQubitPauliGroupElement n₂) :
    (Finset.univ.filter
        (anticommutesAt g.operators (promoteE D.Xbar D.Zbar h).operators)).card
      = ∑ b : Fin n₂, (Finset.univ.filter (anticommutesAt (restrictBlock b g).operators
          (promoteSingle D.Xbar D.Zbar (h.operators b)))).card := by
  rw [Finset.card_eq_sum_card_fiberwise (fun q _ => Finset.mem_univ (blockOf q))]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.filter_filter]
  have himg : Finset.univ.filter (fun q => anticommutesAt g.operators
        (promoteE D.Xbar D.Zbar h).operators q ∧ blockOf q = b)
      = (Finset.univ.filter (anticommutesAt (restrictBlock b g).operators
          (promoteSingle D.Xbar D.Zbar (h.operators b)))).image (qIdx b) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hac, hb⟩
      exact ⟨posOf q, (D.anticommutesAt_g_promoteE g h b q hb).mp hac,
        by rw [← hb]; exact qIdx_blockOf_posOf q⟩
    · rintro ⟨i, hi, rfl⟩
      refine ⟨(D.anticommutesAt_g_promoteE g h b (qIdx b i) (blockOf_qIdx b i)).mpr ?_,
        blockOf_qIdx b i⟩
      rw [posOf_qIdx]; exact hi
  rw [himg, Finset.card_image_of_injective _ (fun i i' h => (qIdx_injective h).2)]

open Classical in
/-- **(Induced parity bridge.)** For a `Y`-free outer operator `h`, the anticommuting-position
count of the induced operator against `h` has the same parity as that of `g` against the
promoted `h`. The dual of `promote_anticommute_parity`. -/
lemma induced_count_mod_two (g : NQubitPauliGroupElement (n₁ * n₂))
    (h : NQubitPauliGroupElement n₂) (hY : ∀ b, h.operators b ≠ PauliOperator.Y) :
    (Finset.univ.filter (anticommutesAt (inducedOuterOp D g) h.operators)).card % 2
      = (Finset.univ.filter
          (anticommutesAt g.operators (promoteE D.Xbar D.Zbar h).operators)).card % 2 := by
  rw [D.count_promoteE_eq_sum_restrict g h, Finset.card_filter]
  conv_rhs => rw [Finset.sum_nat_mod]
  congr 1
  refine Finset.sum_congr rfl (fun b _ => ?_)
  by_cases hac : anticommutesAt (inducedOuterOp D g) h.operators b
  · simp only [if_pos hac]
    exact (Nat.odd_iff.mp ((anticommutes_iff_odd_anticommutes _ _).mp
      ((D.induced_block_anticommute_iff g h b (hY b)).mp hac))).symm
  · simp only [if_neg hac]
    exact (Nat.even_iff.mp (Nat.not_odd_iff_even.mp (fun ho => hac
      ((D.induced_block_anticommute_iff g h b (hY b)).mpr
        ((anticommutes_iff_odd_anticommutes _ _).mpr ho))))).symm

/-- **(M5.)** For a `Y`-free outer operator `h`, the induced operator commutes with `h` iff `g`
commutes with the promoted `h`. -/
lemma induced_commute_iff (g : NQubitPauliGroupElement (n₁ * n₂))
    (h : NQubitPauliGroupElement n₂) (hY : ∀ b, h.operators b ≠ PauliOperator.Y) :
    inducedOuter D g * h = h * inducedOuter D g
      ↔ g * promoteE D.Xbar D.Zbar h = promoteE D.Xbar D.Zbar h * g := by
  rw [commutes_iff_even_anticommutes (inducedOuter D g) h,
    commutes_iff_even_anticommutes g (promoteE D.Xbar D.Zbar h), inducedOuter_operators,
    Nat.even_iff, Nat.even_iff, D.induced_count_mod_two g h hY]

/-- A promoted outer generator is one of the concatenated generators. -/
lemma promoteE_mem_concatGeneratorsList (y : NQubitPauliGroupElement n₂)
    (hy : y ∈ D.outerZ ++ D.outerX) :
    promoteE D.Xbar D.Zbar y ∈ NQubitPauliGroupElement.listToSet D.concatGeneratorsList := by
  simp only [NQubitPauliGroupElement.listToSet, Set.mem_setOf_eq,
    ConcatCSSData.concatGeneratorsList, ConcatCSSData.promotedOuterList, List.mem_append,
    List.mem_map]
  exact Or.inr ⟨y, List.mem_append.mp hy, rfl⟩

/-- **(M5.)** The induced outer operator centralizes the outer stabilizer: for each outer
generator `y`, `inducedOuter D g` commutes with `y` because `g` commutes with `promoteE y`
(a concatenated generator) and the induced bridge transports that commutation. -/
theorem inducedOuter_mem_centralizer (g : NQubitPauliGroupElement (n₁ * n₂))
    (hg : g ∈ centralizer D.concatStabGroup) :
    inducedOuter D g ∈ centralizer D.Cout.toStabilizerGroup := by
  apply CentralizerLemmas.mem_centralizer_of_commutes_list _ _ D.Cout.generatorsList rfl
  intro y hy
  have hymem : y ∈ D.outerZ ++ D.outerX := D.outer_split.mem_iff.mp hy
  have hyY : ∀ b, y.operators b ≠ PauliOperator.Y := D.outer_gen_noY y hymem
  have hprommem : promoteE D.Xbar D.Zbar y ∈ D.concatStabGroup.toSubgroup :=
    Subgroup.subset_closure (D.promoteE_mem_concatGeneratorsList y hymem)
  have hcommg : g * promoteE D.Xbar D.Zbar y = promoteE D.Xbar D.Zbar y * g :=
    ((mem_centralizer_iff g D.concatStabGroup).mp hg (promoteE D.Xbar D.Zbar y) hprommem).symm
  exact ((D.induced_commute_iff g y hyY).mpr hcommg).symm

/-! ## Support of the induced operator: nontrivial-block characterisation (uses M4) -/

/-- For Pauli group elements, commuting precludes anticommuting. -/
lemma commute_not_anticommute {m : ℕ} {p q : NQubitPauliGroupElement m}
    (h : p * q = q * p) : ¬ Anticommute p q := by
  intro hanti
  rw [Anticommute, h] at hanti
  exact one_ne_minusOne (mul_right_cancel (b := q * p) (by rw [one_mul]; exact hanti))

/-- **(Uses M4.)** A block restriction commutes with both inner logicals iff its operator part
is realised by an inner stabilizer. Forward is M4's decisive kernel; backward is operator-part
commutation (the restriction and the matching stabilizer share an operator part, and the
logicals centralise the stabilizer). -/
lemma restrict_commutes_both_iff_stab (g : NQubitPauliGroupElement (n₁ * n₂))
    (hg : g ∈ centralizer D.concatStabGroup)
    (hindep : rowsLinearIndependent D.Cin.generatorsList) (b : Fin n₂) :
    (¬ Anticommute (restrictBlock b g) (D.Cin.logicalZ 0)
      ∧ ¬ Anticommute (restrictBlock b g) (D.Cin.logicalX 0))
    ↔ ∃ s ∈ D.Cin.toStabilizerGroup.toSubgroup, s.operators = (restrictBlock b g).operators := by
  constructor
  · rintro ⟨hZ, hX⟩
    have hcomm_x : restrictBlock b g * D.Cin.logicalX 0
        = D.Cin.logicalX 0 * restrictBlock b g :=
      (commute_or_anticommute _ _).resolve_right hX
    have hcomm_z : restrictBlock b g * D.Cin.logicalZ 0
        = D.Cin.logicalZ 0 * restrictBlock b g :=
      (commute_or_anticommute _ _).resolve_right hZ
    exact operators_eq_stab_of_commutes_both_logicals D.Cin hindep (restrictBlock b g)
      (D.restrictBlock_mem_centralizer g hg b) hcomm_x hcomm_z
  · rintro ⟨s, hs, hsop⟩
    refine ⟨commute_not_anticommute ?_, commute_not_anticommute ?_⟩
    · rw [commutes_iff_even_anticommutes, ← hsop, ← commutes_iff_even_anticommutes]
      exact (mem_centralizer_iff (D.Cin.logicalZ 0) D.Cin.toStabilizerGroup).mp
        (D.Cin.logicalOps 0).z_mem_centralizer s hs
    · rw [commutes_iff_even_anticommutes, ← hsop, ← commutes_iff_even_anticommutes]
      exact (mem_centralizer_iff (D.Cin.logicalX 0) D.Cin.toStabilizerGroup).mp
        (D.Cin.logicalOps 0).x_mem_centralizer s hs

/-- **(M5.)** Block `b` is in the support of the induced outer operator exactly when the
block restriction `restrictBlock b g` is a *nontrivial* inner logical. This is what turns the
per-block weight bound (`weight_ge_of_blocks_ge`) into a count of nontrivial blocks. Uses M4
(`centralizer_classify_of_k1` and the decisive kernel via `restrict_commutes_both_iff_stab`). -/
theorem inducedOuter_support_eq (g : NQubitPauliGroupElement (n₁ * n₂))
    (hg : g ∈ centralizer D.concatStabGroup)
    (hindep : rowsLinearIndependent D.Cin.generatorsList) (b : Fin n₂) :
    b ∈ (inducedOuter D g).support
      ↔ IsNontrivialLogicalOperator (restrictBlock b g) D.Cin.toStabilizerGroup := by
  rw [NQubitPauliGroupElement.mem_support, inducedOuter_operators, ne_eq,
    D.inducedOuterOp_eq_I_iff g b, D.restrict_commutes_both_iff_stab g hg hindep b]
  constructor
  · intro hns
    rcases centralizer_classify_of_k1 D.Cin (restrictBlock b g)
      (D.restrictBlock_mem_centralizer g hg b) with hstab | hnt
    · exact absurd hstab hns
    · exact hnt
  · intro hnt
    rintro ⟨s, hs, hsop⟩
    exact ((IsNontrivialLogicalOperator_iff _ _).mp hnt).2.2 s hs hsop

/-! ## Coset injectivity (plan risk R7)

The nontriviality of `inducedOuter D g` rests on the symplectic fact `inducedOuter_symp_in_span`
below: if some outer stabilizer `t` matches the operator part of `inducedOuter D g`, then `g`'s
symplectic vector already lies in the span of the concatenated check matrix — i.e. `g` is
concatenated-stabilizer-like. Contrapositively, a *nontrivial* concatenated logical `g` cannot
have a stabilizer-like induced operator, so `inducedOuter D g` is itself a nontrivial outer
logical.

`inducedOuter_symp_in_span` is now fully assembled from the symplectic gluing lemma
(`toSymplectic_eq_sum_embed_restrictBlock`), the embed-preserves-span lemma
(`toSymplectic_embedBlock_mem_concatSpan`), and the M4 kernel; the *only* remaining `sorry` is
the class-matching concatenated stabilizer `exists_concatStab_matching_induced`. -/

open NQubitPauliOperator in
/-- `symplecticInner` is additive in the left argument under the group product (it depends only
on the operator part, whose symplectic vector adds, and the form is bilinear). -/
lemma symplecticInner_group_mul_left {m : ℕ} (p q L : NQubitPauliGroupElement m) :
    ⟪(p * q), L⟫ₛ
      = ⟪p, L⟫ₛ + ⟪q, L⟫ₛ := by
  rw [← symplecticBilinear_toSymplectic, ← symplecticBilinear_toSymplectic,
    ← symplecticBilinear_toSymplectic,
    show toSymplectic (p * q).operators
        = toSymplectic p.operators + toSymplectic q.operators from by
      funext j; exact toSymplectic_mul p q j,
    symplecticBilinear_add_left]

open NQubitPauliOperator in
/-- The identity commutes with everything, so its symplectic inner product is zero. -/
lemma symplecticInner_one_left {m : ℕ} (L : NQubitPauliGroupElement m) :
    ⟪(1 : NQubitPauliGroupElement m), L⟫ₛ = 0 :=
  (commutes_iff_symplectic_inner_zero 1 L).mp (by rw [one_mul, mul_one])

open NQubitPauliOperator in
/-- `symplecticInner` of the identity operator (left) is zero. -/
lemma symplecticInner_identity_left {m : ℕ} (L : NQubitPauliGroupElement m) :
    symplecticInner (NQubitPauliOperator.identity m) L.operators = 0 :=
  symplecticInner_one_left L

omit [NeZero n₁] in
open NQubitPauliOperator in
/-- Additivity of the block-restricted symplectic inner product: the restriction of a product
multiplies block-wise, so its symplectic inner product against `L` is additive. -/
lemma symplecticInner_restrictBlock_mul (b : Fin n₂) (x y : NQubitPauliGroupElement (n₁ * n₂))
    (L : NQubitPauliGroupElement n₁) :
    ⟪restrictBlock b (x * y), L⟫ₛ
      = ⟪restrictBlock b x, L⟫ₛ
        + ⟪restrictBlock b y, L⟫ₛ := by
  rw [show (restrictBlock b (x * y)).operators
      = (restrictBlock b x * restrictBlock b y).operators from by funext i; rfl]
  exact symplecticInner_group_mul_left (restrictBlock b x) (restrictBlock b y) L

open NQubitPauliOperator in
/-- The induced class Pauli at block `b`, read off symplectically: its `(x,z)` bits are the
symplectic inner products of the restriction with `Z̄₁` and `X̄₁`. -/
lemma inducedOuterOp_toSymplecticSingle (D : ConcatCSSData n₁ n₂ k₂)
    (x : NQubitPauliGroupElement (n₁ * n₂)) (b : Fin n₂) :
    (inducedOuterOp D x b).toSymplecticSingle
      = (⟪restrictBlock b x, (D.Cin.logicalZ 0)⟫ₛ,
         ⟪restrictBlock b x, (D.Cin.logicalX 0)⟫ₛ) := by
  classical
  have hz : ⟪restrictBlock b x, (D.Cin.logicalZ 0)⟫ₛ
      = if Anticommute (restrictBlock b x) (D.Cin.logicalZ 0) then (1 : ZMod 2) else 0 := by
    split_ifs with h
    · exact (anticommutes_iff_symplectic_inner_one _ _).mp h
    · exact (commutes_iff_symplectic_inner_zero _ _).mp
        ((commute_or_anticommute _ _).resolve_right h)
  have hx : ⟪restrictBlock b x, (D.Cin.logicalX 0)⟫ₛ
      = if Anticommute (restrictBlock b x) (D.Cin.logicalX 0) then (1 : ZMod 2) else 0 := by
    split_ifs with h
    · exact (anticommutes_iff_symplectic_inner_one _ _).mp h
    · exact (commutes_iff_symplectic_inner_zero _ _).mp
        ((commute_or_anticommute _ _).resolve_right h)
  rw [hz, hx]
  unfold inducedOuterOp
  split_ifs <;> rfl

open NQubitPauliOperator in
/-- **(M5, R7 sub-pole.)** The class-matching concatenated stabilizer: given an outer
stabilizer `t` matching the operator part of `inducedOuter D g`, there is a concatenated
stabilizer `u` such that `g * u` restricts, on every block, to an operator commuting with *both*
inner logicals (i.e. inner-stabilizer-like).

`u` is the concat-group product of promoted outer generators in a decomposition of `t`. The
concat-group multiplication — unlike `promoteE t`, which is lossy on `Y` (`promoteSingle Y = I`)
— correctly realizes the `Y = X̄₁Z̄₁` class on `Y`-blocks. The construction is a
`Subgroup.closure_induction` on `t ∈ Cout.stab` carrying the per-block class-match invariant
`inducedOuterOp D u = t.operators` (base: `promoteE` of a `Y`-free outer generator, where the
class equals the generator's Pauli; multiplicative step: the inner-logical class is additive
under multiplication). Since `t.operators = inducedOuterOp D g` and the classes match, each
`restrictBlock b (g * u)` has trivial class and so commutes with both inner logicals. This is
the entirety of the remaining M5 work. -/
lemma exists_concatStab_matching_induced (g : NQubitPauliGroupElement (n₁ * n₂))
    (t : NQubitPauliGroupElement n₂) (ht : t ∈ D.Cout.toStabilizerGroup.toSubgroup)
    (htop : t.operators = (inducedOuter D g).operators) :
    ∃ u ∈ D.concatStabGroup.toSubgroup, ∀ b : Fin n₂,
      restrictBlock b (g * u) * D.Cin.logicalX 0
          = D.Cin.logicalX 0 * restrictBlock b (g * u)
        ∧ restrictBlock b (g * u) * D.Cin.logicalZ 0
          = D.Cin.logicalZ 0 * restrictBlock b (g * u) := by
  classical
  -- Symplectic-inner values of the inner logical pair.
  have hXZ : ⟪(D.Cin.logicalX 0), (D.Cin.logicalZ 0)⟫ₛ
      = 1 := (anticommutes_iff_symplectic_inner_one _ _).mp (D.Cin.logicalOps 0).anticommute
  have hZX : ⟪(D.Cin.logicalZ 0), (D.Cin.logicalX 0)⟫ₛ
      = 1 := (anticommutes_iff_symplectic_inner_one _ _).mp
        (NQubitPauliGroupElement.anticommute_symm _ _ (D.Cin.logicalOps 0).anticommute)
  have hXX : ⟪(D.Cin.logicalX 0), (D.Cin.logicalX 0)⟫ₛ
      = 0 := (commutes_iff_symplectic_inner_zero _ _).mp rfl
  have hZZ : ⟪(D.Cin.logicalZ 0), (D.Cin.logicalZ 0)⟫ₛ
      = 0 := (commutes_iff_symplectic_inner_zero _ _).mp rfl
  -- Step 1: build a class-matching concatenated stabilizer `u` with `inducedOuterOp u = t`.
  have ht' : t ∈ Subgroup.closure (NQubitPauliGroupElement.listToSet D.Cout.generatorsList) := ht
  obtain ⟨u, hu_mem, hu_sig⟩ : ∃ u ∈ D.concatStabGroup.toSubgroup, ∀ b : Fin n₂,
      ((⟪restrictBlock b u, (D.Cin.logicalZ 0)⟫ₛ,
        ⟪restrictBlock b u, (D.Cin.logicalX 0)⟫ₛ)
        : ZMod 2 × ZMod 2) = (t.operators b).toSymplecticSingle := by
    refine Subgroup.closure_induction
      (p := fun t _ => ∃ u ∈ D.concatStabGroup.toSubgroup, ∀ b : Fin n₂,
        ((⟪restrictBlock b u, (D.Cin.logicalZ 0)⟫ₛ,
          ⟪restrictBlock b u, (D.Cin.logicalX 0)⟫ₛ)
          : ZMod 2 × ZMod 2) = (t.operators b).toSymplecticSingle)
      ?_ ?_ ?_ ?_ ht'
    · -- mem: a `Y`-free outer generator `y` promotes to a matching concat generator.
      intro y hy
      have hymem : y ∈ D.outerZ ++ D.outerX := D.outer_split.mem_iff.mp hy
      refine ⟨promoteE D.Xbar D.Zbar y,
        Subgroup.subset_closure (D.promoteE_mem_concatGeneratorsList y hymem), fun b => ?_⟩
      have hrp : (restrictBlock b (promoteE D.Xbar D.Zbar y)).operators
          = promoteSingle D.Xbar D.Zbar (y.operators b) := by
        funext i
        change (promoteE D.Xbar D.Zbar y).operators (qIdx b i)
          = promoteSingle D.Xbar D.Zbar (y.operators b) i
        simp only [promoteE_operators, promoteOp, blockOf_qIdx, posOf_qIdx]
      have hyY : y.operators b ≠ PauliOperator.Y := D.outer_gen_noY y hymem b
      rw [hrp]
      rcases hb : y.operators b with _ | _ | _ | _
      · simp only [promoteSingle, PauliOperator.toSymplecticSingle_I, Prod.mk.injEq]
        exact ⟨symplecticInner_identity_left _, symplecticInner_identity_left _⟩
      · simp only [promoteSingle, ConcatCSSData.Xbar, PauliOperator.toSymplecticSingle_X,
          Prod.mk.injEq]
        exact ⟨hXZ, hXX⟩
      · exact absurd hb hyY
      · simp only [promoteSingle, ConcatCSSData.Zbar, PauliOperator.toSymplecticSingle_Z,
          Prod.mk.injEq]
        exact ⟨hZZ, hZX⟩
    · -- one
      refine ⟨1, Subgroup.one_mem _, fun b => ?_⟩
      have hr1 : (restrictBlock b (1 : NQubitPauliGroupElement (n₁ * n₂))).operators
          = (1 : NQubitPauliGroupElement n₁).operators := by
        funext i
        simp [restrictBlockOp, NQubitPauliOperator.identity]
      rw [hr1, symplecticInner_one_left, symplecticInner_one_left]
      simp [NQubitPauliOperator.identity]
    · -- mul
      intro a a' _ _ iha iha'
      obtain ⟨u₁, hu₁, hsig₁⟩ := iha
      obtain ⟨u₂, hu₂, hsig₂⟩ := iha'
      refine ⟨u₁ * u₂, Subgroup.mul_mem _ hu₁ hu₂, fun b => ?_⟩
      have e1 : ⟪restrictBlock b u₁, (D.Cin.logicalZ 0)⟫ₛ
          = ((a.operators b).toSymplecticSingle).1 := congrArg Prod.fst (hsig₁ b)
      have e2 : ⟪restrictBlock b u₁, (D.Cin.logicalX 0)⟫ₛ
          = ((a.operators b).toSymplecticSingle).2 := congrArg Prod.snd (hsig₁ b)
      have e3 : ⟪restrictBlock b u₂, (D.Cin.logicalZ 0)⟫ₛ
          = ((a'.operators b).toSymplecticSingle).1 := congrArg Prod.fst (hsig₂ b)
      have e4 : ⟪restrictBlock b u₂, (D.Cin.logicalX 0)⟫ₛ
          = ((a'.operators b).toSymplecticSingle).2 := congrArg Prod.snd (hsig₂ b)
      rw [symplecticInner_restrictBlock_mul, symplecticInner_restrictBlock_mul,
        show (a * a').operators b
            = ((a.operators b).mulOp (a'.operators b)).operator from rfl,
        PauliOperator.toSymplecticSingle_add, Prod.mk.injEq]
      exact ⟨by rw [e1, e3], by rw [e2, e4]⟩
    · -- inv
      intro a _ iha
      obtain ⟨u₁, hu₁, hsig₁⟩ := iha
      refine ⟨u₁⁻¹, Subgroup.inv_mem _ hu₁, fun b => ?_⟩
      rw [show (restrictBlock b u₁⁻¹).operators = (restrictBlock b u₁).operators from rfl,
        show (a⁻¹).operators b = a.operators b from rfl]
      exact hsig₁ b
  -- Step 2: `inducedOuterOp u = inducedOuterOp g`, so `g * u` restricts to commuting elements.
  refine ⟨u, hu_mem, fun b => ?_⟩
  have hsig_g : (t.operators b).toSymplecticSingle
      = (⟪restrictBlock b g, (D.Cin.logicalZ 0)⟫ₛ,
         ⟪restrictBlock b g, (D.Cin.logicalX 0)⟫ₛ) := by
    rw [htop, inducedOuter_operators]
    exact D.inducedOuterOp_toSymplecticSingle g b
  have hpair := (hu_sig b).trans hsig_g
  have hzg : ⟪restrictBlock b u, (D.Cin.logicalZ 0)⟫ₛ
      = ⟪restrictBlock b g, (D.Cin.logicalZ 0)⟫ₛ :=
    congrArg Prod.fst hpair
  have hxg : ⟪restrictBlock b u, (D.Cin.logicalX 0)⟫ₛ
      = ⟪restrictBlock b g, (D.Cin.logicalX 0)⟫ₛ :=
    congrArg Prod.snd hpair
  refine ⟨?_, ?_⟩
  · refine (commutes_iff_symplectic_inner_zero _ _).mpr ?_
    rw [symplecticInner_restrictBlock_mul, hxg, CharTwo.add_self_eq_zero]
  · refine (commutes_iff_symplectic_inner_zero _ _).mpr ?_
    rw [symplecticInner_restrictBlock_mul, hzg, CharTwo.add_self_eq_zero]

open NQubitPauliOperator in
/-- **(M5.)** Coset injectivity, symplectic form: if an outer stabilizer `t` matches the
operator part of `inducedOuter D g`, then `toSymplectic g.operators` lies in the concatenated
row span (so `g` is concatenated-stabilizer-like).

Assembled from `exists_concatStab_matching_induced` (the class-matching stabilizer `u`), the
gluing lemma, the embed-preserves-span lemma, and the M4 kernel: `g * u` restricts per block to
an inner-stabilizer-like operator, so (gluing + embed-span) `toSymplectic (g * u) ∈ sympSpan`;
`toSymplectic u ∈ sympSpan` since `u` is a concatenated stabilizer; and over `ZMod 2`
`toSymplectic g = toSymplectic (g * u) + toSymplectic u`. -/
lemma inducedOuter_symp_in_span (g : NQubitPauliGroupElement (n₁ * n₂))
    (hg : g ∈ centralizer D.concatStabGroup)
    (hindep : rowsLinearIndependent D.Cin.generatorsList)
    (t : NQubitPauliGroupElement n₂) (ht : t ∈ D.Cout.toStabilizerGroup.toSubgroup)
    (htop : t.operators = (inducedOuter D g).operators) :
    toSymplectic g.operators ∈ sympSpan D.concatGeneratorsList := by
  obtain ⟨u, hu_mem, hu_comm⟩ := D.exists_concatStab_matching_induced g t ht htop
  have hgu_cent : g * u ∈ centralizer D.concatStabGroup :=
    Subgroup.mul_mem _ hg (stabilizer_le_centralizer _ hu_mem)
  have hgu_span : toSymplectic (g * u).operators ∈ sympSpan D.concatGeneratorsList := by
    rw [toSymplectic_eq_sum_embed_restrictBlock (g * u)]
    refine Submodule.sum_mem _ (fun b _ => ?_)
    refine D.toSymplectic_embedBlock_mem_concatSpan b (restrictBlock b (g * u)) ?_
    obtain ⟨s, hs_mem, hs_op⟩ := operators_eq_stab_of_commutes_both_logicals D.Cin hindep
      (restrictBlock b (g * u)) (D.restrictBlock_mem_centralizer (g * u) hgu_cent b)
      (hu_comm b).1 (hu_comm b).2
    rw [← hs_op]
    exact mem_closure_implies_symp_in_span D.Cin.generatorsList D.Cin.generators_phaseZero s hs_mem
  have hu_span : toSymplectic u.operators ∈ sympSpan D.concatGeneratorsList :=
    mem_closure_implies_symp_in_span D.concatGeneratorsList
      D.concatGeneratorsList_phaseZero u hu_mem
  have hsum : toSymplectic g.operators
      = toSymplectic (g * u).operators + toSymplectic u.operators := by
    funext j
    rw [Pi.add_apply, toSymplectic_mul g u j, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [hsum]
  exact Submodule.add_mem _ hgu_span hu_span

/-- Coset injectivity: an outer stabilizer matching `inducedOuter D g`'s operator part forces
`g` to be concatenated-stabilizer-like. -/
lemma inducedOuter_coset_injective (g : NQubitPauliGroupElement (n₁ * n₂))
    (hg : g ∈ centralizer D.concatStabGroup)
    (hindep : rowsLinearIndependent D.Cin.generatorsList)
    (t : NQubitPauliGroupElement n₂) (ht : t ∈ D.Cout.toStabilizerGroup.toSubgroup)
    (htop : t.operators = (inducedOuter D g).operators) :
    ∃ S ∈ D.concatStabGroup.toSubgroup, S.operators = g.operators :=
  exists_mem_closure_of_symp_in_span D.concatGeneratorsList g.operators
    (D.inducedOuter_symp_in_span g hg hindep t ht htop)

/-- **(M5.)** The induced outer operator of a *nontrivial* concatenated logical is not an
outer stabilizer (else `g` would be concatenated-stabilizer-like, contradicting nontriviality).
-/
theorem inducedOuter_not_mem_stabilizer (g : NQubitPauliGroupElement (n₁ * n₂))
    (hg : IsNontrivialLogicalOperator g D.concatStabGroup)
    (hindep : rowsLinearIndependent D.Cin.generatorsList) :
    inducedOuter D g ∉ D.Cout.toStabilizerGroup.toSubgroup := by
  intro hmem
  obtain ⟨S, hS, hSop⟩ :=
    D.inducedOuter_coset_injective g hg.1 hindep (inducedOuter D g) hmem rfl
  exact ((IsNontrivialLogicalOperator_iff _ _).mp hg).2.2 S hS hSop

/-- **(M5, headline correspondence.)** The induced outer operator of a nontrivial concatenated
logical is a nontrivial outer logical: it centralizes the outer stabilizer
(`inducedOuter_mem_centralizer`) and its coset is nontrivial (coset injectivity, both the
not-in-stabilizer and the distinct-operator-part clauses). This is the bridge that, with
`inducedOuter_support_eq` and `weight_eq_sum_restrictBlock`, yields the M6 distance bound. -/
theorem inducedOuter_isNontrivialLogical (g : NQubitPauliGroupElement (n₁ * n₂))
    (hg : IsNontrivialLogicalOperator g D.concatStabGroup)
    (hindep : rowsLinearIndependent D.Cin.generatorsList) :
    IsNontrivialLogicalOperator (inducedOuter D g) D.Cout.toStabilizerGroup := by
  refine (IsNontrivialLogicalOperator_iff _ _).mpr
    ⟨D.inducedOuter_mem_centralizer g hg.1, D.inducedOuter_not_mem_stabilizer g hg hindep, ?_⟩
  intro t ht htop
  obtain ⟨S, hS, hSop⟩ := D.inducedOuter_coset_injective g hg.1 hindep t ht htop
  exact ((IsNontrivialLogicalOperator_iff _ _).mp hg).2.2 S hS hSop

end ConcatCSSData

end Quantum.Concatenation
