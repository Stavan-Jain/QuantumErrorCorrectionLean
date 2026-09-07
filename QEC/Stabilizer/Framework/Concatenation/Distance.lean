import QEC.Stabilizer.Framework.Concatenation.Correspondence
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance

/-!
# Concatenation, Tier 2b: the distance lower bound (Milestone M6)

Milestone **M6** of the CSS concatenation plan
(`qec-lab:pipeline/attempts/concat_css_general/plan.md`) — the headline distance
result.

The structural core is `weight_ge_d1_mul_d2`: every nontrivial logical of the
concatenated code has weight at least `d₁ · d₂`. The argument assembles the M5
correspondence:

* each block restriction of a nontrivial logical is either inner-stabilizer-like
  or a *nontrivial inner logical* (the latter contributing weight ≥ `d₁`);
* the nontrivial blocks are exactly the support of `inducedOuter`, which is a
  *nontrivial outer logical* (so ≥ `d₂` of them);
* weight superadditivity over the disjoint blocks (`weight_ge_of_blocks_ge`,
  M1).

`concat_hasCodeDistance` packages this into
`HasCodeDistance (concatenate D) (d₁·d₂)`. The exact-distance *witness* (a
nontrivial logical of weight exactly `d₁·d₂`) genuinely depends on
minimum-weight logical representatives, which the abstract `ConcatCSSData` does
not pin down, so it is an explicit hypothesis here and is exhibited concretely
in the Steane⊗Steane instance (M7).
-/

namespace Quantum.Concatenation

open NQubitPauliGroupElement StabilizerGroup

variable {n₁ n₂ k₂ : ℕ} [NeZero n₁]

/-- A nontrivial logical operator has positive weight: weight 0 means operator
part `I`, which the identity stabilizer already realizes (contradicting the
distinct-operator clause). -/
lemma weight_pos_of_nontrivial {m : ℕ} {S : StabilizerGroup m} {g : NQubitPauliGroupElement m}
    (hg : IsNontrivialLogicalOperator g S) : 0 < weight g := by
  rcases Nat.eq_zero_or_pos (weight g) with h0 | h0
  · exact absurd ((NQubitPauliGroupElement.one_operators_def m).trans
      ((NQubitPauliGroupElement.weight_eq_zero_iff g).mp h0).symm)
      (((IsNontrivialLogicalOperator_iff g S).mp hg).2.2 1 S.one_mem)
  · exact h0

/-- The number of support qubits of `g` lying in block `b` equals the weight of
the block restriction (the `qIdx b`-image bijection of
`image_qIdx_support_restrictBlock`). -/
lemma card_block_filter_eq_restrictBlock_weight (b : Fin n₂)
    (g : NQubitPauliGroupElement (n₁ * n₂)) :
    (g.support.filter (fun q => blockOf q = b)).card = weight (restrictBlock b g) := by
  rw [← image_qIdx_support_restrictBlock b g,
    Finset.card_image_of_injective _ (fun i i' h => (qIdx_injective h).2)]
  rfl

namespace ConcatCSSData

variable (D : ConcatCSSData n₁ n₂ k₂)

/-- **(M6, the structural distance bound.)** Every nontrivial logical of the
concatenated code has weight at least `d₁ · d₂`. Assembled entirely from the M5
correspondence: `inducedOuter_support_eq` (nontrivial blocks = support of
`inducedOuter`), `inducedOuter_isNontrivialLogical` (so `≥ d₂` of them),
`HasCodeDistance.min_weight` on both codes, and `weight_ge_of_blocks_ge` (M1).
-/
theorem weight_ge_d1_mul_d2 (hindep : rowsLinearIndependent D.Cin.generatorsList)
    {d₁ d₂ : ℕ} (h1 : HasCodeDistance D.Cin d₁) (h2 : HasCodeDistance D.Cout d₂)
    (g : NQubitPauliGroupElement (n₁ * n₂))
    (hg : IsNontrivialLogicalOperator g D.concatStabGroup) (_hw : 0 < weight g) :
    d₁ * d₂ ≤ weight g := by
  classical
  have hgc : g ∈ centralizer D.concatStabGroup := hg.1
  -- Each nontrivial block contributes at least `d₁` to the weight.
  have hblock : ∀ b ∈ (inducedOuter D g).support,
      d₁ ≤ (g.support.filter (fun q => blockOf q = b)).card := by
    intro b hbB
    have hnt : IsNontrivialLogicalOperator (restrictBlock b g) D.Cin.toStabilizerGroup :=
      (D.inducedOuter_support_eq g hgc hindep b).mp hbB
    rw [card_block_filter_eq_restrictBlock_weight]
    exact HasCodeDistance.min_weight D.Cin d₁ h1 _ hnt (weight_pos_of_nontrivial hnt)
  have hwt : d₁ * (inducedOuter D g).support.card ≤ weight g :=
    weight_ge_of_blocks_ge d₁ g (inducedOuter D g).support hblock
  -- The induced outer operator is a nontrivial outer logical: ≥ `d₂` nontrivial blocks.
  have hntO : IsNontrivialLogicalOperator (inducedOuter D g) D.Cout.toStabilizerGroup :=
    D.inducedOuter_isNontrivialLogical g hg hindep
  have hd2 : d₂ ≤ (inducedOuter D g).support.card :=
    HasCodeDistance.min_weight D.Cout d₂ h2 _ hntO (weight_pos_of_nontrivial hntO)
  calc d₁ * d₂ ≤ d₁ * (inducedOuter D g).support.card := Nat.mul_le_mul le_rfl hd2
    _ ≤ weight g := hwt

/-- **(M6, headline.)** The concatenated code has distance `d₁ · d₂`: the lower
bound is `weight_ge_d1_mul_d2`, and a weight-`d₁·d₂` nontrivial logical witness
(which depends on the codes' minimum-weight representatives) is supplied as
`hwit` — discharged concretely for Steane⊗Steane in M7. -/
theorem concat_hasCodeDistance
    (hindep : GeneratorsIndependent (n₁ * n₂) D.concatGeneratorsList)
    (hindepCin : rowsLinearIndependent D.Cin.generatorsList)
    {d₁ d₂ : ℕ} (h1 : HasCodeDistance D.Cin d₁) (h2 : HasCodeDistance D.Cout d₂)
    (hwit : ∃ g, IsNontrivialLogicalOperator g D.concatStabGroup ∧ weight g = d₁ * d₂) :
    HasCodeDistance (D.concatenate hindep) (d₁ * d₂) := by
  refine ⟨Nat.mul_pos h1.1 h2.1, ?_, hwit⟩
  intro g hg hw
  exact D.weight_ge_d1_mul_d2 hindepCin h1 h2 g hg hw

/-- **(M6, packaged.)** The concatenated code as a `StabilizerCodeWithDistance`
— one object carrying all three `[[n₁ n₂, k₂, d₁ d₂]]` parameters in its type,
combining `concatenate` with `concat_hasCodeDistance`. With this, any
inner⊗outer instance becomes a first-class `[[n, k, d]]` code once its five
inputs (independence, inner-row independence, inner/outer distances, and a
`d₁·d₂`-weight witness) are discharged. -/
noncomputable def concatenateWithDistance
    (hindep : GeneratorsIndependent (n₁ * n₂) D.concatGeneratorsList)
    (hindepCin : rowsLinearIndependent D.Cin.generatorsList)
    {d₁ d₂ : ℕ} (h1 : HasCodeDistance D.Cin d₁) (h2 : HasCodeDistance D.Cout d₂)
    (hwit : ∃ g, IsNontrivialLogicalOperator g D.concatStabGroup ∧ weight g = d₁ * d₂) :
    StabilizerCodeWithDistance (n₁ * n₂) k₂ (d₁ * d₂) where
  toStabilizerCode := D.concatenate hindep
  hasDistance := D.concat_hasCodeDistance hindep hindepCin h1 h2 hwit

end ConcatCSSData

end Quantum.Concatenation
