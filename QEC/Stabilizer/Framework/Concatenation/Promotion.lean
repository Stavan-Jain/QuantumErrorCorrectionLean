import QEC.Stabilizer.Framework.Concatenation.Embedding
import QEC.Stabilizer.Framework.Core
import QEC.Stabilizer.Framework.Symplectic

/-!
# Concatenation, Tier 1a: promotion map, `ConcatCSSData`, generator list

Milestone **M2** of the CSS concatenation plan
(`qec-lab:pipeline/attempts/concat_css_general/plan.md`).

Promotes each single-qubit Pauli of an *outer* generator to the corresponding
inner logical operator on its block: `I ↦ I`, `X ↦ X̄₁`, `Z ↦ Z̄₁` (CSS, so the
`Y ↦ I` branch of `promoteSingle` is unreachable for CSS-typed inputs — see
`promoteE_isX/isZ`). The concatenated generator list is the inner stabilizers
replicated per block, followed by the promoted (typed) outer stabilizers.

Unlike `Embedding` (Foundations-only), this module sits at the
`Framework.Symplectic` tier: it needs `StabilizerCode`, the CSS typing
predicates, and `AllPhaseZero`.
-/

namespace Quantum.Concatenation

open NQubitPauliGroupElement StabilizerGroup

variable {n₁ n₂ k₂ : ℕ} [NeZero n₁]

/-! ## The promotion map -/

/-- Promote a single outer-qubit Pauli to the matching inner logical operator.
The `Y` branch is a CSS dead end (never reached for CSS-typed generators). -/
def promoteSingle (Xbar Zbar : NQubitPauliOperator n₁) : PauliOperator → NQubitPauliOperator n₁
  | PauliOperator.I => NQubitPauliOperator.identity n₁
  | PauliOperator.X => Xbar
  | PauliOperator.Z => Zbar
  | PauliOperator.Y => NQubitPauliOperator.identity n₁

/-- Promote an outer operator to `Fin (n₁ * n₂)`: block `b` carries
`promoteSingle (h b)`, evaluated at the in-block position. -/
def promoteOp (Xbar Zbar : NQubitPauliOperator n₁) (h : NQubitPauliOperator n₂) :
    NQubitPauliOperator (n₁ * n₂) :=
  fun q => promoteSingle Xbar Zbar (h (blockOf q)) (posOf q)

/-- Group-element promotion (phase 0, per the zero-phase convention). -/
def promoteE (Xbar Zbar : NQubitPauliOperator n₁) (h : NQubitPauliGroupElement n₂) :
    NQubitPauliGroupElement (n₁ * n₂) :=
  ofOperator (promoteOp Xbar Zbar h.operators)

@[simp] lemma promoteE_phasePower (Xbar Zbar : NQubitPauliOperator n₁)
    (h : NQubitPauliGroupElement n₂) : (promoteE Xbar Zbar h).phasePower = 0 := rfl

@[simp] lemma promoteE_operators (Xbar Zbar : NQubitPauliOperator n₁)
    (h : NQubitPauliGroupElement n₂) :
    (promoteE Xbar Zbar h).operators = promoteOp Xbar Zbar h.operators := rfl

/-- A Z-type outer operator promotes (with a Z-type `Z̄`) to a Z-type element. -/
lemma promoteE_isZ {Xbar Zbar : NQubitPauliOperator n₁} (hZbar : NQubitPauliOperator.IsZType Zbar)
    {h : NQubitPauliGroupElement n₂} (hh : NQubitPauliOperator.IsZType h.operators) :
    IsZTypeElement (promoteE Xbar Zbar h) := by
  refine ⟨rfl, fun q => ?_⟩
  simp only [promoteE_operators, promoteOp]
  rcases hh (blockOf q) with hI | hZ
  · rw [hI]; exact Or.inl rfl
  · rw [hZ]; exact hZbar (posOf q)

/-- An X-type outer operator promotes (with an X-type `X̄`) to an X-type element. -/
lemma promoteE_isX {Xbar Zbar : NQubitPauliOperator n₁} (hXbar : NQubitPauliOperator.IsXType Xbar)
    {h : NQubitPauliGroupElement n₂} (hh : NQubitPauliOperator.IsXType h.operators) :
    IsXTypeElement (promoteE Xbar Zbar h) := by
  refine ⟨rfl, fun q => ?_⟩
  simp only [promoteE_operators, promoteOp]
  rcases hh (blockOf q) with hI | hX
  · rw [hI]; exact Or.inl rfl
  · rw [hX]; exact hXbar (posOf q)

/-- Embedding a Z-type element into a block yields a Z-type element (the off-block
positions are `I`, which is Z-type). -/
lemma embedBlock_isZ (b : Fin n₂) {g : NQubitPauliGroupElement n₁}
    (hg : IsZTypeElement g) : IsZTypeElement (embedBlock b g) := by
  refine ⟨rfl, fun q => ?_⟩
  simp only [embedBlock_operators, embedBlockOp]
  by_cases hbq : blockOf q = b
  · rw [if_pos hbq]; exact hg.2 (posOf q)
  · rw [if_neg hbq]; exact Or.inl rfl

/-- Embedding an X-type element into a block yields an X-type element. -/
lemma embedBlock_isX (b : Fin n₂) {g : NQubitPauliGroupElement n₁}
    (hg : IsXTypeElement g) : IsXTypeElement (embedBlock b g) := by
  refine ⟨rfl, fun q => ?_⟩
  simp only [embedBlock_operators, embedBlockOp]
  by_cases hbq : blockOf q = b
  · rw [if_pos hbq]; exact hg.2 (posOf q)
  · rw [if_neg hbq]; exact Or.inl rfl

/-- An X-type operator tensor has no `Y` component (feeds the `no-Y` hypotheses of
`promote_anticommute_parity`). -/
lemma noY_of_isXType {n : ℕ} {op : NQubitPauliOperator n}
    (h : NQubitPauliOperator.IsXType op) (i : Fin n) : op i ≠ PauliOperator.Y := by
  rcases h i with hi | hi <;> rw [hi] <;> decide

/-- A Z-type operator tensor has no `Y` component. -/
lemma noY_of_isZType {n : ℕ} {op : NQubitPauliOperator n}
    (h : NQubitPauliOperator.IsZType op) (i : Fin n) : op i ≠ PauliOperator.Y := by
  rcases h i with hi | hi <;> rw [hi] <;> decide

/-! ## The concatenated-code data bundle -/

/-- Input data for concatenating a `k₁ = 1` CSS inner code with a CSS outer code.
Carries the typed (Z/X) splits of both generator lists and the CSS-typed,
phase-0 inner logical representatives `X̄₁ = (Cin.logicalX 0)`,
`Z̄₁ = (Cin.logicalZ 0)`. -/
structure ConcatCSSData (n₁ n₂ k₂ : ℕ) [NeZero n₁] where
  Cin : StabilizerCode n₁ 1
  Cout : StabilizerCode n₂ k₂
  innerZ : List (NQubitPauliGroupElement n₁)
  innerX : List (NQubitPauliGroupElement n₁)
  inner_split : List.Perm Cin.generatorsList (innerZ ++ innerX)
  innerZ_isZ : ∀ g ∈ innerZ, IsZTypeElement g
  innerX_isX : ∀ g ∈ innerX, IsXTypeElement g
  outerZ : List (NQubitPauliGroupElement n₂)
  outerX : List (NQubitPauliGroupElement n₂)
  outer_split : List.Perm Cout.generatorsList (outerZ ++ outerX)
  outerZ_isZ : ∀ g ∈ outerZ, IsZTypeElement g
  outerX_isX : ∀ g ∈ outerX, IsXTypeElement g
  innerLogX_isX : NQubitPauliOperator.IsXType (Cin.logicalX 0).operators
  innerLogX_phaseZero : (Cin.logicalX 0).phasePower = 0
  innerLogZ_isZ : NQubitPauliOperator.IsZType (Cin.logicalZ 0).operators
  innerLogZ_phaseZero : (Cin.logicalZ 0).phasePower = 0
  /-- The outer logical `X` representatives are X-type (hence `Y`-free): required so that
  `promote_anticommute_parity` applies to the promoted logicals. A CSS outer code admits
  such representatives. -/
  outerLogX_isX : ∀ ℓ : Fin k₂, NQubitPauliOperator.IsXType (Cout.logicalX ℓ).operators
  /-- The outer logical `Z` representatives are Z-type (hence `Y`-free). -/
  outerLogZ_isZ : ∀ ℓ : Fin k₂, NQubitPauliOperator.IsZType (Cout.logicalZ ℓ).operators

namespace ConcatCSSData

variable (D : ConcatCSSData n₁ n₂ k₂)

/-- The inner logical-`X` operator used as the `X ↦ X̄₁` promotion target. -/
def Xbar : NQubitPauliOperator n₁ := (D.Cin.logicalX 0).operators

/-- The inner logical-`Z` operator used as the `Z ↦ Z̄₁` promotion target. -/
def Zbar : NQubitPauliOperator n₁ := (D.Cin.logicalZ 0).operators

/-! ## The concatenated generator list -/

/-- Inner stabilizers replicated across every block. -/
def s1PerBlockList : List (NQubitPauliGroupElement (n₁ * n₂)) :=
  (List.finRange n₂).flatMap (fun b => D.Cin.generatorsList.map (embedBlock b))

/-- Promoted outer stabilizers (routed through the typed sublists, so the
`promoteSingle` `Y` branch is provably unreachable). -/
def promotedOuterList : List (NQubitPauliGroupElement (n₁ * n₂)) :=
  (D.outerZ ++ D.outerX).map (promoteE D.Xbar D.Zbar)

/-- The full generator list of the concatenated code. -/
def concatGeneratorsList : List (NQubitPauliGroupElement (n₁ * n₂)) :=
  D.s1PerBlockList ++ D.promotedOuterList

/-! ## Easy structural facts -/

lemma s1PerBlockList_length :
    D.s1PerBlockList.length = n₂ * (n₁ - 1) := by
  simp [ConcatCSSData.s1PerBlockList, List.length_flatMap, List.length_map,
    D.Cin.generators_length]

lemma promotedOuterList_length :
    D.promotedOuterList.length = n₂ - k₂ := by
  rw [ConcatCSSData.promotedOuterList, List.length_map]
  rw [← D.outer_split.length_eq, D.Cout.generators_length]

lemma concatGeneratorsList_length :
    D.concatGeneratorsList.length = n₁ * n₂ - k₂ := by
  rw [ConcatCSSData.concatGeneratorsList, List.length_append, D.s1PerBlockList_length,
    D.promotedOuterList_length]
  have hn1 : 1 ≤ n₁ := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n₁)
  have hk : k₂ ≤ n₂ := D.Cout.hk
  have e1 : n₂ * (n₁ - 1) = n₁ * n₂ - n₂ := by rw [Nat.mul_sub, Nat.mul_one, Nat.mul_comm]
  have e2 : n₂ ≤ n₁ * n₂ := Nat.le_mul_of_pos_left n₂ hn1
  omega

lemma concatGeneratorsList_phaseZero :
    AllPhaseZero D.concatGeneratorsList := by
  intro g hg
  simp only [ConcatCSSData.concatGeneratorsList, ConcatCSSData.s1PerBlockList,
    ConcatCSSData.promotedOuterList, List.mem_append, List.mem_flatMap, List.mem_map] at hg
  rcases hg with ⟨b, -, x, -, rfl⟩ | ⟨y, -, rfl⟩ <;> simp

end ConcatCSSData

end Quantum.Concatenation
