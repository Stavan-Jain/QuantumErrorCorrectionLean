import QEC.Stabilizer.Homological.CSS
import QEC.Stabilizer.Core.CSSCommutationLemmas
import QEC.Stabilizer.PauliGroup.SupportLemmas

/-!
# §B.2 — Stabilizer generators of a homological CSS code

For a `HomologicalCode X`, the X-stabilizer generators are face stabilizers
`chainXOperator (∂₂ (singleFace f))`, and the Z-stabilizer generators are
vertex stabilizers `chainZOperator (cutMap (singleVtx v))`.

We prove pairwise commutation:

* X-X commute (both X-type).
* Z-Z commute (both Z-type).
* X-Z commute iff their `Σ e, c e * c' e` vanishes (the bilinear pairing on
  chains).  For face/vertex generators this is `0` by the chain-complex law
  `∂₁ ∘ ∂₂ = 0` together with `boundary1_cutMap_transpose` from §A.
-/

namespace Quantum
namespace Stabilizer
namespace Homological

open scoped BigOperators

namespace HomologicalCode

variable (X : HomologicalCode)

/-- Indicator chain at a single 2-cell. -/
noncomputable def singleFace (f : X.C2) : X.C2 → ZMod 2 := Pi.single f 1

/-- Indicator chain at a single 0-cell. -/
noncomputable def singleVtx (v : X.C0) : X.C0 → ZMod 2 := Pi.single v 1

/-- Indicator chain at a single 1-cell. -/
noncomputable def singleEdge (e : X.C1) : X.C1 → ZMod 2 := Pi.single e 1

/-- The X face stabilizer at face `f`. -/
noncomputable def faceStabOf (f : X.C2) :
    NQubitPauliGroupElement X.numQubits :=
  X.chainXOperator (X.boundary2 (X.singleFace f))

/-- The Z vertex stabilizer at vertex `v`. -/
noncomputable def vertexStabOf (v : X.C0) :
    NQubitPauliGroupElement X.numQubits :=
  X.chainZOperator (X.cutMap (X.singleVtx v))

/-- The set of X stabilizer generators. -/
noncomputable def XGenerators : Set (NQubitPauliGroupElement X.numQubits) :=
  Set.range X.faceStabOf

/-- The set of Z stabilizer generators. -/
noncomputable def ZGenerators : Set (NQubitPauliGroupElement X.numQubits) :=
  Set.range X.vertexStabOf

variable {X}

/-- Every X generator is X-type. -/
lemma faceStabOf_isXType (f : X.C2) :
    NQubitPauliGroupElement.IsXTypeElement (X.faceStabOf f) :=
  chainXOperator_isXType _

/-- Every Z generator is Z-type. -/
lemma vertexStabOf_isZType (v : X.C0) :
    NQubitPauliGroupElement.IsZTypeElement (X.vertexStabOf v) :=
  chainZOperator_isZType _

lemma XGenerators_isXType :
    ∀ g ∈ X.XGenerators, NQubitPauliGroupElement.IsXTypeElement g := by
  rintro _ ⟨f, rfl⟩; exact faceStabOf_isXType f

lemma ZGenerators_isZType :
    ∀ g ∈ X.ZGenerators, NQubitPauliGroupElement.IsZTypeElement g := by
  rintro _ ⟨v, rfl⟩; exact vertexStabOf_isZType v

/-! ## Inner product of two 1-chains and the chain-complex law -/

/-- The bilinear pairing on 1-chains over `𝔽₂`. -/
noncomputable def chainInnerProduct (c c' : X.C1 → ZMod 2) : ZMod 2 :=
  ∑ e : X.C1, c e * c' e

/-- The pairing of `∂₂ f` against `cutMap s` is zero (the chain-complex law,
expressed bilinearly via the §A transpose theorem). -/
theorem chainInnerProduct_boundary2_cutMap_eq_zero
    (f : X.C2 → ZMod 2) (s : X.C0 → ZMod 2) :
    chainInnerProduct (X.boundary2 f) (X.cutMap s) = 0 := by
  unfold chainInnerProduct
  rw [← X.boundary1_cutMap_transpose]
  rw [X.boundary_comp_apply f]
  simp

/-! ## Filter cardinalities and the X-Z commutation criterion -/

/-- Helper: a `ZMod 2` element is `0` or `1`. -/
private lemma zmod2_dichotomy (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hvalle : a.val ≤ 1 := Nat.le_of_lt_succ a.val_lt
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hvalle with h0 | h1
  · left
    calc a = ((a.val : ZMod 2)) := (ZMod.natCast_zmod_val a).symm
      _ = 0 := by simp [h0]
  · right
    calc a = ((a.val : ZMod 2)) := (ZMod.natCast_zmod_val a).symm
      _ = 1 := by simp [h1]

/-- Inner product equals filter cardinality in `ZMod 2`. -/
private lemma chainInnerProduct_eq_card_filter (c c' : X.C1 → ZMod 2) :
    chainInnerProduct c c' =
      ((Finset.univ.filter (fun e : X.C1 => c e = 1 ∧ c' e = 1)).card : ZMod 2) := by
  classical
  unfold chainInnerProduct
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro e _
  rcases zmod2_dichotomy (c e) with hc | hc <;>
    rcases zmod2_dichotomy (c' e) with hc' | hc' <;>
    simp [hc, hc']

/-- A Nat is even iff its `ZMod 2` cast is 0. -/
private lemma nat_cast_zmod2_eq_zero_iff_even (n : ℕ) :
    ((n : ZMod 2) = 0) ↔ Even n :=
  ZMod.natCast_eq_zero_iff_even

open Classical in
/-- The anticommutation filter on qubits has the same cardinality as the
inner-product filter on edges (via the `edgeEquiv` bijection). -/
private lemma anticomm_filter_card_eq_inner_filter_card
    (c c' : X.C1 → ZMod 2) :
    (Finset.univ.filter (fun q : Fin X.numQubits =>
      NQubitPauliGroupElement.anticommutesAt
        (X.chainXOperator c).operators (X.chainZOperator c').operators q)).card
    = (Finset.univ.filter (fun e : X.C1 => c e = 1 ∧ c' e = 1)).card := by
  classical
  rw [Finset.card_filter, Finset.card_filter]
  -- Reindex: ∑ q : Fin n, g q = ∑ e : C1, g (eqv e), via X.edgeEquiv : C1 ≃ Fin n.
  have hreindex :
      (∑ q : Fin X.numQubits,
        if NQubitPauliGroupElement.anticommutesAt
            (X.chainXOperator c).operators (X.chainZOperator c').operators q
          then (1 : ℕ) else 0)
      =
      (∑ e : X.C1,
        if NQubitPauliGroupElement.anticommutesAt
            (X.chainXOperator c).operators (X.chainZOperator c').operators (X.edgeEquiv e)
          then (1 : ℕ) else 0) :=
    (Equiv.sum_comp X.edgeEquiv (fun q =>
      if NQubitPauliGroupElement.anticommutesAt
          (X.chainXOperator c).operators (X.chainZOperator c').operators q
        then (1 : ℕ) else 0)).symm
  rw [hreindex]
  apply Finset.sum_congr rfl
  intro e _
  -- Pointwise: anticommutesAt at (eqv e) ↔ c e = 1 ∧ c' e = 1
  have hX :=
    (chainXOperator_isXType (X := X) c).2
  have hZ :=
    (chainZOperator_isZType (X := X) c').2
  have hbiconditional :
      NQubitPauliGroupElement.anticommutesAt
          (X.chainXOperator c).operators (X.chainZOperator c').operators (X.edgeEquiv e)
        ↔ c e = 1 ∧ c' e = 1 := by
    rw [NQubitPauliGroupElement.anticommutesAt_iff_mem_support_both_of_XZType hX hZ]
    constructor
    · rintro ⟨hxs, hzs⟩
      exact ⟨(mem_support_chainXOperator_iff c e).mp hxs,
             (mem_support_chainZOperator_iff c' e).mp hzs⟩
    · rintro ⟨hc, hc'⟩
      exact ⟨(mem_support_chainXOperator_iff c e).mpr hc,
             (mem_support_chainZOperator_iff c' e).mpr hc'⟩
  by_cases h : NQubitPauliGroupElement.anticommutesAt
      (X.chainXOperator c).operators (X.chainZOperator c').operators (X.edgeEquiv e)
  · rw [if_pos h, if_pos (hbiconditional.mp h)]
  · rw [if_neg h, if_neg (h ∘ hbiconditional.mpr)]

open Classical in
/-- Commutation criterion: `chainXOperator c` commutes with `chainZOperator c'`
iff their inner product over `𝔽₂` vanishes. -/
theorem chainXOperator_commutes_chainZOperator_iff (c c' : X.C1 → ZMod 2) :
    X.chainXOperator c * X.chainZOperator c' =
      X.chainZOperator c' * X.chainXOperator c
    ↔ chainInnerProduct c c' = 0 := by
  classical
  rw [NQubitPauliGroupElement.commutes_iff_even_anticommutes,
      anticomm_filter_card_eq_inner_filter_card c c',
      chainInnerProduct_eq_card_filter c c']
  exact (nat_cast_zmod2_eq_zero_iff_even _).symm

/-- The face X-stabilizer commutes with the vertex Z-stabilizer (chain-complex law). -/
theorem faceStabOf_commutes_vertexStabOf (f : X.C2) (v : X.C0) :
    X.faceStabOf f * X.vertexStabOf v = X.vertexStabOf v * X.faceStabOf f := by
  unfold faceStabOf vertexStabOf
  rw [chainXOperator_commutes_chainZOperator_iff]
  exact chainInnerProduct_boundary2_cutMap_eq_zero (X.singleFace f) (X.singleVtx v)

/-- Two face X-stabilizers commute (both X-type). -/
theorem faceStabOf_commutes_faceStabOf (f f' : X.C2) :
    X.faceStabOf f * X.faceStabOf f' = X.faceStabOf f' * X.faceStabOf f :=
  Quantum.StabilizerGroup.CSSCommutationLemmas.XType_commutes
    (faceStabOf_isXType f) (faceStabOf_isXType f')

/-- Two vertex Z-stabilizers commute (both Z-type). -/
theorem vertexStabOf_commutes_vertexStabOf (v v' : X.C0) :
    X.vertexStabOf v * X.vertexStabOf v' = X.vertexStabOf v' * X.vertexStabOf v :=
  Quantum.StabilizerGroup.CSSCommutationLemmas.ZType_commutes
    (vertexStabOf_isZType v) (vertexStabOf_isZType v')

/-- Z generators commute with X generators (CSS cross-commutation). -/
theorem ZGenerators_commute_XGenerators :
    ∀ z ∈ X.ZGenerators, ∀ x ∈ X.XGenerators, z * x = x * z := by
  rintro _ ⟨v, rfl⟩ _ ⟨f, rfl⟩
  exact (faceStabOf_commutes_vertexStabOf f v).symm

end HomologicalCode

end Homological
end Stabilizer
end Quantum
