/-
# The Bockstein tower-lift core (A13, element level)

For a free ℤ₂ BB cover with deck `σ`, `ε = 1+σ`, the transfer-LES
connecting maps `δ₂ : H₂(base) → H₁(base)`, `δ₁ : H₁(base) → H₀(base)`
compose to zero, which forces `dim (1+σ)H₁(cover) = k(cover) − k(base)`
and the deck-module classification `H₁ ≅ D^{k̃−k} ⊕ F₂^{2k−k̃}`
(`qec-lab:experiments/bb_lab/notes/A13_result.md`).

This file formalizes the **element-level core** of the proof: the
composite's canonical representative `W = A·b + B·a` vanishes, because
everything lifts one more rung up the doubling tower (`ε̂` with
`Ann(ε̂) = (ε̂³)` — the group-algebra of the ℤ/4 Frattini extension of the
deck), where `ε̂·Ŵ = 2·ÂB̂ẑ = 0` in characteristic 2.

The three lemmas are stated over an abstract commutative ring with the
annihilator facts as hypotheses, so they apply to `F₂[Ĝ]` for every
finite abelian `Ĝ` (where the hypotheses hold by freeness over
`F₂[ℤ/4]`), to every coefficient block `S[P]`, and — per instance — are
finite, decidable side conditions.

* `rep_eq_zero_upstairs` — the four-line kill: upstairs, `W` is
  divisible by `ε̂³`, hence lies in `(ε̂²)` = the kernel of the descent
  to the cover ring.
* `exists_vanishing_choice_in_quotient` — descended statement: in
  `R̂ ⧸ (ε̂²)` every 2-cycle-type element has a *canonical* choice of
  `ε`-preimages with `A·b₀ + B·a₀ = 0` on the nose.
* `mem_span_of_vanishing_choice` — choice independence: any other valid
  choice moves `W` within `ε·(A,B)`, giving A12 OQ2's element form
  exactly as stated there ("well-defined mod `ε(A,B)`").

TODO(a13-lean): instantiate the annihilator hypotheses for
`MonoidAlgebra (ZMod 2) Ĝ` via freeness over the subgroup algebra of
`⟨σ̂⟩` (coset basis), and connect to `BBDoubling`'s convolution layer.
-/
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Data.ZMod.Basic

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BocksteinLift

variable {R : Type*} [CommRing R]

/-- **Upstairs core.** In a commutative ring of characteristic 2 where
`Ann(ε) = (ε³)` (e.g. `F₂[Ĝ]` with `ε = 1 + σ̂`, `σ̂` of order 4, by freeness
over `F₂[ℤ/4]`), if `A·z` and `B·z` are both divisible by `ε` then the Bockstein
representative `A·b + B·a` built from the quotients is divisible by `ε³`; in
particular it lies in `(ε²)`, the kernel of the descent to the cover ring. -/
theorem rep_eq_zero_upstairs (ε A B z a b : R)
    (hchar : (2 : R) = 0)
    (hann : ∀ w : R, ε * w = 0 → ∃ v, w = ε ^ 3 * v)
    (hAz : A * z = ε * a) (hBz : B * z = ε * b) :
    ∃ v, A * b + B * a = ε ^ 2 * (ε * v) := by
  have hkill : ε * (A * b + B * a) = 0 := by
    have h1 : ε * (A * b + B * a) = A * (ε * b) + B * (ε * a) := by ring
    rw [h1, ← hAz, ← hBz]
    have h2 : A * (B * z) + B * (A * z) = 2 * (A * B * z) := by ring
    rw [h2, hchar, zero_mul]
  obtain ⟨v, hv⟩ := hann _ hkill
  exact ⟨v, by rw [hv]; ring⟩

/-- The annihilator of `ε` in the descended ring `R ⧸ (ε²)` is `(ε)`: what
`Ann(ε̂) = (ε̂³)` upstairs becomes downstairs. -/
theorem ann_eps_quotient (ε : R)
    (hann : ∀ w : R, ε * w = 0 → ∃ v, w = ε ^ 3 * v)
    (w : R ⧸ Ideal.span {ε ^ 2})
    (hw : Ideal.Quotient.mk (Ideal.span {ε ^ 2}) ε * w = 0) :
    ∃ v, w = Ideal.Quotient.mk (Ideal.span {ε ^ 2}) ε * v := by
  obtain ⟨wHat, rfl⟩ := Ideal.Quotient.mk_surjective w
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at hw
  obtain ⟨r, hr⟩ := hw
  have hkill : ε * (wHat - ε * r) = 0 := by
    rw [mul_sub, hr]; ring
  obtain ⟨v, hv⟩ := hann _ hkill
  have h3 : wHat = ε * (r + ε ^ 2 * v) := by
    have h4 : wHat = ε * r + ε ^ 3 * v := by rw [← hv]; ring
    rw [h4]; ring
  exact ⟨Ideal.Quotient.mk _ (r + ε ^ 2 * v), by rw [← map_mul, h3]⟩

/-- **Descended canonical choice.** In the cover ring `R̃ = R̂ ⧸ (ε̂²)`,
whenever `A·z` and `B·z` are divisible by `ε`, there are `ε`-preimages `a₀, b₀`
with `A·b₀ + B·a₀ = 0` on the nose: lift `z` upstairs, apply
`rep_eq_zero_upstairs`, and descend. This is the tower-compatible choice of the
paper proof. -/
theorem exists_vanishing_choice_in_quotient (ε A B : R)
    (hchar : (2 : R) = 0)
    (hann : ∀ w : R, ε * w = 0 → ∃ v, w = ε ^ 3 * v)
    (z a b : R ⧸ Ideal.span {ε ^ 2})
    (hAz : Ideal.Quotient.mk _ A * z = Ideal.Quotient.mk _ ε * a)
    (hBz : Ideal.Quotient.mk _ B * z = Ideal.Quotient.mk _ ε * b) :
    ∃ a₀ b₀ : R ⧸ Ideal.span {ε ^ 2},
      Ideal.Quotient.mk _ A * z = Ideal.Quotient.mk _ ε * a₀ ∧
      Ideal.Quotient.mk _ B * z = Ideal.Quotient.mk _ ε * b₀ ∧
      Ideal.Quotient.mk _ A * b₀ + Ideal.Quotient.mk _ B * a₀ = 0 := by
  obtain ⟨zHat, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨aHat, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨bHat, rfl⟩ := Ideal.Quotient.mk_surjective b
  -- upgrade the two congruences to exact divisibility upstairs
  rw [← map_mul, ← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hAz hBz
  obtain ⟨rA, hrA⟩ := hAz
  obtain ⟨rB, hrB⟩ := hBz
  have hAz' : A * zHat = ε * (aHat + ε * rA) := by
    have h := sub_eq_iff_eq_add.mp hrA
    rw [h]; ring
  have hBz' : B * zHat = ε * (bHat + ε * rB) := by
    have h := sub_eq_iff_eq_add.mp hrB
    rw [h]; ring
  obtain ⟨v, hv⟩ :=
    rep_eq_zero_upstairs ε A B zHat (aHat + ε * rA) (bHat + ε * rB) hchar hann hAz' hBz'
  refine ⟨Ideal.Quotient.mk _ (aHat + ε * rA), Ideal.Quotient.mk _ (bHat + ε * rB),
    by rw [← map_mul, ← map_mul, hAz'], by rw [← map_mul, ← map_mul, hBz'], ?_⟩
  rw [← map_mul, ← map_mul, ← map_add, hv]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_span_singleton.mpr ⟨ε * v, rfl⟩)

/-- **Choice independence.** If one valid choice `(a₀, b₀)` of `ε`-preimages
makes `W` vanish, then every valid choice `(a, b)` lands in `ε·(A,B)`: the A12
OQ2 element form. Works in any commutative ring whose `ε`-annihilator is `(ε)` —
downstairs, that is `ann_eps_quotient`. -/
theorem mem_span_of_vanishing_choice (ε A B z a b a₀ b₀ : R)
    (hannε : ∀ w : R, ε * w = 0 → ∃ v, w = ε * v)
    (hAz : ε * a = A * z) (hBz : ε * b = B * z)
    (hAz₀ : ε * a₀ = A * z) (hBz₀ : ε * b₀ = B * z)
    (h₀ : A * b₀ + B * a₀ = 0) :
    A * b + B * a ∈ Ideal.span {ε * A, ε * B} := by
  obtain ⟨va, hva⟩ := hannε (a - a₀) (by rw [mul_sub, hAz, hAz₀, sub_self])
  obtain ⟨vb, hvb⟩ := hannε (b - b₀) (by rw [mul_sub, hBz, hBz₀, sub_self])
  have key : A * b + B * a = ε * B * va + ε * A * vb := by
    have ha : a = a₀ + ε * va := by rw [← hva]; ring
    have hb : b = b₀ + ε * vb := by rw [← hvb]; ring
    calc A * b + B * a
        = (A * b₀ + B * a₀) + (ε * B * va + ε * A * vb) := by rw [ha, hb]; ring
      _ = ε * B * va + ε * A * vb := by rw [h₀, zero_add]
  rw [key]
  exact Ideal.add_mem _
    (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)))
    (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _)))

/-- **The element form (A12 OQ2), abstract capstone.** Downstairs in the cover
ring `Q = R ⧸ (ε²)` (with `R = F₂[Ĝ]` the Frattini lift and `ε = ε̂` its order-4
deck class), whenever `A·z̄` and `B·z̄` are `ε`-divisible the Bockstein
representative `A·b + B·a` lies in `ε·(A,B)`. This is `δ₁∘δ₂ = 0` at the element
level: `exists_vanishing_choice_*` produces the ℤ/4-compatible choice that
vanishes on the nose, and `mem_span_of_vanishing_choice` (fed the downstairs
annihilator fact `ann_eps_quotient`) absorbs any other choice into `ε·(A,B)`. -/
theorem bockstein_element_form (ε A B : R)
    (hchar : (2 : R) = 0)
    (hann : ∀ w : R, ε * w = 0 → ∃ v, w = ε ^ 3 * v)
    (z a b : R ⧸ Ideal.span {ε ^ 2})
    (hAz : Ideal.Quotient.mk _ A * z = Ideal.Quotient.mk _ ε * a)
    (hBz : Ideal.Quotient.mk _ B * z = Ideal.Quotient.mk _ ε * b) :
    Ideal.Quotient.mk _ A * b + Ideal.Quotient.mk _ B * a ∈
      Ideal.span {Ideal.Quotient.mk (Ideal.span {ε ^ 2}) ε * Ideal.Quotient.mk _ A,
        Ideal.Quotient.mk (Ideal.span {ε ^ 2}) ε * Ideal.Quotient.mk _ B} := by
  obtain ⟨a₀, b₀, hAz₀, hBz₀, h₀⟩ :=
    exists_vanishing_choice_in_quotient ε A B hchar hann z a b hAz hBz
  exact mem_span_of_vanishing_choice _ _ _ z a b a₀ b₀
    (ann_eps_quotient ε hann) hAz.symm hBz.symm hAz₀.symm hBz₀.symm h₀

/-! ## The ℤ/4 deck algebra: an unconditional instance

`F₂[ℤ/4] ≅ F₂[X]/(X⁴)` (freshman's dream twice: `X⁴−1 = X⁴+1 = (X+1)⁴` in
characteristic 2, so with `ε = 1+σ = X+1 ↦ X` the group algebra is the truncated
polynomial ring). It is the Frattini-lift local model of the deck, and it
satisfies both upstairs hypotheses — `char 2` and `Ann(ε) = (ε³)` — so the
element form holds **unconditionally** on its cover quotient `F₂[X]/(X⁴) ⧸ (X²)`
(`≅ F₂[ℤ/2]`, the `r = 1` chain block). By the CRT block decomposition (A13 §3)
this is the local content behind the odd-undoubled-coordinate corollary. -/

open Polynomial in
/-- The truncated polynomial ring `F₂[X]/(X⁴)`, standing in for `F₂[ℤ/4]`. -/
abbrev DeckRing := Polynomial (ZMod 2) ⧸ Ideal.span {(X : Polynomial (ZMod 2)) ^ 4}

open Polynomial in
/-- `ε = X`, i.e. the deck class `1 + σ̂` in the group-algebra picture. -/
noncomputable abbrev deckEps : DeckRing := Ideal.Quotient.mk _ (X : Polynomial (ZMod 2))

open Polynomial in
/-- Characteristic 2. -/
theorem deckRing_two : (2 : DeckRing) = 0 := by
  have hP : (2 : Polynomial (ZMod 2)) = 0 := by
    rw [show (2 : Polynomial (ZMod 2)) = C 2 from (map_ofNat C 2).symm,
      show (2 : ZMod 2) = 0 from by decide, map_zero]
  rw [show (2 : DeckRing) = Ideal.Quotient.mk _ (2 : Polynomial (ZMod 2)) from
    (map_ofNat (Ideal.Quotient.mk _) 2).symm, hP, map_zero]

open Polynomial in
/-- `Ann(ε) = (ε³)` in `F₂[X]/(X⁴)`: if `X·p ≡ 0 mod X⁴` then `X³ ∣ p` (cancel
`X` in the polynomial domain). -/
theorem deckRing_ann :
    ∀ w : DeckRing, deckEps * w = 0 → ∃ v, w = deckEps ^ 3 * v := by
  haveI : NoZeroDivisors (ZMod 2) := ⟨by decide⟩
  intro w hw
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective w
  have hmul : deckEps * Ideal.Quotient.mk _ p = Ideal.Quotient.mk _ (X * p) :=
    (map_mul (Ideal.Quotient.mk _) X p).symm
  rw [hmul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hw
  obtain ⟨r, hr⟩ := hw
  have hXp : p = X ^ 3 * r := by
    have hc : X * p = X * (X ^ 3 * r) := by rw [hr]; ring
    exact mul_left_cancel₀ X_ne_zero hc
  refine ⟨Ideal.Quotient.mk _ r, ?_⟩
  have hpow : deckEps ^ 3 = Ideal.Quotient.mk _ (X ^ 3) :=
    (map_pow (Ideal.Quotient.mk _) X 3).symm
  rw [hpow, ← map_mul, hXp]

/-- **Unconditional element form on the ℤ/4 chain block.** No hypotheses: the
Bockstein composite vanishes at the element level on the cover ring
`DeckRing ⧸ (ε²)`. A fully kernel-checked instance of `bockstein_element_form`,
witnessing that the theorem's hypotheses are satisfiable by the actual deck
algebra. -/
theorem bockstein_element_form_deck (A B : DeckRing)
    (z a b : DeckRing ⧸ Ideal.span {deckEps ^ 2})
    (hAz : Ideal.Quotient.mk _ A * z = Ideal.Quotient.mk _ deckEps * a)
    (hBz : Ideal.Quotient.mk _ B * z = Ideal.Quotient.mk _ deckEps * b) :
    Ideal.Quotient.mk _ A * b + Ideal.Quotient.mk _ B * a ∈
      Ideal.span {Ideal.Quotient.mk (Ideal.span {deckEps ^ 2}) deckEps * Ideal.Quotient.mk _ A,
        Ideal.Quotient.mk (Ideal.span {deckEps ^ 2}) deckEps * Ideal.Quotient.mk _ B} :=
  bockstein_element_form deckEps A B deckRing_two deckRing_ann z a b hAz hBz

end BocksteinLift
end Homological
end Stabilizer
end Quantum
