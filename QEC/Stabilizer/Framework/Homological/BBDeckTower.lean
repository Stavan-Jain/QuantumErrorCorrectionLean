/-
# The deck-tower descent: `σ_* = id` forces Bezout membership (A13)

This file formalizes the **hard direction** of the tour-de-gross tower
question (research note `qec-lab:experiments/bb_lab/notes/A13_deck_tower_plan.md`):

> For a free `ℤ_{2^r}` doubling cover with deck generator `σ`, if the deck
> acts trivially on `H₁` of the top complex, then `1 + σ ∈ (A, B)` — hence
> (counting lemma) `k(top) = k(base)`, and the whole deck acts trivially at
> every intermediate level.

The converse (`membership ⟹ deck-trivial`, Koszul annihilation) is already
formalized as `Quantum.Stabilizer.Homological.BB.deckTrivial_of_bezout`
(A12). Together they give the family statement **deck-trivial ⟺ k constant
along the tower**.

## What is proved here, and how it maps to the geometry

Everything is stated over an abstract commutative ring `S` of characteristic
two, for an element `ε` (the reduced deck translation `1 + σ`, so
`ε^{2^r} = (1+σ)^{2^r} = 1 + σ^{2^r} = 0` in char two) and a pair `A B : S`.
The two geometric inputs become two hypotheses:

* **`EpsFree ε N`** — `Ann_S(ε^t) = ε^{N-t}·S`. In the model
  `S = 𝔽₂[G]`, `G = Z_{2^r ℓ} × Z_m`, this holds because `S` is *free* as a
  module over the subgroup algebra `Λ = 𝔽₂[⟨σ⟩] ≅ 𝔽₂[ε]/(ε^{2^r})` (a chain
  ring, where the annihilator identity is elementary), and freeness
  transports annihilators.
* **`DeckTrivial ε A B`** — for every Koszul 1-cycle `(y₁, y₂)` (`A y₁ + B y₂
  = 0`) the shifted chain `ε·(y₁, y₂)` is a boundary `(B z, A z)`. This is
  exactly `ε · H₁ = 0`, i.e. `σ_* = id` on `H₁` (char two: `σ_* - id` is
  multiplication by `ε`).

The engine is `descent`: from a membership witness `ε^t ∈ (A,B)` and
`DeckTrivial`, one deck application on the *canonical cycle* `ε^{N-t}(f,g)`
produces `ε ∈ (A,B) + ε^{N-t}·S` (the key step is that the returned boundary
coefficient `z` satisfies `ε^t z = 0`, so `EpsFree` divides it by `ε^{N-t}`).
`iterate` then bootstraps the tail `ε^{N-t}·S` away using only `ε^N = 0`
(each `boost` pass grows the tail exponent). The entry witness at
`t = 2^{r-1}` is A12 applied to the top `ℤ₂`-step; here it is taken as the
hypothesis `ε^m ∈ (A,B)`, `2 ≤ m ≤ N-2`.

The `qec-lab:experiments/bb_lab/scripts/a13_deck_tower_block_sweep.py` screen checks
this statement, the canonical-cycle mechanism, and the intermediate
identities exhaustively on CRT blocks up to deck order 8; all clean.
-/

import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.LinearCombination

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BBDeckTower

variable {S : Type*} [CommRing S]

/-- **ε-freeness** (the annihilator shape of a free `𝔽₂[ε]/(ε^N)`-module): every
element killed by `ε^t` is divisible by `ε^{N-t}`. Satisfied in the model
`S = 𝔽₂[G]` with `ε = 1 + σ` of deck order `N`, since `S` is free over the chain
ring `𝔽₂[⟨σ⟩]`. -/
def EpsFree (ε : S) (N : ℕ) : Prop :=
  ∀ t, 1 ≤ t → t ≤ N → ∀ x : S, ε ^ t * x = 0 → ∃ y : S, x = ε ^ (N - t) * y

/-- **Deck-triviality on `H₁`**: every Koszul 1-cycle, shifted by `ε`, is a
Koszul boundary. Over char two this is `ε · H₁ = 0`, i.e. `σ_* = id`. -/
def DeckTrivial (ε A B : S) : Prop :=
  ∀ y₁ y₂ : S, A * y₁ + B * y₂ = 0 → ∃ z : S, ε * y₁ = B * z ∧ ε * y₂ = A * z

/-- **One bootstrap pass** (pure commutative-ring algebra, no char or freeness):
a tail `ε^{j+1}·S` is re-expressed with the strictly larger tail exponent
`(j+1)+j`. Iterated, this walks the tail exponent past `N`. -/
theorem boost (ε A B : S) (j : ℕ)
    (h : ∃ p q v : S, ε = p * A + q * B + ε ^ (j + 1) * v) :
    ∃ p q v : S, ε = p * A + q * B + ε ^ (j + 1 + j) * v := by
  obtain ⟨p, q, v, hpqv⟩ := h
  exact ⟨p + ε ^ j * v * p, q + ε ^ j * v * q, v * v, by
    linear_combination (1 + ε ^ j * v) * hpqv⟩

/-- **The tail-elimination iteration.** With `ε^N = 0`, any expression
`ε = p·A + q·B + ε^m·v` with `2 ≤ m` collapses to `ε ∈ (A,B)`: repeated `boost`
grows `m` until `ε^m = 0`. Fuel `k` bounds `N - m`. -/
theorem iterate_aux (ε A B : S) (N : ℕ) (hN : ε ^ N = 0) :
    ∀ (k m : ℕ), 2 ≤ m → N ≤ m + k →
      (∃ p q v : S, ε = p * A + q * B + ε ^ m * v) → ε ∈ Ideal.span {A, B} := by
  intro k
  induction k with
  | zero =>
    intro m _ hNmk h
    obtain ⟨p, q, v, hpqv⟩ := h
    have hεm : ε ^ m = 0 := by
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show N ≤ m by omega)
      rw [hd, pow_add, hN, zero_mul]
    rw [hεm, zero_mul, add_zero] at hpqv
    exact (Ideal.mem_span_pair).mpr ⟨p, q, hpqv.symm⟩
  | succ k ih =>
    intro m hm2 hNmk h
    rcases Nat.lt_or_ge m N with hmN | hNm
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      exact ih (j + 1 + j) (by omega) (by omega) (boost ε A B j h)
    · obtain ⟨p, q, v, hpqv⟩ := h
      have hεm : ε ^ m = 0 := by
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hNm
        rw [hd, pow_add, hN, zero_mul]
      rw [hεm, zero_mul, add_zero] at hpqv
      exact (Ideal.mem_span_pair).mpr ⟨p, q, hpqv.symm⟩

/-- Convenience wrapper: `ε = p·A + q·B + ε^m·v` with `2 ≤ m` and `ε^N = 0`
gives `ε ∈ (A,B)`. -/
theorem iterate (ε A B : S) (N : ℕ) (hN : ε ^ N = 0) {m : ℕ} (hm : 2 ≤ m)
    (h : ∃ p q v : S, ε = p * A + q * B + ε ^ m * v) :
    ε ∈ Ideal.span {A, B} :=
  iterate_aux ε A B N hN N m hm (by omega) h

variable [CharP S 2]

/-- **The descent step.** Given a membership witness `ε^t = f·A + g·B` at a
level `1 ≤ t ≤ N-1` and deck-triviality, one deck application on the canonical
cycle `ε^{N-t}·(f,g)` yields `ε = p·A + q·B + ε^{N-t}·v`. -/
theorem descent (ε A B : S) (N : ℕ) (hN : ε ^ N = 0)
    (hfree : EpsFree ε N) (hR : DeckTrivial ε A B)
    {t : ℕ} (h1 : 1 ≤ t) (h2 : t ≤ N - 1)
    {f g : S} (hfg : ε ^ t = f * A + g * B) :
    ∃ p q v : S, ε = p * A + q * B + ε ^ (N - t) * v := by
  set s := N - t with hs
  have htN : t ≤ N := le_trans h2 (Nat.sub_le N 1)
  have hst : s + t = N := Nat.sub_add_cancel htN
  have hs1 : 1 ≤ s := by omega
  have hsN : s ≤ N := by omega
  have hNs : N - s = t := by omega
  -- the canonical cycle `(ε^s f, ε^s g)`
  have hcyc : A * (ε ^ s * f) + B * (ε ^ s * g) = 0 := by
    have e : A * (ε ^ s * f) + B * (ε ^ s * g) = ε ^ s * (f * A + g * B) := by
      ring
    rw [e, ← hfg, ← pow_add, hst, hN]
  obtain ⟨z, hz1, hz2⟩ := hR _ _ hcyc
  -- `ε^t z = 0`
  have hz0 : ε ^ t * z = 0 := by
    have e : ε ^ t * z = f * (A * z) + g * (B * z) := by rw [hfg]; ring
    rw [e, ← hz2, ← hz1]
    have e2 : f * (ε * (ε ^ s * g)) + g * (ε * (ε ^ s * f))
        = ε * ε ^ s * (f * g) + ε * ε ^ s * (f * g) := by ring
    rw [e2, CharTwo.add_self_eq_zero]
  -- divide `z` by `ε^s`
  obtain ⟨u, hu⟩ := hfree t h1 htN z hz0
  rw [← hs] at hu
  -- `ε f = ε^t p + B u`
  have h5f : ε ^ s * (ε * f + B * u) = 0 := by
    have e : ε ^ s * (ε * f + B * u) = ε * (ε ^ s * f) + ε ^ s * (B * u) := by
      ring
    rw [e, hz1, hu]
    have e2 : B * (ε ^ s * u) + ε ^ s * (B * u) = ε ^ s * (B * u) + ε ^ s * (B * u) := by
      ring
    rw [e2, CharTwo.add_self_eq_zero]
  obtain ⟨p, hp⟩ := hfree s hs1 hsN _ h5f
  rw [hNs] at hp
  have hεf : ε * f = ε ^ t * p + B * u := by
    have := eq_sub_of_add_eq hp; rwa [CharTwo.sub_eq_add] at this
  -- `ε g = ε^t q + A u`
  have h5g : ε ^ s * (ε * g + A * u) = 0 := by
    have e : ε ^ s * (ε * g + A * u) = ε * (ε ^ s * g) + ε ^ s * (A * u) := by
      ring
    rw [e, hz2, hu]
    have e2 : A * (ε ^ s * u) + ε ^ s * (A * u) = ε ^ s * (A * u) + ε ^ s * (A * u) := by
      ring
    rw [e2, CharTwo.add_self_eq_zero]
  obtain ⟨q, hq⟩ := hfree s hs1 hsN _ h5g
  rw [hNs] at hq
  have hεg : ε * g = ε ^ t * q + A * u := by
    have := eq_sub_of_add_eq hq; rwa [CharTwo.sub_eq_add] at this
  -- `ε^{t+1} = ε^t (p A + q B)`
  have h7 : ε ^ t * ε = ε ^ t * (p * A + q * B) := by
    have lhs : ε ^ t * ε = ε * (f * A + g * B) := by rw [← hfg]; ring
    rw [lhs]
    have e : ε * (f * A + g * B) = ε * f * A + ε * g * B := by ring
    rw [e, hεf, hεg]
    have e2 : (ε ^ t * p + B * u) * A + (ε ^ t * q + A * u) * B
        = ε ^ t * (p * A + q * B) + (A * B * u + A * B * u) := by ring
    rw [e2, CharTwo.add_self_eq_zero, add_zero]
  -- `ε + (p A + q B) ∈ ann(ε^t) = ε^s S`
  have h8 : ε ^ t * (ε + (p * A + q * B)) = 0 := by
    have e : ε ^ t * (ε + (p * A + q * B)) = ε ^ t * ε + ε ^ t * (p * A + q * B) := by
      ring
    rw [e, h7, CharTwo.add_self_eq_zero]
  obtain ⟨v, hv⟩ := hfree t h1 htN _ h8
  rw [← hs] at hv
  refine ⟨p, q, v, ?_⟩
  have := eq_sub_of_add_eq hv
  rw [CharTwo.sub_eq_add] at this
  linear_combination this

/-- **A13, the hard direction (⟹).** For a free `ℤ_{2^r}` doubling cover
(`ε = 1 + σ`, deck order `N`, `ε^N = 0`, `EpsFree`), deck-triviality on `H₁`
forces the Bezout membership `ε ∈ (A, B)`. The entry `ε^m ∈ (A,B)` with
`2 ≤ m ≤ N-2` is A12 applied to the top `ℤ₂`-step (`m = 2^{r-1}`; needs `r ≥ 2`,
i.e. `N ≥ 4`). Combined with `deckTrivial_of_bezout` (the ⟸) this gives
**deck-trivial ⟺ `ε ∈ (A,B)` ⟺ k constant along the tower**. -/
theorem eps_mem_of_deckTrivial (ε A B : S) (N : ℕ) (hN : ε ^ N = 0)
    (hfree : EpsFree ε N) (hR : DeckTrivial ε A B)
    {m : ℕ} (hm2 : 2 ≤ m) (hmN : m ≤ N - 2)
    (hentry : ε ^ m ∈ Ideal.span {A, B}) :
    ε ∈ Ideal.span {A, B} := by
  obtain ⟨f, g, hfg⟩ := (Ideal.mem_span_pair).mp hentry
  have hd := descent ε A B N hN hfree hR (show 1 ≤ m by omega)
    (show m ≤ N - 1 by omega) hfg.symm
  exact iterate ε A B N hN (m := N - m) (by omega) hd

end BBDeckTower
end Homological
end Stabilizer
end Quantum
