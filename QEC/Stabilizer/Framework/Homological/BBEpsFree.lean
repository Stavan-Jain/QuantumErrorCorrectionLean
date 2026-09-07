/-
# `EpsFree` instances: chain rings and freeness transfer (A13 L2a)

`BBDeckTower.EpsFree ε N` (`ε^t x = 0 → ∃ y, x = ε^{N-t}·y`) is the
annihilator shape of a free `𝔽₂[ε]/(ε^N)`-module. It is the central
hypothesis of *both* deck-lines:

* `BBDeckTower.eps_mem_of_deckTrivial` (OQ1 tower: deck-trivial ⟹ k const)
  takes it as `hfree`;
* `BocksteinLift.bockstein_element_form` (OQ2 element form) takes its
  `N = 4, t = 1` special case as `hann` (`Ann(ε) = (ε³)`).

Neither file discharges it for the group algebra. This file builds the
tools to do so, bottom-up:

* `epsFree_quotXpow` — the **chain ring** `R[X]/(X^N)` with `ε = X`
  satisfies `EpsFree` (any commutative base `R`; the point is that `X` is
  a non-zero-divisor because it is monic). This is the local block, and
  the general `deckRing_ann` of `BocksteinLift` is its `R = 𝔽₂, N = 4,
  t = 1` slice.
* `epsFree_of_free` — **freeness transfer**: if `S` is a free module over
  a commutative subring `Λ` and `ε ∈ Λ` satisfies `EpsFree` in `Λ`, then
  it satisfies `EpsFree` in `S`. This is the "annihilator transports
  across a free module" step, applied with `Λ = 𝔽₂[⟨σ⟩]` (a chain ring)
  and `S = 𝔽₂[G]`.

The remaining gap to a real cover algebra is the freeness of `𝔽₂[G]` over
the subgroup algebra `𝔽₂[⟨σ⟩]` (a coset basis), recorded in the plan as
the residual L2a step with no mathlib support.
-/
import QEC.Stabilizer.Framework.Homological.BBDeckTower
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Basis.Basic

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BBEpsFree

open Polynomial BBDeckTower

/-- **Chain-ring `EpsFree`.** In `R[X]/(X^N)` with `ε = X`, an element killed by
`ε^t` is divisible by `ε^{N-t}` — because `X^t` is monic, hence a
non-zero-divisor, so it cancels. Works over any commutative base `R`. -/
theorem epsFree_quotXpow {R : Type*} [CommRing R] (N : ℕ) :
    EpsFree (Ideal.Quotient.mk (Ideal.span {(X : R[X]) ^ N}) X) N := by
  intro t _ htN x hx
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hεt : (Ideal.Quotient.mk (Ideal.span {(X : R[X]) ^ N}) X) ^ t
        * Ideal.Quotient.mk _ p = Ideal.Quotient.mk _ (X ^ t * p) := by
    rw [← map_pow, ← map_mul]
  rw [hεt, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hx
  obtain ⟨r, hr⟩ := hx
  have hsplit : (X : R[X]) ^ N = X ^ t * X ^ (N - t) := by
    rw [← pow_add, Nat.add_sub_cancel' htN]
  have hcancel : (X : R[X]) ^ t * p = X ^ t * (X ^ (N - t) * r) := by
    rw [hr, hsplit]; ring
  have hp : p = X ^ (N - t) * r := (monic_X_pow t).isRegular.left hcancel
  exact ⟨Ideal.Quotient.mk _ r, by rw [hp, ← map_pow, ← map_mul]⟩

/-- **Freeness transfer for `EpsFree`.** If `S` is a commutative `Λ`-algebra
that is free as a `Λ`-module and `ε₀ ∈ Λ` satisfies `EpsFree` in `Λ`, then its
image `ε = algebraMap ε₀` satisfies `EpsFree` in `S`.

Idea: expand `x` in a `Λ`-basis; `ε^t·x = 0` means every coordinate is killed by
`ε₀^t` (linear independence), so `EpsFree` in `Λ` divides each coordinate by
`ε₀^{N-t}`, and reassembling gives `x = ε^{N-t}·y`. -/
theorem epsFree_of_free {Λ S : Type*} [CommRing Λ] [CommRing S] [Algebra Λ S]
    [Module.Free Λ S] {ε₀ : Λ} {N : ℕ} (hΛ : EpsFree ε₀ N) :
    EpsFree (algebraMap Λ S ε₀) N := by
  classical
  set b := Module.Free.chooseBasis Λ S with hb
  intro t ht1 htN x hx
  -- `ε^t • x = 0` in the module sense; push to coordinates
  have hsmul : ε₀ ^ t • x = 0 := by
    rw [Algebra.smul_def, map_pow]; exact hx
  -- each coordinate of x is killed by ε₀^t (linear independence)
  have hcoord : ∀ i, ε₀ ^ t * b.repr x i = 0 := by
    intro i
    have h1 : (ε₀ ^ t • b.repr x) i = (0 : Module.Free.ChooseBasisIndex Λ S →₀ Λ) i := by
      rw [← map_smul, hsmul, map_zero]
    rwa [Finsupp.smul_apply, smul_eq_mul, Finsupp.zero_apply] at h1
  -- divide each coordinate by ε₀^{N-t}
  choose y hy using fun i => hΛ t ht1 htN (b.repr x i) (hcoord i)
  refine ⟨∑ i ∈ (b.repr x).support, y i • b i, ?_⟩
  -- reassemble: x = ∑ (b.repr x i) • b i = ε^{N-t} · ∑ (y i · b i)
  conv_lhs => rw [← b.linearCombination_repr x]
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hy i, mul_smul, Algebra.smul_def, map_pow]

/-- **Bridge to `BocksteinLift`.** `EpsFree ε 4` (its `t = 1` slice) is exactly
the annihilator hypothesis `Ann(ε) = (ε³)` that
`BocksteinLift.bockstein_element_form` takes as `hann`. So the OQ1 tower line
(`BBDeckTower`, which consumes the full `EpsFree`) and the OQ2 element-form line
(`BocksteinLift`) rest on the *same* ring input, and
`epsFree_quotXpow`/`epsFree_of_free` discharge it uniformly. -/
theorem hann_of_epsFree {S : Type*} [CommRing S] {ε : S} (h : EpsFree ε 4) :
    ∀ w : S, ε * w = 0 → ∃ v, w = ε ^ 3 * v := by
  intro w hw
  have h1 := h 1 le_rfl (by norm_num) w (by rw [pow_one]; exact hw)
  simpa using h1

end BBEpsFree
end Homological
end Stabilizer
end Quantum
