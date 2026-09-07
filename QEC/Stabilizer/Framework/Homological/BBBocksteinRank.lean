/-
# The transfer-inequality core: `dim (im ε) ≥ dim Hc − dim Hb` (A13 L2b, Phase 1)

The rank corollary of the Bockstein equality is
`dim (1+σ)·H₁(cover) = k(cover) − k(base)` (A13 `A13_result.md` §1). Its
**inequality** direction (`≥`, which is A12 part 2, so far only on paper)
has a purely linear-algebraic heart, isolated here:

> Given finite-dimensional `F`-spaces `Hc, Hb` and maps `p : Hc → Hb`,
> `τ : Hb → Hc` with `ker p = im τ` (exactness at `Hc` of the transfer
> sequence `Hb →τ Hc →p Hb`), the composite `ε = τ ∘ p` satisfies
> `dim Hc − dim Hb ≤ dim (im ε)`.

In the intended instance `Hc = H₁(cover)`, `Hb = H₁(base)`, `p = p_*`
(pushforward), `τ = τ_*` (transfer), and `ε_* = τ_* ∘ p_* = (1+σ)_*` is
the deck action (repo: `pull1_push1 : pull1 (push1 v) = v + σv`). Then
`dim Hc = k̃`, `dim Hb = k`, `dim (im ε_*) = E`, giving `E ≥ k̃ − k`.

The one homological input the instance must supply is the exactness
`ker p_* = im τ_*` (the transfer LES's exactness at the cover) — a
diagram chase over the repo's chain-level exactness
(`push1_eq_zero_iff`, `push1_pull1_eq_zero`, `pull1_injective`,
`push1_surjective`). That instantiation is the next Phase-1 step; the core
below is complete and instance-agnostic.
-/
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BBBocksteinRank

open Module LinearMap

variable {F Hc Hb : Type*} [Field F]
  [AddCommGroup Hc] [Module F Hc] [FiniteDimensional F Hc]
  [AddCommGroup Hb] [Module F Hb] [FiniteDimensional F Hb]

/-- `dim ker (g ∘ f) ≤ dim ker f + dim ker g`: the kernel of a composite is
`comap f (ker g)`, which sits over `ker f` with quotient embedding into `ker g`.
-/
theorem finrank_ker_comp_le (f : Hc →ₗ[F] Hb) (g : Hb →ₗ[F] Hc) :
    finrank F (ker (g ∘ₗ f)) ≤ finrank F (ker f) + finrank F (ker g) := by
  set K := ker (g ∘ₗ f) with hK
  -- restrict `f` to `K`; rank-nullity: `dim K = dim (range) + dim (ker)`
  have hrn := LinearMap.finrank_range_add_finrank_ker (f.domRestrict K)
  -- `range (f|K) = map f K ≤ ker g`  (same ambient `Hb`)
  have hrange : finrank F (range (f.domRestrict K)) ≤ finrank F (ker g) := by
    rw [LinearMap.range_domRestrict]
    apply Submodule.finrank_mono
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    rw [LinearMap.mem_ker]
    have hxK : (g ∘ₗ f) x = 0 := LinearMap.mem_ker.mp hx
    rwa [LinearMap.comp_apply] at hxK
  -- `ker (f|K)` injects (via `K.subtype`) into `ker f`, so `dim ≤ dim (ker f)`
  have hker : finrank F (ker (f.domRestrict K)) ≤ finrank F (ker f) := by
    rw [(Submodule.equivMapOfInjective K.subtype Subtype.coe_injective
      (ker (f.domRestrict K))).finrank_eq]
    apply Submodule.finrank_mono
    rintro _ ⟨x, hx, rfl⟩
    rw [LinearMap.mem_ker]
    have : (f.domRestrict K) x = 0 := LinearMap.mem_ker.mp hx
    rwa [LinearMap.domRestrict_apply] at this
  omega

/-- **The transfer-inequality core.** With exactness `ker p = im τ` of the
transfer sequence at the cover, the deck composite `ε = τ ∘ p` has image of
dimension at least `dim Hc − dim Hb`. -/
theorem finrank_sub_le_finrank_range_comp
    (p : Hc →ₗ[F] Hb) (τ : Hb →ₗ[F] Hc)
    (hexact : ker p = range τ) :
    finrank F Hc - finrank F Hb ≤ finrank F (range (τ ∘ₗ p)) := by
  -- names
  have hEc := LinearMap.finrank_range_add_finrank_ker (τ ∘ₗ p)  -- E + dim ker(τ∘p) = dim Hc
  have hp := LinearMap.finrank_range_add_finrank_ker p          -- dim im p + dim ker p = dim Hc
  have hτ := LinearMap.finrank_range_add_finrank_ker τ          -- dim im τ + dim ker τ = dim Hb
  have hkerp : finrank F (ker p) = finrank F (range τ) := by rw [hexact]
  have hcomp := finrank_ker_comp_le p τ                   -- dim ker(τ∘p) ≤ dim ker p + dim ker τ
  omega

/-- **Exact defect identity.** With exactness `ker p = range τ`, the deck
composite `ε = τ ∘ p` satisfies
`dim (im ε) + dim Hb + dim (range p ⊓ ker τ) = dim Hc + dim (ker τ)`.

The `range p ⊓ ker τ` term is the entire obstruction to tightness of
`finrank_sub_le_finrank_range_comp`: it is `≤ ker τ` always, and equals `ker τ`
exactly when `ker τ ≤ range p`. In the homology instance this
`range p ⊓ ker τ = ker τ` condition is the Bockstein vanishing `δ₁ ∘ δ₂ = 0`. -/
theorem finrank_range_comp_add_eq
    (p : Hc →ₗ[F] Hb) (τ : Hb →ₗ[F] Hc)
    (hexact : ker p = range τ) :
    finrank F (range (τ ∘ₗ p)) + finrank F Hb
        + finrank F (range p ⊓ ker τ : Submodule F Hb)
      = finrank F Hc + finrank F (ker τ) := by
  -- rank-nullity for `τ ∘ p`, `τ`, and `p` restricted to `K := ker (τ ∘ p)`
  have hEc := LinearMap.finrank_range_add_finrank_ker (τ ∘ₗ p)
  have hτ := LinearMap.finrank_range_add_finrank_ker τ
  have hrn := LinearMap.finrank_range_add_finrank_ker
    (p.domRestrict (ker (τ ∘ₗ p)))
  -- `range (p|K) = range p ⊓ ker τ`  (`K = comap p (ker τ)`)
  have hrange : finrank F (range (p.domRestrict (ker (τ ∘ₗ p))))
      = finrank F (range p ⊓ ker τ : Submodule F Hb) := by
    rw [LinearMap.range_domRestrict, LinearMap.ker_comp, Submodule.map_comap_eq]
  -- `ker (p|K) ≅ ker p`  (since `ker p ≤ K`)
  have hker : finrank F (ker (p.domRestrict (ker (τ ∘ₗ p))))
      = finrank F (ker p) := by
    rw [LinearMap.ker_domRestrict]
    exact (Submodule.comapSubtypeEquivOfLe (LinearMap.ker_le_ker_comp p τ)).finrank_eq
  rw [hrange, hker] at hrn
  -- `ker p = range τ`
  have hkerp : finrank F (ker p) = finrank F (range τ) := by rw [hexact]
  omega

/-- **The tightness criterion (sufficient direction).**
`finrank_sub_le_finrank_range_comp` is an equality when `ker τ ≤ range p`. In
the homology instance `ker τ ≤ range p` is the Bockstein vanishing
`δ₁ ∘ δ₂ = 0`, so this is the step that turns `E ≥ k̃ − k` into `E = k̃ − k`. -/
theorem finrank_range_comp_eq_of_ker_le
    (p : Hc →ₗ[F] Hb) (τ : Hb →ₗ[F] Hc)
    (hexact : ker p = range τ) (hle : ker τ ≤ range p) :
    finrank F (range (τ ∘ₗ p)) = finrank F Hc - finrank F Hb := by
  have hid := finrank_range_comp_add_eq p τ hexact
  rw [inf_of_le_right hle] at hid
  omega

end BBBocksteinRank
end Homological
end Stabilizer
end Quantum
