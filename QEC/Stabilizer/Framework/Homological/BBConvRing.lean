/-
# The group-algebra ↔ convolution bridge (A13 L2, Phase 2 keystone)

The repo represents BB chains as functions `G → ZMod 2` with the standalone
convolution `conv` (`BBChainComplex.lean`), while the element form
(`BocksteinLift`) and the L2a freeness (`BBEpsFreeGroupAlgebra`) live in the
group algebra `AddMonoidAlgebra (ZMod 2) G` (with its convolution *product*).
`G → ZMod 2` carries the *pointwise* ring structure by default, so the two
cannot be the same typeclass instance; this file supplies the explicit
`ZMod 2`-linear equivalence identifying them and shows it carries the
group-algebra product to `conv`:

* `convEquiv : AddMonoidAlgebra (ZMod 2) G ≃ₗ[ZMod 2] (G → ZMod 2)`.
* `convEquiv_mul` — `convEquiv (a * b) = conv (convEquiv a) (convEquiv b)`:
  the group-algebra product **is** the repo's `conv`.
* `conv_convEquiv_single` — `conv (convEquiv (single s 1)) v = translate (-s) v`:
  multiplication by a group element is a translation, so the deck operator
  `ε = 1 + x^σ` of `BBEpsFreeGroupAlgebra` acts on 0/2-chains as
  `v ↦ v + translate (-σ) v` (`= v + σv` when `σ` has order 2, the repo's
  `deckShift0`).

This is the standard-but-verbose transport identified in the L2 plan
(§2.3, decision 2): it lets the element form's `Ann(ε) = (ε³)` and L2a's
`EpsFree` speak about the repo's actual chain-level deck action.  The
remaining L2 gap (the `seamC`↔connecting-map identification carrying the
element fact onto `BBTransferH1.BocksteinVanishes`) builds on this bridge.
-/

import QEC.Stabilizer.Framework.Homological.BBChainComplex
import Mathlib.Algebra.MonoidAlgebra.Basic

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open scoped BigOperators

variable {G : Type} [Fintype G]

/-- The `ZMod 2`-linear equivalence `𝔽₂[G] = (G →₀ 𝔽₂) ≃ (G → 𝔽₂)`
identifying the group algebra with the repo's function-space chains. -/
noncomputable def convEquiv :
    AddMonoidAlgebra (ZMod 2) G ≃ₗ[ZMod 2] (G → ZMod 2) :=
  Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) G

@[simp] lemma convEquiv_apply (a : AddMonoidAlgebra (ZMod 2) G) (g : G) :
    convEquiv a g = a g := rfl

@[simp] lemma convEquiv_symm_apply (a : G → ZMod 2) (g : G) :
    (convEquiv.symm a) g = a g := rfl

variable [AddCommGroup G]

/-- **Convolution is the group-algebra product.** Under `convEquiv` the
multiplication of `𝔽₂[G]` is exactly the repo's `conv`. -/
lemma convEquiv_mul (a b : AddMonoidAlgebra (ZMod 2) G) :
    convEquiv (a * b) = convEquiv a ⋆ convEquiv b := by
  classical
  funext g
  rw [convEquiv_apply, conv_apply]
  -- the antidiagonal of `g` indexed by the first coordinate
  have hinj : Function.Injective (fun h : G => (h, g - h)) :=
    fun x y hxy => (Prod.ext_iff.mp hxy).1
  have hs : ∀ {p : G × G},
      p ∈ (Finset.univ.map ⟨fun h => (h, g - h), hinj⟩) ↔ p.1 + p.2 = g := by
    intro p
    simp only [Finset.mem_map, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨h, rfl⟩
      exact add_sub_cancel _ _
    · intro hp
      exact ⟨p.1, Prod.ext rfl (by rw [eq_sub_of_add_eq' hp])⟩
  rw [AddMonoidAlgebra.mul_apply_antidiagonal a b g _ hs, Finset.sum_map]
  rfl

/-- Multiplication by a group generator is a translation: on `0`/`2`-chains
`conv (x^s) v = translate (-s) v`.  (`x^s := convEquiv (single s 1)`, the
indicator of `s`.) -/
lemma conv_convEquiv_single (s : G) (v : G → ZMod 2) :
    convEquiv (AddMonoidAlgebra.single s 1) ⋆ v = translate (-s) v := by
  classical
  funext g
  rw [conv_apply, translate_apply, Finset.sum_eq_single s]
  · rw [convEquiv_apply, AddMonoidAlgebra.single_apply, if_pos rfl, one_mul,
      sub_eq_add_neg]
  · intro h _ hhs
    rw [convEquiv_apply, AddMonoidAlgebra.single_apply, if_neg (Ne.symm hhs),
      zero_mul]
  · intro hcon
    exact absurd (Finset.mem_univ s) hcon

/-- The deck operator `ε = 1 + x^σ` of `BBEpsFreeGroupAlgebra`, transported
through `convEquiv`, acts on `0`/`2`-chains as `v ↦ v + translate (-σ) v`
— the repo's `v + σv` once `σ` has order 2. -/
lemma conv_convEquiv_one_add_single (σ : G) (v : G → ZMod 2) :
    convEquiv (1 + AddMonoidAlgebra.single σ 1) ⋆ v
      = v + translate (-σ) v := by
  classical
  have h1 : convEquiv (1 + AddMonoidAlgebra.single σ (1 : ZMod 2))
      = convEquiv 1 + convEquiv (AddMonoidAlgebra.single σ 1) := map_add _ _ _
  rw [h1, conv_add_left]
  have hone : convEquiv (1 : AddMonoidAlgebra (ZMod 2) G) ⋆ v = v := by
    funext g
    rw [conv_apply, Finset.sum_eq_single (0 : G)]
    · rw [convEquiv_apply, AddMonoidAlgebra.one_def, AddMonoidAlgebra.single_apply,
        if_pos rfl, one_mul, sub_zero]
    · intro h _ hh0
      rw [convEquiv_apply, AddMonoidAlgebra.one_def, AddMonoidAlgebra.single_apply,
        if_neg (Ne.symm hh0), zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ (0 : G)) hcon
  rw [hone, conv_convEquiv_single]

end BB
end Homological
end Stabilizer
end Quantum
