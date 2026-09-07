/-
# Bivariate bicycle codes: the gross code and its bb72 base — definitions

The gross code is the `[[144, 12, 12]]` bivariate bicycle code of
Bravyi–Cross–Gambetta–Maslov–Rall–Yoder (Nature 627, 778 (2024)), with
group `Z₁₂ × Z₆` and polynomials `A = x³ + y + y²`, `B = y³ + x + x²`.
Reducing the `x`-coordinate mod 6 gives a 2:1 covering onto the
`[[72, 12, 6]]` code with the same polynomials over `Z₆ × Z₆` (the "base").

This file instantiates both chain complexes on the generic `bbChainComplex`
and builds the covering data: the projection `coverPi`, the deck element
`deckS = x⁶`, a section `coverSec`, and the deck-shift operators on chains.

## Convention bridge (lab notes → repo) — IMPORTANT

Repo convention (`BBChainComplex.lean`): `∂₂ f = (A⋆f | B⋆f)`,
`∂₁ c = B⋆c_L + A⋆c_R`; cycle condition `B⋆v_L = A⋆v_R`.
**Repo-left = lab-right.**  Consequently the witness chain (`Witness.lean`)
puts `zStar` in the *right* block, and the homotopy chain
(`DeckHomotopy.lean`) is built from `rightHalf v`.
-/

import QEC.Stabilizer.Framework.Homological.Covering
import QEC.Stabilizer.Framework.Homological.BBDuality

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

/-! ## Groups -/

/-- The gross-code group `Z₁₂ × Z₆` (`x` has order 12, `y` has order 6). -/
abbrev GrossGroup : Type := ZMod 12 × ZMod 6

/-- The base-code group `Z₆ × Z₆` for the `[[72, 12, 6]]` quotient code. -/
abbrev BaseGroup : Type := ZMod 6 × ZMod 6

/-! ## Polynomials

Group-algebra elements are `ZMod 2`-valued indicator functions of their
supports.  Monomial `xᵃyᵇ` ↦ the point `(a, b)`; `poly[x^3 + y + y^2]`
(`BBChainComplex.lean`) expands to exactly the
`fun g => if g = (3, 0) ∨ g = (0, 1) ∨ g = (0, 2) then 1 else 0` indicator. -/

/-- Gross-code `A = x³ + y + y²`. -/
def grossA : GrossGroup → ZMod 2 := poly[x^3 + y + y^2]

/-- Gross-code `B = y³ + x + x²`. -/
def grossB : GrossGroup → ZMod 2 := poly[y^3 + x + x^2]

/-- Base-code `A = x³ + y + y²` (over `Z₆ × Z₆`). -/
def baseA : BaseGroup → ZMod 2 := poly[x^3 + y + y^2]

/-- Base-code `B = y³ + x + x²` (over `Z₆ × Z₆`). -/
def baseB : BaseGroup → ZMod 2 := poly[y^3 + x + x^2]

/-- The polynomial `1 + x²` (homotopy-chain prefactor). -/
def onePlusX2 : GrossGroup → ZMod 2 := poly[1 + x^2]

/-- `B ⋆ B = 1 + x² + x⁴` over the gross group (squares kill cross terms in
char 2, and `y⁶ = 1`). -/
def bSquaredPoly : GrossGroup → ZMod 2 := poly[1 + x^2 + x^4]

/-- The polynomial `1 + x⁶ = 1 + deck`. -/
def onePlusX6 : GrossGroup → ZMod 2 := poly[1 + x^6]

/-! ## Chain complexes -/

/-- The gross `[[144, 12, 12]]` chain complex. -/
noncomputable def grossComplex : HomologicalCode := bbChainComplex grossA grossB

/-- The base `[[72, 12, 6]]` chain complex. -/
noncomputable def bb72Complex : HomologicalCode := bbChainComplex baseA baseB

theorem grossComplex_numQubits : grossComplex.numQubits = 144 := by
  change bbNumQubits GrossGroup = 144
  unfold bbNumQubits
  rw [Fintype.card_prod, ZMod.card, ZMod.card]

theorem bb72Complex_numQubits : bb72Complex.numQubits = 72 := by
  change bbNumQubits BaseGroup = 72
  unfold bbNumQubits
  rw [Fintype.card_prod, ZMod.card]

/-! ## Covering data -/

/-- The deck element `x⁶`: generator of the kernel of the covering map. -/
def deckS : GrossGroup := (6, 0)

theorem deckS_ne_zero : deckS ≠ 0 := by decide

theorem neg_deckS : -deckS = deckS := by decide

/-- The 2:1 covering projection `Z₁₂ × Z₆ →+ Z₆ × Z₆` (reduce `x` mod 6). -/
def coverPi : GrossGroup →+ BaseGroup :=
  AddMonoidHom.prodMap
    (ZMod.castHom (by norm_num : (6 : ℕ) ∣ 12) (ZMod 6)).toAddMonoidHom
    (AddMonoidHom.id (ZMod 6))

/-- Fibers of `coverPi` are deck orbits: `π g' = π g ↔ g' = g ∨ g' = g + deckS`. -/
theorem coverPi_fiber :
    ∀ g g' : GrossGroup, coverPi g' = coverPi g ↔ g' = g ∨ g' = g + deckS := by
  decide +kernel

theorem coverPi_surjective : Function.Surjective ⇑coverPi := by
  decide +kernel

/-- A set-theoretic section of `coverPi` (lift the `x`-coordinate by its
canonical representative). -/
def coverSec : BaseGroup → GrossGroup := fun p => ((p.1.val : ZMod 12), p.2)

theorem coverPi_coverSec : ∀ p : BaseGroup, coverPi (coverSec p) = p := by
  decide +kernel

/-! ## Deck shifts on chains -/

/-- Deck shift on 0- and 2-chains: `(σ v)(g) = v (g + deckS)`. -/
def deckShift0 (v : GrossGroup → ZMod 2) : GrossGroup → ZMod 2 :=
  fun g => v (g + deckS)

/-- Deck shift on 1-chains (qubits): shift the group coordinate, keep the
block. -/
def deckShift1 (v : GrossGroup × Fin 2 → ZMod 2) : GrossGroup × Fin 2 → ZMod 2 :=
  fun p => v (p.1 + deckS, p.2)

@[simp] lemma deckShift0_apply (v : GrossGroup → ZMod 2) (g : GrossGroup) :
    deckShift0 v g = v (g + deckS) := rfl

@[simp] lemma deckShift1_apply (v : GrossGroup × Fin 2 → ZMod 2)
    (p : GrossGroup × Fin 2) :
    deckShift1 v p = v (p.1 + deckS, p.2) := rfl

end BB
end Homological
end Stabilizer
end Quantum
