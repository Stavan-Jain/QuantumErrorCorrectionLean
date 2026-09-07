/-
# Phase 4: the safe sector — the Smith-coset reduction to (M-im)

The safe-sector bound (`SafeSectorGe12`, A4 Part II) reduced to a single
named hypothesis, `MImBound` ((M-im), A4 §8/Theorem D: every chain in a
seam-coset `C(ζ) + im ∂₂`, `ζ ∈ ker ∂₂`, that is not itself a boundary has
weight ≥ 12).  The reduction — the lab's "safe sector sees exactly the Smith
classes" (`im pr_* ⊆ im Δ`, Entry 16; only this inclusion is load-bearing,
per the Entry-27 review) — is **proven here from the deck homotopy (R)**:

For a safe cycle `v` with `w := p(v)`, (R) gives `v + σv = ∂₂(z)` for the
explicit homotopy 2-chain `z`.  Splitting `z` into its two sheets
`z = lift(ζ₀) + σ·lift(ζ₁)` and reading the two sheet components of
`v + σv = ∂₂ z` (both equal `w`) gives

    w = N(ζ₀) + C(ζ₁)  and  w = C(ζ₀) + N(ζ₁),

where `N/C` are the sheet components of the lifted stabilizer (the seam
decomposition `N(ξ) + C(ξ) = ∂₂ ξ`).  Summing: `∂₂(ζ₀ + ζ₁) = w + w = 0`,
so `ζ := ζ₀ + ζ₁ ∈ ker ∂₂`; substituting back: `w = C(ζ) + ∂₂ ζ₀` — exactly
the Smith-coset form.  Then `|v| ≥ |w| ≥ 12` by (M-im).

## Convention bridge (lab notes → repo)

Repo convention: `∂₂ f = (A⋆f | B⋆f)`, `∂₁ c = B⋆c_L + A⋆c_R`.
**Repo-left = lab-right.**  Sheet 0 = the `coverSec` image; `C = seamC` is
the lab's `d2c` (seam-crossing part), `N = seamN` the `d2nc`.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Gross.DangerousSector

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open scoped BigOperators

-- Defeq checks through the lifted-stabilizer and pushforward bridges unfold
-- deep `Prod`/`ZMod` instance chains (same as `CoverTransfer.lean`).
set_option maxRecDepth 4096

/-! ## Sheet decomposition of cover 2-chains -/

/-- Sheet-0 restriction of a cover 2-chain. -/
def sheetC2_0 (z : GrossGroup → ZMod 2) : BaseGroup → ZMod 2 :=
  fun j => z (coverSec j)

/-- Sheet-1 restriction of a cover 2-chain. -/
def sheetC2_1 (z : GrossGroup → ZMod 2) : BaseGroup → ZMod 2 :=
  fun j => z (coverSec j + deckS)

lemma deckS_add_deckS : deckS + deckS = 0 := by decide

lemma coverPi_add_deckS (g : GrossGroup) : coverPi (g + deckS) = coverPi g :=
  (coverPi_fiber g (g + deckS)).mpr (Or.inr rfl)

/-- Every cover point is the section point of its fiber or its deck
partner. -/
lemma cover_point_dichotomy (g : GrossGroup) :
    g = coverSec (coverPi g) ∨ g = coverSec (coverPi g) + deckS :=
  (coverPi_fiber (coverSec (coverPi g)) g).mp (coverPi_coverSec (coverPi g)).symm

/-- A cover 2-chain is the sum of the lifts of its two sheets. -/
lemma liftC2_decomp (z : GrossGroup → ZMod 2) :
    z = liftC2 (sheetC2_0 z) + deckShift0 (liftC2 (sheetC2_1 z)) := by
  funext g
  rw [Pi.add_apply]
  rcases cover_point_dichotomy g with hg | hg
  · have h1 : liftC2 (sheetC2_0 z) g = z g := by
      change (if g = coverSec (coverPi g) then sheetC2_0 z (coverPi g) else 0)
        = z g
      rw [if_pos hg]
      change z (coverSec (coverPi g)) = z g
      rw [← hg]
    have h2 : deckShift0 (liftC2 (sheetC2_1 z)) g = 0 := by
      change (if g + deckS = coverSec (coverPi (g + deckS)) then
        sheetC2_1 z (coverPi (g + deckS)) else 0) = 0
      rw [if_neg ?_]
      intro hcon
      rw [coverPi_add_deckS, ← hg] at hcon
      apply deckS_ne_zero
      have hcon' : g + deckS = g + 0 := by rw [add_zero]; exact hcon
      exact add_left_cancel hcon'
    rw [h1, h2, add_zero]
  · have h1 : liftC2 (sheetC2_0 z) g = 0 := by
      change (if g = coverSec (coverPi g) then sheetC2_0 z (coverPi g) else 0)
        = 0
      rw [if_neg ?_]
      intro hcon
      have hcontra := hcon.symm.trans hg
      apply deckS_ne_zero
      have hg' : coverSec (coverPi g) + 0 = coverSec (coverPi g) + deckS := by
        rw [add_zero]; exact hcontra
      exact (add_left_cancel hg').symm
    have h2 : deckShift0 (liftC2 (sheetC2_1 z)) g = z g := by
      have hgd : g + deckS = coverSec (coverPi g) := by
        rw [hg, add_assoc, deckS_add_deckS, add_zero, coverPi_add_deckS,
          coverPi_coverSec]
      change (if g + deckS = coverSec (coverPi (g + deckS)) then
        sheetC2_1 z (coverPi (g + deckS)) else 0) = z g
      rw [coverPi_add_deckS, if_pos hgd]
      change z (coverSec (coverPi g) + deckS) = z g
      rw [← hg]
    rw [h1, h2, zero_add]

lemma liftC2_add (ξ η : BaseGroup → ZMod 2) :
    liftC2 (ξ + η) = liftC2 ξ + liftC2 η := by
  funext g
  change (if g = coverSec (coverPi g) then (ξ + η) (coverPi g) else 0)
    = (if g = coverSec (coverPi g) then ξ (coverPi g) else 0)
      + (if g = coverSec (coverPi g) then η (coverPi g) else 0)
  by_cases hg : g = coverSec (coverPi g)
  · rw [if_pos hg, if_pos hg, if_pos hg]
    rfl
  · rw [if_neg hg, if_neg hg, if_neg hg, add_zero]

/-! ## The seam decomposition `∂₂ = N + C` -/

/-- The non-crossing seam part: sheet-0 component of the lifted stabilizer
(the lab's `d2nc`). -/
def seamN (ξ : BaseGroup → ZMod 2) : BaseGroup × Fin 2 → ZMod 2 :=
  sheet0 (liftStab ξ)

/-- The seam-crossing part: sheet-1 component of the lifted stabilizer
(the lab's `d2c`).  The Smith connecting map at chain level is
`ζ ↦ seamC ζ` on 2-cycles. -/
def seamC (ξ : BaseGroup → ZMod 2) : BaseGroup × Fin 2 → ZMod 2 :=
  sheet1 (liftStab ξ)

/-- The seam split sums to the base boundary. -/
lemma seamN_add_seamC (ξ : BaseGroup → ZMod 2) (j : BaseGroup × Fin 2) :
    seamN ξ j + seamC ξ j = bbBoundary2Fn baseA baseB ξ j := by
  have h := sheet0_add_sheet1 (liftStab ξ) j
  rw [coverPush1_liftStab] at h
  exact h

lemma seamC_add (ξ η : BaseGroup → ZMod 2) :
    seamC (ξ + η) = seamC ξ + seamC η := by
  unfold seamC liftStab
  rw [liftC2_add, bbBoundary2Fn_add, sheet1_add]

/-! ## Deck-shift bookkeeping -/

lemma liftStab_deckShift (ξ : BaseGroup → ZMod 2) :
    bbBoundary2Fn grossA grossB (deckShift0 (liftC2 ξ))
      = deckShift1 (liftStab ξ) :=
  bbBoundary2Fn_translate grossA grossB deckS (liftC2 ξ)

lemma sheet0_deckShift1 (s : GrossGroup × Fin 2 → ZMod 2) :
    sheet0 (deckShift1 s) = sheet1 s := rfl

lemma sheet1_deckShift1 (s : GrossGroup × Fin 2 → ZMod 2) :
    sheet1 (deckShift1 s) = sheet0 s := by
  funext q
  change s ((coverSec1 q).1 + deckS + deckS, (coverSec1 q).2) = s (coverSec1 q)
  rw [add_assoc, deckS_add_deckS, add_zero]

/-- Sheet 0 of `v + σv` is the pushforward. -/
lemma sheet0_self_add_deck (v : GrossGroup × Fin 2 → ZMod 2)
    (j : BaseGroup × Fin 2) :
    sheet0 (v + deckShift1 v) j = coverPush1 v j := by
  rw [sheet0_add, Pi.add_apply, sheet0_deckShift1]
  exact sheet0_add_sheet1 v j

/-- Sheet 1 of `v + σv` is also the pushforward. -/
lemma sheet1_self_add_deck (v : GrossGroup × Fin 2 → ZMod 2)
    (j : BaseGroup × Fin 2) :
    sheet1 (v + deckShift1 v) j = coverPush1 v j := by
  rw [sheet1_add, Pi.add_apply, sheet1_deckShift1, add_comm]
  exact sheet0_add_sheet1 v j

/-! ## The (M-im) hypothesis and the reduction -/

/-- **(M-im)** (A4 Part II / Theorem D): every chain in a Smith seam-coset
`seamC ζ + im ∂₂` (`ζ ∈ ker ∂₂`) that is not itself a base boundary has
weight ≥ 12.  This is the single remaining analytic input for the safe
sector; its paper proof is the confined-floor program of A4 §§9–13. -/
def MImBound : Prop :=
  ∀ ζ : BaseGroup → ZMod 2, bbBoundary2Fn baseA baseB ζ = 0 →
    ∀ f : BaseGroup → ZMod 2,
      seamC ζ + bbBoundary2Fn baseA baseB f ∉ bb72Complex.boundaries →
      12 ≤ bb72Complex.chainWeight (seamC ζ + bbBoundary2Fn baseA baseB f)

/-- **The safe-sector reduction**: (M-im) implies `SafeSectorGe12`.  The
Smith-coset membership of `p(v)` is derived from the deck homotopy (R). -/
theorem safe_sector_of_mim (hMim : MImBound) : SafeSectorGe12 := by
  intro v hv hb
  -- (R): v + σv = ∂₂(homotopyChain v)
  have hR : bbBoundary2Fn grossA grossB (homotopyChain v) = v + deckShift1 v :=
    bbBoundary2Fn_homotopyChain hv
  -- split the homotopy 2-chain into sheets
  have hsplit : v + deckShift1 v
      = liftStab (sheetC2_0 (homotopyChain v))
        + deckShift1 (liftStab (sheetC2_1 (homotopyChain v))) := by
    rw [← hR]
    conv_lhs => rw [liftC2_decomp (homotopyChain v)]
    rw [bbBoundary2Fn_add, liftStab_deckShift]
    rfl
  -- read the two sheet components: both equal w := p(v)
  have hw0 : ∀ j, coverPush1 v j
      = seamN (sheetC2_0 (homotopyChain v)) j
        + seamC (sheetC2_1 (homotopyChain v)) j := by
    intro j
    calc coverPush1 v j
        = sheet0 (v + deckShift1 v) j := (sheet0_self_add_deck v j).symm
      _ = sheet0 (liftStab (sheetC2_0 (homotopyChain v))
            + deckShift1 (liftStab (sheetC2_1 (homotopyChain v)))) j := by
          rw [hsplit]
      _ = seamN (sheetC2_0 (homotopyChain v)) j
            + seamC (sheetC2_1 (homotopyChain v)) j := by
          rw [sheet0_add, Pi.add_apply, sheet0_deckShift1]
          rfl
  have hw1 : ∀ j, coverPush1 v j
      = seamC (sheetC2_0 (homotopyChain v)) j
        + seamN (sheetC2_1 (homotopyChain v)) j := by
    intro j
    calc coverPush1 v j
        = sheet1 (v + deckShift1 v) j := (sheet1_self_add_deck v j).symm
      _ = sheet1 (liftStab (sheetC2_0 (homotopyChain v))
            + deckShift1 (liftStab (sheetC2_1 (homotopyChain v)))) j := by
          rw [hsplit]
      _ = seamC (sheetC2_0 (homotopyChain v)) j
            + seamN (sheetC2_1 (homotopyChain v)) j := by
          rw [sheet1_add, Pi.add_apply, sheet1_deckShift1]
          rfl
  -- the sheet sum is a 2-cycle
  have hker : bbBoundary2Fn baseA baseB
      (sheetC2_0 (homotopyChain v) + sheetC2_1 (homotopyChain v)) = 0 := by
    funext j
    rw [bbBoundary2Fn_add, Pi.add_apply, Pi.zero_apply]
    have hkey : ∀ n0 c0 n1 c1 w b0 b1 : ZMod 2,
        w = n0 + c1 → w = c0 + n1 → n0 + c0 = b0 → n1 + c1 = b1 →
        b0 + b1 = 0 := by decide
    exact hkey _ _ _ _ _ _ _ (hw0 j) (hw1 j)
      (seamN_add_seamC (sheetC2_0 (homotopyChain v)) j)
      (seamN_add_seamC (sheetC2_1 (homotopyChain v)) j)
  -- the Smith-coset form of w
  have hwform : coverPush1 v
      = seamC (sheetC2_0 (homotopyChain v) + sheetC2_1 (homotopyChain v))
        + bbBoundary2Fn baseA baseB (sheetC2_0 (homotopyChain v)) := by
    funext j
    rw [Pi.add_apply, seamC_add, Pi.add_apply]
    have hkey : ∀ n0 c0 c1 w b0 : ZMod 2,
        w = n0 + c1 → n0 + c0 = b0 → w = (c0 + c1) + b0 := by decide
    exact hkey _ _ _ _ _ (hw0 j)
      (seamN_add_seamC (sheetC2_0 (homotopyChain v)) j)
  -- conclude via (M-im)
  have h12 : 12 ≤ bb72Complex.chainWeight (coverPush1 v) := by
    rw [hwform]
    refine hMim _ hker _ ?_
    rw [← hwform]
    exact hb
  exact le_trans h12 (chainWeight_coverPush_le v)

/-! ## Warm-up: the connecting map lands in cycles, and the ≥ 6 floor

The chain-level Smith connecting map `ζ ↦ seamC ζ` carries 2-cycles to
1-cycles, so every element of a Smith seam-coset `seamC ζ + im ∂₂`
(`ζ ∈ ker ∂₂`) is itself a base 1-cycle.  Combined with the unconditional
base small-cycle theorem (`base_cycle_weight_ge_6`, A4 Theorem A) this gives
the ≥ 6 floor on the safe sector with no CRT engine — the honest partial
result toward the ≥ 12 target of `MImBound`.  The engine (A4 §§9–13) is what
lifts this 6 to 12; `seamC_mem_cycles` is the foundation it builds on, since
it is what makes `chainWeight (seamC ζ + ∂₂ f)` a *cycle* weight for the
confined-floor program to bound. -/

/-- **The chain-level Smith connecting map lands in cycles.**  For a base
2-cycle `ζ` (`∂₂ ζ = 0`), the seam-crossing component `seamC ζ` is a base
1-cycle.

The proof is exactness of the double cover, *not* seam geometry: `liftStab ζ`
is a gross 1-cycle (a gross boundary) that pushes forward to `∂₂ ζ = 0`, so
by `ker p = im τ` (`coverPush1_eq_zero_iff`) it equals `coverPull1 u` for a
base 1-chain `u`; `u` is a base cycle because `τ` is an injective chain map,
and `seamC ζ = seamN ζ = sheet0 (liftStab ζ) = u` (the first equality is
char 2 applied to `seamN ζ + seamC ζ = ∂₂ ζ = 0`). -/
theorem seamC_mem_cycles {ζ : BaseGroup → ZMod 2}
    (hζ : bbBoundary2Fn baseA baseB ζ = 0) :
    seamC ζ ∈ bb72Complex.cycles := by
  -- `liftStab ζ` is a gross cycle (it is a gross boundary)
  have hgross_cyc : liftStab ζ ∈ grossComplex.cycles :=
    grossComplex.boundaries_le_cycles (liftStab_mem_boundaries ζ)
  -- it pushes forward to `∂₂ ζ = 0`
  have hpush : coverPush1 (liftStab ζ) = 0 := by
    rw [coverPush1_liftStab]; exact hζ
  -- exactness `ker p = im τ`: `liftStab ζ = coverPull1 u` for some base 1-chain
  obtain ⟨u, hu⟩ := (coverPush1_eq_zero_iff _).mp hpush
  -- `u` is a base 1-cycle (pull the gross-cycle condition back along `τ`)
  have hu_cyc : u ∈ bb72Complex.cycles := by
    have h1 : grossComplex.boundary1 (coverPull1 u) = 0 := by
      rw [← hu]; exact hgross_cyc
    rw [coverPull_boundary1_comm] at h1
    have h2 : bb72Complex.boundary1 u = 0 := by
      apply coverPull0_injective
      rw [h1]
      exact (map_zero coverPull0).symm
    exact h2
  -- `seamN ζ = sheet0 (liftStab ζ) = sheet0 (coverPull1 u) = u`
  have hseamN : seamN ζ = u := by
    change sheet0 (liftStab ζ) = u
    rw [hu, sheet0_coverPull1]
  -- char 2: `seamN ζ + seamC ζ = ∂₂ ζ = 0`, hence `seamC ζ = seamN ζ = u`
  have hseamC : seamC ζ = u := by
    have hkey : ∀ a b : ZMod 2, a + b = 0 → b = a := by decide
    funext j
    have hsum := seamN_add_seamC ζ j
    rw [hseamN, hζ, Pi.zero_apply] at hsum
    exact hkey _ _ hsum
  rw [hseamC]; exact hu_cyc

/-- **(M-im) warm-up: the ≥ 6 floor on the safe sector.**  Every element of a
Smith seam-coset `seamC ζ + im ∂₂` (`ζ ∈ ker ∂₂`) that is not itself a base
boundary has weight ≥ 6.  This is `MImBound` with the target relaxed from 12
to 6: it is unconditional (no CRT engine), resting only on `seamC_mem_cycles`
and the base small-cycle theorem.  Discharging the full `MImBound` is the
A4 §§9–13 confined-floor program that lifts this 6 to 12. -/
theorem mim_bound_ge_6 :
    ∀ ζ : BaseGroup → ZMod 2, bbBoundary2Fn baseA baseB ζ = 0 →
      ∀ f : BaseGroup → ZMod 2,
        seamC ζ + bbBoundary2Fn baseA baseB f ∉ bb72Complex.boundaries →
        6 ≤ bb72Complex.chainWeight (seamC ζ + bbBoundary2Fn baseA baseB f) := by
  intro ζ hζ f hb
  have hbd : bbBoundary2Fn baseA baseB f ∈ bb72Complex.boundaries := ⟨f, rfl⟩
  have hcyc : seamC ζ + bbBoundary2Fn baseA baseB f ∈ bb72Complex.cycles :=
    Submodule.add_mem _ (seamC_mem_cycles hζ) (bb72Complex.boundaries_le_cycles hbd)
  have hne : seamC ζ + bbBoundary2Fn baseA baseB f ≠ 0 := by
    intro h0
    apply hb
    rw [h0]
    exact Submodule.zero_mem _
  rw [bb72Complex_chainWeight_eq]
  refine base_cycle_weight_ge_6 _ ?_ hne
  exact hcyc

/-! ## The final conditional assembly

`d(gross) = 12` from exactly the two CRT-engine inputs. -/

/-- **Conditional Pauli-level `d(gross) = 12` on the two CRT-engine
inputs**: the light-stabilizer classification (A4 §6.3) and (M-im)
(A4 Part II).  Everything else — Theorems A and B, the slice machinery, the
m-rungs, (R), the duality, the sector assembly, and the weight-12 witness —
is unconditionally proven in this development. -/
theorem gross_pauli_distance_eq_12_of_engine
    (hC : LightStabilizerClassification) (hMim : MImBound) :
    IsLeast {w : ℕ | ∃ g : NQubitPauliGroupElement grossComplex.numQubits,
      Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
        grossComplex.homologicalStabilizerGroup ∧
      NQubitPauliGroupElement.weight g = w} 12 :=
  gross_pauli_distance_eq_12_of_two_sectors
    (dangerous_sector_of_classification hC) (safe_sector_of_mim hMim)

/-- Chain-level version of the final conditional assembly. -/
theorem gross_chain_distance_eq_12_of_engine
    (hC : LightStabilizerClassification) (hMim : MImBound) :
    IsLeast {w : ℕ | ∃ v : GrossGroup × Fin 2 → ZMod 2,
      v ∈ grossComplex.cycles ∧ v ∉ grossComplex.boundaries ∧
      grossComplex.chainWeight v = w} 12 :=
  gross_chain_distance_eq_12_of_sectors base_distance_ge_6
    (dangerous_sector_of_classification hC) (safe_sector_of_mim hMim)

/-! ## Sparse pointwise form of the seam-crossing map (kernel-evaluation layer)

`seamC`'s definitional form evaluates a 72-term `Finset.sum` (`conv` over
`GrossGroup`) through the bundled `coverPi` tower at every point — opaque to
kernel reduction.  The lemmas below collapse it to three sheet-indicator
translate terms per block, which the kernel evaluates in a few hundred steps
per point.  This is the evaluation substrate for the seam-offset read-offs and
the seam covariance certificates (all kernel `decide`, no `native_decide`). -/

/-- Three-monomial sparse form of `conv`: convolving against an explicit
three-point indicator collapses the `Finset.sum` to three translates. -/
lemma conv_indicator3 {G : Type} [Fintype G] [AddCommGroup G] [DecidableEq G]
    (m₁ m₂ m₃ : G) (h₁₂ : m₁ ≠ m₂) (h₁₃ : m₁ ≠ m₃) (h₂₃ : m₂ ≠ m₃)
    (f : G → ZMod 2) (g : G) :
    ((fun h => if h = m₁ ∨ h = m₂ ∨ h = m₃ then 1 else 0) ⋆ f) g
      = f (g - m₁) + f (g - m₂) + f (g - m₃) := by
  have key : ∀ h : G,
      (if h = m₁ ∨ h = m₂ ∨ h = m₃ then (1 : ZMod 2) else 0) * f (g - h)
        = (if h = m₁ then f (g - h) else 0) + (if h = m₂ then f (g - h) else 0)
          + (if h = m₃ then f (g - h) else 0) := by
    intro h
    by_cases e₁ : h = m₁
    · subst e₁
      simp [h₁₂, h₁₃]
    · by_cases e₂ : h = m₂
      · subst e₂
        simp [e₁, h₂₃]
      · by_cases e₃ : h = m₃ <;> simp [e₁, e₂, e₃, Ne.symm h₁₃, Ne.symm h₂₃]
  rw [conv_apply, Finset.sum_congr rfl (fun h _ => key h)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq' Finset.univ m₁ (fun h => f (g - h)),
      Finset.sum_ite_eq' Finset.univ m₂ (fun h => f (g - h)),
      Finset.sum_ite_eq' Finset.univ m₃ (fun h => f (g - h))]
  simp

/-- The seam-crossing map in explicit sparse form: three sheet-indicator
translate terms per block, evaluated at the deck-shifted section point.
Kernel-evaluable pointwise (no `Finset.sum`, no bundled-hom towers). -/
def seamCSparse (ξ : BaseGroup → ZMod 2) : BaseGroup × Fin 2 → ZMod 2 := fun q =>
  if q.2 = 0 then
    liftC2 ξ (coverSec q.1 + deckS - (3, 0)) + liftC2 ξ (coverSec q.1 + deckS - (0, 1))
      + liftC2 ξ (coverSec q.1 + deckS - (0, 2))
  else
    liftC2 ξ (coverSec q.1 + deckS - (0, 3)) + liftC2 ξ (coverSec q.1 + deckS - (1, 0))
      + liftC2 ξ (coverSec q.1 + deckS - (2, 0))

/-- `seamC` agrees with its sparse form. -/
theorem seamC_eq_sparse (ξ : BaseGroup → ZMod 2) : seamC ξ = seamCSparse ξ := by
  funext q
  obtain ⟨p, j⟩ := q
  change liftStab ξ (deckSigma1 (coverSec1 (p, j))) = _
  rw [deckSigma1_apply]
  change bbBoundary2Fn grossA grossB (liftC2 ξ) ((coverSec1 (p, j)).1 + deckS, j) = _
  change (if j = 0 then (grossA ⋆ liftC2 ξ) (coverSec p + deckS)
        else (grossB ⋆ liftC2 ξ) (coverSec p + deckS)) = _
  have hA : (grossA ⋆ liftC2 ξ) (coverSec p + deckS)
      = liftC2 ξ (coverSec p + deckS - (3, 0)) + liftC2 ξ (coverSec p + deckS - (0, 1))
        + liftC2 ξ (coverSec p + deckS - (0, 2)) :=
    conv_indicator3 ((3, 0) : GrossGroup) (0, 1) (0, 2)
      (by decide) (by decide) (by decide) (liftC2 ξ) (coverSec p + deckS)
  have hB : (grossB ⋆ liftC2 ξ) (coverSec p + deckS)
      = liftC2 ξ (coverSec p + deckS - (0, 3)) + liftC2 ξ (coverSec p + deckS - (1, 0))
        + liftC2 ξ (coverSec p + deckS - (2, 0)) :=
    conv_indicator3 ((0, 3) : GrossGroup) (1, 0) (2, 0)
      (by decide) (by decide) (by decide) (liftC2 ξ) (coverSec p + deckS)
  by_cases hj : j = 0
  · rw [if_pos hj, hA]
    simp [seamCSparse, hj]
  · rw [if_neg hj, hB]
    simp [seamCSparse, hj]

end BB
end Homological
end Stabilizer
end Quantum
