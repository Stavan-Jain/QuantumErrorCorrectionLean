/-
# Gross ↔ bb72 cover-transfer maps

Instantiates the generic covering machinery (`Covering.lean`) on the 2:1
cover `coverPi : Z₁₂ × Z₆ →+ Z₆ × Z₆`:

* `coverPush0/1` — pushforward `p` (fiber summation) on 0- and 1-chains
* `coverPull0/1` — pullback `τ = · ∘ π` on 0- and 1-chains
* both are chain maps between `grossComplex` and `bb72Complex`
* `coverPush1 ∘ coverPull1 = 0`, `coverPull1` injective, `coverPush1`
  surjective, `ker coverPush1 = range coverPull1`
* `coverPull1_coverPush1 : τ(p(v)) = v + σv` (how the deck homotopy (R)
  enters the Phase-1 distance assembly)
* the weight identity `chainWeight v = chainWeight (p v) + overlapCount v`
  and cycle-membership transfer in both directions.

## Convention bridge (lab notes → repo)

Repo convention: `∂₂ f = (A⋆f | B⋆f)`, `∂₁ c = B⋆c_L + A⋆c_R`; cycle
condition `B⋆v_L = A⋆v_R`.  **Repo-left = lab-right.**
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Gross.Defs

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open scoped BigOperators

-- Defeq checks through `fiberSum (Prod.map ⇑coverPi id)` (the `coverPush1`
-- bridges and `change`-steps below) unfold deep `Prod`/`ZMod` instance
-- chains and exceed the default recursion depth of 512.
set_option maxRecDepth 4096

/-! ## Deck data on qubits (`C1 = GrossGroup × Fin 2`) -/

/-- The deck involution on qubit indices: shift the group coordinate by `deckS`,
keep the block. -/
def deckSigma1 : GrossGroup × Fin 2 → GrossGroup × Fin 2 :=
  fun p => (p.1 + deckS, p.2)

@[simp] lemma deckSigma1_apply (p : GrossGroup × Fin 2) :
    deckSigma1 p = (p.1 + deckS, p.2) := rfl

lemma deckShift1_eq_comp (v : GrossGroup × Fin 2 → ZMod 2) :
    deckShift1 v = v ∘ deckSigma1 := rfl

theorem deckSigma1_ne : ∀ p : GrossGroup × Fin 2, deckSigma1 p ≠ p := by
  intro p hp
  have h1 : p.1 + deckS = p.1 := congrArg Prod.fst hp
  have h2 : deckS = 0 := by
    have := congrArg (fun x => x - p.1) h1
    simpa [add_comm, add_sub_cancel_right] using this
  exact deckS_ne_zero h2

/-- The fibers of `Prod.map coverPi id` on qubit indices are the
`deckSigma1`-orbits. -/
theorem coverPi_prodMap_fiber :
    ∀ q q' : GrossGroup × Fin 2,
      Prod.map ⇑coverPi id q' = Prod.map ⇑coverPi id q
        ↔ q' = q ∨ q' = deckSigma1 q := by
  intro q q'
  obtain ⟨g, j⟩ := q
  obtain ⟨g', j'⟩ := q'
  change (coverPi g', j') = (coverPi g, j)
    ↔ (g', j') = (g, j) ∨ (g', j') = (g + deckS, j)
  constructor
  · intro h
    have hg : coverPi g' = coverPi g := congrArg Prod.fst h
    have hj : j' = j := congrArg Prod.snd h
    rcases (coverPi_fiber g g').mp hg with h1 | h1
    · exact Or.inl (by rw [h1, hj])
    · exact Or.inr (by rw [h1, hj])
  · rintro (h | h)
    · have hg : g' = g := congrArg Prod.fst h
      have hj : j' = j := congrArg Prod.snd h
      rw [hg, hj]
    · have hg : g' = g + deckS := congrArg Prod.fst h
      have hj : j' = j := congrArg Prod.snd h
      rw [hg, hj, (coverPi_fiber g (g + deckS)).mpr (Or.inr rfl)]

/-- Section of `Prod.map coverPi id` on qubit indices. -/
def coverSec1 : BaseGroup × Fin 2 → GrossGroup × Fin 2 := Prod.map coverSec id

theorem coverPi_prodMap_coverSec1 :
    ∀ p : BaseGroup × Fin 2, Prod.map ⇑coverPi id (coverSec1 p) = p := by
  intro p
  obtain ⟨b, j⟩ := p
  change (coverPi (coverSec (b, j).1), j) = (b, j)
  rw [coverPi_coverSec]

/-! ## The four transfer maps -/

/-- Pushforward on 0- and 2-chains. -/
noncomputable def coverPush0 :
    (GrossGroup → ZMod 2) →ₗ[ZMod 2] (BaseGroup → ZMod 2) :=
  fiberSum ⇑coverPi

/-- Pushforward on 1-chains (qubits). -/
noncomputable def coverPush1 :
    (GrossGroup × Fin 2 → ZMod 2) →ₗ[ZMod 2] (BaseGroup × Fin 2 → ZMod 2) :=
  fiberSum (Prod.map ⇑coverPi id)

/-- Pullback on 0- and 2-chains. -/
noncomputable def coverPull0 :
    (BaseGroup → ZMod 2) →ₗ[ZMod 2] (GrossGroup → ZMod 2) :=
  LinearMap.funLeft (ZMod 2) (ZMod 2) ⇑coverPi

/-- Pullback on 1-chains (qubits). -/
noncomputable def coverPull1 :
    (BaseGroup × Fin 2 → ZMod 2) →ₗ[ZMod 2] (GrossGroup × Fin 2 → ZMod 2) :=
  LinearMap.funLeft (ZMod 2) (ZMod 2) (Prod.map ⇑coverPi id)

@[simp] lemma coverPush0_apply (v : GrossGroup → ZMod 2) :
    coverPush0 v = fiberSumFn ⇑coverPi v := rfl

@[simp] lemma coverPush1_apply (v : GrossGroup × Fin 2 → ZMod 2) :
    coverPush1 v = fiberSumFn (Prod.map ⇑coverPi id) v := rfl

@[simp] lemma coverPull0_apply (u : BaseGroup → ZMod 2) :
    coverPull0 u = u ∘ ⇑coverPi := rfl

@[simp] lemma coverPull1_apply (u : BaseGroup × Fin 2 → ZMod 2) :
    coverPull1 u = u ∘ Prod.map ⇑coverPi id := rfl

/-! ## The polynomials descend -/

theorem coverPush_grossA : fiberSumFn ⇑coverPi grossA = baseA := by
  decide +kernel

theorem coverPush_grossB : fiberSumFn ⇑coverPi grossB = baseB := by
  decide +kernel

/-! ## Chain maps -/

/-- `p` is a chain map at level 1: `p₀ ∘ ∂₁ = ∂₁ ∘ p₁`. -/
theorem coverPush_boundary1_comm (c : GrossGroup × Fin 2 → ZMod 2) :
    coverPush0 (grossComplex.boundary1 c)
      = bb72Complex.boundary1 (coverPush1 c) := by
  change fiberSumFn ⇑coverPi (bbBoundary1Fn grossA grossB c)
    = bbBoundary1Fn baseA baseB (fiberSumFn (Prod.map ⇑coverPi id) c)
  exact fiberSum_bbBoundary1Fn coverPi grossA grossB baseA baseB
    coverPush_grossA coverPush_grossB c

/-- `p` is a chain map at level 2: `p₁ ∘ ∂₂ = ∂₂ ∘ p₂`. -/
theorem coverPush_boundary2_comm (f : GrossGroup → ZMod 2) :
    coverPush1 (grossComplex.boundary2 f)
      = bb72Complex.boundary2 (coverPush0 f) := by
  change fiberSumFn (Prod.map ⇑coverPi id) (bbBoundary2Fn grossA grossB f)
    = bbBoundary2Fn baseA baseB (fiberSumFn ⇑coverPi f)
  exact fiberSum_bbBoundary2Fn coverPi grossA grossB baseA baseB
    coverPush_grossA coverPush_grossB f

/-- `τ` is a chain map at level 1: `∂₁ ∘ τ₁ = τ₀ ∘ ∂₁`. -/
theorem coverPull_boundary1_comm (u : BaseGroup × Fin 2 → ZMod 2) :
    grossComplex.boundary1 (coverPull1 u)
      = coverPull0 (bb72Complex.boundary1 u) := by
  change bbBoundary1Fn grossA grossB (u ∘ Prod.map ⇑coverPi id)
    = (bbBoundary1Fn baseA baseB u) ∘ ⇑coverPi
  exact pullback_bbBoundary1Fn coverPi grossA grossB baseA baseB
    coverPush_grossA coverPush_grossB u

/-- `τ` is a chain map at level 2: `∂₂ ∘ τ₂ = τ₁ ∘ ∂₂`. -/
theorem coverPull_boundary2_comm (f : BaseGroup → ZMod 2) :
    grossComplex.boundary2 (coverPull0 f)
      = coverPull1 (bb72Complex.boundary2 f) := by
  change bbBoundary2Fn grossA grossB (f ∘ ⇑coverPi)
    = (bbBoundary2Fn baseA baseB f) ∘ Prod.map ⇑coverPi id
  exact pullback_bbBoundary2Fn coverPi grossA grossB baseA baseB
    coverPush_grossA coverPush_grossB f

/-! ## Exactness package on 1-chains -/

/-- `p ∘ τ = 0` on 1-chains (each fiber contributes twice in char 2). -/
theorem coverPush1_coverPull1_eq_zero (u : BaseGroup × Fin 2 → ZMod 2) :
    coverPush1 (coverPull1 u) = 0 :=
  fiberSumFn_pullback deckSigma1_ne coverPi_prodMap_fiber u

theorem coverPi_prodMap_surjective :
    Function.Surjective (Prod.map ⇑coverPi (id : Fin 2 → Fin 2)) :=
  Function.Surjective.prodMap coverPi_surjective Function.surjective_id

theorem coverPull1_injective : Function.Injective ⇑coverPull1 :=
  LinearMap.funLeft_injective_of_surjective (ZMod 2) (ZMod 2) _
    coverPi_prodMap_surjective

theorem coverPull0_injective : Function.Injective ⇑coverPull0 :=
  LinearMap.funLeft_injective_of_surjective (ZMod 2) (ZMod 2) _
    coverPi_surjective

theorem coverPush1_surjective : Function.Surjective ⇑coverPush1 := fun u =>
  ⟨lift0 (Prod.map ⇑coverPi id) coverSec1 u,
    fiberSumFn_lift0 coverPi_prodMap_coverSec1 u⟩

/-- `ker p = range τ` on 1-chains. -/
theorem coverPush1_eq_zero_iff (v : GrossGroup × Fin 2 → ZMod 2) :
    coverPush1 v = 0 ↔ ∃ u : BaseGroup × Fin 2 → ZMod 2, v = coverPull1 u :=
  fiberSumFn_eq_zero_iff deckSigma1_ne coverPi_prodMap_fiber
    coverPi_prodMap_coverSec1 v

/-- The chain identity `τ(p(v)) = v + σv` = `(1 + σ)v`. This is how the deck
homotopy (R) enters the Phase-1 distance assembly. -/
theorem coverPull1_coverPush1 (v : GrossGroup × Fin 2 → ZMod 2) :
    coverPull1 (coverPush1 v) = v + deckShift1 v := by
  funext p
  change fiberSumFn (Prod.map ⇑coverPi id) v (Prod.map ⇑coverPi id p)
    = v p + v (p.1 + deckS, p.2)
  rw [fiberSumFn_pair deckSigma1_ne coverPi_prodMap_fiber v p]
  rfl

/-! ## Weight identity -/

/-- The number of qubits in the support of `v` whose deck partner is also in the
support. Counts each doubly-covered fiber twice (matching the informal
`2 · overlap`). -/
noncomputable def overlapCount (v : GrossGroup × Fin 2 → ZMod 2) : ℕ :=
  (Finset.univ.filter fun p : GrossGroup × Fin 2 =>
    v p ≠ 0 ∧ v (p.1 + deckS, p.2) ≠ 0).card

/-- `chainWeight` of a gross 1-chain in terms of raw `Finset` data. -/
lemma grossComplex_chainWeight_eq (v : GrossGroup × Fin 2 → ZMod 2) :
    grossComplex.chainWeight v
      = (Finset.univ.filter fun p : GrossGroup × Fin 2 => v p ≠ 0).card := rfl

/-- `chainWeight` of a base 1-chain in terms of raw `Finset` data. -/
lemma bb72Complex_chainWeight_eq (u : BaseGroup × Fin 2 → ZMod 2) :
    bb72Complex.chainWeight u
      = (Finset.univ.filter fun p : BaseGroup × Fin 2 => u p ≠ 0).card := rfl

/-- Weight identity for the gross → bb72 pushforward: `|v| = |p(v)| + overlap`.
-/
theorem gross_chainWeight_eq (v : GrossGroup × Fin 2 → ZMod 2) :
    grossComplex.chainWeight v
      = bb72Complex.chainWeight (coverPush1 v) + overlapCount v := by
  rw [grossComplex_chainWeight_eq, bb72Complex_chainWeight_eq,
    coverPush1_apply, overlapCount]
  exact card_support_fiberSum_add_overlap deckSigma1_ne coverPi_prodMap_fiber v

/-- Pushing forward can only shrink chain weight. -/
theorem chainWeight_coverPush_le (v : GrossGroup × Fin 2 → ZMod 2) :
    bb72Complex.chainWeight (coverPush1 v) ≤ grossComplex.chainWeight v := by
  rw [gross_chainWeight_eq v]
  exact Nat.le_add_right _ _

/-- Pulling back exactly doubles chain weight (each base qubit in the support
contributes its full two-point fiber). -/
theorem chainWeight_coverPull1 (u : BaseGroup × Fin 2 → ZMod 2) :
    grossComplex.chainWeight (coverPull1 u) = 2 * bb72Complex.chainWeight u := by
  rw [grossComplex_chainWeight_eq, bb72Complex_chainWeight_eq, coverPull1_apply]
  exact card_support_pullback deckSigma1_ne coverPi_prodMap_fiber
    coverPi_prodMap_coverSec1 u

/-! ## Cycle-membership transfer -/

/-- Pushforwards of cycles are cycles. -/
theorem coverPush1_mem_cycles {v : GrossGroup × Fin 2 → ZMod 2}
    (hv : v ∈ grossComplex.cycles) :
    coverPush1 v ∈ bb72Complex.cycles := by
  have hv' : grossComplex.boundary1 v = 0 := hv
  have hgoal : bb72Complex.boundary1 (coverPush1 v) = 0 := by
    rw [← coverPush_boundary1_comm, hv']
    exact map_zero coverPush0
  exact hgoal

/-- Pullbacks of cycles are cycles. -/
theorem coverPull1_mem_cycles {u : BaseGroup × Fin 2 → ZMod 2}
    (hu : u ∈ bb72Complex.cycles) :
    coverPull1 u ∈ grossComplex.cycles := by
  have hu' : bb72Complex.boundary1 u = 0 := hu
  have hgoal : grossComplex.boundary1 (coverPull1 u) = 0 := by
    rw [coverPull_boundary1_comm, hu']
    exact map_zero coverPull0
  exact hgoal

/-- Pushforwards of boundaries are boundaries. -/
theorem coverPush1_mem_boundaries {v : GrossGroup × Fin 2 → ZMod 2}
    (hv : v ∈ grossComplex.boundaries) :
    coverPush1 v ∈ bb72Complex.boundaries := by
  obtain ⟨f, rfl⟩ := hv
  exact ⟨coverPush0 f, (coverPush_boundary2_comm f).symm⟩

/-- Pullbacks of boundaries are boundaries. -/
theorem coverPull1_mem_boundaries {u : BaseGroup × Fin 2 → ZMod 2}
    (hu : u ∈ bb72Complex.boundaries) :
    coverPull1 u ∈ grossComplex.boundaries := by
  obtain ⟨f, rfl⟩ := hu
  exact ⟨coverPull0 f, coverPull_boundary2_comm f⟩

end BB
end Homological
end Stabilizer
end Quantum
