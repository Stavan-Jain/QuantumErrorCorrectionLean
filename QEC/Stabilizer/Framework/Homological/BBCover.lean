/-
# Parametric free-ℤ₂ cover bundle for BB codes

`XDoubleCoverData G H` packages a bivariate-bicycle code over `G` presented
as the free ℤ₂ cover of a BB code over `H` along one doubled axis: the
projection `proj : G →+ H`, the deck translation `deckS` (the nonzero kernel
element), a set-theoretic section `sec`, and the two polynomial pairs with
their descent equations `fiberSumFn proj Ac = Ab`, `fiberSumFn proj Bc = Bb`.

From those five data fields and four proof obligations everything the gross
development built in `Codes/BivariateBicycle/CoverTransfer.lean` and the
sheet/seam plumbing of `DangerousSector.lean`/`SafeSector.lean` is derived
*generically*: transfer maps, chain-map identities, the exactness package,
the weight identities, the sheet decomposition, the lifted stabilizer, the
seam split `∂₂ = N + C`, and the chain-level Smith connecting map
(`seamC_mem_cycles`).  The doubling-template theorems consuming this bundle
live in `BBDoubling.lean`.

## Name map (parametric ↔ gross instantiation)

| here (`D : XDoubleCoverData G H`)  | gross (`Codes/BivariateBicycle/`)  |
|------------------------------------|------------------------------------|
| `D.proj`, `D.deckS`, `D.sec`       | `coverPi`, `deckS`, `coverSec`     |
| `D.Ac/Bc`, `D.Ab/Bb`               | `grossA/B`, `baseA/B`              |
| `D.coverComplex`, `D.baseComplex`  | `grossComplex`, `bb72Complex`      |
| `D.push0/1`, `D.pull0/1`           | `coverPush0/1`, `coverPull0/1`     |
| `D.deckSigma1`, `D.deckShift0/1`   | `deckSigma1`, `deckShift0/1`       |
| `D.sec1`                           | `coverSec1`                        |
| `D.sheet0/1`, `D.liftC2/liftStab`  | `sheet0/1`, `liftC2/liftStab`      |
| `D.seamN/seamC`                    | `seamN/seamC`                      |
| `D.chainWeight_sheet_eq`           | `gross_chainWeight_sheet_eq`       |

## Convention bridge (lab notes → repo)

Repo convention (`BBChainComplex.lean`): `∂₂ f = (A⋆f | B⋆f)`,
`∂₁ c = B⋆c_L + A⋆c_R`; cycle condition `B⋆v_L = A⋆v_R`.
**Repo-left = lab-right.**  Sheet 0 = the `sec` image.
-/

import QEC.Stabilizer.Framework.Homological.Covering
import QEC.Stabilizer.Framework.Homological.BBDuality

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open scoped BigOperators

-- Defeq checks through `fiberSum (Prod.map ⇑D.proj id)` and the lifted-
-- stabilizer bridges unfold deep `Prod`/`ZMod` instance chains, exactly as
-- in the gross instantiation (`CoverTransfer.lean`).
set_option maxRecDepth 4096

/-- The data of a BB code over `G` presented as a free ℤ₂ cover of a BB code
over `H` along one doubled axis. `proj` is the covering projection, `deckS` the
deck translation, `sec` a set-theoretic section, `Ac, Bc` the cover polynomials
and `Ab, Bb` their descents. -/
structure XDoubleCoverData (G H : Type)
    [Fintype G] [AddCommGroup G] [DecidableEq G]
    [Fintype H] [AddCommGroup H] [DecidableEq H] where
  /-- The covering projection (reduce the doubled axis). -/
  proj : G →+ H
  /-- The deck translation: the nonzero element of `ker proj`. -/
  deckS : G
  /-- A set-theoretic section of `proj`. -/
  sec : H → G
  /-- The cover-code polynomial `A`. -/
  Ac : G → ZMod 2
  /-- The cover-code polynomial `B`. -/
  Bc : G → ZMod 2
  /-- The base-code polynomial `A`. -/
  Ab : H → ZMod 2
  /-- The base-code polynomial `B`. -/
  Bb : H → ZMod 2
  /-- The deck translation is nonzero (the cover is genuinely 2:1). -/
  deckS_ne_zero : deckS ≠ 0
  /-- Fibers of `proj` are deck orbits. -/
  proj_fiber : ∀ g g' : G, proj g' = proj g ↔ g' = g ∨ g' = g + deckS
  /-- `sec` sections `proj`. -/
  proj_sec : ∀ p : H, proj (sec p) = p
  /-- The polynomial `A` descends. -/
  push_A : fiberSumFn ⇑proj Ac = Ab
  /-- The polynomial `B` descends. -/
  push_B : fiberSumFn ⇑proj Bc = Bb

namespace XDoubleCoverData

variable {G H : Type}
  [Fintype G] [AddCommGroup G] [DecidableEq G]
  [Fintype H] [AddCommGroup H] [DecidableEq H]
  (D : XDoubleCoverData G H)

/-! ## Derived group facts (lemmas, not fields) -/

lemma proj_deckS : D.proj D.deckS = 0 := by
  have h := (D.proj_fiber 0 D.deckS).mpr (Or.inr (zero_add D.deckS).symm)
  rwa [map_zero] at h

lemma deckS_add_deckS : D.deckS + D.deckS = 0 := by
  have h0 : D.proj 0 = D.proj D.deckS := by
    rw [map_zero, D.proj_deckS]
  rcases (D.proj_fiber D.deckS 0).mp h0 with h | h
  · exact absurd h.symm D.deckS_ne_zero
  · exact h.symm

lemma neg_deckS : -D.deckS = D.deckS :=
  neg_eq_of_add_eq_zero_left D.deckS_add_deckS

lemma proj_add_deckS (g : G) : D.proj (g + D.deckS) = D.proj g :=
  (D.proj_fiber g (g + D.deckS)).mpr (Or.inr rfl)

lemma proj_surjective : Function.Surjective ⇑D.proj := fun p =>
  ⟨D.sec p, D.proj_sec p⟩

/-- Every cover point is the section point of its fiber or its deck partner. -/
lemma point_dichotomy (g : G) :
    g = D.sec (D.proj g) ∨ g = D.sec (D.proj g) + D.deckS :=
  (D.proj_fiber (D.sec (D.proj g)) g).mp (D.proj_sec (D.proj g)).symm

/-! ## The two chain complexes -/

/-- The cover-code chain complex. -/
noncomputable def coverComplex : HomologicalCode := bbChainComplex D.Ac D.Bc

/-- The base-code chain complex. -/
noncomputable def baseComplex : HomologicalCode := bbChainComplex D.Ab D.Bb

/-! ## Deck data on chains -/

/-- The deck involution on qubit indices: shift the group coordinate by `deckS`,
keep the block. -/
def deckSigma1 : G × Fin 2 → G × Fin 2 :=
  fun p => (p.1 + D.deckS, p.2)

@[simp] lemma deckSigma1_apply (p : G × Fin 2) :
    D.deckSigma1 p = (p.1 + D.deckS, p.2) := rfl

/-- Deck shift on 0- and 2-chains: `(σ v)(g) = v (g + deckS)`. -/
def deckShift0 (v : G → ZMod 2) : G → ZMod 2 :=
  fun g => v (g + D.deckS)

/-- Deck shift on 1-chains (qubits): shift the group coordinate, keep the block.
-/
def deckShift1 (v : G × Fin 2 → ZMod 2) : G × Fin 2 → ZMod 2 :=
  fun p => v (p.1 + D.deckS, p.2)

@[simp] lemma deckShift0_apply (v : G → ZMod 2) (g : G) :
    D.deckShift0 v g = v (g + D.deckS) := rfl

@[simp] lemma deckShift1_apply (v : G × Fin 2 → ZMod 2) (p : G × Fin 2) :
    D.deckShift1 v p = v (p.1 + D.deckS, p.2) := rfl

lemma deckShift1_eq_comp (v : G × Fin 2 → ZMod 2) :
    D.deckShift1 v = v ∘ D.deckSigma1 := rfl

theorem deckSigma1_ne : ∀ p : G × Fin 2, D.deckSigma1 p ≠ p := by
  intro p hp
  have h1 : p.1 + D.deckS = p.1 := congrArg Prod.fst hp
  have h2 : D.deckS = 0 := by
    have := congrArg (fun x => x - p.1) h1
    simpa [add_comm, add_sub_cancel_right] using this
  exact D.deckS_ne_zero h2

/-- The fibers of `Prod.map proj id` on qubit indices are the
`deckSigma1`-orbits. -/
theorem proj_prodMap_fiber :
    ∀ q q' : G × Fin 2,
      Prod.map ⇑D.proj id q' = Prod.map ⇑D.proj id q
        ↔ q' = q ∨ q' = D.deckSigma1 q := by
  intro q q'
  obtain ⟨g, j⟩ := q
  obtain ⟨g', j'⟩ := q'
  change (D.proj g', j') = (D.proj g, j)
    ↔ (g', j') = (g, j) ∨ (g', j') = (g + D.deckS, j)
  constructor
  · intro h
    have hg : D.proj g' = D.proj g := congrArg Prod.fst h
    have hj : j' = j := congrArg Prod.snd h
    rcases (D.proj_fiber g g').mp hg with h1 | h1
    · exact Or.inl (by rw [h1, hj])
    · exact Or.inr (by rw [h1, hj])
  · rintro (h | h)
    · have hg : g' = g := congrArg Prod.fst h
      have hj : j' = j := congrArg Prod.snd h
      rw [hg, hj]
    · have hg : g' = g + D.deckS := congrArg Prod.fst h
      have hj : j' = j := congrArg Prod.snd h
      rw [hg, hj, (D.proj_fiber g (g + D.deckS)).mpr (Or.inr rfl)]

/-- Section of `Prod.map proj id` on qubit indices. -/
def sec1 : H × Fin 2 → G × Fin 2 := Prod.map D.sec id

theorem proj_prodMap_sec1 :
    ∀ p : H × Fin 2, Prod.map ⇑D.proj id (D.sec1 p) = p := by
  intro p
  obtain ⟨b, j⟩ := p
  change (D.proj (D.sec (b, j).1), j) = (b, j)
  rw [D.proj_sec]

/-! ## The four transfer maps -/

/-- Pushforward on 0- and 2-chains. -/
noncomputable def push0 :
    (G → ZMod 2) →ₗ[ZMod 2] (H → ZMod 2) :=
  fiberSum ⇑D.proj

/-- Pushforward on 1-chains (qubits). -/
noncomputable def push1 :
    (G × Fin 2 → ZMod 2) →ₗ[ZMod 2] (H × Fin 2 → ZMod 2) :=
  fiberSum (Prod.map ⇑D.proj id)

/-- Pullback on 0- and 2-chains. -/
noncomputable def pull0 :
    (H → ZMod 2) →ₗ[ZMod 2] (G → ZMod 2) :=
  LinearMap.funLeft (ZMod 2) (ZMod 2) ⇑D.proj

/-- Pullback on 1-chains (qubits). -/
noncomputable def pull1 :
    (H × Fin 2 → ZMod 2) →ₗ[ZMod 2] (G × Fin 2 → ZMod 2) :=
  LinearMap.funLeft (ZMod 2) (ZMod 2) (Prod.map ⇑D.proj id)

@[simp] lemma push0_apply (v : G → ZMod 2) :
    D.push0 v = fiberSumFn ⇑D.proj v := rfl

@[simp] lemma push1_apply (v : G × Fin 2 → ZMod 2) :
    D.push1 v = fiberSumFn (Prod.map ⇑D.proj id) v := rfl

@[simp] lemma pull0_apply (u : H → ZMod 2) :
    D.pull0 u = u ∘ ⇑D.proj := rfl

@[simp] lemma pull1_apply (u : H × Fin 2 → ZMod 2) :
    D.pull1 u = u ∘ Prod.map ⇑D.proj id := rfl

/-! ## Chain maps -/

/-- `p` is a chain map at level 1: `p₀ ∘ ∂₁ = ∂₁ ∘ p₁`. -/
theorem push_boundary1_comm (c : G × Fin 2 → ZMod 2) :
    D.push0 (D.coverComplex.boundary1 c)
      = D.baseComplex.boundary1 (D.push1 c) := by
  change fiberSumFn ⇑D.proj (bbBoundary1Fn D.Ac D.Bc c)
    = bbBoundary1Fn D.Ab D.Bb (fiberSumFn (Prod.map ⇑D.proj id) c)
  exact fiberSum_bbBoundary1Fn D.proj D.Ac D.Bc D.Ab D.Bb
    D.push_A D.push_B c

/-- `p` is a chain map at level 2: `p₁ ∘ ∂₂ = ∂₂ ∘ p₂`. -/
theorem push_boundary2_comm (f : G → ZMod 2) :
    D.push1 (D.coverComplex.boundary2 f)
      = D.baseComplex.boundary2 (D.push0 f) := by
  change fiberSumFn (Prod.map ⇑D.proj id) (bbBoundary2Fn D.Ac D.Bc f)
    = bbBoundary2Fn D.Ab D.Bb (fiberSumFn ⇑D.proj f)
  exact fiberSum_bbBoundary2Fn D.proj D.Ac D.Bc D.Ab D.Bb
    D.push_A D.push_B f

/-- `τ` is a chain map at level 1: `∂₁ ∘ τ₁ = τ₀ ∘ ∂₁`. -/
theorem pull_boundary1_comm (u : H × Fin 2 → ZMod 2) :
    D.coverComplex.boundary1 (D.pull1 u)
      = D.pull0 (D.baseComplex.boundary1 u) := by
  change bbBoundary1Fn D.Ac D.Bc (u ∘ Prod.map ⇑D.proj id)
    = (bbBoundary1Fn D.Ab D.Bb u) ∘ ⇑D.proj
  exact pullback_bbBoundary1Fn D.proj D.Ac D.Bc D.Ab D.Bb
    D.push_A D.push_B u

/-- `τ` is a chain map at level 2: `∂₂ ∘ τ₂ = τ₁ ∘ ∂₂`. -/
theorem pull_boundary2_comm (f : H → ZMod 2) :
    D.coverComplex.boundary2 (D.pull0 f)
      = D.pull1 (D.baseComplex.boundary2 f) := by
  change bbBoundary2Fn D.Ac D.Bc (f ∘ ⇑D.proj)
    = (bbBoundary2Fn D.Ab D.Bb f) ∘ Prod.map ⇑D.proj id
  exact pullback_bbBoundary2Fn D.proj D.Ac D.Bc D.Ab D.Bb
    D.push_A D.push_B f

/-! ## Exactness package on 1-chains -/

/-- `p ∘ τ = 0` on 1-chains (each fiber contributes twice in char 2). -/
theorem push1_pull1_eq_zero (u : H × Fin 2 → ZMod 2) :
    D.push1 (D.pull1 u) = 0 :=
  fiberSumFn_pullback D.deckSigma1_ne D.proj_prodMap_fiber u

theorem proj_prodMap_surjective :
    Function.Surjective (Prod.map ⇑D.proj (id : Fin 2 → Fin 2)) :=
  Function.Surjective.prodMap D.proj_surjective Function.surjective_id

theorem pull1_injective : Function.Injective ⇑D.pull1 :=
  LinearMap.funLeft_injective_of_surjective (ZMod 2) (ZMod 2) _
    D.proj_prodMap_surjective

theorem pull0_injective : Function.Injective ⇑D.pull0 :=
  LinearMap.funLeft_injective_of_surjective (ZMod 2) (ZMod 2) _
    D.proj_surjective

theorem push1_surjective : Function.Surjective ⇑D.push1 := fun u =>
  ⟨lift0 (Prod.map ⇑D.proj id) D.sec1 u,
    fiberSumFn_lift0 D.proj_prodMap_sec1 u⟩

theorem push0_surjective : Function.Surjective ⇑D.push0 := fun u =>
  ⟨lift0 ⇑D.proj D.sec u, fiberSumFn_lift0 D.proj_sec u⟩

/-- `ker p = range τ` on 1-chains. -/
theorem push1_eq_zero_iff (v : G × Fin 2 → ZMod 2) :
    D.push1 v = 0 ↔ ∃ u : H × Fin 2 → ZMod 2, v = D.pull1 u :=
  fiberSumFn_eq_zero_iff D.deckSigma1_ne D.proj_prodMap_fiber
    D.proj_prodMap_sec1 v

/-- The chain identity `τ(p(v)) = v + σv` = `(1 + σ)v`. -/
theorem pull1_push1 (v : G × Fin 2 → ZMod 2) :
    D.pull1 (D.push1 v) = v + D.deckShift1 v := by
  funext p
  change fiberSumFn (Prod.map ⇑D.proj id) v (Prod.map ⇑D.proj id p)
    = v p + v (p.1 + D.deckS, p.2)
  rw [fiberSumFn_pair D.deckSigma1_ne D.proj_prodMap_fiber v p]
  rfl

/-- **The transfer chase at the cover**: a cover 1-cycle whose pushforward is a
base boundary differs from the pullback of a base 1-cycle by a cover boundary.
This is the hard (`ker ≤ range`) half of the exactness of the transfer sequence
on `H₁`; the quotient-level packaging lives in `BBTransferH1.lean`.

Chase: `p₁ v = ∂₂ᵇ w`; lift `w = p₀ w'` (`push0_surjective`); then
`p₁ (v + ∂₂ᶜ w') = ∂₂ᵇ w + ∂₂ᵇ w = 0` (char 2), so `v + ∂₂ᶜ w' = τ₁ u`
(`push1_eq_zero_iff`); finally `u` is a base cycle by `pull_boundary1_comm` and
`pull0_injective`. -/
theorem exists_pull_eq_add_boundary {v : G × Fin 2 → ZMod 2}
    (hv : v ∈ D.coverComplex.cycles)
    (hbd : D.push1 v ∈ D.baseComplex.boundaries) :
    ∃ u : H × Fin 2 → ZMod 2, u ∈ D.baseComplex.cycles ∧
      ∃ f : G → ZMod 2, D.pull1 u = v + bbBoundary2Fn D.Ac D.Bc f := by
  have hkey : ∀ a : ZMod 2, a + a = 0 := by decide
  obtain ⟨w, hw⟩ := hbd
  -- lift the 2-chain witness through the surjective `p₀`
  obtain ⟨w', rfl⟩ := D.push0_surjective w
  set v' : G × Fin 2 → ZMod 2 := v + bbBoundary2Fn D.Ac D.Bc w' with hv'
  -- the corrected chain pushes to zero (char 2)
  have hzero : D.push1 v' = 0 := by
    have h1 : D.push1 v'
        = D.push1 v + D.push1 (bbBoundary2Fn D.Ac D.Bc w') := by
      rw [hv']; exact map_add _ _ _
    have h2 : D.push1 (bbBoundary2Fn D.Ac D.Bc w') = D.push1 v :=
      (D.push_boundary2_comm w').trans hw
    rw [h1, h2]
    funext j
    rw [Pi.add_apply, Pi.zero_apply]
    exact hkey _
  -- hence it is a pullback: `v + ∂₂ᶜ w' = τ₁ u`
  obtain ⟨u, hu⟩ := (D.push1_eq_zero_iff _).mp hzero
  -- the descended chain `u` is a base cycle
  have hu_cyc : u ∈ D.baseComplex.cycles := by
    have hb1 : D.coverComplex.boundary1 v' = 0 := by
      have h1 : D.coverComplex.boundary1 v'
          = D.coverComplex.boundary1 v
            + D.coverComplex.boundary1 (bbBoundary2Fn D.Ac D.Bc w') := by
        rw [hv']; exact map_add _ _ _
      have h2 : D.coverComplex.boundary1 v = 0 := hv
      have h3 : D.coverComplex.boundary1 (bbBoundary2Fn D.Ac D.Bc w') = 0 :=
        D.coverComplex.boundary_comp_apply w'
      rw [h1, h2, h3, add_zero]
    have h4 : D.coverComplex.boundary1 (D.pull1 u) = 0 := by
      rw [← hu]; exact hb1
    rw [D.pull_boundary1_comm] at h4
    exact (D.baseComplex.mem_cycles_iff u).mpr
      (D.pull0_injective (h4.trans (map_zero D.pull0).symm))
  exact ⟨u, hu_cyc, w', hu.symm.trans hv'⟩

/-! ## Weight identities -/

/-- The number of qubits in the support of `v` whose deck partner is also in the
support (counts each doubly-covered fiber twice). -/
noncomputable def overlapCount (v : G × Fin 2 → ZMod 2) : ℕ :=
  (Finset.univ.filter fun p : G × Fin 2 =>
    v p ≠ 0 ∧ v (p.1 + D.deckS, p.2) ≠ 0).card

/-- `chainWeight` of a cover 1-chain in terms of raw `Finset` data. -/
lemma coverComplex_chainWeight_eq (v : G × Fin 2 → ZMod 2) :
    D.coverComplex.chainWeight v
      = (Finset.univ.filter fun p : G × Fin 2 => v p ≠ 0).card := rfl

/-- `chainWeight` of a base 1-chain in terms of raw `Finset` data. -/
lemma baseComplex_chainWeight_eq (u : H × Fin 2 → ZMod 2) :
    D.baseComplex.chainWeight u
      = (Finset.univ.filter fun p : H × Fin 2 => u p ≠ 0).card := rfl

/-- Weight identity for the pushforward: `|v| = |p(v)| + overlap`. -/
theorem chainWeight_eq_push_add_overlap (v : G × Fin 2 → ZMod 2) :
    D.coverComplex.chainWeight v
      = D.baseComplex.chainWeight (D.push1 v) + D.overlapCount v := by
  rw [coverComplex_chainWeight_eq, baseComplex_chainWeight_eq,
    push1_apply, overlapCount]
  exact card_support_fiberSum_add_overlap D.deckSigma1_ne D.proj_prodMap_fiber v

/-- Pushing forward can only shrink chain weight. -/
theorem chainWeight_push_le (v : G × Fin 2 → ZMod 2) :
    D.baseComplex.chainWeight (D.push1 v) ≤ D.coverComplex.chainWeight v := by
  rw [D.chainWeight_eq_push_add_overlap v]
  exact Nat.le_add_right _ _

/-- Pulling back exactly doubles chain weight. -/
theorem chainWeight_pull1 (u : H × Fin 2 → ZMod 2) :
    D.coverComplex.chainWeight (D.pull1 u)
      = 2 * D.baseComplex.chainWeight u := by
  rw [coverComplex_chainWeight_eq, baseComplex_chainWeight_eq, pull1_apply]
  exact card_support_pullback D.deckSigma1_ne D.proj_prodMap_fiber
    D.proj_prodMap_sec1 u

/-! ## Cycle-membership transfer -/

/-- Pushforwards of cycles are cycles. -/
theorem push1_mem_cycles {v : G × Fin 2 → ZMod 2}
    (hv : v ∈ D.coverComplex.cycles) :
    D.push1 v ∈ D.baseComplex.cycles := by
  have hv' : D.coverComplex.boundary1 v = 0 := hv
  have hgoal : D.baseComplex.boundary1 (D.push1 v) = 0 := by
    rw [← D.push_boundary1_comm, hv']
    exact map_zero D.push0
  exact hgoal

/-- Pullbacks of cycles are cycles. -/
theorem pull1_mem_cycles {u : H × Fin 2 → ZMod 2}
    (hu : u ∈ D.baseComplex.cycles) :
    D.pull1 u ∈ D.coverComplex.cycles := by
  have hu' : D.baseComplex.boundary1 u = 0 := hu
  have hgoal : D.coverComplex.boundary1 (D.pull1 u) = 0 := by
    rw [D.pull_boundary1_comm, hu']
    exact map_zero D.pull0
  exact hgoal

/-- Pushforwards of boundaries are boundaries. -/
theorem push1_mem_boundaries {v : G × Fin 2 → ZMod 2}
    (hv : v ∈ D.coverComplex.boundaries) :
    D.push1 v ∈ D.baseComplex.boundaries := by
  obtain ⟨f, rfl⟩ := hv
  exact ⟨D.push0 f, (D.push_boundary2_comm f).symm⟩

/-- Pullbacks of boundaries are boundaries. -/
theorem pull1_mem_boundaries {u : H × Fin 2 → ZMod 2}
    (hu : u ∈ D.baseComplex.boundaries) :
    D.pull1 u ∈ D.coverComplex.boundaries := by
  obtain ⟨f, rfl⟩ := hu
  exact ⟨D.pull0 f, D.pull_boundary2_comm f⟩

/-! ## Sheet decomposition of cover 1-chains -/

/-- Sheet-0 restriction of a cover 1-chain (via the section `sec1`). -/
def sheet0 (v : G × Fin 2 → ZMod 2) : H × Fin 2 → ZMod 2 :=
  fun q => v (D.sec1 q)

/-- Sheet-1 restriction of a cover 1-chain (deck partner of sheet 0). -/
def sheet1 (v : G × Fin 2 → ZMod 2) : H × Fin 2 → ZMod 2 :=
  fun q => v (D.deckSigma1 (D.sec1 q))

@[simp] lemma sheet0_apply (v : G × Fin 2 → ZMod 2) (q : H × Fin 2) :
    D.sheet0 v q = v (D.sec1 q) := rfl

@[simp] lemma sheet1_apply (v : G × Fin 2 → ZMod 2) (q : H × Fin 2) :
    D.sheet1 v q = v (D.deckSigma1 (D.sec1 q)) := rfl

lemma sheet0_add (v w : G × Fin 2 → ZMod 2) :
    D.sheet0 (v + w) = D.sheet0 v + D.sheet0 w := rfl

lemma sheet1_add (v w : G × Fin 2 → ZMod 2) :
    D.sheet1 (v + w) = D.sheet1 v + D.sheet1 w := rfl

/-- The two sheets sum to the pushforward. -/
lemma sheet0_add_sheet1 (v : G × Fin 2 → ZMod 2) (j : H × Fin 2) :
    D.sheet0 v j + D.sheet1 v j = D.push1 v j := by
  have h := fiberSumFn_pair D.deckSigma1_ne D.proj_prodMap_fiber v (D.sec1 j)
  rw [D.proj_prodMap_sec1 j] at h
  exact h.symm

/-- Sheet-0 restriction inverts the pullback. -/
lemma sheet0_pull1 (u : H × Fin 2 → ZMod 2) :
    D.sheet0 (D.pull1 u) = u := by
  funext q
  change u (Prod.map ⇑D.proj id (D.sec1 q)) = u q
  rw [D.proj_prodMap_sec1 q]

/-! ## The refined slice identity -/

/-- The deck-overlap of `v` counts twice the overlapping fibers. -/
lemma overlapCount_eq_two_mul_sheets (v : G × Fin 2 → ZMod 2) :
    D.overlapCount v
      = 2 * (Finset.univ.filter fun j =>
          D.sheet0 v j ≠ 0 ∧ D.sheet1 v j ≠ 0).card := by
  exact card_overlap_eq_two_mul D.deckSigma1_ne D.proj_prodMap_fiber
    D.proj_prodMap_sec1 v

/-- **Refined slice identity**: `|v| = |p(v)| + 2·|supp(sheet0 v) ∖ supp p(v)|`.
-/
theorem chainWeight_sheet_eq (v : G × Fin 2 → ZMod 2) :
    D.coverComplex.chainWeight v
      = D.baseComplex.chainWeight (D.push1 v)
        + 2 * (Finset.univ.filter fun j =>
            D.sheet0 v j ≠ 0 ∧ D.push1 v j = 0).card := by
  rw [D.chainWeight_eq_push_add_overlap v, D.overlapCount_eq_two_mul_sheets]
  have hfilter : (Finset.univ.filter fun j =>
        D.sheet0 v j ≠ 0 ∧ D.sheet1 v j ≠ 0)
      = Finset.univ.filter fun j =>
          D.sheet0 v j ≠ 0 ∧ D.push1 v j = 0 := by
    apply Finset.filter_congr
    intro j _
    have key : ∀ a b c : ZMod 2, a + b = c →
        ((a ≠ 0 ∧ b ≠ 0) ↔ (a ≠ 0 ∧ c = 0)) := by decide
    exact key _ _ _ (D.sheet0_add_sheet1 v j)
  rw [hfilter]

/-! ## The lifted stabilizer -/

/-- Sheet-0 lift of a base 2-chain to the cover. -/
def liftC2 (ξ : H → ZMod 2) : G → ZMod 2 :=
  lift0 ⇑D.proj D.sec ξ

lemma push0_liftC2 (ξ : H → ZMod 2) :
    fiberSumFn ⇑D.proj (D.liftC2 ξ) = ξ :=
  fiberSumFn_lift0 D.proj_sec ξ

/-- The lifted stabilizer of a base 2-chain: `∂₂(cover) (lift ξ)`. -/
def liftStab (ξ : H → ZMod 2) : G × Fin 2 → ZMod 2 :=
  bbBoundary2Fn D.Ac D.Bc (D.liftC2 ξ)

lemma liftStab_mem_boundaries (ξ : H → ZMod 2) :
    D.liftStab ξ ∈ D.coverComplex.boundaries :=
  ⟨D.liftC2 ξ, rfl⟩

/-- The lifted stabilizer pushes forward to the base stabilizer. -/
lemma push1_liftStab (ξ : H → ZMod 2) :
    D.push1 (D.liftStab ξ) = bbBoundary2Fn D.Ab D.Bb ξ := by
  change fiberSumFn (Prod.map ⇑D.proj id) (bbBoundary2Fn D.Ac D.Bc (D.liftC2 ξ))
    = bbBoundary2Fn D.Ab D.Bb ξ
  rw [fiberSum_bbBoundary2Fn D.proj D.Ac D.Bc D.Ab D.Bb
    D.push_A D.push_B (D.liftC2 ξ), D.push0_liftC2]

/-- The descended chain of a dangerous normalization is a base cycle. -/
lemma descend_cycle {u : H × Fin 2 → ZMod 2}
    (h : D.pull1 u ∈ D.coverComplex.cycles) :
    bbBoundary1Fn D.Ab D.Bb u = 0 := by
  have h1 : D.coverComplex.boundary1 (D.pull1 u) = 0 := h
  rw [D.pull_boundary1_comm] at h1
  apply D.pull0_injective
  change D.pull0 (D.baseComplex.boundary1 u) = D.pull0 0
  rw [h1]
  exact (map_zero D.pull0).symm

/-! ## Sheet decomposition of cover 2-chains -/

/-- Sheet-0 restriction of a cover 2-chain. -/
def sheetC2_0 (z : G → ZMod 2) : H → ZMod 2 :=
  fun j => z (D.sec j)

/-- Sheet-1 restriction of a cover 2-chain. -/
def sheetC2_1 (z : G → ZMod 2) : H → ZMod 2 :=
  fun j => z (D.sec j + D.deckS)

/-- A cover 2-chain is the sum of the lifts of its two sheets. -/
lemma liftC2_decomp (z : G → ZMod 2) :
    z = D.liftC2 (D.sheetC2_0 z)
      + D.deckShift0 (D.liftC2 (D.sheetC2_1 z)) := by
  funext g
  rw [Pi.add_apply]
  rcases D.point_dichotomy g with hg | hg
  · have h1 : D.liftC2 (D.sheetC2_0 z) g = z g := by
      change (if g = D.sec (D.proj g) then D.sheetC2_0 z (D.proj g) else 0)
        = z g
      rw [if_pos hg]
      change z (D.sec (D.proj g)) = z g
      rw [← hg]
    have h2 : D.deckShift0 (D.liftC2 (D.sheetC2_1 z)) g = 0 := by
      change (if g + D.deckS = D.sec (D.proj (g + D.deckS)) then
        D.sheetC2_1 z (D.proj (g + D.deckS)) else 0) = 0
      rw [if_neg ?_]
      intro hcon
      rw [D.proj_add_deckS, ← hg] at hcon
      apply D.deckS_ne_zero
      have hcon' : g + D.deckS = g + 0 := by rw [add_zero]; exact hcon
      exact add_left_cancel hcon'
    rw [h1, h2, add_zero]
  · have h1 : D.liftC2 (D.sheetC2_0 z) g = 0 := by
      change (if g = D.sec (D.proj g) then D.sheetC2_0 z (D.proj g) else 0)
        = 0
      rw [if_neg ?_]
      intro hcon
      have hcontra := hcon.symm.trans hg
      apply D.deckS_ne_zero
      have hg' : D.sec (D.proj g) + 0 = D.sec (D.proj g) + D.deckS := by
        rw [add_zero]; exact hcontra
      exact (add_left_cancel hg').symm
    have h2 : D.deckShift0 (D.liftC2 (D.sheetC2_1 z)) g = z g := by
      have hgd : g + D.deckS = D.sec (D.proj g) := by
        rw [hg, add_assoc, D.deckS_add_deckS, add_zero, D.proj_add_deckS,
          D.proj_sec]
      change (if g + D.deckS = D.sec (D.proj (g + D.deckS)) then
        D.sheetC2_1 z (D.proj (g + D.deckS)) else 0) = z g
      rw [D.proj_add_deckS, if_pos hgd]
      change z (D.sec (D.proj g) + D.deckS) = z g
      rw [← hg]
    rw [h1, h2, zero_add]

lemma liftC2_add (ξ η : H → ZMod 2) :
    D.liftC2 (ξ + η) = D.liftC2 ξ + D.liftC2 η := by
  funext g
  change (if g = D.sec (D.proj g) then (ξ + η) (D.proj g) else 0)
    = (if g = D.sec (D.proj g) then ξ (D.proj g) else 0)
      + (if g = D.sec (D.proj g) then η (D.proj g) else 0)
  by_cases hg : g = D.sec (D.proj g)
  · rw [if_pos hg, if_pos hg, if_pos hg]
    rfl
  · rw [if_neg hg, if_neg hg, if_neg hg, add_zero]

/-! ## The seam decomposition `∂₂ = N + C` -/

/-- The non-crossing seam part: sheet-0 component of the lifted stabilizer. -/
def seamN (ξ : H → ZMod 2) : H × Fin 2 → ZMod 2 :=
  D.sheet0 (D.liftStab ξ)

/-- The seam-crossing part: sheet-1 component of the lifted stabilizer. The
Smith connecting map at chain level is `ζ ↦ seamC ζ` on 2-cycles. -/
def seamC (ξ : H → ZMod 2) : H × Fin 2 → ZMod 2 :=
  D.sheet1 (D.liftStab ξ)

/-- The seam split sums to the base boundary. -/
lemma seamN_add_seamC (ξ : H → ZMod 2) (j : H × Fin 2) :
    D.seamN ξ j + D.seamC ξ j = bbBoundary2Fn D.Ab D.Bb ξ j := by
  have h := D.sheet0_add_sheet1 (D.liftStab ξ) j
  rw [D.push1_liftStab] at h
  exact h

lemma seamC_add (ξ η : H → ZMod 2) :
    D.seamC (ξ + η) = D.seamC ξ + D.seamC η := by
  unfold seamC liftStab
  rw [D.liftC2_add, bbBoundary2Fn_add, D.sheet1_add]

lemma liftC2_zero : D.liftC2 (0 : H → ZMod 2) = 0 := by
  funext g
  change (if g = D.sec (D.proj g) then (0 : H → ZMod 2) (D.proj g) else 0) = 0
  split <;> rfl

lemma seamC_zero : D.seamC (0 : H → ZMod 2) = 0 := by
  unfold seamC liftStab
  rw [D.liftC2_zero]
  funext q
  have h : bbBoundary2Fn D.Ac D.Bc (0 : G → ZMod 2) = 0 := by
    have h0 : D.coverComplex.boundary2 0 = 0 := map_zero _
    exact h0
  rw [h]
  rfl

/-! ## Deck-shift bookkeeping -/

lemma liftStab_deckShift (ξ : H → ZMod 2) :
    bbBoundary2Fn D.Ac D.Bc (D.deckShift0 (D.liftC2 ξ))
      = D.deckShift1 (D.liftStab ξ) :=
  bbBoundary2Fn_translate D.Ac D.Bc D.deckS (D.liftC2 ξ)

lemma sheet0_deckShift1 (s : G × Fin 2 → ZMod 2) :
    D.sheet0 (D.deckShift1 s) = D.sheet1 s := rfl

lemma sheet1_deckShift1 (s : G × Fin 2 → ZMod 2) :
    D.sheet1 (D.deckShift1 s) = D.sheet0 s := by
  funext q
  change s ((D.sec1 q).1 + D.deckS + D.deckS, (D.sec1 q).2) = s (D.sec1 q)
  rw [add_assoc, D.deckS_add_deckS, add_zero]

/-- Sheet 0 of `v + σv` is the pushforward. -/
lemma sheet0_self_add_deck (v : G × Fin 2 → ZMod 2) (j : H × Fin 2) :
    D.sheet0 (v + D.deckShift1 v) j = D.push1 v j := by
  rw [D.sheet0_add, Pi.add_apply, D.sheet0_deckShift1]
  exact D.sheet0_add_sheet1 v j

/-- Sheet 1 of `v + σv` is also the pushforward. -/
lemma sheet1_self_add_deck (v : G × Fin 2 → ZMod 2) (j : H × Fin 2) :
    D.sheet1 (v + D.deckShift1 v) j = D.push1 v j := by
  rw [D.sheet1_add, Pi.add_apply, D.sheet1_deckShift1, add_comm]
  exact D.sheet0_add_sheet1 v j

/-! ## The chain-level Smith connecting map lands in cycles -/

/-- For a base 2-cycle `ζ` (`∂₂ ζ = 0`), the seam-crossing component `seamC ζ`
is a base 1-cycle. Pure exactness of the double cover. -/
theorem seamC_mem_cycles {ζ : H → ZMod 2}
    (hζ : bbBoundary2Fn D.Ab D.Bb ζ = 0) :
    D.seamC ζ ∈ D.baseComplex.cycles := by
  -- `liftStab ζ` is a cover cycle (it is a cover boundary)
  have hcover_cyc : D.liftStab ζ ∈ D.coverComplex.cycles :=
    D.coverComplex.boundaries_le_cycles (D.liftStab_mem_boundaries ζ)
  -- it pushes forward to `∂₂ ζ = 0`
  have hpush : D.push1 (D.liftStab ζ) = 0 := by
    rw [D.push1_liftStab]; exact hζ
  -- exactness `ker p = im τ`
  obtain ⟨u, hu⟩ := (D.push1_eq_zero_iff _).mp hpush
  -- `u` is a base 1-cycle
  have hu_cyc : u ∈ D.baseComplex.cycles := by
    have h1 : D.coverComplex.boundary1 (D.pull1 u) = 0 := by
      rw [← hu]; exact hcover_cyc
    rw [D.pull_boundary1_comm] at h1
    have h2 : D.baseComplex.boundary1 u = 0 := by
      apply D.pull0_injective
      rw [h1]
      exact (map_zero D.pull0).symm
    exact h2
  -- `seamN ζ = sheet0 (liftStab ζ) = sheet0 (pull1 u) = u`
  have hseamN : D.seamN ζ = u := by
    change D.sheet0 (D.liftStab ζ) = u
    rw [hu, D.sheet0_pull1]
  -- char 2: `seamN ζ + seamC ζ = ∂₂ ζ = 0`, hence `seamC ζ = seamN ζ = u`
  have hseamC : D.seamC ζ = u := by
    have hkey : ∀ a b : ZMod 2, a + b = 0 → b = a := by decide
    funext j
    have hsum := D.seamN_add_seamC ζ j
    rw [hseamN, hζ, Pi.zero_apply] at hsum
    exact hkey _ _ hsum
  rw [hseamC]; exact hu_cyc

end XDoubleCoverData

end BB
end Homological
end Stabilizer
end Quantum
