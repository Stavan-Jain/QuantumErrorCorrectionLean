/-
# Transfer maps on `H₁` and the deck-image rank floor `E ≥ k̃ − k` (A13 L2b)

This instantiates the abstract transfer-inequality core
(`BBBocksteinRank.finrank_sub_le_finrank_range_comp`) on the homology of an
`XDoubleCoverData` bundle:

* `push1Cycles` / `pull1Cycles` — the transfer maps `p₁, τ₁` restricted to
  1-cycles (they preserve cycles by the chain-map identities).
* `pushH1` / `pullH1` — the induced maps `p_*, τ_*` on `H₁ = Z₁/B₁`
  (they preserve boundaries, so `Submodule.mapQ` applies).
* `ker_pushH1_eq_range_pullH1` — exactness of the transfer sequence at the
  cover.  The hard direction consumes the chain-level chase
  `exists_pull_eq_add_boundary` (`BBCover.lean`); the easy direction is
  `push1_pull1_eq_zero`.
* `epsH1` — the induced deck map `ε_* = τ_* ∘ p_*`; on cycle
  representatives it is `1 + σ` (`coe_pull1Cycles_push1Cycles`, from
  `pull1_push1`), so `range ε_*` is `(1+σ)·H₁(cover)`.
* `finrank_H1_sub_le_finrank_range_epsH1` (capstone) —
  `dim H₁(cover) − dim H₁(base) ≤ dim (1+σ)·H₁(cover)`, i.e. `E ≥ k̃ − k`:
  the inequality half of the A13 Bockstein rank equality
  (`qec-lab:experiments/bb_lab/notes/A13_result.md` §1; A12 part 2).
-/

import QEC.Stabilizer.Framework.Homological.BBCover
import QEC.Stabilizer.Framework.Homological.BBBocksteinRank

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open scoped Homology

-- Defeq checks through `coverComplex`/`baseComplex` projections unfold deep
-- `Prod`/`ZMod` instance chains, exactly as in `BBCover.lean`.
set_option maxRecDepth 4096

namespace XDoubleCoverData

variable {G H : Type}
  [Fintype G] [AddCommGroup G] [DecidableEq G]
  [Fintype H] [AddCommGroup H] [DecidableEq H]
  (D : XDoubleCoverData G H)

/-! ## The transfer maps restricted to 1-cycles -/

/-- `p₁` restricted to 1-cycles. -/
noncomputable def push1Cycles :
    D.coverComplex.cycles →ₗ[ZMod 2] D.baseComplex.cycles :=
  D.push1.restrict fun _ hv => D.push1_mem_cycles hv

/-- `τ₁` restricted to 1-cycles. -/
noncomputable def pull1Cycles :
    D.baseComplex.cycles →ₗ[ZMod 2] D.coverComplex.cycles :=
  D.pull1.restrict fun _ hu => D.pull1_mem_cycles hu

@[simp] lemma coe_push1Cycles (v : D.coverComplex.cycles) :
    (D.push1Cycles v : D.baseComplex.C1 → ZMod 2)
      = D.push1 (v : D.coverComplex.C1 → ZMod 2) := rfl

@[simp] lemma coe_pull1Cycles (u : D.baseComplex.cycles) :
    (D.pull1Cycles u : D.coverComplex.C1 → ZMod 2)
      = D.pull1 (u : D.baseComplex.C1 → ZMod 2) := rfl

/-- The composite `τ₁ ∘ p₁` on cycles is `τ ∘ p` on chains. -/
@[simp] lemma coe_pull1Cycles_push1Cycles (v : D.coverComplex.cycles) :
    (D.pull1Cycles (D.push1Cycles v) : D.coverComplex.C1 → ZMod 2)
      = D.pull1 (D.push1 (v : D.coverComplex.C1 → ZMod 2)) := rfl

/-- On cycles, `τ₁ ∘ p₁` is the deck averaging `1 + σ`, pointwise
(chain level: `pull1_push1`). -/
lemma pull1Cycles_push1Cycles_apply (v : D.coverComplex.cycles)
    (p : G × Fin 2) :
    (D.pull1Cycles (D.push1Cycles v) : D.coverComplex.C1 → ZMod 2) p
      = (v : D.coverComplex.C1 → ZMod 2) p
        + (v : D.coverComplex.C1 → ZMod 2) (p.1 + D.deckS, p.2) :=
  congrFun (D.pull1_push1 (v : D.coverComplex.C1 → ZMod 2)) p

/-! ## The induced maps on `H₁` -/

/-- The induced pushforward `p_* : H₁(cover) → H₁(base)`. -/
noncomputable def pushH1 :
    D.coverComplex.H1 →ₗ[ZMod 2] D.baseComplex.H1 :=
  Submodule.mapQ _ _ D.push1Cycles (by
    intro v hv
    have hv' : (v : D.coverComplex.C1 → ZMod 2) ∈ D.coverComplex.boundaries :=
      hv
    change (D.push1Cycles v : D.baseComplex.C1 → ZMod 2)
      ∈ D.baseComplex.boundaries
    exact D.push1_mem_boundaries hv')

/-- The induced transfer `τ_* : H₁(base) → H₁(cover)`. -/
noncomputable def pullH1 :
    D.baseComplex.H1 →ₗ[ZMod 2] D.coverComplex.H1 :=
  Submodule.mapQ _ _ D.pull1Cycles (by
    intro u hu
    have hu' : (u : D.baseComplex.C1 → ZMod 2) ∈ D.baseComplex.boundaries :=
      hu
    change (D.pull1Cycles u : D.coverComplex.C1 → ZMod 2)
      ∈ D.coverComplex.boundaries
    exact D.pull1_mem_boundaries hu')

lemma pushH1_mk (v : D.coverComplex.cycles) :
    D.pushH1 (Submodule.Quotient.mk v)
      = Submodule.Quotient.mk (D.push1Cycles v) := rfl

lemma pullH1_mk (u : D.baseComplex.cycles) :
    D.pullH1 (Submodule.Quotient.mk u)
      = Submodule.Quotient.mk (D.pull1Cycles u) := rfl

/-! ## Exactness of the transfer sequence at the cover -/

/-- Hard direction of exactness: `ker p_* ≤ range τ_*` (the diagram chase,
delegated to the chain level: `exists_pull_eq_add_boundary`). -/
theorem ker_pushH1_le_range_pullH1 :
    LinearMap.ker D.pushH1 ≤ LinearMap.range D.pullH1 := by
  intro x hx
  obtain ⟨⟨v, hv⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  -- `p₁ v` is a base boundary
  have hx0 : D.pushH1 (Submodule.Quotient.mk ⟨v, hv⟩) = 0 :=
    LinearMap.mem_ker.mp hx
  rw [D.pushH1_mk, Submodule.Quotient.mk_eq_zero] at hx0
  have hbd : D.push1 v ∈ D.baseComplex.boundaries := hx0
  -- chain-level chase: `τ₁ u = v + ∂₂ᶜ f` with `u` a base cycle
  obtain ⟨u, hu_cyc, f, hf⟩ := D.exists_pull_eq_add_boundary hv hbd
  refine ⟨Submodule.Quotient.mk ⟨u, hu_cyc⟩, ?_⟩
  rw [D.pullH1_mk, Submodule.Quotient.eq]
  change ((D.pull1Cycles ⟨u, hu_cyc⟩ - ⟨v, hv⟩ : D.coverComplex.cycles) :
      D.coverComplex.C1 → ZMod 2) ∈ D.coverComplex.boundaries
  -- the difference of representatives is the boundary `∂₂ᶜ f`, pointwise
  -- from `hf` (all arithmetic scalar in `ZMod 2`, dodging the mixed
  -- `D.coverComplex.C1` / `G × Fin 2` Pi instances)
  refine ⟨f, funext fun p => ?_⟩
  have hp := congrFun hf p
  have key : ∀ a b c : ZMod 2, a = b + c → c = a - b := by decide
  exact key _ _ _ hp

/-- Easy direction of exactness: `range τ_* ≤ ker p_*` (from `p ∘ τ = 0`). -/
theorem range_pullH1_le_ker_pushH1 :
    LinearMap.range D.pullH1 ≤ LinearMap.ker D.pushH1 := by
  rintro x ⟨y, rfl⟩
  obtain ⟨⟨u, hu⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [LinearMap.mem_ker, D.pullH1_mk, D.pushH1_mk,
    Submodule.Quotient.mk_eq_zero]
  change (D.push1Cycles (D.pull1Cycles ⟨u, hu⟩) : D.baseComplex.C1 → ZMod 2)
      ∈ D.baseComplex.boundaries
  have hz : (D.push1Cycles (D.pull1Cycles ⟨u, hu⟩) :
      D.baseComplex.C1 → ZMod 2) = 0 := by
    change D.push1 (D.pull1 u) = 0
    exact D.push1_pull1_eq_zero u
  rw [hz]
  exact zero_mem _

/-- **Exactness of the transfer sequence at the cover on `H₁`**:
`ker p_* = range τ_*`. -/
theorem ker_pushH1_eq_range_pullH1 :
    LinearMap.ker D.pushH1 = LinearMap.range D.pullH1 :=
  le_antisymm D.ker_pushH1_le_range_pullH1 D.range_pullH1_le_ker_pushH1

/-! ## The deck map on `H₁` and the rank floor -/

/-- The induced deck map `ε_* = τ_* ∘ p_*` on `H₁(cover)`; on cycle
representatives it is `1 + σ` (`coe_pull1Cycles_push1Cycles`). -/
noncomputable def epsH1 :
    D.coverComplex.H1 →ₗ[ZMod 2] D.coverComplex.H1 :=
  D.pullH1 ∘ₗ D.pushH1

lemma epsH1_mk (v : D.coverComplex.cycles) :
    D.epsH1 (Submodule.Quotient.mk v)
      = Submodule.Quotient.mk (D.pull1Cycles (D.push1Cycles v)) := rfl

/-- **The deck-image rank floor `E ≥ k̃ − k`** (A13 rank corollary,
inequality half): `dim H₁(cover) − dim H₁(base) ≤ dim (1+σ)·H₁(cover)`. -/
theorem finrank_H1_sub_le_finrank_range_epsH1 :
    dim₂ D.coverComplex.H1
      - dim₂ D.baseComplex.H1
      ≤ dim₂ (LinearMap.range D.epsH1) :=
  BBBocksteinRank.finrank_sub_le_finrank_range_comp D.pushH1 D.pullH1
    D.ker_pushH1_eq_range_pullH1

/-! ## The Bockstein-vanishing criterion and the rank equality -/

/-- **The Bockstein-vanishing criterion** for a cover: `ker τ_* ≤ range p_*`
on `H₁`.  Equivalently `δ₁ ∘ δ₂ = 0` for the two connecting maps of the
transfer LES (`im δ₂ = ker τ_*`, `ker δ₁ = range p_*`).  It is exactly the
hypothesis under which the deck-image floor `E ≥ k̃ − k` is an equality
(`BBBocksteinRank.finrank_range_comp_eq_of_ker_le`); the OQ2 element form
(`BocksteinLift`) + L2a (`BBEpsFreeGroupAlgebra`) are what establish it for
actual BB covers. -/
def BocksteinVanishes : Prop :=
  LinearMap.ker D.pullH1 ≤ LinearMap.range D.pushH1

/-- **The rank corollary, additive form.** Under `BocksteinVanishes`,
`dim (1+σ)·H₁(cover) + k = k̃` exactly (no truncated subtraction) — in
particular `k̃ ≥ k`. -/
theorem finrank_range_epsH1_add_eq (h : D.BocksteinVanishes) :
    dim₂ (LinearMap.range D.epsH1)
        + dim₂ D.baseComplex.H1
      = dim₂ D.coverComplex.H1 := by
  have hid := BBBocksteinRank.finrank_range_comp_add_eq D.pushH1 D.pullH1
    D.ker_pushH1_eq_range_pullH1
  rw [inf_of_le_right h] at hid
  change dim₂ (LinearMap.range (D.pullH1 ∘ₗ D.pushH1))
      + _ = _
  omega

/-- **The rank corollary, equality form.** Under `BocksteinVanishes`, the
deck-image floor is tight: `dim (1+σ)·H₁(cover) = k̃ − k`. -/
theorem finrank_range_epsH1_eq (h : D.BocksteinVanishes) :
    dim₂ (LinearMap.range D.epsH1)
      = dim₂ D.coverComplex.H1
        - dim₂ D.baseComplex.H1 := by
  have h := D.finrank_range_epsH1_add_eq h
  omega

/-! ## The deck endomorphism squares to zero -/

/-- `ε_*² = 0` on `H₁(cover)`: `(1+σ)² = 1 + σ² = 0` in char 2, here read
off `push_*∘pull_* = 0` (`range τ_* ≤ ker p_*`). This makes `H₁(cover)` a
module over `D = 𝔽₂[ε]/(ε²)`; with `finrank_range_epsH1_eq` giving
`dim ε_*H₁ = k̃ − k`, the deck-module structure is
`H₁ ≅ D^{k̃−k} ⊕ 𝔽₂^{2k−k̃}`. -/
theorem epsH1_epsH1_apply (x : D.coverComplex.H1) :
    D.epsH1 (D.epsH1 x) = 0 := by
  have hmid : D.pushH1 (D.pullH1 (D.pushH1 x)) = 0 :=
    D.range_pullH1_le_ker_pushH1 ⟨D.pushH1 x, rfl⟩
  simp only [epsH1, LinearMap.comp_apply]
  rw [hmid, map_zero]

/-- Under `BocksteinVanishes`, `dim (ker ε_*) = k`: the complementary rank
to `finrank_range_epsH1_eq`, via rank-nullity for `ε_*`. -/
theorem finrank_ker_epsH1_eq (h : D.BocksteinVanishes) :
    dim₂ (LinearMap.ker D.epsH1)
      = dim₂ D.baseComplex.H1 := by
  have hrn := LinearMap.finrank_range_add_finrank_ker D.epsH1
  have hadd := D.finrank_range_epsH1_add_eq h
  omega

end XDoubleCoverData

end BB
end Homological
end Stabilizer
end Quantum
