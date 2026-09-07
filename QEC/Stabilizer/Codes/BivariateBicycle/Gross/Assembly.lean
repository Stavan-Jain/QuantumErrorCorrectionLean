/-
# Phase 1: conditional assembly — d(gross) = 12 at the chain level

The sector-dichotomy assembly of the bb_lab analytic proof
(`qec-lab:experiments/bb_lab/notes/A4_writeup.md`, Theorems A–D), formalized at the
`𝔽₂`-chain level with the three hard analytic inputs left as named
hypotheses.  For a nontrivial gross cycle `v`, split on `b := p(v)`
(pushforward to the bb72 base):

* **safe sector** (`b` not a base boundary): `SafeSectorGe12` — the paper's
  (R) + flux characterization + (M-im) chain (A4 Part II, Theorem D);
* **dangerous, `b ≠ 0`**: `DangerousSectorGe12` — the paper's (M) on the
  light-stabilizer slices (A4 Theorem C);
* **dangerous, `b = 0`**: discharged HERE — by exactness `v = τ(u)` for a
  base cycle `u`, nontrivial since `τ` maps boundaries to boundaries, and
  `|v| = 2|u| ≥ 2·6` given `BaseDistanceGe6` (A4 Theorem A / Corollary A′).

Together with the Phase-0 weight-12 witness `τ(u*)` this gives the
conditional chain-level `d(gross) = 12` (`gross_chain_distance_eq_12_of_sectors`),
its dual-side mirror via the Φ duality, and the Pauli-level corollaries
through the CSS distance bridge: every nontrivial logical operator of the
gross homological stabilizer group has weight ≥ 12, with weight 12 attained
(unconditionally) by `chainXOperator τ(u*)`.

Phases 2–4 discharge the three hypotheses; their Lean statements below are
the interface those phases must hit.

## Convention bridge (lab notes → repo)

Repo convention: `∂₂ f = (A⋆f | B⋆f)`, `∂₁ c = B⋆c_L + A⋆c_R`; cycle
condition `B⋆v_L = A⋆v_R`.  **Repo-left = lab-right.**  "Dangerous sector"
= `[v] ∈ ker pr_*`, which at the chain level is `coverPush1 v ∈ boundaries`.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Gross.Witness

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open scoped BigOperators

/-! ## The three residual hypotheses (the Phase 2–4 targets) -/

/-- **(A)** Chain-level `d(base) ≥ 6`: every nontrivial cycle of the bb72
complex has weight ≥ 6. Paper source: the small-cycle theorem, A4 Theorem A /
Corollary A′ (Entry 13). Phase-2 target. -/
def BaseDistanceGe6 : Prop :=
  ∀ u : BaseGroup × Fin 2 → ZMod 2,
    u ∈ bb72Complex.cycles → u ∉ bb72Complex.boundaries →
    6 ≤ bb72Complex.chainWeight u

/-- **(M), `b ≠ 0` rungs**: every nontrivial gross cycle in the dangerous sector
(pushforward a base boundary) with *nonzero* pushforward has weight ≥ 12. Paper
source: the light-stabilizer classification + m-rungs, A4 Theorem C (Entries
10–13). Phase-3 target. (The `b = 0` rung is discharged below from
`BaseDistanceGe6` alone.) -/
def DangerousSectorGe12 : Prop :=
  ∀ v : GrossGroup × Fin 2 → ZMod 2,
    v ∈ grossComplex.cycles → v ∉ grossComplex.boundaries →
    coverPush1 v ∈ bb72Complex.boundaries → coverPush1 v ≠ 0 →
    12 ≤ grossComplex.chainWeight v

/-- **(M-im)**: every gross cycle in the safe sector (pushforward NOT a base
boundary) has weight ≥ 12. Paper source: (R) + the flux characterization + the
(M-im) confined-floor program, A4 Part II / Theorem D (Entries 16–28). Phase-4
target. (Such a `v` is automatically not a boundary, since `p` maps boundaries
to boundaries.) -/
def SafeSectorGe12 : Prop :=
  ∀ v : GrossGroup × Fin 2 → ZMod 2,
    v ∈ grossComplex.cycles → coverPush1 v ∉ bb72Complex.boundaries →
    12 ≤ grossComplex.chainWeight v

/-! ## The `b = 0` dangerous rung (discharged here)

If `p(v) = 0` then by exactness `v = τ(u)`; `u` is a cycle because `τ` is an
injective chain map, `u` is nontrivial because `τ` carries boundaries to
boundaries, and `|v| = 2|u| ≥ 2·6 = 12`. -/

theorem gross_chainWeight_ge_12_of_coverPush_eq_zero
    (hbase : BaseDistanceGe6)
    {v : GrossGroup × Fin 2 → ZMod 2}
    (hv : v ∈ grossComplex.cycles) (hnb : v ∉ grossComplex.boundaries)
    (h0 : coverPush1 v = 0) :
    12 ≤ grossComplex.chainWeight v := by
  obtain ⟨u, rfl⟩ := (coverPush1_eq_zero_iff v).mp h0
  have hu_cyc : u ∈ bb72Complex.cycles := by
    have h1 : grossComplex.boundary1 (coverPull1 u) = 0 := hv
    rw [coverPull_boundary1_comm] at h1
    have h2 : bb72Complex.boundary1 u = 0 := by
      apply coverPull0_injective
      rw [h1]
      exact (map_zero coverPull0).symm
    exact h2
  have hu_nb : u ∉ bb72Complex.boundaries := fun hu =>
    hnb (coverPull1_mem_boundaries hu)
  have h6 := hbase u hu_cyc hu_nb
  rw [chainWeight_coverPull1]
  omega

/-! ## The assembly -/

/-- **Sector-dichotomy assembly**: given the three analytic inputs, every
nontrivial cycle of the gross complex has chain weight ≥ 12. -/
theorem gross_chainWeight_ge_12_of_sectors
    (hbase : BaseDistanceGe6) (hM : DangerousSectorGe12)
    (hMim : SafeSectorGe12) :
    ∀ v : GrossGroup × Fin 2 → ZMod 2,
      v ∈ grossComplex.cycles → v ∉ grossComplex.boundaries →
      12 ≤ grossComplex.chainWeight v := by
  intro v hv hnb
  by_cases hb : coverPush1 v ∈ bb72Complex.boundaries
  · by_cases h0 : coverPush1 v = 0
    · exact gross_chainWeight_ge_12_of_coverPush_eq_zero hbase hv hnb h0
    · exact hM v hv hnb hb h0
  · exact hMim v hv hb

/-- Conditional chain-level `d(gross) = 12`: the weight 12 is attained by a
nontrivial cycle (the Phase-0 witness `τ(u*)`, unconditional) and is minimal
(given the three sector inputs). -/
theorem gross_chain_distance_eq_12_of_sectors
    (hbase : BaseDistanceGe6) (hM : DangerousSectorGe12)
    (hMim : SafeSectorGe12) :
    IsLeast {w : ℕ | ∃ v : GrossGroup × Fin 2 → ZMod 2,
      v ∈ grossComplex.cycles ∧ v ∉ grossComplex.boundaries ∧
      grossComplex.chainWeight v = w} 12 := by
  constructor
  · exact ⟨coverPull1 uStar, tauUStar_mem_cycles,
      tauUStar_not_mem_boundaries, chainWeight_tauUStar⟩
  · rintro w ⟨v, hv, hnb, rfl⟩
    exact gross_chainWeight_ge_12_of_sectors hbase hM hMim v hv hnb

/-! ## The dual (Z) side, by the Φ duality -/

/-- Dual-side mirror: the same three inputs bound every nontrivial *dual* cycle
(Z-side chain) at ≥ 12, via the chain-level `d_X = d_Z` duality. -/
theorem gross_dual_chainWeight_ge_12_of_sectors
    (hbase : BaseDistanceGe6) (hM : DangerousSectorGe12)
    (hMim : SafeSectorGe12) :
    ∀ c ∈ grossComplex.dualCycles, c ∉ grossComplex.dualBoundaries →
      12 ≤ grossComplex.chainWeight c := by
  have hX : ∀ c ∈ (bbChainComplex grossA grossB).cycles,
      c ∉ (bbChainComplex grossA grossB).boundaries →
      12 ≤ (bbChainComplex grossA grossB).chainWeight c := fun c hc hnb =>
    gross_chainWeight_ge_12_of_sectors hbase hM hMim c hc hnb
  exact (bb_cycle_bound_iff_dual_bound grossA grossB 12).mp hX

/-! ## Pauli-level corollaries (the CSS distance bridge) -/

/-- Unconditional: an explicit weight-12 nontrivial logical Pauli operator of
the gross homological stabilizer group (the X-type encoding of the Phase-0
witness `τ(u*)`). -/
theorem gross_exists_weight12_logical :
    ∃ g : NQubitPauliGroupElement grossComplex.numQubits,
      Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
        grossComplex.homologicalStabilizerGroup ∧
      NQubitPauliGroupElement.weight g = 12 := by
  refine ⟨grossComplex.chainXOperator (coverPull1 uStar), ?_, ?_⟩
  · exact (HomologicalCode.chainXOperator_isNontrivialLogical_iff
      (X := grossComplex) (coverPull1 uStar)).mpr
      ⟨tauUStar_mem_cycles, tauUStar_not_mem_boundaries⟩
  · rw [HomologicalCode.weight_chainXOperator, chainWeight_tauUStar]

/-- Conditional Pauli-level lower bound: given the three sector inputs, every
nontrivial logical operator of the gross homological stabilizer group has weight
≥ 12. -/
theorem gross_logical_weight_ge_12_of_sectors
    (hbase : BaseDistanceGe6) (hM : DangerousSectorGe12)
    (hMim : SafeSectorGe12)
    (g : NQubitPauliGroupElement grossComplex.numQubits)
    (hg : Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
      grossComplex.homologicalStabilizerGroup) :
    12 ≤ NQubitPauliGroupElement.weight g :=
  HomologicalCode.chainWeight_lower_bound_transfers grossComplex 12
    (fun c hc hnb => gross_chainWeight_ge_12_of_sectors hbase hM hMim c hc hnb)
    (gross_dual_chainWeight_ge_12_of_sectors hbase hM hMim) g hg

/-- **Conditional Pauli-level `d(gross) = 12`**: given the three sector inputs,
12 is the least weight of a nontrivial logical operator of the gross homological
stabilizer group. -/
theorem gross_pauli_distance_eq_12_of_sectors
    (hbase : BaseDistanceGe6) (hM : DangerousSectorGe12)
    (hMim : SafeSectorGe12) :
    IsLeast {w : ℕ | ∃ g : NQubitPauliGroupElement grossComplex.numQubits,
      Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
        grossComplex.homologicalStabilizerGroup ∧
      NQubitPauliGroupElement.weight g = w} 12 := by
  constructor
  · obtain ⟨g, hg, hw⟩ := gross_exists_weight12_logical
    exact ⟨g, hg, hw⟩
  · rintro w ⟨g, hg, rfl⟩
    exact gross_logical_weight_ge_12_of_sectors hbase hM hMim g hg

end BB
end Homological
end Stabilizer
end Quantum
