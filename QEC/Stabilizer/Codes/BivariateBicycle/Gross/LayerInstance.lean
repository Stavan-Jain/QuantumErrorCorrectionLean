/-
# The gross code as an instance of the parametric doubling layer

The retrofit queued by the doubling-layer PR: `grossCoverData` packages the
gross ↔ bb72 cover (`Defs.lean` / `CoverTransfer.lean`) as an
`XDoubleCoverData GrossGroup BaseGroup`, and the unconditional `d(gross) = 12`
is re-derived **through the layer's generic assemblies**
(`chain_distance_eq_double` / `pauli_distance_eq_double`), exactly as the
`[[72,4,8]]` instance is proven (that instance is parked on branch
`claude/z3z6-parked`).

The retrofit is *interface-level*: the layer's five per-instance inputs are
discharged by the existing gross theorems —

| layer input                | gross discharger                                              |
|----------------------------|---------------------------------------------------------------|
| bundle obligations         | `coverPi_fiber`, `coverPi_coverSec`, `coverPush_grossA/B`     |
| `StrongBaseFloor 6`        | `base_cycle_weight_ge_6` (small-cycle theorem)                |
| `DangerousFloorNZ 12`      | `LightStab.dangerous_sector_unconditional` ((M))              |
| `SafeFloor 12`             | `safe_sector_of_mim LightStab.mimBound_holds` ((M-im))        |
| tight witness              | `uStar` / `chainWeight_uStar` / `tauUStar_not_mem_boundaries` |

— so **no `native_decide` leaf is re-run or re-stated**: the engine files keep
computing against the gross definitions, and every bridge below is `rfl`
(`coverPush1`/`coverPull1` and the layer's `push1`/`pull1` are the *same*
`fiberSum`/`funLeft` construction applied to `coverPi`).  The bespoke
sector-dichotomy assembly in `Assembly.lean` (the layer's ancestor) is retained
as the conditional interface those dischargers hit; this file adds the
layer-routed, now-unconditional `IsLeast` endpoints
`gross_chain_distance_eq_12` and `gross_pauli_distance_eq_12`, statement-
identical to `Assembly.lean`'s conditional forms.
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Gross.SafeFloor.MImAssembly
import QEC.Stabilizer.Framework.Homological.BBDoubling

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open scoped BigOperators

-- Defeq checks through `fiberSum (Prod.map ⇑coverPi id)` unfold deep
-- `Prod`/`ZMod` instance chains, exactly as in `CoverTransfer.lean`.
set_option maxRecDepth 4096

/-! ## The bundle -/

/-- The gross ↔ bb72 cover as an instance of the parametric doubling layer.
Every field is an existing `Defs.lean` / `CoverTransfer.lean` object. -/
def grossCoverData : XDoubleCoverData GrossGroup BaseGroup where
  proj := coverPi
  deckS := deckS
  sec := coverSec
  Ac := grossA
  Bc := grossB
  Ab := baseA
  Bb := baseB
  deckS_ne_zero := deckS_ne_zero
  proj_fiber := coverPi_fiber
  proj_sec := coverPi_coverSec
  push_A := coverPush_grossA
  push_B := coverPush_grossB

/-! ## `rfl` bridges (the layer's derived objects ARE the gross ones) -/

lemma grossCoverData_coverComplex : grossCoverData.coverComplex = grossComplex :=
  rfl

lemma grossCoverData_baseComplex : grossCoverData.baseComplex = bb72Complex :=
  rfl

lemma grossCoverData_push1 : grossCoverData.push1 = coverPush1 := rfl

lemma grossCoverData_pull1 : grossCoverData.pull1 = coverPull1 := rfl

/-! ## The five layer inputs, from the existing gross theorems -/

/-- **`StrongBaseFloor 6`** — the small-cycle theorem (A4 Theorem A, boundaries
included). -/
theorem grossCoverData_strongBaseFloor : grossCoverData.StrongBaseFloor 6 := by
  intro u hcyc hne
  change 6 ≤ bb72Complex.chainWeight u
  rw [bb72Complex_chainWeight_eq]
  exact base_cycle_weight_ge_6 u hcyc hne

/-- **`DangerousFloorNZ 12`** — (M) on the `b ≠ 0` rungs, unconditional via the
light-stabilizer classification. -/
theorem grossCoverData_dangerousFloorNZ : grossCoverData.DangerousFloorNZ 12 :=
  fun v hv hnb hb h0 => LightStab.dangerous_sector_unconditional v hv hnb hb h0

/-- **`SafeFloor 12`** — (M-im), unconditional via `mimBound_holds`. -/
theorem grossCoverData_safeFloor : grossCoverData.SafeFloor 12 :=
  fun v hv hb => safe_sector_of_mim LightStab.mimBound_holds v hv hb

/-! ## Interface identities (documentation-grade: the layer's sector `Prop`s
are definitionally the `Assembly.lean` ones) -/

theorem grossCoverData_dangerousFloorNZ_iff :
    grossCoverData.DangerousFloorNZ 12 ↔ DangerousSectorGe12 :=
  Iff.rfl

theorem grossCoverData_safeFloor_iff :
    grossCoverData.SafeFloor 12 ↔ SafeSectorGe12 :=
  Iff.rfl

/-! ## The layer-routed unconditional endpoints -/

/-- **Unconditional chain-level `d(gross) = 12`, through the parametric layer**:
12 is the least weight of a nontrivial cycle of the gross complex.
Statement-identical to `gross_chain_distance_eq_12_of_sectors` with the sector
hypotheses discharged. -/
theorem gross_chain_distance_eq_12 :
    IsLeast {w : ℕ | ∃ v : GrossGroup × Fin 2 → ZMod 2,
      v ∈ grossComplex.cycles ∧ v ∉ grossComplex.boundaries ∧
      grossComplex.chainWeight v = w} 12 := by
  have h := grossCoverData.chain_distance_eq_double (d := 6)
    grossCoverData_strongBaseFloor grossCoverData_dangerousFloorNZ
    grossCoverData_safeFloor uStar uStar_mem_cycles chainWeight_uStar
    tauUStar_not_mem_boundaries
  norm_num at h
  exact h

/-- **Unconditional Pauli-level `d(gross) = 12`, through the parametric layer**:
12 is the least weight of a nontrivial logical operator of the gross homological
stabilizer group. Statement-identical to `gross_pauli_distance_eq_12_of_sectors`
with the sector hypotheses discharged. -/
theorem gross_pauli_distance_eq_12 :
    IsLeast {w : ℕ | ∃ g : NQubitPauliGroupElement grossComplex.numQubits,
      Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
        grossComplex.homologicalStabilizerGroup ∧
      NQubitPauliGroupElement.weight g = w} 12 := by
  have h := grossCoverData.pauli_distance_eq_double (d := 6)
    grossCoverData_strongBaseFloor grossCoverData_dangerousFloorNZ
    grossCoverData_safeFloor uStar uStar_mem_cycles chainWeight_uStar
    tauUStar_not_mem_boundaries
  norm_num at h
  exact h

end BB
end Homological
end Stabilizer
end Quantum
