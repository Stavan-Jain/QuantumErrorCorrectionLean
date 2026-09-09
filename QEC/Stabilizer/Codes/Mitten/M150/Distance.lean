/-
# The `[[150,30,10]]` mitten code's distance capstones

M5 of the mitten certification: the two chain floors (`floorZ`,
`floorX`) transfer through the CSS bridge
(`chainWeight_lower_bound_transfers` at `K = 10`) to the `≥ 10` half,
the M3 witness (`Witness.lean`) supplies the `≤ 10` half, and the two
assemble into `HasCodeDistance m150StabilizerCode 10` and the bundled

  `mitten150StabilizerCodeWithDistance : StabilizerCodeWithDistance 150 30 10`

— the library's first qLDPC `[[n,k,d]]` bundle and the first formally
verified non-abelian lifted-product distance.  Attempt state:
`qec-lab:pipeline/attempts/mitten_150_30_10/`.
-/

import QEC.Stabilizer.Codes.Mitten.M150.FloorZSide
import QEC.Stabilizer.Codes.Mitten.M150.FloorXSide
import QEC.Stabilizer.Codes.Mitten.M150.Witness

namespace Quantum
namespace Stabilizer
namespace Homological
namespace LP
namespace M150

open Quantum.StabilizerGroup NQubitPauliGroupElement

/-- Contrapositive `floorX`: non-boundary cycles have weight ≥ 10. -/
private lemma floorX_contra : ∀ c ∈ m150Complex.cycles,
    c ∉ m150Complex.boundaries → 10 ≤ m150Complex.chainWeight c := by
  intro c hc hnb
  by_contra hlt
  push Not at hlt
  exact hnb (floorX c ((m150Complex.mem_cycles_iff c).mp hc) (by omega))

/-- Contrapositive `floorZ`: non-dual-boundary dual cycles have weight
≥ 10. -/
private lemma floorZ_contra : ∀ c ∈ m150Complex.dualCycles,
    c ∉ m150Complex.dualBoundaries → 10 ≤ m150Complex.chainWeight c := by
  intro c hc hnb
  by_contra hlt
  push Not at hlt
  exact hnb (floorZ c (LinearMap.mem_ker.mp hc) (by omega))

/-- **The `≥ 10` half**: every nontrivial logical of the mitten
homological stabilizer group has weight ≥ 10. -/
theorem m150_logical_weight_ge_10
    (g : NQubitPauliGroupElement m150Complex.numQubits)
    (hg : IsNontrivialLogicalOperator g
      m150Complex.homologicalStabilizerGroup) :
    10 ≤ NQubitPauliGroupElement.weight g :=
  HomologicalCode.chainWeight_lower_bound_transfers m150Complex 10
    floorX_contra floorZ_contra g hg

/-- **`HasCodeDistance m150StabilizerCode 10`** — the packaged
`[[150,30,10]]` mitten code has distance exactly 10.  The `≥ 10` half is
the M4 floors through the CSS bridge; the `≤ 10` half is the M3
weight-10 witness `chainZOperator witChain`.  Axiom-clean (the standard
three + the `native_decide` compiler axiom). -/
theorem m150StabilizerCode_hasCodeDistance_10 :
    HasCodeDistance m150StabilizerCode 10 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · intro g hg _
    exact m150_logical_weight_ge_10 g
      ((IsNontrivialLogicalOperator_of_toSubgroup_eq g
        m150StabilizerCode_toSubgroup_eq).mp hg)
  · refine ⟨m150Complex.chainZOperator witChain, ?_, ?_⟩
    · refine (IsNontrivialLogicalOperator_of_toSubgroup_eq _
        m150StabilizerCode_toSubgroup_eq).mpr ?_
      rw [HomologicalCode.chainZOperator_isNontrivialLogical_iff]
      exact ⟨LinearMap.mem_ker.mpr witChain_dualBoundary,
        witChain_not_mem_dualBoundaries⟩
    · rw [HomologicalCode.weight_chainZOperator]
      exact chainWeight_witChain

/-- **The `[[150, 30, 10]]` mitten code as a fully-parametrized
object** — the non-abelian lifted product LP(A,B) over `𝔽₂[C₅×S₃]`
bundled with its distance proof, all three `[[n, k, d]]` parameters in
the type. -/
noncomputable def mitten150StabilizerCodeWithDistance :
    StabilizerCodeWithDistance 150 30 10 where
  toStabilizerCode := m150StabilizerCode
  hasDistance := m150StabilizerCode_hasCodeDistance_10

end M150
end LP
end Homological
end Stabilizer
end Quantum
