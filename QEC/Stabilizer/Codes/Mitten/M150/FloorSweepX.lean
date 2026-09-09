/-
# M4 sweep obligations — X side (`ker H_X` triples, instances X0/X1)

The three `native_decide` leaves of the `ker H_X` floor: the two split
sweeps (every ≤9-light solution of `a₀u + a₁w = t·b_β` is classified)
and the `t`-join (every compatible classified pair is a generator row).
Tables/lists in the generated `FloorData.lean`; driver + soundness in
`FloorCore.lean`; design + offline validation in
`qec-lab:pipeline/attempts/mitten_150_30_10/m4_findings.md`.

Kept side-disjoint from `FloorSweepZ.lean` so lake parallelism overlaps
the two sides' native compute (budget rule 4, build_budget.md).
-/

import QEC.Stabilizer.Codes.Mitten.M150.FloorData

namespace Quantum
namespace Stabilizer
namespace Homological
namespace LP
namespace M150

/-- All 95 even splits of instance X0 classify into `clsX0`. -/
theorem checkAll_X0 : checkAll m4TX0 splitsX0 = true := by native_decide

/-- All 95 even splits of instance X1 classify into `clsX1`. -/
theorem checkAll_X1 : checkAll m4TX1 splitsX1 = true := by native_decide

/-- Every `t`-compatible weight-≤9 pair from `clsX0 × clsX1` joins to a
row of `H_Z` (`rowsXpk`). -/
theorem checkJoin_X : checkJoin clsX0 clsX1 rowsXpk = true := by
  native_decide

end M150
end LP
end Homological
end Stabilizer
end Quantum
