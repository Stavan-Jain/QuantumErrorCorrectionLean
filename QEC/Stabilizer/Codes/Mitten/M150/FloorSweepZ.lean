/-
# M4 sweep obligations — Z side (`ker H_Z` triples, instances Z0/Z1)

Mirror of `FloorSweepX.lean` for the `ker H_Z` floor: the two split
sweeps (every ≤9-light solution of `u·b₀~ + w·b₁~ = a_α~·t` is
classified) and the `t`-join onto the rows of `H_X` (`rowsZpk`).
-/

import QEC.Stabilizer.Codes.Mitten.M150.FloorData

namespace Quantum
namespace Stabilizer
namespace Homological
namespace LP
namespace M150

/-- All 95 even splits of instance Z0 classify into `clsZ0`. -/
theorem checkAll_Z0 : checkAll m4TZ0 splitsZ0 = true := by native_decide

/-- All 95 even splits of instance Z1 classify into `clsZ1`. -/
theorem checkAll_Z1 : checkAll m4TZ1 splitsZ1 = true := by native_decide

/-- Every `t`-compatible weight-≤9 pair from `clsZ0 × clsZ1` joins to a
row of `H_X` (`rowsZpk`). -/
theorem checkJoin_Z : checkJoin clsZ0 clsZ1 rowsZpk = true := by
  native_decide

end M150
end LP
end Homological
end Stabilizer
end Quantum
