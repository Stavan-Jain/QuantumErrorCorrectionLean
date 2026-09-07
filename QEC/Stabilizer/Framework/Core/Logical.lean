import QEC.Stabilizer.Framework.Core.Logical.LogicalOperators
import QEC.Stabilizer.Framework.Core.Logical.LogicalOperatorCoset
import QEC.Stabilizer.Framework.Core.Logical.LogicalGates
import QEC.Stabilizer.Framework.Core.Logical.LogicalGateGroup
import QEC.Stabilizer.Framework.Core.Logical.LogicalCliffordAction
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance

/-!
# Core: logical-operator theory

Logical operators, their cosets, logical gates, the Clifford action on logicals,
and code distance (distance is fundamentally a property of nontrivial logicals —
`chainWeight_lower_bound_transfers` etc.).
-/
