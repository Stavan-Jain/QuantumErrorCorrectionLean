import QEC.Stabilizer.Framework.Core.Stabilizer
import QEC.Stabilizer.Framework.Core.Logical
import QEC.Stabilizer.Framework.Core.CSS
import QEC.Stabilizer.Framework.Core.CodeNotation

/-!
# Framework.Core

Abstract stabilizer-formalism content, split into three buckets:
- `QEC.Stabilizer.Framework.Core.Stabilizer` — stabilizer-group + codespace +
  centralizer
- `QEC.Stabilizer.Framework.Core.Logical` — logical-operator theory + code
  distance
- `QEC.Stabilizer.Framework.Core.CSS` — CSS-code theory
- `QEC.Stabilizer.Framework.Core.CodeNotation` — scoped `Code[[n, k]]` /
  `Code[[n, k, d]]` type notation for the bundled codes
-/
