import QEC.Stabilizer.Codes._TEMPLATE
import QEC.Stabilizer.Codes.Toric
import QEC.Stabilizer.Codes.RotatedSurface
import QEC.Stabilizer.Codes.Repetition
import QEC.Stabilizer.Codes.Iceberg
import QEC.Stabilizer.Codes.BivariateBicycle
import QEC.Stabilizer.Codes.Mitten
import QEC.Stabilizer.Codes.Small

/-!
# Codes

Concrete stabilizer codes, organized by family:
- `Toric` — parametric toric code (code + lattice + homology)
- `RotatedSurface` — rotated surface code (code + lattice + homology)
- `Repetition` — classical repetition codes
- `Iceberg` — parametric `[[2m, 2m−2, 2]]` iceberg / generalized parity code
  family
- `BivariateBicycle` — chain-level gross `[[144,12,12]]` code + bb72 base
- `Small` — single-instance codes (Shor9, Steane7, [[5,1,3]], …)

The concrete concatenated codes (`Concat/`: Steane⊗Steane `[[49,1,9]]` and
Steane⊗`[[4,2,2]]` `[[28,2,6]]`) are **parked on branch `claude/z3z6-parked`**
pending de-nativization. The concatenation framework itself
(`Framework/Concatenation`, M1–M6) stays in this tree; it currently has no
concrete instance here.

`_TEMPLATE.lean` is the canonical structural reference for drafting new codes.
-/
