import QECLight

/-!
# Playground

A scratch file for trying things against QECLean. Edit freely — nothing here
is part of the library, and no `lean_lib` builds it.

It imports `QECLight`, which is the library minus the bivariate-bicycle code
family (too memory-hungry for a container or a shared session; see
`QECLight.lean`). For the gross-code results, use `import QEC` in a local
checkout with the memory to spare.

Put your cursor at the end of a line to see the goal state in the InfoView.
-/

open Quantum.StabilizerGroup

-- The two central definitions: an `[[n, k]]` stabilizer code, and one whose
-- distance has been proved.
#check @StabilizerCode
#check @StabilizerCodeWithDistance
#check @HasCodeDistance

-- A worked result to inspect: the `[[5, 1, 3]]` perfect code, packaged with its
-- proved distance. (It is the repo's first non-CSS code.)
#check FiveQubit_5_1_3.stabilizerCodeWithDistance

-- The same object through the scoped `[[n, k, d]]` type notation: `Code[[5, 1, 3]]` is
-- `StabilizerCodeWithDistance 5 1 3` (and `Code[[5, 1]]` is `StabilizerCode 5 1`). The
-- `open Quantum.StabilizerGroup` above activates it.
#check (FiveQubit_5_1_3.stabilizerCodeWithDistance : Code[[5, 1, 3]])
#check (Steane7.stabilizerCode : Code[[7, 1]])
#check (Steane7.stabilizerCodeWithDistance : Code[[7, 1, 3]])

-- The parametric toric code, for every `L ≥ 2`. (It lives under
-- `Quantum.Stabilizer.Lattice`, not the `Quantum.StabilizerGroup` opened above.)
#check @Quantum.Stabilizer.Lattice.toricHomologicalCode

/-
Your turn. For example:

example : 2 + 2 = 4 := by decide
-/
