import QEC.Stabilizer.Codes.Iceberg.N

/-!
# Iceberg codes

The parametric `[[2m, 2m − 2, 2]]` iceberg / generalized parity code family for
`m ≥ 2`. Generators `{XX…X, ZZ…Z}` acting on all `2m` qubits.

- `N`: the parametric `[[2m, 2m−2, 2]]` formalization (this file)

The `m = 2` instance is also formalized separately in
`Codes/Small/FourQubit_4_2_2.lean` under a different logical basis; they coexist
as two formalizations of the same code (mirroring the `Repetition3.lean` /
`RepetitionN.lean` pattern).
-/
