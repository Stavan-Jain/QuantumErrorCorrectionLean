import QEC.Stabilizer.Framework.Core.Logical.CodeDistance

/-!
# `[[n, k, d]]` code-parameter notation

Scoped type notation for the bundled code structures, following the standard
`[[n, k, d]]` parameter convention described in `CodeDistance.lean`:

- `Code[[n, k]]` is `StabilizerCode n k` — `n` physical qubits, `k` logical
  qubits, and nothing else: the bare code;
- `Code[[n, k, d]]` is `StabilizerCodeWithDistance n k d` — additionally, a
  proved distance `d`;
- `Code[[n, k]]ₗ` is `StabilizerCodeWithLogicals n k` — additionally, a chosen
  logical basis (the trailing `ₗ` is `\_l`).

Bare `[[n, k]]` already parses as a nested list literal, hence the `Code`
prefix: the leading token is `Code[[`, and the closing brackets are two ordinary
`]` tokens (a single `]]` token would break every nested `[[…]]` / `#[#[…]]`
literal in scope). The logical-basis form adds a trailing `ₗ` token after the
closing brackets, so `Code[[n, k]]` and `Code[[n, k]]ₗ` are distinguished by
longest match. The notation lives in the `Quantum.StabilizerGroup` scope, so it
is active inside that namespace and after `open Quantum.StabilizerGroup` /
`open scoped Quantum.StabilizerGroup`, and each form has an unexpander so goals
and `#check` output display `Code[[7, 1]]` rather than `StabilizerCode 7 1`.
-/

namespace Quantum.StabilizerGroup

/-- `Code[[n, k]]` is the type `StabilizerCode n k` of `[[n, k]]` stabilizer
codes: `n` physical qubits, `k` logical qubits. Scoped:
`open scoped Quantum.StabilizerGroup`. -/
scoped notation:max "Code[[" n ", " k "]" "]" => StabilizerCode n k

/-- `Code[[n, k, d]]` is the type `StabilizerCodeWithDistance n k d` of
`[[n, k, d]]` stabilizer codes packaged with a proof that their distance is `d`.
Scoped: `open scoped Quantum.StabilizerGroup`. -/
scoped notation:max "Code[[" n ", " k ", " d "]" "]" => StabilizerCodeWithDistance n k d

/-- `Code[[n, k]]ₗ` is the type `StabilizerCodeWithLogicals n k` of `[[n, k]]`
stabilizer codes packaged with a chosen logical basis (`X̄ℓ`, `Z̄ℓ` for each of
the `k` logical qubits). Scoped: `open scoped Quantum.StabilizerGroup`. -/
scoped notation:max "Code[[" n ", " k "]" "]" "ₗ" => StabilizerCodeWithLogicals n k

end Quantum.StabilizerGroup

/-!
## Round-trip tests

Each form is the corresponding structure type, definitionally and syntactically.
-/

section RoundTrip

open Quantum.StabilizerGroup

example : Code[[7, 1]] = StabilizerCode 7 1 := rfl

example : Code[[5, 1, 3]] = StabilizerCodeWithDistance 5 1 3 := rfl

example (n k : ℕ) : Code[[n, k]] = StabilizerCode n k := rfl

example (n k d : ℕ) : Code[[n, k, d]] = StabilizerCodeWithDistance n k d := rfl

example (C : Code[[7, 1]]) : Code[[7, 1]] := C

example (C : Code[[5, 1, 3]]) : Code[[5, 1]] := C.toStabilizerCode

example : Code[[7, 1]]ₗ = StabilizerCodeWithLogicals 7 1 := rfl

example (n k : ℕ) : Code[[n, k]]ₗ = StabilizerCodeWithLogicals n k := rfl

example (C : Code[[7, 1]]ₗ) : Code[[7, 1]] := C.toStabilizerCode

example (C : Code[[7, 1]]ₗ) : List (Quantum.NQubitPauliGroupElement 7) := C.generatorsList

end RoundTrip
