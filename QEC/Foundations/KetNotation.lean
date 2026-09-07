import Lean.PrettyPrinter.Delaborator.Basic
import QEC.Foundations.Basic

/-!
# Dirac ket notation

Scoped notation for the computational-basis kets defined in `Basic.lean`, so
proofs and statements can be written the way they are on paper: `|0⟩`, `|+⟩`,
`|01⟩`, `|0101⟩`, …

`|b⟩` for a bitstring `b` of length `n ≥ 1` is the standard basis state of the
corresponding `n`-qubit state type, i.e. exactly the pre-existing term for it:

| length  | elaborates to                   | type              |
|---------|---------------------------------|-------------------|
| 1       | `ket0`, `ket1`                  | `Qubit`           |
| 2       | `ket00`, …, `ket11`             | `TwoQubitState`   |
| 3       | `ket000`, …, `ket111`           | `ThreeQubitState` |
| `n ≥ 4` | `nQubitKet n ![b₀, …, bₙ₋₁]`    | `NQubitState n`   |

The tuple-indexed state types stop at three qubits, so from four qubits on the
only `n`-qubit state type is `NQubitState n`. `|+⟩` and `|-⟩` are the
Hadamard-basis kets `ketPlus` and `ketMinus`.

**Parsing.** The bitstring lexes as a single numeral token (`0101` is one `num`
literal), and the macro reads that token's *source text* — `"0101"`, leading
zeros included, where the literal's numeric value would lose them — accepting
only the digits `0` and `1`. No new token is introduced: `|` and `⟩` are the
ordinary bar and right-angle tokens, and the whole form is `atomic`, so `|x|`
(absolute value) and `{x | p x}` (set-builder) parse exactly as before.

Bring the notation into scope with `open scoped Quantum` (or `open Quantum`). It
is `scoped` deliberately, like this library's other notation, so that files
which never mention kets do not get a term-level parser on the bar token. Each
ket displays back as `|…⟩` in goals while the scope is open
(`set_option pp.notation false` recovers the names).

The kets themselves — `ket0`, `ket00`, `ketPlus`, `nQubitKet`, … — are defined
in `QEC/Foundations/Basic.lean`; this file adds only syntax and display for
them, following the same notation-in-its-own-module convention as
`QEC/Stabilizer/Foundations/PauliGroup/Notation.lean`.
-/

namespace Quantum

section KetNotation

open Lean

/-- `|b⟩` for a bitstring `b` (e.g. `|0⟩`, `|01⟩`, `|0101⟩`): the computational
basis state of the `n`-qubit state type, `n` the length of `b` — `ket0`/`ket1`
for one qubit, `ket00`…`ket11` for two, `ket000`…`ket111` for three, and
`nQubitKet n ![b₀, …, bₙ₋₁]` from four qubits on. Scoped: `open scoped Quantum`.
-/
scoped syntax:max (name := ketLit) atomic("|" noWs num noWs "⟩") : term

/-- The bit `0`/`1` as a numeral term (for the `![…]` of an `n ≥ 4` ket). -/
private def bitLit (c : Char) : Term :=
  ⟨(Syntax.mkNumLit (if c == '1' then "1" else "0")).raw⟩

macro_rules
  | `(|$b:num⟩) => do
    let some s := b.raw.isLit? numLitKind
      | Macro.throwErrorAt b "expected a bitstring of 0s and 1s"
    unless s.all fun c => c == '0' || c == '1' do
      Macro.throwErrorAt b s!"invalid ket bitstring '{s}': expected the digits 0 and 1 only"
    match s with
    | "0" => `(ket0)
    | "1" => `(ket1)
    | "00" => `(ket00)
    | "01" => `(ket01)
    | "10" => `(ket10)
    | "11" => `(ket11)
    | "000" => `(ket000)
    | "001" => `(ket001)
    | "010" => `(ket010)
    | "011" => `(ket011)
    | "100" => `(ket100)
    | "101" => `(ket101)
    | "110" => `(ket110)
    | "111" => `(ket111)
    | _ =>
      let bits : Syntax.TSepArray `term "," := .ofElems (s.toList.toArray.map bitLit)
      `(nQubitKet $(quote s.length) ![$bits,*])

/-- Hadamard-basis ket `|+⟩ = (|0⟩ + |1⟩)/√2`, i.e. `ketPlus`. -/
scoped notation "|+⟩" => ketPlus

/-- Hadamard-basis ket `|−⟩ = (|0⟩ − |1⟩)/√2`, i.e. `ketMinus`. -/
scoped notation "|-⟩" => ketMinus

/-! ### Display

The named kets display back as `|…⟩` (one unexpander each), and an `n ≥ 4` ket
`nQubitKet n ![b₀, …, bₙ₋₁]` with literal `n` and literal bits displays as
`|b₀…bₙ₋₁⟩`. All of these are scoped with the notation. -/

/-- `ket0` displays as `|0⟩`. -/
@[scoped app_unexpander Quantum.ket0] def unexpandKet0 : PrettyPrinter.Unexpander
  | `($_:ident) => `(|0⟩)
  | _ => throw ()

/-- `ket1` displays as `|1⟩`. -/
@[scoped app_unexpander Quantum.ket1] def unexpandKet1 : PrettyPrinter.Unexpander
  | `($_:ident) => `(|1⟩)
  | _ => throw ()

/-- `ket00` displays as `|00⟩`. -/
@[scoped app_unexpander Quantum.ket00] def unexpandKet00 : PrettyPrinter.Unexpander
  | `($_:ident) => `(|00⟩)
  | _ => throw ()

/-- `ket01` displays as `|01⟩`. -/
@[scoped app_unexpander Quantum.ket01] def unexpandKet01 : PrettyPrinter.Unexpander
  | `($_:ident) => `(|01⟩)
  | _ => throw ()

/-- `ket10` displays as `|10⟩`. -/
@[scoped app_unexpander Quantum.ket10] def unexpandKet10 : PrettyPrinter.Unexpander
  | `($_:ident) => `(|10⟩)
  | _ => throw ()

/-- `ket11` displays as `|11⟩`. -/
@[scoped app_unexpander Quantum.ket11] def unexpandKet11 : PrettyPrinter.Unexpander
  | `($_:ident) => `(|11⟩)
  | _ => throw ()

/-- `ket000` displays as `|000⟩`. -/
@[scoped app_unexpander Quantum.ket000] def unexpandKet000 : PrettyPrinter.Unexpander
  | `($_:ident) => `(|000⟩)
  | _ => throw ()

/-- `ket001` displays as `|001⟩`. -/
@[scoped app_unexpander Quantum.ket001] def unexpandKet001 : PrettyPrinter.Unexpander
  | `($_:ident) => `(|001⟩)
  | _ => throw ()

/-- `ket010` displays as `|010⟩`. -/
@[scoped app_unexpander Quantum.ket010] def unexpandKet010 : PrettyPrinter.Unexpander
  | `($_:ident) => `(|010⟩)
  | _ => throw ()

/-- `ket011` displays as `|011⟩`. -/
@[scoped app_unexpander Quantum.ket011] def unexpandKet011 : PrettyPrinter.Unexpander
  | `($_:ident) => `(|011⟩)
  | _ => throw ()

/-- `ket100` displays as `|100⟩`. -/
@[scoped app_unexpander Quantum.ket100] def unexpandKet100 : PrettyPrinter.Unexpander
  | `($_:ident) => `(|100⟩)
  | _ => throw ()

/-- `ket101` displays as `|101⟩`. -/
@[scoped app_unexpander Quantum.ket101] def unexpandKet101 : PrettyPrinter.Unexpander
  | `($_:ident) => `(|101⟩)
  | _ => throw ()

/-- `ket110` displays as `|110⟩`. -/
@[scoped app_unexpander Quantum.ket110] def unexpandKet110 : PrettyPrinter.Unexpander
  | `($_:ident) => `(|110⟩)
  | _ => throw ()

/-- `ket111` displays as `|111⟩`. -/
@[scoped app_unexpander Quantum.ket111] def unexpandKet111 : PrettyPrinter.Unexpander
  | `($_:ident) => `(|111⟩)
  | _ => throw ()

/-- A literal natural: a raw `Nat` literal or `OfNat.ofNat` of one. -/
private def natLit? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal k) => some k
  | _ =>
    if e.isAppOfArity ``OfNat.ofNat 3 then
      match e.getArg! 1 with
      | .lit (.natVal k) => some k
      | _ => none
    else none

/-- The literal bits of a `![b₀, …, bₙ₋₁]` vector (a `Matrix.vecCons` chain
ending in `Matrix.vecEmpty`), each a literal `0` or `1`; `none` on any other
shape. -/
private partial def vecBits? (e : Expr) (acc : Array Nat := #[]) : Option (Array Nat) :=
  if e.isAppOfArity ``Matrix.vecCons 4 then do
    let b ← natLit? (e.getArg! 2)
    guard (b == 0 || b == 1)
    vecBits? (e.getArg! 3) (acc.push b)
  else if e.isAppOfArity ``Matrix.vecEmpty 1 then
    some acc
  else none

open PrettyPrinter Delaborator SubExpr in
/-- Delaborate `nQubitKet n ![b₀, …, bₙ₋₁]` with literal `n ≥ 4` and literal
bits back to `|b₀…bₙ₋₁⟩`. Stays silent on any other shape, and on `n ≤ 3` (where
`|…⟩` denotes the tuple-indexed kets, so displaying it would not round-trip). -/
@[scoped app_delab Quantum.nQubitKet] def delabNQubitKet : Delab :=
  whenPPOption getPPNotation <| whenNotPPOption getPPExplicit do
    let e ← getExpr
    unless e.isAppOfArity ``Quantum.nQubitKet 2 do failure
    let some n := natLit? (e.getArg! 0) | failure
    let some bits := vecBits? (e.getArg! 1) | failure
    unless bits.size == n && 4 ≤ n do failure
    let s := String.ofList (bits.toList.map fun b => if b == 1 then '1' else '0')
    `(|$(Syntax.mkNumLit s)⟩)

end KetNotation

/-!
### Round-trip tests

Each ket literal elaborates to exactly the pre-existing term.
-/

section KetRoundTrip

example : |0⟩ = ket0 := rfl
example : |1⟩ = ket1 := rfl
example : |00⟩ = ket00 := rfl
example : |01⟩ = ket01 := rfl
example : |10⟩ = ket10 := rfl
example : |11⟩ = ket11 := rfl
example : |000⟩ = ket000 := rfl
example : |101⟩ = ket101 := rfl
example : |111⟩ = ket111 := rfl
example : |0101⟩ = nQubitKet 4 ![0, 1, 0, 1] := rfl
example : |1000000⟩ = nQubitKet 7 ![1, 0, 0, 0, 0, 0, 0] := rfl
example : (|0110⟩ : NQubitState 4).val = basisVec ![0, 1, 1, 0] := rfl
example : |+⟩ = ketPlus := rfl
example : |-⟩ = ketMinus := rfl

end KetRoundTrip

end Quantum
