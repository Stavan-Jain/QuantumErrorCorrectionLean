import Lean.PrettyPrinter.Delaborator.Basic
import QEC.Stabilizer.Foundations.PauliGroup.NQubitElement

/-!
# Physics-style construction notation for `NQubitPauliGroupElement`

This file provides scoped notation for writing concrete n-qubit Pauli group elements the
way the physics literature does:

- `σ[XXIXII]` — phase `+1` (`phasePower = 0`)
- `iσ[XXIXII]` — phase `i` (`phasePower = 1`)
- `-σ[XXIXII]` — phase `-1` (`phasePower = 2`)
- `-iσ[XXIXII]` — phase `-i` (`phasePower = 3`)

and for the bare Pauli string with no phase at all, an `NQubitPauliOperator`:

- `P[XXIXII]` — the operator part on its own, i.e. `σ[XXIXII].operators`

The letters between the brackets form a single identifier over the alphabet `X`, `Y`,
`Z`, `I`, read left to right as qubits `0, 1, …`; the number of letters fixes the number
of qubits, so `σ[XIZ] : NQubitPauliGroupElement 3` and `P[XIZ] : NQubitPauliOperator 3`
with no ascription needed.

Parametric families, whose qubit count and positions are terms rather than numerals, use
the **symbolic form** with the same leading tokens:

- `σ[n | i ↦ Z, j ↦ Z]` — `Z` at qubits `i` and `j` of `n`, phase `+1`
- `iσ[n | …]`, `-σ[n | …]`, `-iσ[n | …]` — the same with the phase prefixes
- `P[n | i ↦ Z, j ↦ Z]` — the bare Pauli string

where `n` and the indices are arbitrary terms and the letters are `X`, `Y`, `Z` (see
§ "Symbolic (parametric) form" below).

The notation is **scoped**: enable it with `open scoped Pauli`. It must be opt-in
because any notation whose leading token is `σ[` takes over that token from `GetElem`
indexing (`σ[i]`) for variables named `σ` (likewise `iσ[…]` for variables named `iσ`, and
`P[…]` for variables named `P`). The phase prefixes are part of the leading token (`-σ[`,
`iσ[`, `-iσ[`): write them with no space before `σ[`, and keep spaces around a binary `-`
(`a - σ[XX]`) when you mean subtraction with the scope open.

## Elaboration guarantee

`σ[…]` elaborates to **exactly** the canonical literal normal form used throughout the
concrete code files:

```lean
⟨phase, ((NQubitPauliOperator.identity n).set i₀ op₀).set i₁ op₁ ⋯⟩
```

with `.set` applied only at the non-identity positions, in increasing index order, and
`P[…]` elaborates to exactly the operator half of that form, the bare `.set` chain (so
`P[II…I]` is `NQubitPauliOperator.identity n` itself). The notation is a macro (pure
syntax expansion into that form), so kernel-reduction behavior and every existing
`simp`/`decide`/`rfl` proof over such literals are unchanged. In particular there is
deliberately no `ofList`-style helper on the elaboration path: a list lookup is an O(n)
walk under kernel reduction (see the axiom-policy notes in `CLAUDE.md`), whereas the
`.set` chain is the form all existing proofs already consume.

## Delaborator

Terms of exactly that literal shape (literal phase, literal indices, `PauliOperator`
constructors, literal qubit count) display back as `σ[…]`/`iσ[…]`/`-σ[…]`/`-iσ[…]` in
goals and diagnostics, and a literal-shaped `.set` chain on its own displays as `P[…]`
(so an element whose phase is not a literal shows as `⟨k, P[…]⟩`; a bare `identity n`
keeps its name). The letters form is used only for a chain in the literal normal form —
literal indices in strictly increasing order, no explicit `I` — so that the display
re-parses to the very same term. Any other `.set` chain over an `identity n` whose
operators are `X`/`Y`/`Z` constructors — symbolic qubit count or indices, literal indices
out of order or out of range — displays in the symbolic form `σ[n | i ↦ Z, …]` /
`P[n | i ↦ Z, …]`, with the `.set`s listed innermost first (the written order). Anything
else — variable phase or operators, an explicit `I`, a chain not rooted at `identity` — is
left to the default printer. The delaborators are `scoped` with the notation, so a goal
only ever shows syntax the current file can parse; `set_option pp.notation false` (or
`pp.explicit true`) recovers the raw term.
-/

namespace Pauli

open Lean

/-- `σ[XZIX]` is the `NQubitPauliGroupElement` with phase `+1` (`phasePower = 0`) whose
operator at qubit `k` is the `k`-th letter (letters `X`, `Y`, `Z`, `I`; qubit count =
letter count). Scoped: enable with `open scoped Pauli`. Elaborates to the literal
`⟨0, (NQubitPauliOperator.identity n).set i₀ op₀ …⟩` normal form. -/
scoped syntax:max (name := sigma) "σ[" ident "]" : term

/-- `iσ[XZIX]`: as `σ[XZIX]` but with phase `i` (`phasePower = 1`).
Scoped: enable with `open scoped Pauli`. -/
scoped syntax:max (name := iSigma) "iσ[" ident "]" : term

/-- `-σ[XZIX]`: as `σ[XZIX]` but with phase `-1` (`phasePower = 2`).
Scoped: enable with `open scoped Pauli`. -/
scoped syntax:max (name := negSigma) "-σ[" ident "]" : term

/-- `-iσ[XZIX]`: as `σ[XZIX]` but with phase `-i` (`phasePower = 3`).
Scoped: enable with `open scoped Pauli`. -/
scoped syntax:max (name := negISigma) "-iσ[" ident "]" : term

/-- `P[XZIX]` is the bare Pauli string, an `NQubitPauliOperator` with no phase, whose
operator at qubit `k` is the `k`-th letter (letters `X`, `Y`, `Z`, `I`; qubit count =
letter count); it is `σ[XZIX].operators`. Scoped: enable with `open scoped Pauli`.
Elaborates to the literal `(NQubitPauliOperator.identity n).set i₀ op₀ …` normal form. -/
scoped syntax:max (name := pauliString) "P[" ident "]" : term

/-- Split the letters identifier of a `σ[…]`-family literal into its characters, checking
that the identifier is a single atomic name over the alphabet `X`, `Y`, `Z`, `I`. -/
def pauliLetters (stx : Syntax) : MacroM (List Char) := do
  let .str .anonymous s := stx.getId.eraseMacroScopes
    | Macro.throwErrorAt stx "expected a string of Pauli letters (X, Y, Z, I)"
  let cs := s.toList
  for c in cs do
    unless c == 'X' || c == 'Y' || c == 'Z' || c == 'I' do
      Macro.throwErrorAt stx s!"invalid Pauli letter '{c}': expected X, Y, Z, or I"
  return cs

/-- Expand the letters of a literal into the canonical operator-string normal form
`(NQubitPauliOperator.identity n).set i₀ op₀ …`, setting only the non-identity positions,
in increasing index order. This is the expansion of `P[…]`, and the operator half of the
`σ[…]` family. -/
def expandPauliString (letters : Syntax) : MacroM Term := do
  let cs ← pauliLetters letters
  let mut ops : Term ← `(Quantum.NQubitPauliOperator.identity $(quote cs.length))
  let mut i : Nat := 0
  for c in cs do
    if c != 'I' then
      let opStx : Term ← match c with
        | 'X' => `(Quantum.PauliOperator.X)
        | 'Y' => `(Quantum.PauliOperator.Y)
        | _ => `(Quantum.PauliOperator.Z)
      ops ← `(Quantum.NQubitPauliOperator.set $ops $(quote i) $opStx)
    i := i + 1
  return ops

/-- Expand a `σ[…]`-family literal with the given `phasePower` into the canonical normal
form `NQubitPauliGroupElement.mk phase ((NQubitPauliOperator.identity n).set i₀ op₀ …)`,
whose operator part is the `expandPauliString` chain. -/
def expandSigma (phase : Nat) (letters : Syntax) : MacroM Term := do
  let ops ← expandPauliString letters
  `(Quantum.NQubitPauliGroupElement.mk $(quote phase) $ops)

macro_rules
  | `(σ[$letters:ident]) => expandSigma 0 letters
  | `(iσ[$letters:ident]) => expandSigma 1 letters
  | `(-σ[$letters:ident]) => expandSigma 2 letters
  | `(-iσ[$letters:ident]) => expandSigma 3 letters
  | `(P[$letters:ident]) => expandPauliString letters

/-!
## Symbolic (parametric) form

`σ[n | i ↦ Z, j ↦ Z]` is the same literal with the qubit count `n` and the indices
`i`, `j` arbitrary terms — the form parametric families need, where the qubit count is
`numQubits L` or `n + 2` and the positions are `hEdge L x y` or `Fin.succ i`. It expands
to exactly

```lean
⟨0, ((NQubitPauliOperator.identity n).set i PauliOperator.Z).set j PauliOperator.Z⟩
```

with the `.set`s applied **in the written order** (there is no index to sort by), so a
downstream `simp [NQubitPauliOperator.set, NQubitPauliOperator.identity]` sees the same
chain it always did. The letters are `X`, `Y`, `Z` (an explicit `I` is rejected: leave the
qubit out instead). The phase prefixes and `P[n | …]` work the same way.
-/

/-- One qubit assignment `i ↦ Z` in a symbolic `σ[n | …]`-family literal: the index `i` is
an arbitrary term, the letter is `X`, `Y`, or `Z`. -/
syntax pauliAssign := term " ↦ " ident

/-- `σ[n | i ↦ Z, j ↦ Z]` is the `NQubitPauliGroupElement n` with phase `+1` whose
operator at `i` is `Z`, at `j` is `Z`, and `I` elsewhere, for arbitrary terms `n`, `i`,
`j` (letters `X`, `Y`, `Z`). Scoped: enable with `open scoped Pauli`. Elaborates to the
literal `⟨0, ((NQubitPauliOperator.identity n).set i Z).set j Z⟩`, the `.set`s in the
written order. -/
scoped syntax:max (name := sigmaSym) "σ[" term " | " pauliAssign,+ "]" : term

/-- `iσ[n | i ↦ Z, …]`: as `σ[n | i ↦ Z, …]` but with phase `i` (`phasePower = 1`).
Scoped: enable with `open scoped Pauli`. -/
scoped syntax:max (name := iSigmaSym) "iσ[" term " | " pauliAssign,+ "]" : term

/-- `-σ[n | i ↦ Z, …]`: as `σ[n | i ↦ Z, …]` but with phase `-1` (`phasePower = 2`).
Scoped: enable with `open scoped Pauli`. -/
scoped syntax:max (name := negSigmaSym) "-σ[" term " | " pauliAssign,+ "]" : term

/-- `-iσ[n | i ↦ Z, …]`: as `σ[n | i ↦ Z, …]` but with phase `-i` (`phasePower = 3`).
Scoped: enable with `open scoped Pauli`. -/
scoped syntax:max (name := negISigmaSym) "-iσ[" term " | " pauliAssign,+ "]" : term

/-- `P[n | i ↦ Z, j ↦ Z]` is the bare Pauli string on `n` qubits with `Z` at `i` and at
`j`, for arbitrary terms `n`, `i`, `j`; it is `σ[n | i ↦ Z, j ↦ Z].operators`. Scoped:
enable with `open scoped Pauli`. Elaborates to the literal
`((NQubitPauliOperator.identity n).set i Z).set j Z`, the `.set`s in the written order. -/
scoped syntax:max (name := pauliStringSym) "P[" term " | " pauliAssign,+ "]" : term

/-- The `PauliOperator` constructor named by a letter identifier `X`, `Y`, or `Z`. -/
def pauliOpOfLetter (c : Ident) : MacroM Term :=
  match c.getId.eraseMacroScopes with
  | .str .anonymous "X" => `(Quantum.PauliOperator.X)
  | .str .anonymous "Y" => `(Quantum.PauliOperator.Y)
  | .str .anonymous "Z" => `(Quantum.PauliOperator.Z)
  | _ => Macro.throwErrorAt c "expected a Pauli letter X, Y, or Z"

/-- Expand the symbolic assignments `i₀ ↦ op₀, i₁ ↦ op₁, …` on `n` qubits into the chain
`((NQubitPauliOperator.identity n).set i₀ op₀).set i₁ op₁ …`, in the written order. This
is the expansion of `P[n | …]`, and the operator half of the `σ[n | …]` family. -/
def expandSymbolicString (n : Term) (idxs : Array Term) (letters : Array Ident) :
    MacroM Term := do
  let mut ops : Term ← `(Quantum.NQubitPauliOperator.identity $n)
  for i in idxs, c in letters do
    let opStx ← pauliOpOfLetter c
    ops ← `(Quantum.NQubitPauliOperator.set $ops $i $opStx)
  return ops

/-- Expand a symbolic `σ[n | …]`-family literal with the given `phasePower` into
`NQubitPauliGroupElement.mk phase ((NQubitPauliOperator.identity n).set i₀ op₀ …)`. -/
def expandSymbolicSigma (phase : Nat) (n : Term) (idxs : Array Term)
    (letters : Array Ident) : MacroM Term := do
  let ops ← expandSymbolicString n idxs letters
  `(Quantum.NQubitPauliGroupElement.mk $(quote phase) $ops)

macro_rules
  | `(σ[$n | $[$is ↦ $cs],*]) => expandSymbolicSigma 0 n is cs
  | `(iσ[$n | $[$is ↦ $cs],*]) => expandSymbolicSigma 1 n is cs
  | `(-σ[$n | $[$is ↦ $cs],*]) => expandSymbolicSigma 2 n is cs
  | `(-iσ[$n | $[$is ↦ $cs],*]) => expandSymbolicSigma 3 n is cs
  | `(P[$n | $[$is ↦ $cs],*]) => expandSymbolicString n is cs

/-!
## Delaborator

Displays literal-shaped `NQubitPauliGroupElement.mk` applications back as `σ[…]`, and
literal-shaped `NQubitPauliOperator.set` chains back as `P[…]`; any other `.set` chain over
an `identity n` whose operators are `X`/`Y`/`Z` constructors displays in the symbolic form
`σ[n | i ↦ Z, …]` / `P[n | i ↦ Z, …]`.
-/

section Delaborator

open PrettyPrinter Delaborator SubExpr

/-- Match a literal natural number: a raw `Nat` literal or an `OfNat.ofNat` application
of one (the form numerals elaborate to). -/
def natLitOf? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal k) => some k
  | _ =>
    if e.isAppOfArity ``OfNat.ofNat 3 then
      match e.getArg! 1 with
      | .lit (.natVal k) => some k
      | _ => none
    else none

/-- Match a `PauliOperator` constructor constant, as its letter. -/
def pauliOpChar? (e : Expr) : Option Char :=
  match e with
  | .const c _ =>
    if c == ``Quantum.PauliOperator.X then some 'X'
    else if c == ``Quantum.PauliOperator.Y then some 'Y'
    else if c == ``Quantum.PauliOperator.Z then some 'Z'
    else if c == ``Quantum.PauliOperator.I then some 'I'
    else none
  | _ => none

/-- Match a literal `set`-chain `(NQubitPauliOperator.identity n).set i₀ op₀ …` with
literal indices and constructor operators. Returns the literal `n` together with the
`(index, letter)` assignments, innermost first. Returns `none` on any other shape. -/
partial def setChain? (e : Expr) (acc : List (Nat × Char) := []) :
    Option (Nat × List (Nat × Char)) :=
  if e.isAppOfArity ``Quantum.NQubitPauliOperator.set 4 then do
    let i ← natLitOf? (e.getArg! 2)
    let c ← pauliOpChar? (e.getArg! 3)
    setChain? (e.getArg! 1) ((i, c) :: acc)
  else if e.isAppOfArity ``Quantum.NQubitPauliOperator.identity 1 then do
    let n ← natLitOf? (e.getArg! 0)
    return (n, acc)
  else
    none

/-- The letters identifier of a literal chain over `n > 0` qubits whose indices are all
in range, or `none` otherwise. Later (outer) `.set`s override earlier ones, so the
innermost-first assignment list is folded left to right. -/
def lettersOf? (n : Nat) (sets : List (Nat × Char)) : Option Ident := do
  guard (0 < n)
  guard (sets.all fun ic => ic.1 < n)
  let letters := String.ofList <| (List.range n).map fun j =>
    sets.foldl (fun acc ic => if ic.1 == j then ic.2 else acc) 'I'
  return mkIdent (.mkSimple letters)

/-- The letters identifier of the `set`-chain `e`, if it is in the literal normal form the
letters notation expands to: literal `n > 0`, literal in-range indices in strictly
increasing order, and no explicit `I`. A chain of any other shape (an out-of-order literal
index, a set `I`) is left to the symbolic printer, so that the display always re-parses to
the same term. -/
def literalLetters? (e : Expr) : Option Ident := do
  let (n, sets) ← setChain? e
  guard (sets.all fun ic => ic.2 != 'I')
  let idxs := sets.map (·.1)
  guard ((idxs.zip (idxs.drop 1)).all fun ab => ab.1 < ab.2)
  lettersOf? n sets

/-- Delaborate the symbolic `set`-chain at the current position: a chain
`((NQubitPauliOperator.identity n).set i₀ op₀).set i₁ op₁ …` whose operators are `X`/`Y`/`Z`
constructors, with `n` and the indices arbitrary. Returns the delaborated `n` and the
delaborated indices with their letters, innermost first (the written order of the
notation); each subterm is delaborated at its own position, so hover and
`pp.` options behave as usual. Fails on any other shape, including an explicit `I`. -/
partial def delabSymbolicChain : DelabM (Term × Array Term × Array Ident) := do
  let e ← getExpr
  if e.isAppOfArity ``Quantum.NQubitPauliOperator.set 4 then
    let some c := pauliOpChar? (e.getArg! 3) | failure
    if c == 'I' then failure
    let (n, is, cs) ← withNaryArg 1 delabSymbolicChain
    let i ← withNaryArg 2 delab
    return (n, is.push i, cs.push (mkIdent (.mkSimple (toString c))))
  else if e.isAppOfArity ``Quantum.NQubitPauliOperator.identity 1 then
    let n ← withNaryArg 0 delab
    return (n, #[], #[])
  else
    failure

/-- Delaborate `NQubitPauliGroupElement.mk` applications back to the
`σ[…]`/`iσ[…]`/`-σ[…]`/`-iσ[…]` notation. Fires only when the phase is a literal `0`–`3`
and the operator part is a `set`-chain over `identity n`: a chain in the literal normal
form (see `literalLetters?`) displays in the letters form `σ[XIZ]`, any other chain with
`X`/`Y`/`Z` operators in the symbolic form `σ[n | i ↦ Z, …]`; stays silent otherwise.
Scoped with the notation. -/
@[scoped app_delab Quantum.NQubitPauliGroupElement.mk]
def delabSigma : Delab :=
  whenPPOption getPPNotation <| whenNotPPOption getPPExplicit do
    let e ← getExpr
    unless e.isAppOfArity ``Quantum.NQubitPauliGroupElement.mk 3 do failure
    let some phase := natLitOf? (e.getArg! 1) | failure
    if let some letters := literalLetters? (e.getArg! 2) then
      match phase with
      | 0 => `(σ[$letters])
      | 1 => `(iσ[$letters])
      | 2 => `(-σ[$letters])
      | 3 => `(-iσ[$letters])
      | _ => failure
    else
      let (n, is, cs) ← withNaryArg 2 delabSymbolicChain
      if is.isEmpty then failure
      match phase with
      | 0 => `(σ[$n | $[$is ↦ $cs],*])
      | 1 => `(iσ[$n | $[$is ↦ $cs],*])
      | 2 => `(-σ[$n | $[$is ↦ $cs],*])
      | 3 => `(-iσ[$n | $[$is ↦ $cs],*])
      | _ => failure

/-- Delaborate `NQubitPauliOperator.set` chains back to the `P[…]` notation. Fires only on
a `set` application whose whole chain runs over an `identity n`: a chain in the literal
normal form (see `literalLetters?`) displays as `P[XIZ]`, any other chain with `X`/`Y`/`Z`
operators as `P[n | i ↦ Z, …]`; stays silent otherwise (in particular a bare `identity n`
keeps its name). An over-applied chain — the operator string evaluated at a qubit,
`P[XIZ] i` — is handled by `withOverApp`, so the extra arguments follow the notation.
Scoped with the notation. -/
@[scoped app_delab Quantum.NQubitPauliOperator.set]
def delabPauliString : Delab :=
  whenPPOption getPPNotation <| whenNotPPOption getPPExplicit <| withOverApp 4 do
    let e ← getExpr
    if let some letters := literalLetters? e then
      `(P[$letters])
    else
      let (n, is, cs) ← delabSymbolicChain
      if is.isEmpty then failure
      `(P[$n | $[$is ↦ $cs],*])

end Delaborator

end Pauli

/-!
## Round-trip tests

Each phase prefix elaborates to exactly the hand-written literal normal form, and `P[…]`
to exactly its operator half.
-/

section RoundTrip

open Quantum
open scoped Pauli

example :
    σ[XIZ] =
      ⟨0, ((NQubitPauliOperator.identity 3).set 0 PauliOperator.X).set 2 PauliOperator.Z⟩ :=
  rfl

example :
    σ[XZZXI] =
      ⟨0, ((((NQubitPauliOperator.identity 5).set 0 PauliOperator.X).set 1
        PauliOperator.Z).set 2 PauliOperator.Z).set 3 PauliOperator.X⟩ :=
  rfl

example : σ[IIII] = ⟨0, NQubitPauliOperator.identity 4⟩ := rfl

example : iσ[Z] = ⟨1, (NQubitPauliOperator.identity 1).set 0 PauliOperator.Z⟩ := rfl

example :
    -σ[YY] =
      ⟨2, ((NQubitPauliOperator.identity 2).set 0 PauliOperator.Y).set 1 PauliOperator.Y⟩ :=
  rfl

example : -iσ[XI] = ⟨3, (NQubitPauliOperator.identity 2).set 0 PauliOperator.X⟩ := rfl

example : σ[XIZ].phasePower = 0 := rfl

example : σ[XIZ].operators 2 = PauliOperator.Z := rfl

example : σ[XIZ].operators 1 = PauliOperator.I := rfl

example :
    P[XIZ] = ((NQubitPauliOperator.identity 3).set 0 PauliOperator.X).set 2 PauliOperator.Z :=
  rfl

example : P[III] = NQubitPauliOperator.identity 3 := rfl

example : P[XIZ] 2 = PauliOperator.Z := rfl

example : σ[XIZ].operators = P[XIZ] := rfl

example : (⟨1, P[YY]⟩ : NQubitPauliGroupElement 2) = iσ[YY] := rfl

/-! The symbolic form expands to the same chain with the `.set`s in the written order. -/

example (n : ℕ) (i : Fin (n + 1)) :
    σ[n + 2 | Fin.castSucc i ↦ Z, Fin.succ i ↦ Z] =
      ⟨0, ((NQubitPauliOperator.identity (n + 2)).set (Fin.castSucc i) PauliOperator.Z).set
        (Fin.succ i) PauliOperator.Z⟩ :=
  rfl

example (n : ℕ) (i j : Fin n) :
    σ[n | j ↦ X, i ↦ Y] =
      ⟨0, ((NQubitPauliOperator.identity n).set j PauliOperator.X).set i PauliOperator.Y⟩ :=
  rfl

example (n : ℕ) (i : Fin n) :
    iσ[n | i ↦ Z] = ⟨1, (NQubitPauliOperator.identity n).set i PauliOperator.Z⟩ :=
  rfl

example (n : ℕ) (i : Fin n) :
    -σ[n | i ↦ Z] = ⟨2, (NQubitPauliOperator.identity n).set i PauliOperator.Z⟩ :=
  rfl

example (n : ℕ) (i : Fin n) :
    -iσ[n | i ↦ X] = ⟨3, (NQubitPauliOperator.identity n).set i PauliOperator.X⟩ :=
  rfl

example (n : ℕ) (i j : Fin n) :
    P[n | i ↦ X, j ↦ Z] =
      ((NQubitPauliOperator.identity n).set i PauliOperator.X).set j PauliOperator.Z :=
  rfl

example (n : ℕ) (i j : Fin n) : σ[n | i ↦ X, j ↦ Z].operators = P[n | i ↦ X, j ↦ Z] := rfl

example (i : Fin 3) : P[3 | i ↦ Z] = (NQubitPauliOperator.identity 3).set i PauliOperator.Z :=
  rfl

/-! ### Display

The printers are checked on their output: literal normal forms print in the letters form,
everything else that re-parses prints in the symbolic form, and a chain that would not
re-parse to itself (an explicit `I`) is left to the default printer. -/

open Lean Elab Command in
/-- Display test: elaborate `stx` and check that its pretty-printed text is `expected`
(`exact := false`: contains `expected`). Run through `run_cmd` so no `#`-command is needed. -/
private def checkDisplay (stx : Syntax) (expected : String) (exact : Bool := true) :
    CommandElabM Unit :=
  liftTermElabM do
    let e ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVarsNoPostponing
    let s := toString (← Meta.ppExpr (← instantiateMVars e))
    unless (if exact then s == expected else (s.splitOn expected).length > 1) do
      throwError "display test failed:{indentD s}\nexpected{indentD expected}"

run_cmd do
  checkDisplay (← `(σ[XIZ])) "σ[XIZ]"
run_cmd do
  checkDisplay (← `(-iσ[XI])) "-iσ[XI]"
run_cmd do
  checkDisplay (← `(P[XIZ])) "P[XIZ]"
run_cmd do
  checkDisplay (← `(σ[IIII])) "σ[IIII]"
-- written order that is not the sorted normal form stays symbolic (a different term)
run_cmd do
  checkDisplay (← `(σ[3 | 1 ↦ Z, 0 ↦ X])) "σ[3 | 1 ↦ Z, 0 ↦ X]"
run_cmd do
  checkDisplay (← `(P[3 | 1 ↦ Z, 0 ↦ Z])) "P[3 | 1 ↦ Z, 0 ↦ Z]"
-- sorted written order is the literal normal form
run_cmd do
  checkDisplay (← `(P[3 | 0 ↦ Z, 1 ↦ Z])) "P[ZZI]"
-- an explicit `I` never prints as a letters string that would drop it
run_cmd do
  checkDisplay
    (← `(((NQubitPauliOperator.identity 3).set 0 PauliOperator.X).set 1 PauliOperator.I))
    "P[XII].set 1 PauliOperator.I"
-- symbolic qubit count and indices
run_cmd do
  checkDisplay (← `(fun (n : ℕ) (i j : Fin n) => σ[n | j ↦ X, i ↦ Y]))
    "σ[n | j ↦ X, i ↦ Y]" (exact := false)
run_cmd do
  checkDisplay (← `(fun (n : ℕ) (i : Fin n) => P[n | i ↦ Z] i))
    "P[n | i ↦ Z] i" (exact := false)

end RoundTrip
