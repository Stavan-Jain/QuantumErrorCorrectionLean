import Mathlib.Tactic
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerGroup
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerCode
import QEC.Stabilizer.Framework.Core.Stabilizer.SubgroupLemmas
import QEC.Stabilizer.Framework.Core.CSS.CSSPredicates
import QEC.Stabilizer.Framework.Core.CSS.CSSNoNegI
import QEC.Stabilizer.Framework.Core.CSS.CSSCommutationLemmas
import QEC.Stabilizer.Framework.Core.Stabilizer.Centralizer
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance
import QEC.Stabilizer.Framework.Core.Logical.LogicalOperators
import QEC.Stabilizer.Foundations.PauliGroup.Commutation
import QEC.Stabilizer.Foundations.PauliGroup.CommutationTactics
import QEC.Stabilizer.Foundations.PauliGroup.NQubitOperator
import QEC.Stabilizer.Foundations.PauliGroup.NQubitElement
import QEC.Stabilizer.Foundations.PauliGroup.Notation
import QEC.Stabilizer.Foundations.BinarySymplectic.Core
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrix
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrixDecidable
import QEC.Stabilizer.Framework.Symplectic.IndependentEquiv

/-!
# Template — standard CSS stabilizer-code formalization

This file documents **the canonical structure** for formalizing a CSS stabilizer
code in this repo. It is *not* a working code — the actual content is in the
embedded code samples below. Copy this file, rename it to `<CodeName>.lean`,
fill in the parameters / Pauli strings, and adapt section by section.

The pattern was first established in `Steane7.lean`; this file is the explicit,
copy-paste-ready version. The skeleton-drafter agent
(`.claude/agents/qec-skeleton-drafter.md`) uses this file as its primary
structural reference.

## When to use this template

Use as-is for **CSS codes with `k = 1` logical qubit** (the most common case):
Steane7, Shor9, RepetitionCode3, RepetitionCodeN. The structure scales
straightforwardly to:

- **`k ≥ 2`** — see variant notes under §10 (StabilizerCode packaging) and §11
  (logical operators). The only field that genuinely changes is
  `logical_commute_cross` — for `k = 1` the `Subsingleton.elim` shortcut
  suffices; for `k ≥ 2` you need explicit case-splits on `Fin k × Fin k`.
- **Parametric families** (toric, rotated surface, …) — generators are defined
  as functions of `L` (the toric, repetition and iceberg families write theirs
  with the symbolic `σ[n | i ↦ Z, …]` form, see §1; the rotated surface code
  builds them through the homological-code layer instead), the subgroup is
  parametric, and the `StabilizerCode` packaging often requires a *trimmed*
  generator list (see `ToricCodeNStabilizerCode.lean` for the pattern). The
  distance proof typically lives in a *separate file* (`<Code>Distance.lean`).
- **Non-CSS codes** (Pauli-mixed generators) — see variant notes under §3
  (typing) and §4 (cross-commutation). The CSS shortcuts (`IsXTypeElement`,
  `IsZTypeElement`, `CSS.negIdentity_not_mem_closure_union`) don't apply; use
  the general centralizer machinery instead.

## Section overview

| § | Content | Required? |
|---|---|---|
| §1 | Generator definitions (`Z1`, `Z2`, …, `X1`, `X2`, …) | always |
| §2 | Generator sets (`ZGenerators`, `XGenerators`, `generators`) and subgroup | always |
| §3 | Z/X type predicates (`ZGenerators_are_ZType`, `XGenerators_are_XType`) | CSS only |
| §4 | Cross-commutation (`ZGenerators_commute_XGenerators`) | always |
| §5 | All-pair commutation (`generators_commute`) | always |
| §6 | `negIdentity ∉ subgroup` | always |
| §7 | Generator list + `listToSet` equality | always |
| §8 | Bundled `StabilizerGroup n` | always |
| §9 | Phase-zero + generator independence | always |
| §10 | Logical operators (`logicalX`, `logicalZ`, optional `logicalY`) | when `k ≥ 1` |
| §11 | Logical anticommutation | when `k ≥ 1` |
| §12 | Logicals in centralizer | when `k ≥ 1` |
| §13 | `StabilizerCode n k` packaging | always |
| §14 | `HasCodeDistance` | optional (often in a sibling file for parametric codes) |

## File header pattern

Open with a doc-section citing the original paper and stating the generators /
logical operators / distance claim explicitly. The informal_spec.md produced by
the skeleton drafter should populate this verbatim.
-/

namespace Quantum
namespace StabilizerGroup
namespace _Template

open NQubitPauliGroupElement
open scoped Pauli

/-!
## §1 — Generators

For an `[[n, k, d]]` CSS code, you need `m_Z` Z-type generators and `m_X` X-type
generators, with `m_Z + m_X = n - k`. Each is an `NQubitPauliGroupElement n`
with `phasePower = 0`, written with the scoped `σ[…]` construction notation
(`open scoped Pauli`, provided by
`QEC.Stabilizer.Foundations.PauliGroup.Notation` — see this file's header).

Pattern (Steane code, [[7, 1, 3]], `m_Z = m_X = 3`):

```lean
/-- Z-check on row r₁ = {0,1,2,4}: Z on qubits 0,1,2,4 and I elsewhere. -/
def Z1 : NQubitPauliGroupElement 7 := σ[ZZZIZII]
```

`σ[ZZZIZII]` elaborates to **exactly** the literal normal form

```lean
⟨0,
  (((NQubitPauliOperator.identity 7).set 0 PauliOperator.Z).set 1 PauliOperator.Z).set 2
    PauliOperator.Z |>.set 4 PauliOperator.Z⟩
```

(`.set` applied at the non-identity positions in increasing index order), so
`rfl`/`decide`/`simp` behavior is identical to writing the chain by hand, and
goals display such literals back as `σ[…]`.

Conventions:

- `phasePower = 0` always for stabilizer generators — the plain `σ[…]` form.
  (Phase-prefix variants exist for other elements: `iσ[…]` = phase `i`,
  `-σ[…]` = phase `-1`, `-iσ[…]` = phase `-i`.)
- 0-based qubit indexing: the k-th letter is the operator on qubit k.
- One `def` per generator. Name them `Z1, Z2, …, X1, X2, …`.
- The bare Pauli string with no phase (an `NQubitPauliOperator n`) is `P[…]`:
  `σ[ZZZIZII].operators = P[ZZZIZII]` by `rfl`, and `P[…]` elaborates to exactly
  the bare `.set` chain. Reach for it in `operators`-level statements (support,
  check-matrix rows) rather than spelling the chain out.

**Non-CSS variant.** Mixed-Pauli generators use the same notation (e.g., the
5-qubit perfect code's `σ[XZZXI]`); there is no Z/X partition.

**Parametric variant.** When the qubit count and the positions are terms
rather than numerals, use the symbolic form with the same leading tokens:

```lean
/-- The adjacent Z-check `Z_i Z_{i+1}` on `n + 2` qubits. -/
def ZPair (n : ℕ) (i : Fin (n + 1)) : NQubitPauliGroupElement (n + 2) :=
  σ[n + 2 | Fin.castSucc i ↦ Z, Fin.succ i ↦ Z]
```

`σ[n | i ↦ Z, j ↦ Z]` elaborates to exactly
`⟨0, ((NQubitPauliOperator.identity n).set i PauliOperator.Z).set j PauliOperator.Z⟩`,
the `.set`s in the written order, so the usual
`simp [NQubitPauliOperator.set, NQubitPauliOperator.identity]` unfolding is
unchanged; `P[n | …]` is the phase-less string, and the phase prefixes work the
same way. Letters are `X`, `Y`, `Z` only — leave identity qubits out. See
`Repetition/N.lean`, `Iceberg/N.lean`, and `Toric/CodeN.lean` (`vertexStab`,
`faceStab`) for uses.
-/

/-!
## §2 — Generator sets and subgroup

Bundle the generators into `Set`s plus their union, then take the
`Subgroup.closure`. The subgroup must be `noncomputable` because mathlib's
`Group` instance on `NQubitPauliGroupElement` is noncomputable as of v4.30 (see
CLAUDE.md).

Pattern:

```lean
def ZGenerators : Set (NQubitPauliGroupElement 7) := {Z1, Z2, Z3}
def XGenerators : Set (NQubitPauliGroupElement 7) := {X1, X2, X3}
def generators : Set (NQubitPauliGroupElement 7) := ZGenerators ∪ XGenerators

noncomputable def subgroup : Subgroup (NQubitPauliGroupElement 7) :=
  Subgroup.closure generators
```

**Non-CSS variant.** Skip `ZGenerators`/`XGenerators`; just define
`generators : Set (NQubitPauliGroupElement n)` directly as the set of all
mixed-Pauli generators, and `subgroup := Subgroup.closure generators`.
-/

/-!
## §3 — Z-type and X-type predicates (CSS only)

Prove that every Z-generator is Z-type (operator is `I` or `Z` on every qubit)
and similarly for X. These predicates feed into the CSS commutation shortcuts of
§4–6.

Pattern (the trivial direction — case-split on the singleton/finite set):

```lean
lemma ZGenerators_are_ZType :
    ∀ g, g ∈ ZGenerators → NQubitPauliGroupElement.IsZTypeElement g := by
  intro g hg
  rcases hg with rfl | rfl | rfl
  all_goals
    constructor
    · rfl  -- phase = 0
    · intro i; fin_cases i <;>
        simp [Z1, Z2, Z3, NQubitPauliOperator.set, NQubitPauliOperator.identity,
              PauliOperator.IsZType]
```

Helpful imports: `Core/CSSPredicates.lean` defines `IsZTypeElement`,
`IsXTypeElement`, plus the per-qubit `PauliOperator.IsZType` /
`PauliOperator.IsXType`.

**Non-CSS variant.** Skip this section entirely. The general centralizer
machinery in §6 / §12 works directly without typing predicates.
-/

/-!
## §4 — Cross-commutation (CSS: Z-generators commute with X-generators)

For each `(z, x) ∈ ZGenerators × XGenerators`, prove `z * x = x * z`. The shape
of the proof is:

```lean
private lemma Z1_comm_X1 : Z1 * X1 = X1 * Z1 := by
  classical
  pauli_comm_even_anticommutes
  -- residual goal: even number of anticommuting qubits between Z1 and X1
  have hfilter :
      (Finset.univ.filter
        (NQubitPauliGroupElement.anticommutesAt Z1.operators X1.operators)) =
      (<the explicit Finset>) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, Z1, X1,
            NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide
```

Then bundle into a `∀`-statement:

```lean
lemma ZGenerators_commute_XGenerators :
    ∀ z ∈ ZGenerators, ∀ x ∈ XGenerators, z * x = x * z := by
  intro z hz x hx
  rcases hz with rfl | rfl | rfl <;> rcases hx with rfl | rfl | rfl <;>
    first
      | exact Z1_comm_X1
      | exact Z2_comm_X1
      | exact Z3_comm_X1
      | …
```

The `pauli_comm_even_anticommutes` tactic is in
`PauliGroup/CommutationTactics.lean`; it converts the commutation goal into a
parity-of-anticommuting-qubits goal, which is then closed by computing the
explicit `Finset` and `decide`-ing its cardinality is even.

**Performance note.** For small `n` (≤ 9 with few generators), the whole batch
may close as a single `by decide` on the symplectic check-matrix product without
spelling out the per-pair filter Finsets. Try that first. For larger codes, the
explicit-Finset approach is cleaner and reliably fast.

**Non-CSS variant.** Without Z/X partition, prove pairwise commutation for
*every* pair of generators (`m * (m-1)/2` cases for `m` generators); fall back
to the same `pauli_comm_even_anticommutes` machinery.
-/

/-!
## §5 — All-pair commutation (full stabilizer abelianness)

Combine §3 and §4 via the CSS shortcuts in `Core/CSSCommutationLemmas.lean`:

```lean
theorem generators_commute :
    ∀ g h, g ∈ generators → h ∈ generators → g * h = h * g := by
  intro g h hg hh
  rcases hg with hgZ | hgX <;> rcases hh with hhZ | hhX
  · exact ZType_commutes (ZGenerators_are_ZType g hgZ) (ZGenerators_are_ZType h hhZ)
  · exact ZGenerators_commute_XGenerators _ hgZ _ hhX
  · exact (ZGenerators_commute_XGenerators _ hhZ _ hgX).symm
  · exact XType_commutes (XGenerators_are_XType g hgX) (XGenerators_are_XType h hhX)
```

`ZType_commutes` and `XType_commutes` are the CSS-side trivial commutations: two
Z-type elements always commute (both contain only `I`s and `Z`s, which commute
pairwise), same for X-type.

**Non-CSS variant.** No CSS shortcuts; you proved pairwise commutation directly
in §4, so `generators_commute` is just `rcases` + lookup.
-/

/-!
## §6 — `−I` is not in the stabilizer subgroup

For CSS codes, the lemma `CSS.negIdentity_not_mem_closure_union` in
`Core/CSSNoNegI.lean` handles this once you have the Z/X partition and their
cross-commutation:

```lean
theorem negIdentity_not_mem :
    negIdentity n ∉ subgroup := by
  have hZX : ∀ z ∈ ZGenerators, ∀ x ∈ XGenerators, z * x = x * z :=
    ZGenerators_commute_XGenerators
  simpa [subgroup, generators] using
    (CSS.negIdentity_not_mem_closure_union (n := n) ZGenerators XGenerators
      ZGenerators_are_ZType XGenerators_are_XType hZX)
```

This is a one-line proof reusing §3, §4. Don't reprove it.

**Non-CSS variant.** Use the general lemma in `Core/SubgroupLemmas.lean`:
`negIdentity_not_mem_of_independent_phase_zero` — requires the generator list to
be phase-0 and have linearly-independent symplectic rows (§9).
-/

/-!
## §7 — Generator list and `listToSet` equality

A `List` form is needed for symplectic-span / bundled-StabilizerGroup arguments.
Define the list in a canonical order (Z-generators first, then X-generators,
matching the `generators` set's union order):

```lean
def generatorsList : List (NQubitPauliGroupElement 7) :=
  [Z1, Z2, Z3, X1, X2, X3]

lemma listToSet_generatorsList :
    NQubitPauliGroupElement.listToSet generatorsList = generators := by
  simp only [generatorsList, generators, ZGenerators, XGenerators,
    NQubitPauliGroupElement.listToSet_cons, NQubitPauliGroupElement.listToSet_nil]
  ext g
  simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff,
             Set.mem_empty_iff_false, or_false, or_assoc]
```

Length must equal `n - k`; this is enforced by
`StabilizerCode.generators_length` (§13).

**Parametric variant.** For toric / rotated-surface codes with parametric `L`,
the natural full generator list (e.g., all `2L²` vertex + face stabilizers of
the toric code) is *redundant* — i.e. its length exceeds `n - k`. In that case,
define a separate *trimmed* list `generatorsListPackaged` with length exactly
`n - k`, drop the redundant generators, and prove the closures are equal. See
`ToricCodeNStabilizerCode.lean` for the canonical pattern. The trimmed list goes
into `StabilizerCode.generatorsList`; the original full list stays in the bare
`StabilizerGroup` definition.
-/

/-!
## §9 — Phase-zero + generator independence

These two facts feed `StabilizerCode.generators_phaseZero` and
`StabilizerCode.generators_independent` in §13.

```lean
lemma AllPhaseZero_generatorsList :
    NQubitPauliGroupElement.AllPhaseZero generatorsList := by
  rw [generatorsList, NQubitPauliGroupElement.AllPhaseZero_cons]
  -- chain of `AllPhaseZero_cons.mpr ⟨rfl, ...⟩` per element
  exact ⟨rfl, (NQubitPauliGroupElement.AllPhaseZero_cons _ _).mpr
    ⟨rfl, …⟩⟩

theorem rowsLinearIndependent_generatorsList :
    NQubitPauliGroupElement.rowsLinearIndependent generatorsList := by decide

theorem GeneratorsIndependent_n_generatorsList :
    GeneratorsIndependent n generatorsList :=
  GeneratorsIndependent_of_rowsLinearIndependent n generatorsList
    rowsLinearIndependent_generatorsList
```

`decide` closes this for every small code on `main` (`n ≤ 9` or so); reach for
`decide +kernel` before anything heavier, never `native_decide` (banned, see
CLAUDE.md § "Axiom policy"). For parametric codes with `L ≥ 2`, replace `decide`
with a parametric independence proof — see
`rowsLinearIndependent_generatorsListPackaged` in `Toric/StabilizerCode.lean`.
-/

/-!
## §8 — Bundled `StabilizerGroup n`

Define the canonical `StabilizerGroup n` from `generatorsList` using the smart
constructor `mkStabilizerFromGenerators` (in `Core/StabilizerGroup.lean`):

```lean
noncomputable def stabilizerGroup : StabilizerGroup n :=
  mkStabilizerFromGenerators n generatorsList
    (by rw [listToSet_generatorsList]; exact generators_commute)
    (by rw [listToSet_generatorsList]; exact negIdentity_not_mem)

lemma stabilizerGroup_toSubgroup_eq : stabilizerGroup.toSubgroup = subgroup := by
  simp only [stabilizerGroup, mkStabilizerFromGenerators, subgroup]
  rw [listToSet_generatorsList]
```

This bridges the `List`-based packaging (used by `StabilizerCode`) with the
`Set`-based subgroup (used by `IsNontrivialLogicalOperator` and centralizer
arguments). The equality lemma `stabilizerGroup_toSubgroup_eq` is consumed by
downstream proofs that need to translate between the two forms — see
`IsNontrivialLogicalOperator_of_toSubgroup_eq` in `Core/StabilizerCode.lean`.
-/

/-!
## §10 — Logical operators

For an `[[n, k, d]]` code, define `k` `logicalX_i` and `k` `logicalZ_i`. For
`k = 1`, names are simply `logicalX` / `logicalZ`. For `k ≥ 2`, index them
explicitly (`logicalX_1`, `logicalX_2`, …, `logicalZ_1`, `logicalZ_2`, …).

```lean
/-- Logical X: X on all qubits (Steane, Shor; for surface codes the support
is a non-contractible loop instead). -/
def logicalX : NQubitPauliGroupElement n :=
  ⟨0, NQubitPauliOperator.X n⟩

def logicalZ : NQubitPauliGroupElement n :=
  ⟨0, NQubitPauliOperator.Z n⟩
```

`NQubitPauliOperator.X n` and `.Z n` are the "all-X" / "all-Z" operators —
convenient when the logical operator has the full-support form. For other
support patterns, use the `.set` chain pattern from §1.

**Logical Y.** Optional, with the canonical phase convention `Ȳ = i X̄ Z̄`:

```lean
noncomputable def logicalY : NQubitPauliGroupElement n :=
  NQubitPauliGroupElement.phaseI n * (logicalX * logicalZ)

lemma logicalY_eq_phase2_allY :
    logicalY = ({ phasePower := (2 : Fin 4), operators := NQubitPauliOperator.Y n } :
      NQubitPauliGroupElement n) := by
  ext
  · decide
  · simp [logicalY, logicalX, logicalZ, NQubitPauliGroupElement.mul,
          NQubitPauliGroupElement.mulOp, NQubitPauliOperator.X, NQubitPauliOperator.Z,
          NQubitPauliOperator.Y, NQubitPauliOperator.identity, PauliOperator.mulOp]
```

**`k ≥ 2` variant.** Define `logicalX_i`, `logicalZ_i` per logical-qubit
index. The (anti)commutation pattern in §11 expands to *pairwise* relations
(see §11 variant note).
-/

/-!
## §11 — Logical anticommutation

For `k = 1`, prove that `logicalX` anticommutes with `logicalZ`. When both are
all-X / all-Z, the dedicated lemma `NQubitPauliOperator.allX_allZ_anticommute`
closes this in one line:

```lean
theorem logicalX_anticommutes_logicalZ :
    NQubitPauliGroupElement.Anticommute logicalX logicalZ :=
  NQubitPauliOperator.allX_allZ_anticommute n (by decide)
```

The `(by decide)` discharges `Odd n` (anticommutation requires odd `n` for the
all-X/all-Z pair to anticommute — true for Steane7 (n=7), false for [[4,2,2]]
(n=4)).

**Non-all-X variant.** For partial-support logicals, use
`pauli_comm_even_anticommutes` like in §4 and compute the anticommute filter
explicitly.

**`k ≥ 2` variant.** You need *four* relations per logical qubit *pair*:

```lean
-- For each (i, j) ∈ Fin k × Fin k:
theorem logicalX_anticommutes_logicalZ_diag (i : Fin k) :
    NQubitPauliGroupElement.Anticommute (logicalX i) (logicalZ i)

theorem logicalX_commutes_logicalZ_offdiag (i j : Fin k) (h : i ≠ j) :
    (logicalX i) * (logicalZ j) = (logicalZ j) * (logicalX i)

theorem logicalX_commutes_logicalX (i j : Fin k) :
    (logicalX i) * (logicalX j) = (logicalX j) * (logicalX i)

theorem logicalZ_commutes_logicalZ (i j : Fin k) :
    (logicalZ i) * (logicalZ j) = (logicalZ j) * (logicalZ i)
```

These feed `StabilizerCode.logical_commute_cross` (see §13).
-/

/-!
## §12 — Logicals in centralizer

Show that each `logicalX_i` and `logicalZ_i` commutes with every
stabilizer-group element. The standard pattern is `Subgroup.closure_induction`
with cases `| mem | one | mul | inv` (note v4.30 naming):

```lean
theorem logicalX_mem_centralizer :
    logicalX ∈ centralizer stabilizerGroup := by
  rw [centralizer, Subgroup.mem_centralizer_iff]
  rw [stabilizerGroup_toSubgroup_eq]
  intro s hs
  refine Subgroup.closure_induction
    (p := fun y _ => y * logicalX = logicalX * y) ?_ ?_ ?_ ?_ hs
  case mem =>
    -- show logicalX commutes with each generator
    intro y hy
    simp [generators] at hy
    rcases hy with hgZ | hgX
    · rcases (by simpa [ZGenerators] using hgZ) with rfl | rfl | rfl
      · exact logicalX_commutes_Z1.symm
      · exact logicalX_commutes_Z2.symm
      · …
    · …
  case one =>
    change (1 : NQubitPauliGroupElement n) * logicalX = logicalX * 1
    rw [_root_.one_mul, _root_.mul_one]
  case mul =>
    intros y₁ y₂ _ _ hy₁ hy₂
    calc (y₁ * y₂) * logicalX
        = y₁ * (y₂ * logicalX)         := _root_.mul_assoc _ _ _
      _ = y₁ * (logicalX * y₂)         := by rw [hy₂]
      _ = (y₁ * logicalX) * y₂         := (_root_.mul_assoc _ _ _).symm
      _ = (logicalX * y₁) * y₂         := by rw [hy₁]
      _ = logicalX * (y₁ * y₂)         := _root_.mul_assoc _ _ _
  case inv =>
    intros y _ hy
    exact (show Commute y logicalX from hy).inv_left.eq
```

**Three things that recurrently go wrong here** (per CLAUDE.md):

1. **`one` case fails with `rw [one_mul]`.** The goal is `(fun y _ => …) 1 ⋯`,
   unreduced. Insert `change (1 : ...) * logicalX = logicalX * 1` before `rw` to
   beta-reduce.
2. **Ambiguous `mul_assoc`.** When `open NQubitPauliGroupElement` is in scope,
   both `_root_.mul_assoc` and `NQubitPauliGroupElement.mul_assoc` resolve.
   Qualify with `_root_.mul_assoc` (same for `one_mul`, `mul_one`).
3. **Per-generator commutation lemmas (e.g. `logicalX_commutes_Z1`) need to be
   separate `private lemma`s** before this theorem — define them with the same
   `pauli_comm_even_anticommutes` + filter pattern from §4.
-/

/-!
## §13 — `StabilizerCode n k` packaging

The bundled structure. Combine §7–§12:

```lean
private def logicalOps_<CodeName> : Fin k → LogicalQubitOps n stabilizerGroup :=
  fun _ => ⟨logicalX, logicalZ, logicalX_mem_centralizer, logicalZ_mem_centralizer,
            logicalX_anticommutes_logicalZ⟩

noncomputable def stabilizerCode : StabilizerCode n k where
  hk := by decide                          -- 0 < k ≤ n; trivial for fixed values
  generatorsList := generatorsList
  generators_length := rfl                 -- length = n - k by construction
  generators_phaseZero := AllPhaseZero_generatorsList
  generators_independent := GeneratorsIndependent_n_generatorsList
  generators_commute := by
    rw [listToSet_generatorsList]; exact generators_commute
  closure_no_neg_identity := by
    rw [listToSet_generatorsList]; exact negIdentity_not_mem
  logicalOps := logicalOps_<CodeName>
  logical_commute_cross := fun ℓ ℓ' h => (h (Subsingleton.elim ℓ ℓ')).elim
```

The `logical_commute_cross` shortcut `(h (Subsingleton.elim ℓ ℓ')).elim`
discharges the field vacuously when `k = 1` (only one possible index, so the
hypothesis `ℓ ≠ ℓ'` is automatically false).

**`k ≥ 2` variant.** The `Subsingleton.elim` trick **does not apply**. Spell out
the cross-commutation by case-split on `Fin k × Fin k`:

```lean
private def logicalOps_<CodeName> : Fin k → LogicalQubitOps n stabilizerGroup
  | 0 => ⟨logicalX_1, logicalZ_1, logicalX_1_mem_centralizer,
           logicalZ_1_mem_centralizer, logicalX_1_anticommutes_logicalZ_1⟩
  | 1 => ⟨logicalX_2, logicalZ_2, logicalX_2_mem_centralizer,
           logicalZ_2_mem_centralizer, logicalX_2_anticommutes_logicalZ_2⟩
  -- ... one per logical qubit

noncomputable def stabilizerCode : StabilizerCode n k where
  -- (fields as above)
  logical_commute_cross := fun ℓ ℓ' h => by
    fin_cases ℓ <;> fin_cases ℓ' <;> first
      | exact absurd rfl h
      | exact ⟨logicalX_commutes_logicalX_offdiag _ _,
                logicalX_commutes_logicalZ_offdiag _ _,
                logicalZ_commutes_logicalX_offdiag _ _,
                logicalZ_commutes_logicalZ_offdiag _ _⟩
```

The bundled `∧` of four equalities is the off-diagonal commutation requirement.
See `gap_audit.md` template in `.claude/agents/qec-skeleton-drafter.md` for a
discussion of why a smart constructor `LogicalQubitOps.cross_commute_pair` could
clean this up.
-/

/-!
## §14 — `HasCodeDistance` (optional)

Every distance proof on `main` is kernel-only. `native_decide` is banned
repo-wide (CLAUDE.md § "Axiom policy"), so there is no "decide the whole
`HasCodeDistance` predicate" shortcut, and no `sorry` placeholder either: pick
the closer that matches the code's shape. The two CSS closers live in
`Framework/Core/CSS/CSSDistance.lean`, the general one in
`Framework/Core/Logical/CodeDistance.lean`. All three consume the same two
ingredients — the §13 closure equation

```lean
lemma stabilizerCode_toSubgroup_eq :
    stabilizerCode.toStabilizerGroup.toSubgroup = Subgroup.closure generators :=
  stabilizerGroup_toSubgroup_eq  -- §8, up to unfolding
```

and an explicit witness `⟨g, h_nontrivial, by decide⟩`, a nontrivial logical of
weight exactly `d` — and every finite side condition closes with `decide`
(`Decidable (Anticommute p q)` is a global instance, see
`PauliGroup/Commutation.lean`).

**Distance 2, CSS** — `hasCodeDistance_two_of_anticommute_witness`. Supply a
witness function: for every qubit `i` and non-identity Pauli `P`, a generator
anticommuting with `weightOneAt i P`. `fin_cases` on `i`, `match` on `P`, and
let `first` backtrack over the generators of the right type (`Z`-generators
detect `X`/`Y`, `X`-generators detect `Z`). See `Codes/Small/CSS_4_1_2.lean`
and `FourQubit_4_2_2.lean`.

```lean
private lemma weight_one_anticomm_witness :
    ∀ i : Fin n, ∀ P : PauliOperator, P ≠ PauliOperator.I →
      ∃ g ∈ generators, NQubitPauliGroupElement.Anticommute
        (weightOneAt i P) g := by
  intro i P hP
  fin_cases i <;>
    (match P, hP with
    | PauliOperator.X, _ => first
      | exact ⟨Z1, by simp [generators, ZGenerators], by decide⟩
      | exact ⟨Z2, by simp [generators, ZGenerators], by decide⟩
    | PauliOperator.Y, _ => first
      | exact ⟨Z1, by simp [generators, ZGenerators], by decide⟩
      | exact ⟨Z2, by simp [generators, ZGenerators], by decide⟩
    | PauliOperator.Z, _ => first
      | exact ⟨X1, by simp [generators, XGenerators], by decide⟩
      | exact ⟨X2, by simp [generators, XGenerators], by decide⟩
    | PauliOperator.I, hP => exact (hP rfl).elim)

theorem code_has_distance_two : HasCodeDistance stabilizerCode 2 :=
  hasCodeDistance_two_of_anticommute_witness stabilizerCode generators
    stabilizerCode_toSubgroup_eq weight_one_anticomm_witness
    ⟨logicalX, (logicalOps_<CodeName> 0).xOp_nontrivial, by decide⟩
```

**Distance 3, CSS** — `hasCodeDistance_three_of_columns`. Present each check
as the `Finset` of qubits it acts on (`zOn S` / `xOn S` are `Z` / `X` on `S`);
the closer then needs only the classical column conditions on both check
matrices — no column is zero, no two columns coincide — each a closed
statement over `Fin n` that `decide` settles. See
`Codes/Small/Steane7Distance.lean` (self-dual, so one `row` serves both sides).

```lean
def zRow : Fin 3 → Finset (Fin 7) := ![{0, 1, 2, 4}, {0, 1, 3, 5}, {0, 2, 3, 6}]

lemma Z1_eq_zOn : Z1 = zOn {0, 1, 2, 4} :=
  NQubitPauliGroupElement.ext _ _ rfl (funext fun i => by fin_cases i <;> rfl)

lemma zOn_row_mem (r : Fin 3) : zOn (zRow r) ∈ generators := by
  fin_cases r <;> simp [zRow, generators, ZGenerators, Z1_eq_zOn, Z2_eq_zOn, Z3_eq_zOn]

lemma zRow_cover : ∀ i : Fin 7, ∃ r, i ∈ zRow r := by decide

lemma zRow_separate : ∀ i j : Fin 7, i ≠ j → ∃ r, (i ∈ zRow r ↔ j ∉ zRow r) := by
  decide
-- … and the same for `xRow` / `xOn_row_mem` / `xRow_cover` / `xRow_separate`.

theorem code_has_distance_three : HasCodeDistance stabilizerCode 3 :=
  hasCodeDistance_three_of_columns zRow xRow generators stabilizerCode
    stabilizerCode_toSubgroup_eq zOn_row_mem xOn_row_mem zRow_cover xRow_cover
    zRow_separate xRow_separate ⟨logicalXw3, logicalXw3_isNontrivial, logicalXw3_weight⟩
```

The weight-3 witness is usually a stabilizer multiple of `logicalX` (`X̄ · X₁`
for Steane); its weight is `by decide`, and its nontriviality comes from
`isNontrivialLogicalOperator_of_anticommute_centralizer`
(`Core/Logical/LogicalOperators.lean`): it lies in the centralizer and
anticommutes with the centralizer element `Z̄`.

**General case** (non-CSS, or no closer fits) — `hasCodeDistance_of`. It asks
for `d ≥ 1`, the weight-`d` witness, and, for every `1 ≤ w < d`, that no
weight-`w` element is a nontrivial logical. `interval_cases w` splits the last
goal, and each weight is ruled out with an *anti-witness table* fed to
`no_weight_one_mem_centralizer_of_anticommute_witness` /
`no_weight_two_mem_centralizer_of_anticommute_witness` (they live in
`CSSDistance.lean` but assume nothing CSS — any generating set works, which is
how the non-CSS `[[5,1,3]]` uses them). The weight-2 table is the weight-1 one
nested: `match` on `(P, Q)`, then `fin_cases i <;> fin_cases j`, with `first`
backtracking over `exact absurd rfl hij` (the diagonal) and the generators. See
`Codes/Small/FiveQubit_5_1_3.lean` and qec-lab's `docs/lean-patterns.md`
§ non-CSS distance.

```lean
theorem code_has_distance_three : HasCodeDistance stabilizerCode 3 := by
  refine hasCodeDistance_of stabilizerCode 3 (by decide)
    ⟨logicalX_w3, logicalX_w3_isNontrivial, by decide⟩ ?_
  intro w hw_pos hw_lt g hg_weight h_nontrivial
  rcases (IsNontrivialLogicalOperator_iff g stabilizerCode.toStabilizerGroup).mp h_nontrivial
    with ⟨h_cent, _, _⟩
  interval_cases w
  · exact no_weight_one_mem_centralizer_of_anticommute_witness
      stabilizerCode.toStabilizerGroup generators stabilizerCode_toSubgroup_eq
      weight_one_anticomm_witness g hg_weight h_cent
  · exact no_weight_two_mem_centralizer_of_anticommute_witness
      stabilizerCode.toStabilizerGroup generators stabilizerCode_toSubgroup_eq
      weight_two_anticomm_witness g hg_weight h_cent
```

Whichever route, finish by bundling the code with its distance
(`Code[[n, k, d]]` is the scoped notation for `StabilizerCodeWithDistance n k d`
from `Framework/Core/CodeNotation.lean`):

```lean
noncomputable def stabilizerCodeWithDistance : Code[[n, k, d]] where
  toStabilizerCode := stabilizerCode
  hasDistance := code_has_distance_three
```

For **parametric families**, the distance proof typically lives in a *separate
file* (`<Code>Distance.lean`, `<Code>DistanceX.lean`, `<Code>DistanceZ.lean`).
Patterns:

- The X-side and Z-side bounds are proved separately (CSS structure).
- For surface-style codes, the homological framework in
  `Framework/Homological/Distance.lean` provides the abstract bridge — see
  `RotatedSurface/Distance.lean` and `Toric/Distance.lean`.
- A subgroup-equality bridge between `stabilizerGroup` and
  `stabilizerCode.toStabilizerGroup` is usually needed; package it as
  `<CodeName>StabilizerCode_subgroup_eq_homological`.
-/

/-!
## End-of-file checklist

Before declaring a CSS-code formalization complete, verify:

- [ ] `lake build QEC.Stabilizer.Codes.<CodeName>` succeeds (no errors, no
  `sorry` warnings).
- [ ] No `set_option linter.* false` in the file (project-wide policy).
- [ ] All sections from §1 through §13 are present (§14 may be in a separate
  distance file).
- [ ] `stabilizerCode_toSubgroup_eq_subgroup` lemma exposed if downstream proofs
  need to translate between the two forms.
- [ ] Module imported in `QEC/Stabilizer/Codes.lean` umbrella (otherwise
  orphan-module trap — see CLAUDE.md).
- [ ] Doc-comment header references the original paper.
- [ ] Logical-operator (anti)commutation pattern matches the codeword basis from
  the original paper (Stage-3 review point).

## See also

- `Steane7.lean` — canonical k = 1 CSS instantiation of this template
- `Shor9.lean` — alternative k = 1 reference
- `RepetitionCode3.lean`, `RepetitionCodeN.lean` — degenerate small-distance
  cases (d = 1)
- `RotatedSurfaceCodeN*.lean` — parametric L family
- `ToricCodeN*.lean` — parametric family with trimmed-generator packaging
- `.claude/agents/qec-skeleton-drafter.md` — Stage-2 agent that uses this
  template to draft new code skeletons
- CLAUDE.md — project-wide naming, tactics, linter conventions
-/

end _Template
end StabilizerGroup
end Quantum
