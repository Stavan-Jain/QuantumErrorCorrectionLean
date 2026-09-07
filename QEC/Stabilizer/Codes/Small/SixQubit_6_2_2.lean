import Mathlib.Tactic
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerGroup
import QEC.Stabilizer.Framework.Core.Stabilizer.SubgroupLemmas
import QEC.Stabilizer.Framework.Core.CSS.CSSPredicates
import QEC.Stabilizer.Framework.Core.CSS.CSSNoNegI
import QEC.Stabilizer.Framework.Core.Stabilizer.Centralizer
import QEC.Stabilizer.Framework.Core.CSS.CSSCommutationLemmas
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance
import QEC.Stabilizer.Framework.Core.CSS.CSSDistance
import QEC.Stabilizer.Framework.Core.Logical.LogicalOperators
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerCode
import QEC.Stabilizer.Foundations.PauliGroup.Commutation
import QEC.Stabilizer.Foundations.PauliGroup.CommutationTactics
import QEC.Stabilizer.Foundations.PauliGroup.NQubitOperator
import QEC.Stabilizer.Foundations.PauliGroup.NQubitElement
import QEC.Stabilizer.Foundations.BinarySymplectic.Core
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrix
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrixDecidable
import QEC.Stabilizer.Framework.Symplectic.IndependentEquiv

namespace Quantum
open scoped BigOperators
open scoped Pauli

namespace StabilizerGroup
namespace SixQubit_6_2_2

/-!
# The [[6, 2, 2]] `C_6` code (Knill 2004)

A six-qubit normal self-dual CSS stabilizer code encoding **two logical qubits**
with code distance 2. Originally introduced in [E. Knill, *Quantum computing
with realistically noisy devices*, Nature 434, 39 (2005);
`arxiv:quant-ph/0410199`], where it serves as the outer code in Knill's C_4/C_6
fault-tolerant architecture (with `[[4,2,2]]` at the inner level).

## Stabilizer tableau (Knill / EC Zoo / Qiskit preset ID 126)

```
S_Z1 = Z Z Z Z I I
S_Z2 = Z Z I I Z Z
S_X1 = X X X X I I
S_X2 = X X I I X X
```

Uniform-weight-4 generators; n − k = 4. Each stabilizer corresponds to a square
face of a triangular-prism ladder (3 rungs, periodic boundary).

## Logical operators (Knill 2004 via EC Zoo)

```
X̄_1 = I I X X I I   (= X_L, weight 2, support {2,3})
Z̄_1 = Z I I Z Z I   (= Z_L, weight 3, support {0,3,4})
X̄_2 = I X I X X I   (= X_S, weight 3, support {1,3,4})
Z̄_2 = I I I I Z Z   (= Z_S, weight 2, support {4,5})
```

Anticommutation table: `X̄_1` anticomm `Z̄_1` (overlap {3}, odd), `X̄_2`
anticomm `Z̄_2` (overlap {4}, odd); all other pairwise logical products commute
(cross-pairs have even overlap, same-X / same-Z trivially).

## Equivalence notes

- The Ganti-Onunkwo-Young (GOY) code at r = 1 is the C_6 code (different
  family-presentation; not formalized here).
- The [[k+4, k, 2]] H code at k = 2 is the C_6 code.
- The Khesin-Lu-Shor code at r = 2, m = 3 is the C_6 code.
- The [[4, 2, 2]] code (`FourQubit_4_2_2.lean`) is C_6's structural sibling in
  Knill's C_4/C_6 concatenation; we copy that file's k = 2 logical packaging
  pattern.

This file is a **Stage-2 skeleton**: every theorem ends in a `sorry` tagged
`TODO(stab_6_2_2-T<n>): …`. Stage 4 closes them following the
`FourQubit_4_2_2.lean` (k = 2 structure) + `CSS_4_1_2.lean` (multi-Z-stab
structure) blended template.
-/

open NQubitPauliGroupElement

/-! ## §1 — Generators

The four Knill stabilizers of C_6. All have phase 0 and uniform weight 4. Qubit
indexing is 0-based; qubits 0,1 are the "top" pair, 2,3 the "middle" pair, 4,5
the "bottom" pair.
-/

/-- First Z-check stabilizer: `Z Z Z Z I I` (Z on qubits 0,1,2,3). -/
def S_Z1 : NQubitPauliGroupElement 6 := σ[ZZZZII]

/-- Second Z-check stabilizer: `Z Z I I Z Z` (Z on qubits 0,1,4,5). -/
def S_Z2 : NQubitPauliGroupElement 6 := σ[ZZIIZZ]

/-- First X-check stabilizer: `X X X X I I` (X on qubits 0,1,2,3). -/
def S_X1 : NQubitPauliGroupElement 6 := σ[XXXXII]

/-- Second X-check stabilizer: `X X I I X X` (X on qubits 0,1,4,5). -/
def S_X2 : NQubitPauliGroupElement 6 := σ[XXIIXX]

/-! ## §2 — Generator sets and subgroup -/

/-- The two Z-check generators. -/
def ZGenerators : Set (NQubitPauliGroupElement 6) :=
  {S_Z1, S_Z2}

/-- The two X-check generators. -/
def XGenerators : Set (NQubitPauliGroupElement 6) :=
  {S_X1, S_X2}

/-- The full generator set: two Z-checks and two X-checks. -/
def generators : Set (NQubitPauliGroupElement 6) :=
  ZGenerators ∪ XGenerators

/-- The [[6, 2, 2]] C_6 stabilizer subgroup: closure of the four Knill
generators. -/
noncomputable def subgroup : Subgroup (NQubitPauliGroupElement 6) :=
  Subgroup.closure generators

/-! ## §3 — Z-type and X-type predicates -/

/-- Each Z-generator is Z-type (I or Z on every qubit). -/
lemma ZGenerators_are_ZType :
    ∀ g, g ∈ ZGenerators → NQubitPauliGroupElement.IsZTypeElement g := by
  classical
  intro g hg
  rcases (by simpa [ZGenerators] using hg) with rfl | rfl
  · refine ⟨rfl, ?_⟩
    intro i
    fin_cases i <;>
      simp [PauliOperator.IsZType, S_Z1, NQubitPauliOperator.set, NQubitPauliOperator.identity]
  · refine ⟨rfl, ?_⟩
    intro i
    fin_cases i <;>
      simp [PauliOperator.IsZType, S_Z2, NQubitPauliOperator.set, NQubitPauliOperator.identity]

/-- Each X-generator is X-type (I or X on every qubit). -/
lemma XGenerators_are_XType :
    ∀ g, g ∈ XGenerators → NQubitPauliGroupElement.IsXTypeElement g := by
  classical
  intro g hg
  rcases (by simpa [XGenerators] using hg) with rfl | rfl
  · refine ⟨rfl, ?_⟩
    intro i
    fin_cases i <;>
      simp [PauliOperator.IsXType, S_X1, NQubitPauliOperator.set, NQubitPauliOperator.identity]
  · refine ⟨rfl, ?_⟩
    intro i
    fin_cases i <;>
      simp [PauliOperator.IsXType, S_X2, NQubitPauliOperator.set, NQubitPauliOperator.identity]

/-! ## §4 — Cross-commutation (Z-generators commute with X-generators)

Pairwise overlap counts (all even ⇒ all commute):
- `S_Z1 = ZZZZ II` vs `S_X1 = XXXX II`: anti at {0,1,2,3}, count 4.
- `S_Z1` vs `S_X2 = XX II XX`: anti at {0,1}, count 2.
- `S_Z2 = ZZ II ZZ` vs `S_X1`: anti at {0,1}, count 2.
- `S_Z2` vs `S_X2`: anti at {0,1,4,5}, count 4.
-/

private lemma S_Z1_comm_S_X1 : S_Z1 * S_X1 = S_X1 * S_Z1 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 6) S_Z1.operators S_X1.operators)) =
        ({0, 1, 2, 3} : Finset (Fin 6)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, S_Z1, S_X1,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma S_Z1_comm_S_X2 : S_Z1 * S_X2 = S_X2 * S_Z1 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 6) S_Z1.operators S_X2.operators)) =
        ({0, 1} : Finset (Fin 6)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, S_Z1, S_X2,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma S_Z2_comm_S_X1 : S_Z2 * S_X1 = S_X1 * S_Z2 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 6) S_Z2.operators S_X1.operators)) =
        ({0, 1} : Finset (Fin 6)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, S_Z2, S_X1,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma S_Z2_comm_S_X2 : S_Z2 * S_X2 = S_X2 * S_Z2 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 6) S_Z2.operators S_X2.operators)) =
        ({0, 1, 4, 5} : Finset (Fin 6)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, S_Z2, S_X2,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

/-- Every Z-generator commutes with every X-generator. -/
lemma ZGenerators_commute_XGenerators :
    ∀ z ∈ ZGenerators, ∀ x ∈ XGenerators, z * x = x * z := by
  classical
  intro z hz x hx
  rcases (by simpa [ZGenerators] using hz) with rfl | rfl
  · rcases (by simpa [XGenerators] using hx) with rfl | rfl
    · exact S_Z1_comm_S_X1
    · exact S_Z1_comm_S_X2
  · rcases (by simpa [XGenerators] using hx) with rfl | rfl
    · exact S_Z2_comm_S_X1
    · exact S_Z2_comm_S_X2

/-! ## §5 — All-pair commutation -/

private lemma ZType_commutes {g h : NQubitPauliGroupElement 6}
    (hg : NQubitPauliGroupElement.IsZTypeElement g)
    (hh : NQubitPauliGroupElement.IsZTypeElement h) :
    g * h = h * g :=
  CSSCommutationLemmas.ZType_commutes hg hh

private lemma XType_commutes {g h : NQubitPauliGroupElement 6}
    (hg : NQubitPauliGroupElement.IsXTypeElement g)
    (hh : NQubitPauliGroupElement.IsXTypeElement h) :
    g * h = h * g :=
  CSSCommutationLemmas.XType_commutes hg hh

/-- All generators of the [[6, 2, 2]] code pairwise commute. -/
theorem generators_commute :
    ∀ g ∈ generators, ∀ h ∈ generators, g * h = h * g := by
  classical
  intro g hg h hh
  have hg' : g ∈ ZGenerators ∨ g ∈ XGenerators := by simpa [generators] using hg
  have hh' : h ∈ ZGenerators ∨ h ∈ XGenerators := by simpa [generators] using hh
  rcases hg' with hgZ | hgX <;> rcases hh' with hhZ | hhX
  · exact ZType_commutes (ZGenerators_are_ZType g hgZ) (ZGenerators_are_ZType h hhZ)
  · exact ZGenerators_commute_XGenerators g hgZ h hhX
  · simpa using (ZGenerators_commute_XGenerators h hhZ g hgX).symm
  · exact XType_commutes (XGenerators_are_XType g hgX) (XGenerators_are_XType h hhX)

/-! ## §6 — `−I` is not in the stabilizer subgroup -/

/-- The [[6, 2, 2]] C_6 stabilizer subgroup does not contain `−I` (CSS
argument). -/
theorem negIdentity_not_mem :
    negIdentity 6 ∉ subgroup := by
  have hZX : ∀ z ∈ ZGenerators, ∀ x ∈ XGenerators, z * x = x * z :=
    ZGenerators_commute_XGenerators
  simpa [subgroup, generators] using
    (CSS.negIdentity_not_mem_closure_union (n := 6) ZGenerators XGenerators
      ZGenerators_are_ZType XGenerators_are_XType hZX)

/-! ## §7 — Generator list & symplectic-side independence -/

/-- The generator list (canonical order: Z-checks first, then X-checks). -/
def generatorsList : List (NQubitPauliGroupElement 6) :=
  [S_Z1, S_Z2, S_X1, S_X2]

/-- The list of generators has the same elements as the generator set. -/
lemma listToSet_generatorsList :
    NQubitPauliGroupElement.listToSet generatorsList = generators := by
  simp only [generatorsList, generators, ZGenerators, XGenerators,
    NQubitPauliGroupElement.listToSet_cons, NQubitPauliGroupElement.listToSet_nil]
  ext g
  simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false,
    or_false, or_assoc]

/-! ## §8 — Phase-zero + symplectic independence -/

/-- All four generators have phase 0 (no `i` or `−1` factor). -/
lemma AllPhaseZero_generatorsList :
    NQubitPauliGroupElement.AllPhaseZero generatorsList := by
  rw [generatorsList, NQubitPauliGroupElement.AllPhaseZero_cons]
  refine ⟨rfl, ?_⟩
  rw [NQubitPauliGroupElement.AllPhaseZero_cons]
  refine ⟨rfl, ?_⟩
  rw [NQubitPauliGroupElement.AllPhaseZero_cons]
  refine ⟨rfl, ?_⟩
  rw [NQubitPauliGroupElement.AllPhaseZero_cons]
  exact ⟨rfl, NQubitPauliGroupElement.AllPhaseZero_nil⟩

/-- The check-matrix rows of the four generators are linearly independent over
GF(2). -/
theorem rowsLinearIndependent_generatorsList :
    NQubitPauliGroupElement.rowsLinearIndependent generatorsList := by decide

/-- The generator list is an independent generating set. -/
theorem GeneratorsIndependent_6_generatorsList :
    GeneratorsIndependent 6 generatorsList :=
  GeneratorsIndependent_of_rowsLinearIndependent 6 generatorsList
    rowsLinearIndependent_generatorsList

/-! ## §9 — Bundled `StabilizerGroup 6` -/

/-- The [[6, 2, 2]] C_6 stabilizer group, from the generator list. -/
noncomputable def stabilizerGroup : StabilizerGroup 6 :=
  mkStabilizerFromGenerators 6 generatorsList
    (by rw [listToSet_generatorsList]; exact generators_commute)
    (by rw [listToSet_generatorsList]; exact negIdentity_not_mem)

/-- The bundled stabilizer group's underlying subgroup equals the closure of
`generators`. -/
lemma stabilizerGroup_toSubgroup_eq :
    stabilizerGroup.toSubgroup = subgroup := by
  simp only [stabilizerGroup, mkStabilizerFromGenerators, subgroup]
  rw [listToSet_generatorsList]

/-! ## §10 — Logical operators

The four logical operators per Knill 2004 (via EC Zoo `stab_6_2_2`):

```
X̄_1 = IIXXII   (= X_L, Knill "L" pair)
Z̄_1 = ZIIZZI   (= Z_L, Knill "L" pair)
X̄_2 = IXIXXI   (= X_S, Knill "S" pair)
Z̄_2 = IIIIZZ   (= Z_S, Knill "S" pair)
```

Indexing: `_1` ≡ Knill's "L" (long support on Z, short on X); `_2` ≡ Knill's "S"
(short support on Z, mid support on X).
-/

/-- Logical X for logical qubit 1: `IIXXII` (X on qubits 2, 3). -/
def logicalX_1 : NQubitPauliGroupElement 6 := σ[IIXXII]

/-- Logical X for logical qubit 2: `IXIXXI` (X on qubits 1, 3, 4). -/
def logicalX_2 : NQubitPauliGroupElement 6 := σ[IXIXXI]

/-- Logical Z for logical qubit 1: `ZIIZZI` (Z on qubits 0, 3, 4). -/
def logicalZ_1 : NQubitPauliGroupElement 6 := σ[ZIIZZI]

/-- Logical Z for logical qubit 2: `IIIIZZ` (Z on qubits 4, 5). -/
def logicalZ_2 : NQubitPauliGroupElement 6 := σ[IIIIZZ]

/-! ### Diagonal anticommutation: X̄_ℓ anticommutes Z̄_ℓ -/

/-- `X̄_1 = IIXXII` and `Z̄_1 = ZIIZZI` anticommute (overlap at qubit 3 only —
odd parity). -/
theorem logicalX_1_anticommutes_logicalZ_1 :
    NQubitPauliGroupElement.Anticommute logicalX_1 logicalZ_1 := by
  classical
  pauli_anticomm_odd_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 6)
              logicalX_1.operators logicalZ_1.operators)) =
        ({3} : Finset (Fin 6)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalX_1, logicalZ_1,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

/-- `X̄_2 = IXIXXI` and `Z̄_2 = IIIIZZ` anticommute (overlap at qubit 4 only —
odd parity). -/
theorem logicalX_2_anticommutes_logicalZ_2 :
    NQubitPauliGroupElement.Anticommute logicalX_2 logicalZ_2 := by
  classical
  pauli_anticomm_odd_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 6)
              logicalX_2.operators logicalZ_2.operators)) =
        ({4} : Finset (Fin 6)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalX_2, logicalZ_2,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

/-! ### Off-diagonal logical commutation (the k = 2 novelty) -/

/-- `X̄_1 = IIXXII` and `X̄_2 = IXIXXI` commute (both X-type — trivial). -/
theorem logicalX_1_commutes_logicalX_2 :
    logicalX_1 * logicalX_2 = logicalX_2 * logicalX_1 := by
  pauli_comm_componentwise [logicalX_1, logicalX_2]

/-- `X̄_1 = IIXXII` and `Z̄_2 = IIIIZZ` commute (disjoint supports {2,3} vs
{4,5} — empty overlap). -/
theorem logicalX_1_commutes_logicalZ_2 :
    logicalX_1 * logicalZ_2 = logicalZ_2 * logicalX_1 := by
  pauli_comm_componentwise [logicalX_1, logicalZ_2]

/-- `X̄_2 = IXIXXI` and `Z̄_1 = ZIIZZI` commute (anticommute at qubits 3,4;
count 2). -/
theorem logicalX_2_commutes_logicalZ_1 :
    logicalX_2 * logicalZ_1 = logicalZ_1 * logicalX_2 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 6)
              logicalX_2.operators logicalZ_1.operators)) =
        ({3, 4} : Finset (Fin 6)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalX_2, logicalZ_1,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

/-- `Z̄_1 = ZIIZZI` and `Z̄_2 = IIIIZZ` commute (both Z-type — trivial). -/
theorem logicalZ_1_commutes_logicalZ_2 :
    logicalZ_1 * logicalZ_2 = logicalZ_2 * logicalZ_1 := by
  pauli_comm_componentwise [logicalZ_1, logicalZ_2]

/-! ### Logical operators are in the centralizer

Per-generator commutation lemmas (16 total: 4 logicals × 4 generators). Each is
either `pauli_comm_componentwise` (when both factors are same-type or have
disjoint supports) or `pauli_comm_even_anticommutes` with an explicit filter
Finset. Supports of the filter Finsets:

| Logical \ Gen | `S_Z1` (q0,1,2,3) | `S_Z2` (q0,1,4,5) | `S_X1` (q0,1,2,3) | `S_X2` (q0,1,4,5) |
|---------------|-------------------|-------------------|-------------------|-------------------|
| `X̄_1=IIXXII` (q2,3) | {2,3}, 2 | ∅, 0 | both X | both X |
| `X̄_2=IXIXXI` (q1,3,4) | {1,3}, 2 | {1,4}, 2 | both X | both X |
| `Z̄_1=ZIIZZI` (q0,3,4) | both Z | both Z | {0,3}, 2 | {0,4}, 2 |
| `Z̄_2=IIIIZZ` (q4,5) | both Z | both Z | ∅, 0 | {4,5}, 2 |
-/

private lemma logicalX_1_commutes_S_Z1 : logicalX_1 * S_Z1 = S_Z1 * logicalX_1 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 6)
              logicalX_1.operators S_Z1.operators)) =
        ({2, 3} : Finset (Fin 6)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalX_1, S_Z1,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma logicalX_1_commutes_S_Z2 : logicalX_1 * S_Z2 = S_Z2 * logicalX_1 := by
  pauli_comm_componentwise [logicalX_1, S_Z2]

private lemma logicalX_1_commutes_S_X1 : logicalX_1 * S_X1 = S_X1 * logicalX_1 := by
  pauli_comm_componentwise [logicalX_1, S_X1]

private lemma logicalX_1_commutes_S_X2 : logicalX_1 * S_X2 = S_X2 * logicalX_1 := by
  pauli_comm_componentwise [logicalX_1, S_X2]

private lemma logicalX_2_commutes_S_Z1 : logicalX_2 * S_Z1 = S_Z1 * logicalX_2 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 6)
              logicalX_2.operators S_Z1.operators)) =
        ({1, 3} : Finset (Fin 6)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalX_2, S_Z1,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma logicalX_2_commutes_S_Z2 : logicalX_2 * S_Z2 = S_Z2 * logicalX_2 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 6)
              logicalX_2.operators S_Z2.operators)) =
        ({1, 4} : Finset (Fin 6)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalX_2, S_Z2,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma logicalX_2_commutes_S_X1 : logicalX_2 * S_X1 = S_X1 * logicalX_2 := by
  pauli_comm_componentwise [logicalX_2, S_X1]

private lemma logicalX_2_commutes_S_X2 : logicalX_2 * S_X2 = S_X2 * logicalX_2 := by
  pauli_comm_componentwise [logicalX_2, S_X2]

private lemma logicalZ_1_commutes_S_Z1 : logicalZ_1 * S_Z1 = S_Z1 * logicalZ_1 := by
  pauli_comm_componentwise [logicalZ_1, S_Z1]

private lemma logicalZ_1_commutes_S_Z2 : logicalZ_1 * S_Z2 = S_Z2 * logicalZ_1 := by
  pauli_comm_componentwise [logicalZ_1, S_Z2]

private lemma logicalZ_1_commutes_S_X1 : logicalZ_1 * S_X1 = S_X1 * logicalZ_1 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 6)
              logicalZ_1.operators S_X1.operators)) =
        ({0, 3} : Finset (Fin 6)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalZ_1, S_X1,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma logicalZ_1_commutes_S_X2 : logicalZ_1 * S_X2 = S_X2 * logicalZ_1 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 6)
              logicalZ_1.operators S_X2.operators)) =
        ({0, 4} : Finset (Fin 6)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalZ_1, S_X2,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma logicalZ_2_commutes_S_Z1 : logicalZ_2 * S_Z1 = S_Z1 * logicalZ_2 := by
  pauli_comm_componentwise [logicalZ_2, S_Z1]

private lemma logicalZ_2_commutes_S_Z2 : logicalZ_2 * S_Z2 = S_Z2 * logicalZ_2 := by
  pauli_comm_componentwise [logicalZ_2, S_Z2]

private lemma logicalZ_2_commutes_S_X1 : logicalZ_2 * S_X1 = S_X1 * logicalZ_2 := by
  pauli_comm_componentwise [logicalZ_2, S_X1]

private lemma logicalZ_2_commutes_S_X2 : logicalZ_2 * S_X2 = S_X2 * logicalZ_2 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 6)
              logicalZ_2.operators S_X2.operators)) =
        ({4, 5} : Finset (Fin 6)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalZ_2, S_X2,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

/-- `X̄_1 = IIXXII` commutes with every element of the stabilizer. -/
theorem logicalX_1_mem_centralizer :
    logicalX_1 ∈ centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff, stabilizerGroup_toSubgroup_eq, subgroup]
  rw [Subgroup.forall_comm_closure_iff]
  intro s hs
  simp only [generators, Set.mem_union] at hs
  rcases hs with hgZ | hgX
  · rcases (by simpa [ZGenerators] using hgZ) with rfl | rfl
    · exact logicalX_1_commutes_S_Z1.symm
    · exact logicalX_1_commutes_S_Z2.symm
  · rcases (by simpa [XGenerators] using hgX) with rfl | rfl
    · exact logicalX_1_commutes_S_X1.symm
    · exact logicalX_1_commutes_S_X2.symm

/-- `X̄_2 = IXIXXI` commutes with every element of the stabilizer. -/
theorem logicalX_2_mem_centralizer :
    logicalX_2 ∈ centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff, stabilizerGroup_toSubgroup_eq, subgroup]
  rw [Subgroup.forall_comm_closure_iff]
  intro s hs
  simp only [generators, Set.mem_union] at hs
  rcases hs with hgZ | hgX
  · rcases (by simpa [ZGenerators] using hgZ) with rfl | rfl
    · exact logicalX_2_commutes_S_Z1.symm
    · exact logicalX_2_commutes_S_Z2.symm
  · rcases (by simpa [XGenerators] using hgX) with rfl | rfl
    · exact logicalX_2_commutes_S_X1.symm
    · exact logicalX_2_commutes_S_X2.symm

/-- `Z̄_1 = ZIIZZI` commutes with every element of the stabilizer. -/
theorem logicalZ_1_mem_centralizer :
    logicalZ_1 ∈ centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff, stabilizerGroup_toSubgroup_eq, subgroup]
  rw [Subgroup.forall_comm_closure_iff]
  intro s hs
  simp only [generators, Set.mem_union] at hs
  rcases hs with hgZ | hgX
  · rcases (by simpa [ZGenerators] using hgZ) with rfl | rfl
    · exact logicalZ_1_commutes_S_Z1.symm
    · exact logicalZ_1_commutes_S_Z2.symm
  · rcases (by simpa [XGenerators] using hgX) with rfl | rfl
    · exact logicalZ_1_commutes_S_X1.symm
    · exact logicalZ_1_commutes_S_X2.symm

/-- `Z̄_2 = IIIIZZ` commutes with every element of the stabilizer. -/
theorem logicalZ_2_mem_centralizer :
    logicalZ_2 ∈ centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff, stabilizerGroup_toSubgroup_eq, subgroup]
  rw [Subgroup.forall_comm_closure_iff]
  intro s hs
  simp only [generators, Set.mem_union] at hs
  rcases hs with hgZ | hgX
  · rcases (by simpa [ZGenerators] using hgZ) with rfl | rfl
    · exact logicalZ_2_commutes_S_Z1.symm
    · exact logicalZ_2_commutes_S_Z2.symm
  · rcases (by simpa [XGenerators] using hgX) with rfl | rfl
    · exact logicalZ_2_commutes_S_X1.symm
    · exact logicalZ_2_commutes_S_X2.symm

/-! ## §13 — `StabilizerCode 6 2` packaging -/

/-- The two-logical-qubit `LogicalQubitOps` family. -/
private def logicalOps6_2_2 : Fin 2 → LogicalQubitOps 6 stabilizerGroup := fun ℓ =>
  match ℓ with
  | 0 => ⟨logicalX_1, logicalZ_1,
            logicalX_1_mem_centralizer, logicalZ_1_mem_centralizer,
            logicalX_1_anticommutes_logicalZ_1⟩
  | 1 => ⟨logicalX_2, logicalZ_2,
            logicalX_2_mem_centralizer, logicalZ_2_mem_centralizer,
            logicalX_2_anticommutes_logicalZ_2⟩

/-- The [[6, 2, 2]] C_6 code as a stabilizer code on 6 physical qubits with 2
logical qubits. -/
noncomputable def stabilizerCode : StabilizerCode 6 2 where
  hk := by decide
  generatorsList := generatorsList
  generators_length := rfl
  generators_phaseZero := AllPhaseZero_generatorsList
  generators_independent := GeneratorsIndependent_6_generatorsList
  generators_commute := by rw [listToSet_generatorsList]; exact generators_commute
  closure_no_neg_identity := by rw [listToSet_generatorsList]; exact negIdentity_not_mem
  logicalOps := logicalOps6_2_2
  logical_commute_cross := by
    intro ℓ ℓ' hne
    fin_cases ℓ <;> fin_cases ℓ'
    · exact (hne rfl).elim
    · refine ⟨logicalX_1_commutes_logicalX_2, logicalX_1_commutes_logicalZ_2, ?_, ?_⟩
      · exact logicalX_2_commutes_logicalZ_1.symm
      · exact logicalZ_1_commutes_logicalZ_2
    · refine ⟨logicalX_1_commutes_logicalX_2.symm, logicalX_2_commutes_logicalZ_1, ?_, ?_⟩
      · exact logicalX_1_commutes_logicalZ_2.symm
      · exact logicalZ_1_commutes_logicalZ_2.symm
    · exact (hne rfl).elim

/-! ## §14 — Code distance = 2 -/

/-- The stabilizer-code subgroup equals the closure of the (set-form)
generators. -/
private lemma stabilizerCode_toSubgroup_eq :
    stabilizerCode.toStabilizerGroup.toSubgroup = Subgroup.closure generators := by
  change (Subgroup.closure (NQubitPauliGroupElement.listToSet generatorsList) : _) =
    Subgroup.closure generators
  rw [listToSet_generatorsList]

/-- Helper: a weight-1 Pauli with local Pauli `P ∈ {X, Y}` at qubit
`i ∈ {0,1,2,3}` (the support of `S_Z1`) anticommutes with `S_Z1 = ZZZZ II`. -/
private lemma weightOneAt_anticomm_S_Z1 (i : Fin 6) (P : PauliOperator)
    (hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3)
    (hP : P = PauliOperator.X ∨ P = PauliOperator.Y) :
    NQubitPauliGroupElement.Anticommute (weightOneAt i P) S_Z1 := by
  classical
  pauli_anticomm_odd_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 6)
              (weightOneAt i P).operators S_Z1.operators)) =
        ({i} : Finset (Fin 6)) := by
    ext j
    rcases hi with rfl | rfl | rfl | rfl <;> rcases hP with rfl | rfl <;> fin_cases j <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt,
        weightOneAt, NQubitPauliGroupElement.ofOperator,
        S_Z1, NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; simp +decide

/-- Helper: a weight-1 Pauli with local Pauli `P ∈ {X, Y}` at qubit
`i ∈ {0,1,4,5}` (the support of `S_Z2`) anticommutes with `S_Z2 = ZZ II ZZ`. -/
private lemma weightOneAt_anticomm_S_Z2 (i : Fin 6) (P : PauliOperator)
    (hi : i = 0 ∨ i = 1 ∨ i = 4 ∨ i = 5)
    (hP : P = PauliOperator.X ∨ P = PauliOperator.Y) :
    NQubitPauliGroupElement.Anticommute (weightOneAt i P) S_Z2 := by
  classical
  pauli_anticomm_odd_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 6)
              (weightOneAt i P).operators S_Z2.operators)) =
        ({i} : Finset (Fin 6)) := by
    ext j
    rcases hi with rfl | rfl | rfl | rfl <;> rcases hP with rfl | rfl <;> fin_cases j <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt,
        weightOneAt, NQubitPauliGroupElement.ofOperator,
        S_Z2, NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; simp +decide

/-- Helper: a weight-1 Pauli with local Pauli `Z` at qubit `i ∈ {0,1,2,3}` (the
support of `S_X1`) anticommutes with `S_X1 = XXXX II`. -/
private lemma weightOneAt_Z_anticomm_S_X1 (i : Fin 6)
    (hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) :
    NQubitPauliGroupElement.Anticommute (weightOneAt i PauliOperator.Z) S_X1 := by
  classical
  pauli_anticomm_odd_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 6)
              (weightOneAt i PauliOperator.Z).operators S_X1.operators)) =
        ({i} : Finset (Fin 6)) := by
    ext j
    rcases hi with rfl | rfl | rfl | rfl <;> fin_cases j <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt,
        weightOneAt, NQubitPauliGroupElement.ofOperator,
        S_X1, NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; simp +decide

/-- Helper: a weight-1 Pauli with local Pauli `Z` at qubit `i ∈ {0,1,4,5}` (the
support of `S_X2`) anticommutes with `S_X2 = XX II XX`. -/
private lemma weightOneAt_Z_anticomm_S_X2 (i : Fin 6)
    (hi : i = 0 ∨ i = 1 ∨ i = 4 ∨ i = 5) :
    NQubitPauliGroupElement.Anticommute (weightOneAt i PauliOperator.Z) S_X2 := by
  classical
  pauli_anticomm_odd_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 6)
              (weightOneAt i PauliOperator.Z).operators S_X2.operators)) =
        ({i} : Finset (Fin 6)) := by
    ext j
    rcases hi with rfl | rfl | rfl | rfl <;> fin_cases j <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt,
        weightOneAt, NQubitPauliGroupElement.ofOperator,
        S_X2, NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; simp +decide

/-- Anticommute witness for the C_6 code: every weight-1 Pauli anticommutes with
at least one stabilizer generator.

Strategy: 3-way `hi_trichotomy` partition of qubits ({0,1} | {2,3} | {4,5}),
dispatched on the local Pauli `P`:
- `P = X` or `P = Y`: pick a Z-stab.
  - `i ∈ {0,1}`: both `S_Z1` and `S_Z2` work; pick `S_Z1` canonically.
  - `i ∈ {2,3}`: only `S_Z1` covers; use it.
  - `i ∈ {4,5}`: only `S_Z2` covers; use it.
- `P = Z`: pick an X-stab — same partition.
  - `i ∈ {0,1}`: pick `S_X1` canonically.
  - `i ∈ {2,3}`: only `S_X1` covers.
  - `i ∈ {4,5}`: only `S_X2` covers.
-/
private lemma weight_one_anticomm_witness :
    ∀ i : Fin 6, ∀ P : PauliOperator, P ≠ PauliOperator.I →
      ∃ g ∈ generators, NQubitPauliGroupElement.Anticommute
        (weightOneAt i P) g := by
  intro i P hP
  -- 3-way trichotomy: i ∈ {0,1} (both Z-stabs cover; pick S_Z1) |
  --                   i ∈ {2,3} (only S_Z1) | i ∈ {4,5} (only S_Z2).
  -- Dual partition holds for the X-stabs.
  have hi_trichotomy : (i = 0 ∨ i = 1) ∨ (i = 2 ∨ i = 3) ∨ (i = 4 ∨ i = 5) := by
    fin_cases i <;> tauto
  match P, hP with
  | PauliOperator.X, _ =>
    rcases hi_trichotomy with hi | hi | hi
    · -- i ∈ {0,1}: pick S_Z1 (also covers).
      refine ⟨S_Z1, by simp [generators, ZGenerators], ?_⟩
      exact weightOneAt_anticomm_S_Z1 i _
        (by rcases hi with rfl | rfl <;> tauto) (Or.inl rfl)
    · -- i ∈ {2,3}: pick S_Z1 (only one that covers).
      refine ⟨S_Z1, by simp [generators, ZGenerators], ?_⟩
      exact weightOneAt_anticomm_S_Z1 i _
        (by rcases hi with rfl | rfl <;> tauto) (Or.inl rfl)
    · -- i ∈ {4,5}: pick S_Z2 (only one that covers).
      refine ⟨S_Z2, by simp [generators, ZGenerators], ?_⟩
      exact weightOneAt_anticomm_S_Z2 i _
        (by rcases hi with rfl | rfl <;> tauto) (Or.inl rfl)
  | PauliOperator.Y, _ =>
    rcases hi_trichotomy with hi | hi | hi
    · refine ⟨S_Z1, by simp [generators, ZGenerators], ?_⟩
      exact weightOneAt_anticomm_S_Z1 i _
        (by rcases hi with rfl | rfl <;> tauto) (Or.inr rfl)
    · refine ⟨S_Z1, by simp [generators, ZGenerators], ?_⟩
      exact weightOneAt_anticomm_S_Z1 i _
        (by rcases hi with rfl | rfl <;> tauto) (Or.inr rfl)
    · refine ⟨S_Z2, by simp [generators, ZGenerators], ?_⟩
      exact weightOneAt_anticomm_S_Z2 i _
        (by rcases hi with rfl | rfl <;> tauto) (Or.inr rfl)
  | PauliOperator.Z, _ =>
    rcases hi_trichotomy with hi | hi | hi
    · -- i ∈ {0,1}: pick S_X1.
      refine ⟨S_X1, by simp [generators, XGenerators], ?_⟩
      exact weightOneAt_Z_anticomm_S_X1 i (by rcases hi with rfl | rfl <;> tauto)
    · -- i ∈ {2,3}: pick S_X1 (only one that covers).
      refine ⟨S_X1, by simp [generators, XGenerators], ?_⟩
      exact weightOneAt_Z_anticomm_S_X1 i (by rcases hi with rfl | rfl <;> tauto)
    · -- i ∈ {4,5}: pick S_X2 (only one that covers).
      refine ⟨S_X2, by simp [generators, XGenerators], ?_⟩
      exact weightOneAt_Z_anticomm_S_X2 i (by rcases hi with rfl | rfl <;> tauto)
  | PauliOperator.I, hP => exact (hP rfl).elim

/-- The C_6 [[6, 2, 2]] code has distance 2: every weight-1 single-qubit Pauli
anticommutes with at least one stabilizer generator (T31), and `X̄_1 = IIXXII`
is a nontrivial logical operator of weight exactly 2. -/
theorem code_has_distance_two : HasCodeDistance stabilizerCode 2 :=
  hasCodeDistance_two_of_anticommute_witness stabilizerCode generators
    stabilizerCode_toSubgroup_eq weight_one_anticomm_witness
    ⟨logicalX_1, (logicalOps6_2_2 0).xOp_nontrivial, by decide⟩

/-- The C_6 [[6, 2, 2]] code packaged with its distance. -/
noncomputable def stabilizerCodeWithDistance : StabilizerCodeWithDistance 6 2 2 where
  toStabilizerCode := stabilizerCode
  hasDistance      := code_has_distance_two

end SixQubit_6_2_2
end StabilizerGroup
end Quantum
