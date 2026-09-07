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
namespace CSS_4_1_2

/-!
# The [[4, 1, 2]] LNCY code

The Leung-Nielsen-Chuang-Yamamoto [[4, 1, 2]] code is a four-qubit CSS
stabilizer code encoding one logical qubit, with code distance 2. It detects
(but does not correct) a single arbitrary Pauli error. Originally introduced in
[Leung-Nielsen-Chuang-Yamamoto 1997, `arxiv:quant-ph/9704002`, §II Eqs. 5–6].

## Codewords (LNCY convention, paper Eqs. 5–6)

```
|0_L⟩ = (|0000⟩ + |1111⟩)/√2
|1_L⟩ = (|0011⟩ + |1100⟩)/√2
```

## Stabilizer (chosen to stabilize the LNCY codewords above)

Three generators, n − k = 3:
- `S_Z1 = Z Z I I` (Z-type)
- `S_Z2 = I I Z Z` (Z-type)
- `S_X1 = X X X X` (X-type)

Note: the EC Zoo entry quotes a *dual* tableau `(XXII, IIXX, ZZZZ)` from the
Qiskit preset; that one stabilizes a different 2-d subspace. We use the LNCY
codeword convention as the ground truth.

## Logical operators

- `X̄ = X X I I` (overlaps `S_Z1` at qubits 0, 1; even ⇒ commutes)
- `Z̄ = Z I Z I` (overlaps `S_X1` at qubits 0, 2; even ⇒ commutes)

The two anticommute at qubit 0 only (X·Z vs no I overlap with I·I).

All theorems closed via the `FourQubit_4_2_2.lean` template, adjusted for the k
= 1, 2-Z-stab CSS structure (logical operators are weight-2 strings, and the
weight-1 anti-witness function dispatches on `i ∈ {0, 1}` vs `i ∈ {2, 3}` to
pick the appropriate Z-generator).
-/

open NQubitPauliGroupElement

/-! ## §1 — Generators -/

/-- First Z-check stabilizer: `Z Z I I` (Z on qubits 0, 1). -/
def S_Z1 : NQubitPauliGroupElement 4 := σ[ZZII]

/-- Second Z-check stabilizer: `I I Z Z` (Z on qubits 2, 3). -/
def S_Z2 : NQubitPauliGroupElement 4 := σ[IIZZ]

/-- The X-check stabilizer: `X X X X` (X on every qubit). -/
def S_X1 : NQubitPauliGroupElement 4 := σ[XXXX]

/-! ## §2 — Generator sets and subgroup -/

/-- The two Z-check generators. -/
def ZGenerators : Set (NQubitPauliGroupElement 4) :=
  {S_Z1, S_Z2}

/-- The single X-check generator. -/
def XGenerators : Set (NQubitPauliGroupElement 4) :=
  {S_X1}

/-- The full generator set: two Z-checks and one X-check. -/
def generators : Set (NQubitPauliGroupElement 4) :=
  ZGenerators ∪ XGenerators

/-- The [[4, 1, 2]] stabilizer subgroup: closure of `{ZZII, IIZZ, XXXX}`. -/
noncomputable def subgroup : Subgroup (NQubitPauliGroupElement 4) :=
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

/-- The X-generator is X-type (I or X on every qubit). -/
lemma XGenerators_are_XType :
    ∀ g, g ∈ XGenerators → NQubitPauliGroupElement.IsXTypeElement g := by
  classical
  intro g hg
  rcases (by simpa [XGenerators] using hg) with rfl
  refine ⟨rfl, ?_⟩
  intro i
  fin_cases i <;>
    simp [PauliOperator.IsXType, S_X1, NQubitPauliOperator.set]

/-! ## §4 — Cross-commutation (Z-generators commute with X-generators)

`S_Z1 = ZZII` overlaps `S_X1 = XXXX` (anticommutes pairwise) at qubits 0 and 1:
count 2 (even) ⇒ they commute. `S_Z2 = IIZZ` overlaps `S_X1` at qubits 2 and 3:
count 2 (even) ⇒ they commute. -/

private lemma S_Z1_comm_S_X1 : S_Z1 * S_X1 = S_X1 * S_Z1 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 4) S_Z1.operators S_X1.operators)) =
        ({0, 1} : Finset (Fin 4)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, S_Z1, S_X1,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma S_Z2_comm_S_X1 : S_Z2 * S_X1 = S_X1 * S_Z2 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 4) S_Z2.operators S_X1.operators)) =
        ({2, 3} : Finset (Fin 4)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, S_Z2, S_X1,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

/-- Every Z-generator commutes with every X-generator. -/
lemma ZGenerators_commute_XGenerators :
    ∀ z ∈ ZGenerators, ∀ x ∈ XGenerators, z * x = x * z := by
  classical
  intro z hz x hx
  rcases (by simpa [ZGenerators] using hz) with rfl | rfl
  · rcases (by simpa [XGenerators] using hx) with rfl
    exact S_Z1_comm_S_X1
  · rcases (by simpa [XGenerators] using hx) with rfl
    exact S_Z2_comm_S_X1

/-! ## §5 — All-pair commutation -/

private lemma ZType_commutes {g h : NQubitPauliGroupElement 4}
    (hg : NQubitPauliGroupElement.IsZTypeElement g)
    (hh : NQubitPauliGroupElement.IsZTypeElement h) :
    g * h = h * g :=
  CSSCommutationLemmas.ZType_commutes hg hh

private lemma XType_commutes {g h : NQubitPauliGroupElement 4}
    (hg : NQubitPauliGroupElement.IsXTypeElement g)
    (hh : NQubitPauliGroupElement.IsXTypeElement h) :
    g * h = h * g :=
  CSSCommutationLemmas.XType_commutes hg hh

/-- All generators of the [[4, 1, 2]] code pairwise commute. -/
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

/-- The [[4, 1, 2]] stabilizer subgroup does not contain `−I` (CSS argument). -/
theorem negIdentity_not_mem :
    negIdentity 4 ∉ subgroup := by
  have hZX : ∀ z ∈ ZGenerators, ∀ x ∈ XGenerators, z * x = x * z :=
    ZGenerators_commute_XGenerators
  simpa [subgroup, generators] using
    (CSS.negIdentity_not_mem_closure_union (n := 4) ZGenerators XGenerators
      ZGenerators_are_ZType XGenerators_are_XType hZX)

/-! ## §7 — Generator list & symplectic-side independence -/

/-- The generator list (canonical order: Z-checks first, then X-check). -/
def generatorsList : List (NQubitPauliGroupElement 4) :=
  [S_Z1, S_Z2, S_X1]

/-- The list of generators has the same elements as the generator set. -/
lemma listToSet_generatorsList :
    NQubitPauliGroupElement.listToSet generatorsList = generators := by
  simp only [generatorsList, generators, ZGenerators, XGenerators,
    NQubitPauliGroupElement.listToSet_cons, NQubitPauliGroupElement.listToSet_nil]
  ext g
  simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false,
    or_false, or_assoc]

/-! ## §8 — Phase-zero + symplectic independence -/

/-- All three generators have phase 0 (no `i` or `−1` factor). -/
lemma AllPhaseZero_generatorsList :
    NQubitPauliGroupElement.AllPhaseZero generatorsList := by
  rw [generatorsList, NQubitPauliGroupElement.AllPhaseZero_cons]
  refine ⟨rfl, ?_⟩
  rw [NQubitPauliGroupElement.AllPhaseZero_cons]
  refine ⟨rfl, ?_⟩
  rw [NQubitPauliGroupElement.AllPhaseZero_cons]
  exact ⟨rfl, NQubitPauliGroupElement.AllPhaseZero_nil⟩

/-- The check-matrix rows of the three generators are linearly independent over
GF(2). -/
theorem rowsLinearIndependent_generatorsList :
    NQubitPauliGroupElement.rowsLinearIndependent generatorsList := by decide

/-- The generator list is an independent generating set. -/
theorem GeneratorsIndependent_4_generatorsList :
    GeneratorsIndependent 4 generatorsList :=
  GeneratorsIndependent_of_rowsLinearIndependent 4 generatorsList
    rowsLinearIndependent_generatorsList

/-! ## §9 — Bundled `StabilizerGroup 4` -/

/-- The [[4, 1, 2]] stabilizer group, from the generator list. -/
noncomputable def stabilizerGroup : StabilizerGroup 4 :=
  mkStabilizerFromGenerators 4 generatorsList
    (by rw [listToSet_generatorsList]; exact generators_commute)
    (by rw [listToSet_generatorsList]; exact negIdentity_not_mem)

/-- The bundled stabilizer group's underlying subgroup equals the closure of
`generators`. -/
lemma stabilizerGroup_toSubgroup_eq :
    stabilizerGroup.toSubgroup = subgroup := by
  simp only [stabilizerGroup, mkStabilizerFromGenerators, subgroup]
  rw [listToSet_generatorsList]

/-! ## §10 — Logical operators

Logical `X̄ = X X I I` and logical `Z̄ = Z I Z I`, derived from the LNCY
codewords:

```
|0_L⟩ = (|0000⟩ + |1111⟩)/√2,   |1_L⟩ = (|0011⟩ + |1100⟩)/√2
```

`X̄ = XXII` maps `|0_L⟩ ↔ |1_L⟩`. `Z̄ = ZIZI` has eigenvalue +1 on `|0_L⟩` and
−1 on `|1_L⟩` (the parity `(-1)^(q₀ + q₂)` of the codeword basis kets is
constant on each codeword).
-/

/-- Logical X: `X X I I` (overlaps `S_Z1` at qubits 0, 1; even ⇒ commutes). -/
def logicalX : NQubitPauliGroupElement 4 := σ[XXII]

/-- Logical Z: `Z I Z I` (overlaps `S_X1` at qubits 0, 2; even ⇒ commutes). -/
def logicalZ : NQubitPauliGroupElement 4 := σ[ZIZI]

/-! ### §11 — Logical anticommutation -/

/-- `X̄ = XXII` and `Z̄ = ZIZI` anticommute (overlap at qubit 0 only — odd
parity). -/
theorem logicalX_anticommutes_logicalZ :
    NQubitPauliGroupElement.Anticommute logicalX logicalZ := by
  classical
  pauli_anticomm_odd_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 4)
              logicalX.operators logicalZ.operators)) =
        ({0} : Finset (Fin 4)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalX, logicalZ,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

/-! ### §12 — Logicals in centralizer (per-generator commutation lemmas) -/

private lemma logicalX_commutes_S_Z1 : logicalX * S_Z1 = S_Z1 * logicalX := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 4)
              logicalX.operators S_Z1.operators)) =
        ({0, 1} : Finset (Fin 4)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalX, S_Z1,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma logicalX_commutes_S_Z2 : logicalX * S_Z2 = S_Z2 * logicalX := by
  pauli_comm_componentwise [logicalX, S_Z2]

private lemma logicalX_commutes_S_X1 : logicalX * S_X1 = S_X1 * logicalX := by
  pauli_comm_componentwise [logicalX, S_X1]

private lemma logicalZ_commutes_S_Z1 : logicalZ * S_Z1 = S_Z1 * logicalZ := by
  pauli_comm_componentwise [logicalZ, S_Z1]

private lemma logicalZ_commutes_S_Z2 : logicalZ * S_Z2 = S_Z2 * logicalZ := by
  pauli_comm_componentwise [logicalZ, S_Z2]

private lemma logicalZ_commutes_S_X1 : logicalZ * S_X1 = S_X1 * logicalZ := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 4)
              logicalZ.operators S_X1.operators)) =
        ({0, 2} : Finset (Fin 4)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalZ, S_X1,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

/-- `X̄ = XXII` commutes with every element of the stabilizer. -/
theorem logicalX_mem_centralizer :
    logicalX ∈ centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff, stabilizerGroup_toSubgroup_eq, subgroup]
  rw [Subgroup.forall_comm_closure_iff]
  intro s hs
  simp only [generators, Set.mem_union] at hs
  rcases hs with hgZ | hgX
  · rcases (by simpa [ZGenerators] using hgZ) with rfl | rfl
    · exact logicalX_commutes_S_Z1.symm
    · exact logicalX_commutes_S_Z2.symm
  · rcases (by simpa [XGenerators] using hgX) with rfl
    exact logicalX_commutes_S_X1.symm

/-- `Z̄ = ZIZI` commutes with every element of the stabilizer. -/
theorem logicalZ_mem_centralizer :
    logicalZ ∈ centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff, stabilizerGroup_toSubgroup_eq, subgroup]
  rw [Subgroup.forall_comm_closure_iff]
  intro s hs
  simp only [generators, Set.mem_union] at hs
  rcases hs with hgZ | hgX
  · rcases (by simpa [ZGenerators] using hgZ) with rfl | rfl
    · exact logicalZ_commutes_S_Z1.symm
    · exact logicalZ_commutes_S_Z2.symm
  · rcases (by simpa [XGenerators] using hgX) with rfl
    exact logicalZ_commutes_S_X1.symm

/-! ## §13 — `StabilizerCode 4 1` packaging -/

/-- The single-logical-qubit `LogicalQubitOps` bundle. -/
private noncomputable def logicalOpsCSS_4_1_2 : Fin 1 → LogicalQubitOps 4 stabilizerGroup :=
  fun _ => ⟨logicalX, logicalZ, logicalX_mem_centralizer, logicalZ_mem_centralizer,
            logicalX_anticommutes_logicalZ⟩

/-- The [[4, 1, 2]] LNCY code as a stabilizer code on 4 physical qubits with 1
logical qubit. -/
noncomputable def stabilizerCode : StabilizerCode 4 1 where
  hk := by decide
  generatorsList := generatorsList
  generators_length := rfl
  generators_phaseZero := AllPhaseZero_generatorsList
  generators_independent := GeneratorsIndependent_4_generatorsList
  generators_commute := by rw [listToSet_generatorsList]; exact generators_commute
  closure_no_neg_identity := by rw [listToSet_generatorsList]; exact negIdentity_not_mem
  logicalOps := logicalOpsCSS_4_1_2
  logical_commute_cross := fun ℓ ℓ' h => (h (Subsingleton.elim ℓ ℓ')).elim

/-! ## §14 — Code distance = 2 -/

/-- The stabilizer-code subgroup equals the closure of the (set-form)
generators. -/
private lemma stabilizerCode_toSubgroup_eq :
    stabilizerCode.toStabilizerGroup.toSubgroup = Subgroup.closure generators := by
  change (Subgroup.closure (NQubitPauliGroupElement.listToSet generatorsList) : _) =
    Subgroup.closure generators
  rw [listToSet_generatorsList]

/-- Helper: a weight-1 Pauli with local Pauli `P ∈ {X, Y}` at qubit `i ∈ {0, 1}`
anticommutes with `S_Z1 = ZZII`. The proof shape mirrors
`FourQubit_4_2_2.weightOneAt_anticomm_Z1` but with the extra constraint
`i ∈ {0, 1}` (qubit indices where `S_Z1` has a Z), which we case-split on by
`rcases`. -/
private lemma weightOneAt_anticomm_S_Z1 (i : Fin 4) (P : PauliOperator)
    (hi : i = 0 ∨ i = 1)
    (hP : P = PauliOperator.X ∨ P = PauliOperator.Y) :
    NQubitPauliGroupElement.Anticommute (weightOneAt i P) S_Z1 := by
  classical
  pauli_anticomm_odd_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 4)
              (weightOneAt i P).operators S_Z1.operators)) =
        ({i} : Finset (Fin 4)) := by
    ext j; rcases hi with rfl | rfl <;> rcases hP with rfl | rfl <;> fin_cases j <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt,
        weightOneAt, NQubitPauliGroupElement.ofOperator,
        S_Z1, NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; simp +decide

/-- Helper: a weight-1 Pauli with local Pauli `P ∈ {X, Y}` at qubit `i ∈ {2, 3}`
anticommutes with `S_Z2 = IIZZ`. -/
private lemma weightOneAt_anticomm_S_Z2 (i : Fin 4) (P : PauliOperator)
    (hi : i = 2 ∨ i = 3)
    (hP : P = PauliOperator.X ∨ P = PauliOperator.Y) :
    NQubitPauliGroupElement.Anticommute (weightOneAt i P) S_Z2 := by
  classical
  pauli_anticomm_odd_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 4)
              (weightOneAt i P).operators S_Z2.operators)) =
        ({i} : Finset (Fin 4)) := by
    ext j; rcases hi with rfl | rfl <;> rcases hP with rfl | rfl <;> fin_cases j <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt,
        weightOneAt, NQubitPauliGroupElement.ofOperator,
        S_Z2, NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; simp +decide

/-- Helper: a weight-1 Pauli with local Pauli `Z` at any qubit `i` anticommutes
with `S_X1 = XXXX`. -/
private lemma weightOneAt_Z_anticomm_S_X1 (i : Fin 4) :
    NQubitPauliGroupElement.Anticommute (weightOneAt i PauliOperator.Z) S_X1 := by
  classical
  pauli_anticomm_odd_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 4)
              (weightOneAt i PauliOperator.Z).operators S_X1.operators)) =
        ({i} : Finset (Fin 4)) := by
    ext j; fin_cases i <;> fin_cases j <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt,
        weightOneAt, NQubitPauliGroupElement.ofOperator,
        S_X1, NQubitPauliOperator.set, PauliOperator.mulOp]
  rw [hfilter]; simp +decide

/-- Anticommute witness for the [[4,1,2]] LNCY code: every weight-1 Pauli
anticommutes with one of `S_Z1`, `S_Z2`, or `S_X1`. The Z-side splits on
`i ∈ {0, 1}` (use `S_Z1`) vs. `i ∈ {2, 3}` (use `S_Z2`). -/
private lemma weight_one_anticomm_witness :
    ∀ i : Fin 4, ∀ P : PauliOperator, P ≠ PauliOperator.I →
      ∃ g ∈ generators, NQubitPauliGroupElement.Anticommute
        (weightOneAt i P) g := by
  intro i P hP
  -- Dispatch the i ∈ {0,1} vs i ∈ {2,3} split once, reusable across P = X, P = Y.
  have hi_dichotomy : (i = 0 ∨ i = 1) ∨ (i = 2 ∨ i = 3) := by
    fin_cases i <;> tauto
  match P, hP with
  | PauliOperator.X, _ =>
    rcases hi_dichotomy with hi | hi
    · exact ⟨S_Z1, by simp [generators, ZGenerators],
        weightOneAt_anticomm_S_Z1 i _ hi (Or.inl rfl)⟩
    · exact ⟨S_Z2, by simp [generators, ZGenerators],
        weightOneAt_anticomm_S_Z2 i _ hi (Or.inl rfl)⟩
  | PauliOperator.Y, _ =>
    rcases hi_dichotomy with hi | hi
    · exact ⟨S_Z1, by simp [generators, ZGenerators],
        weightOneAt_anticomm_S_Z1 i _ hi (Or.inr rfl)⟩
    · exact ⟨S_Z2, by simp [generators, ZGenerators],
        weightOneAt_anticomm_S_Z2 i _ hi (Or.inr rfl)⟩
  | PauliOperator.Z, _ =>
    exact ⟨S_X1, by simp [generators, XGenerators], weightOneAt_Z_anticomm_S_X1 i⟩
  | PauliOperator.I, hP => exact (hP rfl).elim

/-- The [[4, 1, 2]] LNCY code has distance 2: every weight-1 single-qubit Pauli
anticommutes with at least one stabilizer generator, and `X̄ = XXII` is a
nontrivial logical operator of weight exactly 2. -/
theorem code_has_distance_two : HasCodeDistance stabilizerCode 2 :=
  hasCodeDistance_two_of_anticommute_witness stabilizerCode generators
    stabilizerCode_toSubgroup_eq weight_one_anticomm_witness
    ⟨logicalX, (logicalOpsCSS_4_1_2 0).xOp_nontrivial, by decide⟩

/-- The [[4, 1, 2]] LNCY code packaged with its distance. -/
noncomputable def stabilizerCodeWithDistance : StabilizerCodeWithDistance 4 1 2 where
  toStabilizerCode := stabilizerCode
  hasDistance      := code_has_distance_two

end CSS_4_1_2
end StabilizerGroup
end Quantum
