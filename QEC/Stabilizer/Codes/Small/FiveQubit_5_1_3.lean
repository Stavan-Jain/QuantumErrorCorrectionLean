import Mathlib.Tactic
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerGroup
import QEC.Stabilizer.Framework.Core.Stabilizer.SubgroupLemmas
import QEC.Stabilizer.Framework.Core.Stabilizer.Centralizer
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance
import QEC.Stabilizer.Framework.Core.CSS.CSSDistance
import QEC.Stabilizer.Framework.Core.Logical.LogicalOperators
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerCode
import QEC.Stabilizer.Framework.Core.CodeNotation
import QEC.Stabilizer.Foundations.PauliGroup.Commutation
import QEC.Stabilizer.Foundations.PauliGroup.CommutationTactics
import QEC.Stabilizer.Foundations.PauliGroup.NQubitOperator
import QEC.Stabilizer.Foundations.PauliGroup.NQubitElement
import QEC.Stabilizer.Foundations.BinarySymplectic.Core
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrix
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrixDecidable
import QEC.Stabilizer.Framework.Symplectic.IndependentEquiv
import QEC.Stabilizer.Foundations.BinarySymplectic.SymplecticInner
import QEC.Stabilizer.Framework.Symplectic.SymplecticSpan

namespace Quantum
open scoped BigOperators
open scoped Pauli

namespace StabilizerGroup
namespace FiveQubit_5_1_3

/-!
# The five-qubit perfect code [[5, 1, 3]] (Laflamme et al. 1996)

The smallest stabilizer code that corrects an arbitrary single-qubit error.
It encodes `k = 1` logical qubit in `n = 5` physical qubits with distance
`d = 3`, saturating the quantum Hamming bound.

## Stabilizer generators (cyclic shifts of XZZXI)

| Name | Pauli string |
|------|--------------|
| g₁   | `X Z Z X I`  |
| g₂   | `I X Z Z X`  |
| g₃   | `X I X Z Z`  |
| g₄   | `Z X I X Z`  |

## Logical operators

`X̄ = X X X X X`, `Z̄ = Z Z Z Z Z` (full-support, same as Steane7 / Shor9).

## Non-CSS divergence

This is the **first non-CSS code** in the repository. Each generator
contains both `X` and `Z` factors on different qubits, so it satisfies
neither `IsZTypeElement` nor `IsXTypeElement`. Consequently:

* §3 (typing predicates) — SKIPPED.
* §4–§5 (cross-commutation + all-pair commutation) — done as 6 explicit
  pairwise commutations, then bundled via `rcases` on the 4-element
  generator set. No CSS shortcut.
* §6 (`−I ∉ closure`) — uses `negIdentity_not_mem_of_independent_phase_zero`
  (a general-form helper introduced for this code; see `gap_audit.md`),
  *not* `CSS.negIdentity_not_mem_closure_union`.
* §14 (distance proof) — preferentially `native_decide` on full
  `HasCodeDistance`; if that fails, manual enumeration of weight-1
  (via existing helper) and weight-2 (via a new helper —
  `no_weight_two_mem_centralizer_of_anticommute_witness`).

## References

* Laflamme, Miquel, Paz, Zurek, `arxiv:quant-ph/9602019`
* Bennett, DiVincenzo, Smolin, Wootters, `arxiv:quant-ph/9604024`
* EC Zoo `stab_5_1_3`, cross-referenced with Qiskit `preset:qiskit ID 21`

Stage 4 closed all 23 sorries from the original skeleton; the file
compiles to `lake build` without warnings other than mathlib-style
lints inherited from upstream files. See
`qec-lab:pipeline/attempts/stab_5_1_3/result.md` for the full session log.
-/

open NQubitPauliGroupElement

/-! ## Decidability

The anti-witness tables below close by `decide`, through the global
`DecidableEq (NQubitPauliGroupElement n)` and `Decidable (Anticommute p q)` instances in
`PauliGroup/Commutation.lean` (§ "Decidability of equality and `Anticommute`"). -/

/-! ## §1 — Generators (cyclic shifts of `XZZXI`) -/

/-- First generator: `X Z Z X I` (positions 0..4). -/
def g1 : NQubitPauliGroupElement 5 := σ[XZZXI]

/-- Second generator: `I X Z Z X` (cyclic shift of `g1` by 1). -/
def g2 : NQubitPauliGroupElement 5 := σ[IXZZX]

/-- Third generator: `X I X Z Z` (cyclic shift of `g1` by 2). -/
def g3 : NQubitPauliGroupElement 5 := σ[XIXZZ]

/-- Fourth generator: `Z X I X Z` (cyclic shift of `g1` by 3). -/
def g4 : NQubitPauliGroupElement 5 := σ[ZXIXZ]

/-! ## §2 — Generator set and subgroup

Non-CSS: a single flat generator set, no `ZGenerators`/`XGenerators`
partition. -/

/-- The four stabilizer generators of the [[5, 1, 3]] code. -/
def generators : Set (NQubitPauliGroupElement 5) :=
  {g1, g2, g3, g4}

/-- The [[5, 1, 3]] stabilizer subgroup: closure of `{g1, g2, g3, g4}`. -/
noncomputable def subgroup : Subgroup (NQubitPauliGroupElement 5) :=
  Subgroup.closure generators

/-! ## §3 — Z/X-type predicates

SKIPPED: this is a non-CSS code. Each `gᵢ` carries both `X` and `Z`
factors on different qubits, so `IsZTypeElement` and `IsXTypeElement`
both fail.
-/

/-! ## §4 — Pairwise commutation of generators (6 unordered pairs)

Each pair has an even number of anticommuting qubit positions (count = 2
in every case — see `informal_spec.md` for the explicit Finsets).
Closed by `pauli_comm_even_anticommutes` + explicit Finset computation,
mirroring `Steane7.lean`'s `Zᵢ_comm_Xⱼ` pattern.
-/

private lemma g1_comm_g2 : g1 * g2 = g2 * g1 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 5) g1.operators g2.operators)) =
        ({1, 3} : Finset (Fin 5)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, g1, g2,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma g1_comm_g3 : g1 * g3 = g3 * g1 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 5) g1.operators g3.operators)) =
        ({2, 3} : Finset (Fin 5)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, g1, g3,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma g1_comm_g4 : g1 * g4 = g4 * g1 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 5) g1.operators g4.operators)) =
        ({0, 1} : Finset (Fin 5)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, g1, g4,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma g2_comm_g3 : g2 * g3 = g3 * g2 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 5) g2.operators g3.operators)) =
        ({2, 4} : Finset (Fin 5)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, g2, g3,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma g2_comm_g4 : g2 * g4 = g4 * g2 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 5) g2.operators g4.operators)) =
        ({3, 4} : Finset (Fin 5)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, g2, g4,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma g3_comm_g4 : g3 * g4 = g4 * g3 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 5) g3.operators g4.operators)) =
        ({0, 3} : Finset (Fin 5)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, g3, g4,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  rw [hfilter]; decide

/-! ## §5 — All-pair commutation (full stabilizer abelianness) -/

/-- All four generators pairwise commute. -/
theorem generators_commute :
    ∀ g ∈ generators, ∀ h ∈ generators, g * h = h * g := by
  classical
  intro g hg h hh
  simp only [generators, Set.mem_insert_iff, Set.mem_singleton_iff] at hg hh
  rcases hg with rfl | rfl | rfl | rfl <;>
    rcases hh with rfl | rfl | rfl | rfl <;>
    first
      | rfl
      | exact g1_comm_g2 | exact g1_comm_g2.symm
      | exact g1_comm_g3 | exact g1_comm_g3.symm
      | exact g1_comm_g4 | exact g1_comm_g4.symm
      | exact g2_comm_g3 | exact g2_comm_g3.symm
      | exact g2_comm_g4 | exact g2_comm_g4.symm
      | exact g3_comm_g4 | exact g3_comm_g4.symm

/-! ## §7 — Generator list and `listToSet` equality

(Section §7 of `_TEMPLATE.lean`; moved here before §6 because the
`negIdentity_not_mem` proof refers to the list-form independence.)
-/

/-- Generators as a list (for symplectic-span / independence arguments). -/
def generatorsList : List (NQubitPauliGroupElement 5) :=
  [g1, g2, g3, g4]

/-- The list-form generators have the same elements as the set-form `generators`. -/
lemma listToSet_generatorsList :
    NQubitPauliGroupElement.listToSet generatorsList = generators := by
  simp only [generatorsList, generators,
    NQubitPauliGroupElement.listToSet_cons, NQubitPauliGroupElement.listToSet_nil]
  ext g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
    or_false]

/-! ## §9 — Phase-zero and generator independence -/

/-- Every element of the generators list has phase power 0. -/
lemma AllPhaseZero_generatorsList :
    NQubitPauliGroupElement.AllPhaseZero generatorsList := by
  rw [generatorsList, NQubitPauliGroupElement.AllPhaseZero_cons]
  exact ⟨rfl, (NQubitPauliGroupElement.AllPhaseZero_cons _ _).mpr
    ⟨rfl, (NQubitPauliGroupElement.AllPhaseZero_cons _ _).mpr
      ⟨rfl, (NQubitPauliGroupElement.AllPhaseZero_cons _ _).mpr
        ⟨rfl, NQubitPauliGroupElement.AllPhaseZero_nil⟩⟩⟩⟩

/-- The check-matrix rows of the four generators are linearly independent. -/
theorem rowsLinearIndependent_generatorsList :
    NQubitPauliGroupElement.rowsLinearIndependent generatorsList := by decide

/-- The generator list is an independent generating set. -/
theorem GeneratorsIndependent_5_generatorsList :
    GeneratorsIndependent 5 generatorsList :=
  GeneratorsIndependent_of_rowsLinearIndependent 5 generatorsList
    rowsLinearIndependent_generatorsList

/-! ## §6 — `−I` is not in the stabilizer subgroup

**Non-CSS divergence**: cannot use
`CSS.negIdentity_not_mem_closure_union`. We rely on the general-form
helper `negIdentity_not_mem_of_indep_phase_zero_commute` in
`BinarySymplectic/SymplecticSpan.lean` (added during Stage-4 of this
code's formalization; see `gap_audit.md` Gap 1).
-/

/-- `−I` is not in the [[5, 1, 3]] stabilizer subgroup.

Non-CSS argument via the general helper
`NQubitPauliGroupElement.negIdentity_not_mem_of_indep_phase_zero_commute` in
`BinarySymplectic/SymplecticSpan.lean`. The first non-CSS code in the repo
exercises this helper. -/
theorem negIdentity_not_mem :
    negIdentity 5 ∉ subgroup := by
  rw [subgroup, ← listToSet_generatorsList]
  refine NQubitPauliGroupElement.negIdentity_not_mem_of_indep_phase_zero_commute
    generatorsList AllPhaseZero_generatorsList rowsLinearIndependent_generatorsList ?_
  rw [listToSet_generatorsList]; exact generators_commute

/-! ## §8 — Bundled `StabilizerGroup 5` -/

/-- The [[5, 1, 3]] stabilizer group as a `StabilizerGroup 5`. -/
noncomputable def stabilizerGroup : StabilizerGroup 5 :=
  mkStabilizerFromGenerators 5 generatorsList
    (by rw [listToSet_generatorsList]; exact generators_commute)
    (by rw [listToSet_generatorsList]; exact negIdentity_not_mem)

/-- The bundled stabilizer subgroup agrees with the set-form `subgroup`. -/
lemma stabilizerGroup_toSubgroup_eq :
    stabilizerGroup.toSubgroup = subgroup := by
  simp only [stabilizerGroup, mkStabilizerFromGenerators, subgroup]
  rw [listToSet_generatorsList]

/-! ## §10 — Logical operators

Standard Gottesman / EC Zoo convention: full-support all-X and all-Z.
-/

/-- Logical `X̄`: `X` on all five qubits. -/
def logicalX : NQubitPauliGroupElement 5 :=
  ⟨0, NQubitPauliOperator.X 5⟩

/-- Logical `Z̄`: `Z` on all five qubits. -/
def logicalZ : NQubitPauliGroupElement 5 :=
  ⟨0, NQubitPauliOperator.Z 5⟩

/-- Optional logical `Ȳ` with the convention `Ȳ = i X̄ Z̄`. -/
noncomputable def logicalY : NQubitPauliGroupElement 5 :=
  NQubitPauliGroupElement.phaseI 5 * (logicalX * logicalZ)

/-! ## §11 — Logical anticommutation (`X̄` and `Z̄`)

For all-X / all-Z logicals, the dedicated lemma
`NQubitPauliOperator.allX_allZ_anticommute` closes this in one line
(since `n = 5` is odd).
-/

/-- `X̄` and `Z̄` anticommute (since `n = 5` is odd). -/
theorem logicalX_anticommutes_logicalZ :
    NQubitPauliGroupElement.Anticommute logicalX logicalZ :=
  NQubitPauliOperator.allX_allZ_anticommute 5 (by decide)

/-! ## §12 — Logicals in centralizer

Eight per-generator commutation lemmas (4 for `logicalX`, 4 for
`logicalZ`), each closed by `pauli_comm_even_anticommutes` + explicit
Finset. Then bundled via `Subgroup.forall_comm_closure_iff`.
-/

private lemma logicalX_commutes_g1 : logicalX * g1 = g1 * logicalX := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 5) logicalX.operators g1.operators)) =
        ({1, 2} : Finset (Fin 5)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalX, g1,
        NQubitPauliOperator.X, NQubitPauliOperator.set, NQubitPauliOperator.identity,
        PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma logicalX_commutes_g2 : logicalX * g2 = g2 * logicalX := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 5) logicalX.operators g2.operators)) =
        ({2, 3} : Finset (Fin 5)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalX, g2,
        NQubitPauliOperator.X, NQubitPauliOperator.set, NQubitPauliOperator.identity,
        PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma logicalX_commutes_g3 : logicalX * g3 = g3 * logicalX := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 5) logicalX.operators g3.operators)) =
        ({3, 4} : Finset (Fin 5)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalX, g3,
        NQubitPauliOperator.X, NQubitPauliOperator.set, NQubitPauliOperator.identity,
        PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma logicalX_commutes_g4 : logicalX * g4 = g4 * logicalX := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 5) logicalX.operators g4.operators)) =
        ({0, 4} : Finset (Fin 5)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalX, g4,
        NQubitPauliOperator.X, NQubitPauliOperator.set, NQubitPauliOperator.identity,
        PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma logicalZ_commutes_g1 : logicalZ * g1 = g1 * logicalZ := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 5) logicalZ.operators g1.operators)) =
        ({0, 3} : Finset (Fin 5)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalZ, g1,
        NQubitPauliOperator.Z, NQubitPauliOperator.set, NQubitPauliOperator.identity,
        PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma logicalZ_commutes_g2 : logicalZ * g2 = g2 * logicalZ := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 5) logicalZ.operators g2.operators)) =
        ({1, 4} : Finset (Fin 5)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalZ, g2,
        NQubitPauliOperator.Z, NQubitPauliOperator.set, NQubitPauliOperator.identity,
        PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma logicalZ_commutes_g3 : logicalZ * g3 = g3 * logicalZ := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 5) logicalZ.operators g3.operators)) =
        ({0, 2} : Finset (Fin 5)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalZ, g3,
        NQubitPauliOperator.Z, NQubitPauliOperator.set, NQubitPauliOperator.identity,
        PauliOperator.mulOp]
  rw [hfilter]; decide

private lemma logicalZ_commutes_g4 : logicalZ * g4 = g4 * logicalZ := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 5) logicalZ.operators g4.operators)) =
        ({1, 3} : Finset (Fin 5)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, logicalZ, g4,
        NQubitPauliOperator.Z, NQubitPauliOperator.set, NQubitPauliOperator.identity,
        PauliOperator.mulOp]
  rw [hfilter]; decide

/-- `X̄` commutes with every element of the stabilizer. -/
theorem logicalX_mem_centralizer :
    logicalX ∈ centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff, stabilizerGroup_toSubgroup_eq, subgroup]
  rw [Subgroup.forall_comm_closure_iff]
  intro s hs
  simp only [generators, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact logicalX_commutes_g1.symm
  · exact logicalX_commutes_g2.symm
  · exact logicalX_commutes_g3.symm
  · exact logicalX_commutes_g4.symm

/-- `Z̄` commutes with every element of the stabilizer. -/
theorem logicalZ_mem_centralizer :
    logicalZ ∈ centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff, stabilizerGroup_toSubgroup_eq, subgroup]
  rw [Subgroup.forall_comm_closure_iff]
  intro s hs
  simp only [generators, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact logicalZ_commutes_g1.symm
  · exact logicalZ_commutes_g2.symm
  · exact logicalZ_commutes_g3.symm
  · exact logicalZ_commutes_g4.symm

/-! ## §13 — `StabilizerCode 5 1` packaging -/

/-- The single logical-qubit data (`k = 1`). -/
private def logicalOps5_1_3 : Fin 1 → LogicalQubitOps 5 stabilizerGroup :=
  fun _ => ⟨logicalX, logicalZ,
            logicalX_mem_centralizer, logicalZ_mem_centralizer,
            logicalX_anticommutes_logicalZ⟩

/-- The [[5, 1, 3]] five-qubit perfect code as a `StabilizerCode 5 1`. -/
noncomputable def stabilizerCode : Code[[5, 1]] where
  hk := by decide
  generatorsList := generatorsList
  generators_length := rfl
  generators_phaseZero := AllPhaseZero_generatorsList
  generators_independent := GeneratorsIndependent_5_generatorsList
  generators_commute := by rw [listToSet_generatorsList]; exact generators_commute
  closure_no_neg_identity := by rw [listToSet_generatorsList]; exact negIdentity_not_mem
  logicalOps := logicalOps5_1_3
  logical_commute_cross := fun ℓ ℓ' h => (h (Subsingleton.elim ℓ ℓ')).elim

/-- Bridge: the stabilizer-code's underlying subgroup is the closure of `generators`.
Used to translate distance proofs against `stabilizerGroup` into proofs against
`stabilizerCode.toStabilizerGroup`. -/
private lemma stabilizerCode_toSubgroup_eq :
    stabilizerCode.toStabilizerGroup.toSubgroup = Subgroup.closure generators := by
  change (Subgroup.closure (NQubitPauliGroupElement.listToSet generatorsList) : _) =
    Subgroup.closure generators
  rw [listToSet_generatorsList]

/-! ## §14 — Code distance = 3

The Core infrastructure for this proof has been added (Gap 1:
`negIdentity_not_mem_of_indep_phase_zero_commute` in `SymplecticSpan.lean`;
Gap 2: `weightTwoAt` + `no_weight_two_mem_centralizer_of_anticommute_witness`
in `Core/CSSDistance.lean`). What remains is the in-file enumeration of the
anticomm-witness table — 15 weight-1 cases and 90 weight-2 cases. Each case
needs an explicit Finset computation because the parity-based `Anticommute`
characterization uses `Classical.propDecidable` and the wrong-generator
branches need a clean failure path.

This is mechanical work (~300-500 LoC) deferred to a follow-up session;
the structure is documented below and in `gap_audit.md`.
-/

/-- Anticommutation depends only on the operator-parts (not phases): if two
elements have the same operator-part, they anticommute with the same things.
Promoted to `Core` if useful, but kept local here for now. -/
private lemma anticommute_of_operators_eq
    (p q r : NQubitPauliGroupElement 5) (h : p.operators = q.operators)
    (h_ac : NQubitPauliGroupElement.Anticommute p r) :
    NQubitPauliGroupElement.Anticommute q r := by
  rw [anticommutes_iff_odd_anticommutes] at h_ac ⊢
  classical
  have : Finset.univ.filter
        (NQubitPauliGroupElement.anticommutesAt q.operators r.operators) =
      Finset.univ.filter
        (NQubitPauliGroupElement.anticommutesAt p.operators r.operators) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [h]
  rw [this]
  exact h_ac

/-- The weight-3 distance witness, defined directly with operators `I, Y, Y,
I, X` and phase power 2. This is the operator-part of `logicalX * g1` (see
`logicalX_w3_eq_mul` below for the equivalence). Defined explicitly (not via
the `*` of noncomputable group operations) so that `decide` can reduce it. -/
def logicalX_w3 : NQubitPauliGroupElement 5 := -σ[IYYIX]

/-- Sanity check: the explicit definition matches `logicalX * g1`. -/
lemma logicalX_w3_eq_mul : logicalX_w3 = logicalX * g1 := by
  apply NQubitPauliGroupElement.ext
  · decide
  · funext i; fin_cases i <;> decide

/-- `logicalX_w3` has weight 3. -/
@[simp] lemma logicalX_w3_weight :
    NQubitPauliGroupElement.weight logicalX_w3 = 3 := by
  decide

/-- `logicalX_w3` anticommutes with `logicalZ`. By the parity criterion, the
overlap pattern `IYYIX` vs `ZZZZZ` anticommutes at qubits 1, 2, 4 (odd count). -/
private lemma logicalX_w3_anticomm_logicalZ :
    NQubitPauliGroupElement.Anticommute logicalX_w3 logicalZ := by
  change logicalX_w3 * logicalZ = NQubitPauliGroupElement.minusOne 5 * (logicalZ * logicalX_w3)
  apply NQubitPauliGroupElement.ext
  · decide
  · funext i; fin_cases i <;> decide

/-- `logicalX_w3 ∈ centralizer (stabilizerCode.toStabilizerGroup)`. Use the
equivalence `logicalX_w3 = logicalX * g1`: `logicalX` is in the centralizer
(it's the StabilizerCode's logical X), `g1` is in the stabilizer (which is
contained in the centralizer because the stabilizer is abelian), and the
centralizer is closed under multiplication. -/
private lemma logicalX_w3_mem_centralizer :
    logicalX_w3 ∈ centralizer stabilizerCode.toStabilizerGroup := by
  rw [logicalX_w3_eq_mul]
  apply (centralizer stabilizerCode.toStabilizerGroup).mul_mem
  · exact (logicalOps5_1_3 0).x_mem_centralizer
  · apply stabilizer_le_centralizer
    rw [stabilizerCode_toSubgroup_eq]
    exact Subgroup.subset_closure (by simp [generators])

/-- `logicalX_w3 ∉ stabilizerCode.toStabilizerGroup.toSubgroup`. Since it
anticommutes with `logicalZ` (a centralizer element), it cannot itself be
in the stabilizer. -/
private lemma logicalX_w3_not_mem_subgroup :
    logicalX_w3 ∉ stabilizerCode.toStabilizerGroup.toSubgroup := by
  apply not_mem_stabilizer_of_anticommutes_centralizer _ logicalX_w3 logicalZ
  · exact (logicalOps5_1_3 0).z_mem_centralizer
  · exact logicalX_w3_anticomm_logicalZ

/-- No stabilizer element shares `logicalX_w3`'s operator-part. If one did,
that element would anticommute with `logicalZ` (anticommutation depends only
on operators), but it commutes with `logicalZ` by virtue of being in the
abelian stabilizer subgroup. -/
private lemma logicalX_w3_no_stab_same_operators :
    ∀ s ∈ stabilizerCode.toStabilizerGroup.toSubgroup,
      s.operators ≠ logicalX_w3.operators := by
  intro s hs h_ops
  have hs_anti : NQubitPauliGroupElement.Anticommute s logicalZ :=
    anticommute_of_operators_eq logicalX_w3 s logicalZ h_ops.symm logicalX_w3_anticomm_logicalZ
  exact not_mem_stabilizer_of_anticommutes_centralizer
    stabilizerCode.toStabilizerGroup s logicalZ
    (logicalOps5_1_3 0).z_mem_centralizer hs_anti hs

/-- `logicalX_w3` is a non-trivial logical operator of `stabilizerCode`. -/
private lemma logicalX_w3_isNontrivial :
    IsNontrivialLogicalOperator logicalX_w3 stabilizerCode.toStabilizerGroup :=
  ⟨logicalX_w3_mem_centralizer, logicalX_w3_not_mem_subgroup,
   logicalX_w3_no_stab_same_operators⟩

/-! ### Weight-1 anticomm witness

For every qubit `i ∈ Fin 5` and every non-identity single-qubit Pauli `P`,
some generator anticommutes with `weightOneAt i P`. We use the
high-priority computable `DecidableEq` and `Decidable Anticommute`
instances from `PauliGroup/Commutation.lean` to close each case by
`decide`, with `first` backtracking across the four generators.

Generator local Paulis (for reference):
* `g₁ = X Z Z X I`
* `g₂ = I X Z Z X`
* `g₃ = X I X Z Z`
* `g₄ = Z X I X Z`
-/

private lemma weight_one_anticomm_witness :
    ∀ i : Fin 5, ∀ P : PauliOperator, P ≠ PauliOperator.I →
      ∃ g ∈ generators, NQubitPauliGroupElement.Anticommute
        (weightOneAt i P) g := by
  intro i P hP
  fin_cases i <;>
    (match P, hP with
    | PauliOperator.X, _ => first
      | exact ⟨g1, by simp [generators], by decide⟩
      | exact ⟨g2, by simp [generators], by decide⟩
      | exact ⟨g3, by simp [generators], by decide⟩
      | exact ⟨g4, by simp [generators], by decide⟩
    | PauliOperator.Y, _ => first
      | exact ⟨g1, by simp [generators], by decide⟩
      | exact ⟨g2, by simp [generators], by decide⟩
    | PauliOperator.Z, _ => first
      | exact ⟨g1, by simp [generators], by decide⟩
      | exact ⟨g2, by simp [generators], by decide⟩
      | exact ⟨g3, by simp [generators], by decide⟩
    | PauliOperator.I, hP => exact (hP rfl).elim)

/-! ### Weight-2 anticomm witness

For every distinct qubit pair `(i, j)` with `i ≠ j` and every pair of
non-identity Paulis `(P, Q)`, some generator anticommutes with
`weightTwoAt i j P Q`. Same structure as the weight-1 witness, but
nested: `match` on `(P, Q)` then `fin_cases i <;> fin_cases j` and
backtrack over generators by `first`. The `i = j` subgoals discharge
via `exact absurd rfl hij`. Unused generator branches per `(P, Q)`
case are trimmed (`g₄` is not needed for `(X, X)`, `(Y, Z)`, `(Z, Y)`)
to avoid `linter.unusedTactic` warnings. -/

private lemma weight_two_anticomm_witness :
    ∀ i j : Fin 5, i ≠ j → ∀ P Q : PauliOperator, P ≠ PauliOperator.I →
        Q ≠ PauliOperator.I →
      ∃ g ∈ generators, NQubitPauliGroupElement.Anticommute
        (weightTwoAt i j P Q) g := by
  intro i j hij P Q hP hQ
  match P, Q, hP, hQ with
  | PauliOperator.I, _, hP, _ => exact (hP rfl).elim
  | _, PauliOperator.I, _, hQ => exact (hQ rfl).elim
  | PauliOperator.X, PauliOperator.X, _, _ =>
      fin_cases i <;> fin_cases j <;> first
        | exact absurd rfl hij
        | exact ⟨g1, by simp [generators], by decide⟩
        | exact ⟨g2, by simp [generators], by decide⟩
        | exact ⟨g3, by simp [generators], by decide⟩
  | PauliOperator.X, PauliOperator.Y, _, _ =>
      fin_cases i <;> fin_cases j <;> first
        | exact absurd rfl hij
        | exact ⟨g1, by simp [generators], by decide⟩
        | exact ⟨g2, by simp [generators], by decide⟩
        | exact ⟨g3, by simp [generators], by decide⟩
        | exact ⟨g4, by simp [generators], by decide⟩
  | PauliOperator.X, PauliOperator.Z, _, _ =>
      fin_cases i <;> fin_cases j <;> first
        | exact absurd rfl hij
        | exact ⟨g1, by simp [generators], by decide⟩
        | exact ⟨g2, by simp [generators], by decide⟩
        | exact ⟨g3, by simp [generators], by decide⟩
        | exact ⟨g4, by simp [generators], by decide⟩
  | PauliOperator.Y, PauliOperator.X, _, _ =>
      fin_cases i <;> fin_cases j <;> first
        | exact absurd rfl hij
        | exact ⟨g1, by simp [generators], by decide⟩
        | exact ⟨g2, by simp [generators], by decide⟩
        | exact ⟨g3, by simp [generators], by decide⟩
        | exact ⟨g4, by simp [generators], by decide⟩
  | PauliOperator.Y, PauliOperator.Y, _, _ =>
      fin_cases i <;> fin_cases j <;> first
        | exact absurd rfl hij
        | exact ⟨g1, by simp [generators], by decide⟩
        | exact ⟨g2, by simp [generators], by decide⟩
        | exact ⟨g3, by simp [generators], by decide⟩
        | exact ⟨g4, by simp [generators], by decide⟩
  | PauliOperator.Y, PauliOperator.Z, _, _ =>
      fin_cases i <;> fin_cases j <;> first
        | exact absurd rfl hij
        | exact ⟨g1, by simp [generators], by decide⟩
        | exact ⟨g2, by simp [generators], by decide⟩
        | exact ⟨g3, by simp [generators], by decide⟩
  | PauliOperator.Z, PauliOperator.X, _, _ =>
      fin_cases i <;> fin_cases j <;> first
        | exact absurd rfl hij
        | exact ⟨g1, by simp [generators], by decide⟩
        | exact ⟨g2, by simp [generators], by decide⟩
        | exact ⟨g3, by simp [generators], by decide⟩
        | exact ⟨g4, by simp [generators], by decide⟩
  | PauliOperator.Z, PauliOperator.Y, _, _ =>
      fin_cases i <;> fin_cases j <;> first
        | exact absurd rfl hij
        | exact ⟨g1, by simp [generators], by decide⟩
        | exact ⟨g2, by simp [generators], by decide⟩
        | exact ⟨g3, by simp [generators], by decide⟩
  | PauliOperator.Z, PauliOperator.Z, _, _ =>
      fin_cases i <;> fin_cases j <;> first
        | exact absurd rfl hij
        | exact ⟨g1, by simp [generators], by decide⟩
        | exact ⟨g2, by simp [generators], by decide⟩
        | exact ⟨g3, by simp [generators], by decide⟩
        | exact ⟨g4, by simp [generators], by decide⟩

/-- The [[5, 1, 3]] five-qubit perfect code has distance 3.

Combines the weight-1 and weight-2 anti-witness tables above (which rule
out nontrivial logical operators of weight `< 3`) with the explicit
weight-3 witness `logicalX_w3 = IYYIX` and its non-triviality proof. -/
theorem code_has_distance_three : HasCodeDistance stabilizerCode 3 := by
  refine hasCodeDistance_of stabilizerCode 3 (by decide)
    ⟨logicalX_w3, logicalX_w3_isNontrivial, by decide⟩ ?_
  intro w hw_pos hw_lt g hg_weight h_nontrivial
  rcases (IsNontrivialLogicalOperator_iff g stabilizerCode.toStabilizerGroup).mp h_nontrivial
    with ⟨h_cent, _, _⟩
  interval_cases w
  · -- w = 1: no weight-1 nontrivial logical operator
    exact no_weight_one_mem_centralizer_of_anticommute_witness
      stabilizerCode.toStabilizerGroup generators stabilizerCode_toSubgroup_eq
      weight_one_anticomm_witness g hg_weight h_cent
  · -- w = 2: no weight-2 nontrivial logical operator
    exact no_weight_two_mem_centralizer_of_anticommute_witness
      stabilizerCode.toStabilizerGroup generators stabilizerCode_toSubgroup_eq
      weight_two_anticomm_witness g hg_weight h_cent

/-- The [[5, 1, 3]] perfect code packaged with its distance. -/
noncomputable def stabilizerCodeWithDistance : Code[[5, 1, 3]] where
  toStabilizerCode := stabilizerCode
  hasDistance      := code_has_distance_three

end FiveQubit_5_1_3
end StabilizerGroup
end Quantum
