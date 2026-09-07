import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.Complex.Basic
import QEC.Stabilizer.Codes.Small.Steane7
import QEC.Foundations.Gates
import QEC.Foundations.GateConjugation
import QEC.Stabilizer.Framework.Core.Logical.LogicalGates
import QEC.Stabilizer.Framework.Core.Logical.LogicalCliffordAction
import QEC.Stabilizer.Foundations.PauliGroup.NQubitOperator
import QEC.Stabilizer.Foundations.PauliGroup.NQubitElement
import QEC.Stabilizer.Foundations.PauliGroup.Representation
import QEC.Stabilizer.Foundations.PauliGroup.TransversalConjugation
import QEC.Stabilizer.Foundations.PauliGroupSingle.Operator

namespace Quantum

open Matrix
open scoped BigOperators

/-!
Conjugation convention: conjugation by a matrix U means U P U† (adjoint on the
right). So we state and prove equalities of the form U * M * star U = ...
-/

namespace StabilizerGroup
namespace Steane7

open Matrix
open scoped BigOperators

/-!
# Transversal H and S as logical gates for the Steane [[7,1,3]] code

We show that the uniform transversal Hadamard and phase gates (H⊗7 and S⊗7) are
logical gates for the Steane code: they map the codespace to itself.
-/

/-- Transversal Hadamard: H on each of the 7 physical qubits. -/
noncomputable def transversalH_Steane7 : NQubitGate 7 :=
  uniformTransversalGate 7 H

/-- Transversal phase gate: S† on each of the 7 physical qubits. Conjugation is
U P U† (adjoint on the right). -/
noncomputable def transversalS_Steane7 : NQubitGate 7 :=
  uniformTransversalGate 7 inv_S

/-- Steane generators use only I, X, Z (no Y). -/
lemma generators_no_Y :
    ∀ g ∈ generatorsList, ∀ i, g.operators i ≠ PauliOperator.Y := by
  intro g hg i
  have h : g = Z1 ∨ g = Z2 ∨ g = Z3 ∨ g = X1 ∨ g = X2 ∨ g = X3 := by
    unfold generatorsList at hg
    aesop
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> fin_cases i <;> simp [Z1, Z2, Z3, X1, X2, X3,
    NQubitPauliOperator.set, NQubitPauliOperator.identity]

/-- Pauli group element with operators swapped (X↔Z). -/
def swapXZ_element (g : NQubitPauliGroupElement 7) : NQubitPauliGroupElement 7 :=
  ⟨g.phasePower, NQubitPauliOperator.transversalSwapXZ g.operators⟩

/-- `swapXZ_element` pairwise swaps the Steane X- and Z-generators. -/
private lemma swapXZ_element_swaps_generators :
    swapXZ_element Z1 = X1 ∧ swapXZ_element Z2 = X2 ∧ swapXZ_element Z3 = X3 ∧
      swapXZ_element X1 = Z1 ∧ swapXZ_element X2 = Z2 ∧ swapXZ_element X3 = Z3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (unfold swapXZ_element; congr 2; ext i; fin_cases i <;>
      simp [Z1, Z2, Z3, X1, X2, X3, NQubitPauliOperator.transversalSwapXZ,
        PauliOperator.swapXZ, NQubitPauliOperator.set, NQubitPauliOperator.identity])

/-- Swapping X↔Z on any Steane generator yields an element of the stabilizer
subgroup. -/
lemma transversalSwapXZ_mem_subgroup
    (g : NQubitPauliGroupElement 7) (hg : g ∈ generatorsList) :
    (⟨g.phasePower, NQubitPauliOperator.transversalSwapXZ g.operators⟩ :
      NQubitPauliGroupElement 7) ∈ subgroup := by
  obtain ⟨hZ1, hZ2, hZ3, hX1, hX2, hX3⟩ := swapXZ_element_swaps_generators
  change swapXZ_element g ∈ subgroup
  rcases (by simpa [generatorsList] using hg) with
    (rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals
    unfold subgroup
    refine Subgroup.subset_closure ?_
    simp [generators, ZGenerators, XGenerators, hZ1, hZ2, hZ3, hX1, hX2, hX3]

/-- Conjugating a Pauli group element (no Y) by transversal H gives the swapXZ
element (U P U†). -/
lemma transversalH_conjugates_element
    (g : NQubitPauliGroupElement 7) (h_no_Y : ∀ i, g.operators i ≠ .Y) :
    (uniformTransversalGateMatrix 7 H) * g.toMatrix * star (uniformTransversalGateMatrix 7 H) =
    (swapXZ_element g).toMatrix := by
  have h_conj := uniformTransversalGateMatrix_H_conj_op 7 g.operators h_no_Y
  unfold NQubitPauliGroupElement.toMatrix swapXZ_element
  simp [h_conj]

/-- Transversal H conjugates every stabilizer element to some stabilizer element
(U P U†). -/
lemma transversalH_conjugates_stabilizer_to_stabilizer (g : NQubitPauliGroupElement 7)
    (hg : g ∈ stabilizerGroup.toSubgroup) :
    ∃ g' ∈ stabilizerGroup.toSubgroup,
      transversalH_Steane7.val * g.toMatrix * star transversalH_Steane7.val = g'.toMatrix := by
  have hS :
      stabilizerGroup.toSubgroup =
        Subgroup.closure (NQubitPauliGroupElement.listToSet generatorsList) := by
    simp [stabilizerGroup_toSubgroup_eq, subgroup, listToSet_generatorsList]
  have hgen :
      ∀ x ∈ NQubitPauliGroupElement.listToSet generatorsList,
        ∃ x' ∈ stabilizerGroup.toSubgroup, conjByGate transversalH_Steane7 x.gate = x'.gate := by
    intro x hx
    have hxList : x ∈ generatorsList := by
      simpa [NQubitPauliGroupElement.listToSet] using hx
    refine ⟨swapXZ_element x, ?_, ?_⟩
    · simpa [stabilizerGroup_toSubgroup_eq] using transversalSwapXZ_mem_subgroup x hxList
    · apply Subtype.ext
      simpa [conjByGate_val, NQubitPauliGroupElement.gate_val] using
        transversalH_conjugates_element x (generators_no_Y x hxList)
  obtain ⟨g', hg', hgg'⟩ :=
    conjugates_mem_closure_of_set_conjugates transversalH_Steane7
      (NQubitPauliGroupElement.listToSet generatorsList)
      (by
        intro x hx
        obtain ⟨x', hx', hxx'⟩ := hgen x hx
        exact ⟨x', by simpa [hS] using hx', hxx'⟩) g (by simpa [hS] using hg)
  refine ⟨g', by simpa [hS] using hg', ?_⟩
  simpa [conjByGate_val, NQubitPauliGroupElement.gate_val] using congrArg Subtype.val hgg'

/-- Transversal Hadamard is a logical gate for the Steane code. -/
theorem transversalH_Steane7_isLogicalGate :
    IsLogicalGate transversalH_Steane7 stabilizerGroup := by
  have hS :
      stabilizerGroup.toSubgroup =
        Subgroup.closure (NQubitPauliGroupElement.listToSet generatorsList) := by
    simp [stabilizerGroup_toSubgroup_eq, subgroup, listToSet_generatorsList]
  refine isLogicalGate_of_generator_set_conjugation transversalH_Steane7 stabilizerGroup
    (NQubitPauliGroupElement.listToSet generatorsList) hS ?_
  intro x hx
  have hxList : x ∈ generatorsList := by
    simpa [NQubitPauliGroupElement.listToSet] using hx
  refine ⟨swapXZ_element x, ?_, ?_⟩
  · simpa [stabilizerGroup_toSubgroup_eq] using transversalSwapXZ_mem_subgroup x hxList
  · apply Subtype.ext
    simpa [conjByGate_val, NQubitPauliGroupElement.gate_val] using
      transversalH_conjugates_element x (generators_no_Y x hxList)

/-- `swapXZ_element` sends Steane logical X to logical Z. -/
private lemma swapXZ_element_logicalX_eq_logicalZ :
    swapXZ_element logicalX = logicalZ := by
  ext i <;> simp [swapXZ_element, logicalX, logicalZ, NQubitPauliOperator.transversalSwapXZ,
    NQubitPauliOperator.X, NQubitPauliOperator.Z, PauliOperator.swapXZ]

/-- `swapXZ_element` sends Steane logical Z to logical X. -/
private lemma swapXZ_element_logicalZ_eq_logicalX :
    swapXZ_element logicalZ = logicalX := by
  ext i <;> simp [swapXZ_element, logicalX, logicalZ, NQubitPauliOperator.transversalSwapXZ,
    NQubitPauliOperator.X, NQubitPauliOperator.Z, PauliOperator.swapXZ]

/-- Steane logical X has no Y components. -/
private lemma logicalX_no_Y : ∀ i, logicalX.operators i ≠ PauliOperator.Y := by
  simp [logicalX, NQubitPauliOperator.X]

/-- Steane logical Z has no Y components. -/
private lemma logicalZ_no_Y : ∀ i, logicalZ.operators i ≠ PauliOperator.Y := by
  simp [logicalZ, NQubitPauliOperator.Z]

/-- Transversal Hadamard acts as logical Hadamard on the canonical Steane
logical pair. -/
theorem transversalH_Steane7_isLogicalHadamard :
    LogicalQubitOps.IsLogicalHadamard
      ⟨logicalX, logicalZ, logicalX_mem_centralizer, logicalZ_mem_centralizer,
        logicalX_anticommutes_logicalZ⟩
      transversalH_Steane7 := by
  refine ⟨transversalH_Steane7_isLogicalGate, ?_, ?_⟩
  · apply Subtype.ext
    simpa [conjByGate_val, NQubitPauliGroupElement.gate_val,
      swapXZ_element_logicalX_eq_logicalZ] using
      transversalH_conjugates_element logicalX logicalX_no_Y
  · apply Subtype.ext
    simpa [conjByGate_val, NQubitPauliGroupElement.gate_val,
      swapXZ_element_logicalZ_eq_logicalX] using
      transversalH_conjugates_element logicalZ logicalZ_no_Y

/-!
## Transversal S as a logical gate

Conjugation is U P U† (adjoint on the right). S† on each qubit fixes Z and sends
X to Y. Z-generators are fixed; X-generators go to X*Z (in the stabilizer).
-/

lemma transversalS_conjugates_Z_generator (g : NQubitPauliGroupElement 7) (hg : g ∈ ZGenerators) :
    transversalS_Steane7.val * g.toMatrix * star transversalS_Steane7.val = g.toMatrix := by
  have hZ : ∀ i, g.operators i = .Z ∨ g.operators i = .I := by
    rcases hg with rfl | rfl | rfl <;> intro i <;> fin_cases i <;> decide
  have hphase : g.phasePower = 0 := by
    rcases hg with rfl | rfl | rfl <;> decide
  simpa [transversalS_Steane7, NQubitPauliGroupElement.toMatrix,
         PauliGroupElement.phasePowerToComplex, hphase] using
    uniformTransversalGateMatrix_inv_S_conj_Z_op 7 g.operators hZ

/-- Gate-level version: transversal `inv_S` fixes each Steane Z-generator. -/
lemma transversalS_conjugates_Z_generator_gate
    (g : NQubitPauliGroupElement 7) (hg : g ∈ ZGenerators) :
    conjByGate transversalS_Steane7 g.gate = g.gate := by
  apply Subtype.ext
  simpa [conjByGate_val, NQubitPauliGroupElement.gate_val] using
    transversalS_conjugates_Z_generator g hg

/-- Generic gate-level helper: transversal `inv_S` conjugation for a phase-0 X/I
generator with X-support of size 4 sends `g` to `h` whenever `invSConjXIImage`
matches `h.operators` and `h.phasePower = 0`. Specializations follow for each
Steane X-generator. -/
private lemma transversalS_conjugates_XI_phase0_card4_gate
    {g h : NQubitPauliGroupElement 7}
    (hphase_g : g.phasePower = 0) (hphase_h : h.phasePower = 0)
    (hXI : ∀ i, g.operators i = .X ∨ g.operators i = .I)
    (hcard : (xSupport g.operators).card = 4)
    (himage : invSConjXIImage g.operators = h.operators) :
    conjByGate transversalS_Steane7 g.gate = h.gate := by
  apply Subtype.ext
  have hscalar : invSConjXIScalar g.operators = 1 := by
    rw [invSConjXIScalar_eq_negOne_pow_xSupportCard, hcard]; norm_num
  have hconj := uniformTransversalGateMatrix_inv_S_conj_element_XI_phase0 7 g hphase_g hXI
  simpa [conjByGate_val, transversalS_Steane7, NQubitPauliGroupElement.gate_val,
    himage, hscalar, NQubitPauliGroupElement.toMatrix, hphase_h, hphase_g,
    PauliGroupElement.phasePowerToComplex] using hconj

/-- Gate-level `inv_S` conjugation for `X1`: `X1 ↦ X1*Z1`. -/
lemma transversalS_conjugates_X1_gate :
    conjByGate transversalS_Steane7 X1.gate = (X1 * Z1).gate :=
  transversalS_conjugates_XI_phase0_card4_gate rfl (by decide)
    (fun i => by fin_cases i <;>
      simp [X1, NQubitPauliOperator.set, NQubitPauliOperator.identity])
    (by unfold xSupport X1; decide)
    (by ext i; fin_cases i <;>
      simp [invSConjXIImage, X1, Z1, NQubitPauliOperator.set, NQubitPauliOperator.identity,
        NQubitPauliGroupElement.mul, NQubitPauliGroupElement.mulOp, PauliOperator.mulOp])

/-- Gate-level `inv_S` conjugation for `X2`: `X2 ↦ X2*Z2`. -/
lemma transversalS_conjugates_X2_gate :
    conjByGate transversalS_Steane7 X2.gate = (X2 * Z2).gate :=
  transversalS_conjugates_XI_phase0_card4_gate rfl (by decide)
    (fun i => by fin_cases i <;>
      simp [X2, NQubitPauliOperator.set, NQubitPauliOperator.identity])
    (by unfold xSupport X2; decide)
    (by ext i; fin_cases i <;>
      simp [invSConjXIImage, X2, Z2, NQubitPauliOperator.set, NQubitPauliOperator.identity,
        NQubitPauliGroupElement.mul, NQubitPauliGroupElement.mulOp, PauliOperator.mulOp])

/-- Gate-level `inv_S` conjugation for `X3`: `X3 ↦ X3*Z3`. -/
lemma transversalS_conjugates_X3_gate :
    conjByGate transversalS_Steane7 X3.gate = (X3 * Z3).gate :=
  transversalS_conjugates_XI_phase0_card4_gate rfl (by decide)
    (fun i => by fin_cases i <;>
      simp [X3, NQubitPauliOperator.set, NQubitPauliOperator.identity])
    (by unfold xSupport X3; decide)
    (by ext i; fin_cases i <;>
      simp [invSConjXIImage, X3, Z3, NQubitPauliOperator.set, NQubitPauliOperator.identity,
        NQubitPauliGroupElement.mul, NQubitPauliGroupElement.mulOp, PauliOperator.mulOp])

/-- Transversal S conjugates X1 to X1*Z1 (matrix bridge). -/
lemma transversalS_conjugates_X1 :
    transversalS_Steane7.val * X1.toMatrix * star transversalS_Steane7.val =
      (X1 * Z1).toMatrix := by
  simpa [conjByGate_val, NQubitPauliGroupElement.gate_val] using
    congrArg Subtype.val transversalS_conjugates_X1_gate

/-- Transversal S conjugates X2 to X2*Z2 (matrix bridge). -/
lemma transversalS_conjugates_X2 :
    transversalS_Steane7.val * X2.toMatrix * star transversalS_Steane7.val =
      (X2 * Z2).toMatrix := by
  simpa [conjByGate_val, NQubitPauliGroupElement.gate_val] using
    congrArg Subtype.val transversalS_conjugates_X2_gate

/-- Transversal S conjugates X3 to X3*Z3 (matrix bridge). -/
lemma transversalS_conjugates_X3 :
    transversalS_Steane7.val * X3.toMatrix * star transversalS_Steane7.val =
      (X3 * Z3).toMatrix := by
  simpa [conjByGate_val, NQubitPauliGroupElement.gate_val] using
    congrArg Subtype.val transversalS_conjugates_X3_gate

/-- Transversal S is a logical gate for the Steane code. -/
theorem transversalS_Steane7_isLogicalGate :
    IsLogicalGate transversalS_Steane7 stabilizerGroup := by
  have hS :
      stabilizerGroup.toSubgroup =
        Subgroup.closure (NQubitPauliGroupElement.listToSet generatorsList) := by
    simp [stabilizerGroup_toSubgroup_eq, subgroup, listToSet_generatorsList]
  have hmemGen : ∀ x ∈ generatorsList, x ∈ stabilizerGroup.toSubgroup := fun x hx =>
    hS ▸ Subgroup.subset_closure (by simpa [NQubitPauliGroupElement.listToSet] using hx)
  refine isLogicalGate_of_generator_set_conjugation transversalS_Steane7 stabilizerGroup
    (NQubitPauliGroupElement.listToSet generatorsList) hS ?_
  intro x hx
  have hxList : x ∈ generatorsList := by
    simpa [NQubitPauliGroupElement.listToSet] using hx
  have hxCases : x = Z1 ∨ x = Z2 ∨ x = Z3 ∨ x = X1 ∨ x = X2 ∨ x = X3 := by
    unfold generatorsList at hxList
    aesop
  rcases hxCases with (rfl | rfl | rfl | rfl | rfl | rfl)
  · refine ⟨Z1, hmemGen Z1 (by simp [generatorsList]), ?_⟩
    simpa [transversalS_Steane7] using
      transversalS_conjugates_Z_generator_gate Z1 (by simp [ZGenerators])
  · refine ⟨Z2, hmemGen Z2 (by simp [generatorsList]), ?_⟩
    simpa [transversalS_Steane7] using
      transversalS_conjugates_Z_generator_gate Z2 (by simp [ZGenerators])
  · refine ⟨Z3, hmemGen Z3 (by simp [generatorsList]), ?_⟩
    simpa [transversalS_Steane7] using
      transversalS_conjugates_Z_generator_gate Z3 (by simp [ZGenerators])
  · refine ⟨X1 * Z1, ?_, ?_⟩
    · exact Subgroup.mul_mem _ (hmemGen X1 (by simp [generatorsList]))
        (hmemGen Z1 (by simp [generatorsList]))
    · simpa [transversalS_Steane7] using transversalS_conjugates_X1_gate
  · refine ⟨X2 * Z2, ?_, ?_⟩
    · exact Subgroup.mul_mem _ (hmemGen X2 (by simp [generatorsList]))
        (hmemGen Z2 (by simp [generatorsList]))
    · simpa [transversalS_Steane7] using transversalS_conjugates_X2_gate
  · refine ⟨X3 * Z3, ?_, ?_⟩
    · exact Subgroup.mul_mem _ (hmemGen X3 (by simp [generatorsList]))
        (hmemGen Z3 (by simp [generatorsList]))
    · simpa [transversalS_Steane7] using transversalS_conjugates_X3_gate

/-- Transversal `S†` (implemented as `inv_S` on each qubit) acts as logical
phase `S` on the canonical Steane logical pair under the convention
`Ȳ := i X̄ Z̄`. -/
theorem transversalS_Steane7_isLogicalS :
    LogicalQubitOps.IsLogicalS
      ⟨logicalX, logicalZ, logicalX_mem_centralizer, logicalZ_mem_centralizer,
        logicalX_anticommutes_logicalZ⟩
      transversalS_Steane7 := by
  refine ⟨transversalS_Steane7_isLogicalGate, ?_, ?_⟩
  · apply Subtype.ext
    change (uniformTransversalGateMatrix 7 inv_S) * logicalZ.toMatrix *
      star (uniformTransversalGateMatrix 7 inv_S) = logicalZ.toMatrix
    simpa [conjByGate_val, NQubitPauliGroupElement.gate_val,
      logicalZ, NQubitPauliGroupElement.toMatrix, PauliGroupElement.phasePowerToComplex] using
      (uniformTransversalGateMatrix_inv_S_conj_Z_op 7 (NQubitPauliOperator.Z 7)
        (fun _ => Or.inl rfl))
  · apply Subtype.ext
    have hXY : (uniformTransversalGateMatrix 7 inv_S) * logicalX.toMatrix *
        star (uniformTransversalGateMatrix 7 inv_S) = logicalY.toMatrix := by
      have hX :
          logicalX.toMatrix = (NQubitPauliOperator.X 7).toMatrix := by
        simp [logicalX, NQubitPauliGroupElement.toMatrix, PauliGroupElement.phasePowerToComplex]
      rw [hX, uniformTransversalGateMatrix_inv_S_conj_allX]
      have hpow : ((-1 : ℂ) ^ 7) = -1 := by norm_num
      simp [logicalY_eq_phase2_allY, NQubitPauliGroupElement.toMatrix,
        PauliGroupElement.phasePowerToComplex, hpow]
    simpa [conjByGate_val, NQubitPauliGroupElement.gate_val] using hXY


end Steane7
end StabilizerGroup
end Quantum
