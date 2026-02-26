import Mathlib.Tactic
import QEC.Stabilizer.Core.StabilizerGroup
import QEC.Stabilizer.Core.SubgroupLemmas
import QEC.Stabilizer.Core.CSSNoNegI
import QEC.Stabilizer.Core.Centralizer
import QEC.Stabilizer.PauliGroup.Commutation
import QEC.Stabilizer.PauliGroup.CommutationTactics
import QEC.Stabilizer.BinarySymplectic.Core
import QEC.Stabilizer.BinarySymplectic.CheckMatrix
import QEC.Stabilizer.BinarySymplectic.CheckMatrixDecidable
import QEC.Stabilizer.BinarySymplectic.SymplecticSpan
import QEC.Stabilizer.Core.StabilizerCode
import QEC.Stabilizer.BinarySymplectic.IndependentEquiv
import QEC.Stabilizer.BinarySymplectic.SymplecticInner
import QEC.Stabilizer.PauliGroup.NQubitOperator

/-!
# Rotated planar surface code with distance d = 3 ([[9, 1, 3]])

Formalization of the rotated planar surface code: 9 physical qubits, 1 logical qubit, distance 3.
Includes Z- and X-type stabilizer generators, logical operators, and proofs of commutation,
independence, and CSS structure. Constructs a `StabilizerCode 9 1` instance.
-/

namespace Quantum
open scoped BigOperators

namespace StabilizerGroup
namespace RotatedSurfaceCode3

/-- Z-check on face A: Z on qubits {0, 1, 3, 4}. -/
def Z0 : Quantum.NQubitPauliGroupElement 9 :=
  ⟨0, ((((NQubitPauliOperator.identity 9).set 0 PauliOperator.Z).set 1 PauliOperator.Z).set 3
    PauliOperator.Z).set 4 PauliOperator.Z⟩

/-
Z-check on face D: Z on qubits {4, 5, 7, 8}.
-/
def Z1 : Quantum.NQubitPauliGroupElement 9 :=
  ⟨0, ((((NQubitPauliOperator.identity 9).set 4 PauliOperator.Z).set 5 PauliOperator.Z).set 7
    PauliOperator.Z).set 8 PauliOperator.Z⟩

/-
Z-check on left boundary: Z on qubits {0, 3}.
-/
def Z2 : Quantum.NQubitPauliGroupElement 9 :=
  ⟨0, ((NQubitPauliOperator.identity 9).set 0 PauliOperator.Z).set 3 PauliOperator.Z⟩

/-
Z-check on right boundary: Z on qubits {2, 5}.
-/
def Z3 : Quantum.NQubitPauliGroupElement 9 :=
  ⟨0, ((NQubitPauliOperator.identity 9).set 2 PauliOperator.Z).set 5 PauliOperator.Z⟩

/-
X-check on face B: X on qubits {1, 2, 4, 5}.
-/
def X0 : Quantum.NQubitPauliGroupElement 9 :=
  ⟨0, ((((NQubitPauliOperator.identity 9).set 1 PauliOperator.X).set 2 PauliOperator.X).set 4
    PauliOperator.X).set 5 PauliOperator.X⟩

/-
X-check on face C: X on qubits {3, 4, 6, 7}.
-/
def X1 : Quantum.NQubitPauliGroupElement 9 :=
  ⟨0, ((((NQubitPauliOperator.identity 9).set 3 PauliOperator.X).set 4 PauliOperator.X).set 6
    PauliOperator.X).set 7 PauliOperator.X⟩

/-
X-check on top boundary: X on qubits {0, 1}.
-/
def X2 : Quantum.NQubitPauliGroupElement 9 :=
  ⟨0, ((NQubitPauliOperator.identity 9).set 0 PauliOperator.X).set 1 PauliOperator.X⟩

/-
X-check on bottom boundary: X on qubits {7, 8}.
-/
def X3 : Quantum.NQubitPauliGroupElement 9 :=
  ⟨0, ((NQubitPauliOperator.identity 9).set 7 PauliOperator.X).set 8 PauliOperator.X⟩

/-
Any two Z-type elements commute.
-/
private lemma ZType_commutes {g h : Quantum.NQubitPauliGroupElement 9}
    (hg : NQubitPauliGroupElement.IsZTypeElement g)
    (hh : NQubitPauliGroupElement.IsZTypeElement h) :
    g * h = h * g := by
  apply NQubitPauliGroupElement.commutes_of_componentwise_commutes g h (fun i => by
    have h_op : ∀ i, g.operators i = .I ∨ g.operators i = .Z := by
      unfold NQubitPauliGroupElement.IsZTypeElement at hg; aesop
    have h_op' : ∀ i, h.operators i = .I ∨ h.operators i = .Z := by
      intro i; specialize hh; unfold NQubitPauliGroupElement.IsZTypeElement at hh; aesop
    cases h_op i <;> cases h_op' i <;> simp +decide [*])

/-
Any two X-type elements commute.
-/
private lemma XType_commutes {g h : Quantum.NQubitPauliGroupElement 9}
    (hg : NQubitPauliGroupElement.IsXTypeElement g)
    (hh : NQubitPauliGroupElement.IsXTypeElement h) :
    g * h = h * g := by
  apply NQubitPauliGroupElement.commutes_of_componentwise_commutes
  intro i
  have h_op : ∀ i, g.operators i = .I ∨ g.operators i = .X := by
    unfold NQubitPauliGroupElement.IsXTypeElement at hg; aesop
  have h_op' : ∀ i, h.operators i = .I ∨ h.operators i = .X := by
    intro i; specialize hh; unfold NQubitPauliGroupElement.IsXTypeElement at hh; aesop
  cases h_op i <;> cases h_op' i <;> simp +decide [*]

/-
Z-check on left boundary: Z on qubits {3, 6}.
(The original Z2 with {0, 3} anticommutes with X2 and X1.)
-/
def Z2' : Quantum.NQubitPauliGroupElement 9 :=
  ⟨0, ((NQubitPauliOperator.identity 9).set 3 PauliOperator.Z).set 6 PauliOperator.Z⟩

/-
The list of all 8 generators for the d=3 rotated surface code (using Z2' on left boundary).
-/
def generatorsList : List (Quantum.NQubitPauliGroupElement 9) :=
  [Z0,
Z1,
Z2',
Z3,
X0,
X1,
X2,
X3]

/-
The set of Z-check generators.
-/
def ZGenerators : Set (Quantum.NQubitPauliGroupElement 9) :=
  {Z0,
Z1,
Z2',
Z3}

/-
The set of X-check generators.
-/
def XGenerators : Set (Quantum.NQubitPauliGroupElement 9) :=
  {X0,
X1,
X2,
X3}

/-
The full generator set: Z-checks and X-checks.
-/
def generators : Set (Quantum.NQubitPauliGroupElement 9) :=
  ZGenerators ∪ XGenerators

/-
All Z-generators are Z-type elements.
-/
lemma ZGenerators_are_ZType :
    ∀ g, g ∈ ZGenerators → NQubitPauliGroupElement.IsZTypeElement g := by
  unfold ZGenerators; simp +decide [NQubitPauliGroupElement.IsZTypeElement]
  unfold NQubitPauliOperator.IsZType; simp +decide [Z0, Z1, Z2', Z3, PauliOperator.IsZType]

/-
All Z-generators commute with each other.
-/
lemma ZGenerators_commute :
    ∀ z1 ∈ ZGenerators, ∀ z2 ∈ ZGenerators, z1 * z2 = z2 * z1 := by
  exact fun z1 hz1 z2 hz2 =>
    ZType_commutes (ZGenerators_are_ZType z1 hz1) (ZGenerators_are_ZType z2 hz2)

/-
Every Z-generator commutes with every X-generator.
-/
lemma ZGenerators_commute_XGenerators :
    ∀ z ∈ ZGenerators, ∀ x ∈ XGenerators, z * x = x * z := by
  intro z hz x hx
  simp only [ZGenerators, XGenerators] at hz hx
  rcases hz with rfl | rfl | rfl | rfl <;> rcases hx with rfl | rfl | rfl | rfl
  all_goals simp only [NQubitPauliGroupElement.mul_eq, NQubitPauliGroupElement.mul]; ext
  all_goals first | rfl | decide +revert

/-
The set of elements in the generator list equals the generator set.
-/
lemma listToSet_generatorsList :
  NQubitPauliGroupElement.listToSet generatorsList = generators := by
  simp [NQubitPauliGroupElement.listToSet, generatorsList, generators, ZGenerators, XGenerators]
  aesop

/-
All X-generators are X-type elements.
-/
lemma XGenerators_are_XType :
    ∀ g, g ∈ XGenerators → NQubitPauliGroupElement.IsXTypeElement g := by
  unfold XGenerators
  simp +decide [NQubitPauliGroupElement.IsXTypeElement, NQubitPauliOperator.IsXType,
    PauliOperator.IsXType]

/-
The stabilizer subgroup: closure of the 8 generators.
-/
def subgroup : Subgroup (NQubitPauliGroupElement 9) :=
  Subgroup.closure generators

/-
-I is not in the stabilizer subgroup.
-/
theorem negIdentity_not_mem :
    StabilizerGroup.negIdentity 9 ∉ subgroup := by
  simpa only [subgroup, generators] using
    CSS.negIdentity_not_mem_closure_union ZGenerators XGenerators
      ZGenerators_are_ZType XGenerators_are_XType ZGenerators_commute_XGenerators

/-
Logical X: X on qubits {1, 4, 7} (vertical). Commutes with all generators.
-/
def logicalX : Quantum.NQubitPauliGroupElement 9 :=
  ⟨0, (((NQubitPauliOperator.identity 9).set 1 PauliOperator.X).set 4 PauliOperator.X).set 7
    PauliOperator.X⟩

/-
Logical Z: Z on qubits {3, 4, 5} (horizontal). Commutes with all generators.
-/
def logicalZ : Quantum.NQubitPauliGroupElement 9 :=
  ⟨0, (((NQubitPauliOperator.identity 9).set 3 PauliOperator.Z).set 4 PauliOperator.Z).set 5
    PauliOperator.Z⟩

/-
logicalX is an X-type element.
-/
lemma logicalX_is_XType :
  NQubitPauliGroupElement.IsXTypeElement logicalX := by
  unfold NQubitPauliGroupElement.IsXTypeElement
  simp [logicalX]; simp +decide [NQubitPauliOperator.IsXType, PauliOperator.IsXType]

/-
logicalZ is a Z-type element.
-/
lemma logicalZ_is_ZType :
  NQubitPauliGroupElement.IsZTypeElement logicalZ := by
  unfold NQubitPauliGroupElement.IsZTypeElement
  simp +decide [NQubitPauliOperator.IsZType]
  unfold logicalZ; simp +decide [Fin.forall_fin_succ]
  simp +decide [NQubitPauliOperator.set] at *; tauto

/-
logicalX commutes with all Z-generators.
-/
lemma logicalX_commutes_ZGenerators :
    ∀ z ∈ ZGenerators, logicalX * z = z * logicalX := by
  rintro z (rfl | rfl | rfl | rfl)
  · simp only [NQubitPauliGroupElement.mul_eq, NQubitPauliGroupElement.mul, Z0, logicalX]
    ext <;> [rfl; decide +revert]
  · simp only [NQubitPauliGroupElement.mul_eq, NQubitPauliGroupElement.mul, Z1, logicalX]
    ext <;> [rfl; decide +revert]
  · simp only [NQubitPauliGroupElement.mul_eq, NQubitPauliGroupElement.mul, Z2', logicalX]
    ext <;> [rfl; decide +revert]
  · simp only [NQubitPauliGroupElement.mul_eq, NQubitPauliGroupElement.mul, Z3, logicalX]
    ext <;> [rfl; decide +revert]

/-
logicalX commutes with all X-generators.
-/
lemma logicalX_commutes_XGenerators :
    ∀ x ∈ XGenerators, logicalX * x = x * logicalX := by
  intro x hx
  have h_type := XGenerators_are_XType x hx
  exact XType_commutes logicalX_is_XType h_type

/-
logicalZ commutes with all X-generators.
-/
lemma logicalZ_commutes_XGenerators :
    ∀ x ∈ XGenerators, logicalZ * x = x * logicalZ := by
  intro x hx; simp only [XGenerators] at hx
  rcases hx with (rfl | rfl | rfl | rfl)
  · simp only [NQubitPauliGroupElement.mul_eq, NQubitPauliGroupElement.mul, logicalZ, X0]
    ext <;> [rfl; decide +revert]
  · simp only [NQubitPauliGroupElement.mul_eq, NQubitPauliGroupElement.mul]
    ext <;> [rfl; decide +revert]
  · simp only [NQubitPauliGroupElement.mul_eq, NQubitPauliGroupElement.mul]
    ext <;> [rfl; decide +revert]
  · simp only [NQubitPauliGroupElement.mul_eq, NQubitPauliGroupElement.mul, logicalZ, X3]
    ext <;> [rfl; decide +revert]

/-
logicalZ commutes with all Z-generators.
-/
lemma logicalZ_commutes_ZGenerators :
    ∀ z ∈ ZGenerators, logicalZ * z = z * logicalZ := by
  intro z hz
  have h_type := ZGenerators_are_ZType z hz
  exact ZType_commutes logicalZ_is_ZType h_type

/-
All X-generators commute.
-/
lemma XGenerators_commute :
    ∀ x1 ∈ XGenerators, ∀ x2 ∈ XGenerators, x1 * x2 = x2 * x1 := by
  intros x1 hx1 x2 hx2
  have hx1_type := XGenerators_are_XType x1 hx1
  have hx2_type := XGenerators_are_XType x2 hx2
  exact XType_commutes hx1_type hx2_type

/-
All generators commute.
-/
theorem generators_commute :
    ∀ g ∈ generators, ∀ h ∈ generators, g * h = h * g := by
  intros g hg h hh
  simp [generators] at hg hh
  rcases hg with (hgZ | hgX) <;> rcases hh with (hhZ | hhX)
  · exact ZGenerators_commute g hgZ h hhZ
  · exact ZGenerators_commute_XGenerators g hgZ h hhX
  · rw [NQubitPauliGroupElement.commutes_symm]
    exact ZGenerators_commute_XGenerators h hhZ g hgX
  · exact XGenerators_commute g hgX h hhX

/-
All elements in the generator list have phase 0.
-/
lemma AllPhaseZero_generatorsList :
    NQubitPauliGroupElement.AllPhaseZero generatorsList := by
  exact fun g hg => by fin_cases hg <;> rfl

/-
The logical X and Z operators anticommute.
-/
theorem logicalX_anticommutes_logicalZ :
    NQubitPauliGroupElement.Anticommute logicalX logicalZ := by
  rw [NQubitPauliGroupElement.anticommutes_iff_mulOp_phasePower]
  simp only [logicalX, logicalZ, NQubitPauliGroupElement.mulOp]
  decide

/-
The rows of the check matrix for the generator list are linearly independent.
-/
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
-- decide needs many heartbeats for 2^8 coefficient vectors
theorem rowsLinearIndependent_generatorsList :
    NQubitPauliGroupElement.rowsLinearIndependent generatorsList := by
  rw [NQubitPauliGroupElement.rowsLinearIndependent_iff_forall]
  decide

/-
The generator list forms an independent generating set.
-/
theorem GeneratorsIndependent_generatorsList :
    StabilizerGroup.GeneratorsIndependent 9 generatorsList := by
  apply StabilizerGroup.GeneratorsIndependent_of_rowsLinearIndependent
  exact rowsLinearIndependent_generatorsList

/-
The stabilizer group bundled with its properties.
-/
noncomputable def stabilizerGroup : StabilizerGroup 9 :=
  StabilizerGroup.mkStabilizerFromGenerators 9
    generatorsList
    (by rw [listToSet_generatorsList]; exact generators_commute)
    (by rw [listToSet_generatorsList]; exact negIdentity_not_mem)

lemma stabilizerGroup_toSubgroup_eq : stabilizerGroup.toSubgroup = subgroup := by
  simp only [stabilizerGroup, StabilizerGroup.mkStabilizerFromGenerators, subgroup]
  rw [listToSet_generatorsList]

/-- logicalX is in the centralizer of the stabilizer group. -/
lemma logicalX_mem_centralizer :
    logicalX ∈ StabilizerGroup.centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff_closure logicalX stabilizerGroup
    generators stabilizerGroup_toSubgroup_eq]
  intro s hs
  simp only [generators] at hs
  rcases hs with (hz | hx)
  · exact (logicalX_commutes_ZGenerators s hz).symm
  · exact (logicalX_commutes_XGenerators s hx).symm

/-- logicalZ is in the centralizer of the stabilizer group. -/
lemma logicalZ_mem_centralizer :
    logicalZ ∈ StabilizerGroup.centralizer stabilizerGroup := by
  rw [StabilizerGroup.mem_centralizer_iff_closure logicalZ stabilizerGroup
    generators stabilizerGroup_toSubgroup_eq]
  intro s hs
  simp only [generators] at hs
  rcases hs with (hz | hx)
  · exact (logicalZ_commutes_ZGenerators s hz).symm
  · exact (logicalZ_commutes_XGenerators s hx).symm

/-
The logical operators packaged for the stabilizer code.
-/
noncomputable def logicalOpsRotatedSurfaceCode3 :
    Fin 1 → StabilizerGroup.LogicalQubitOps 9 stabilizerGroup :=
  fun _ => {
    xOp := logicalX
    zOp := logicalZ
    x_mem_centralizer := logicalX_mem_centralizer
    z_mem_centralizer := logicalZ_mem_centralizer
    anticommute := logicalX_anticommutes_logicalZ
  }

/-
The rotated surface code as a StabilizerCode [[9, 1]].
-/
noncomputable def stabilizerCode : StabilizerGroup.StabilizerCode 9 1 where
  hk := by decide
  generatorsList := generatorsList
  generators_length := by rfl
  generators_phaseZero := AllPhaseZero_generatorsList
  generators_independent := GeneratorsIndependent_generatorsList
  generators_commute := by
    rw [listToSet_generatorsList]
    exact generators_commute
  closure_no_neg_identity := by
    rw [listToSet_generatorsList]
    exact negIdentity_not_mem
  logicalOps := logicalOpsRotatedSurfaceCode3
  logical_commute_cross := fun ℓ ℓ' h => (h (Subsingleton.elim ℓ ℓ')).elim

end RotatedSurfaceCode3
end StabilizerGroup
end Quantum
