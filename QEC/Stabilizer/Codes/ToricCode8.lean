import Mathlib.Tactic
import QEC.Stabilizer.Core.StabilizerGroup
import QEC.Stabilizer.Core.SubgroupLemmas
import QEC.Stabilizer.Core.CSSNoNegI
import QEC.Stabilizer.Core.Centralizer
import QEC.Stabilizer.Core.CSSCommutationLemmas
import QEC.Stabilizer.Core.CentralizerLemmas
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
# [8, 2, 2] toric code

Formalization of the [8, 2, 2] toric code: 8 physical qubits, 2 logical qubits, distance 2.
Includes 8 standard generators (4 vertex Z-type, 4 face X-type), an independent subset of 6
generators, logical operators for both logical qubits, and proofs of commutation, anticommutation,
and CSS structure. Constructs a `StabilizerCode 8 2` instance.

Convention: face/plaquette checks are X-type and vertex/star checks are Z-type,
matching the convention in `distance_proof.md`.
-/

namespace Quantum
open scoped BigOperators

namespace StabilizerGroup
namespace ToricCode8

/-- Vertex operator A00: Z on qubits {0, 1, 4, 6}. -/
def A00 : NQubitPauliGroupElement 8 :=
  ⟨0, ((((NQubitPauliOperator.identity 8).set 0 PauliOperator.Z).set 1 PauliOperator.Z).set 4
    PauliOperator.Z).set 6 PauliOperator.Z⟩

/-- Vertex operator A01: Z on qubits {0, 1, 5, 7}. -/
def A01 : NQubitPauliGroupElement 8 :=
  ⟨0, ((((NQubitPauliOperator.identity 8).set 0 PauliOperator.Z).set 1 PauliOperator.Z).set 5
    PauliOperator.Z).set 7 PauliOperator.Z⟩

/-- Vertex operator A10: Z on qubits {2, 3, 4, 6}. -/
def A10 : NQubitPauliGroupElement 8 :=
  ⟨0, ((((NQubitPauliOperator.identity 8).set 2 PauliOperator.Z).set 3 PauliOperator.Z).set 4
    PauliOperator.Z).set 6 PauliOperator.Z⟩

/-- Vertex operator A11: Z on qubits {2, 3, 5, 7}. -/
def A11 : NQubitPauliGroupElement 8 :=
  ⟨0, ((((NQubitPauliOperator.identity 8).set 2 PauliOperator.Z).set 3 PauliOperator.Z).set 5
    PauliOperator.Z).set 7 PauliOperator.Z⟩

/-- Face operator B00: X on qubits {0, 2, 4, 5}. -/
def B00 : NQubitPauliGroupElement 8 :=
  ⟨0, ((((NQubitPauliOperator.identity 8).set 0 PauliOperator.X).set 2 PauliOperator.X).set 4
    PauliOperator.X).set 5 PauliOperator.X⟩

/-- Face operator B01: X on qubits {1, 3, 4, 5}. -/
def B01 : NQubitPauliGroupElement 8 :=
  ⟨0, ((((NQubitPauliOperator.identity 8).set 1 PauliOperator.X).set 3 PauliOperator.X).set 4
    PauliOperator.X).set 5 PauliOperator.X⟩

/-- Face operator B10: X on qubits {0, 2, 6, 7}. -/
def B10 : NQubitPauliGroupElement 8 :=
  ⟨0, ((((NQubitPauliOperator.identity 8).set 0 PauliOperator.X).set 2 PauliOperator.X).set 6
    PauliOperator.X).set 7 PauliOperator.X⟩

/-- Face operator B11: X on qubits {1, 3, 6, 7}. -/
def B11 : NQubitPauliGroupElement 8 :=
  ⟨0, ((((NQubitPauliOperator.identity 8).set 1 PauliOperator.X).set 3 PauliOperator.X).set 6
    PauliOperator.X).set 7 PauliOperator.X⟩

/-- The list of all 8 generators (4 X-face, 4 Z-vertex). -/
def generatorsList : List (NQubitPauliGroupElement 8) :=
  [B00, B01, B10, B11, A00, A01, A10, A11]

/-- The set of Z-type (vertex) generators. -/
def ZGenerators : Set (NQubitPauliGroupElement 8) :=
  {A00, A01, A10, A11}

/-- The set of X-type (face) generators. -/
def XGenerators : Set (NQubitPauliGroupElement 8) :=
  {B00, B01, B10, B11}

/-- The full generator set. -/
def generators : Set (NQubitPauliGroupElement 8) :=
  ZGenerators ∪ XGenerators

/-- The set of elements in the generator list equals the generator set. -/
lemma listToSet_generatorsList :
  NQubitPauliGroupElement.listToSet generatorsList = generators := by
  simp [NQubitPauliGroupElement.listToSet, generatorsList, generators, ZGenerators, XGenerators]
  aesop

/-- Any two Z-type elements commute. -/
private lemma ZType_commutes {g h : NQubitPauliGroupElement 8}
    (hg : NQubitPauliGroupElement.IsZTypeElement g)
    (hh : NQubitPauliGroupElement.IsZTypeElement h) :
    g * h = h * g := by
  exact CSSCommutationLemmas.ZType_commutes hg hh

/-- Any two X-type elements commute. -/
private lemma XType_commutes {g h : NQubitPauliGroupElement 8}
    (hg : NQubitPauliGroupElement.IsXTypeElement g)
    (hh : NQubitPauliGroupElement.IsXTypeElement h) :
    g * h = h * g := by
  exact CSSCommutationLemmas.XType_commutes hg hh

/-- All Z-generators are Z-type elements. -/
lemma ZGenerators_are_ZType :
    ∀ g, g ∈ ZGenerators → NQubitPauliGroupElement.IsZTypeElement g := by
  unfold ZGenerators; simp +decide [NQubitPauliGroupElement.IsZTypeElement]
  unfold NQubitPauliOperator.IsZType; simp +decide [A00, A01, A10, A11, PauliOperator.IsZType]

/-- All X-generators are X-type elements. -/
lemma XGenerators_are_XType :
    ∀ g, g ∈ XGenerators → NQubitPauliGroupElement.IsXTypeElement g := by
  unfold XGenerators; simp +decide [NQubitPauliGroupElement.IsXTypeElement]
  unfold NQubitPauliOperator.IsXType; simp +decide [B00, B01, B10, B11, PauliOperator.IsXType]

/-- All Z-generators commute with each other. -/
lemma ZGenerators_commute :
    ∀ z1 ∈ ZGenerators, ∀ z2 ∈ ZGenerators, z1 * z2 = z2 * z1 := by
  exact fun z1 hz1 z2 hz2 =>
    ZType_commutes (ZGenerators_are_ZType z1 hz1) (ZGenerators_are_ZType z2 hz2)

/-- All X-generators commute with each other. -/
lemma XGenerators_commute :
    ∀ x1 ∈ XGenerators, ∀ x2 ∈ XGenerators, x1 * x2 = x2 * x1 := by
  intros x1 hx1 x2 hx2
  have hx1_type := XGenerators_are_XType x1 hx1
  have hx2_type := XGenerators_are_XType x2 hx2
  exact XType_commutes hx1_type hx2_type

/-- Every Z-generator commutes with every X-generator. -/
lemma ZGenerators_commute_XGenerators :
    ∀ z ∈ ZGenerators, ∀ x ∈ XGenerators, z * x = x * z := by
  intro z hz x hx
  simp only [ZGenerators, XGenerators] at hz hx
  rcases hz with rfl | rfl | rfl | rfl <;> rcases hx with rfl | rfl | rfl | rfl
  all_goals simp only [NQubitPauliGroupElement.mul_eq, NQubitPauliGroupElement.mul]; ext
  all_goals first | rfl | decide +revert

/-- All generators commute. -/
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

/-- The stabilizer subgroup: closure of the 8 generators. -/
noncomputable def subgroup : Subgroup (NQubitPauliGroupElement 8) :=
  Subgroup.closure generators

/-- -I is not in the stabilizer subgroup. -/
theorem negIdentity_not_mem :
    StabilizerGroup.negIdentity 8 ∉ subgroup := by
  simpa only [subgroup, generators] using
    CSS.negIdentity_not_mem_closure_union ZGenerators XGenerators
      ZGenerators_are_ZType XGenerators_are_XType ZGenerators_commute_XGenerators

/-- Logical X₁: X on qubits {0, 1} (horizontal loop). -/
def logicalX1 : NQubitPauliGroupElement 8 :=
  ⟨0, ((NQubitPauliOperator.identity 8).set 0 PauliOperator.X).set 1 PauliOperator.X⟩

/-- Logical Z₁: Z on qubits {0, 2}. -/
def logicalZ1 : NQubitPauliGroupElement 8 :=
  ⟨0, ((NQubitPauliOperator.identity 8).set 0 PauliOperator.Z).set 2 PauliOperator.Z⟩

/-- Logical X₂: X on qubits {4, 6} (vertical loop). -/
def logicalX2 : NQubitPauliGroupElement 8 :=
  ⟨0, ((NQubitPauliOperator.identity 8).set 4 PauliOperator.X).set 6 PauliOperator.X⟩

/-- Logical Z₂: Z on qubits {4, 5}. -/
def logicalZ2 : NQubitPauliGroupElement 8 :=
  ⟨0, ((NQubitPauliOperator.identity 8).set 4 PauliOperator.Z).set 5 PauliOperator.Z⟩

/-- logicalX1 is an X-type element. -/
lemma logicalX1_is_XType :
  NQubitPauliGroupElement.IsXTypeElement logicalX1 := by
  unfold NQubitPauliGroupElement.IsXTypeElement
  simp [logicalX1]; simp +decide [NQubitPauliOperator.IsXType, PauliOperator.IsXType]

/-- logicalZ1 is a Z-type element. -/
lemma logicalZ1_is_ZType :
  NQubitPauliGroupElement.IsZTypeElement logicalZ1 := by
  unfold NQubitPauliGroupElement.IsZTypeElement
  simp +decide [NQubitPauliOperator.IsZType]
  unfold logicalZ1; simp +decide [Fin.forall_fin_succ]
  simp +decide [NQubitPauliOperator.set] at *; tauto

/-- logicalX2 is an X-type element. -/
lemma logicalX2_is_XType :
  NQubitPauliGroupElement.IsXTypeElement logicalX2 := by
  unfold NQubitPauliGroupElement.IsXTypeElement
  simp [logicalX2]; simp +decide [NQubitPauliOperator.IsXType, PauliOperator.IsXType]

/-- logicalZ2 is a Z-type element. -/
lemma logicalZ2_is_ZType :
  NQubitPauliGroupElement.IsZTypeElement logicalZ2 := by
  unfold NQubitPauliGroupElement.IsZTypeElement
  simp +decide [NQubitPauliOperator.IsZType]
  unfold logicalZ2; simp +decide [Fin.forall_fin_succ]
  simp +decide [NQubitPauliOperator.set] at *; tauto

/-- logicalX1 commutes with all Z-generators. -/
lemma logicalX1_commutes_ZGenerators :
    ∀ z ∈ ZGenerators, logicalX1 * z = z * logicalX1 := by
  rintro z (rfl | rfl | rfl | rfl)
  · simp only [NQubitPauliGroupElement.mul_eq, NQubitPauliGroupElement.mul, logicalX1, A00]
    ext <;> [rfl; decide +revert]
  · simp only [NQubitPauliGroupElement.mul_eq, NQubitPauliGroupElement.mul, logicalX1, A01]
    ext <;> [rfl; decide +revert]
  · simp only [NQubitPauliGroupElement.mul_eq, NQubitPauliGroupElement.mul, logicalX1, A10]
    ext <;> [rfl; decide +revert]
  · simp only [NQubitPauliGroupElement.mul_eq, NQubitPauliGroupElement.mul, logicalX1, A11]
    ext <;> [rfl; decide +revert]

/-- logicalX1 commutes with all X-generators. -/
lemma logicalX1_commutes_XGenerators :
    ∀ x ∈ XGenerators, logicalX1 * x = x * logicalX1 := by
  intro x hx
  have h_type := XGenerators_are_XType x hx
  exact XType_commutes logicalX1_is_XType h_type

/-- logicalX2 commutes with all Z-generators. -/
lemma logicalX2_commutes_ZGenerators :
    ∀ z ∈ ZGenerators, logicalX2 * z = z * logicalX2 := by
  rintro z (rfl | rfl | rfl | rfl)
  · simp only [NQubitPauliGroupElement.mul_eq, NQubitPauliGroupElement.mul, logicalX2, A00]
    ext <;> [rfl; decide +revert]
  · simp only [NQubitPauliGroupElement.mul_eq, NQubitPauliGroupElement.mul, logicalX2, A01]
    ext <;> [rfl; decide +revert]
  · simp only [NQubitPauliGroupElement.mul_eq, NQubitPauliGroupElement.mul, logicalX2, A10]
    ext <;> [rfl; decide +revert]
  · simp only [NQubitPauliGroupElement.mul_eq, NQubitPauliGroupElement.mul, logicalX2, A11]
    ext <;> [rfl; decide +revert]

/-- logicalX2 commutes with all X-generators. -/
lemma logicalX2_commutes_XGenerators :
    ∀ x ∈ XGenerators, logicalX2 * x = x * logicalX2 := by
  intro x hx
  have h_type := XGenerators_are_XType x hx
  exact XType_commutes logicalX2_is_XType h_type

/-- logicalZ1 commutes with all Z-generators. -/
lemma logicalZ1_commutes_ZGenerators :
    ∀ z ∈ ZGenerators, logicalZ1 * z = z * logicalZ1 := by
  intro z hz
  have h_type := ZGenerators_are_ZType z hz
  exact ZType_commutes logicalZ1_is_ZType h_type

/-- logicalZ1 commutes with all X-generators. -/
lemma logicalZ1_commutes_XGenerators :
    ∀ x ∈ XGenerators, logicalZ1 * x = x * logicalZ1 := by
  intro x hx; simp only [XGenerators] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · simp only [NQubitPauliGroupElement.mul_eq, NQubitPauliGroupElement.mul, logicalZ1, B00]
    ext <;> [rfl; decide +revert]
  · simp only [NQubitPauliGroupElement.mul_eq, NQubitPauliGroupElement.mul, logicalZ1, B01]
    ext <;> [rfl; decide +revert]
  · simp only [NQubitPauliGroupElement.mul_eq, NQubitPauliGroupElement.mul, logicalZ1, B10]
    ext <;> [rfl; decide +revert]
  · simp only [NQubitPauliGroupElement.mul_eq, NQubitPauliGroupElement.mul, logicalZ1, B11]
    ext <;> [rfl; decide +revert]

/-- logicalZ2 commutes with all Z-generators. -/
lemma logicalZ2_commutes_ZGenerators :
    ∀ z ∈ ZGenerators, logicalZ2 * z = z * logicalZ2 := by
  intro z hz
  have h_type := ZGenerators_are_ZType z hz
  exact ZType_commutes logicalZ2_is_ZType h_type

/-- logicalZ2 commutes with all X-generators. -/
lemma logicalZ2_commutes_XGenerators :
    ∀ x ∈ XGenerators, logicalZ2 * x = x * logicalZ2 := by
  intro x hx; simp only [XGenerators] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · simp only [NQubitPauliGroupElement.mul_eq, NQubitPauliGroupElement.mul, logicalZ2, B00]
    ext <;> [rfl; decide +revert]
  · simp only [NQubitPauliGroupElement.mul_eq, NQubitPauliGroupElement.mul, logicalZ2, B01]
    ext <;> [rfl; decide +revert]
  · simp only [NQubitPauliGroupElement.mul_eq, NQubitPauliGroupElement.mul, logicalZ2, B10]
    ext <;> [rfl; decide +revert]
  · simp only [NQubitPauliGroupElement.mul_eq, NQubitPauliGroupElement.mul, logicalZ2, B11]
    ext <;> [rfl; decide +revert]

/-- Logical operators for different logical qubits commute. -/
lemma logicalX1_commutes_logicalX2 :
  logicalX1 * logicalX2 = logicalX2 * logicalX1 := by
  pauli_comm_componentwise [logicalX1, logicalX2]

lemma logicalZ1_commutes_logicalZ2 :
  logicalZ1 * logicalZ2 = logicalZ2 * logicalZ1 := by
  pauli_comm_componentwise [logicalZ1, logicalZ2]

lemma logicalX1_commutes_logicalZ2 :
  logicalX1 * logicalZ2 = logicalZ2 * logicalX1 := by
  pauli_comm_componentwise [logicalX1, logicalZ2]

lemma logicalZ1_commutes_logicalX2 :
  logicalZ1 * logicalX2 = logicalX2 * logicalZ1 := by
  pauli_comm_componentwise [logicalZ1, logicalX2]

/-- Logical X and Z on the same logical qubit anticommute. -/
theorem logicalX1_anticommutes_logicalZ1 :
  NQubitPauliGroupElement.Anticommute logicalX1 logicalZ1 := by
  rw [NQubitPauliGroupElement.anticommutes_iff_mulOp_phasePower]
  simp only [logicalX1, logicalZ1, NQubitPauliGroupElement.mulOp]
  decide

theorem logicalX2_anticommutes_logicalZ2 :
  NQubitPauliGroupElement.Anticommute logicalX2 logicalZ2 := by
  rw [NQubitPauliGroupElement.anticommutes_iff_mulOp_phasePower]
  simp only [logicalX2, logicalZ2, NQubitPauliGroupElement.mulOp]
  decide

/-- Independent generating list: 6 generators (B00, B01, B10, A00, A01, A10).
    B11 and A11 are products of the first three X and first three Z respectively. -/
def generatorsList6 : List (NQubitPauliGroupElement 8) :=
  [B00, B01, B10, A00, A01, A10]

/-- B11 = B00 * B01 * B10. -/
lemma B11_eq_mul :
  B11 = B00 * B01 * B10 := by
  unfold B11 B00 B01 B10
  congr 1
  ext i; fin_cases i <;> simp +decide

/-- A11 = A00 * A01 * A10. -/
lemma A11_eq_mul :
  A11 = A00 * A01 * A10 := by
  unfold A11 A00 A01 A10
  congr 1
  ext i; fin_cases i <;> simp +decide

/-- The 6 independent generators are contained in the full generator set. -/
lemma generatorsList6_subset_generators :
  NQubitPauliGroupElement.listToSet generatorsList6 ⊆ generators := by
  intro g hg
  rw [NQubitPauliGroupElement.listToSet, generatorsList6, Set.mem_setOf,
    List.mem_cons, List.mem_cons, List.mem_cons, List.mem_cons, List.mem_cons] at hg
  rw [List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (Set.mem_insert B00 _)
  · exact Or.inr (Set.mem_insert_of_mem _ (Set.mem_insert B01 _))
  · exact Or.inr (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert B10 _)))
  · exact Or.inl (Set.mem_insert A00 _)
  · exact Or.inl (Set.mem_insert_of_mem _ (Set.mem_insert A01 _))
  · exact Or.inl (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert A10 _)))

/-- The stabilizer subgroup equals the closure of the 6 independent generators. -/
lemma subgroup_eq_closure_generatorsList6 :
  subgroup = Subgroup.closure (NQubitPauliGroupElement.listToSet generatorsList6) := by
  refine le_antisymm ?_ ?_
  · rw [subgroup, generators]
    intro g hg
    refine Subgroup.closure_induction
      (p := fun g _ => g ∈ Subgroup.closure (NQubitPauliGroupElement.listToSet generatorsList6))
      ?_ ?_ ?_ ?_ hg
    · intro s hs
      rw [Set.mem_union] at hs
      rcases hs with hz | hx
      · -- hz : s ∈ ZGenerators = {A00, A01, A10, A11}
        simp only [ZGenerators, Set.mem_insert_iff] at hz
        rcases hz with rfl | rfl | rfl | rfl
        · exact Subgroup.subset_closure (
            by simp [NQubitPauliGroupElement.listToSet, generatorsList6])
        · exact Subgroup.subset_closure (
            by simp [NQubitPauliGroupElement.listToSet, generatorsList6])
        · exact Subgroup.subset_closure (
            by simp [NQubitPauliGroupElement.listToSet, generatorsList6])
        · rw [A11_eq_mul]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _
            (Subgroup.subset_closure (
              by simp [NQubitPauliGroupElement.listToSet, generatorsList6]))
            (Subgroup.subset_closure (
              by simp [NQubitPauliGroupElement.listToSet, generatorsList6])))
            (Subgroup.subset_closure (
              by simp [NQubitPauliGroupElement.listToSet, generatorsList6]))
      · -- hx : s ∈ XGenerators = {B00, B01, B10, B11}
        simp only [XGenerators, Set.mem_insert_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact Subgroup.subset_closure (
            by simp [NQubitPauliGroupElement.listToSet, generatorsList6])
        · exact Subgroup.subset_closure (
            by simp [NQubitPauliGroupElement.listToSet, generatorsList6])
        · exact Subgroup.subset_closure (
            by simp [NQubitPauliGroupElement.listToSet, generatorsList6])
        · rw [B11_eq_mul]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _
            (Subgroup.subset_closure (
              by simp [NQubitPauliGroupElement.listToSet, generatorsList6]))
            (Subgroup.subset_closure (
              by simp [NQubitPauliGroupElement.listToSet, generatorsList6])))
            (Subgroup.subset_closure (
              by simp [NQubitPauliGroupElement.listToSet, generatorsList6]))
    · exact Subgroup.one_mem _
    · intro a b _ _; exact Subgroup.mul_mem _
    · intro a _; exact Subgroup.inv_mem _
  · rw [subgroup]
    apply Subgroup.closure_mono
    exact generatorsList6_subset_generators

/-- The rows of the check matrix for the 6 generators are linearly independent. -/
theorem rowsLinearIndependent_generatorsList6 :
  NQubitPauliGroupElement.rowsLinearIndependent generatorsList6 := by
  rw [NQubitPauliGroupElement.rowsLinearIndependent_iff_forall]
  decide

/-- All elements in the 6-generator list have phase 0. -/
lemma AllPhaseZero_generatorsList6 :
  NQubitPauliGroupElement.AllPhaseZero generatorsList6 := by
  rw [generatorsList6, NQubitPauliGroupElement.AllPhaseZero_cons]
  exact ⟨rfl, (NQubitPauliGroupElement.AllPhaseZero_cons _ _).mpr
    ⟨rfl, (NQubitPauliGroupElement.AllPhaseZero_cons _ _).mpr
      ⟨rfl, (NQubitPauliGroupElement.AllPhaseZero_cons _ _).mpr
        ⟨rfl, (NQubitPauliGroupElement.AllPhaseZero_cons _ _).mpr
          ⟨rfl, (NQubitPauliGroupElement.AllPhaseZero_cons _ _).mpr
            ⟨rfl, NQubitPauliGroupElement.AllPhaseZero_nil⟩⟩⟩⟩⟩⟩

/-- The 6 generators pairwise commute. -/
lemma generatorsList6_commute :
  ∀ g ∈ NQubitPauliGroupElement.listToSet generatorsList6,
  ∀ h ∈ NQubitPauliGroupElement.listToSet generatorsList6,
  g * h = h * g := by
  intro g hg h hh
  exact generators_commute g (generatorsList6_subset_generators hg) h
    (generatorsList6_subset_generators hh)

/-- -I is not in the closure of the 6 generators. -/
lemma generatorsList6_no_negIdentity :
  StabilizerGroup.negIdentity 8 ∉
    Subgroup.closure (NQubitPauliGroupElement.listToSet generatorsList6) := by
  rw [← subgroup_eq_closure_generatorsList6]
  exact negIdentity_not_mem

/-- The stabilizer group bundled with its properties (from the 6 independent generators). -/
noncomputable def stabilizerGroup : StabilizerGroup 8 :=
  StabilizerGroup.mkStabilizerFromGenerators 8
    generatorsList6
    generatorsList6_commute
    generatorsList6_no_negIdentity

/-- The stabilizer group's subgroup equals the closure of the full 8 generators. -/
lemma stabilizerGroup_toSubgroup_eq : stabilizerGroup.toSubgroup = subgroup := by
  simp only [stabilizerGroup, StabilizerGroup.mkStabilizerFromGenerators]
  rw [subgroup_eq_closure_generatorsList6]

/-- logicalX1 is in the centralizer of the stabilizer group. -/
lemma logicalX1_mem_centralizer :
  logicalX1 ∈ StabilizerGroup.centralizer stabilizerGroup := by
  exact StabilizerGroup.CentralizerLemmas.mem_centralizer_of_commutes_genSet
    logicalX1 stabilizerGroup generators stabilizerGroup_toSubgroup_eq
    (by
      intro s hs
      simp only [generators] at hs
      rcases hs with (hz | hx)
      · exact (logicalX1_commutes_ZGenerators s hz).symm
      · exact (logicalX1_commutes_XGenerators s hx).symm)

/-- logicalZ1 is in the centralizer of the stabilizer group. -/
lemma logicalZ1_mem_centralizer :
  logicalZ1 ∈ StabilizerGroup.centralizer stabilizerGroup := by
  exact StabilizerGroup.CentralizerLemmas.mem_centralizer_of_commutes_genSet
    logicalZ1 stabilizerGroup generators stabilizerGroup_toSubgroup_eq
    (by
      intro s hs
      simp only [generators] at hs
      rcases hs with (hz | hx)
      · exact (logicalZ1_commutes_ZGenerators s hz).symm
      · exact (logicalZ1_commutes_XGenerators s hx).symm)

/-- logicalX2 is in the centralizer of the stabilizer group. -/
lemma logicalX2_mem_centralizer :
  logicalX2 ∈ StabilizerGroup.centralizer stabilizerGroup := by
  exact StabilizerGroup.CentralizerLemmas.mem_centralizer_of_commutes_genSet
    logicalX2 stabilizerGroup generators stabilizerGroup_toSubgroup_eq
    (by
      intro s hs
      simp only [generators] at hs
      rcases hs with (hz | hx)
      · exact (logicalX2_commutes_ZGenerators s hz).symm
      · exact (logicalX2_commutes_XGenerators s hx).symm)

/-- logicalZ2 is in the centralizer of the stabilizer group. -/
lemma logicalZ2_mem_centralizer :
  logicalZ2 ∈ StabilizerGroup.centralizer stabilizerGroup := by
  exact StabilizerGroup.CentralizerLemmas.mem_centralizer_of_commutes_genSet
    logicalZ2 stabilizerGroup generators stabilizerGroup_toSubgroup_eq
    (by
      intro s hs
      simp only [generators] at hs
      rcases hs with (hz | hx)
      · exact (logicalZ2_commutes_ZGenerators s hz).symm
      · exact (logicalZ2_commutes_XGenerators s hx).symm)

/-- The 6-generator list forms an independent generating set. -/
theorem GeneratorsIndependent_generatorsList6 :
  StabilizerGroup.GeneratorsIndependent 8 generatorsList6 := by
  apply StabilizerGroup.GeneratorsIndependent_of_rowsLinearIndependent
  exact rowsLinearIndependent_generatorsList6

/-- The logical operators packaged for the stabilizer code. -/
noncomputable def logicalOpsToricCode8 :
  Fin 2 → StabilizerGroup.LogicalQubitOps 8 stabilizerGroup :=
  fun i => match i with
  | 0 => {
    xOp := logicalX1
    zOp := logicalZ1
    x_mem_centralizer := logicalX1_mem_centralizer
    z_mem_centralizer := logicalZ1_mem_centralizer
    anticommute := logicalX1_anticommutes_logicalZ1
  }
  | 1 => {
    xOp := logicalX2
    zOp := logicalZ2
    x_mem_centralizer := logicalX2_mem_centralizer
    z_mem_centralizer := logicalZ2_mem_centralizer
    anticommute := logicalX2_anticommutes_logicalZ2
  }

/-- Logical operators for qubits 0 and 1 commute (concrete case ℓ=0, ℓ'=1). -/
lemma logical_commute_cross_01 :
  (logicalOpsToricCode8 0).xOp * (logicalOpsToricCode8 1).xOp =
    (logicalOpsToricCode8 1).xOp * (logicalOpsToricCode8 0).xOp ∧
  (logicalOpsToricCode8 0).xOp * (logicalOpsToricCode8 1).zOp =
    (logicalOpsToricCode8 1).zOp * (logicalOpsToricCode8 0).xOp ∧
  (logicalOpsToricCode8 0).zOp * (logicalOpsToricCode8 1).xOp =
    (logicalOpsToricCode8 1).xOp * (logicalOpsToricCode8 0).zOp ∧
  (logicalOpsToricCode8 0).zOp * (logicalOpsToricCode8 1).zOp =
    (logicalOpsToricCode8 1).zOp * (logicalOpsToricCode8 0).zOp := by
  simp only [logicalOpsToricCode8]
  exact ⟨logicalX1_commutes_logicalX2, logicalX1_commutes_logicalZ2,
    logicalZ1_commutes_logicalX2, logicalZ1_commutes_logicalZ2⟩

/-- Logical operators for qubits 1 and 0 commute (concrete case ℓ=1, ℓ'=0). -/
lemma logical_commute_cross_10 :
  (logicalOpsToricCode8 1).xOp * (logicalOpsToricCode8 0).xOp =
    (logicalOpsToricCode8 0).xOp * (logicalOpsToricCode8 1).xOp ∧
  (logicalOpsToricCode8 1).xOp * (logicalOpsToricCode8 0).zOp =
    (logicalOpsToricCode8 0).zOp * (logicalOpsToricCode8 1).xOp ∧
  (logicalOpsToricCode8 1).zOp * (logicalOpsToricCode8 0).xOp =
    (logicalOpsToricCode8 0).xOp * (logicalOpsToricCode8 1).zOp ∧
  (logicalOpsToricCode8 1).zOp * (logicalOpsToricCode8 0).zOp =
    (logicalOpsToricCode8 0).zOp * (logicalOpsToricCode8 1).zOp := by
  simp only [logicalOpsToricCode8]
  exact ⟨Eq.symm logicalX1_commutes_logicalX2, Eq.symm logicalZ1_commutes_logicalX2,
    Eq.symm logicalX1_commutes_logicalZ2, Eq.symm logicalZ1_commutes_logicalZ2⟩

/-- Logical operators for distinct logical qubits commute. -/
lemma logical_commute_cross_lemma (ℓ ℓ' : Fin 2) (h : ℓ ≠ ℓ') :
  (logicalOpsToricCode8 ℓ).xOp * (logicalOpsToricCode8 ℓ').xOp =
    (logicalOpsToricCode8 ℓ').xOp * (logicalOpsToricCode8 ℓ).xOp ∧
  (logicalOpsToricCode8 ℓ).xOp * (logicalOpsToricCode8 ℓ').zOp =
    (logicalOpsToricCode8 ℓ').zOp * (logicalOpsToricCode8 ℓ).xOp ∧
  (logicalOpsToricCode8 ℓ).zOp * (logicalOpsToricCode8 ℓ').xOp =
    (logicalOpsToricCode8 ℓ').xOp * (logicalOpsToricCode8 ℓ).zOp ∧
  (logicalOpsToricCode8 ℓ).zOp * (logicalOpsToricCode8 ℓ').zOp =
    (logicalOpsToricCode8 ℓ').zOp * (logicalOpsToricCode8 ℓ).zOp := by
  have h01 : (ℓ = 0 ∧ ℓ' = 1) ∨ (ℓ = 1 ∧ ℓ' = 0) := by
    fin_cases ℓ <;> fin_cases ℓ' <;> first
      | exact (h rfl).elim
      | exact Or.inl ⟨rfl, rfl⟩
      | exact Or.inr ⟨rfl, rfl⟩
  rcases h01 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact logical_commute_cross_01
  · exact logical_commute_cross_10

/-- The [8, 2, 2] toric code as a StabilizerCode [[8, 2]]. -/
noncomputable def stabilizerCode : StabilizerGroup.StabilizerCode 8 2 where
  hk := by decide
  generatorsList := generatorsList6
  generators_length := by rfl
  generators_phaseZero := AllPhaseZero_generatorsList6
  generators_independent := GeneratorsIndependent_generatorsList6
  generators_commute := generatorsList6_commute
  closure_no_neg_identity := generatorsList6_no_negIdentity
  logicalOps := logicalOpsToricCode8
  logical_commute_cross := logical_commute_cross_lemma

end ToricCode8
end StabilizerGroup
end Quantum
