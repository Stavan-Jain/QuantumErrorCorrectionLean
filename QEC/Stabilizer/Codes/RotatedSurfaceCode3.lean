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
import QEC.Stabilizer.Core.CodeDistance
import QEC.Stabilizer.Core.LogicalOperators
import QEC.Stabilizer.BinarySymplectic.IndependentEquiv
import QEC.Stabilizer.BinarySymplectic.SymplecticInner
import QEC.Stabilizer.BinarySymplectic.SymplecticOrthogonal
import QEC.Stabilizer.BinarySymplectic.WeightTwoInSpan
import QEC.Stabilizer.PauliGroup.NQubitOperator

/-!
# Rotated planar surface code ([[9, 1, 3]] / Surface-17)

Formalization of the rotated planar surface code: 9 data qubits, 1 logical qubit. In the
literature (Bombin–Martin-Delgado, Error Correction Zoo, Surface-17), [[9,1,3]] denotes
**n = 9, k = 1, d = 3** (distance 3).

Qubit indices follow a canonical layout so that the standard generators (left-boundary Z on
{0,3}, top-boundary X, etc.) pairwise commute. Stabilizer group does **not** contain -I.

Includes Z- and X-type stabilizer generators, logical operators, and proofs of commutation,
independence, and CSS structure. Constructs a `StabilizerCode 9 1` instance.
-/

namespace Quantum
open scoped BigOperators

namespace StabilizerGroup
namespace RotatedSurfaceCode3

/-- Z-check on face A: Z on qubits {0, 1, 4, 6}. -/
def Z0 : Quantum.NQubitPauliGroupElement 9 :=
  ⟨0, ((((NQubitPauliOperator.identity 9).set 0 PauliOperator.Z).set 1 PauliOperator.Z).set 4
    PauliOperator.Z).set 6 PauliOperator.Z⟩

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
X-check on face C: X on qubits {0, 3, 4, 7}.
-/
def X1 : Quantum.NQubitPauliGroupElement 9 :=
  ⟨0, ((((NQubitPauliOperator.identity 9).set 0 PauliOperator.X).set 3 PauliOperator.X).set 4
    PauliOperator.X).set 7 PauliOperator.X⟩

/-
X-check on top boundary: X on qubits {1, 6}.
-/
def X2 : Quantum.NQubitPauliGroupElement 9 :=
  ⟨0, ((NQubitPauliOperator.identity 9).set 1 PauliOperator.X).set 6 PauliOperator.X⟩

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
The list of all 8 generators for the rotated surface code [[9,1,3]] (canonical layout).
-/
def generatorsList : List (Quantum.NQubitPauliGroupElement 9) :=
  [Z0,
Z1,
Z2,
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
Z2,
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
  unfold NQubitPauliOperator.IsZType; simp +decide [Z0, Z1, Z2, Z3, PauliOperator.IsZType]

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
Logical Z: Z on qubits {0, 4, 5} (horizontal). Commutes with all generators.
-/
def logicalZ : Quantum.NQubitPauliGroupElement 9 :=
  ⟨0, (((NQubitPauliOperator.identity 9).set 0 PauliOperator.Z).set 4 PauliOperator.Z).set 5
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
  · simp only [NQubitPauliGroupElement.mul_eq, NQubitPauliGroupElement.mul, Z2, logicalX]
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
set_option maxHeartbeats 1500000 in
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

lemma subgroup_eq_closure : subgroup = Subgroup.closure
(NQubitPauliGroupElement.listToSet generatorsList) := by
  simp only [subgroup, listToSet_generatorsList]

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

lemma stabilizerCode_toStabilizerGroup_eq : stabilizerCode.toStabilizerGroup =
stabilizerGroup := rfl

/-!
## Code distance [[9, 1, 3]]

The rotated surface code has distance 3: the minimum weight of a nontrivial logical operator
is 3 (witnessed by logical X and logical Z), and no weight-1 or weight-2 Pauli is a
nontrivial logical operator.
-/

open NQubitPauliGroupElement NQubitPauliOperator

/-- The weight of logical X is 3. -/
lemma logicalX_weight : weight logicalX = 3 := by decide

/-- The weight of logical Z is 3. -/
lemma logicalZ_weight : weight logicalZ = 3 := by decide

set_option maxHeartbeats 1500000 in
-- decide needs many heartbeats for the full ∀ so we use
theorem weight_1_not_centralizer :
    ∀ g : NQubitPauliGroupElement 9, NQubitPauliGroupElement.weight g = 1 →
      g ∉ centralizer stabilizerGroup := by
  intro g h_weight
  rw [StabilizerGroup.mem_centralizer_iff_closure g stabilizerGroup generators
    stabilizerGroup_toSubgroup_eq]
  intro h_comm
  have h : ∀ s ∈ generatorsList, g * s = s * g := fun s hs =>
    (h_comm s (by rw [← listToSet_generatorsList]; exact Set.mem_setOf.mpr hs)).symm
  have key : ∀ g' : NQubitPauliGroupElement 9, NQubitPauliGroupElement.weight g' = 1 →
      ¬∀ s ∈ generatorsList, g' * s = s * g' := by
    intros g' hg' h_comm';
    have h_cases : ∀ p : Fin 9 → PauliOperator, weight (⟨g'.phasePower, p⟩ :
    NQubitPauliGroupElement 9) = 1 →
    ¬(∀ s ∈ generatorsList,
    (⟨g'.phasePower, p⟩ :
    NQubitPauliGroupElement 9) * s = s * (⟨g'.phasePower, p⟩ :
    NQubitPauliGroupElement 9)) := by
      intros p hp h_comm''; (
      have h_cases : ∀ i : Fin 9, ∀ p_i : PauliOperator, p_i ≠ PauliOperator.I →
      ¬(∀ s ∈ generatorsList,
      (⟨g'.phasePower, (fun j => if j = i then p_i else PauliOperator.I)⟩
      : NQubitPauliGroupElement 9) * s =
      s * (⟨g'.phasePower, (fun j => if j = i then p_i else PauliOperator.I)⟩ :
      NQubitPauliGroupElement 9)) := by
        intros i p_i hp_i_ne_I h_comm''; simp_all +decide ;
        fin_cases i <;> simp +decide
        [ generatorsList ] at h_comm'' ⊢;
        all_goals rcases p_i with ( _ | _ | _ | _ ) <;> simp +decide
        [ NQubitPauliGroupElement.mul ] at h_comm'' hp_i_ne_I ⊢;
        all_goals simp +decide [
        Z0, Z1, Z2, Z3, X0, X1, X2, X3 ] at h_comm'' ⊢;
      obtain ⟨i, hi⟩ : ∃ i : Fin 9, p i ≠ PauliOperator.I ∧ ∀ j : Fin 9, j ≠ i →
      p j = PauliOperator.I := by
        have h_card : Finset.card (Finset.filter (fun i => p i ≠
        PauliOperator.I) Finset.univ) = 1 := by
          exact hp;
        obtain ⟨ i, hi ⟩ := Finset.card_eq_one.mp h_card;
        exact ⟨ i, by simpa using Finset.ext_iff.mp hi i, fun j hj =>
        Classical.not_not.1 fun h => hj <| by simpa [ h ] using Finset.ext_iff.mp hi j ⟩;
      apply h_cases i (p i) hi.left;
      convert h_comm'' using 3;
      · congr! 2;
        ext j; by_cases hj : j = i <;> simp +decide [ hj, hi.2 ] ;
      · congr! 2;
        ext j; by_cases hj : j = i <;> simp +decide [ hj, hi.2 ] ;);
    exact h_cases _ hg' h_comm'
  exact key g h_weight h

/-- No weight-1 Pauli is a nontrivial logical operator. -/
theorem no_weight_1_logical (g : NQubitPauliGroupElement 9)
    (hg : NQubitPauliGroupElement.weight g = 1) :
    ¬IsNontrivialLogicalOperator g stabilizerGroup := by
  intro h_nontrivial
  have h_cent := (IsNontrivialLogicalOperator_iff g stabilizerGroup).mp h_nontrivial |>.1
  exact weight_1_not_centralizer g hg h_cent

-- native_decide checks all (i,j,pi,pj) combinations: 9×8×3×3 = 648 cases,
-- each checking commutation with generators and existence of span coefficients.
set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private lemma weight_2_pairs_span_coeffs :
    ∀ (i j : Fin 9), i ≠ j → ∀ (pi pj : PauliOperator), pi ≠ .I → pj ≠ .I →
    let op : NQubitPauliOperator 9 := fun k => if k = i then pi else if k = j then pj else .I
    (∀ g ∈ generatorsList, symplecticInner op g.operators = 0) →
    ∃ (c : Fin 8 → ZMod 2),
      NQubitPauliOperator.toSymplectic op = ∑ k : Fin 8, c k • checkMatrix generatorsList k := by
  native_decide

/-- Every weight-2 operator that commutes with all generators has its symplectic vector
    in the symplectic span of the generators. -/
theorem weight_2_operators_in_span (op : NQubitPauliOperator 9)
    (h_weight : NQubitPauliOperator.weight op = 2)
    (h_comm : ∀ g ∈ generatorsList, symplecticInner op g.operators = 0) :
    NQubitPauliOperator.toSymplectic op ∈ sympSpan generatorsList :=
  NQubitPauliGroupElement.weight_2_in_span_by_enum generatorsList
    (fun i j hij pi pj hpi hpj h_comm' => by
      obtain ⟨c, hc⟩ := weight_2_pairs_span_coeffs i j hij pi pj hpi hpj h_comm'
      unfold sympSpan
      rw [hc]
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self k)))
    op h_weight h_comm

/-- If the symplectic vector of an operator is in the span of the generators, there is
    a stabilizer element with that operator part. (Used for no_weight_2_logical.) -/
lemma exists_mem_subgroup_operators_of_symp_in_span (op : NQubitPauliOperator 9)
    (h_in_span : NQubitPauliOperator.toSymplectic op ∈ sympSpan generatorsList) :
    ∃ s ∈ subgroup, s.operators = op := by
  obtain ⟨s, hs_closure, hs_eq⟩ :=
    NQubitPauliGroupElement.exists_mem_closure_of_symp_in_span generatorsList op h_in_span
  exact ⟨s, subgroup_eq_closure.symm ▸ hs_closure, hs_eq⟩

/-- No weight-2 Pauli is a nontrivial logical operator. -/
theorem no_weight_2_logical (g : NQubitPauliGroupElement 9)
    (hg : NQubitPauliGroupElement.weight g = 2) :
    ¬IsNontrivialLogicalOperator g stabilizerGroup := by
  intro h_nontrivial
  exact NQubitPauliGroupElement.no_weight_w_logical_of_centralizer_in_span generatorsList
    stabilizerGroup 2 (stabilizerGroup_toSubgroup_eq.trans subgroup_eq_closure)
    (fun op h_weight h_comm => weight_2_operators_in_span op h_weight h_comm) g hg h_nontrivial

/-- The rotated surface code has code distance 3. -/
theorem rotatedSurfaceCode3_has_distance_three : HasCodeDistance stabilizerCode 3 :=
  hasCodeDistance_of stabilizerCode 3 (by decide)
    ⟨logicalX, stabilizerCode.logicalX_nontrivial ⟨0, by decide⟩, logicalX_weight⟩
    (fun w _ hw_lt g hw => by
      have hw_val : w = 1 ∨ w = 2 := by omega
      have h_subgroup_eq :
        stabilizerCode.toStabilizerGroup.toSubgroup = stabilizerGroup.toSubgroup :=
        congr_arg StabilizerGroup.toSubgroup stabilizerCode_toStabilizerGroup_eq
      rcases hw_val with rfl | rfl
      · exact (Iff.not (IsNontrivialLogicalOperator_of_toSubgroup_eq g h_subgroup_eq)).2
          (no_weight_1_logical g hw)
      · exact (Iff.not (IsNontrivialLogicalOperator_of_toSubgroup_eq g h_subgroup_eq)).2
          (no_weight_2_logical g hw))

end RotatedSurfaceCode3
end StabilizerGroup
end Quantum
