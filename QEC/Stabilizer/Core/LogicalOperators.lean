import QEC.Foundations.Basic
import QEC.Stabilizer.Core.StabilizerGroup
import QEC.Stabilizer.Core.Centralizer
import QEC.Stabilizer.Core.LogicalOperatorCoset
import QEC.Stabilizer.Core.Codespace
import QEC.Stabilizer.Core.LogicalGates
import QEC.Stabilizer.Core.LogicalGateGroup
import QEC.Stabilizer.PauliGroup
import QEC.Stabilizer.PauliGroup.Representation
import QEC.Stabilizer.PauliGroup.NQubitElement
import QEC.Stabilizer.PauliGroup.Commutation

namespace Quantum
namespace StabilizerGroup

variable {n : ℕ}
open Matrix
open scoped BigOperators

/-!
# Logical operators

**Pauli logical operators** are Pauli group elements that preserve the codespace: when
viewed as a unitary gate via `toGate`, they map the codespace to itself (i.e. are logical gates).
We define `IsPauliLogicalOperator g S` as `IsLogicalGate (g.toGate) S`. This is equivalent to
lying in the centralizer of S (commuting with every element of the stabilizer).

**Logical operators as cosets**: The mathematical notion of "a logical operator" is a coset of S
in the group of Pauli logical operators (the centralizer). Two elements represent the same
logical operator iff they lie in the same coset (`SameLogicalOperator`).

**Nontrivial logical operators (for distance)** are those that represent a coset that is not the
identity coset and not a phase-only coset (φ·S). The element predicate
 `IsNontrivialLogicalOperator g S`
means: g is a Pauli logical operator and g represents such a nontrivial coset (i.e.
`RepresentsNontrivialCoset g S`).
-/

/-- A Pauli logical operator is a Pauli whose associated gate maps the codespace to itself.
    Equivalently, it lies in the centralizer of S (commutes with every element of S). -/
def IsPauliLogicalOperator (g : NQubitPauliGroupElement n) (S : StabilizerGroup n) : Prop :=
  IsLogicalGate (g.toGate) S

/-- If a Pauli operator anticommutes with an element of the stabilizer group,
    it is not a Pauli logical operator. -/
lemma anticommutes_imp_not_isPauliLogicalOperator (g : NQubitPauliGroupElement n)
    (S : StabilizerGroup n) (s : NQubitPauliGroupElement n) (hs : s ∈ S.toSubgroup)
    (h_anti : NQubitPauliGroupElement.Anticommute s g) : ¬IsPauliLogicalOperator g S := by
  intro hg
  have h_contradiction : ∀ ψ : NQubitState n,
      ¬IsInCodespace ψ S ∨ ¬IsInCodespace (g.toGate • ψ) S := by
    intro ψ
    by_contra h_contra
    push_neg at h_contra
    obtain ⟨hψ, hgψ⟩ := h_contra
    unfold NQubitPauliGroupElement.Anticommute at h_anti
    have h_sg := NQubitPauliGroupElement.Anticommute.toMatrix_mul_neg s g h_anti
    have h_lhs : (s.toMatrix * g.toMatrix) *ᵥ ↑ψ = (g.toMatrix * s.toMatrix) *ᵥ ↑ψ := by
      have hab := mulVec_mulVec (↑ψ) s.toMatrix g.toMatrix
      have hba := mulVec_mulVec (↑ψ) g.toMatrix s.toMatrix
      rw [← hab]
      conv_lhs => arg 2; rw [QuantumState.coe_val ψ, ← NQubitPauliGroupElement.toGate_val,
        ← smul_QState_val g.toGate ψ]
      rw [hgψ s hs, ← hba, hψ s hs, QuantumState.coe_val (g.toGate • ψ), smul_QState_val g.toGate ψ,
        QuantumState.coe_val ψ, NQubitPauliGroupElement.toGate_val]
    have h_rhs : (s.toMatrix * g.toMatrix) *ᵥ ↑ψ = (-1 : ℂ) • (g.toMatrix * s.toMatrix) *ᵥ ↑ψ := by
      rw [h_sg]
      show (-1 • (g.toMatrix * s.toMatrix)).mulVec (↑ψ) =
          (-1 : ℂ) • (g.toMatrix * s.toMatrix).mulVec (↑ψ)
      rw [Matrix.smul_mulVec]
    have h_eq : (g.toMatrix * s.toMatrix) *ᵥ ↑ψ = (-1 : ℂ) • (g.toMatrix * s.toMatrix) *ᵥ ↑ψ := by
      rw [← h_rhs, h_lhs]
    have h_zero : (g.toMatrix * s.toMatrix) *ᵥ ↑ψ = 0 := by
      ext i
      have h_eq_i := congr_fun h_eq i
      have h2 : 2 * ((g.toMatrix * s.toMatrix) *ᵥ ↑ψ) i = 0 := by
        have e := h_eq_i; rw [Pi.smul_apply] at e
        calc 2 * ((g.toMatrix * s.toMatrix) *ᵥ ↑ψ) i
            = ((g.toMatrix * s.toMatrix) *ᵥ ↑ψ) i + ((g.toMatrix * s.toMatrix) *ᵥ ↑ψ) i := by
                rw [two_mul]
          _ = (-1 : ℂ) • ((g.toMatrix * s.toMatrix) *ᵥ ↑ψ) i +
                ((g.toMatrix * s.toMatrix) *ᵥ ↑ψ) i := by
              conv_lhs => arg 1; rw [e]
          _ = 0 := by rw [neg_one_smul ℂ, add_comm]; exact add_neg_cancel _
      exact (mul_eq_zero.1 h2).resolve_left (by norm_num)
    have h_sψ : s.toMatrix *ᵥ ↑ψ = ↑ψ := by rw [QuantumState.coe_val ψ]; exact hψ s hs
    have h_ψ_zero : g.toMatrix *ᵥ ↑ψ = 0 := by
      calc g.toMatrix *ᵥ ↑ψ
          = g.toMatrix *ᵥ (s.toMatrix *ᵥ ↑ψ) := by rw [h_sψ]
        _ = (g.toMatrix * s.toMatrix) *ᵥ ↑ψ := by rw [← mulVec_mulVec (↑ψ) g.toMatrix s.toMatrix]
        _ = 0 := h_zero
    have h_ψ_val_zero : ψ.val = 0 := by
      have h_inv : (star g.toGate.val).mulVec (g.toGate.val.mulVec ψ.val) = ψ.val := by
        rw [mulVec_mulVec ψ.val (star g.toGate.val) g.toGate.val,
          Matrix.mem_unitaryGroup_iff'.1 (g.toGate.2), one_mulVec]
      rw [← h_inv, NQubitPauliGroupElement.toGate_val]
      rw [QuantumState.coe_val ψ] at h_ψ_zero
      rw [h_ψ_zero, Matrix.mulVec_zero]
    have h_norm : Quantum.norm ψ.val = 1 := ψ.2
    rw [h_ψ_val_zero, Quantum.norm_zero] at h_norm
    norm_num at h_norm
  obtain ⟨ψ, hψ⟩ := exists_codespace_state S
  exact (h_contradiction ψ).elim (fun nψ => absurd hψ nψ) (fun ngψ =>
    absurd (mem_logicalGateGroup_iff (g.toGate) S |>.1 hg ψ hψ) ngψ)

/-- A Pauli is a logical operator if and only if it lies in the centralizer of S. -/
theorem isPauliLogicalOperator_iff_mem_centralizer (g : NQubitPauliGroupElement n)
    (S : StabilizerGroup n) : IsPauliLogicalOperator g S ↔ g ∈ centralizer S := by
  constructor
  · intro hg
    by_contra h_not_comm
    obtain ⟨h, hh⟩ : ∃ h ∈ S.toSubgroup, h * g ≠ g * h := by
      contrapose! h_not_comm
      rw [mem_centralizer_iff]
      intro x hx
      exact h_not_comm x hx
    have h_anticomm : NQubitPauliGroupElement.Anticommute h g := by
      apply Classical.byContradiction
      intro h_not_anticomm
      have h_comm : h * g = g * h := by
        have h_or := NQubitPauliGroupElement.commute_or_anticommute h g
        cases h_or with
        | inl heq => exact heq
        | inr h_anti => exact absurd h_anti h_not_anticomm
      exact hh.2 h_comm
    exact absurd hg (anticommutes_imp_not_isPauliLogicalOperator g S h hh.1 h_anticomm)
  · intro hg
    rw [IsPauliLogicalOperator, isLogicalGate_iff_conjugation_matrix]
    intro h hh ψ hψ
    have h_comm : g.toGate.val * h.toMatrix = h.toMatrix * g.toGate.val := by
      have h_comm : g.toMatrix * h.toMatrix = h.toMatrix * g.toMatrix := by
        have h_comm : g * h = h * g := by
          exact (NQubitPauliGroupElement.commutes_symm h g).mp (hg h hh)
        rw [ ← Quantum.NQubitPauliGroupElement.toMatrix_mul,
        ← Quantum.NQubitPauliGroupElement.toMatrix_mul, h_comm ];
      convert h_comm;
      · exact NQubitPauliGroupElement.toGate_val g;
      · exact NQubitPauliGroupElement.toGate_val g;
    simp_all +decide [ mul_assoc];
    have h_stab : Matrix.mulVec h.toMatrix ψ.val = ψ.val := hψ h hh
    have h_unitary :
        g.toMatrix * star g.toMatrix =
          (1 : Matrix (NQubitBasis n) (NQubitBasis n) ℂ) := by
      simpa [NQubitPauliGroupElement.toGate_val] using g.toGate.2.2
    simpa [Matrix.mulVec_mulVec, Matrix.mul_assoc, h_unitary] using h_stab

/-- A Pauli is a logical operator iff it commutes with every element of a generating set
    for the stabilizer. -/
theorem isPauliLogicalOperator_iff_commutes_generators (g : NQubitPauliGroupElement n)
    (S : StabilizerGroup n) (genSet : Set (NQubitPauliGroupElement n))
    (h_closure : S.toSubgroup = Subgroup.closure genSet) :
    IsPauliLogicalOperator g S ↔ ∀ s ∈ genSet, s * g = g * s := by
  rw [isPauliLogicalOperator_iff_mem_centralizer, mem_centralizer_iff_closure g S genSet h_closure]

/-- The stabilizer group is contained in its centralizer (every stabilizer is a
    Pauli logical operator). -/
lemma IsPauliLogicalOperator_of_mem_stabilizer (S : StabilizerGroup n)
    {g : NQubitPauliGroupElement n} (hg : g ∈ S.toSubgroup) :
    IsPauliLogicalOperator g S :=
  (isPauliLogicalOperator_iff_mem_centralizer g S).2 (stabilizer_le_centralizer S hg)

/-- Pauli logical operator is unchanged when the stabilizer has the same subgroup. -/
theorem IsPauliLogicalOperator_of_toSubgroup_eq (g : NQubitPauliGroupElement n)
    {S T : StabilizerGroup n} (h : S.toSubgroup = T.toSubgroup) :
    (IsPauliLogicalOperator g S ↔ IsPauliLogicalOperator g T) := by
  rw [IsPauliLogicalOperator, IsPauliLogicalOperator]
  exact isLogicalGate_iff_toSubgroup_eq (g.toGate) S T h

/-- A nontrivial logical operator (for code distance) is a Pauli logical operator that represents
    a nontrivial coset: g is in the centralizer, not in S, and no s ∈ S has the same operator
    part as g (so the coset is not a phase-only coset φ·S). -/
def IsNontrivialLogicalOperator (g : NQubitPauliGroupElement n) (S : StabilizerGroup n) : Prop :=
  RepresentsNontrivialCoset g S

/-- Nontrivial logical operator is equivalent to representing a nontrivial coset. -/
theorem IsNontrivialLogicalOperator_iff (g : NQubitPauliGroupElement n) (S : StabilizerGroup n) :
    IsNontrivialLogicalOperator g S ↔
      g ∈ centralizer S ∧ g ∉ S.toSubgroup ∧ ∀ s ∈ S.toSubgroup, s.operators ≠ g.operators :=
  Iff.rfl

/-- Nontrivial logical operator is unchanged when the stabilizer has the same subgroup. -/
theorem IsNontrivialLogicalOperator_of_toSubgroup_eq (g : NQubitPauliGroupElement n)
    {S T : StabilizerGroup n} (h : S.toSubgroup = T.toSubgroup) :
    (IsNontrivialLogicalOperator g S ↔ IsNontrivialLogicalOperator g T) :=
  RepresentsNontrivialCoset_of_toSubgroup_eq g h

/-- Data for one logical qubit: a pair of logical X and Z operators that commute with
    the stabilizer and anticommute with each other. -/
structure LogicalQubitOps (n : ℕ) (S : StabilizerGroup n) where
  /-- Logical X operator. -/
  xOp : NQubitPauliGroupElement n
  /-- Logical Z operator. -/
  zOp : NQubitPauliGroupElement n
  /-- Logical X is in the centralizer of S. -/
  x_mem_centralizer : xOp ∈ centralizer S
  /-- Logical Z is in the centralizer of S. -/
  z_mem_centralizer : zOp ∈ centralizer S
  /-- X̄ and Z̄ anticommute. -/
  anticommute : NQubitPauliGroupElement.Anticommute xOp zOp

namespace LogicalQubitOps

/-- The logical X operator is a Pauli logical operator. -/
theorem xOp_IsPauliLogicalOperator {S : StabilizerGroup n} (ops : LogicalQubitOps n S) :
    IsPauliLogicalOperator ops.xOp S :=
  (isPauliLogicalOperator_iff_mem_centralizer ops.xOp S).2 ops.x_mem_centralizer

/-- The logical Z operator is a Pauli logical operator. -/
theorem zOp_IsPauliLogicalOperator {S : StabilizerGroup n} (ops : LogicalQubitOps n S) :
    IsPauliLogicalOperator ops.zOp S :=
  (isPauliLogicalOperator_iff_mem_centralizer ops.zOp S).2 ops.z_mem_centralizer

/-- The logical X operator is not in the stabilizer. -/
theorem xOp_not_mem {S : StabilizerGroup n} (ops : LogicalQubitOps n S) :
    ops.xOp ∉ S.toSubgroup :=
  not_mem_stabilizer_of_anticommutes_centralizer S ops.xOp ops.zOp ops.z_mem_centralizer
    ops.anticommute

/-- The logical Z operator is not in the stabilizer. -/
theorem zOp_not_mem {S : StabilizerGroup n} (ops : LogicalQubitOps n S) :
    ops.zOp ∉ S.toSubgroup :=
  not_mem_stabilizer_of_anticommutes_centralizer S ops.zOp ops.xOp ops.x_mem_centralizer
    (NQubitPauliGroupElement.anticommute_symm ops.xOp ops.zOp ops.anticommute)

/-- No stabilizer element has the same operator part as logical X; otherwise X̄ would commute
    with Z̄ (since X̄ would differ from that stabilizer only by phase). -/
theorem xOp_operators_ne_of_mem {S : StabilizerGroup n} (ops : LogicalQubitOps n S)
    (s : NQubitPauliGroupElement n) (hs : s ∈ S.toSubgroup) :
    s.operators ≠ ops.xOp.operators := by
  intro heq
  have h_phase : (ops.xOp * s⁻¹).operators = NQubitPauliOperator.identity n :=
    NQubitPauliGroupElement.mul_inv_operators_identity_of_eq_operators ops.xOp s heq.symm
  have h_comm_phase : (ops.xOp * s⁻¹) * ops.zOp = ops.zOp * (ops.xOp * s⁻¹) :=
    NQubitPauliGroupElement.commutes_of_operators_identity (ops.xOp * s⁻¹) ops.zOp h_phase
  have h_sz : s * ops.zOp = ops.zOp * s :=
  (mem_centralizer_iff ops.zOp S).1 ops.z_mem_centralizer s hs
  have key_sz : ops.zOp = s * ops.zOp * s⁻¹ :=
    (show s * ops.zOp * s⁻¹ = ops.zOp by rw [h_sz, mul_assoc,
    NQubitPauliGroupElement.mul_right_inv, mul_one]).symm
  have h_inv_sz : s⁻¹ * ops.zOp = ops.zOp * s⁻¹ := by
    have h_comm_s : s⁻¹ * ops.zOp * s = ops.zOp := by
      rw [ mul_assoc, eq_comm ];
      rw [ ← h_sz, inv_mul_cancel_left ];
    convert congr_arg ( · * s⁻¹ ) h_comm_s using 1 ; group
  have h_eq : (ops.xOp * ops.zOp) * s⁻¹ = (ops.zOp * ops.xOp) * s⁻¹ := by
    calc (ops.xOp * ops.zOp) * s⁻¹ = ops.xOp * (ops.zOp * s⁻¹) := by group
      _ = ops.xOp * (s⁻¹ * ops.zOp) := by rw [h_inv_sz]
      _ = (ops.xOp * s⁻¹) * ops.zOp := by group
      _ = ops.zOp * (ops.xOp * s⁻¹) := h_comm_phase
      _ = (ops.zOp * ops.xOp) * s⁻¹ := by group
  have h_comm : ops.xOp * ops.zOp = ops.zOp * ops.xOp := by
    calc ops.xOp * ops.zOp = (ops.xOp * ops.zOp) * (s⁻¹ * s) := by group
      _ = ((ops.xOp * ops.zOp) * s⁻¹) * s := by group
      _ = ((ops.zOp * ops.xOp) * s⁻¹) * s := by rw [h_eq]
      _ = ops.zOp * ops.xOp := by group
  have h_neg : negIdentity n * (ops.xOp * ops.zOp) = ops.xOp * ops.zOp := by
    have h_anticomm : ops.xOp * ops.zOp =
    Quantum.StabilizerGroup.negIdentity n * (ops.zOp * ops.xOp) := by
      exact ops.anticommute;
    grind
  have h_one : negIdentity n = 1 := by
    exact right_eq_mul.mp (id (Eq.symm h_neg))
  exact negIdentity_ne_one n h_one

/-- No stabilizer element has the same operator part as logical Z; otherwise Z̄ would commute
    with X̄ (since Z̄ would differ from that stabilizer only by phase). -/
theorem zOp_operators_ne_of_mem {S : StabilizerGroup n} (ops : LogicalQubitOps n S)
    (s : NQubitPauliGroupElement n) (hs : s ∈ S.toSubgroup) :
    s.operators ≠ ops.zOp.operators := by
  intro heq
  have h_phase : (ops.zOp * s⁻¹).operators = NQubitPauliOperator.identity n :=
    NQubitPauliGroupElement.mul_inv_operators_identity_of_eq_operators ops.zOp s heq.symm
  have h_comm_phase : (ops.zOp * s⁻¹) * ops.xOp = ops.xOp * (ops.zOp * s⁻¹) :=
    NQubitPauliGroupElement.commutes_of_operators_identity (ops.zOp * s⁻¹) ops.xOp h_phase
  have h_sx : s * ops.xOp = ops.xOp * s :=
  (mem_centralizer_iff ops.xOp S).1 ops.x_mem_centralizer s hs
  have key_sx : ops.xOp = s * ops.xOp * s⁻¹ :=
    (show s * ops.xOp * s⁻¹ = ops.xOp by
    rw [h_sx, mul_assoc, NQubitPauliGroupElement.mul_right_inv, mul_one]).symm
  have h_inv_sx : s⁻¹ * ops.xOp = ops.xOp * s⁻¹ := by
    rw [ eq_comm ] at key_sx;
    have h_s_inv_x : s⁻¹ * (s * ops.xOp * s⁻¹) = s⁻¹ * ops.xOp := by
      rw [key_sx];
    convert h_s_inv_x.symm using 1 ; group
  have h_eq : (ops.zOp * ops.xOp) * s⁻¹ = (ops.xOp * ops.zOp) * s⁻¹ := by
    calc (ops.zOp * ops.xOp) * s⁻¹ = ops.zOp * (ops.xOp * s⁻¹) := by group
      _ = ops.zOp * (s⁻¹ * ops.xOp) := by rw [h_inv_sx]
      _ = (ops.zOp * s⁻¹) * ops.xOp := by group
      _ = ops.xOp * (ops.zOp * s⁻¹) := h_comm_phase
      _ = (ops.xOp * ops.zOp) * s⁻¹ := by group
  have h_comm : ops.zOp * ops.xOp = ops.xOp * ops.zOp := by
    calc ops.zOp * ops.xOp = (ops.zOp * ops.xOp) * (s⁻¹ * s) := by group
      _ = ((ops.zOp * ops.xOp) * s⁻¹) * s := by group
      _ = ((ops.xOp * ops.zOp) * s⁻¹) * s := by rw [h_eq]
      _ = ops.xOp * ops.zOp := by group
  have h_symm := NQubitPauliGroupElement.anticommute_symm ops.xOp ops.zOp ops.anticommute
  have h_neg : negIdentity n * (ops.zOp * ops.xOp) = ops.zOp * ops.xOp := by
    calc negIdentity n * (ops.zOp * ops.xOp)
        = negIdentity n * (NQubitPauliGroupElement.minusOne n *
        (ops.xOp * ops.zOp)) := by rw [h_symm.symm]
      _ = (negIdentity n * NQubitPauliGroupElement.minusOne n) *
      (ops.xOp * ops.zOp) := by rw [mul_assoc]
      _ = 1 * (ops.xOp * ops.zOp) := by
        have h_contra : NQubitPauliGroupElement.Anticommute ops.zOp ops.xOp → False := by
          intro h_anti
          have h_contra : ops.zOp * ops.xOp =
          (Quantum.StabilizerGroup.negIdentity n) * (ops.xOp * ops.zOp) := by
            exact h_anti.symm ▸ by rfl;
          generalize_proofs at *;
          rw [ h_comm ] at h_contra
          generalize_proofs at *; (
          have h_contra : Quantum.StabilizerGroup.negIdentity n = 1 := by
            exact right_eq_mul.mp h_contra
          generalize_proofs at *; (
          exact absurd h_contra ( by
          exact ne_of_apply_ne ( fun x => x.phasePower ) ( by
          simp +decide [ Quantum.StabilizerGroup.negIdentity ] ) ) ;));
        exact False.elim <| h_contra h_symm
      _ = ops.xOp * ops.zOp := by rw [one_mul]
      _ = ops.zOp * ops.xOp := h_comm.symm
  have h_one : negIdentity n = 1 := by
    exact right_eq_mul.mp (id (Eq.symm h_neg))
  exact negIdentity_ne_one n h_one

/-- The logical X operator is a nontrivial logical operator (represents a nontrivial coset). -/
theorem xOp_nontrivial {S : StabilizerGroup n} (ops : LogicalQubitOps n S) :
    IsNontrivialLogicalOperator ops.xOp S :=
  ⟨ops.x_mem_centralizer, ops.xOp_not_mem, fun s hs => xOp_operators_ne_of_mem ops s hs⟩

/-- The logical Z operator is a nontrivial logical operator (represents a nontrivial coset). -/
theorem zOp_nontrivial {S : StabilizerGroup n} (ops : LogicalQubitOps n S) :
    IsNontrivialLogicalOperator ops.zOp S :=
  ⟨ops.z_mem_centralizer, ops.zOp_not_mem, fun s hs => zOp_operators_ne_of_mem ops s hs⟩

end LogicalQubitOps

/-- Two Pauli elements represent the same logical operator if they differ by an element
    of the stabilizer (same coset of S in the centralizer). -/
def SameLogicalOperator (L L' : NQubitPauliGroupElement n) (S : StabilizerGroup n) : Prop :=
  L⁻¹ * L' ∈ S.toSubgroup

namespace SameLogicalOperator

/-- Every Pauli element is the same logical operator as itself. -/
theorem refl (L : NQubitPauliGroupElement n) (S : StabilizerGroup n) :
    SameLogicalOperator L L S := by
  simp only [SameLogicalOperator]
  rw [inv_mul_cancel]
  exact S.one_mem

/-- If L and L' represent the same logical operator, so do L' and L. -/
theorem symm (S : StabilizerGroup n) {L L' : NQubitPauliGroupElement n}
    (h : SameLogicalOperator L L' S) : SameLogicalOperator L' L S := by
  simp only [SameLogicalOperator] at h ⊢
  suffices L'⁻¹ * L = (L⁻¹ * L')⁻¹ by rw [this]; exact S.inv_mem h
  rw [_root_.mul_inv_rev, inv_inv]

/-- Same logical operator is transitive. -/
theorem trans (S : StabilizerGroup n) {L L' L'' : NQubitPauliGroupElement n}
    (h₁ : SameLogicalOperator L L' S) (h₂ : SameLogicalOperator L' L'' S) :
    SameLogicalOperator L L'' S := by
  simp only [SameLogicalOperator] at h₁ h₂ ⊢
  have : L⁻¹ * L'' = (L⁻¹ * L') * (L'⁻¹ * L'') := by group
  rw [this]
  exact S.mul_mem h₁ h₂

instance (S : StabilizerGroup n) : Equivalence (fun L L' => SameLogicalOperator L L' S) where
  refl L := refl L S
  symm := symm S
  trans := trans S

end SameLogicalOperator

end StabilizerGroup
end Quantum
