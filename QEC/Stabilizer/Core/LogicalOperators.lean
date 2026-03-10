import QEC.Foundations.Basic
import QEC.Stabilizer.Core.StabilizerGroup
import QEC.Stabilizer.Core.Centralizer
import QEC.Stabilizer.Core.Codespace
import QEC.Stabilizer.Core.LogicalGates
import QEC.Stabilizer.Core.LogicalGateGroup
import QEC.Stabilizer.PauliGroup
import QEC.Stabilizer.PauliGroup.Representation

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

**Nontrivial logical operators** (logical errors) are those that are logical operators but not
in the stabilizer; they act nontrivially on the logical qubits. Two operators that
differ by a stabilizer element act the same on the codespace (same logical operator).
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
    rw [IsPauliLogicalOperator, isLogicalGate_iff_conjugation]
    intro h hh ψ hψ
    have h_comm := (mem_centralizer_iff g S).1 hg h hh
    have h_mat_comm : h.toMatrix * g.toMatrix = g.toMatrix * h.toMatrix := by
      rw [← NQubitPauliGroupElement.toMatrix_mul, ← NQubitPauliGroupElement.toMatrix_mul, h_comm]
    have h_star_mul : star g.toGate.val * g.toMatrix = 1 := by
      have h_mul : g.toGate.val * star g.toGate.val = 1 := g.toGate.2.2
      rw [NQubitPauliGroupElement.toGate_val] at h_mul ⊢
      exact Matrix.mul_eq_one_comm.mp h_mul
    have h_star_mul' : star g.toMatrix * g.toMatrix = 1 := by
      rw [← NQubitPauliGroupElement.toGate_val]
      exact Matrix.mem_unitaryGroup_iff'.1 (g.toGate.2)
    have h_conj_eq : star g.toGate.val * h.toMatrix * g.toGate.val = h.toMatrix := by
      calc star g.toGate.val * h.toMatrix * g.toGate.val
          = (star g.toGate.val * h.toMatrix) * g.toGate.val := by rw [Matrix.mul_assoc]
        _ = star g.toGate.val * (h.toMatrix * g.toGate.val) := by rw [Matrix.mul_assoc]
        _ = star g.toGate.val * (g.toGate.val * h.toMatrix) := by
            rw [NQubitPauliGroupElement.toGate_val, ← h_mat_comm]
        _ = (star g.toGate.val * g.toGate.val) * h.toMatrix := by rw [Matrix.mul_assoc]
        _ = 1 * h.toMatrix := by
            rw [NQubitPauliGroupElement.toGate_val, h_star_mul']
        _ = h.toMatrix := by rw [Matrix.one_mul]
    change (star g.toGate.val * h.toMatrix * g.toGate.val).mulVec ψ.val = ψ.val
    rw [h_conj_eq, hψ h hh]

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

/-- A nontrivial logical operator is a Pauli logical operator that is not in S;
    it acts nontrivially on the logical qubits. -/
def IsNontrivialLogicalOperator (g : NQubitPauliGroupElement n) (S : StabilizerGroup n) : Prop :=
  IsPauliLogicalOperator g S ∧ g ∉ S.toSubgroup

/-- Nontrivial logical operator is equivalent to Pauli logical operator not in S. -/
theorem IsNontrivialLogicalOperator_iff (g : NQubitPauliGroupElement n) (S : StabilizerGroup n) :
    IsNontrivialLogicalOperator g S ↔ IsPauliLogicalOperator g S ∧ g ∉ S.toSubgroup :=
  Iff.rfl

/-- Nontrivial logical operator is unchanged when the stabilizer has the same subgroup. -/
theorem IsNontrivialLogicalOperator_of_toSubgroup_eq (g : NQubitPauliGroupElement n)
    {S T : StabilizerGroup n} (h : S.toSubgroup = T.toSubgroup) :
    (IsNontrivialLogicalOperator g S ↔ IsNontrivialLogicalOperator g T) := by
  rw [IsNontrivialLogicalOperator, IsNontrivialLogicalOperator]
  constructor
  · intro ⟨h1, h2⟩
    exact ⟨(IsPauliLogicalOperator_of_toSubgroup_eq g h).1 h1, by rw [← h]; exact h2⟩
  · intro ⟨h1, h2⟩
    exact ⟨(IsPauliLogicalOperator_of_toSubgroup_eq g h).2 h1, by rw [h]; exact h2⟩

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

/-- The logical X operator is a nontrivial logical operator. -/
theorem xOp_nontrivial {S : StabilizerGroup n} (ops : LogicalQubitOps n S) :
    IsNontrivialLogicalOperator ops.xOp S :=
  ⟨xOp_IsPauliLogicalOperator ops, ops.xOp_not_mem⟩

/-- The logical Z operator is a nontrivial logical operator. -/
theorem zOp_nontrivial {S : StabilizerGroup n} (ops : LogicalQubitOps n S) :
    IsNontrivialLogicalOperator ops.zOp S :=
  ⟨zOp_IsPauliLogicalOperator ops, ops.zOp_not_mem⟩

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
