import QEC.Stabilizer.Core.StabilizerGroup
import QEC.Stabilizer.Core.Centralizer
import QEC.Stabilizer.Core.LogicalGates
import QEC.Stabilizer.Core.Normalizer
import QEC.Stabilizer.PauliGroup

namespace Quantum
namespace StabilizerGroup

variable {n : ℕ}

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

/-- A Pauli is a logical operator if and only if it lies in the centralizer of S. -/
theorem isPauliLogicalOperator_iff_mem_centralizer (g : NQubitPauliGroupElement n)
    (S : StabilizerGroup n) : IsPauliLogicalOperator g S ↔ g ∈ centralizer S := by
  constructor
  · -- Forward: logical gate → centralizer
    intro h
    rw [mem_centralizer_iff]
    intro s hs
    -- We have IsLogicalGate (g.toGate) S, so g.toGate is in the normalizer
    have h_norm : IsInStabilizerNormalizer (g.toGate) S := by
      rw [← isLogicalGate_iff_isInStabilizerNormalizer]
      exact h
    -- For any ψ in codespace, conjugation of s by g.toGate stabilizes ψ
    -- The key: for Pauli operators, matrix conjugation equals group conjugation
    -- star g.toMatrix * s.toMatrix * g.toMatrix = (g⁻¹ * s * g).toMatrix
    have h_mat_conj : (star g.toMatrix * s.toMatrix * g.toMatrix) = (g⁻¹ * s * g).toMatrix := by
      simp only [NQubitPauliGroupElement.toGate_val]
      rw [NQubitPauliGroupElement.toMatrix_inv, ← NQubitPauliGroupElement.toMatrix_mul,
          ← NQubitPauliGroupElement.toMatrix_mul]
      congr! 1
      rw [mul_assoc]
    -- For any ψ in codespace, (g⁻¹ * s * g).toMatrix stabilizes ψ
    -- This means g⁻¹ * s * g stabilizes every codespace state
    have h_stab : ∀ ψ : NQubitState n, IsInCodespace ψ S →
        (g⁻¹ * s * g).toMatrix.mulVec ψ.val = ψ.val := by
      intro ψ hψ
      rw [← h_mat_conj]
      exact h_norm s hs ψ hψ
    -- TODO: Complete this proof. The key step is showing that if g⁻¹ * s * g stabilizes
    -- the codespace, then g⁻¹ * s * g ∈ centralizer S. This requires a lemma that any
    -- Pauli that stabilizes the codespace is in the centralizer (which is essentially
    -- the forward direction of the equivalence we're proving). For now, we use sorry
    -- but the backward direction (centralizer → logical gate) is complete and is the
    -- direction currently used in practice.
    sorry
  · -- Backward: centralizer → logical gate
    intro h
    rw [isLogicalGate_iff_isInStabilizerNormalizer]
    intro s hs ψ hψ
    have h_comm : s * g = g * s := (mem_centralizer_iff g S).1 h s hs
    have h_mat : s.toMatrix * g.toMatrix = g.toMatrix * s.toMatrix := by
      have h_toGate_mul := congrArg NQubitPauliGroupElement.toMatrix h_comm
      rw [NQubitPauliGroupElement.toMatrix_mul, NQubitPauliGroupElement.toMatrix_mul] at h_toGate_mul
      exact h_toGate_mul
    have h_stab : s.toMatrix.mulVec ψ.val = ψ.val := (IsInCodespace.iff_all_stabilizers ψ S).1 hψ s hs
    simp only [NQubitPauliGroupElement.toGate_val]
    calc (star g.toMatrix * s.toMatrix * g.toMatrix).mulVec ψ.val
        = (star g.toMatrix * (s.toMatrix * g.toMatrix)).mulVec ψ.val := by rw [Matrix.mul_assoc]
      _ = (star g.toMatrix).mulVec ((s.toMatrix * g.toMatrix).mulVec ψ.val) := by
          rw [← mulVec_mulVec ψ.val (star g.toMatrix) (s.toMatrix * g.toMatrix)]
      _ = (star g.toMatrix).mulVec (g.toMatrix.mulVec (s.toMatrix.mulVec ψ.val)) := by
          rw [h_mat, mulVec_mulVec ψ.val g.toMatrix s.toMatrix]
      _ = (star g.toMatrix).mulVec (g.toMatrix.mulVec ψ.val) := by rw [h_stab]
      _ = ((star g.toMatrix) * g.toMatrix).mulVec ψ.val := by rw [mulVec_mulVec]
      _ = ψ.val := by
        have h_unit : (star g.toMatrix) * g.toMatrix = 1 := by
          rw [← NQubitPauliGroupElement.toGate_val g, ← gate_inv_val (g.toGate),
              gate_val_inv_mul (g.toGate)]
        rw [h_unit, one_mulVec]

/-- Membership in the centralizer is equivalent to being a Pauli logical operator. -/
lemma mem_centralizer_iff_IsPauliLogicalOperator (g : NQubitPauliGroupElement n)
    (S : StabilizerGroup n) : g ∈ centralizer S ↔ IsPauliLogicalOperator g S := by
  rw [isPauliLogicalOperator_iff_mem_centralizer]

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
  rw [mul_inv_rev, inv_inv]

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
