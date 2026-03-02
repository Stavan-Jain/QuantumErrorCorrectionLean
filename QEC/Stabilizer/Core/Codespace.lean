import QEC.Foundations.Basic
import QEC.Stabilizer.Core.StabilizerGroup
import QEC.Stabilizer.PauliGroup
import QEC.Stabilizer.PauliGroup.Representation

set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.style.multiGoal false

namespace Quantum
namespace StabilizerGroup

variable {n : ℕ}
open Matrix
open Classical
open scoped BigOperators

/-!
# Codespace and stabilizer sum

The **codespace** of a stabilizer group is the subspace of states stabilized by every element.
This file defines the **stabilizer sum** (sum of all group elements' matrices), shows it is
nonzero and projects onto the codespace, and proves the codespace is non-empty.
-/

noncomputable section

instance : Fintype PauliOperator where
  elems := {PauliOperator.I, PauliOperator.X, PauliOperator.Y, PauliOperator.Z}
  complete := by
    intro x
    cases x <;> simp +decide

noncomputable instance : Fintype (NQubitPauliGroupElement n) :=
  Fintype.ofEquiv (Fin 4 × (Fin n → PauliOperator))
  { toFun := fun p => ⟨p.1, p.2⟩
    invFun := fun p => (p.phasePower, p.operators)
    left_inv := by intro p; simp
    right_inv := by intro p; cases p; simp }

/-- The sum of matrix representations of all elements in the stabilizer group. -/
noncomputable def stabilizerSum (S : StabilizerGroup n) :
    Matrix (NQubitBasis n) (NQubitBasis n) ℂ :=
  ∑ g ∈ (Finset.univ.filter (fun g => g ∈ S.toSubgroup)), g.toMatrix

/-- The only scalar element in a stabilizer group is the identity (since -I is excluded). -/
lemma eq_one_of_mem_stabilizer_and_is_scalar (S : StabilizerGroup n) (g : NQubitPauliGroupElement n)
    (hg : g ∈ S.toSubgroup) (h_scalar : g.operators = NQubitPauliOperator.identity n) :
    g = 1 := by
      -- Since g is a Pauli operator with identity for all qubits, it must be of the form $i^k I$ for some $k$.
      obtain ⟨k, hk⟩ : ∃ k : Fin 4, g = ⟨k, (NQubitPauliOperator.identity n)⟩ := by
        exact ⟨ g.phasePower, by cases g; aesop ⟩;
      fin_cases k <;> simp_all +decide;
      · convert S.no_neg_identity ?_;
        convert S.toSubgroup.mul_mem hg hg using 1;
        ext <;> norm_num [ Quantum.NQubitPauliGroupElement.mul ];
        · erw [show (NQubitPauliOperator.identity n *ₚ NQubitPauliOperator.identity n).phasePower = 0
            from ?_]; norm_num
          · decide +revert
          · exact NQubitPauliGroupElement.mulOp_identity_left_phase (NQubitPauliOperator.identity n)
        · exact?
      · exact S.no_neg_identity hg;
      · -- Since $g^2 = -I$, and $-I$ is not in the stabilizer group $S$, this leads to a contradiction.
        have h_contra : (g * g) ∈ S.toSubgroup := by
          exact S.toSubgroup.mul_mem ( hk ▸ hg ) ( hk ▸ hg );
        convert S.neg_identity_not_mem _;
        convert h_contra using 1;
        ext <;> simp +decide [*, NQubitPauliGroupElement.mul]
        · erw [show (NQubitPauliOperator.identity n *ₚ NQubitPauliOperator.identity n).phasePower = 0
            from ?_]
          · norm_num
          exact?
        · exact rfl

/-- The trace of a Pauli group element is non-zero only if it is proportional to the identity. -/
lemma trace_eq_zero_of_ne_identity (g : NQubitPauliGroupElement n)
    (h_ne_I : g.operators ≠ NQubitPauliOperator.identity n) :
    (g.toMatrix).trace = 0 := by
  have h_trace_zero : ∀ (p : NQubitPauliOperator n),
      p ≠ NQubitPauliOperator.identity n → (p.toMatrix).trace = 0 := by
    intros p hp_ne_I
    have h_trace_zero : (p.toMatrix * (NQubitPauliOperator.identity n).toMatrix).trace = 0 := by
      have h_trace_zero : (p.toMatrix * (NQubitPauliOperator.identity n).toMatrix).trace =
          if p = NQubitPauliOperator.identity n then (2 : ℂ)^n else 0 := by exact?
      rw [h_trace_zero, if_neg hp_ne_I]
    convert h_trace_zero using 1
    rw [show (NQubitPauliOperator.identity n |> NQubitPauliOperator.toMatrix) = 1 from ?_]
    · norm_num
    · exact?
  unfold NQubitPauliGroupElement.toMatrix; aesop

/-- The trace of the stabilizer sum is 2^n. -/
lemma trace_stabilizerSum (S : StabilizerGroup n) : (stabilizerSum S).trace = (2 : ℂ)^n := by
  have h_trace_sum : ∑ g ∈ S.toSubgroup.carrier.toFinset, (g.toMatrix).trace = 2 ^ n := by
    have h_trace_sum : ∑ g ∈ S.toSubgroup.carrier.toFinset, (g.toMatrix).trace =
        ∑ g ∈ S.toSubgroup.carrier.toFinset, if g = 1 then 2 ^ n else 0 := by
      apply Finset.sum_congr rfl
      intro g hg
      by_cases h : g.operators = NQubitPauliOperator.identity n <;> simp_all +decide [trace_eq_zero_of_ne_identity]
      · rw [if_pos]
        · rw [eq_one_of_mem_stabilizer_and_is_scalar S g hg h]
          norm_num [NQubitPauliGroupElement.toMatrix_one]
        · have := eq_one_of_mem_stabilizer_and_is_scalar S g hg h; aesop
      · aesop
    simp_all +decide
    exact fun h => False.elim <| h <| S.one_mem
  convert h_trace_sum using 1
  unfold stabilizerSum
  rw [Matrix.trace_sum]
  rcongr g; aesop

/-- The stabilizer sum is not the zero matrix. -/
lemma stabilizerSum_ne_zero (S : StabilizerGroup n) : stabilizerSum S ≠ 0 := by
  -- The trace of the stabilizer sum is $2^n$, which is not zero.
  have h_trace_nonzero : (stabilizerSum S).trace ≠ 0 := by
    -- Since $2^n$ is always positive, its real part is also positive, hence non-zero.
    have h_trace_pos : (S.stabilizerSum).trace = (2 : ℂ)^n := by
      -- Apply the lemma that states the trace of the stabilizer sum is 2^n.
      apply trace_stabilizerSum
    rw [h_trace_pos]
    norm_num [Complex.ext_iff]
  exact fun h => h_trace_nonzero (by rw [h]; norm_num)

/-- The stabilizer sum projects onto the codespace (up to scaling).
    Specifically, for any g ∈ S, g * P = P. -/
lemma mul_stabilizerSum_eq (S : StabilizerGroup n) (g : NQubitPauliGroupElement n)
    (hg : g ∈ S.toSubgroup) : g.toMatrix * stabilizerSum S = stabilizerSum S := by
  have h_mul : ∀ h ∈ S.toSubgroup, g * h ∈ S.toSubgroup := fun h hh => S.toSubgroup.mul_mem hg hh
  have h_bij : Finset.image (fun h => g * h) (Finset.univ.filter (fun h => h ∈ S.toSubgroup)) =
      Finset.univ.filter (fun h => h ∈ S.toSubgroup) := by
    refine Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr fun h hh => by aesop) ?_
    rw [Finset.card_image_of_injective _ fun x y hxy => mul_left_cancel hxy]
  have h_sum_eq : ∑ h ∈ Finset.univ.filter (fun h => h ∈ S.toSubgroup), (g * h).toMatrix =
      ∑ h ∈ Finset.univ.filter (fun h => h ∈ S.toSubgroup), h.toMatrix := by
    conv_rhs => rw [← h_bij, Finset.sum_image (Finset.card_image_iff.mp <| by aesop)]
  convert h_sum_eq using 1
  simp only [stabilizerSum, Finset.mul_sum _ _ _]
  exact Finset.sum_congr rfl fun x hx => by exact?

/-- The codespace of a stabilizer group is always non-empty. -/
lemma exists_codespace_state (S : StabilizerGroup n) : ∃ ψ : NQubitState n, IsInCodespace ψ S := by
  obtain ⟨v, hv⟩ : ∃ v : NQubitVec n, v ≠ 0 ∧ ∀ g ∈ S.toSubgroup, Matrix.mulVec g.toMatrix v = v := by
    have h_stabilizer_sum_nonzero : stabilizerSum S ≠ 0 := stabilizerSum_ne_zero S
    obtain ⟨v, hv⟩ : ∃ v : NQubitVec n, (stabilizerSum S).mulVec v ≠ 0 := by
      contrapose! h_stabilizer_sum_nonzero with h_stabilizer_sum_zero
      ext i j
      specialize h_stabilizer_sum_zero (Pi.single j 1)
      replace h_stabilizer_sum_zero := congr_fun h_stabilizer_sum_zero i
      aesop
    refine ⟨(stabilizerSum S).mulVec v, hv, ?_⟩
    intro g hg
    simp +decide [mul_stabilizerSum_eq S g hg]
  refine ⟨⟨fun i => v i / Real.sqrt (∑ i, ‖v i‖ ^ 2), ?_⟩, ?_⟩
  · unfold Quantum.norm
    simp +decide [div_pow, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    rw [← Finset.sum_div, div_self (ne_of_gt (lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (Ne.symm (by intro h; exact hv.1 (funext fun i => by
        have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).1 h i (Finset.mem_univ i)
        simpa [h] using hi)))))]
  · intro g hg
    specialize hv
    have := hv.2 g hg
    simp_all +decide
    ext i
    specialize hv
    have := congr_fun (hv.2 g hg) i
    simp_all +decide [Matrix.mulVec, dotProduct]
    simp +decide [← this, Finset.sum_div, mul_div]

end

end StabilizerGroup
end Quantum
