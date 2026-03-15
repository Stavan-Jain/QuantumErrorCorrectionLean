import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.Complex.Basic
import QEC.Stabilizer.Codes.Steane7
import QEC.Foundations.UniformTransversalGate
import QEC.Foundations.Gates
import QEC.Foundations.GateConjugation
import QEC.Stabilizer.Core.LogicalGates
import QEC.Stabilizer.Core.LogicalCliffordAction
import QEC.Stabilizer.PauliGroup.NQubitOperator
import QEC.Stabilizer.PauliGroup.NQubitElement
import QEC.Stabilizer.PauliGroup.Representation
import QEC.Stabilizer.PauliGroup.TransversalConjugation
import QEC.Stabilizer.PauliGroupSingle.Operator

namespace Quantum

open Matrix
open scoped BigOperators

/-!
Conjugation convention: conjugation by a matrix U means U P U† (adjoint on the right).
So we state and prove equalities of the form U * M * star U = ...
-/

namespace StabilizerGroup
namespace Steane7

open Matrix
open scoped BigOperators

/-!
# Transversal H and S as logical gates for the Steane [[7,1,3]] code

We show that the uniform transversal Hadamard and phase gates
(H⊗7 and S⊗7) are logical gates for the Steane code:
they map the codespace to itself.
-/

/-- Transversal Hadamard: H on each of the 7 physical qubits. -/
noncomputable def transversalH_Steane7 : NQubitGate 7 :=
  uniformTransversalGate 7 H

/-- Transversal phase gate: S† on each of the 7 physical qubits.
Conjugation is U P U† (adjoint on the right). -/
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

/-- swapXZ (Z↔X) sends Z-generators to X-generators: swapXZ_element Z1 = X1, etc. -/
private lemma swapXZ_element_Z1_eq_X1 : swapXZ_element Z1 = X1 := by
  unfold swapXZ_element; congr 2; ext i; fin_cases i <;>
    simp [Z1, NQubitPauliOperator.transversalSwapXZ, PauliOperator.swapXZ,
      NQubitPauliOperator.set, NQubitPauliOperator.identity]
private lemma swapXZ_element_Z2_eq_X2 : swapXZ_element Z2 = X2 := by
  unfold swapXZ_element; congr 2; ext i; fin_cases i <;>
    simp [Z2, NQubitPauliOperator.transversalSwapXZ, PauliOperator.swapXZ,
      NQubitPauliOperator.set, NQubitPauliOperator.identity]
private lemma swapXZ_element_Z3_eq_X3 :
    swapXZ_element Z3 = X3 := by
  unfold swapXZ_element; congr 2; ext i; fin_cases i <;>
    simp [Z3, NQubitPauliOperator.transversalSwapXZ, PauliOperator.swapXZ,
      NQubitPauliOperator.set, NQubitPauliOperator.identity]

/-- Swapping X↔Z on any Steane generator yields an element of the stabilizer subgroup. -/
lemma transversalSwapXZ_mem_subgroup
    (g : NQubitPauliGroupElement 7) (hg : g ∈ generatorsList) :
    (⟨g.phasePower, NQubitPauliOperator.transversalSwapXZ g.operators⟩ :
      NQubitPauliGroupElement 7) ∈ subgroup := by
  unfold subgroup generatorsList at *
  simp_all +decide [Subgroup.mem_closure]
  rcases hg with (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp +decide [generators]
  all_goals
    intro K hK₁ hK₂
    unfold ZGenerators XGenerators at *
    simp_all +decide [Set.insert_subset_iff, Set.singleton_subset_iff]
  · convert hK₂.1 using 1
    congr
    ext i
    fin_cases i <;> rfl
  · convert hK₂.2.1 using 1
    congr
    ext i
    fin_cases i <;> rfl
  · convert hK₂.2.2 using 1
    congr
    ext i
    fin_cases i <;> rfl
  · convert hK₁.1 using 1
    congr
    ext i
    fin_cases i <;> rfl
  · convert hK₁.2.1 using 1
    congr
    ext i
    fin_cases i <;> rfl
  · convert hK₁.2.2 using 1
    congr
    ext i
    fin_cases i <;> rfl

/-- Single-qubit: H P H† = swapXZ(P) for P ≠ Y
(conjugation = adjoint on the right). -/
lemma H_conj_mul_toMatrix_mul_H_adj
    (p : PauliOperator) (h : p ≠ .Y) :
    H.val * p.toMatrix * star H.val = (PauliOperator.swapXZ p).toMatrix := by
  cases p <;> simp_all +decide [PauliOperator.swapXZ]
  · simpa using (Matrix.mem_unitaryGroup_iff.1 H.2)
  · simpa using H_conj_X
  · simpa using H_conj_Z

/-- Conjugation of n-qubit Pauli (no Y) by transversal H equals transversalSwapXZ (U P U†). -/
lemma uniformTransversalGateMatrix_H_conj_op (n : ℕ) (op : NQubitPauliOperator n)
    (h : ∀ i, op i ≠ .Y) :
    (uniformTransversalGateMatrix n H) * op.toMatrix * star (uniformTransversalGateMatrix n H) =
      (NQubitPauliOperator.transversalSwapXZ op).toMatrix := by
  rw [ uniformTransversalGateMatrix_conjugation ];
  have h_conj : ∀ i,
      (H.val * (op i).toMatrix * star H.val) = (PauliOperator.swapXZ (op i)).toMatrix := by
    exact fun i => H_conj_mul_toMatrix_mul_H_adj _ ( h i );
  aesop

/-- Conjugating a Pauli group element (no Y) by transversal H gives the swapXZ element (U P U†). -/
lemma transversalH_conjugates_element
    (g : NQubitPauliGroupElement 7) (h_no_Y : ∀ i, g.operators i ≠ .Y) :
    (uniformTransversalGateMatrix 7 H) * g.toMatrix * star (uniformTransversalGateMatrix 7 H) =
    (swapXZ_element g).toMatrix := by
  have h_conj :
      (uniformTransversalGateMatrix 7 H) * g.operators.toMatrix *
        star (uniformTransversalGateMatrix 7 H) =
      (NQubitPauliOperator.transversalSwapXZ g.operators).toMatrix := by
    exact uniformTransversalGateMatrix_H_conj_op 7 g.operators h_no_Y
  unfold NQubitPauliGroupElement.toMatrix swapXZ_element
  simp [h_conj]

/-- Transversal H conjugates every stabilizer element to some stabilizer element (U P U†). -/
lemma transversalH_conjugates_stabilizer_to_stabilizer (g : NQubitPauliGroupElement 7)
    (hg : g ∈ stabilizerGroup.toSubgroup) :
    ∃ g' ∈ stabilizerGroup.toSubgroup,
      transversalH_Steane7.val * g.toMatrix * star transversalH_Steane7.val = g'.toMatrix := by
  obtain ⟨seq, hseq⟩ : ∃ seq : List (NQubitPauliGroupElement 7),
      (∀ g ∈ seq, g ∈ generatorsList) ∧ g = List.prod seq := by
    have h_seq : g ∈ Subgroup.closure (NQubitPauliGroupElement.listToSet generatorsList) := by
      convert hg using 1;
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ h_seq
    · intro x hx
      use [x]
      simp;
      exact ⟨ by simpa [ NQubitPauliGroupElement.listToSet ] using hx, by
        simp [NQubitPauliGroupElement.mul];
        simp [NQubitPauliGroupElement.mulOp];
        congr! 1;
        · simp +decide [ NQubitPauliOperator.identity ];
          exact Finset.sum_eq_zero fun i _ => by
            rcases x.operators i with ( _ | _ | _ | _ ) <;> rfl;
        · exact funext fun i => by rcases x.operators i with ( _ | _ | _ | _ ) <;> rfl; ⟩;
    · exact ⟨ [ ], by simp +decide ⟩;
    · rintro x y hx hy ⟨ seq₁, hseq₁, rfl ⟩ ⟨ seq₂, hseq₂, rfl ⟩
      exact ⟨ seq₁ ++ seq₂, by aesop ⟩
    · rintro x hx ⟨ seq, hseq, rfl ⟩;
      refine ⟨ seq.reverse.map fun g => g⁻¹, ?_, ?_ ⟩
      · intro g hg
        rcases List.mem_map.1 hg with ⟨g₀, hg₀, rfl⟩
        have hg₀' : g₀ ∈ seq := by
          simpa using (List.mem_reverse.mp hg₀)
        specialize hseq g₀ hg₀'
        have hgen : g₀ = Z1 ∨ g₀ = Z2 ∨ g₀ = Z3 ∨ g₀ = X1 ∨ g₀ = X2 ∨ g₀ = X3 := by
          unfold generatorsList at hseq
          aesop
        rcases hgen with ( rfl | rfl | rfl | rfl | rfl | rfl ) <;>
          simp +decide
            [ Quantum.StabilizerGroup.Steane7.generatorsList, Quantum.StabilizerGroup.Steane7.Z1,
            Quantum.StabilizerGroup.Steane7.Z2,
            Quantum.StabilizerGroup.Steane7.Z3, Quantum.StabilizerGroup.Steane7.X1,
            Quantum.StabilizerGroup.Steane7.X2, Quantum.StabilizerGroup.Steane7.X3,
            Quantum.NQubitPauliGroupElement.inv ]
      · simp_all +decide [ List.prod_inv_reverse ]
  have h_conj_seq : ∀ g ∈ seq, ∃ g' ∈ subgroup,
      (transversalH_Steane7 : NQubitGate 7).val * g.toMatrix *
        star (transversalH_Steane7 : NQubitGate 7).val =
        g'.toMatrix := by
    intros g hg_seq
    obtain ⟨g', hg'_subgroup, hg'_conjugate⟩ : ∃ g' ∈ subgroup,
        (transversalH_Steane7 : NQubitGate 7).val * g.toMatrix *
          star (transversalH_Steane7 : NQubitGate 7).val =
          g'.toMatrix := by
      have h_conj :
          (transversalH_Steane7 : NQubitGate 7).val * g.toMatrix *
            star (transversalH_Steane7 : NQubitGate 7).val =
          (swapXZ_element g).toMatrix := by
        apply transversalH_conjugates_element g (by
        have := hseq.1 g hg_seq; fin_cases this <;> simp +decide [ * ] ;)
      exact ⟨ _, transversalSwapXZ_mem_subgroup g ( hseq.1 g hg_seq ), h_conj ⟩;
    use g';
  have h_conj_prod : ∀ seq : List (NQubitPauliGroupElement 7),
      (∀ g ∈ seq, ∃ g' ∈ subgroup,
          (transversalH_Steane7 : NQubitGate 7).val * g.toMatrix *
            star (transversalH_Steane7 : NQubitGate 7).val =
            g'.toMatrix) →
        ∃ g' ∈ subgroup,
          (transversalH_Steane7 : NQubitGate 7).val * (List.prod seq).toMatrix *
            star (transversalH_Steane7 : NQubitGate 7).val = g'.toMatrix := by
    intro seq hseq
    induction seq with
    | nil =>
        simp_all +decide
        refine ⟨ 1, Subgroup.one_mem subgroup, ?_ ⟩
        erw [ NQubitPauliGroupElement.toMatrix_one ]
        norm_num [ Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul, NQubitPauliGroupElement.one ]
    | cons g seq ih =>
        simp_all +decide [ List.prod_cons ]
        obtain ⟨ g', hg', hg'' ⟩ := ih
        obtain ⟨ g'', hg'', hg''' ⟩ := hseq.1
        use g'' * g'
        simp_all +decide
        have h_conj_prod :
            (transversalH_Steane7 : NQubitGate 7).val * (g.mul seq.prod).toMatrix *
              star (transversalH_Steane7 : NQubitGate 7).val =
            (transversalH_Steane7 : NQubitGate 7).val * g.toMatrix *
              star (transversalH_Steane7 : NQubitGate 7).val *
              (transversalH_Steane7 : NQubitGate 7).val * seq.prod.toMatrix *
              star (transversalH_Steane7 : NQubitGate 7).val := by
          have h_conj_prod : (g.mul seq.prod).toMatrix = g.toMatrix * seq.prod.toMatrix := by
            apply NQubitPauliGroupElement.toMatrix_mul
          simp +decide [ h_conj_prod, mul_assoc ]
        simp_all +decide [ mul_assoc, NQubitPauliGroupElement.mul ]
        constructor
        · exact Subgroup.mul_mem _ hg'' hg'
        · rw [ ← NQubitPauliGroupElement.toMatrix_mul ]
          rfl
  simpa only [ hseq.2 ] using h_conj_prod seq h_conj_seq |>
    fun ⟨ g', hg', hg'' ⟩ => ⟨ g', by simpa [ stabilizerGroup_toSubgroup_eq ] using hg', hg'' ⟩

/-- Transversal Hadamard is a logical gate for the Steane code. -/
theorem transversalH_Steane7_isLogicalGate :
    IsLogicalGate transversalH_Steane7 stabilizerGroup := by
  rw [isLogicalGate_iff_conjugation]
  intro g hg ψ hψ
  obtain ⟨g', hg', heq⟩ := transversalH_conjugates_stabilizer_to_stabilizer g hg
  rw [ heq ];
  exact hψ g' hg'

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
  intro i
  simp [logicalX, NQubitPauliOperator.X]

/-- Steane logical Z has no Y components. -/
private lemma logicalZ_no_Y : ∀ i, logicalZ.operators i ≠ PauliOperator.Y := by
  intro i
  simp [logicalZ, NQubitPauliOperator.Z]

/-- Transversal Hadamard acts as logical Hadamard on the canonical Steane logical pair. -/
theorem transversalH_Steane7_isLogicalHadamardOn :
    LogicalQubitOps.IsLogicalHadamard
      ⟨logicalX, logicalZ, logicalX_mem_centralizer, logicalZ_mem_centralizer,
        logicalX_anticommutes_logicalZ⟩
      transversalH_Steane7 := by
  refine ⟨transversalH_Steane7_isLogicalGate, ?_, ?_⟩
  · simpa [swapXZ_element_logicalX_eq_logicalZ] using
      transversalH_conjugates_element logicalX logicalX_no_Y
  · simpa [swapXZ_element_logicalZ_eq_logicalX] using
      transversalH_conjugates_element logicalZ logicalZ_no_Y

/-!
## Transversal S as a logical gate

Conjugation is U P U† (adjoint on the right). S† on each qubit fixes Z and sends X to Y.
Z-generators are fixed; X-generators go to X*Z (in the stabilizer).
-/

lemma transversalS_conjugates_Z_generator (g : NQubitPauliGroupElement 7) (hg : g ∈ ZGenerators) :
    transversalS_Steane7.val * g.toMatrix * star transversalS_Steane7.val = g.toMatrix := by
  convert uniformTransversalGateMatrix_inv_S_conj_Z_op 7 g.operators _ using 1;
  · unfold NQubitPauliGroupElement.toMatrix;
    have h_phase : g.phasePower = 0 := by
      cases hg <;> aesop;
    unfold Quantum.PauliGroupElement.phasePowerToComplex; aesop;
  · simp [NQubitPauliGroupElement.toMatrix];
    rcases hg with ( rfl | rfl | rfl );
    · unfold Quantum.StabilizerGroup.Steane7.Z1; norm_num;
    · erw [ show Quantum.StabilizerGroup.Steane7.Z2.phasePower = 0 from rfl ] ;
        norm_num [ Quantum.PauliGroupElement.phasePowerToComplex ] ;
    · erw [ show ( Quantum.StabilizerGroup.Steane7.Z3.phasePower : Fin 4 ) = 0 from rfl ] ;
        norm_num [ Quantum.PauliGroupElement.phasePowerToComplex ];
  · rcases hg with ( rfl | rfl | rfl ) <;> simp +decide

set_option maxHeartbeats 1000000 in
-- This proof unfolds large matrix products and does exhaustive `fin_cases` splitting, which
-- can exceed the default heartbeat budget during simplification and arithmetic normalization.
/-- Transversal S conjugates X1 to X1*Z1 (in the stabilizer). -/
lemma transversalS_conjugates_X1 :
    transversalS_Steane7.val * X1.toMatrix * star transversalS_Steane7.val =
      (X1 * Z1).toMatrix := by
  have h_diag : ∀ (g : NQubitPauliOperator 7),
      (uniformTransversalGateMatrix 7 inv_S) * g.toMatrix *
        star (uniformTransversalGateMatrix 7 inv_S) =
        fun b₁ b₂ => (Finset.univ : Finset (Fin 7)).prod
          (fun i => (inv_S.val * (g i).toMatrix * star inv_S.val) (b₁ i) (b₂ i)) := by
    exact fun g ↦ uniformTransversalGateMatrix_conjugation 7 inv_S g;
  ext b₁ b₂
  convert congr_fun ( congr_fun ( h_diag ( X1.operators ) ) b₁ ) b₂ using 1;
  · congr! 2;
    unfold Quantum.StabilizerGroup.Steane7.X1
    unfold Quantum.NQubitPauliGroupElement.toMatrix
    norm_num
  · unfold Quantum.StabilizerGroup.Steane7.X1 Quantum.StabilizerGroup.Steane7.Z1;
    simp +decide
      [ Quantum.NQubitPauliGroupElement.toMatrix, Quantum.NQubitPauliOperator.toMatrix ]
    unfold Quantum.NQubitPauliOperator.set; simp +decide [ Fin.prod_univ_succ ];
    unfold Quantum.NQubitPauliOperator.identity; simp +decide
    simp +decide [ NQubitPauliGroupElement.mul ];
    simp +decide
      [ show
          (fun j : Fin 7 =>
            if j = 4 then Quantum.PauliOperator.X
            else if j = 2 then Quantum.PauliOperator.X
            else if j = 1 then Quantum.PauliOperator.X
            else if j = 0 then Quantum.PauliOperator.X
            else Quantum.PauliOperator.I) *ₚ
              (fun j : Fin 7 =>
                if j = 4 then Quantum.PauliOperator.Z
                else if j = 2 then Quantum.PauliOperator.Z
                else if j = 1 then Quantum.PauliOperator.Z
                else if j = 0 then Quantum.PauliOperator.Z
                else Quantum.PauliOperator.I) =
            ⟨1 + 1 + 1 + 1, fun j =>
              if j = 4 then Quantum.PauliOperator.Y
              else if j = 2 then Quantum.PauliOperator.Y
              else if j = 1 then Quantum.PauliOperator.Y
              else if j = 0 then Quantum.PauliOperator.Y
              else Quantum.PauliOperator.I⟩ from by
          exact
            NQubitPauliGroupElement.toMatrix_inj
              ((fun j ↦
                  if j = 4 then PauliOperator.X
                  else if j = 2 then PauliOperator.X
                  else if j = 1 then PauliOperator.X
                  else if j = 0 then PauliOperator.X
                  else PauliOperator.I) *ₚ
                fun j ↦
                  if j = 4 then PauliOperator.Z
                  else if j = 2 then PauliOperator.Z
                  else if j = 1 then PauliOperator.Z
                  else if j = 0 then PauliOperator.Z
                  else PauliOperator.I)
              { phasePower := 1 + 1 + 1 + 1
                operators := fun j ↦
                  if j = 4 then PauliOperator.Y
                  else if j = 2 then PauliOperator.Y
                  else if j = 1 then PauliOperator.Y
                  else if j = 0 then PauliOperator.Y
                  else PauliOperator.I }
              rfl ]
    unfold Quantum.inv_S; simp +decide [ Matrix.mul_apply, Matrix.one_apply ];
    unfold Quantum.Ymat Quantum.Xmat Quantum.Smat
    simp +decide
    rcases b₁ 0 with ( _ | _ | b₁₀ ) <;> rcases b₂ 0 with ( _ | _ | b₂₀ ) <;>
      norm_num [ Fin.ext_iff ] at *;
    · rcases b₁ 1 with ( _ | _ | b₁₁ ) <;>
        rcases b₂ 1 with ( _ | _ | b₂₁ ) <;> norm_num [ Fin.ext_iff ] at *
      · rcases b₁ 2 with ( _ | _ | b₁₂ ) <;>
          rcases b₂ 2 with ( _ | _ | b₂₂ ) <;> norm_num [ Fin.ext_iff ] at *
        · rcases b₁ 4 with ( _ | _ | b₁₄ ) <;>
            rcases b₂ 4 with ( _ | _ | b₂₄ ) <;> norm_num [ Fin.ext_iff ] at *
        · linarith;
        · rcases b₁ 4 with ( _ | _ | b₁₄ ) <;>
            rcases b₂ 4 with ( _ | _ | b₂₄ ) <;> norm_num [ Fin.ext_iff ] at *
        · linarith;
      · grind;
      · rcases b₁ 2 with ( _ | _ | b₁₂ ) <;>
          rcases b₂ 2 with ( _ | _ | b₂₂ ) <;> norm_num [ Fin.ext_iff ] at *
        · rcases b₁ 4 with ( _ | _ | b₁₄ ) <;>
            rcases b₂ 4 with ( _ | _ | b₂₄ ) <;> norm_num [ Fin.ext_iff ] at *
        · linarith;
        · rcases b₁ 4 with ( _ | _ | b₁₄ ) <;>
            rcases b₂ 4 with ( _ | _ | b₂₄ ) <;> norm_num [ Fin.ext_iff ] at *
        · grind;
      · omega;
    · linarith;
    · rcases b₁ 1 with ( _ | _ | b₁₁ ) <;>
        rcases b₂ 1 with ( _ | _ | b₂₁ ) <;> norm_num [ Fin.ext_iff ] at *
      · rcases b₁ 2 with ( _ | _ | b₁₂ ) <;>
          rcases b₂ 2 with ( _ | _ | b₂₂ ) <;> norm_num [ Fin.ext_iff ] at *
        · rcases b₁ 4 with ( _ | _ | b₁₄ ) <;>
            rcases b₂ 4 with ( _ | _ | b₂₄ ) <;> norm_num [ Fin.ext_iff ] at *
        · linarith;
        · rcases b₁ 4 with ( _ | _ | b₁₄ ) <;>
            rcases b₂ 4 with ( _ | _ | b₂₄ ) <;> norm_num [ Fin.ext_iff ] at *
        · linarith;
      · omega;
      · rcases b₁ 2 with ( _ | _ | b₁₂ ) <;>
          rcases b₂ 2 with ( _ | _ | b₂₂ ) <;> norm_num [ Fin.ext_iff ] at *
        · rcases b₁ 4 with ( _ | _ | b₁₄ ) <;>
            rcases b₂ 4 with ( _ | _ | b₂₄ ) <;> norm_num [ Fin.ext_iff ] at *
        · grind;
        · rcases b₁ 4 with ( _ | _ | b₁₄ ) <;>
            rcases b₂ 4 with ( _ | _ | b₂₄ ) <;> norm_num [ Fin.ext_iff ] at *
        · linarith;
      · linarith;
    · linarith

set_option maxHeartbeats 1000000 in
-- This proof performs repeated symbolic matrix-expansion over 7 qubits; the higher heartbeat
-- cap prevents timeout while `simp`/`norm_num` discharge the generated goals.
-- This proof performs repeated symbolic matrix-expansion over 7 qubits; the higher heartbeat
-- cap prevents timeout while `simp`/`norm_num` discharge the generated goals.
lemma transversalS_conjugates_X2 :
    transversalS_Steane7.val * X2.toMatrix * star transversalS_Steane7.val =
      (X2 * Z2).toMatrix := by
  unfold Quantum.StabilizerGroup.Steane7.X2 Quantum.StabilizerGroup.Steane7.Z2
    Quantum.StabilizerGroup.Steane7.transversalS_Steane7;
  unfold Quantum.uniformTransversalGate; norm_num [ Quantum.NQubitPauliOperator.toMatrix ] ;
  rw [ ← Matrix.ext_iff ] at *;
  simp +decide [ NQubitPauliGroupElement.mul, NQubitPauliGroupElement.toMatrix,
    NQubitPauliOperator.toMatrix ];
  intro i j;
  rw [ uniformTransversalGateMatrix_conjugation ];
  unfold Quantum.PauliGroupElement.phasePowerToComplex; norm_num [ Fin.prod_univ_succ ] ;
  simp +decide [ Quantum.NQubitPauliOperator.set, Quantum.NQubitPauliOperator.identity ] at *;
  simp +decide
    [ NQubitPauliOperator.set, NQubitPauliOperator.identity, NQubitPauliGroupElement.mulOp ] at *
  simp +decide [ Fin.sum_univ_succ, Matrix.one_apply, Matrix.mul_apply, Quantum.Xmat, Quantum.Ymat,
    Quantum.inv_S ] at *;
  simp +decide [ Quantum.Smat ] at *;
  rcases i0 : i 0 with ( _ | _ | i0 ) <;>
    rcases j0 : j 0 with ( _ | _ | j0 ) <;> simp +decide [ i0, j0 ] at *
  · rcases i1 : i 1 with ( _ | _ | i1 ) <;>
      rcases j1 : j 1 with ( _ | _ | j1 ) <;> simp +decide [ i1, j1 ] at *
    · rcases i3 : i 3 with ( _ | _ | i3 ) <;>
        rcases j3 : j 3 with ( _ | _ | j3 ) <;> simp +decide [ i3, j3 ] at *
      · rcases i5 : i 5 with ( _ | _ | i5 ) <;>
          rcases j5 : j 5 with ( _ | _ | j5 ) <;> simp +decide [ i5, j5 ] at *
      · linarith;
      · rcases i5 : i 5 with ( _ | _ | i5 ) <;>
          rcases j5 : j 5 with ( _ | _ | j5 ) <;> simp +decide [ i5, j5 ] at *
      · linarith;
    · omega;
    · rcases i3 : i 3 with ( _ | _ | i3 ) <;>
        rcases j3 : j 3 with ( _ | _ | j3 ) <;> simp +decide [ i3, j3 ] at *
      · rcases i5 : i 5 with ( _ | _ | i5 ) <;>
          rcases j5 : j 5 with ( _ | _ | j5 ) <;> simp +decide [ i5, j5 ] at *
      · omega;
      · rcases i5 : i 5 with ( _ | _ | i5 ) <;>
          rcases j5 : j 5 with ( _ | _ | j5 ) <;> simp +decide [ i5, j5 ] at *
      · omega;
    · omega;
  · omega;
  · rcases i1 : i 1 with ( _ | _ | i1 ) <;>
      rcases j1 : j 1 with ( _ | _ | j1 ) <;> simp +decide [ i1, j1 ] at *
    · rcases i3 : i 3 with ( _ | _ | i3 ) <;>
        rcases j3 : j 3 with ( _ | _ | j3 ) <;> simp +decide [ i3, j3 ] at *
      · rcases i5 : i 5 with ( _ | _ | i5 ) <;>
          rcases j5 : j 5 with ( _ | _ | j5 ) <;> simp +decide [ i5, j5 ] at *
      · omega;
      · rcases i5 : i 5 with ( _ | _ | i5 ) <;>
          rcases j5 : j 5 with ( _ | _ | j5 ) <;> simp +decide [ i5, j5 ] at *
      · omega;
    · omega;
    · rcases i3 : i 3 with ( _ | _ | i3 ) <;>
        rcases j3 : j 3 with ( _ | _ | j3 ) <;> simp +decide [ i3, j3 ] at *
      · rcases i5 : i 5 with ( _ | _ | i5 ) <;>
          rcases j5 : j 5 with ( _ | _ | j5 ) <;> simp +decide [ i5, j5 ] at *
      · omega;
      · rcases i5 : i 5 with ( _ | _ | i5 ) <;>
          rcases j5 : j 5 with ( _ | _ | j5 ) <;> simp +decide [ i5, j5 ] at *
      · omega;
    · omega;
  · omega

set_option maxHeartbeats 1000000 in
-- This proof relies on explicit basis-index case analysis after conjugation expansion, and
-- the default heartbeat limit is too small for the resulting normalization workload.
/-- Transversal S conjugates X3 to X3*Z3. -/
lemma transversalS_conjugates_X3 :
    transversalS_Steane7.val * X3.toMatrix * star transversalS_Steane7.val =
      (X3 * Z3).toMatrix := by
  unfold Quantum.StabilizerGroup.Steane7.X3 Quantum.StabilizerGroup.Steane7.Z3
    Quantum.StabilizerGroup.Steane7.transversalS_Steane7;
  unfold NQubitPauliGroupElement.toMatrix NQubitPauliOperator.toMatrix
  simp +decide [ Matrix.mul_assoc ]
  convert uniformTransversalGateMatrix_conjugation 7 inv_S _ using 1;
  rotate_right;
  · exact fun i =>
      if i = 0 then Quantum.PauliOperator.X
      else if i = 2 then Quantum.PauliOperator.X
      else if i = 3 then Quantum.PauliOperator.X
      else if i = 6 then Quantum.PauliOperator.X
      else Quantum.PauliOperator.I;
  · simp +decide [ Matrix.mul_assoc ];
    congr! 2;
  · ext b₁ b₂; simp +decide [ Fin.prod_univ_succ ] ;
    simp +decide [ Quantum.PauliOperator.toMatrix, Quantum.inv_S ] at *
    simp +decide [ Quantum.NQubitPauliGroupElement.mul ] at *
    simp +decide [ NQubitPauliOperator.set, NQubitPauliOperator.identity,
      Quantum.NQubitPauliGroupElement.mulOp ] at *;
    simp +decide [ Fin.sum_univ_succ, Quantum.PauliOperator.mulOp ] at *;
    simp +decide [ Matrix.mul_apply, Quantum.Smat, Quantum.Xmat, Quantum.Ymat ] at *;
    rcases b₁ 0 with ( _ | _ | b₁₀ ) <;>
      rcases b₂ 0 with ( _ | _ | b₂₀ ) <;> norm_num [ Fin.ext_iff, Matrix.one_apply ] at *
    · rcases b₁ 2 with ( _ | _ | b₁₂ ) <;>
        rcases b₂ 2 with ( _ | _ | b₂₂ ) <;>
        norm_num [ Fin.ext_iff, Matrix.vecHead, Matrix.vecTail ] at *
      · rcases b₁ 3 with ( _ | _ | b₁₃ ) <;>
          rcases b₂ 3 with ( _ | _ | b₂₃ ) <;>
          norm_num [ Fin.ext_iff, Matrix.vecHead, Matrix.vecTail ] at *
        · rcases b₁ 6 with ( _ | _ | b₁₆ ) <;>
            rcases b₂ 6 with ( _ | _ | b₂₆ ) <;>
            norm_num [ Fin.ext_iff, Matrix.vecHead, Matrix.vecTail ] at *
        · grind;
        · rcases b₁ 6 with ( _ | _ | b₁₆ ) <;>
            rcases b₂ 6 with ( _ | _ | b₂₆ ) <;>
            norm_num [ Fin.ext_iff, Matrix.vecHead, Matrix.vecTail ] at *
        · linarith;
      · linarith;
      · rcases b₁ 3 with ( _ | _ | b₁₃ ) <;>
          rcases b₂ 3 with ( _ | _ | b₂₃ ) <;>
          norm_num [ Fin.ext_iff, Matrix.vecHead, Matrix.vecTail ] at *
        · rcases b₁ 6 with ( _ | _ | b₁₆ ) <;>
            rcases b₂ 6 with ( _ | _ | b₂₆ ) <;>
            norm_num [ Fin.ext_iff, Matrix.vecHead, Matrix.vecTail ] at *
        · grind;
        · rcases b₁ 6 with ( _ | _ | b₁₆ ) <;>
            rcases b₂ 6 with ( _ | _ | b₂₆ ) <;>
            norm_num [ Fin.ext_iff, Matrix.vecHead, Matrix.vecTail ] at *
        · grind;
      · linarith;
    · linarith;
    · rcases b₁ 2 with ( _ | _ | b₁₂ ) <;>
        rcases b₂ 2 with ( _ | _ | b₂₂ ) <;>
        norm_num [ Fin.ext_iff, Matrix.vecHead, Matrix.vecTail ] at *
      · rcases b₁ 3 with ( _ | _ | b₁₃ ) <;>
          rcases b₂ 3 with ( _ | _ | b₂₃ ) <;>
          norm_num [ Fin.ext_iff, Matrix.vecHead, Matrix.vecTail ] at *
        · rcases b₁ 6 with ( _ | _ | b₁₆ ) <;>
            rcases b₂ 6 with ( _ | _ | b₂₆ ) <;>
            norm_num [ Fin.ext_iff, Matrix.vecHead, Matrix.vecTail ] at *
        · linarith;
        · rcases b₁ 6 with ( _ | _ | b₁₆ ) <;>
            rcases b₂ 6 with ( _ | _ | b₂₆ ) <;>
            norm_num [ Fin.ext_iff, Matrix.vecHead, Matrix.vecTail ] at *
        · linarith;
      · linarith;
      · rcases b₁ 3 with ( _ | _ | b₁₃ ) <;>
          rcases b₂ 3 with ( _ | _ | b₂₃ ) <;>
          norm_num [ Fin.ext_iff, Matrix.vecHead, Matrix.vecTail ] at *
        · rcases b₁ 6 with ( _ | _ | b₁₆ ) <;>
            rcases b₂ 6 with ( _ | _ | b₂₆ ) <;>
            norm_num [ Fin.ext_iff, Matrix.vecHead, Matrix.vecTail ] at *
        · linarith;
        · rcases b₁ 6 with ( _ | _ | b₁₆ ) <;>
            rcases b₂ 6 with ( _ | _ | b₂₆ ) <;>
            norm_num [ Fin.ext_iff, Matrix.vecHead, Matrix.vecTail ] at *
        · linarith;
      · linarith;
    · grind

set_option maxHeartbeats 1000000 in
-- Closure-induction here combines several heavy conjugation lemmas; keeping a larger heartbeat
-- budget avoids intermittent tactic timeouts in the composed simplification steps.
/-- Transversal S is a logical gate for the Steane code. -/
theorem transversalS_Steane7_isLogicalGate :
    IsLogicalGate transversalS_Steane7 stabilizerGroup := by
  rw [isLogicalGate_iff_conjugation]
  intro g hg ψ hψ
  have h_conjugate : ∀ g' ∈ stabilizerGroup.toSubgroup,
      ∃ g'' ∈ stabilizerGroup.toSubgroup,
        transversalS_Steane7.val * g'.toMatrix * star transversalS_Steane7.val = g''.toMatrix := by
    intro g' hg';
    induction hg' using Subgroup.closure_induction
    · rename_i g' hg'
      obtain ⟨i, hi⟩ : ∃ i : Fin 6, g' = generatorsList.get i := by
        rw [NQubitPauliGroupElement.listToSet] at hg';
        rw [ Set.mem_setOf_eq, List.mem_iff_get ] at hg' ; aesop;
      fin_cases i <;>
        simp_all +decide [ Quantum.StabilizerGroup.Steane7.stabilizerGroup_toSubgroup_eq ];
      all_goals simp_all +decide [ Quantum.StabilizerGroup.Steane7.generatorsList ];
      exact ⟨ _, Subgroup.subset_closure ( Set.mem_union_left _ ( Set.mem_insert _ _ ) ),
        Steane7.transversalS_conjugates_Z_generator _ ( Set.mem_insert _ _ ) ⟩;
      · exact ⟨ _,
          Subgroup.subset_closure
            (Set.mem_union_left _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))),
          Steane7.transversalS_conjugates_Z_generator _
            (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) ⟩;
      · exact ⟨ _,
          Subgroup.subset_closure
            (Set.mem_union_left _
              (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))),
          Steane7.transversalS_conjugates_Z_generator _
            (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) ⟩;
      · exact ⟨ _,
          Subgroup.mul_mem _
            (Subgroup.subset_closure (Set.mem_union_right _ (Set.mem_insert _ _)))
            (Subgroup.subset_closure (Set.mem_union_left _ (Set.mem_insert _ _))),
          Steane7.transversalS_conjugates_X1 ⟩;
      · exact ⟨ X2 * Z2,
          Subgroup.mul_mem _
            (Subgroup.subset_closure
              (Set.mem_union_right _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
            (Subgroup.subset_closure
              (Set.mem_union_left _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))),
          Steane7.transversalS_conjugates_X2 ⟩;
      · exact ⟨ _,
          Subgroup.mul_mem _
            (Subgroup.subset_closure
              (Set.mem_union_right _
                (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))))
            (Subgroup.subset_closure
              (Set.mem_union_left _
                (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))),
          Steane7.transversalS_conjugates_X3 ⟩;
    · refine ⟨ 1, Subgroup.one_mem _, ?_ ⟩
      have hU : transversalS_Steane7.val * star transversalS_Steane7.val = 1 :=
        Matrix.mem_unitaryGroup_iff.1 transversalS_Steane7.2
      rw [Quantum.NQubitPauliGroupElement.toMatrix_one]
      simp
    · rename_i h₁ h₂ h₃ h₄
      obtain ⟨ g'', hg'', hconj_x ⟩ := h₃
      obtain ⟨ g''', hg''', hconj_y ⟩ := h₄
      use g'' * g''';
      exact ⟨ Subgroup.mul_mem _ hg'' hg''', by
        rw [ NQubitPauliGroupElement.toMatrix_mul ];
        rw [ NQubitPauliGroupElement.toMatrix_mul ];
        simp +decide only [← mul_assoc, ← hconj_x, ← hconj_y];
        simp +decide [ mul_assoc, Quantum.StabilizerGroup.Steane7.transversalS_Steane7 ] ⟩;
    · rename_i g'' hg'' h_conj
      obtain ⟨ g'', hg'', hg''' ⟩ := h_conj
      refine ⟨ g''⁻¹, Subgroup.inv_mem _ hg'', ?_ ⟩
      convert congr_arg Star.star hg''' using 1 <;> norm_num [ Matrix.mul_assoc, Matrix.star_mul ];
      · congr! 2;
        convert NQubitPauliGroupElement.toMatrix_inv _ using 1;
        rw [ Matrix.inv_eq_left_inv ];
        have h_unitary :
            ∀ (g : NQubitPauliGroupElement 7),
              g.toMatrix ∈ Matrix.unitaryGroup (NQubitBasis 7) ℂ := by
          intro g; exact (by
          convert g.toGate.2 using 1;
          exact Eq.symm (NQubitPauliGroupElement.toGate_val g));
        exact h_unitary _ |>.1;
      · convert NQubitPauliGroupElement.toMatrix_inv g'' using 1;
        rw [ Matrix.inv_eq_left_inv ];
        convert g''.toGate.2.2 using 1;
        simp +decide [ NQubitPauliGroupElement.toGate_val, NQubitPauliGroupElement.toMatrix ];
        rw [ show g''.operators.toMatrix * Star.star g''.operators.toMatrix = 1 from ?_,
          show Star.star g''.operators.toMatrix * g''.operators.toMatrix = 1 from ?_ ];
        · rw [ SMulCommClass.smul_comm ];
        · have := g''.operators.toMatrix_mem_unitaryGroup
          simp_all +decide [ Matrix.mem_unitaryGroup_iff ]
        · have := NQubitPauliOperator.toMatrix_mem_unitaryGroup g''.operators; aesop;
  obtain ⟨g', hg', heq⟩ := h_conjugate g hg
  rw [ heq ];
  convert hψ g' hg' using 1

/-- Transversal `S†` (implemented as `inv_S` on each qubit) acts as logical phase `S` on the
canonical Steane logical pair under the convention `Ȳ := i X̄ Z̄`. -/
theorem transversalS_Steane7_isLogicalS :
    LogicalQubitOps.IsLogicalS
      ⟨logicalX, logicalZ, logicalX_mem_centralizer, logicalZ_mem_centralizer,
        logicalX_anticommutes_logicalZ⟩
      transversalS_Steane7 := by
  refine ⟨transversalS_Steane7_isLogicalGate, ?_, ?_⟩
  · change (uniformTransversalGateMatrix 7 inv_S) * logicalZ.toMatrix *
      star (uniformTransversalGateMatrix 7 inv_S) = logicalZ.toMatrix
    simpa [logicalZ, NQubitPauliGroupElement.toMatrix, PauliGroupElement.phasePowerToComplex] using
      (uniformTransversalGateMatrix_inv_S_conj_Z_op 7 (NQubitPauliOperator.Z 7)
        (by intro i; exact Or.inl rfl))
  · change (uniformTransversalGateMatrix 7 inv_S) * logicalX.toMatrix *
      star (uniformTransversalGateMatrix 7 inv_S) =
      (LogicalQubitOps.logicalY
        ⟨logicalX, logicalZ, logicalX_mem_centralizer, logicalZ_mem_centralizer,
          logicalX_anticommutes_logicalZ⟩).toMatrix
    change (uniformTransversalGateMatrix 7 inv_S) * logicalX.toMatrix *
      star (uniformTransversalGateMatrix 7 inv_S) = logicalY.toMatrix
    have hX :
        logicalX.toMatrix = (NQubitPauliOperator.X 7).toMatrix := by
      simp [logicalX, NQubitPauliGroupElement.toMatrix, PauliGroupElement.phasePowerToComplex]
    rw [hX, uniformTransversalGateMatrix_inv_S_conj_allX]
    have hpow : ((-1 : ℂ) ^ 7) = -1 := by norm_num
    simp [logicalY_eq_phase2_allY, NQubitPauliGroupElement.toMatrix,
      PauliGroupElement.phasePowerToComplex, hpow]


end Steane7
end StabilizerGroup
end Quantum
