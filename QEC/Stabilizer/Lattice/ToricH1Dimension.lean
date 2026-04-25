import Mathlib.Tactic
import QEC.Stabilizer.Lattice.ToricHomology

namespace Quantum
namespace Stabilizer
namespace Lattice

open scoped BigOperators

variable (L : ℕ) [Fact (0 < L)]

/-- The boundary submodule viewed inside the cycle submodule (`B₁` as a submodule of `Z₁`). -/
abbrev toricBoundarySubmoduleInCycles : Submodule (ZMod 2) (toricCycles (L := L)) :=
  Submodule.comap (toricCycles (L := L)).subtype (toricBoundaries (L := L))

/-- Finrank of the toric 0-chain space. -/
theorem toric_finrank_C0 :
    Module.finrank (ZMod 2) (C0 L) = L * L := by
  let _ := (Fact.out : 0 < L)
  calc
    Module.finrank (ZMod 2) (C0 L) = Fintype.card (VtxIdx L) := by
      exact Module.finrank_fintype_fun_eq_card (R := ZMod 2) (η := VtxIdx L)
    _ = L * L := by simp

/-- Finrank of the toric 1-chain space. -/
theorem toric_finrank_C1 :
    Module.finrank (ZMod 2) (C1 L) = 2 * L * L := by
  let _ := (Fact.out : 0 < L)
  calc
    Module.finrank (ZMod 2) (C1 L) = Fintype.card (EdgeIdx L) := by
      exact Module.finrank_fintype_fun_eq_card (R := ZMod 2) (η := EdgeIdx L)
    _ = 2 * L * L := by simp

/-- Finrank of the toric 2-chain space. -/
theorem toric_finrank_C2 :
    Module.finrank (ZMod 2) (C2 L) = L * L := by
  let _ := (Fact.out : 0 < L)
  calc
    Module.finrank (ZMod 2) (C2 L) = Fintype.card (FaceIdx L) := by
      exact Module.finrank_fintype_fun_eq_card (R := ZMod 2) (η := FaceIdx L)
    _ = L * L := by simp

/-- `B₁ ≤ Z₁` for the toric chain complex. -/
theorem toric_boundaries_le_cycles :
    toricBoundaries (L := L) ≤ toricCycles (L := L) := by
  simpa using toricBoundaries_le_toricCycles (L := L)

/-- Rank-nullity specialization for `∂₁`. -/
theorem toric_rank_nullity_boundary1 :
    Module.finrank (ZMod 2) (C1 L) =
      Module.finrank (ZMod 2) (toricCycles (L := L)) +
        Module.finrank (ZMod 2) (LinearMap.range (toricBoundary1 (L := L))) := by
  simpa [toricCycles, add_comm, add_left_comm, add_assoc] using
    (LinearMap.finrank_range_add_finrank_ker (toricBoundary1 (L := L))).symm

/-- Rank-nullity specialization for `∂₂`. -/
theorem toric_rank_nullity_boundary2 :
    Module.finrank (ZMod 2) (C2 L) =
      Module.finrank (ZMod 2) (LinearMap.ker (toricBoundary2 (L := L))) +
        Module.finrank (ZMod 2) (toricBoundaries (L := L)) := by
  simpa [toricBoundaries, add_comm, add_left_comm, add_assoc] using
    (LinearMap.finrank_range_add_finrank_ker (toricBoundary2 (L := L))).symm

/-- Auxiliary map placeholder for the transpose/cut-map route used to compute `rank(∂₁)`. -/
noncomputable def toricVertexCutMap : C0 L →ₗ[ZMod 2] C1 L := by
  refine
    { toFun := fun s =>
        fun e =>
          match e with
          | EdgeIdx.h x y => s (x, y) + s (next L x, y)
          | EdgeIdx.v x y => s (x, y) + s (x, next L y)
      map_add' := ?_
      map_smul' := ?_ }
  · intro s t
    ext e
    cases e <;> simp [add_assoc, add_left_comm, add_comm]
  · intro a s
    ext e
    cases e <;> simp [mul_add]

/-- Bridge theorem placeholder between `∂₁` rank and cut-map rank. -/
theorem toric_rank_boundary1_eq_rank_cutMap :
    Module.finrank (ZMod 2) (LinearMap.range (toricBoundary1 (L := L))) =
      Module.finrank (ZMod 2) (LinearMap.range (toricVertexCutMap (L := L))) := by
  sorry

/-- Kernel-dimension placeholder for the cut-map connectivity argument. -/
theorem toric_finrank_ker_cutMap_eq_one :
    Module.finrank (ZMod 2) (LinearMap.ker (toricVertexCutMap (L := L))) = 1 := by
  sorry

/-- Target rank formula for `∂₁`. -/
theorem toric_rank_boundary1 :
    Module.finrank (ZMod 2) (LinearMap.range (toricBoundary1 (L := L))) = L * L - 1 := by
  have hcut_rk :
      Module.finrank (ZMod 2) (LinearMap.range (toricVertexCutMap (L := L))) = L * L - 1 := by
    have hcut_rn := LinearMap.finrank_range_add_finrank_ker (toricVertexCutMap (L := L))
    have hC0 := toric_finrank_C0 (L := L)
    have hker := toric_finrank_ker_cutMap_eq_one (L := L)
    omega
  have hbridge := toric_rank_boundary1_eq_rank_cutMap (L := L)
  omega

/-- Target cycle-space dimension formula. -/
theorem toric_finrank_cycles :
    Module.finrank (ZMod 2) (toricCycles (L := L)) = L * L + 1 := by
  have hrn := toric_rank_nullity_boundary1 (L := L)
  have hC1 := toric_finrank_C1 (L := L)
  have hrk := toric_rank_boundary1 (L := L)
  rw [hC1, hrk] at hrn
  have hEq : Module.finrank (ZMod 2) (toricCycles (L := L)) + (L * L - 1) = 2 * L * L := by
    simpa [add_comm, add_left_comm, add_assoc] using hrn.symm
  have hsq : 1 ≤ L * L := by
    have hL : 0 < L := Fact.out
    exact Nat.succ_le_of_lt (Nat.mul_pos hL hL)
  have hsplit : (L * L + 1) + (L * L - 1) = 2 * L * L := by
    calc
      (L * L + 1) + (L * L - 1) = ((L * L - 1) + 1) + (L * L) := by
        ac_rfl
      _ = (L * L) + (L * L) := by
        rw [Nat.sub_add_cancel hsq]
      _ = 2 * L * L := by ring
  have : Module.finrank (ZMod 2) (toricCycles (L := L)) + (L * L - 1) =
      (L * L + 1) + (L * L - 1) := by
    exact hEq.trans hsplit.symm
  exact Nat.add_right_cancel this

/-- Kernel-dimension placeholder for `∂₂`. -/
theorem toric_finrank_ker_boundary2_eq_one :
    Module.finrank (ZMod 2) (LinearMap.ker (toricBoundary2 (L := L))) = 1 := by
  sorry

/-- Target boundary-space dimension formula. -/
theorem toric_finrank_boundaries :
    Module.finrank (ZMod 2) (toricBoundaries (L := L)) = L * L - 1 := by
  have hrn := toric_rank_nullity_boundary2 (L := L)
  have hC2 := toric_finrank_C2 (L := L)
  have hker := toric_finrank_ker_boundary2_eq_one (L := L)
  omega

/-- Quotient-dimension bridge for `H₁ = Z₁ / B₁`. -/
theorem toric_finrank_H1_eq_cycles_sub_boundaries
    :
    @Module.finrank (ZMod 2) (toricH1 (L := L)) _
      (Submodule.Quotient.addCommGroup (toricBoundarySubmoduleInCycles (L := L))).toAddCommMonoid
      (Submodule.Quotient.module (toricBoundarySubmoduleInCycles (L := L))) =
      Module.finrank (ZMod 2) (toricCycles (L := L)) -
        Module.finrank (ZMod 2) (toricBoundaries (L := L)) := by
  have hquot :
      @Module.finrank (ZMod 2) (toricH1 (L := L)) _
          (Submodule.Quotient.addCommGroup
            (toricBoundarySubmoduleInCycles (L := L))).toAddCommMonoid
          (Submodule.Quotient.module (toricBoundarySubmoduleInCycles (L := L))) +
          Module.finrank (ZMod 2) (toricBoundarySubmoduleInCycles (L := L)) =
        Module.finrank (ZMod 2) (toricCycles (L := L)) := by
    simpa [toricH1, toricBoundarySubmoduleInCycles] using
      (Submodule.finrank_quotient_add_finrank (R := ZMod 2)
        (toricBoundarySubmoduleInCycles (L := L)))
  have hcomap :
      Module.finrank (ZMod 2) (toricBoundarySubmoduleInCycles (L := L)) =
        Module.finrank (ZMod 2) (toricBoundaries (L := L)) := by
    simpa [toricBoundarySubmoduleInCycles] using
      (Submodule.comapSubtypeEquivOfLe (toric_boundaries_le_cycles (L := L))).finrank_eq
  rw [hcomap] at hquot
  exact Nat.eq_sub_of_add_eq hquot

/-- `dim(H₁) = 2` for the toric chain complex over `ZMod 2`. -/
theorem toric_finrank_H1_eq_two
    :
    @Module.finrank (ZMod 2) (toricH1 (L := L)) _
      (Submodule.Quotient.addCommGroup (toricBoundarySubmoduleInCycles (L := L))).toAddCommMonoid
      (Submodule.Quotient.module (toricBoundarySubmoduleInCycles (L := L))) = 2 := by
  have hH := toric_finrank_H1_eq_cycles_sub_boundaries (L := L)
  have hC := toric_finrank_cycles (L := L)
  have hB := toric_finrank_boundaries (L := L)
  rw [hC, hB] at hH
  have hsq : 1 ≤ L * L := by
    have hL : 0 < L := Fact.out
    exact Nat.succ_le_of_lt (Nat.mul_pos hL hL)
  have hcalc : (L * L + 1) - (L * L - 1) = 2 := by
    omega
  simpa [hcalc] using hH

end Lattice
end Stabilizer
end Quantum
