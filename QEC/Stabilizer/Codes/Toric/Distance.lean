import Mathlib.Tactic
import QEC.Stabilizer.Codes.Toric.DistanceX
import QEC.Stabilizer.Codes.Toric.DistanceZ
import QEC.Stabilizer.Codes.Toric.StabilizerCode
import QEC.Stabilizer.Codes.Toric.LogicalCorrespondenceZ
import QEC.Stabilizer.Codes.Toric.ChainComplex
import QEC.Stabilizer.Framework.Homological.Distance
import QEC.Stabilizer.Foundations.PauliGroup.NQubitElement
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance

namespace Quantum
namespace StabilizerGroup
namespace ToricCodeN

open scoped BigOperators
open NQubitPauliGroupElement
  Quantum.Stabilizer.Homological.HomologicalCode

/-!
# Full toric-code distance = L

Combines the X-distance (from `ToricCodeNDistanceX`) and Z-distance (from
`ToricCodeNDistanceZ`) via the abstract CSS bridge on `HomologicalCode` to
obtain the full distance.

The entire CSS-bridge machinery — centralizer ⇒ cycles, weight bridges, and "not
both boundary" — lives in `Stabilizer.Homological.Distance`. This file just
plugs the toric `HomologicalCode` instance into that machinery and combines the
result with the toric X- / Z-distance witnesses.
-/

variable (L : ℕ) [Fact (2 ≤ L)]

/-! ## CSS bridge: full distance = min(dX, dZ) -/

/-- CSS bridge: full distance = min(dX, dZ). -/
theorem toricCodeN_distance_eq_min_dX_dZ (dX dZ : ℕ)
    (hx : HasToricXDistance L dX) (hz : HasToricZDistance L dZ) :
    HasCodeDistance (toricStabilizerCode L) (Nat.min dX dZ) := by
  have hL0 : 0 < L := Nat.lt_of_lt_of_le (by decide : 0 < 2) (Fact.out : 2 ≤ L)
  haveI : Fact (0 < L) := ⟨hL0⟩
  obtain ⟨hdXpos, hxLB, hxWit⟩ := hx
  obtain ⟨hdZpos, hzLB, hzWit⟩ := hz
  -- Translate `IsNontrivialLogicalOperator g (toricStabilizerCode L).toStabilizerGroup`
  -- to `IsNontrivialLogicalOperator g (stabilizerGroup L)` via the subgroup equality.
  have h_subgroup_eq := toricStabilizerCode_subgroup_eq L
  have h_iff : ∀ g, IsNontrivialLogicalOperator g (toricStabilizerCode L).toStabilizerGroup ↔
      IsNontrivialLogicalOperator g (stabilizerGroup L) :=
    fun g => IsNontrivialLogicalOperator_of_toSubgroup_eq g h_subgroup_eq
  -- Bridge to the abstract homological stabilizer group.
  have h_sub_eq_hom :
      (stabilizerGroup L).toSubgroup =
        (Stabilizer.Lattice.toricHomologicalCode L).homologicalStabilizerGroup.toSubgroup :=
    (Stabilizer.Lattice.toricHomologicalCode_homologicalStabilizerGroup_toSubgroup_eq L).symm
  have h_iff_hom : ∀ g, IsNontrivialLogicalOperator g (stabilizerGroup L) ↔
      IsNontrivialLogicalOperator g
        (Stabilizer.Lattice.toricHomologicalCode L).homologicalStabilizerGroup :=
    fun g => IsNontrivialLogicalOperator_of_toSubgroup_eq g h_sub_eq_hom
  have h_cent_eq :
      centralizer (Stabilizer.Lattice.toricHomologicalCode L).homologicalStabilizerGroup =
        centralizer (stabilizerGroup L) :=
    centralizer_eq_of_toSubgroup_eq _ _ h_sub_eq_hom.symm
  refine ⟨le_min hdXpos hdZpos, ?_, ?_⟩
  · -- Lower bound
    intro g hgLogical' _hgwpos
    have hgLogical := (h_iff g).mp hgLogical'
    have hgLogical_hom := (h_iff_hom g).mp hgLogical
    have hg_cent : g ∈ centralizer (stabilizerGroup L) :=
      (IsNontrivialLogicalOperator_iff g (stabilizerGroup L)).mp hgLogical |>.1
    have hg_cent_hom :
        g ∈ centralizer
          (Stabilizer.Lattice.toricHomologicalCode L).homologicalStabilizerGroup := by
      rw [h_cent_eq]; exact hg_cent
    -- Apply the abstract CSS bridge.
    have h_not_both := not_both_boundary_of_nontrivial
      (X := Stabilizer.Lattice.toricHomologicalCode L) g hgLogical_hom
    -- xChainOf g ∈ cycles, zChainOf g ∈ dualCycles
    have hxCyc := xChainOf_mem_cycles_of_centralizer
      (X := Stabilizer.Lattice.toricHomologicalCode L) g hg_cent_hom
    have hzCyc := zChainOf_mem_dualCycles_of_centralizer
      (X := Stabilizer.Lattice.toricHomologicalCode L) g hg_cent_hom
    by_cases hxBnd : (Stabilizer.Lattice.toricHomologicalCode L).xChainOf g ∈
        (Stabilizer.Lattice.toricHomologicalCode L).boundaries
    · -- Then zChainOf g ∉ dualBoundaries — use Z-distance bound.
      have hzBnd : (Stabilizer.Lattice.toricHomologicalCode L).zChainOf g ∉
          (Stabilizer.Lattice.toricHomologicalCode L).dualBoundaries := by
        intro h; exact h_not_both ⟨hxBnd, h⟩
      -- chainZOperator (zChainOf g) is a Z-type non-trivial logical.
      set gZ : NQubitPauliGroupElement (numQubits L) :=
        (Stabilizer.Lattice.toricHomologicalCode L).chainZOperator
          ((Stabilizer.Lattice.toricHomologicalCode L).zChainOf g) with hgZ_def
      have hgZ_isZType : NQubitPauliGroupElement.IsZTypeElement gZ :=
        chainZOperator_isZType (X := Stabilizer.Lattice.toricHomologicalCode L) _
      have hgZ_nl_hom :
          IsNontrivialLogicalOperator gZ
            (Stabilizer.Lattice.toricHomologicalCode L).homologicalStabilizerGroup :=
        (chainZOperator_isNontrivialLogical_iff
          (X := Stabilizer.Lattice.toricHomologicalCode L)
          ((Stabilizer.Lattice.toricHomologicalCode L).zChainOf g)).mpr ⟨hzCyc, hzBnd⟩
      have hgZ_nl : IsNontrivialLogicalOperator gZ (stabilizerGroup L) :=
        (h_iff_hom gZ).mpr hgZ_nl_hom
      -- Need 0 < weight gZ for the Z-distance lower bound to apply.
      have h_gZ_pos : 0 < weight gZ := by
        change 0 < NQubitPauliGroupElement.weight
            ((Stabilizer.Lattice.toricHomologicalCode L).chainZOperator
              ((Stabilizer.Lattice.toricHomologicalCode L).zChainOf g))
        rw [weight_chainZOperator (X := Stabilizer.Lattice.toricHomologicalCode L)]
        unfold chainWeight chainSupport
        rw [Finset.card_pos]
        by_contra hempty
        rw [Finset.not_nonempty_iff_eq_empty] at hempty
        apply hzBnd
        have h_eq : (Stabilizer.Lattice.toricHomologicalCode L).zChainOf g = 0 := by
          funext e
          change (Stabilizer.Lattice.toricHomologicalCode L).zChainOf g e = (0 : ZMod 2)
          by_contra hne
          have hmem : e ∈
              (Finset.univ : Finset (Stabilizer.Lattice.toricHomologicalCode L).C1).filter
                (fun e => (Stabilizer.Lattice.toricHomologicalCode L).zChainOf g e ≠ 0) := by
            simp [hne]
          rw [hempty] at hmem
          exact (Finset.notMem_empty _ hmem)
        rw [h_eq]; exact Submodule.zero_mem _
      have hwz : weight g ≥ dZ := by
        calc weight g
            ≥ (Stabilizer.Lattice.toricHomologicalCode L).chainWeight
                ((Stabilizer.Lattice.toricHomologicalCode L).zChainOf g) :=
              weight_ge_chainWeight_zChainOf
                (X := Stabilizer.Lattice.toricHomologicalCode L) g
          _ = weight gZ :=
              (weight_chainZOperator
                (X := Stabilizer.Lattice.toricHomologicalCode L) _).symm
          _ ≥ dZ := hzLB _ hgZ_isZType hgZ_nl h_gZ_pos
      exact le_trans (Nat.min_le_right _ _) hwz
    · -- xChainOf g ∉ boundaries — use X-distance bound.
      set gX : NQubitPauliGroupElement (numQubits L) :=
        (Stabilizer.Lattice.toricHomologicalCode L).chainXOperator
          ((Stabilizer.Lattice.toricHomologicalCode L).xChainOf g) with hgX_def
      have hgX_isXType : NQubitPauliGroupElement.IsXTypeElement gX :=
        chainXOperator_isXType (X := Stabilizer.Lattice.toricHomologicalCode L) _
      have hgX_nl_hom :
          IsNontrivialLogicalOperator gX
            (Stabilizer.Lattice.toricHomologicalCode L).homologicalStabilizerGroup :=
        (chainXOperator_isNontrivialLogical_iff
          (X := Stabilizer.Lattice.toricHomologicalCode L)
          ((Stabilizer.Lattice.toricHomologicalCode L).xChainOf g)).mpr ⟨hxCyc, hxBnd⟩
      have hgX_nl : IsNontrivialLogicalOperator gX (stabilizerGroup L) :=
        (h_iff_hom gX).mpr hgX_nl_hom
      have h_gX_pos : 0 < weight gX := by
        change 0 < NQubitPauliGroupElement.weight
            ((Stabilizer.Lattice.toricHomologicalCode L).chainXOperator
              ((Stabilizer.Lattice.toricHomologicalCode L).xChainOf g))
        rw [weight_chainXOperator (X := Stabilizer.Lattice.toricHomologicalCode L)]
        unfold chainWeight chainSupport
        rw [Finset.card_pos]
        by_contra hempty
        rw [Finset.not_nonempty_iff_eq_empty] at hempty
        apply hxBnd
        have h_eq : (Stabilizer.Lattice.toricHomologicalCode L).xChainOf g = 0 := by
          funext e
          change (Stabilizer.Lattice.toricHomologicalCode L).xChainOf g e = (0 : ZMod 2)
          by_contra hne
          have hmem : e ∈
              (Finset.univ : Finset (Stabilizer.Lattice.toricHomologicalCode L).C1).filter
                (fun e => (Stabilizer.Lattice.toricHomologicalCode L).xChainOf g e ≠ 0) := by
            simp [hne]
          rw [hempty] at hmem
          exact (Finset.notMem_empty _ hmem)
        rw [h_eq]; exact Submodule.zero_mem _
      have hwx : weight g ≥ dX := by
        calc weight g
            ≥ (Stabilizer.Lattice.toricHomologicalCode L).chainWeight
                ((Stabilizer.Lattice.toricHomologicalCode L).xChainOf g) :=
              weight_ge_chainWeight_xChainOf
                (X := Stabilizer.Lattice.toricHomologicalCode L) g
          _ = weight gX :=
              (weight_chainXOperator
                (X := Stabilizer.Lattice.toricHomologicalCode L) _).symm
          _ ≥ dX := hxLB _ hgX_isXType hgX_nl h_gX_pos
      exact le_trans (Nat.min_le_left _ _) hwx
  · -- Witness
    by_cases hle : dX ≤ dZ
    · obtain ⟨g, _, hg_logical, hg_weight⟩ := hxWit
      refine ⟨g, (h_iff g).mpr hg_logical, ?_⟩
      rw [hg_weight]; exact (Nat.min_eq_left hle).symm
    · push Not at hle
      obtain ⟨g, _, hg_logical, hg_weight⟩ := hzWit
      refine ⟨g, (h_iff g).mpr hg_logical, ?_⟩
      rw [hg_weight]; exact (Nat.min_eq_right (le_of_lt hle)).symm

/-! ## Full distance = L -/

/-- Section 8.3 endpoint: the full toric-code distance is `L`. -/
theorem toricCodeN_distance_eq_L :
    HasCodeDistance (toricStabilizerCode L) L := by
  have hx : HasToricXDistance L L := toricCodeN_dX_eq_L L
  have hz : HasToricZDistance L L := toricCodeN_dZ_eq_L L
  simpa using toricCodeN_distance_eq_min_dX_dZ L L L hx hz

/-- The toric code on an `L × L` lattice packaged as a `[[2L², 2, L]]`
stabilizer code with distance. -/
noncomputable def toricStabilizerCodeWithDistance :
    StabilizerCodeWithDistance (2 * L * L) 2 L where
  toStabilizerCode := toricStabilizerCode L
  hasDistance      := toricCodeN_distance_eq_L L

end ToricCodeN
end StabilizerGroup
end Quantum
