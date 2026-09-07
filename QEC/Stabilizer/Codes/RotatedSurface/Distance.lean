import Mathlib.Tactic
import QEC.Stabilizer.Codes.RotatedSurface.DistanceX
import QEC.Stabilizer.Codes.RotatedSurface.DistanceZ
import QEC.Stabilizer.Codes.RotatedSurface.StabilizerCode
import QEC.Stabilizer.Framework.Homological.Distance
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance

/-!
# Stage 7 — Combined rotated-surface-code distance = `L`

Combines the X-distance ≥ L (`RotatedSurfaceCodeNDistanceX`) and the Z-distance
≥ L (`RotatedSurfaceCodeNDistanceZ`) via the generic CSS bridge on
`HomologicalCode` to obtain
`HasCodeDistance (rotatedSurfaceStabilizerCode L) L`.

The entire CSS-bridge machinery — centralizer ⇒ cycles, weight bridges, and the
"not both boundary" lemma — lives in `Stabilizer.Homological.Distance`. This
file just plugs the rotated-surface `HomologicalCode` instance into that
machinery and combines the result with the Stage 5/6 weight bounds.
-/

namespace Quantum
namespace StabilizerGroup
namespace RotatedSurfaceCodeN

open scoped BigOperators
open NQubitPauliGroupElement Stabilizer.Lattice.RotatedSurface
  Quantum.Stabilizer.Homological.HomologicalCode

variable (L : ℕ) [Fact (Odd L)] [Fact (3 ≤ L)]

/-- **Stage 7 endpoint.** The rotated surface code on an `L × L` lattice has
code distance exactly `L`. -/
theorem rotatedSurfaceCodeN_distance_eq_L :
    HasCodeDistance (rotatedSurfaceStabilizerCode L) L := by
  have hL_pos : 0 < L := by have h3 : 3 ≤ L := Fact.out; omega
  -- Bridge: the StabilizerCode subgroup equals the homological one.
  have h_sub_eq := rotatedSurfaceStabilizerCode_subgroup_eq_homological L
  -- Bridge `IsNontrivialLogicalOperator` between the two groups.
  have h_iff_NL : ∀ g,
      Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
          (rotatedSurfaceStabilizerCode L).toStabilizerGroup ↔
        Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
          (rotatedSurfaceHomologicalCode L).homologicalStabilizerGroup :=
    fun g => Quantum.StabilizerGroup.IsNontrivialLogicalOperator_of_toSubgroup_eq g h_sub_eq
  refine ⟨hL_pos, ?_, ?_⟩
  · -- Lower bound: every non-trivial logical has weight ≥ L.
    intro g hgLogical _hgwpos
    have hg_hom := (h_iff_NL g).mp hgLogical
    have hg_cent_hom :
        g ∈ Quantum.StabilizerGroup.centralizer
          (rotatedSurfaceHomologicalCode L).homologicalStabilizerGroup :=
      ((Quantum.StabilizerGroup.IsNontrivialLogicalOperator_iff g _).mp hg_hom).1
    -- Apply the abstract CSS bridge: not both boundary.
    have h_not_both :=
      not_both_boundary_of_nontrivial (X := rotatedSurfaceHomologicalCode L) g hg_hom
    -- xChainOf g ∈ cycles, zChainOf g ∈ dualCycles — generic.
    have hxCyc := xChainOf_mem_cycles_of_centralizer
      (X := rotatedSurfaceHomologicalCode L) g hg_cent_hom
    have hzCyc := zChainOf_mem_dualCycles_of_centralizer
      (X := rotatedSurfaceHomologicalCode L) g hg_cent_hom
    -- Case on whether xChainOf g is a boundary.
    by_cases hxBnd : (rotatedSurfaceHomologicalCode L).xChainOf g ∈
        (rotatedSurfaceHomologicalCode L).boundaries
    · -- Then zChainOf g ∉ dualBoundaries — use Z-distance bound.
      have hzBnd : (rotatedSurfaceHomologicalCode L).zChainOf g ∉
          (rotatedSurfaceHomologicalCode L).dualBoundaries := by
        intro h; exact h_not_both ⟨hxBnd, h⟩
      -- chainZOperator (zChainOf g) is a Z-type non-trivial logical.
      set gZ : NQubitPauliGroupElement (numQubits L) :=
        (rotatedSurfaceHomologicalCode L).chainZOperator
          ((rotatedSurfaceHomologicalCode L).zChainOf g) with hgZ_def
      have hgZ_isZType : NQubitPauliGroupElement.IsZTypeElement gZ :=
        chainZOperator_isZType (X := rotatedSurfaceHomologicalCode L) _
      have hgZ_nl_hom :
          Quantum.StabilizerGroup.IsNontrivialLogicalOperator gZ
            (rotatedSurfaceHomologicalCode L).homologicalStabilizerGroup :=
        (chainZOperator_isNontrivialLogical_iff
          (X := rotatedSurfaceHomologicalCode L)
          ((rotatedSurfaceHomologicalCode L).zChainOf g)).mpr ⟨hzCyc, hzBnd⟩
      have hgZ_nl :
          Quantum.StabilizerGroup.IsNontrivialLogicalOperator gZ
            (rotatedSurfaceStabilizerCode L).toStabilizerGroup :=
        (h_iff_NL gZ).mpr hgZ_nl_hom
      have hwZ : L ≤ NQubitPauliGroupElement.weight gZ :=
        weight_ge_L_of_nontrivial_Z_logical L hgZ_isZType hgZ_nl
      have h_step1 :
          (rotatedSurfaceHomologicalCode L).chainWeight
              ((rotatedSurfaceHomologicalCode L).zChainOf g) ≤
            NQubitPauliGroupElement.weight g :=
        weight_ge_chainWeight_zChainOf (X := rotatedSurfaceHomologicalCode L) g
      have h_step2 :
          NQubitPauliGroupElement.weight gZ =
            (rotatedSurfaceHomologicalCode L).chainWeight
              ((rotatedSurfaceHomologicalCode L).zChainOf g) :=
        weight_chainZOperator (X := rotatedSurfaceHomologicalCode L) _
      omega
    · -- xChainOf g ∉ boundaries — use X-distance bound.
      set gX : NQubitPauliGroupElement (numQubits L) :=
        (rotatedSurfaceHomologicalCode L).chainXOperator
          ((rotatedSurfaceHomologicalCode L).xChainOf g) with hgX_def
      have hgX_isXType : NQubitPauliGroupElement.IsXTypeElement gX :=
        chainXOperator_isXType (X := rotatedSurfaceHomologicalCode L) _
      have hgX_nl_hom :
          Quantum.StabilizerGroup.IsNontrivialLogicalOperator gX
            (rotatedSurfaceHomologicalCode L).homologicalStabilizerGroup :=
        (chainXOperator_isNontrivialLogical_iff
          (X := rotatedSurfaceHomologicalCode L)
          ((rotatedSurfaceHomologicalCode L).xChainOf g)).mpr ⟨hxCyc, hxBnd⟩
      have hgX_nl :
          Quantum.StabilizerGroup.IsNontrivialLogicalOperator gX
            (rotatedSurfaceStabilizerCode L).toStabilizerGroup :=
        (h_iff_NL gX).mpr hgX_nl_hom
      have hwX : L ≤ NQubitPauliGroupElement.weight gX :=
        weight_ge_L_of_nontrivial_X_logical L hgX_isXType hgX_nl
      have h_step1 :
          (rotatedSurfaceHomologicalCode L).chainWeight
              ((rotatedSurfaceHomologicalCode L).xChainOf g) ≤
            NQubitPauliGroupElement.weight g :=
        weight_ge_chainWeight_xChainOf (X := rotatedSurfaceHomologicalCode L) g
      have h_step2 :
          NQubitPauliGroupElement.weight gX =
            (rotatedSurfaceHomologicalCode L).chainWeight
              ((rotatedSurfaceHomologicalCode L).xChainOf g) :=
        weight_chainXOperator (X := rotatedSurfaceHomologicalCode L) _
      omega
  · -- Witness: `logicalX L` has weight exactly L.
    refine ⟨logicalX L, ?_, ?_⟩
    · have hlogX_nl_hom :
          Quantum.StabilizerGroup.IsNontrivialLogicalOperator (logicalX L)
            (rotatedSurfaceHomologicalCode L).homologicalStabilizerGroup := by
        change Quantum.StabilizerGroup.IsNontrivialLogicalOperator
          ((rotatedSurfaceHomologicalCode L).chainXOperator (middleColChain L)) _
        exact (chainXOperator_isNontrivialLogical_iff
          (X := rotatedSurfaceHomologicalCode L) (middleColChain L)).mpr
          ⟨middleColChain_mem_cycles L, middleColChain_not_mem_boundaries L⟩
      exact (h_iff_NL (logicalX L)).mpr hlogX_nl_hom
    · exact logicalX_weight_eq_L L

/-- The rotated surface code on an `L × L` lattice packaged as a `[[L*L, 1, L]]`
stabilizer code with distance. -/
noncomputable def rotatedSurfaceStabilizerCodeWithDistance :
    StabilizerCodeWithDistance (numQubits L) 1 L where
  toStabilizerCode := rotatedSurfaceStabilizerCode L
  hasDistance      := rotatedSurfaceCodeN_distance_eq_L L

end RotatedSurfaceCodeN
end StabilizerGroup
end Quantum
