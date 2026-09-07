import QEC.Stabilizer.Codes.RotatedSurface.ChainComplex
import QEC.Stabilizer.Codes.RotatedSurface.H1Dimension
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerGroup
import QEC.Stabilizer.Framework.Core.CSS.CSSCommutationLemmas
import QEC.Stabilizer.Framework.Homological.StabGroup
import QEC.Stabilizer.Framework.Homological.LogicalCorrespondence

/-!
# Parametric rotated surface code on an `L × L` lattice (`L` odd, `L ≥ 3`)

This file defines the lattice-side stabilizer generators for the rotated surface
code, delegating commutation and the no-`-I` property to the generic
`HomologicalCode` abstraction on `rotatedSurfaceHomologicalCode L`.

The full `StabilizerCode (L*L) 1` packaging is built in
[RotatedSurfaceCodeNStabilizerCode.lean](RotatedSurfaceCodeNStabilizerCode.lean).

## Design

The Z-stabilizer at a Z-face `zf : ZFaceIdx L` and the X-stabilizer at an X-face
`xf : XFaceIdx L` are defined directly as the corresponding
`HomologicalCode.vertexStabOf` / `faceStabOf`. This pins every concrete
generator to its abstract counterpart by definition, so the generator-set
bridges below are all `rfl`.

Since the rotated surface code has no redundant generators (we proved
`rscBoundary2_injective` and `rscZCutMap_injective` in Stage 3), the full
generator list has length

  `|ZFaceIdx L| + |XFaceIdx L| = L² − 1 = numQubits L − 1`,

which matches `StabilizerCode (L*L) 1`'s `generators_length` requirement
*without trimming*. Contrast the toric code, where the analogous list needs
trimming by two (one redundancy on each side).
-/

namespace Quantum
namespace StabilizerGroup
namespace RotatedSurfaceCodeN

open scoped BigOperators
open NQubitPauliGroupElement
open Stabilizer.Lattice.RotatedSurface

/-- Physical qubit count: `L × L`. -/
abbrev numQubits (L : ℕ) : ℕ := L * L

variable (L : ℕ) [Fact (Odd L)] [Fact (3 ≤ L)]

/-! ## Qubit indexing -/

/-- Data-qubit index: row-major `(x, y) ↦ y * L + x`, matching `rscQubitEquiv`.
-/
noncomputable def dataQubitIdx (v : VtxIdx L) : Fin (numQubits L) :=
  rscQubitEquiv L v

/-! ## Stabilizer generators

`zStab zf` and `xStab xf` are defined as the abstract `vertexStabOf` /
`faceStabOf` on `rotatedSurfaceHomologicalCode L`. This pins each generator to
its homological counterpart, so the bridges below are all `rfl`.
-/

/-- Z-stabilizer at face `zf`. -/
noncomputable def zStab (zf : ZFaceIdx L) : NQubitPauliGroupElement (numQubits L) :=
  (rotatedSurfaceHomologicalCode L).vertexStabOf zf

/-- X-stabilizer at face `xf`. -/
noncomputable def xStab (xf : XFaceIdx L) : NQubitPauliGroupElement (numQubits L) :=
  (rotatedSurfaceHomologicalCode L).faceStabOf xf

@[simp] lemma zStab_eq_vertexStabOf (zf : ZFaceIdx L) :
    zStab L zf = (rotatedSurfaceHomologicalCode L).vertexStabOf zf := rfl

@[simp] lemma xStab_eq_faceStabOf (xf : XFaceIdx L) :
    xStab L xf = (rotatedSurfaceHomologicalCode L).faceStabOf xf := rfl

/-- Z-type generator set: all `zStab zf` for `zf : ZFaceIdx L`. -/
noncomputable def ZGenerators : Set (NQubitPauliGroupElement (numQubits L)) :=
  Set.range (zStab L)

/-- X-type generator set: all `xStab xf` for `xf : XFaceIdx L`. -/
noncomputable def XGenerators : Set (NQubitPauliGroupElement (numQubits L)) :=
  Set.range (xStab L)

/-- The full CSS generator set. -/
noncomputable def generators : Set (NQubitPauliGroupElement (numQubits L)) :=
  ZGenerators L ∪ XGenerators L

/-- Bridge: the lattice-side Z-generators coincide with the abstract version. -/
lemma ZGenerators_eq_homologicalZGenerators :
    ZGenerators L = (rotatedSurfaceHomologicalCode L).ZGenerators := rfl

/-- Bridge: the lattice-side X-generators coincide with the abstract version. -/
lemma XGenerators_eq_homologicalXGenerators :
    XGenerators L = (rotatedSurfaceHomologicalCode L).XGenerators := rfl

/-- Bridge: the full generator set coincides with the abstract union. -/
lemma generators_eq_homologicalGenerators :
    generators L = (rotatedSurfaceHomologicalCode L).homologicalGenerators := rfl

/-! ## Generator lists

We enumerate the Z- and X-stabs via `Finset.univ.toList`. This gives lists whose
`listToSet` equals the corresponding generator set, and whose lengths are
exactly `Fintype.card (ZFaceIdx L)` and `Fintype.card (XFaceIdx L)`.
-/

/-- Canonical list of all Z-stabs (length `(L²−1)/2`). -/
noncomputable def generatorsListZ : List (NQubitPauliGroupElement (numQubits L)) :=
  (Finset.univ : Finset (ZFaceIdx L)).toList.map (zStab L)

/-- Canonical list of all X-stabs (length `(L²−1)/2`). -/
noncomputable def generatorsListX : List (NQubitPauliGroupElement (numQubits L)) :=
  (Finset.univ : Finset (XFaceIdx L)).toList.map (xStab L)

/-- Canonical list of all generators (Z stabs then X stabs, length `L² − 1`). -/
noncomputable def generatorsList : List (NQubitPauliGroupElement (numQubits L)) :=
  generatorsListZ L ++ generatorsListX L

/-! ### Length facts -/

private lemma length_finset_univ_toList {α : Type*} [Fintype α] :
    (Finset.univ : Finset α).toList.length = Fintype.card α := by
  rw [Finset.length_toList, Finset.card_univ]

lemma generatorsListZ_length :
    (generatorsListZ L).length = Fintype.card (ZFaceIdx L) := by
  simp [generatorsListZ]

lemma generatorsListX_length :
    (generatorsListX L).length = Fintype.card (XFaceIdx L) := by
  simp [generatorsListX]

lemma generatorsList_length :
    (generatorsList L).length = numQubits L - 1 := by
  unfold generatorsList numQubits
  rw [List.length_append, generatorsListZ_length, generatorsListX_length]
  exact card_ZFaceIdx_add_card_XFaceIdx (L := L)

/-! ### `listToSet` for each list -/

private lemma listToSet_map_finsetUnivToList {α : Type*} [Fintype α]
    {n : ℕ} (f : α → NQubitPauliGroupElement n) :
    listToSet ((Finset.univ : Finset α).toList.map f) = Set.range f := by
  ext g
  simp only [listToSet, Set.mem_setOf, Set.mem_range, List.mem_map,
    Finset.mem_toList, Finset.mem_univ, true_and]

lemma listToSet_generatorsListZ :
    listToSet (generatorsListZ L) = ZGenerators L := by
  unfold generatorsListZ ZGenerators
  exact listToSet_map_finsetUnivToList _

lemma listToSet_generatorsListX :
    listToSet (generatorsListX L) = XGenerators L := by
  unfold generatorsListX XGenerators
  exact listToSet_map_finsetUnivToList _

lemma listToSet_generatorsList :
    listToSet (generatorsList L) = generators L := by
  ext g
  have hZ : g ∈ listToSet (generatorsListZ L) ↔ g ∈ ZGenerators L :=
    Set.ext_iff.mp (listToSet_generatorsListZ L) g
  have hX : g ∈ listToSet (generatorsListX L) ↔ g ∈ XGenerators L :=
    Set.ext_iff.mp (listToSet_generatorsListX L) g
  constructor
  · intro hg
    -- `hg : g ∈ listToSet (generatorsListZ L ++ generatorsListX L)` unfolds to a list-mem.
    have hg' : g ∈ generatorsListZ L ++ generatorsListX L := hg
    rcases List.mem_append.mp hg' with hgZ | hgX
    · exact Or.inl (hZ.mp hgZ)
    · exact Or.inr (hX.mp hgX)
  · intro hg
    change g ∈ generatorsListZ L ++ generatorsListX L
    rcases hg with hgZ | hgX
    · exact List.mem_append_left _ (hZ.mpr hgZ)
    · exact List.mem_append_right _ (hX.mpr hgX)

/-! ### Phase-zero -/

lemma allPhaseZero_generatorsListZ : AllPhaseZero (generatorsListZ L) := by
  intro g hg
  rcases List.mem_map.mp hg with ⟨zf, _, rfl⟩
  rfl

lemma allPhaseZero_generatorsListX : AllPhaseZero (generatorsListX L) := by
  intro g hg
  rcases List.mem_map.mp hg with ⟨xf, _, rfl⟩
  rfl

lemma allPhaseZero_generatorsList : AllPhaseZero (generatorsList L) := by
  intro g hg
  rcases List.mem_append.mp hg with hZ | hX
  · exact allPhaseZero_generatorsListZ L g hZ
  · exact allPhaseZero_generatorsListX L g hX

/-! ## Commutation, no `-I`, and the canonical stabilizer group

All three properties are delegated to the generic `HomologicalCode`
infrastructure on `rotatedSurfaceHomologicalCode L`.
-/

/-- Every Z-stab is Z-type. -/
lemma zStab_is_ZType (zf : ZFaceIdx L) :
    NQubitPauliGroupElement.IsZTypeElement (zStab L zf) :=
  (rotatedSurfaceHomologicalCode L).vertexStabOf_isZType zf

/-- Every X-stab is X-type. -/
lemma xStab_is_XType (xf : XFaceIdx L) :
    NQubitPauliGroupElement.IsXTypeElement (xStab L xf) :=
  (rotatedSurfaceHomologicalCode L).faceStabOf_isXType xf

/-- Generators pairwise commute (delegated to the generic CSS argument). -/
lemma generators_commute :
    ∀ g ∈ generators L, ∀ h ∈ generators L, g * h = h * g := by
  intro g hg h hh
  exact (rotatedSurfaceHomologicalCode L).homologicalGenerators_commute g hg h hh

/-- `-I` is not in the closure of the lattice generators. -/
lemma negIdentity_not_mem :
    StabilizerGroup.negIdentity (numQubits L) ∉ Subgroup.closure (generators L) :=
  (rotatedSurfaceHomologicalCode L).negIdentity_not_mem_closure_homologicalGenerators

/-- The canonical rotated-surface stabilizer subgroup.

  Equal by definition to
  `(rotatedSurfaceHomologicalCode L).homologicalStabilizerGroup.toSubgroup`. -/
noncomputable def subgroup : Subgroup (NQubitPauliGroupElement (numQubits L)) :=
  Subgroup.closure (generators L)

lemma subgroup_eq_homologicalStabilizerGroup :
    subgroup L = (rotatedSurfaceHomologicalCode L).homologicalStabilizerGroup.toSubgroup := rfl

/-- The full lattice-side stabilizer group. -/
noncomputable def stabilizerGroup : StabilizerGroup (numQubits L) :=
  StabilizerGroup.mkStabilizerFromGenerators (numQubits L) (generatorsList L)
    (by rw [listToSet_generatorsList]; exact generators_commute L)
    (by rw [listToSet_generatorsList]; exact negIdentity_not_mem L)

lemma stabilizerGroup_toSubgroup_eq :
    (stabilizerGroup L).toSubgroup = subgroup L := by
  simp only [stabilizerGroup, StabilizerGroup.mkStabilizerFromGenerators, subgroup]
  rw [listToSet_generatorsList]

/-- The canonical stabilizer group has the same underlying subgroup as the
generic `homologicalStabilizerGroup` from `rotatedSurfaceHomologicalCode L`.

This is the key bridge that lets distance / centralizer / logical-operator
proofs run against either group interchangeably (via
`IsNontrivialLogicalOperator_of_toSubgroup_eq`). -/
lemma stabilizerGroup_toSubgroup_eq_homologicalStabilizerGroup :
    (stabilizerGroup L).toSubgroup =
      (rotatedSurfaceHomologicalCode L).homologicalStabilizerGroup.toSubgroup := by
  rw [stabilizerGroup_toSubgroup_eq, subgroup_eq_homologicalStabilizerGroup]

end RotatedSurfaceCodeN
end StabilizerGroup
end Quantum
