import QEC.Stabilizer.Codes.RotatedSurface.N
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerCode
import QEC.Stabilizer.Framework.Core.Logical.LogicalOperators
import QEC.Stabilizer.Framework.Symplectic.IndependentEquiv
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrix
import QEC.Stabilizer.Codes.RotatedSurface.H1Dimension

/-!
# Rotated surface code as `StabilizerCode (L*L, 1)`

Upgrades the lattice-side stabilizer family from
[RotatedSurfaceCodeN.lean](RotatedSurfaceCodeN.lean) to a full
`StabilizerCode (numQubits L) 1`, encoding 1 logical qubit, and bundles the
middle-column / middle-row logical pair on top of it as a
`StabilizerCodeWithLogicals` (`rotatedSurfaceStabilizerCodeWithLogicals`).

## Strategy

* **Symplectic linear independence.** The generator list has block structure: a
  Z-block (rows = `vertexStabOf zf`, Z-half = `1[v ∈ zSupport zf]`, X-half =
  `0`) followed by an X-block (rows = `faceStabOf xf`, X-half =
  `1[v ∈ xSupport xf]`, Z-half = `0`). LI of the full row family reduces to LI
  of each block, which follows immediately from `rscBoundary2_injective` and
  `rscZCutMap_injective` (proven in Stage 3): no trimming is needed because the
  rotated surface code has *no* redundant generators.

* **Logical operators.** With Z-rough left/right boundaries and X-rough
  top/bottom boundaries, the logical X is a vertical X-string at the middle
  column `x = (L−1)/2`, and the logical Z is a horizontal Z-string at the middle
  row `y = (L−1)/2`. They intersect at the centre qubit `(mid, mid)` exactly
  once, so they anticommute.
-/

namespace Quantum
namespace StabilizerGroup
namespace RotatedSurfaceCodeN

open scoped BigOperators
open scoped RotatedSurfaceChain
open NQubitPauliGroupElement
open Stabilizer.Lattice
-- Open `Lattice` to access `RotatedSurface.*` with one less prefix.
-- We do NOT open `RotatedSurface` directly to avoid the
-- `xSupport`/`zSupport` clash with the `NQubitPauliOperator` names.

variable (L : ℕ) [Fact (Odd L)] [Fact (3 ≤ L)]

/-! ## §A — `cutMap (singleVtx _)` and `boundary2 (singleFace _)` indicators

The generic `cutMap`/`boundary2`, applied to the canonical single-cell
indicators, reduce to `ZMod 2`-valued membership indicators on the corresponding
`zSupport`/`xSupport` finsets. We use these as the bridges between the abstract
symplectic check matrix and the lattice combinatorics.
-/

omit [Fact (Odd L)] [Fact (3 ≤ L)] in
/-- `rscBoundary1 (Pi.single v 1) zf = 1[v ∈ zSupport zf]`. -/
private lemma boundary1_pi_single (v : RotatedSurface.VtxIdx L)
    (zf : RotatedSurface.ZFaceIdx L) :
    ∂₁ L (Pi.single v 1) zf =
      (if v ∈ RotatedSurface.zSupport zf then (1 : ZMod 2) else 0) := by
  classical
  rw [RotatedSurface.rscBoundary1_apply]
  by_cases hv : v ∈ RotatedSurface.zSupport zf
  · rw [if_pos hv, Finset.sum_eq_single_of_mem v hv]
    · simp
    · intro u _ hne
      simp [hne]
  · rw [if_neg hv]
    apply Finset.sum_eq_zero
    intro u hu
    have hne : u ≠ v := fun heq => hv (heq ▸ hu)
    simp [hne]

/-- The cut-map of `singleVtx zf` reads off the indicator of `zSupport zf`. -/
lemma cutMap_singleVtx_apply (zf : RotatedSurface.ZFaceIdx L)
    (v : RotatedSurface.VtxIdx L) :
    (RotatedSurface.rotatedSurfaceHomologicalCode L).cutMap
        ((RotatedSurface.rotatedSurfaceHomologicalCode L).singleVtx zf) v =
      (if v ∈ RotatedSurface.zSupport zf then (1 : ZMod 2) else 0) := by
  classical
  rw [show (RotatedSurface.rotatedSurfaceHomologicalCode L).cutMap
        ((RotatedSurface.rotatedSurfaceHomologicalCode L).singleVtx zf) v =
      ∑ zf' : RotatedSurface.ZFaceIdx L,
        (RotatedSurface.rotatedSurfaceHomologicalCode L).singleVtx zf zf' *
          ∂₁ L (Pi.single v 1) zf' from rfl]
  rw [Finset.sum_eq_single zf]
  · -- (singleVtx zf zf) * (boundary1 (δ_v) zf) = (1 : ZMod 2) * _ = boundary1 (δ_v) zf
    have hone : (RotatedSurface.rotatedSurfaceHomologicalCode L).singleVtx zf zf =
        (1 : ZMod 2) := Pi.single_eq_same _ _
    rw [hone, _root_.one_mul]
    exact boundary1_pi_single L v zf
  · intro zf' _ hne
    have h0 : (RotatedSurface.rotatedSurfaceHomologicalCode L).singleVtx zf zf' =
        (0 : ZMod 2) := by
      simp only [Quantum.Stabilizer.Homological.HomologicalCode.singleVtx,
        Pi.single_apply]
      exact if_neg hne
    rw [h0]; ring
  · intro hcontra; exact absurd (Finset.mem_univ zf) hcontra

/-- `boundary2 (singleFace xf) v = 1[v ∈ xSupport xf]`. -/
lemma boundary2_singleFace_apply (xf : RotatedSurface.XFaceIdx L)
    (v : RotatedSurface.VtxIdx L) :
    (RotatedSurface.rotatedSurfaceHomologicalCode L).boundary2
        ((RotatedSurface.rotatedSurfaceHomologicalCode L).singleFace xf) v =
      (if v ∈ RotatedSurface.xSupport xf then (1 : ZMod 2) else 0) := by
  classical
  change ∂₂ L (Pi.single xf 1) v = _
  rw [RotatedSurface.rscBoundary2_apply]
  by_cases hv : v ∈ RotatedSurface.xSupport xf
  · rw [if_pos hv, Finset.sum_eq_single xf]
    · simp [hv]
    · intro xf' _ hne
      simp [hne]
    · intro hcontra; exact absurd (Finset.mem_univ xf) hcontra
  · rw [if_neg hv]
    apply Finset.sum_eq_zero
    intro xf' _
    by_cases hxf : xf' = xf
    · subst hxf
      simp [hv]
    · simp [hxf]

/-! ## §B — Symplectic check-matrix entries

Each generator row of the check matrix has a clean closed form: `zStab zf` is
Z-type, so its X-half is uniformly zero; its Z-half at qubit `rscQubitEquiv L v`
is `1[v ∈ zSupport zf]`. Symmetrically for `xStab xf`.
-/

/-- The inverse of `rscQubitEquiv`, mapping a qubit index back to its
data-qubit. -/
noncomputable def vtxOfQubit (q : Fin (numQubits L)) : RotatedSurface.VtxIdx L :=
  (RotatedSurface.rscQubitEquiv L).symm q

omit [Fact (Odd L)] in
@[simp] lemma rscQubitEquiv_vtxOfQubit (q : Fin (numQubits L)) :
    RotatedSurface.rscQubitEquiv L (vtxOfQubit L q) = q :=
  (RotatedSurface.rscQubitEquiv L).apply_symm_apply q

omit [Fact (Odd L)] in
@[simp] lemma vtxOfQubit_rscQubitEquiv (v : RotatedSurface.VtxIdx L) :
    vtxOfQubit L (RotatedSurface.rscQubitEquiv L v) = v :=
  (RotatedSurface.rscQubitEquiv L).symm_apply_apply v

/-- X-half symplectic value of a Z-type generator is always zero. -/
private lemma toSymplectic_zStab_X (zf : RotatedSurface.ZFaceIdx L)
    (q : Fin (numQubits L)) :
    NQubitPauliOperator.toSymplectic (zStab L zf).operators
        (Fin.castAdd (numQubits L) q) = 0 := by
  rcases (zStab_is_ZType L zf).2 q with hI | hZ
  · rw [NQubitPauliOperator.toSymplectic_X_part, hI]
    rfl
  · rw [NQubitPauliOperator.toSymplectic_X_part, hZ]
    rfl

/-- Z-half symplectic value of an X-type generator is always zero. -/
private lemma toSymplectic_xStab_Z (xf : RotatedSurface.XFaceIdx L)
    (q : Fin (numQubits L)) :
    NQubitPauliOperator.toSymplectic (xStab L xf).operators
        (Fin.natAdd (numQubits L) q) = 0 := by
  rcases (xStab_is_XType L xf).2 q with hI | hX
  · rw [NQubitPauliOperator.toSymplectic_Z_part, hI]
    rfl
  · rw [NQubitPauliOperator.toSymplectic_Z_part, hX]
    rfl

/-- Z-half symplectic value of `zStab zf` at qubit `q` is the indicator
`1[vtxOfQubit q ∈ zSupport zf]`. -/
private lemma toSymplectic_zStab_Z (zf : RotatedSurface.ZFaceIdx L)
    (q : Fin (numQubits L)) :
    NQubitPauliOperator.toSymplectic (zStab L zf).operators
        (Fin.natAdd (numQubits L) q) =
      (if vtxOfQubit L q ∈ RotatedSurface.zSupport zf then (1 : ZMod 2) else 0) := by
  classical
  -- zStab zf = chainZOperator (cutMap (singleVtx zf)), and at qubit q the operator is
  -- Z iff cutMap (singleVtx zf) at `(edgeEquiv).symm q = vtxOfQubit q` is 1.
  rw [NQubitPauliOperator.toSymplectic_Z_part]
  set c : RotatedSurface.VtxIdx L → ZMod 2 :=
    (RotatedSurface.rotatedSurfaceHomologicalCode L).cutMap
      ((RotatedSurface.rotatedSurfaceHomologicalCode L).singleVtx zf) with hc
  have hc_val : c (vtxOfQubit L q) =
      (if vtxOfQubit L q ∈ RotatedSurface.zSupport zf then (1 : ZMod 2) else 0) := by
    rw [hc]; exact cutMap_singleVtx_apply L zf (vtxOfQubit L q)
  -- (zStab L zf).operators q is Z if c (vtxOfQubit q) = 1, else I.
  change ((zStab L zf).operators q).toSymplecticSingle.2 = _
  rw [show (zStab L zf).operators q =
      if ∃ v : RotatedSurface.VtxIdx L,
        RotatedSurface.rscQubitEquiv L v = q ∧ c v = 1
      then PauliOperator.Z else PauliOperator.I from rfl]
  by_cases h1 : c (vtxOfQubit L q) = 1
  · -- The witness is vtxOfQubit q.
    have hex : ∃ v : RotatedSurface.VtxIdx L,
        RotatedSurface.rscQubitEquiv L v = q ∧ c v = 1 :=
      ⟨vtxOfQubit L q, rscQubitEquiv_vtxOfQubit L q, h1⟩
    rw [if_pos hex]
    -- RHS: 1[v ∈ zSupport zf] = 1 since hc_val gives c = 1 here.
    have : (if vtxOfQubit L q ∈ RotatedSurface.zSupport zf then (1 : ZMod 2) else 0) = 1 := by
      rw [hc_val] at h1; exact h1
    rw [this]; rfl
  · -- c = 0 here, so no witness exists (any witness would have v = vtxOfQubit q by injectivity).
    have hnotex : ¬ ∃ v : RotatedSurface.VtxIdx L,
        RotatedSurface.rscQubitEquiv L v = q ∧ c v = 1 := by
      rintro ⟨v, hv, hcv⟩
      have hveq : v = vtxOfQubit L q := by
        apply (RotatedSurface.rscQubitEquiv L).injective
        rw [rscQubitEquiv_vtxOfQubit, hv]
      rw [hveq] at hcv
      exact h1 hcv
    rw [if_neg hnotex]
    -- c (vtxOfQubit q) ≠ 1 means c = 0 (ZMod 2 dichotomy), so RHS = 0.
    have h0 : c (vtxOfQubit L q) = 0 := by
      rw [hc_val] at h1 ⊢
      by_cases h : vtxOfQubit L q ∈ RotatedSurface.zSupport zf
      · rw [if_pos h] at h1; exact absurd rfl h1
      · rw [if_neg h]
    have : (if vtxOfQubit L q ∈ RotatedSurface.zSupport zf then (1 : ZMod 2) else 0) = 0 := by
      rw [hc_val] at h0; exact h0
    rw [this]; rfl

/-! ### Indexing into the generator list -/

/-- The Z-stab list, sourced from `Finset.univ.toList`. -/
private noncomputable def zList : List (RotatedSurface.ZFaceIdx L) :=
  (Finset.univ : Finset (RotatedSurface.ZFaceIdx L)).toList

/-- The X-stab list, sourced from `Finset.univ.toList`. -/
private noncomputable def xList : List (RotatedSurface.XFaceIdx L) :=
  (Finset.univ : Finset (RotatedSurface.XFaceIdx L)).toList

omit [Fact (Odd L)] [Fact (3 ≤ L)] in
private lemma zList_length :
    (zList L).length = Fintype.card (RotatedSurface.ZFaceIdx L) := by
  unfold zList
  rw [Finset.length_toList, Finset.card_univ]

omit [Fact (Odd L)] [Fact (3 ≤ L)] in
private lemma xList_length :
    (xList L).length = Fintype.card (RotatedSurface.XFaceIdx L) := by
  unfold xList
  rw [Finset.length_toList, Finset.card_univ]

omit [Fact (Odd L)] [Fact (3 ≤ L)] in
private lemma zList_nodup : (zList L).Nodup := by
  unfold zList; exact Finset.nodup_toList _

omit [Fact (Odd L)] [Fact (3 ≤ L)] in
private lemma xList_nodup : (xList L).Nodup := by
  unfold xList; exact Finset.nodup_toList _

omit [Fact (Odd L)] [Fact (3 ≤ L)] in
private lemma zList_mem (zf : RotatedSurface.ZFaceIdx L) : zf ∈ zList L := by
  unfold zList; rw [Finset.mem_toList]; exact Finset.mem_univ _

omit [Fact (Odd L)] [Fact (3 ≤ L)] in
private lemma xList_mem (xf : RotatedSurface.XFaceIdx L) : xf ∈ xList L := by
  unfold xList; rw [Finset.mem_toList]; exact Finset.mem_univ _

private lemma generatorsListZ_eq_map :
    generatorsListZ L = (zList L).map (zStab L) := rfl

private lemma generatorsListX_eq_map :
    generatorsListX L = (xList L).map (xStab L) := rfl

private lemma generatorsList_length_split :
    (generatorsList L).length = (zList L).length + (xList L).length := by
  unfold generatorsList
  rw [List.length_append, generatorsListZ_eq_map, generatorsListX_eq_map,
    List.length_map, List.length_map]

/-- The generator at index `k` with `k < (zList L).length` is the Z-stab at the
`k`-th element of `zList L`. -/
private lemma get_generatorsList_Z (k : ℕ) (hk : k < (generatorsList L).length)
    (hkZ : k < (zList L).length) :
    (generatorsList L).get ⟨k, hk⟩ = zStab L ((zList L).get ⟨k, hkZ⟩) := by
  change (generatorsListZ L ++ generatorsListX L).get ⟨k, hk⟩ = _
  rw [List.get_eq_getElem]
  have hkZ' : k < (generatorsListZ L).length := by
    change k < ((zList L).map (zStab L)).length
    rw [List.length_map]; exact hkZ
  rw [List.getElem_append_left hkZ']
  -- Goal: (generatorsListZ L)[k] = zStab L (zList L).get ⟨k, hkZ⟩
  change ((zList L).map (zStab L))[k]'hkZ' = _
  rw [List.getElem_map]
  rfl

/-- The generator at index `k` with `k ≥ (zList L).length` is the X-stab at
position `k - (zList L).length` in `xList L`. -/
private lemma get_generatorsList_X (k : ℕ) (hk : k < (generatorsList L).length)
    (hkZge : (zList L).length ≤ k)
    (hkXsub : k - (zList L).length < (xList L).length) :
    (generatorsList L).get ⟨k, hk⟩ =
      xStab L ((xList L).get ⟨k - (zList L).length, hkXsub⟩) := by
  change (generatorsListZ L ++ generatorsListX L).get ⟨k, hk⟩ = _
  rw [List.get_eq_getElem]
  have h_lenZ : (generatorsListZ L).length = (zList L).length := by
    change ((zList L).map (zStab L)).length = _; rw [List.length_map]
  have hkZge' : (generatorsListZ L).length ≤ k := h_lenZ.symm ▸ hkZge
  rw [List.getElem_append_right hkZge']
  -- Now goal involves `(generatorsListX L)[k - (generatorsListZ L).length]`.
  -- We need the index expression to match `k - (zList L).length` for List.getElem_map.
  have hsub_eq : k - (generatorsListZ L).length = k - (zList L).length := by
    rw [h_lenZ]
  -- Use the helper rewriting form.
  have hkXsub' : k - (generatorsListZ L).length < (generatorsListX L).length := by
    change _ < ((xList L).map (xStab L)).length
    rw [List.length_map, hsub_eq]; exact hkXsub
  change ((xList L).map (xStab L))[k - (generatorsListZ L).length]'hkXsub' = _
  rw [List.getElem_map]
  -- Now: xStab L ((xList L)[k - (generatorsListZ L).length]) =
  --      xStab L ((xList L).get ⟨k - (zList L).length, hkXsub⟩)
  rw [List.get_eq_getElem]
  congr 2

/-- X-half symplectic value of `xStab xf` at qubit `q` is the indicator
`1[vtxOfQubit q ∈ xSupport xf]`. -/
private lemma toSymplectic_xStab_X (xf : RotatedSurface.XFaceIdx L)
    (q : Fin (numQubits L)) :
    NQubitPauliOperator.toSymplectic (xStab L xf).operators
        (Fin.castAdd (numQubits L) q) =
      (if vtxOfQubit L q ∈ RotatedSurface.xSupport xf then (1 : ZMod 2) else 0) := by
  classical
  rw [NQubitPauliOperator.toSymplectic_X_part]
  set c : RotatedSurface.VtxIdx L → ZMod 2 :=
    (RotatedSurface.rotatedSurfaceHomologicalCode L).boundary2
      ((RotatedSurface.rotatedSurfaceHomologicalCode L).singleFace xf) with hc
  have hc_val : c (vtxOfQubit L q) =
      (if vtxOfQubit L q ∈ RotatedSurface.xSupport xf then (1 : ZMod 2) else 0) := by
    rw [hc]; exact boundary2_singleFace_apply L xf (vtxOfQubit L q)
  change ((xStab L xf).operators q).toSymplecticSingle.1 = _
  rw [show (xStab L xf).operators q =
      if ∃ v : RotatedSurface.VtxIdx L,
        RotatedSurface.rscQubitEquiv L v = q ∧ c v = 1
      then PauliOperator.X else PauliOperator.I from rfl]
  by_cases h1 : c (vtxOfQubit L q) = 1
  · have hex : ∃ v : RotatedSurface.VtxIdx L,
        RotatedSurface.rscQubitEquiv L v = q ∧ c v = 1 :=
      ⟨vtxOfQubit L q, rscQubitEquiv_vtxOfQubit L q, h1⟩
    rw [if_pos hex]
    have : (if vtxOfQubit L q ∈ RotatedSurface.xSupport xf then (1 : ZMod 2) else 0) = 1 := by
      rw [hc_val] at h1; exact h1
    rw [this]; rfl
  · have hnotex : ¬ ∃ v : RotatedSurface.VtxIdx L,
        RotatedSurface.rscQubitEquiv L v = q ∧ c v = 1 := by
      rintro ⟨v, hv, hcv⟩
      have hveq : v = vtxOfQubit L q := by
        apply (RotatedSurface.rscQubitEquiv L).injective
        rw [rscQubitEquiv_vtxOfQubit, hv]
      rw [hveq] at hcv
      exact h1 hcv
    rw [if_neg hnotex]
    have h0 : c (vtxOfQubit L q) = 0 := by
      rw [hc_val] at h1 ⊢
      by_cases h : vtxOfQubit L q ∈ RotatedSurface.xSupport xf
      · rw [if_pos h] at h1; exact absurd rfl h1
      · rw [if_neg h]
    have : (if vtxOfQubit L q ∈ RotatedSurface.xSupport xf then (1 : ZMod 2) else 0) = 0 := by
      rw [hc_val] at h0; exact h0
    rw [this]; rfl

/-! ## §C — Symplectic linear independence of the generator list

The argument decomposes the sum at column `natAdd numQubits q` (the Z-half)
versus `castAdd numQubits q` (the X-half). At the Z-half, X-block rows
contribute zero by `toSymplectic_xStab_Z`, leaving only the Z-block sum.
Reindexing this sum across vertices via `vtxOfQubit` recovers `rscZCutMap`
applied to the Z-block coefficient function, which is zero by hypothesis.
Injectivity of `rscZCutMap` (Stage 3) finishes the Z-side. The X-side is the
mirror image.
-/

/-- Z-block index → `ZFaceIdx` via `zList`. -/
private noncomputable def zfAt (k : ℕ) (hk : k < (zList L).length) :
    RotatedSurface.ZFaceIdx L :=
  (zList L).get ⟨k, hk⟩

/-- X-block index → `XFaceIdx` via `xList`. -/
private noncomputable def xfAt (k : ℕ) (hk : k < (xList L).length) :
    RotatedSurface.XFaceIdx L :=
  (xList L).get ⟨k, hk⟩

omit [Fact (Odd L)] [Fact (3 ≤ L)] in
private lemma zList_get_injective :
    Function.Injective (fun i : Fin (zList L).length => (zList L).get i) :=
  List.nodup_iff_injective_get.mp (zList_nodup L)

omit [Fact (Odd L)] [Fact (3 ≤ L)] in
private lemma xList_get_injective :
    Function.Injective (fun i : Fin (xList L).length => (xList L).get i) :=
  List.nodup_iff_injective_get.mp (xList_nodup L)

omit [Fact (Odd L)] [Fact (3 ≤ L)] in
/-- Bijection `Fin (zList L).length ≃ ZFaceIdx L` from the Nodup list. -/
private noncomputable def zEquiv :
    Fin (zList L).length ≃ RotatedSurface.ZFaceIdx L := by
  refine Equiv.ofBijective (fun i => (zList L).get i) ?_
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨zList_get_injective L, ?_⟩
  rw [Fintype.card_fin, zList_length]

omit [Fact (Odd L)] [Fact (3 ≤ L)] in
/-- Bijection `Fin (xList L).length ≃ XFaceIdx L` from the Nodup list. -/
private noncomputable def xEquiv :
    Fin (xList L).length ≃ RotatedSurface.XFaceIdx L := by
  refine Equiv.ofBijective (fun i => (xList L).get i) ?_
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨xList_get_injective L, ?_⟩
  rw [Fintype.card_fin, xList_length]

omit [Fact (Odd L)] [Fact (3 ≤ L)] in
@[simp] private lemma zEquiv_apply (i : Fin (zList L).length) :
    zEquiv L i = (zList L).get i := rfl

omit [Fact (Odd L)] [Fact (3 ≤ L)] in
@[simp] private lemma xEquiv_apply (i : Fin (xList L).length) :
    xEquiv L i = (xList L).get i := rfl

omit [Fact (Odd L)] [Fact (3 ≤ L)] in
@[simp] private lemma zEquiv_symm_zfAt (k : ℕ) (hk : k < (zList L).length) :
    (zEquiv L).symm (zfAt L k hk) = ⟨k, hk⟩ := by
  apply (zEquiv L).injective
  rw [Equiv.apply_symm_apply, zEquiv_apply]
  rfl

omit [Fact (Odd L)] [Fact (3 ≤ L)] in
@[simp] private lemma xEquiv_symm_xfAt (k : ℕ) (hk : k < (xList L).length) :
    (xEquiv L).symm (xfAt L k hk) = ⟨k, hk⟩ := by
  apply (xEquiv L).injective
  rw [Equiv.apply_symm_apply, xEquiv_apply]
  rfl

/-- The Z-block coefficient function for a row-coefficient `f`, indexed by
`ZFaceIdx`. -/
private noncomputable def coeffsZ
    (f : Fin (generatorsList L).length → ZMod 2) :
    RotatedSurface.ZFaceIdx L → ZMod 2 := fun zf =>
  let i := (zEquiv L).symm zf
  f ⟨i.val, by
    have := i.isLt
    have hsplit := generatorsList_length_split L
    omega⟩

/-- The X-block coefficient function for a row-coefficient `f`, indexed by
`XFaceIdx`. -/
private noncomputable def coeffsX
    (f : Fin (generatorsList L).length → ZMod 2) :
    RotatedSurface.XFaceIdx L → ZMod 2 := fun xf =>
  let i := (xEquiv L).symm xf
  f ⟨(zList L).length + i.val, by
    have := i.isLt
    have hsplit := generatorsList_length_split L
    omega⟩

private lemma coeffsZ_zfAt (f : Fin (generatorsList L).length → ZMod 2)
    (k : ℕ) (hkZ : k < (zList L).length)
    (hkfull : k < (generatorsList L).length) :
    coeffsZ L f (zfAt L k hkZ) = f ⟨k, hkfull⟩ := by
  unfold coeffsZ
  simp [zEquiv_symm_zfAt]

private lemma coeffsX_xfAt (f : Fin (generatorsList L).length → ZMod 2)
    (k : ℕ) (hkX : k < (xList L).length)
    (hkfull : (zList L).length + k < (generatorsList L).length) :
    coeffsX L f (xfAt L k hkX) = f ⟨(zList L).length + k, hkfull⟩ := by
  unfold coeffsX
  simp [xEquiv_symm_xfAt]

/-! ### Symplectic linear independence — main theorem -/

set_option maxHeartbeats 800000 in
-- Bumped: the proof unfolds finRange-sum reindexings, the Z/X block split,
-- and the rscZCutMap / rscBoundary2 injectivity arguments.
/-- The rotated-surface code generator list has linearly independent
check-matrix rows. -/
theorem rowsLinearIndependent_generatorsList :
    NQubitPauliGroupElement.rowsLinearIndependent (generatorsList L) := by
  classical
  unfold NQubitPauliGroupElement.rowsLinearIndependent
  rw [Fintype.linearIndependent_iff]
  intro f hsum
  -- Stage 1: Reduce hsum at column `natAdd q` to a Z-half equation.
  have hlen := generatorsList_length_split L
  -- Define the convenient embedding into Fin (genList).length.
  set nZ := (zList L).length with hnZ_def
  set nX := (xList L).length with hnX_def
  -- The Z-block split: f over Fin (nZ + nX) restricted to indices < nZ vs ≥ nZ.
  -- (We work directly with index splits instead of introducing custom Embeddings.)
  --
  -- Z-half kernel: rscZCutMap (coeffsZ f) = 0.
  have h_cz_ker : δ⁰ L (coeffsZ L f) = 0 := by
    funext v
    rw [Pi.zero_apply]
    -- Get the column equation at natAdd (rscQubitEquiv v).
    set q := RotatedSurface.rscQubitEquiv L v with hq_def
    have h_col := congr_fun hsum (Fin.natAdd (numQubits L) q)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      NQubitPauliGroupElement.checkMatrix] at h_col
    -- h_col : ∑ k, f k * toSymplectic ((genList).get k).operators (natAdd numQubits q) = 0
    -- Split into Z-block (k.val < nZ) and X-block (k.val ≥ nZ).
    have h_partition :
        (Finset.univ : Finset (Fin (generatorsList L).length)) =
          Finset.univ.filter (fun k => k.val < nZ) ∪
          Finset.univ.filter (fun k => ¬ k.val < nZ) := by
      rw [Finset.filter_union_filter_not_eq]
    have h_disj : Disjoint
        ((Finset.univ : Finset (Fin (generatorsList L).length)).filter (fun k => k.val < nZ))
        (Finset.univ.filter (fun k => ¬ k.val < nZ)) :=
      Finset.disjoint_filter_filter_not _ _ _
    rw [h_partition, Finset.sum_union h_disj] at h_col
    -- The X-block sum (k.val ≥ nZ) is 0 because the X-stabs have 0 Z-half.
    have h_x_zero : ∑ k ∈ (Finset.univ.filter
        (fun k : Fin (generatorsList L).length => ¬ k.val < nZ)),
        f k * NQubitPauliOperator.toSymplectic
          ((generatorsList L).get k).operators (Fin.natAdd (numQubits L) q) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_filter] at hk
      have hkge : nZ ≤ k.val := Nat.le_of_not_lt hk.2
      have hksub : k.val - nZ < nX := by
        have := k.isLt
        omega
      have hgetX := get_generatorsList_X L k.val k.isLt hkge hksub
      rw [hgetX]
      rw [toSymplectic_xStab_Z]
      ring
    rw [h_x_zero, add_zero] at h_col
    -- Now h_col : ∑ k ∈ Z-block, f k * (Z-half value) = 0
    -- Convert each Z-block term to use 1[vtxOfQubit q ∈ zSupport(zfAt k.val)].
    -- Goal: rscZCutMap (coeffsZ f) v = 0, i.e.,
    --   ∑ zf, coeffsZ f zf * 1[v ∈ zSupport zf] = 0
    rw [RotatedSurface.rscZCutMap_apply]
    -- Reindex Z-block sum (over Fin nZ) to a sum over ZFaceIdx L via zEquiv.
    -- Set up: bij between filter (k.val < nZ) and Fin nZ.
    have h_bij_lhs :
        ∑ k ∈ Finset.univ.filter (fun k : Fin (generatorsList L).length => k.val < nZ),
          f k * NQubitPauliOperator.toSymplectic
            ((generatorsList L).get k).operators (Fin.natAdd (numQubits L) q) =
        ∑ i : Fin nZ, f ⟨i.val, by have := i.isLt; omega⟩ *
            NQubitPauliOperator.toSymplectic
              ((generatorsList L).get ⟨i.val, by have := i.isLt; omega⟩).operators
              (Fin.natAdd (numQubits L) q) := by
      apply Finset.sum_bij (fun (k : Fin (generatorsList L).length)
        (hk : k ∈ Finset.univ.filter (fun k => k.val < nZ)) =>
          (⟨k.val, (Finset.mem_filter.mp hk).2⟩ : Fin nZ))
      · intros; exact Finset.mem_univ _
      · intros a _ b _ hab
        rcases a with ⟨a, ha⟩; rcases b with ⟨b, hb⟩
        simpa using Fin.ext (Fin.mk.inj_iff.mp hab)
      · intros b _
        refine ⟨⟨b.val, ?_⟩, ?_, by simp⟩
        · have := b.isLt; omega
        · rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, b.isLt⟩
      · intros; rfl
    rw [h_bij_lhs] at h_col
    -- Now h_col is a sum over Fin nZ. Convert toSymplectic to indicator.
    have h_eval :
        ∀ i : Fin nZ, f ⟨i.val, by have := i.isLt; omega⟩ *
            NQubitPauliOperator.toSymplectic
              ((generatorsList L).get ⟨i.val, by have := i.isLt; omega⟩).operators
              (Fin.natAdd (numQubits L) q) =
          f ⟨i.val, by have := i.isLt; omega⟩ *
            (if v ∈ RotatedSurface.zSupport (zfAt L i.val i.isLt) then (1 : ZMod 2) else 0) := by
      intro i
      congr 1
      have hgetZ := get_generatorsList_Z L i.val (by have := i.isLt; omega) i.isLt
      rw [hgetZ, toSymplectic_zStab_Z, hq_def, vtxOfQubit_rscQubitEquiv]
      rfl
    rw [show ∑ i : Fin nZ, f ⟨i.val, by have := i.isLt; omega⟩ *
            NQubitPauliOperator.toSymplectic
              ((generatorsList L).get ⟨i.val, by have := i.isLt; omega⟩).operators
              (Fin.natAdd (numQubits L) q) =
        ∑ i : Fin nZ, f ⟨i.val, by have := i.isLt; omega⟩ *
            (if v ∈ RotatedSurface.zSupport (zfAt L i.val i.isLt) then (1 : ZMod 2) else 0)
      from Finset.sum_congr rfl (fun i _ => h_eval i)] at h_col
    -- Reindex `∑ zf, _` to `∑ i, _` via `zEquiv`.
    have h_target_eq :
        (∑ zf : RotatedSurface.ZFaceIdx L,
            coeffsZ L f zf *
              (if v ∈ RotatedSurface.zSupport zf then (1 : ZMod 2) else 0)) =
        ∑ i : Fin nZ, f ⟨i.val, by have := i.isLt; omega⟩ *
            (if v ∈ RotatedSurface.zSupport (zfAt L i.val i.isLt) then (1 : ZMod 2) else 0) := by
      rw [← Equiv.sum_comp (zEquiv L) _]
      apply Finset.sum_congr rfl
      intro i _
      have hzfAt : zEquiv L i = zfAt L i.val i.isLt := by
        unfold zfAt; rw [zEquiv_apply]
      rw [hzfAt]
      rw [coeffsZ_zfAt L f i.val i.isLt (by have := i.isLt; omega)]
    rw [h_target_eq]
    exact h_col
  -- coeffsZ L f = 0 by rscZCutMap_injective.
  have h_cz_zero : coeffsZ L f = 0 := by
    apply RotatedSurface.rscZCutMap_injective
    rw [h_cz_ker, LinearMap.map_zero]
  -- For each k < nZ, f k = coeffsZ f (zfAt k) = 0.
  -- For each k ≥ nZ, similar via X-block.
  -- X-half kernel: rscBoundary2 (coeffsX f) = 0.
  have h_cx_ker : ∂₂ L (coeffsX L f) = 0 := by
    funext v
    rw [Pi.zero_apply]
    set q := RotatedSurface.rscQubitEquiv L v with hq_def
    have h_col := congr_fun hsum (Fin.castAdd (numQubits L) q)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      NQubitPauliGroupElement.checkMatrix] at h_col
    have h_partition :
        (Finset.univ : Finset (Fin (generatorsList L).length)) =
          Finset.univ.filter (fun k => k.val < nZ) ∪
          Finset.univ.filter (fun k => ¬ k.val < nZ) := by
      rw [Finset.filter_union_filter_not_eq]
    have h_disj : Disjoint
        ((Finset.univ : Finset (Fin (generatorsList L).length)).filter (fun k => k.val < nZ))
        (Finset.univ.filter (fun k => ¬ k.val < nZ)) :=
      Finset.disjoint_filter_filter_not _ _ _
    rw [h_partition, Finset.sum_union h_disj] at h_col
    -- The Z-block sum is 0 because Z-stabs have 0 X-half.
    have h_z_zero : ∑ k ∈ (Finset.univ.filter
        (fun k : Fin (generatorsList L).length => k.val < nZ)),
        f k * NQubitPauliOperator.toSymplectic
          ((generatorsList L).get k).operators (Fin.castAdd (numQubits L) q) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_filter] at hk
      have hkZ : k.val < nZ := hk.2
      have hgetZ := get_generatorsList_Z L k.val k.isLt hkZ
      rw [hgetZ]
      rw [toSymplectic_zStab_X]
      ring
    rw [h_z_zero, zero_add] at h_col
    rw [RotatedSurface.rscBoundary2_apply]
    -- Reindex X-block sum (filter k.val ≥ nZ) to Fin nX via xEquiv.
    have h_bij_lhs :
        ∑ k ∈ Finset.univ.filter (fun k : Fin (generatorsList L).length => ¬ k.val < nZ),
          f k * NQubitPauliOperator.toSymplectic
            ((generatorsList L).get k).operators (Fin.castAdd (numQubits L) q) =
        ∑ i : Fin nX, f ⟨nZ + i.val, by have := i.isLt; omega⟩ *
            NQubitPauliOperator.toSymplectic
              ((generatorsList L).get ⟨nZ + i.val, by have := i.isLt; omega⟩).operators
              (Fin.castAdd (numQubits L) q) := by
      apply Finset.sum_bij (fun (k : Fin (generatorsList L).length)
        (hk : k ∈ Finset.univ.filter (fun k => ¬ k.val < nZ)) =>
          (⟨k.val - nZ, by
            have hkge : nZ ≤ k.val := Nat.le_of_not_lt (Finset.mem_filter.mp hk).2
            have := k.isLt
            omega⟩ : Fin nX))
      · intros; exact Finset.mem_univ _
      · intros a ha b hb hab
        have ha_ge : nZ ≤ a.val := Nat.le_of_not_lt (Finset.mem_filter.mp ha).2
        have hb_ge : nZ ≤ b.val := Nat.le_of_not_lt (Finset.mem_filter.mp hb).2
        have h_val : a.val - nZ = b.val - nZ := Fin.mk.inj_iff.mp hab
        apply Fin.ext; omega
      · intros b _
        refine ⟨⟨nZ + b.val, by have := b.isLt; omega⟩, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          simp only [not_lt]
          exact Nat.le_add_right _ _
        · apply Fin.ext; simp
      · intros a ha
        have ha_ge : nZ ≤ a.val := Nat.le_of_not_lt (Finset.mem_filter.mp ha).2
        have h_fin_eq : (⟨nZ + (a.val - nZ), by have := a.isLt; omega⟩ :
            Fin (generatorsList L).length) = a := by
          apply Fin.ext
          change nZ + (a.val - nZ) = a.val
          omega
        rw [h_fin_eq]
    rw [h_bij_lhs] at h_col
    have h_eval :
        ∀ i : Fin nX, f ⟨nZ + i.val, by have := i.isLt; omega⟩ *
            NQubitPauliOperator.toSymplectic
              ((generatorsList L).get ⟨nZ + i.val, by have := i.isLt; omega⟩).operators
              (Fin.castAdd (numQubits L) q) =
          f ⟨nZ + i.val, by have := i.isLt; omega⟩ *
            (if v ∈ RotatedSurface.xSupport (xfAt L i.val i.isLt) then (1 : ZMod 2) else 0) := by
      intro i
      congr 1
      have hge : nZ ≤ nZ + i.val := Nat.le_add_right _ _
      have hsub : nZ + i.val - nZ < nX := by
        rw [Nat.add_sub_cancel_left]; exact i.isLt
      have hgetX := get_generatorsList_X L (nZ + i.val) (by have := i.isLt; omega) hge hsub
      rw [hgetX, toSymplectic_xStab_X, hq_def, vtxOfQubit_rscQubitEquiv]
      -- Remaining: xSupport ((xList).get ⟨nZ + i.val - (zList L).length, _⟩) =
      --             xSupport (xfAt L i.val i.isLt)
      -- These agree because the inner indices are equal.
      have h_idx_eq : nZ + i.val - (zList L).length = i.val := by
        change nZ + i.val - nZ = i.val; omega
      congr 1
      unfold xfAt
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp [h_idx_eq]
    rw [show ∑ i : Fin nX, f ⟨nZ + i.val, by have := i.isLt; omega⟩ *
            NQubitPauliOperator.toSymplectic
              ((generatorsList L).get ⟨nZ + i.val, by have := i.isLt; omega⟩).operators
              (Fin.castAdd (numQubits L) q) =
        ∑ i : Fin nX, f ⟨nZ + i.val, by have := i.isLt; omega⟩ *
            (if v ∈ RotatedSurface.xSupport (xfAt L i.val i.isLt) then (1 : ZMod 2) else 0)
      from Finset.sum_congr rfl (fun i _ => h_eval i)] at h_col
    have h_target_eq :
        (∑ xf : RotatedSurface.XFaceIdx L,
            coeffsX L f xf *
              (if v ∈ RotatedSurface.xSupport xf then (1 : ZMod 2) else 0)) =
        ∑ i : Fin nX, f ⟨nZ + i.val, by have := i.isLt; omega⟩ *
            (if v ∈ RotatedSurface.xSupport (xfAt L i.val i.isLt) then (1 : ZMod 2) else 0) := by
      rw [← Equiv.sum_comp (xEquiv L) _]
      apply Finset.sum_congr rfl
      intro i _
      have hxfAt : xEquiv L i = xfAt L i.val i.isLt := by
        unfold xfAt; rw [xEquiv_apply]
      rw [hxfAt]
      rw [coeffsX_xfAt L f i.val i.isLt (by have := i.isLt; omega)]
    rw [h_target_eq]
    exact h_col
  have h_cx_zero : coeffsX L f = 0 := by
    apply RotatedSurface.rscBoundary2_injective
    rw [h_cx_ker, LinearMap.map_zero]
  -- Finally combine Z- and X-block to get f = 0.
  intro j
  by_cases hjZ : j.val < nZ
  · -- j is in Z-block
    have hjz := congr_fun h_cz_zero (zfAt L j.val hjZ)
    rw [coeffsZ_zfAt L f j.val hjZ j.isLt] at hjz
    have : (⟨j.val, j.isLt⟩ : Fin (generatorsList L).length) = j := Fin.ext rfl
    rw [this] at hjz
    exact hjz
  · -- j is in X-block
    push Not at hjZ
    have hjX : j.val - nZ < nX := by
      have := j.isLt; omega
    have hjx := congr_fun h_cx_zero (xfAt L (j.val - nZ) hjX)
    have h_idx_eq : nZ + (j.val - nZ) = j.val := by omega
    rw [coeffsX_xfAt L f (j.val - nZ) hjX (by rw [h_idx_eq]; exact j.isLt)] at hjx
    have : (⟨nZ + (j.val - nZ), by rw [h_idx_eq]; exact j.isLt⟩ :
        Fin (generatorsList L).length) = j := by
      apply Fin.ext; exact h_idx_eq
    rw [this] at hjx
    exact hjx

/-- The rotated-surface generator list is an independent generating set. -/
theorem generators_independent :
    StabilizerGroup.GeneratorsIndependent (numQubits L) (generatorsList L) :=
  StabilizerGroup.GeneratorsIndependent_of_rowsLinearIndependent (numQubits L)
    (generatorsList L) (rowsLinearIndependent_generatorsList L)

/-! ## §D — Logical operators

Logical X is supported on the middle column `x = (L−1)/2`, and logical Z on the
middle row `y = (L−1)/2`. They intersect at the centre qubit `(mid, mid)`
exactly once, so they anticommute.
-/

/-- The middle row/column index `(L − 1) / 2`. -/
def midIdx : Fin L :=
  ⟨(L - 1) / 2, by
    have h3 : 3 ≤ L := Fact.out
    have : (L - 1) / 2 < L := by omega
    exact this⟩

omit [Fact (Odd L)] in
@[simp] lemma midIdx_val : (midIdx L).val = (L - 1) / 2 := rfl

/-- The middle-column 1-chain: 1 on qubits with `x = (L − 1) / 2`, else 0. -/
def middleColChain : RotatedSurface.VtxIdx L → ZMod 2 :=
  fun v => if v.1.val = (L - 1) / 2 then 1 else 0

/-- The middle-row 1-chain: 1 on qubits with `y = (L − 1) / 2`, else 0. -/
def middleRowChain : RotatedSurface.VtxIdx L → ZMod 2 :=
  fun v => if v.2.val = (L - 1) / 2 then 1 else 0

/-- The middle column is a 1-cycle: `∂₁(middleColChain) = 0`. -/
theorem middleColChain_mem_cycles :
    middleColChain L ∈ RotatedSurface.rscCycles L := by
  classical
  change ∂₁ L (middleColChain L) = 0
  have h3 : 3 ≤ L := Fact.out
  have hmid_pos : 0 < (L - 1) / 2 := by omega
  have hmid_lt : (L - 1) / 2 < L - 1 := by omega
  funext zf
  rw [Pi.zero_apply, RotatedSurface.rscBoundary1_apply]
  cases zf with
  | interior zc =>
    -- zSupport interior = faceQubits = 4-element set; x-coords are c.1.val twice
    -- and c.1.val+1 twice.  Sum pairs cancel in ZMod 2.
    rw [show RotatedSurface.zSupport (RotatedSurface.ZFaceIdx.interior zc) =
        RotatedSurface.faceQubits zc.val from rfl]
    -- The four corners; corner.1 has val = c.1.val ("lo") or c.1.val + 1 ("hi").
    set a := zc.val.1.val with ha_def
    -- middleColChain at (cornerLo c.1, _) = 1[a = mid]
    -- middleColChain at (cornerHi c.1, _) = 1[a+1 = mid]
    have h_chain_lo : ∀ b : Fin L, middleColChain L
        (RotatedSurface.cornerLo zc.val.1, b) =
          (if a = (L - 1) / 2 then (1 : ZMod 2) else 0) := fun _ => rfl
    have h_chain_hi : ∀ b : Fin L, middleColChain L
        (RotatedSurface.cornerHi zc.val.1, b) =
          (if a + 1 = (L - 1) / 2 then (1 : ZMod 2) else 0) := fun _ => rfl
    -- The four x-coords cornerLo, cornerHi as Fin L are distinct.
    have h_loHi_ne : RotatedSurface.cornerLo zc.val.1 ≠ RotatedSurface.cornerHi zc.val.1 := by
      intro h; have := congrArg Fin.val h
      simp [RotatedSurface.cornerLo, RotatedSurface.cornerHi] at this
    have h_loHi_ne2 : RotatedSurface.cornerLo zc.val.2 ≠ RotatedSurface.cornerHi zc.val.2 := by
      intro h; have := congrArg Fin.val h
      simp [RotatedSurface.cornerLo, RotatedSurface.cornerHi] at this
    -- Compute the sum using the indicator characterization.
    -- middleColChain depends only on the first coordinate; the four corners pair
    -- (lo, lo)+(lo, hi) and (hi, lo)+(hi, hi). Each pair has the same x-coord.
    rw [show ∑ v ∈ RotatedSurface.faceQubits zc.val, middleColChain L v =
        middleColChain L (RotatedSurface.cornerLo zc.val.1,
          RotatedSurface.cornerLo zc.val.2) +
        middleColChain L (RotatedSurface.cornerHi zc.val.1,
          RotatedSurface.cornerLo zc.val.2) +
        middleColChain L (RotatedSurface.cornerLo zc.val.1,
          RotatedSurface.cornerHi zc.val.2) +
        middleColChain L (RotatedSurface.cornerHi zc.val.1,
          RotatedSurface.cornerHi zc.val.2) from ?_]
    · rw [h_chain_lo, h_chain_hi, h_chain_lo, h_chain_hi]
      have h_2 : (2 : ZMod 2) = 0 := by decide
      have h_dist : ∀ x y : ZMod 2, x + y + x + y = 2 * x + 2 * y := fun _ _ => by ring
      rw [h_dist]
      rw [h_2, zero_mul, zero_mul, add_zero]
    · -- Show the explicit 4-term sum equals the Finset.sum.
      unfold RotatedSurface.faceQubits
      rw [Finset.sum_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or]
          refine ⟨fun hp => h_loHi_ne hp.1, fun hp => h_loHi_ne2 hp.2,
            fun hp => h_loHi_ne hp.1⟩)]
      rw [Finset.sum_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or]
          refine ⟨fun hp => h_loHi_ne (hp.1).symm, fun hp => h_loHi_ne2 hp.2⟩)]
      rw [Finset.sum_insert (by
          simp only [Finset.mem_singleton, Prod.mk.injEq, not_and]
          intro hp _; exact h_loHi_ne hp)]
      rw [Finset.sum_singleton]
      ring
  | leftBdy k =>
    -- Every qubit in zSupport(leftBdy k) has x = 0 ≠ mid.
    apply Finset.sum_eq_zero
    intro v hv
    rw [RotatedSurface.mem_zSupport_leftBdy_iff] at hv
    obtain ⟨hv1, _⟩ := hv
    unfold middleColChain
    rw [hv1]
    rw [if_neg (by omega)]
  | rightBdy k =>
    -- Every qubit in zSupport(rightBdy k) has x = L-1 ≠ mid.
    apply Finset.sum_eq_zero
    intro v hv
    rw [RotatedSurface.mem_zSupport_rightBdy_iff] at hv
    obtain ⟨hv1, _⟩ := hv
    unfold middleColChain
    rw [hv1]
    rw [if_neg (by omega)]

/-- `dualBoundary c xf = ∑ v ∈ xSupport xf, c v` (the indicator
characterization). -/
lemma dualBoundary_apply_eq_sum (c : RotatedSurface.VtxIdx L → ZMod 2)
    (xf : RotatedSurface.XFaceIdx L) :
    (RotatedSurface.rotatedSurfaceHomologicalCode L).dualBoundary c xf =
      ∑ v ∈ RotatedSurface.xSupport xf, c v := by
  classical
  -- Step 1: unfold dualBoundary; convert each summand to its indicator form.
  have h_step1 : (RotatedSurface.rotatedSurfaceHomologicalCode L).dualBoundary c xf =
      ∑ v : RotatedSurface.VtxIdx L,
        c v * (if v ∈ RotatedSurface.xSupport xf then (1 : ZMod 2) else 0) := by
    rw [show (RotatedSurface.rotatedSurfaceHomologicalCode L).dualBoundary c xf =
        ∑ v : RotatedSurface.VtxIdx L, c v *
          (RotatedSurface.rotatedSurfaceHomologicalCode L).boundary2 (Pi.single xf 1) v from rfl]
    apply Finset.sum_congr rfl
    intro v _
    have hb2 := boundary2_singleFace_apply L xf v
    change _ * (RotatedSurface.rotatedSurfaceHomologicalCode L).boundary2
        ((RotatedSurface.rotatedSurfaceHomologicalCode L).singleFace xf) v = _
    rw [hb2]
  rw [h_step1]
  -- Step 2: restructure the indicator multiplication to use Finset.sum_filter.
  have h_step2 : (∑ v : RotatedSurface.VtxIdx L,
      c v * (if v ∈ RotatedSurface.xSupport xf then (1 : ZMod 2) else 0)) =
      ∑ v : RotatedSurface.VtxIdx L,
        (if v ∈ RotatedSurface.xSupport xf then c v else 0) := by
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : v ∈ RotatedSurface.xSupport xf
    · rw [if_pos hv, if_pos hv, _root_.mul_one]
    · rw [if_neg hv, if_neg hv, MulZeroClass.mul_zero]
  rw [h_step2]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr ?_ (fun _ _ => rfl)
  ext v; simp

/-- The middle row is a dual 1-cycle: `dualBoundary (middleRowChain) = 0`. -/
theorem middleRowChain_mem_dualCycles :
    middleRowChain L ∈ (RotatedSurface.rotatedSurfaceHomologicalCode L).dualCycles := by
  classical
  change (RotatedSurface.rotatedSurfaceHomologicalCode L).dualBoundary
      (middleRowChain L) = 0
  have h3 : 3 ≤ L := Fact.out
  have hmid_pos : 0 < (L - 1) / 2 := by omega
  have hmid_lt : (L - 1) / 2 < L - 1 := by omega
  funext xf
  rw [Pi.zero_apply, dualBoundary_apply_eq_sum]
  cases xf with
  | interior xc =>
    -- Symmetric to middleColChain interior case: y-coords pair-cancel.
    rw [show RotatedSurface.xSupport (RotatedSurface.XFaceIdx.interior xc) =
        RotatedSurface.faceQubits xc.val from rfl]
    set b := xc.val.2.val with hb_def
    have h_chain_lo : ∀ a : Fin L, middleRowChain L
        (a, RotatedSurface.cornerLo xc.val.2) =
          (if b = (L - 1) / 2 then (1 : ZMod 2) else 0) := fun _ => rfl
    have h_chain_hi : ∀ a : Fin L, middleRowChain L
        (a, RotatedSurface.cornerHi xc.val.2) =
          (if b + 1 = (L - 1) / 2 then (1 : ZMod 2) else 0) := fun _ => rfl
    have h_loHi_ne : RotatedSurface.cornerLo xc.val.1 ≠ RotatedSurface.cornerHi xc.val.1 := by
      intro h; have := congrArg Fin.val h
      simp [RotatedSurface.cornerLo, RotatedSurface.cornerHi] at this
    have h_loHi_ne2 : RotatedSurface.cornerLo xc.val.2 ≠ RotatedSurface.cornerHi xc.val.2 := by
      intro h; have := congrArg Fin.val h
      simp [RotatedSurface.cornerLo, RotatedSurface.cornerHi] at this
    rw [show ∑ v ∈ RotatedSurface.faceQubits xc.val, middleRowChain L v =
        middleRowChain L (RotatedSurface.cornerLo xc.val.1,
          RotatedSurface.cornerLo xc.val.2) +
        middleRowChain L (RotatedSurface.cornerHi xc.val.1,
          RotatedSurface.cornerLo xc.val.2) +
        middleRowChain L (RotatedSurface.cornerLo xc.val.1,
          RotatedSurface.cornerHi xc.val.2) +
        middleRowChain L (RotatedSurface.cornerHi xc.val.1,
          RotatedSurface.cornerHi xc.val.2) from ?_]
    · rw [h_chain_lo, h_chain_lo, h_chain_hi, h_chain_hi]
      have h_2 : (2 : ZMod 2) = 0 := by decide
      have h_dist : ∀ x y : ZMod 2, x + x + y + y = 2 * x + 2 * y := fun _ _ => by ring
      rw [h_dist]
      rw [h_2, zero_mul, zero_mul, add_zero]
    · unfold RotatedSurface.faceQubits
      rw [Finset.sum_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or]
          refine ⟨fun hp => h_loHi_ne hp.1, fun hp => h_loHi_ne2 hp.2,
            fun hp => h_loHi_ne hp.1⟩)]
      rw [Finset.sum_insert (by
          simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or]
          refine ⟨fun hp => h_loHi_ne (hp.1).symm, fun hp => h_loHi_ne2 hp.2⟩)]
      rw [Finset.sum_insert (by
          simp only [Finset.mem_singleton, Prod.mk.injEq, not_and]
          intro hp _; exact h_loHi_ne hp)]
      rw [Finset.sum_singleton]
      ring
  | topBdy k =>
    -- All qubits have y = 0 ≠ mid.
    apply Finset.sum_eq_zero
    intro v hv
    rw [RotatedSurface.mem_xSupport_topBdy_iff] at hv
    obtain ⟨hv2, _⟩ := hv
    unfold middleRowChain
    rw [hv2]
    rw [if_neg (by omega)]
  | bottomBdy k =>
    -- All qubits have y = L - 1 ≠ mid.
    apply Finset.sum_eq_zero
    intro v hv
    rw [RotatedSurface.mem_xSupport_bottomBdy_iff] at hv
    obtain ⟨hv2, _⟩ := hv
    unfold middleRowChain
    rw [hv2]
    rw [if_neg (by omega)]

/-! ### Logical operators and centralizer membership -/

/-- The logical X operator: vertical X-string at column `(L − 1) / 2`. -/
noncomputable def logicalX : NQubitPauliGroupElement (numQubits L) :=
  (RotatedSurface.rotatedSurfaceHomologicalCode L).chainXOperator (middleColChain L)

/-- The logical Z operator: horizontal Z-string at row `(L − 1) / 2`. -/
noncomputable def logicalZ : NQubitPauliGroupElement (numQubits L) :=
  (RotatedSurface.rotatedSurfaceHomologicalCode L).chainZOperator (middleRowChain L)

/-- Logical X is in the centralizer of the homological stabilizer group. -/
lemma logicalX_mem_centralizer_homological :
    logicalX L ∈ StabilizerGroup.centralizer
      (RotatedSurface.rotatedSurfaceHomologicalCode L).homologicalStabilizerGroup := by
  rw [show logicalX L = (RotatedSurface.rotatedSurfaceHomologicalCode L).chainXOperator
      (middleColChain L) from rfl]
  have h := (RotatedSurface.rotatedSurfaceHomologicalCode L)
      |>.chainXOperator_mem_centralizer_iff_mem_cycles (middleColChain L)
  exact h.mpr (middleColChain_mem_cycles L)

/-- Logical Z is in the centralizer of the homological stabilizer group. -/
lemma logicalZ_mem_centralizer_homological :
    logicalZ L ∈ StabilizerGroup.centralizer
      (RotatedSurface.rotatedSurfaceHomologicalCode L).homologicalStabilizerGroup := by
  rw [show logicalZ L =
      (RotatedSurface.rotatedSurfaceHomologicalCode L).chainZOperator
        (middleRowChain L) from rfl]
  have h := (RotatedSurface.rotatedSurfaceHomologicalCode L)
      |>.chainZOperator_mem_centralizer_iff_mem_dualCycles (middleRowChain L)
  exact h.mpr (middleRowChain_mem_dualCycles L)

/-- The chain inner product of `middleColChain` and `middleRowChain` is 1 (they
share exactly the centre qubit `(mid, mid)`). -/
private lemma chainInnerProduct_middleCol_middleRow :
    Quantum.Stabilizer.Homological.HomologicalCode.chainInnerProduct
        (X := RotatedSurface.rotatedSurfaceHomologicalCode L)
        (middleColChain L) (middleRowChain L) = 1 := by
  classical
  -- Reduce the sum to the single contributing term at (mid, mid).
  change ∑ v : RotatedSurface.VtxIdx L, middleColChain L v * middleRowChain L v = 1
  rw [Finset.sum_eq_single (a := (midIdx L, midIdx L))]
  · unfold middleColChain middleRowChain
    simp
  · intro v _ hne
    unfold middleColChain middleRowChain
    by_cases h1 : v.1.val = (L - 1) / 2
    · by_cases h2 : v.2.val = (L - 1) / 2
      · exfalso
        apply hne
        rcases v with ⟨v1, v2⟩
        congr 1
        · exact Fin.ext h1
        · exact Fin.ext h2
      · rw [if_pos h1, if_neg h2, MulZeroClass.mul_zero]
    · rw [if_neg h1, MulZeroClass.zero_mul]
  · intro hcontra; exact absurd (Finset.mem_univ _) hcontra

/-- Logical X and logical Z anticommute. -/
theorem logicalX_anticommute_logicalZ :
    NQubitPauliGroupElement.Anticommute (logicalX L) (logicalZ L) := by
  have h_not_commute : ¬ ((logicalX L) * (logicalZ L) = (logicalZ L) * (logicalX L)) := by
    intro h
    have h_inner :=
      ((RotatedSurface.rotatedSurfaceHomologicalCode L).chainXOperator_commutes_chainZOperator_iff
        (middleColChain L) (middleRowChain L)).mp h
    rw [chainInnerProduct_middleCol_middleRow] at h_inner
    exact (by decide : (1 : ZMod 2) ≠ 0) h_inner
  rcases NQubitPauliGroupElement.commute_or_anticommute (logicalX L) (logicalZ L) with h | h
  · exact absurd h h_not_commute
  · exact h

/-! ### Logical operator package — translated to `stabilizerGroup` -/

/-- Logical X is in the centralizer of the lattice-side `stabilizerGroup`. -/
lemma logicalX_mem_centralizer :
    logicalX L ∈ StabilizerGroup.centralizer (stabilizerGroup L) := by
  rw [show StabilizerGroup.centralizer (stabilizerGroup L) =
      StabilizerGroup.centralizer
        (RotatedSurface.rotatedSurfaceHomologicalCode L).homologicalStabilizerGroup from
    StabilizerGroup.centralizer_eq_of_toSubgroup_eq _ _
      (stabilizerGroup_toSubgroup_eq_homologicalStabilizerGroup L)]
  exact logicalX_mem_centralizer_homological L

/-- Logical Z is in the centralizer of the lattice-side `stabilizerGroup`. -/
lemma logicalZ_mem_centralizer :
    logicalZ L ∈ StabilizerGroup.centralizer (stabilizerGroup L) := by
  rw [show StabilizerGroup.centralizer (stabilizerGroup L) =
      StabilizerGroup.centralizer
        (RotatedSurface.rotatedSurfaceHomologicalCode L).homologicalStabilizerGroup from
    StabilizerGroup.centralizer_eq_of_toSubgroup_eq _ _
      (stabilizerGroup_toSubgroup_eq_homologicalStabilizerGroup L)]
  exact logicalZ_mem_centralizer_homological L

/-- The logical qubit operator package (single logical qubit). -/
noncomputable def logicalOps :
    Fin 1 → LogicalQubitOps (numQubits L) (stabilizerGroup L) :=
  fun _ =>
    { xOp := logicalX L
      zOp := logicalZ L
      x_mem_centralizer := logicalX_mem_centralizer L
      z_mem_centralizer := logicalZ_mem_centralizer L
      anticommute := logicalX_anticommute_logicalZ L }

/-! ### Final assembly — `StabilizerCode (L * L) 1` -/

/-- The rotated surface code packaged as a `StabilizerCode (L * L) 1`. -/
noncomputable def rotatedSurfaceStabilizerCode :
    StabilizerGroup.StabilizerCode (numQubits L) 1 where
  hk := by
    have h3 : 3 ≤ L := Fact.out
    have : 1 ≤ L * L := by nlinarith
    exact this
  generatorsList := generatorsList L
  generators_length := generatorsList_length L
  generators_phaseZero := allPhaseZero_generatorsList L
  generators_independent := generators_independent L
  generators_commute := by
    rw [listToSet_generatorsList]; exact generators_commute L
  closure_no_neg_identity := by
    rw [listToSet_generatorsList]; exact negIdentity_not_mem L

/-- The rotated surface code packaged with its logical pair: the middle-column
`X`-string and the middle-row `Z`-string (`logicalOps L`). -/
noncomputable def rotatedSurfaceStabilizerCodeWithLogicals :
    StabilizerGroup.StabilizerCodeWithLogicals (numQubits L) 1 where
  toStabilizerCode := rotatedSurfaceStabilizerCode L
  logicalOps := logicalOps L
  logical_commute_cross := fun ℓ ℓ' h => (h (Subsingleton.elim ℓ ℓ')).elim

/-- The rotated-surface stabilizer code's subgroup matches the canonical
`stabilizerGroup L`. -/
theorem rotatedSurfaceStabilizerCode_subgroup_eq :
    (rotatedSurfaceStabilizerCode L).toStabilizerGroup.toSubgroup =
      (stabilizerGroup L).toSubgroup := rfl

/-- Bridge: the rotated-surface stabilizer code's subgroup matches the abstract
homological stabilizer group. -/
theorem rotatedSurfaceStabilizerCode_subgroup_eq_homological :
    (rotatedSurfaceStabilizerCode L).toStabilizerGroup.toSubgroup =
      (RotatedSurface.rotatedSurfaceHomologicalCode L).homologicalStabilizerGroup.toSubgroup := by
  rw [rotatedSurfaceStabilizerCode_subgroup_eq,
    stabilizerGroup_toSubgroup_eq_homologicalStabilizerGroup]

end RotatedSurfaceCodeN
end StabilizerGroup
end Quantum
