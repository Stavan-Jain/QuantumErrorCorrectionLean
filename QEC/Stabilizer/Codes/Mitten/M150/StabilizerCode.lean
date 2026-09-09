/-
# The `[[150,30,10]]` mitten code as a `StabilizerCode`

M2 packaging of `m150Complex` (the `mittenChainComplex m150A m150B` from
`Defs.lean`) as a genuine `StabilizerCode m150Complex.numQubits 30`,
mirroring the gross Phase-5 packaging
(`Codes/BivariateBicycle/Gross/StabilizerCode.lean`) — simplified: both
check matrices are full rank 60, so the generator list keeps *all* 120
stabilizers (no drop sets) and the decoder identities carry no
kernel-correction terms.

The offline-validated `𝔽₂` data lives in the generated `Data.lean`
(`qec-lab:experiments/bb_lab/scripts/m150_gen_lean_data.py`):
* `pivX` / `pivZ` — pivot qubit columns witnessing rank 60;
* `wX` / `wZ` — rows of `(H[:,piv])⁻¹` (packed 60-bit little-endian
  Nats), giving the syndrome-decoder identities `decoder_identity_X/Z`
  that yield generator independence with *no rank theorem*;
* `logXsup` / `logZsup` — a symplectic basis of 30 X-cycles + 30
  Z-dual-cycles with identity `30×30` intersection matrix (the 30
  logical qubits).

Result: `m150StabilizerCode : StabilizerCode m150Complex.numQubits 30`
plus the transport bridge `m150StabilizerCode_toSubgroup_eq` (the entry
point for the M4/M5 distance work).  Attempt state:
`qec-lab:pipeline/attempts/mitten_150_30_10/`.
-/

import QEC.Stabilizer.Codes.Mitten.M150.Defs
import QEC.Stabilizer.Framework.Homological.LogicalCorrespondence
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance

namespace Quantum
namespace Stabilizer
namespace Homological
namespace LP
namespace M150

open scoped BigOperators
open NQubitPauliGroupElement

/-! ## §1  Canonical cell indexing

Both check types (`C2` = X-checks and `C0` = Z-checks) are `Fin 2 × M150G`;
the canonical index of a cell is `30·i + g` (`checkOf` from `Data.lean`).
The bijection lets the packed-Nat decoder tables address cells by index. -/

/-- All 60 check cells in canonical order. -/
def cellList : List (Fin 2 × M150G) := (List.range 60).map checkOf

lemma cellList_length : cellList.length = 60 := by
  simp [cellList]

lemma cellList_nodup : cellList.Nodup := by decide

/-- Every check cell appears in `cellList`. -/
lemma cover : ∀ c : Fin 2 × M150G, c ∈ cellList := by decide

/-- Canonical cell of a `Fin 60` index. -/
def checkOfF (p : Fin 60) : Fin 2 × M150G := checkOf p.val

lemma checkOfF_bijective : Function.Bijective checkOfF := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨by decide, by decide⟩

/-! ## §2  Sparse boundary terms and their bridges

`d2term c q` is the `H_X` entry at X-check `c = (β, h)`, qubit `q = (m, x)`
(grid block `m < 4`: `[m%2 = β]·[h·x⁻¹ ∈ a_{m/2}]`; shared block `m = 4`:
`[x⁻¹·h ∈ b_β]`), and `cmTerm p q` the `H_Z` entry at Z-check `p = (α, y)`
(grid: `[m/2 = α]·[y⁻¹·x ∈ b_{m%2}]`; shared: `[x·y⁻¹ ∈ a_α]`).  The
pointwise bridges to the convolution boundary maps are finite facts
(60 × 150 cells), checked by `native_decide`; the chain-level bridges then
follow by linearity alone — no symbolic convolution reindexing needed. -/

/-- `H_X` entry at X-check `c`, qubit `q` (the `(c, q)` entry of `∂₂`'s
matrix). -/
def d2term (c : Fin 2 × M150G) (q : Fin 5 × M150G) : ZMod 2 :=
  if q.1.val = 4 then m150B c.1 (q.2⁻¹ * c.2)
  else if blockCol q.1 = c.1 then m150A (blockRow q.1) (c.2 * q.2⁻¹) else 0

/-- `H_Z` entry at Z-check `p`, qubit `q` (the `(p, q)` entry of `∂₁`'s
matrix, i.e. of `cutMap`'s columns). -/
def cmTerm (p : Fin 2 × M150G) (q : Fin 5 × M150G) : ZMod 2 :=
  if q.1.val = 4 then m150A p.1 (q.2 * p.2⁻¹)
  else if blockRow q.1 = p.1 then m150B (blockCol q.1) (p.2⁻¹ * q.2) else 0

/-- Pointwise `∂₂` bridge on indicator chains (validated `native_decide`,
9000 cells). -/
lemma lpBoundary2Fn_single_eq_d2term :
    ∀ (c : Fin 2 × M150G) (q : Fin 5 × M150G),
      lpBoundary2Fn m150A m150B (fun e => if e = c then 1 else 0) q
        = d2term c q := by
  native_decide

/-- Pointwise `∂₁` bridge on indicator chains (validated `native_decide`,
9000 cells). -/
lemma lpBoundary1Fn_single_eq_cmTerm :
    ∀ (q : Fin 5 × M150G) (p : Fin 2 × M150G),
      lpBoundary1Fn m150A m150B (fun e => if e = q then 1 else 0) p
        = cmTerm p q := by
  native_decide

/-- `∂₂(δ_c)` evaluated at a qubit is the sparse `d2term`.  (Stated at the
projected cell types so downstream `rw`s match the framework lemmas'
registered instances; the raw-typed `native_decide` fact is consumed by
`exact`, which crosses the instance gap by defeq.) -/
lemma boundary2_single_apply (c : m150Complex.C2) (q : m150Complex.C1) :
    m150Complex.boundary2 (Pi.single c 1) q = d2term c q := by
  have hpt : (Pi.single c (1 : ZMod 2))
      = (fun e => if e = c then (1 : ZMod 2) else 0) := by
    funext e
    exact Pi.single_apply c 1 e
  rw [hpt]
  exact lpBoundary2Fn_single_eq_d2term c q

/-- `∂₁(δ_q)` evaluated at a Z-check is the sparse `cmTerm`. -/
lemma boundary1_single_apply (q : m150Complex.C1) (p : m150Complex.C0) :
    m150Complex.boundary1 (Pi.single q 1) p = cmTerm p q := by
  have hpt : (Pi.single q (1 : ZMod 2))
      = (fun e => if e = q then (1 : ZMod 2) else 0) := by
    funext e
    exact Pi.single_apply q 1 e
  rw [hpt]
  exact lpBoundary1Fn_single_eq_cmTerm q p

private lemma boundary2_apply_eq_sum_single (f : m150Complex.C2 → ZMod 2)
    (q : m150Complex.C1) :
    m150Complex.boundary2 f q
      = ∑ c : m150Complex.C2, f c * m150Complex.boundary2 (Pi.single c 1) q := by
  have hf : f = ∑ c : m150Complex.C2, f c • Pi.single c (1 : ZMod 2) := by
    ext e
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hf]
  simp [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- **(L1, X)** Basis expansion of `∂₂` in the sparse `d2term` form. -/
lemma boundary2_apply_eq_sum_d2term (f : m150Complex.C2 → ZMod 2)
    (q : m150Complex.C1) :
    m150Complex.boundary2 f q = ∑ c : m150Complex.C2, f c * d2term c q := by
  rw [boundary2_apply_eq_sum_single]
  exact Finset.sum_congr rfl fun c _ => by rw [boundary2_single_apply]

/-- **(L1, Z)** `cutMap` in the sparse `cmTerm` form. -/
lemma cutMap_apply_eq_sum_cmTerm (s : m150Complex.C0 → ZMod 2)
    (q : m150Complex.C1) :
    m150Complex.cutMap s q = ∑ p : m150Complex.C0, s p * cmTerm p q := by
  rw [HomologicalCode.cutMap_apply]
  exact Finset.sum_congr rfl fun p _ => by rw [boundary1_single_apply]

/-! ## §3  Decoder identities and the kernel-trivial cores

`wX`/`wZ` pack `(H[:,piv])⁻¹` row-wise; reading `H[:,piv]·W = I` column-wise
gives `Σ_j W[j,p']·H[p, piv_j] = [p = p']`, which inverts `∂₂` (resp.
`cutMap`) on check chains: `f p' = Σ_j W[j,p']·(∂₂ f)(piv_j)`.  Both check
matrices have full rank 60, so there is no kernel-correction term and the
cores conclude `f = 0` outright. -/

/-- Bit `p'` of packed decoder row `j` (`wX`). -/
def wbitX (j p' : Fin 60) : ZMod 2 :=
  if (wX.getD j.val 0).testBit p'.val then 1 else 0

/-- Bit `p'` of packed decoder row `j` (`wZ`). -/
def wbitZ (j p' : Fin 60) : ZMod 2 :=
  if (wZ.getD j.val 0).testBit p'.val then 1 else 0

/-- The `j`-th pivot qubit cell for `H_X`. -/
def pivXcell (j : Fin 60) : Fin 5 × M150G := qubitOf (pivX.getD j.val 0)

/-- The `j`-th pivot qubit cell for `H_Z`. -/
def pivZcell (j : Fin 60) : Fin 5 × M150G := qubitOf (pivZ.getD j.val 0)

/-- **Face decoder identity** (validated `native_decide`, 3600 pairs × 60
terms): the packed `wX` rows invert `H_X` on its pivot columns. -/
theorem decoder_identity_X : ∀ p p' : Fin 60,
    (∑ j : Fin 60, wbitX j p' * d2term (checkOfF p) (pivXcell j))
      = (if p = p' then 1 else 0) := by
  native_decide

/-- **Vertex decoder identity** (validated `native_decide`): mirror of
`decoder_identity_X` for `H_Z` (`cmTerm`, `wZ`, `pivZ`). -/
theorem decoder_identity_Z : ∀ p p' : Fin 60,
    (∑ j : Fin 60, wbitZ j p' * cmTerm (checkOfF p) (pivZcell j))
      = (if p = p' then 1 else 0) := by
  native_decide

/-- Decoder collapse, generic over the side (`γ` instantiates at
`m150Complex.C2` and `.C0`): if the packed decoder rows invert the sparse
matrix `M` on the pivot columns (`hid`) and every pivot column annihilates
`f` (`hz`), then `f = 0`. -/
private lemma kernel_trivial_core {γ : Type} [Fintype γ]
    (f : γ → ZMod 2) (M : γ → (Fin 5 × M150G) → ZMod 2)
    (w : Fin 60 → Fin 60 → ZMod 2) (piv : Fin 60 → Fin 5 × M150G)
    (idx : Fin 60 → γ) (hbij : Function.Bijective idx)
    (hid : ∀ p p' : Fin 60,
      (∑ j : Fin 60, w j p' * M (idx p) (piv j)) = (if p = p' then 1 else 0))
    (hz : ∀ j : Fin 60, (∑ c : γ, f c * M c (piv j)) = 0) :
    f = 0 := by
  funext c'
  obtain ⟨p', rfl⟩ := hbij.surjective c'
  change f (idx p') = 0
  have hexp : f (idx p')
      = ∑ p : Fin 60, f (idx p) * (if p = p' then 1 else 0) := by
    rw [Finset.sum_eq_single p']
    · simp
    · intro b _ hb
      rw [if_neg hb, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ p') h
  have hswap : (∑ p : Fin 60, f (idx p) * (if p = p' then 1 else 0))
      = ∑ j : Fin 60, w j p' * (∑ p : Fin 60, f (idx p) * M (idx p) (piv j)) := by
    have hpt : ∀ p : Fin 60, f (idx p) * (if p = p' then 1 else 0)
        = ∑ j : Fin 60, w j p' * (f (idx p) * M (idx p) (piv j)) := by
      intro p
      rw [← hid p p', Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    simp_rw [hpt]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
  have hcell : ∀ j : Fin 60,
      (∑ p : Fin 60, f (idx p) * M (idx p) (piv j))
        = ∑ c : γ, f c * M c (piv j) :=
    fun j => hbij.sum_comp (fun c => f c * M c (piv j))
  rw [hexp, hswap]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [hcell j, hz j, mul_zero]

/-- **Face block independence core**: a `∂₂`-cycle is `0` (full rank —
no drop set needed, unlike the gross case). -/
lemma face_kernel_trivial {f : m150Complex.C2 → ZMod 2}
    (hf : m150Complex.boundary2 f = 0) : f = 0 := by
  refine kernel_trivial_core f d2term wbitX pivXcell checkOfF checkOfF_bijective
    decoder_identity_X fun j => ?_
  rw [← boundary2_apply_eq_sum_d2term f (pivXcell j), hf]
  rfl

/-- **Vertex block independence core**: a `cutMap`-kernel chain is `0`. -/
lemma vtx_kernel_trivial {s : m150Complex.C0 → ZMod 2}
    (hs : m150Complex.cutMap s = 0) : s = 0 := by
  refine kernel_trivial_core s cmTerm wbitZ pivZcell checkOfF checkOfF_bijective
    decoder_identity_Z fun j => ?_
  rw [← cutMap_apply_eq_sum_cmTerm s (pivZcell j), hs]
  rfl

/-! ## §4  Generator lists and closure equality (obligation 1)

Both check matrices are full rank, so the packaged list keeps *all* 60
vertex stabs and all 60 face stabs; closure equality against the
homological generator set is a direct two-inclusion argument (the gross
§4b/§4c drop machinery vanishes entirely). -/

noncomputable def genListZ : List (NQubitPauliGroupElement m150Complex.numQubits) :=
  cellList.map m150Complex.vertexStabOf

noncomputable def genListX : List (NQubitPauliGroupElement m150Complex.numQubits) :=
  cellList.map m150Complex.faceStabOf

noncomputable def genListPackaged : List (NQubitPauliGroupElement m150Complex.numQubits) :=
  genListZ ++ genListX

/-- **Closure equality**: the packaged 120-generator list generates exactly
the mitten homological stabilizer subgroup. -/
lemma closure_packaged_eq :
    Subgroup.closure (listToSet genListPackaged)
      = m150Complex.homologicalStabilizerGroup.toSubgroup := by
  rw [HomologicalCode.homologicalStabilizerGroup_toSubgroup]
  apply le_antisymm
  · refine Subgroup.closure_mono ?_
    intro g hg
    have hgl : g ∈ genListPackaged := hg
    rw [genListPackaged, List.mem_append] at hgl
    rcases hgl with hz | hx
    · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hz
      exact Or.inl ⟨v, rfl⟩
    · obtain ⟨f, _, rfl⟩ := List.mem_map.mp hx
      exact Or.inr ⟨f, rfl⟩
  · refine (Subgroup.closure_le _).mpr ?_
    rintro g (hz | hx)
    · obtain ⟨v, rfl⟩ := hz
      exact Subgroup.subset_closure
        (List.mem_append_left _ (List.mem_map.mpr ⟨v, cover v, rfl⟩))
    · obtain ⟨f, rfl⟩ := hx
      exact Subgroup.subset_closure
        (List.mem_append_right _ (List.mem_map.mpr ⟨f, cover f, rfl⟩))

/-! ## §5a  Symplectic-row bridges (for `rowsLinearIndependent`) -/

private lemma zmod2_dich (a : ZMod 2) : a = 0 ∨ a = 1 := by
  rcases Fin.exists_fin_two.mp ⟨a, rfl⟩ with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- Z-half symplectic entry of a vertex stab = the cutMap chain value at
that edge. -/
lemma vertexStabOf_sympl_Z (v : m150Complex.C0) (i : Fin m150Complex.numQubits) :
    NQubitPauliOperator.toSymplectic (m150Complex.vertexStabOf v).operators
        (Fin.natAdd m150Complex.numQubits i)
      = m150Complex.cutMap (m150Complex.singleVtx v) (m150Complex.edgeEquiv.symm i) := by
  rw [NQubitPauliOperator.toSymplectic_Z_part]
  change ((m150Complex.chainZOperator
    (m150Complex.cutMap (m150Complex.singleVtx v))).operators i).toSymplecticSingle.2 = _
  rw [HomologicalCode.chainZOperator_op_at]
  set c := m150Complex.cutMap (m150Complex.singleVtx v) with hc
  by_cases h : ∃ e, m150Complex.edgeEquiv e = i ∧ c e = 1
  · obtain ⟨e, he, hce⟩ := h
    rw [if_pos ⟨e, he, hce⟩]
    have : m150Complex.edgeEquiv.symm i = e := by rw [← he, Equiv.symm_apply_apply]
    rw [this, hce]
    rfl
  · rw [if_neg h]
    have hz : c (m150Complex.edgeEquiv.symm i) = 0 := by
      rcases zmod2_dich (c (m150Complex.edgeEquiv.symm i)) with h0 | h1
      · exact h0
      · exact absurd ⟨m150Complex.edgeEquiv.symm i, Equiv.apply_symm_apply _ _, h1⟩ h
    rw [hz]
    rfl

/-- X-half symplectic entry of a face stab = the boundary2 chain value at
that edge. -/
lemma faceStabOf_sympl_X (f : m150Complex.C2) (i : Fin m150Complex.numQubits) :
    NQubitPauliOperator.toSymplectic (m150Complex.faceStabOf f).operators
        (Fin.castAdd m150Complex.numQubits i)
      = m150Complex.boundary2 (m150Complex.singleFace f) (m150Complex.edgeEquiv.symm i) := by
  rw [NQubitPauliOperator.toSymplectic_X_part]
  change ((m150Complex.chainXOperator
      (m150Complex.boundary2 (m150Complex.singleFace f))).operators i).toSymplecticSingle.1 = _
  rw [HomologicalCode.chainXOperator_op_at]
  set c := m150Complex.boundary2 (m150Complex.singleFace f) with hc
  by_cases h : ∃ e, m150Complex.edgeEquiv e = i ∧ c e = 1
  · obtain ⟨e, he, hce⟩ := h
    rw [if_pos ⟨e, he, hce⟩]
    have : m150Complex.edgeEquiv.symm i = e := by rw [← he, Equiv.symm_apply_apply]
    rw [this, hce]
    rfl
  · rw [if_neg h]
    have hz : c (m150Complex.edgeEquiv.symm i) = 0 := by
      rcases zmod2_dich (c (m150Complex.edgeEquiv.symm i)) with h0 | h1
      · exact h0
      · exact absurd ⟨m150Complex.edgeEquiv.symm i, Equiv.apply_symm_apply _ _, h1⟩ h
    rw [hz]
    rfl

/-- A vertex stab (Z-type) has zero X-half symplectic entries. -/
lemma vertexStabOf_sympl_X_zero (v : m150Complex.C0) (i : Fin m150Complex.numQubits) :
    NQubitPauliOperator.toSymplectic (m150Complex.vertexStabOf v).operators
        (Fin.castAdd m150Complex.numQubits i) = 0 := by
  rw [NQubitPauliOperator.toSymplectic_X_part]
  rcases (HomologicalCode.vertexStabOf_isZType v).2 i with hI | hZ
  · rw [hI]
    rfl
  · rw [hZ]
    rfl

/-- A face stab (X-type) has zero Z-half symplectic entries. -/
lemma faceStabOf_sympl_Z_zero (f : m150Complex.C2) (i : Fin m150Complex.numQubits) :
    NQubitPauliOperator.toSymplectic (m150Complex.faceStabOf f).operators
        (Fin.natAdd m150Complex.numQubits i) = 0 := by
  rw [NQubitPauliOperator.toSymplectic_Z_part]
  rcases (HomologicalCode.faceStabOf_isXType f).2 i with hI | hX
  · rw [hI]
    rfl
  · rw [hX]
    rfl

/-! ## §5b  Coefficient-collapse helpers (consume the kernel-trivial cores) -/

private lemma singleVtx_apply' (a b : Fin 2 × M150G) :
    m150Complex.singleVtx a b = if b = a then (1 : ZMod 2) else 0 := by
  rw [HomologicalCode.singleVtx]
  exact Pi.single_apply a 1 b

private lemma singleFace_apply' (a b : Fin 2 × M150G) :
    m150Complex.singleFace a b = if b = a then (1 : ZMod 2) else 0 := by
  rw [HomologicalCode.singleFace]
  exact Pi.single_apply a 1 b

lemma combo_singleVtx_kernel_zero (c : Fin cellList.length → ZMod 2)
    (hker : m150Complex.cutMap
      (∑ i, c i • m150Complex.singleVtx (cellList.get i)) = 0) :
    ∀ i, c i = 0 := by
  set s := ∑ i, c i • m150Complex.singleVtx (cellList.get i) with hs
  have hs0 : s = 0 := vtx_kernel_trivial hker
  intro j
  have hsj := congr_fun hs0 (cellList.get j)
  rw [hs, Finset.sum_apply, Finset.sum_eq_single j] at hsj
  · simpa [singleVtx_apply'] using hsj
  · intro i _ hij
    have hne : cellList.get j ≠ cellList.get i :=
      fun h => hij (List.nodup_iff_injective_get.mp cellList_nodup h.symm)
    simp only [Pi.smul_apply, singleVtx_apply', smul_eq_mul, if_neg hne, mul_zero]
  · intro hc
    exact absurd (Finset.mem_univ j) hc

lemma combo_singleFace_kernel_zero (c : Fin cellList.length → ZMod 2)
    (hker : m150Complex.boundary2
      (∑ i, c i • m150Complex.singleFace (cellList.get i)) = 0) :
    ∀ i, c i = 0 := by
  set s := ∑ i, c i • m150Complex.singleFace (cellList.get i) with hs
  have hs0 : s = 0 := face_kernel_trivial hker
  intro j
  have hsj := congr_fun hs0 (cellList.get j)
  rw [hs, Finset.sum_apply, Finset.sum_eq_single j] at hsj
  · simpa [singleFace_apply'] using hsj
  · intro i _ hij
    have hne : cellList.get j ≠ cellList.get i :=
      fun h => hij (List.nodup_iff_injective_get.mp cellList_nodup h.symm)
    simp only [Pi.smul_apply, singleFace_apply', smul_eq_mul, if_neg hne, mul_zero]
  · intro hc
    exact absurd (Finset.mem_univ j) hc

/-! ## §5c  Packaged-list indexing -/

lemma genListPackaged_length :
    genListPackaged.length = cellList.length + cellList.length := by
  have h : genListPackaged.length = (cellList.map m150Complex.vertexStabOf).length
    + (cellList.map m150Complex.faceStabOf).length := rfl
  simpa [List.length_map] using h

lemma get_packaged_Z (i : Fin cellList.length)
    (hi : i.val < genListPackaged.length) :
    genListPackaged.get ⟨i.val, hi⟩ = m150Complex.vertexStabOf (cellList.get i) := by
  have hlt : i.val < (cellList.map m150Complex.vertexStabOf).length := by
    rw [List.length_map]
    exact i.isLt
  change (cellList.map m150Complex.vertexStabOf
    ++ cellList.map m150Complex.faceStabOf).get ⟨i.val, hi⟩ = _
  rw [List.get_eq_getElem, List.getElem_append_left hlt, List.getElem_map]
  rfl

set_option maxRecDepth 4096 in
lemma get_packaged_X (i : Fin cellList.length)
    (hi : cellList.length + i.val < genListPackaged.length) :
    genListPackaged.get ⟨cellList.length + i.val, hi⟩
      = m150Complex.faceStabOf (cellList.get i) := by
  have hZlen : (cellList.map m150Complex.vertexStabOf).length = cellList.length :=
    List.length_map _
  have hge : (cellList.map m150Complex.vertexStabOf).length ≤ cellList.length + i.val := by
    rw [hZlen]
    omega
  have hidx : cellList.length + i.val - (cellList.map m150Complex.vertexStabOf).length
      = i.val := by
    rw [hZlen]
    omega
  change (cellList.map m150Complex.vertexStabOf
    ++ cellList.map m150Complex.faceStabOf).get ⟨cellList.length + i.val, hi⟩ = _
  rw [List.get_eq_getElem, List.getElem_append_right hge, List.getElem_map]
  simp only [hidx]
  rfl

/-! ## §5d  rowsLinearIndependent (block-split) and generators_independent -/

private lemma zidx_lt (i : Fin cellList.length) : i.val < genListPackaged.length := by
  have := genListPackaged_length
  have := i.isLt
  omega

private lemma xidx_lt (i : Fin cellList.length) :
    cellList.length + i.val < genListPackaged.length := by
  have := genListPackaged_length
  have := i.isLt
  omega

set_option maxRecDepth 4096 in
private lemma sum_split_Z {M : Type*} [AddCommMonoid M]
    (F : Fin genListPackaged.length → M)
    (hX : ∀ i : Fin cellList.length, F ⟨cellList.length + i.val, xidx_lt i⟩ = 0) :
    ∑ k, F k = ∑ i : Fin cellList.length, F ⟨i.val, zidx_lt i⟩ := by
  have hlen := genListPackaged_length
  rw [← Equiv.sum_comp (finCongr hlen.symm) F, Fin.sum_univ_add]
  have hXsum : (∑ i : Fin cellList.length,
      F (finCongr hlen.symm (Fin.natAdd cellList.length i))) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← hX i]
    congr 1
  rw [hXsum, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1

set_option maxRecDepth 4096 in
private lemma sum_split_X {M : Type*} [AddCommMonoid M]
    (F : Fin genListPackaged.length → M)
    (hZ : ∀ i : Fin cellList.length, F ⟨i.val, zidx_lt i⟩ = 0) :
    ∑ k, F k = ∑ i : Fin cellList.length, F ⟨cellList.length + i.val, xidx_lt i⟩ := by
  have hlen := genListPackaged_length
  rw [← Equiv.sum_comp (finCongr hlen.symm) F, Fin.sum_univ_add]
  have hZsum : (∑ i : Fin cellList.length,
      F (finCongr hlen.symm (Fin.castAdd cellList.length i))) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← hZ i]
    congr 1
  rw [hZsum, zero_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
-- the block-split reduction unifies 120 check-matrix rows against the chain maps,
-- which exceeds the default heartbeat budget.
/-- The packaged 120-generator list has linearly independent check-matrix rows. -/
theorem rowsLinearIndependent_packaged :
    NQubitPauliGroupElement.rowsLinearIndependent genListPackaged := by
  rw [NQubitPauliGroupElement.rowsLinearIndependent, Fintype.linearIndependent_iff]
  intro g hsum
  set n := m150Complex.numQubits with hn
  have hZchain : m150Complex.cutMap (∑ i : Fin cellList.length,
      g ⟨i.val, zidx_lt i⟩ • m150Complex.singleVtx (cellList.get i)) = 0 := by
    funext e
    rw [map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have hcol := congr_fun hsum (Fin.natAdd n (m150Complex.edgeEquiv e))
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcol
    rw [← hcol, sum_split_Z (fun k => g k *
      NQubitPauliGroupElement.checkMatrix genListPackaged k
        (Fin.natAdd n (m150Complex.edgeEquiv e)))]
    · refine Finset.sum_congr rfl fun i _ => ?_
      have hterm : NQubitPauliGroupElement.checkMatrix genListPackaged ⟨i.val, zidx_lt i⟩
          (Fin.natAdd n (m150Complex.edgeEquiv e))
          = m150Complex.cutMap (m150Complex.singleVtx (cellList.get i)) e := by
        unfold NQubitPauliGroupElement.checkMatrix
        rw [get_packaged_Z i, vertexStabOf_sympl_Z, Equiv.symm_apply_apply]
      rw [hterm]
    · intro i
      have hterm : NQubitPauliGroupElement.checkMatrix genListPackaged
          ⟨cellList.length + i.val, xidx_lt i⟩ (Fin.natAdd n (m150Complex.edgeEquiv e)) = 0 := by
        unfold NQubitPauliGroupElement.checkMatrix
        rw [get_packaged_X i, faceStabOf_sympl_Z_zero]
      rw [hterm, mul_zero]
  have hZ0 := combo_singleVtx_kernel_zero _ hZchain
  have hXchain : m150Complex.boundary2 (∑ i : Fin cellList.length,
      g ⟨cellList.length + i.val, xidx_lt i⟩ • m150Complex.singleFace (cellList.get i))
        = 0 := by
    funext e
    rw [map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have hcol := congr_fun hsum (Fin.castAdd n (m150Complex.edgeEquiv e))
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcol
    rw [← hcol, sum_split_X (fun k => g k *
      NQubitPauliGroupElement.checkMatrix genListPackaged k
        (Fin.castAdd n (m150Complex.edgeEquiv e)))]
    · refine Finset.sum_congr rfl fun i _ => ?_
      have hterm : NQubitPauliGroupElement.checkMatrix genListPackaged
          ⟨cellList.length + i.val, xidx_lt i⟩ (Fin.castAdd n (m150Complex.edgeEquiv e))
          = m150Complex.boundary2 (m150Complex.singleFace (cellList.get i)) e := by
        unfold NQubitPauliGroupElement.checkMatrix
        rw [get_packaged_X i, faceStabOf_sympl_X, Equiv.symm_apply_apply]
      rw [hterm]
    · intro i
      have hterm : NQubitPauliGroupElement.checkMatrix genListPackaged ⟨i.val, zidx_lt i⟩
          (Fin.castAdd n (m150Complex.edgeEquiv e)) = 0 := by
        unfold NQubitPauliGroupElement.checkMatrix
        rw [get_packaged_Z i, vertexStabOf_sympl_X_zero]
      rw [hterm, mul_zero]
  have hX0 := combo_singleFace_kernel_zero _ hXchain
  intro k
  by_cases hk : k.val < cellList.length
  · have hz := hZ0 ⟨k.val, hk⟩
    rwa [Fin.eta] at hz
  · push Not at hk
    have hlen := genListPackaged_length
    have hkl := k.isLt
    have hsub : k.val - cellList.length < cellList.length := by omega
    have hx := hX0 ⟨k.val - cellList.length, hsub⟩
    have hidx : (⟨cellList.length + (k.val - cellList.length), by omega⟩ :
        Fin genListPackaged.length) = k := by
      apply Fin.ext
      change cellList.length + (k.val - cellList.length) = k.val
      omega
    rwa [hidx] at hx

/-- The packaged generator list is an independent generating set. -/
theorem generators_independent_packaged :
    Quantum.StabilizerGroup.GeneratorsIndependent m150Complex.numQubits genListPackaged :=
  Quantum.StabilizerGroup.GeneratorsIndependent_of_rowsLinearIndependent
    m150Complex.numQubits genListPackaged rowsLinearIndependent_packaged

/-! ## §6  Packaged stabilizer group, the 30 logical qubits, the `StabilizerCode`

The 30 logical-qubit operators are the `chainXOperator`/`chainZOperator` of
the offline-validated symplectic basis `logXsup`/`logZsup` (identity `30×30`
intersection matrix).  As in the gross packaging, every centralizer /
(anti)commutation fact is proved in a helper lemma with the **chain held
abstract**, so the heavy defeq against the concrete operators is paid once,
generically. -/

open Quantum.StabilizerGroup

/-- The 120 packaged generators all lie in the full homological generator set. -/
lemma listToSet_packaged_subset_homGens :
    listToSet genListPackaged ⊆ m150Complex.homologicalGenerators := by
  intro g hg
  have hg' : g ∈ genListZ ++ genListX := hg
  rcases List.mem_append.mp hg' with hz | hx
  · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hz
    exact HomologicalCode.ZGenerators_subset_homologicalGenerators ⟨v, rfl⟩
  · obtain ⟨f, _, rfl⟩ := List.mem_map.mp hx
    exact HomologicalCode.XGenerators_subset_homologicalGenerators ⟨f, rfl⟩

/-- The packaged generators pairwise commute. -/
lemma gens_commute_packaged :
    ∀ g ∈ listToSet genListPackaged, ∀ h ∈ listToSet genListPackaged, g * h = h * g := by
  intro g hg h hh
  exact HomologicalCode.homologicalGenerators_commute g (listToSet_packaged_subset_homGens hg)
    h (listToSet_packaged_subset_homGens hh)

/-- `-I` is not in the closure of the packaged generators. -/
lemma gens_no_neg_packaged :
    negIdentity m150Complex.numQubits ∉ Subgroup.closure (listToSet genListPackaged) := by
  rw [closure_packaged_eq]
  exact m150Complex.homologicalStabilizerGroup.no_neg_identity

/-- The packaged stabilizer group (closure of the 120-generator list). -/
noncomputable def packagedSG : StabilizerGroup m150Complex.numQubits :=
  mkStabilizerFromGenerators m150Complex.numQubits genListPackaged
    gens_commute_packaged gens_no_neg_packaged

/-- The packaged stabilizer subgroup equals the mitten homological stabilizer
subgroup — the bridge transporting the chain-level distance theorems. -/
lemma packagedSG_toSubgroup_eq :
    packagedSG.toSubgroup = m150Complex.homologicalStabilizerGroup.toSubgroup := by
  change Subgroup.closure (listToSet genListPackaged) = _
  exact closure_packaged_eq

/-- Centralizer membership for an X-chain operator, **chain abstract**: the
stuck `c` blocks `m150Complex.chainXOperator` from reducing and `packagedSG`
stays behind `packagedSG_toSubgroup_eq`, so the `centralizer`-transport defeq
is paid once here. -/
lemma chainXOperator_mem_centralizer_packagedSG (c : m150Complex.C1 → ZMod 2)
    (hc : m150Complex.boundary1 c = 0) :
    m150Complex.chainXOperator c ∈ centralizer packagedSG := by
  rw [centralizer_eq_of_toSubgroup_eq packagedSG m150Complex.homologicalStabilizerGroup
    packagedSG_toSubgroup_eq]
  exact (HomologicalCode.chainXOperator_mem_centralizer_iff_mem_cycles c).mpr
    ((m150Complex.mem_cycles_iff c).mpr hc)

/-- Centralizer membership for a Z-chain operator (chain abstract; mirror of
the X case). -/
lemma chainZOperator_mem_centralizer_packagedSG (c : m150Complex.C1 → ZMod 2)
    (hc : m150Complex.dualBoundary c = 0) :
    m150Complex.chainZOperator c ∈ centralizer packagedSG := by
  rw [centralizer_eq_of_toSubgroup_eq packagedSG m150Complex.homologicalStabilizerGroup
    packagedSG_toSubgroup_eq]
  refine (HomologicalCode.chainZOperator_mem_centralizer_iff_mem_dualCycles c).mpr ?_
  change c ∈ LinearMap.ker m150Complex.dualBoundary
  rw [LinearMap.mem_ker]
  exact hc

/-- An X-chain and a Z-chain operator anticommute when their inner product is
`1` (chains abstract). -/
lemma chainXOperator_anticommute_chainZOperator (c c' : m150Complex.C1 → ZMod 2)
    (h : m150Complex.chainInnerProduct c c' = 1) :
    NQubitPauliGroupElement.Anticommute
      (m150Complex.chainXOperator c) (m150Complex.chainZOperator c') := by
  rcases NQubitPauliGroupElement.commute_or_anticommute
    (m150Complex.chainXOperator c) (m150Complex.chainZOperator c') with hcomm | ha
  · exfalso
    have hzero := (HomologicalCode.chainXOperator_commutes_chainZOperator_iff c c').mp hcomm
    rw [h] at hzero
    exact one_ne_zero hzero
  · exact ha

/-- An X-chain and a Z-chain operator commute when their inner product is `0`
(chains abstract). -/
lemma chainXOperator_commute_chainZOperator (c c' : m150Complex.C1 → ZMod 2)
    (h : m150Complex.chainInnerProduct c c' = 0) :
    m150Complex.chainXOperator c * m150Complex.chainZOperator c'
      = m150Complex.chainZOperator c' * m150Complex.chainXOperator c :=
  (HomologicalCode.chainXOperator_commutes_chainZOperator_iff c c').mpr h

/-- Indicator chain of the `i`-th X-logical support (row `i` of `Lx`). -/
def logXchain (i : Fin 30) : Fin 5 × M150G → ZMod 2 :=
  fun q => if q ∈ (logXsup.getD i.val []).map qubitOf then 1 else 0

/-- Indicator chain of the `i`-th Z-logical support (row `i` of `Lz`). -/
def logZchain (i : Fin 30) : Fin 5 × M150G → ZMod 2 :=
  fun q => if q ∈ (logZsup.getD i.val []).map qubitOf then 1 else 0

/-- Computable form of `dualBoundary` on a 1-chain: the transpose of `∂₂`. -/
def dualBfn (c : Fin 5 × M150G → ZMod 2) (p : Fin 2 × M150G) : ZMod 2 :=
  ∑ q : Fin 5 × M150G, c q * d2term p q

lemma dualBoundary_eq_dualBfn (c : Fin 5 × M150G → ZMod 2) (p : Fin 2 × M150G) :
    m150Complex.dualBoundary c p = dualBfn c p := by
  rw [HomologicalCode.dualBoundary_apply]
  exact Finset.sum_congr rfl fun q _ => by rw [boundary2_single_apply]

/-- All 30 X-logicals are cycles (`∂₁ = 0`). -/
lemma logXchain_cycle (i : Fin 30) : m150Complex.boundary1 (logXchain i) = 0 := by
  have h : ∀ k : Fin 30, lpBoundary1Fn m150A m150B (logXchain k) = 0 := by native_decide
  exact h i

/-- All 30 Z-logicals are dual cycles (`dualBoundary = 0`). -/
lemma logZchain_dualCycle (i : Fin 30) : m150Complex.dualBoundary (logZchain i) = 0 := by
  have h : ∀ k : Fin 30, ∀ p : Fin 2 × M150G, dualBfn (logZchain k) p = 0 := by
    native_decide
  funext p
  rw [dualBoundary_eq_dualBfn]
  exact h i p

/-- The `30×30` intersection matrix is the identity (`Lx·Lzᵀ = I₃₀`). -/
lemma logChain_inner (i j : Fin 30) :
    m150Complex.chainInnerProduct (logXchain i) (logZchain j) = (if i = j then 1 else 0) := by
  have h : ∀ a b : Fin 30,
      (∑ e : Fin 5 × M150G, logXchain a e * logZchain b e) = (if a = b then 1 else 0) := by
    native_decide
  exact h i j

set_option maxRecDepth 4096 in
/-- The `i`-th logical qubit operator pair: the abstract helpers above are
simply *applied* to the concrete chains, so no heavy defeq is re-run here. -/
noncomputable def logicalQubit (i : Fin 30) :
    LogicalQubitOps m150Complex.numQubits packagedSG where
  xOp := m150Complex.chainXOperator (logXchain i)
  zOp := m150Complex.chainZOperator (logZchain i)
  x_mem_centralizer := chainXOperator_mem_centralizer_packagedSG (logXchain i) (logXchain_cycle i)
  z_mem_centralizer :=
    chainZOperator_mem_centralizer_packagedSG (logZchain i) (logZchain_dualCycle i)
  anticommute := chainXOperator_anticommute_chainZOperator (logXchain i) (logZchain i)
    (by rw [logChain_inner i i, if_pos rfl])

set_option maxRecDepth 4096 in
/-- Logical operators for different logical qubits commute (the `30×30`
matrix is diagonal off the diagonal). -/
theorem logical_commute_cross : ∀ ℓ ℓ' : Fin 30, ℓ ≠ ℓ' →
    ((logicalQubit ℓ).xOp * (logicalQubit ℓ').xOp
        = (logicalQubit ℓ').xOp * (logicalQubit ℓ).xOp ∧
      (logicalQubit ℓ).xOp * (logicalQubit ℓ').zOp
        = (logicalQubit ℓ').zOp * (logicalQubit ℓ).xOp ∧
      (logicalQubit ℓ).zOp * (logicalQubit ℓ').xOp
        = (logicalQubit ℓ').xOp * (logicalQubit ℓ).zOp ∧
      (logicalQubit ℓ).zOp * (logicalQubit ℓ').zOp
        = (logicalQubit ℓ').zOp * (logicalQubit ℓ).zOp) := by
  intro ℓ ℓ' hne
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Quantum.StabilizerGroup.CSSCommutationLemmas.XType_commutes
      (HomologicalCode.chainXOperator_isXType _) (HomologicalCode.chainXOperator_isXType _)
  · exact chainXOperator_commute_chainZOperator (logXchain ℓ) (logZchain ℓ')
      (by rw [logChain_inner ℓ ℓ', if_neg hne])
  · exact (chainXOperator_commute_chainZOperator (logXchain ℓ') (logZchain ℓ)
      (by rw [logChain_inner ℓ' ℓ, if_neg (Ne.symm hne)])).symm
  · exact Quantum.StabilizerGroup.CSSCommutationLemmas.ZType_commutes
      (HomologicalCode.chainZOperator_isZType _) (HomologicalCode.chainZOperator_isZType _)

set_option maxRecDepth 4096 in
/-- The `[[150, 30, 10]]` mitten code as a `StabilizerCode` (`n` stated as
`m150Complex.numQubits`; `m150_numQubits : m150Complex.numQubits = 150`). -/
noncomputable def m150StabilizerCode : StabilizerCode m150Complex.numQubits 30 where
  hk := by
    rw [m150_numQubits]
    omega
  generatorsList := genListPackaged
  generators_length := by
    have h60 : cellList.length = 60 := cellList_length
    have hn := m150_numQubits
    rw [genListPackaged_length]
    omega
  generators_phaseZero := by
    intro g hg
    rcases List.mem_append.mp (show g ∈ genListZ ++ genListX from hg) with hz | hx
    · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hz
      exact (HomologicalCode.vertexStabOf_isZType v).1
    · obtain ⟨f, _, rfl⟩ := List.mem_map.mp hx
      exact (HomologicalCode.faceStabOf_isXType f).1
  generators_independent := generators_independent_packaged
  generators_commute := gens_commute_packaged
  closure_no_neg_identity := gens_no_neg_packaged
  logicalOps := logicalQubit
  logical_commute_cross := logical_commute_cross

/-- The packaged code's stabilizer subgroup is the mitten homological
stabilizer subgroup — the bridge that will transport the chain-level distance
theorems (M4/M5). -/
theorem m150StabilizerCode_toSubgroup_eq :
    m150StabilizerCode.toStabilizerGroup.toSubgroup
      = m150Complex.homologicalStabilizerGroup.toSubgroup := by
  change Subgroup.closure (listToSet genListPackaged) = _
  exact closure_packaged_eq

end M150
end LP
end Homological
end Stabilizer
end Quantum
