/-
# The gross BB code as a `StabilizerCode 144 12`, with `HasCodeDistance`

Phase 5 of the gross `[[144, 12, 12]]` formalization: package
`grossComplex` (the `bbChainComplex grossA grossB` from `Defs.lean`) as a
genuine `StabilizerCode 144 12`, and transport the Phase-2 (`≥ 6`,
unconditional) and Phase-4 (`= 12`, conditional on the two CRT-engine Props)
distance theorems — stated against `grossComplex.homologicalStabilizerGroup`
— onto the packaged `HasCodeDistance` predicate via
`IsNontrivialLogicalOperator_of_toSubgroup_eq`.

The offline-validated `𝔽₂` linear-algebra data lives in the generated
`StabilizerCodeData.lean` (`qec-lab:experiments/bb_lab/phase5/`, `data.json`):
* `dropSet` — 6 faces / 6 vertices dropped to trim 144 generators to 132;
* `redP2` / `redCM` — reduced bases of `ker ∂₂` / `ker cutMap` (6 each),
  satisfying `redP2 j (dropSet i) = [i=j]`, giving both the closure relations
  and the independence kernel-collapse;
* `phiX` / `phiZ` — left-inverse "syndrome decoder" certificates proving the
  trimmed rows are independent (no rank theorem; see `decoder_identity_*`);
* `logX` / `logZ` — a symplectic basis of 12 X-cycles + 12 Z-dual-cycles
  with identity `12×12` intersection matrix (the 12 logical qubits).

Status: complete. `grossStabilizerCode : StabilizerCode 144 12` is built (all
four packaging obligations — closure equality, generator independence via the
decoder identities, the 12 logical qubits, and assembly), and the chain-level
distance theorems are transported to `grossStabilizerCode_logical_weight_ge_6`
(unconditional `≥ 6`) and `grossStabilizerCode_hasCodeDistance_12` (`= 12`,
conditional only on `MImBound`; the `LightStabilizerClassification` input is
discharged by `LightStab.lightStabilizerClassification_holds`).
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Gross.BaseDistance
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.SafeSector
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.LightStabClassify
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.StabilizerCodeData
import QEC.Stabilizer.Framework.Homological.LogicalCorrespondence
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance
import Mathlib.Data.List.GetD

namespace Quantum.Stabilizer.Homological.BB

open scoped BigOperators
open Quantum.Stabilizer.Homological NQubitPauliGroupElement

/-! ## §2  Sparse boundary terms and the decoder identities

`∂₂(δ_f)` and `cutMap(δ_v)` are sparse point-mass images; evaluating them
through these few-term forms (rather than `conv`) keeps the kernel `decide`
sweeps cheap. -/

/-- `∂₂(δ_f)` evaluated at qubit `(h, j)`:  `A(h-f)` on the left block,
`B(h-f)` on the right. -/
def d2term (f h : GrossGroup) (j : Fin 2) : ZMod 2 :=
  if j = 0 then grossA (h - f) else grossB (h - f)

/-- `cutMap(δ_v)` evaluated at qubit `(h, j)`:  `B(v-h)` on the left block,
`A(v-h)` on the right. -/
def cmTerm (v h : GrossGroup) (j : Fin 2) : ZMod 2 :=
  if j = 0 then grossB (v - h) else grossA (v - h)

/-- Apply the `phiX` decoder to `∂₂(δ_p)`, read at output face `p'`. -/
def decodeXAt (p p' : GrossGroup) : ZMod 2 :=
  (phiX.filter (fun pr => pr.1 = p')).foldl
    (fun acc pr => acc + d2term p pr.2.1 pr.2.2) 0

/-- Apply the `phiZ` decoder to `cutMap(δ_p)`, read at output vertex `p'`. -/
def decodeZAt (p p' : GrossGroup) : ZMod 2 :=
  (phiZ.filter (fun pr => pr.1 = p')).foldl
    (fun acc pr => acc + cmTerm p pr.2.1 pr.2.2) 0

/-- Kernel-basis correction term `Σ_j [p = dropSet j] · (red j)(p')`. -/
def kerCorrection (red : List (List GrossGroup)) (p p' : GrossGroup) : ZMod 2 :=
  ((List.range 6).filter (fun j => dropSet.getD j 0 = p)).foldl
    (fun acc j => acc + (if (red.getD j []).contains p' then 1 else 0)) 0

/-! ### §2a  Kernel-decide infrastructure for the decoder identities

The `72×72` decoder sweeps are checked purely by the kernel (no native code).
Two ingredients keep that feasible: the `phiX`/`phiZ` rows are bucketed by
output coordinate **once** (top-level tables, so the kernel's whnf cache walks
each filter a single time), and the per-pair hot loop is re-encoded over `Nat`
(`encG`) and `Bool` xor-folds, where kernel reduction is GMP-fast. Bridging
lemmas transport the checked Bool tables back to the `ZMod 2` statements. -/

def keptCoords : List GrossGroup := [((0 : ZMod 12), (4 : ZMod 6)), ((0 : ZMod 12), (5 : ZMod 6)),
  ((1 : ZMod 12), (2 : ZMod 6)), ((1 : ZMod 12), (3 : ZMod 6)), ((1 : ZMod 12), (4 : ZMod 6)),
  ((1 : ZMod 12), (5 : ZMod 6)), ((2 : ZMod 12), (0 : ZMod 6)), ((2 : ZMod 12), (1 : ZMod 6)),
  ((2 : ZMod 12), (2 : ZMod 6)), ((2 : ZMod 12), (3 : ZMod 6)), ((2 : ZMod 12), (4 : ZMod 6)),
  ((2 : ZMod 12), (5 : ZMod 6)), ((3 : ZMod 12), (0 : ZMod 6)), ((3 : ZMod 12), (1 : ZMod 6)),
  ((3 : ZMod 12), (2 : ZMod 6)), ((3 : ZMod 12), (3 : ZMod 6)), ((3 : ZMod 12), (4 : ZMod 6)),
  ((3 : ZMod 12), (5 : ZMod 6)), ((4 : ZMod 12), (0 : ZMod 6)), ((4 : ZMod 12), (1 : ZMod 6)),
  ((4 : ZMod 12), (2 : ZMod 6)), ((4 : ZMod 12), (3 : ZMod 6)), ((4 : ZMod 12), (4 : ZMod 6)),
  ((4 : ZMod 12), (5 : ZMod 6)), ((5 : ZMod 12), (0 : ZMod 6)), ((5 : ZMod 12), (1 : ZMod 6)),
  ((5 : ZMod 12), (2 : ZMod 6)), ((5 : ZMod 12), (3 : ZMod 6)), ((5 : ZMod 12), (4 : ZMod 6)),
  ((5 : ZMod 12), (5 : ZMod 6)), ((6 : ZMod 12), (0 : ZMod 6)), ((6 : ZMod 12), (1 : ZMod 6)),
  ((6 : ZMod 12), (2 : ZMod 6)), ((6 : ZMod 12), (3 : ZMod 6)), ((6 : ZMod 12), (4 : ZMod 6)),
  ((6 : ZMod 12), (5 : ZMod 6)), ((7 : ZMod 12), (0 : ZMod 6)), ((7 : ZMod 12), (1 : ZMod 6)),
  ((7 : ZMod 12), (2 : ZMod 6)), ((7 : ZMod 12), (3 : ZMod 6)), ((7 : ZMod 12), (4 : ZMod 6)),
  ((7 : ZMod 12), (5 : ZMod 6)), ((8 : ZMod 12), (0 : ZMod 6)), ((8 : ZMod 12), (1 : ZMod 6)),
  ((8 : ZMod 12), (2 : ZMod 6)), ((8 : ZMod 12), (3 : ZMod 6)), ((8 : ZMod 12), (4 : ZMod 6)),
  ((8 : ZMod 12), (5 : ZMod 6)), ((9 : ZMod 12), (0 : ZMod 6)), ((9 : ZMod 12), (1 : ZMod 6)),
  ((9 : ZMod 12), (2 : ZMod 6)), ((9 : ZMod 12), (3 : ZMod 6)), ((9 : ZMod 12), (4 : ZMod 6)),
  ((9 : ZMod 12), (5 : ZMod 6)), ((10 : ZMod 12), (0 : ZMod 6)), ((10 : ZMod 12), (1 : ZMod 6)),
  ((10 : ZMod 12), (2 : ZMod 6)), ((10 : ZMod 12), (3 : ZMod 6)), ((10 : ZMod 12), (4 : ZMod 6)),
  ((10 : ZMod 12), (5 : ZMod 6)), ((11 : ZMod 12), (0 : ZMod 6)), ((11 : ZMod 12), (1 : ZMod 6)),
  ((11 : ZMod 12), (2 : ZMod 6)), ((11 : ZMod 12), (3 : ZMod 6)), ((11 : ZMod 12), (4 : ZMod 6)),
  ((11 : ZMod 12), (5 : ZMod 6))]

/-- Literal enumeration of `GrossGroup` (completeness certified below). -/
private def grossEnum : List GrossGroup := dropSet ++ keptCoords

set_option maxRecDepth 40000 in
-- kernel decide needs more recursion headroom on the 72-point enumeration.
private lemma grossEnum_complete : ∀ g : GrossGroup, g ∈ grossEnum := by decide

/-- A `ZMod 2`-valued left fold with `+` from `0` is the sum of the mapped list. -/
private lemma foldl_add_eq_sum {α : Type*} (l : List α) (g : α → ZMod 2) :
    l.foldl (fun acc x => acc + g x) 0 = (l.map g).sum := by
  have gen : ∀ (a : ZMod 2), l.foldl (fun acc x => acc + g x) a = a + (l.map g).sum := by
    induction l with
    | nil => intro a; simp
    | cons x xs ih => intro a; simp [ih (a + g x), add_assoc]
  simpa using gen 0

/-- Nat encoding of `GrossGroup` (kernel-fast comparisons). -/
private def encG (g : GrossGroup) : Nat := g.1.val * 6 + g.2.val

set_option maxRecDepth 40000 in
-- kernel decide needs more recursion headroom on the 72×72 sweep.
private lemma encG_inj : ∀ a b : GrossGroup, encG a = encG b → a = b := by decide

private lemma encG_eq_iff (a b : GrossGroup) : encG a = encG b ↔ a = b :=
  ⟨encG_inj a b, fun h => by rw [h]⟩

private def dropSetE : List Nat := dropSet.map encG
private def redP2E : List (List Nat) := redP2.map (fun l => l.map encG)
private def redCME : List (List Nat) := redCM.map (fun l => l.map encG)

set_option maxRecDepth 40000 in
-- kernel decide needs more recursion headroom here.
private lemma dropSetE_getD :
    ∀ j ∈ List.range 6, dropSetE.getD j 720 = encG (dropSet.getD j 0) := by decide

set_option maxRecDepth 40000 in
-- kernel decide needs more recursion headroom here.
private lemma redP2E_getD :
    ∀ j ∈ List.range 6, redP2E.getD j [] = (redP2.getD j []).map encG := by decide

set_option maxRecDepth 40000 in
-- kernel decide needs more recursion headroom here.
private lemma redCME_getD :
    ∀ j ∈ List.range 6, redCME.getD j [] = (redCM.getD j []).map encG := by decide

/-- Bool-to-`ZMod 2` bit view. -/
private def z2 (b : Bool) : ZMod 2 := if b then 1 else 0

private lemma z2_xor (a b : Bool) : z2 (xor a b) = z2 a + z2 b := by
  cases a <;> cases b <;> decide

/-- `ZMod 2` bit sums as one Bool xor-fold. -/
private lemma sum_map_z2_eq_foldl_xor {α : Type*} (f : α → Bool) (l : List α) :
    ∀ b : Bool, z2 b + (l.map (fun e => z2 (f e))).sum
      = z2 (l.foldl (fun acc e => xor acc (f e)) b) := by
  induction l with
  | nil => intro b; simp
  | cons x t ih =>
    intro b
    rw [List.map_cons, List.sum_cons, List.foldl_cons, ← ih (xor b (f x)), z2_xor, ← add_assoc]

private lemma sum_map_z2_eq_foldl_xor_false {α : Type*} (f : α → Bool) (l : List α) :
    (l.map (fun e => z2 (f e))).sum = z2 (l.foldl (fun acc e => xor acc (f e)) false) := by
  have h := sum_map_z2_eq_foldl_xor f l false
  rwa [show z2 false = 0 from rfl, zero_add] at h

/-- Encoded sparse boundary-column entry (`ZMod 2` view). -/
private def d2E (A1 A2 A3 B1 B2 B3 eh : Nat) (j : Fin 2) : ZMod 2 :=
  if j = 0 then (if eh = A1 ∨ eh = A2 ∨ eh = A3 then 1 else 0)
  else (if eh = B1 ∨ eh = B2 ∨ eh = B3 then 1 else 0)

/-- Bool form of `d2E` (beq-only; the kernel hot path). -/
private def hitB (A1 A2 A3 B1 B2 B3 : Nat) (e : Nat × Fin 2) : Bool :=
  if e.2 = 0 then (e.1 == A1) || (e.1 == A2) || (e.1 == A3)
  else (e.1 == B1) || (e.1 == B2) || (e.1 == B3)

private lemma d2E_eq_z2_hitB (A1 A2 A3 B1 B2 B3 : Nat) (e : Nat × Fin 2) :
    d2E A1 A2 A3 B1 B2 B3 e.1 e.2 = z2 (hitB A1 A2 A3 B1 B2 B3 e) := by
  unfold d2E hitB
  by_cases hj : e.2 = 0
  · rw [if_pos hj, if_pos hj]
    by_cases h1 : e.1 = A1 <;> by_cases h2 : e.1 = A2 <;> by_cases h3 : e.1 = A3 <;>
      simp [h1, h2, h3, z2]
  · rw [if_neg hj, if_neg hj]
    by_cases h1 : e.1 = B1 <;> by_cases h2 : e.1 = B2 <;> by_cases h3 : e.1 = B3 <;>
      simp [h1, h2, h3, z2]

/-- `d2term` through the encoding: compare `encG h` against the six encoded
translates `encG (p + monomial)` (no group subtraction in the kernel loop). -/
private lemma d2term_eq_d2E (p h : GrossGroup) (j : Fin 2) :
    d2term p h j
      = d2E (encG (p + ((3 : ZMod 12), (0 : ZMod 6)))) (encG (p + ((0 : ZMod 12), (1 : ZMod 6))))
            (encG (p + ((0 : ZMod 12), (2 : ZMod 6)))) (encG (p + ((0 : ZMod 12), (3 : ZMod 6))))
            (encG (p + ((1 : ZMod 12), (0 : ZMod 6)))) (encG (p + ((2 : ZMod 12), (0 : ZMod 6))))
            (encG h) j := by
  have hiff : ∀ c : GrossGroup, h - p = c ↔ encG h = encG (p + c) := fun c => by
    rw [sub_eq_iff_eq_add, add_comm c p, encG_eq_iff]
  simp only [d2term, grossA, grossB, d2E]
  by_cases hj : j = 0
  · rw [if_pos hj, if_pos hj]
    exact if_congr (or_congr (hiff _) (or_congr (hiff _) (hiff _))) rfl rfl
  · rw [if_neg hj, if_neg hj]
    exact if_congr (or_congr (hiff _) (or_congr (hiff _) (hiff _))) rfl rfl

/-- `cmTerm` mirror of `d2term_eq_d2E` (translates are `v - monomial`). -/
private lemma cmTerm_eq_d2E (v h : GrossGroup) (j : Fin 2) :
    cmTerm v h j
      = d2E (encG (v - ((0 : ZMod 12), (3 : ZMod 6)))) (encG (v - ((1 : ZMod 12), (0 : ZMod 6))))
            (encG (v - ((2 : ZMod 12), (0 : ZMod 6)))) (encG (v - ((3 : ZMod 12), (0 : ZMod 6))))
            (encG (v - ((0 : ZMod 12), (1 : ZMod 6)))) (encG (v - ((0 : ZMod 12), (2 : ZMod 6))))
            (encG h) j := by
  have hiff : ∀ c : GrossGroup, v - h = c ↔ encG h = encG (v - c) := fun c =>
    (⟨fun hc => by rw [← hc, sub_sub_cancel], fun hc => by rw [hc, sub_sub_cancel]⟩ :
        v - h = c ↔ h = v - c).trans (encG_eq_iff h (v - c)).symm
  simp only [cmTerm, grossA, grossB, d2E]
  by_cases hj : j = 0
  · rw [if_pos hj, if_pos hj]
    exact if_congr (or_congr (hiff _) (or_congr (hiff _) (hiff _))) rfl rfl
  · rw [if_neg hj, if_neg hj]
    exact if_congr (or_congr (hiff _) (or_congr (hiff _) (hiff _))) rfl rfl

private lemma bool_eq_false_of_ne_true : ∀ b : Bool, b ≠ true → b = false := fun b => by
  cases b
  · intro _; rfl
  · intro h; exact absurd rfl h

/-- Encoded kernel-correction as a Bool xor-fold (beq/contains only). -/
private def kerCorrB (redE : List (List Nat)) (ep ep' : Nat) : Bool :=
  ((List.range 6).filter (fun j => dropSetE.getD j 720 == ep)).foldl
    (fun acc j => xor acc ((redE.getD j []).contains ep')) false

private lemma kerCorrection_eq_kerCorrB (red : List (List GrossGroup)) (redE : List (List Nat))
    (hredE : ∀ j ∈ List.range 6, redE.getD j [] = (red.getD j []).map encG)
    (p p' : GrossGroup) :
    kerCorrection red p p' = z2 (kerCorrB redE (encG p) (encG p')) := by
  rw [kerCorrection, foldl_add_eq_sum]
  have hfe : (List.range 6).filter (fun j => decide (dropSet.getD j 0 = p))
      = (List.range 6).filter (fun j => dropSetE.getD j 720 == encG p) := by
    refine List.filter_congr fun j hj => ?_
    rw [dropSetE_getD j hj]
    by_cases hc : dropSet.getD j 0 = p
    · rw [decide_eq_true hc, hc, beq_self_eq_true]
    · rw [decide_eq_false hc,
        bool_eq_false_of_ne_true _ (fun ht => hc ((encG_eq_iff _ _).mp (eq_of_beq ht)))]
  rw [hfe]
  have hmapc : ((List.range 6).filter (fun j => dropSetE.getD j 720 == encG p)).map
        (fun j => if (red.getD j []).contains p' then (1 : ZMod 2) else 0)
      = ((List.range 6).filter (fun j => dropSetE.getD j 720 == encG p)).map
        (fun j => z2 ((redE.getD j []).contains (encG p'))) := by
    refine List.map_congr_left fun j hj => ?_
    rw [hredE j (List.mem_of_mem_filter hj)]
    have hcb : ((red.getD j []).map encG).contains (encG p') = (red.getD j []).contains p' := by
      by_cases hm : p' ∈ red.getD j []
      · rw [List.contains_iff_mem.mpr hm, List.contains_iff_mem.mpr
          ((List.mem_map_of_injective (fun a b => encG_inj a b)).mpr hm)]
      · rw [bool_eq_false_of_ne_true _ (fun ht => hm (List.contains_iff_mem.mp ht)),
          bool_eq_false_of_ne_true _ (fun ht => hm ((List.mem_map_of_injective
            (fun a b => encG_inj a b)).mp (List.contains_iff_mem.mp ht)))]
    rw [hcb]
    rfl
  rw [hmapc, sum_map_z2_eq_foldl_xor_false (fun j => (redE.getD j []).contains (encG p'))]
  rfl

/-- Per-input shifted-point tables: `(encG p, the six encoded translate points)`. -/
private def shiftTableXE : List (Nat × (Nat × Nat × Nat × Nat × Nat × Nat)) :=
  grossEnum.map (fun p =>
    (encG p, (encG (p + ((3 : ZMod 12), (0 : ZMod 6))), encG (p + ((0 : ZMod 12), (1 : ZMod 6))),
      encG (p + ((0 : ZMod 12), (2 : ZMod 6))), encG (p + ((0 : ZMod 12), (3 : ZMod 6))),
      encG (p + ((1 : ZMod 12), (0 : ZMod 6))), encG (p + ((2 : ZMod 12), (0 : ZMod 6))))))

private def shiftTableZE : List (Nat × (Nat × Nat × Nat × Nat × Nat × Nat)) :=
  grossEnum.map (fun v =>
    (encG v, (encG (v - ((0 : ZMod 12), (3 : ZMod 6))), encG (v - ((1 : ZMod 12), (0 : ZMod 6))),
      encG (v - ((2 : ZMod 12), (0 : ZMod 6))), encG (v - ((3 : ZMod 12), (0 : ZMod 6))),
      encG (v - ((0 : ZMod 12), (1 : ZMod 6))), encG (v - ((0 : ZMod 12), (2 : ZMod 6))))))

/-- Encoded per-row bucket tables (one `phiX`/`phiZ` filter pass per output row). -/
private def phiXBucketsE : List (Nat × List (Nat × Fin 2)) :=
  grossEnum.map (fun p' => (encG p',
    (phiX.filter (fun pr => pr.1 = p')).map (fun pr => (encG pr.2.1, pr.2.2))))

private def phiZBucketsE : List (Nat × List (Nat × Fin 2)) :=
  grossEnum.map (fun p' => (encG p',
    (phiZ.filter (fun pr => pr.1 = p')).map (fun pr => (encG pr.2.1, pr.2.2))))

/-- Bool-only per-row check: xor-fold of hits, xor correction, compare to Kronecker. -/
private def checkRowB (tbl : List (Nat × (Nat × Nat × Nat × Nat × Nat × Nat)))
    (redE : List (List Nat)) (ep' : Nat) (bucketE : List (Nat × Fin 2)) : Bool :=
  tbl.all (fun ps =>
    xor (bucketE.foldl (fun acc e => xor acc (hitB ps.2.1 ps.2.2.1 ps.2.2.2.1 ps.2.2.2.2.1
          ps.2.2.2.2.2.1 ps.2.2.2.2.2.2 e)) false)
        (kerCorrB redE ps.1 ep')
      == (ep' == ps.1))

private lemma decoder_X_tableB :
    phiXBucketsE.all (fun pb => checkRowB shiftTableXE redP2E pb.1 pb.2) = true := by
  decide +kernel

private lemma decoder_Z_tableB :
    phiZBucketsE.all (fun pb => checkRowB shiftTableZE redCME pb.1 pb.2) = true := by
  decide +kernel

/-- Bool-level row identity unpacked to the `ZMod 2` identity. -/
private lemma row_check_to_zmod {bp cb : Bool} {ep' ep : Nat}
    (h : (xor bp cb == (ep' == ep)) = true) :
    z2 bp + z2 cb = (if ep' = ep then (1 : ZMod 2) else 0) := by
  rw [← z2_xor, eq_of_beq h]
  by_cases hc : ep' = ep
  · simp [hc, z2]
  · simp [hc, z2]

/-- **Face decoder identity** (kernel-checked via the encoded Bool tables): the
`phiX` decoder inverts `∂₂` on the trimmed face subspace, modulo the `redP2`
kernel basis. Over all `72×72` basis pairs. This is the independence hard-core
for the X block — it yields `∂₂ f = 0 ∧ f|_dropSet = 0 → f = 0` by linearity. -/
theorem decoder_identity_X :
    ∀ p p' : GrossGroup,
      decodeXAt p p' + kerCorrection redP2 p p' = (if p' = p then 1 else 0) := by
  intro p p'
  have h1 : checkRowB shiftTableXE redP2E (encG p')
      ((phiX.filter (fun pr => pr.1 = p')).map (fun pr => (encG pr.2.1, pr.2.2))) = true :=
    List.all_eq_true.mp decoder_X_tableB _ (List.mem_map.mpr ⟨p', grossEnum_complete p', rfl⟩)
  have h2 := List.all_eq_true.mp h1 _ (List.mem_map.mpr ⟨p, grossEnum_complete p, rfl⟩)
  have h3 := row_check_to_zmod h2
  rw [decodeXAt, foldl_add_eq_sum, kerCorrection_eq_kerCorrB redP2 redP2E redP2E_getD]
  have hite : (if p' = p then (1 : ZMod 2) else 0) = (if encG p' = encG p then 1 else 0) :=
    (if_congr (encG_eq_iff p' p) rfl rfl).symm
  rw [hite]
  have hmap : ((phiX.filter (fun pr => pr.1 = p')).map (fun pr => d2term p pr.2.1 pr.2.2))
      = ((phiX.filter (fun pr => pr.1 = p')).map (fun pr => (encG pr.2.1, pr.2.2))).map
          (fun e => z2 (hitB (encG (p + ((3 : ZMod 12), (0 : ZMod 6))))
            (encG (p + ((0 : ZMod 12), (1 : ZMod 6)))) (encG (p + ((0 : ZMod 12), (2 : ZMod 6))))
            (encG (p + ((0 : ZMod 12), (3 : ZMod 6)))) (encG (p + ((1 : ZMod 12), (0 : ZMod 6))))
            (encG (p + ((2 : ZMod 12), (0 : ZMod 6)))) e)) := by
    rw [List.map_map]
    refine List.map_congr_left fun pr _ => ?_
    rw [d2term_eq_d2E p pr.2.1 pr.2.2]
    exact d2E_eq_z2_hitB _ _ _ _ _ _ (encG pr.2.1, pr.2.2)
  rw [hmap, sum_map_z2_eq_foldl_xor_false]
  exact h3

/-- **Vertex decoder identity** (kernel-checked): mirror of
`decoder_identity_X` for the Z block (`cutMap`, `phiZ`, `redCM`). -/
theorem decoder_identity_Z :
    ∀ p p' : GrossGroup,
      decodeZAt p p' + kerCorrection redCM p p' = (if p' = p then 1 else 0) := by
  intro p p'
  have h1 : checkRowB shiftTableZE redCME (encG p')
      ((phiZ.filter (fun pr => pr.1 = p')).map (fun pr => (encG pr.2.1, pr.2.2))) = true :=
    List.all_eq_true.mp decoder_Z_tableB _ (List.mem_map.mpr ⟨p', grossEnum_complete p', rfl⟩)
  have h2 := List.all_eq_true.mp h1 _ (List.mem_map.mpr ⟨p, grossEnum_complete p, rfl⟩)
  have h3 := row_check_to_zmod h2
  rw [decodeZAt, foldl_add_eq_sum, kerCorrection_eq_kerCorrB redCM redCME redCME_getD]
  have hite : (if p' = p then (1 : ZMod 2) else 0) = (if encG p' = encG p then 1 else 0) :=
    (if_congr (encG_eq_iff p' p) rfl rfl).symm
  rw [hite]
  have hmap : ((phiZ.filter (fun pr => pr.1 = p')).map (fun pr => cmTerm p pr.2.1 pr.2.2))
      = ((phiZ.filter (fun pr => pr.1 = p')).map (fun pr => (encG pr.2.1, pr.2.2))).map
          (fun e => z2 (hitB (encG (p - ((0 : ZMod 12), (3 : ZMod 6))))
            (encG (p - ((1 : ZMod 12), (0 : ZMod 6)))) (encG (p - ((2 : ZMod 12), (0 : ZMod 6))))
            (encG (p - ((3 : ZMod 12), (0 : ZMod 6)))) (encG (p - ((0 : ZMod 12), (1 : ZMod 6))))
            (encG (p - ((0 : ZMod 12), (2 : ZMod 6)))) e)) := by
    rw [List.map_map]
    refine List.map_congr_left fun pr _ => ?_
    rw [cmTerm_eq_d2E p pr.2.1 pr.2.2]
    exact d2E_eq_z2_hitB _ _ _ _ _ _ (encG pr.2.1, pr.2.2)
  rw [hmap, sum_map_z2_eq_foldl_xor_false]
  exact h3

/-! ## §3  Lift the decoder identities to all chains (the independence core)

`decoder_identity_X` is a per-basis-vector fact; here we lift it by linearity
to `face_kernel_trivial : ∂₂ f = 0 ∧ f|_dropSet = 0 → f = 0` (and the mirror
`vtx_kernel_trivial`). These feed the block-split `rowsLinearIndependent`. -/

/-- **(L1, X)** Basis expansion of `∂₂` in the sparse `d2term` form. -/
lemma boundary2_apply_eq_sum_d2term (f : GrossGroup → ZMod 2) (h : GrossGroup) (j : Fin 2) :
    grossComplex.boundary2 f (h, j) = ∑ p : GrossGroup, f p * d2term p h j := by
  have hgr : grossComplex.boundary2 f = bbBoundary2Fn grossA grossB f := rfl
  rw [hgr]
  by_cases hj : j = 0
  · subst hj
    change (grossA ⋆ f) h = ∑ p : GrossGroup, f p * d2term p h 0
    rw [conv_apply]
    refine (Equiv.sum_comp (Equiv.subLeft h) (fun x => grossA x * f (h - x))).symm.trans ?_
    refine Finset.sum_congr rfl fun p _ => ?_
    have hp : h - (h - p) = p := by abel
    simp [d2term, Equiv.subLeft_apply, hp, mul_comm]
  · have hj1 : j = 1 := by omega
    subst hj1
    change (grossB ⋆ f) h = ∑ p : GrossGroup, f p * d2term p h 1
    rw [conv_apply]
    refine (Equiv.sum_comp (Equiv.subLeft h) (fun x => grossB x * f (h - x))).symm.trans ?_
    refine Finset.sum_congr rfl fun p _ => ?_
    have hp : h - (h - p) = p := by abel
    simp [d2term, Equiv.subLeft_apply, hp, mul_comm]

/-- **(L1, Z)** `cutMap(δ_v)` per qubit, in the sparse `cmTerm` form. -/
lemma cmTerm_eq (v h : GrossGroup) (j : Fin 2) :
    grossComplex.boundary1 (Pi.single (h, j) 1) v = cmTerm v h j := by
  have hgr : grossComplex.boundary1 (Pi.single (h, j) (1:ZMod 2))
      = bbBoundary1Fn grossA grossB (Pi.single (h, j) 1) := rfl
  rw [hgr, bbBoundary1Fn]
  by_cases hj : j = 0
  · subst hj
    have hL : leftHalf (Pi.single ((h, (0:Fin 2))) (1:ZMod 2)) = Pi.single h 1 := by
      funext g; simp [leftHalf, Pi.single_apply, Prod.ext_iff]
    have hR : rightHalf (Pi.single ((h, (0:Fin 2))) (1:ZMod 2)) = 0 := by
      funext g; simp [rightHalf, Prod.ext_iff]
    rw [hL, hR, conv_comm grossB (Pi.single h 1), conv_single_left_apply]
    simp [cmTerm, conv_apply]
  · have hj1 : j = 1 := by omega
    subst hj1
    have hL : leftHalf (Pi.single ((h, (1:Fin 2))) (1:ZMod 2)) = 0 := by
      funext g; simp [leftHalf, Prod.ext_iff]
    have hR : rightHalf (Pi.single ((h, (1:Fin 2))) (1:ZMod 2)) = Pi.single h 1 := by
      funext g; simp [rightHalf, Pi.single_apply, Prod.ext_iff]
    rw [hL, hR, conv_comm grossA (Pi.single h 1), conv_single_left_apply]
    simp [cmTerm, conv_apply]

lemma cutMap_apply_eq_sum_cmTerm (s : GrossGroup → ZMod 2) (h : GrossGroup) (j : Fin 2) :
    grossComplex.cutMap s (h, j) = ∑ v : GrossGroup, s v * cmTerm v h j := by
  rw [HomologicalCode.cutMap_apply]
  exact Finset.sum_congr rfl fun v _ => by rw [cmTerm_eq]

/-- Interchange a `Fintype` sum with a `List` sum (over `ZMod 2`). -/
private lemma finset_sum_list_sum_comm {ι α : Type*} [Fintype ι] (l : List α)
    (k : ι → α → ZMod 2) :
    ∑ p : ι, (l.map (k p)).sum = (l.map (fun x => ∑ p : ι, k p x)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

/-- `kerCorrection` vanishes off the drop-set. -/
private lemma kerCorrection_eq_zero_of_not_mem (red : List (List GrossGroup)) {p : GrossGroup}
    (hp : p ∉ dropSet) (p' : GrossGroup) : kerCorrection red p p' = 0 := by
  have hempty : (List.range 6).filter (fun j => dropSet.getD j 0 = p) = [] := by
    rw [List.filter_eq_nil_iff]
    intro j hj hcond
    rw [List.mem_range] at hj
    have hlen : dropSet.length = 6 := by decide
    have hmem : dropSet.getD j 0 ∈ dropSet := by
      rw [List.getD_eq_getElem dropSet 0 (by omega)]; exact List.getElem_mem _
    have : dropSet.getD j 0 = p := by simpa using hcond
    exact hp (this ▸ hmem)
  rw [kerCorrection, hempty]; rfl

/-- **(A, X)** A `∂₂`-cycle makes the `phiX`-decoder sum vanish. -/
lemma sum_decodeXAt_eq_zero_of_boundary {f : GrossGroup → ZMod 2}
    (hf : grossComplex.boundary2 f = 0) (p' : GrossGroup) :
    ∑ p : GrossGroup, f p * decodeXAt p p' = 0 := by
  have hstep : ∀ p : GrossGroup, f p * decodeXAt p p'
      = ((phiX.filter (fun pr => pr.1 = p')).map
          (fun pr => f p * d2term p pr.2.1 pr.2.2)).sum := fun p => by
    rw [decodeXAt, foldl_add_eq_sum, List.sum_map_mul_left]
  simp_rw [hstep]
  rw [finset_sum_list_sum_comm]
  have hz : ∀ pr : GrossGroup × (GrossGroup × Fin 2),
      (∑ p : GrossGroup, f p * d2term p pr.2.1 pr.2.2) = 0 := fun pr => by
    rw [← boundary2_apply_eq_sum_d2term, hf]; rfl
  simp [hz]

/-- **(A, Z)** A `cutMap`-kernel chain makes the `phiZ`-decoder sum vanish. -/
lemma sum_decodeZAt_eq_zero_of_cutMap {s : GrossGroup → ZMod 2}
    (hs : grossComplex.cutMap s = 0) (p' : GrossGroup) :
    ∑ v : GrossGroup, s v * decodeZAt v p' = 0 := by
  have hstep : ∀ v : GrossGroup, s v * decodeZAt v p'
      = ((phiZ.filter (fun pr => pr.1 = p')).map
          (fun pr => s v * cmTerm v pr.2.1 pr.2.2)).sum := fun v => by
    rw [decodeZAt, foldl_add_eq_sum, List.sum_map_mul_left]
  simp_rw [hstep]
  rw [finset_sum_list_sum_comm]
  have hz : ∀ pr : GrossGroup × (GrossGroup × Fin 2),
      (∑ v : GrossGroup, s v * cmTerm v pr.2.1 pr.2.2) = 0 := fun pr => by
    rw [← cutMap_apply_eq_sum_cmTerm, hs]; rfl
  simp [hz]

/-- **Face block independence core**: a `∂₂`-cycle vanishing on `dropSet` is `0`. -/
lemma face_kernel_trivial {f : GrossGroup → ZMod 2}
    (hf : grossComplex.boundary2 f = 0) (hd : ∀ d ∈ dropSet, f d = 0) : f = 0 := by
  funext p'
  have hId : ∀ p, decodeXAt p p' = (if p' = p then 1 else 0) + kerCorrection redP2 p p' :=
    fun p => by rw [← decoder_identity_X p p', add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hA := sum_decodeXAt_eq_zero_of_boundary hf p'
  simp_rw [hId, mul_add, Finset.sum_add_distrib] at hA
  have hfirst : (∑ p : GrossGroup, f p * (if p' = p then (1:ZMod 2) else 0)) = f p' := by
    rw [Finset.sum_eq_single p']
    · simp
    · intro b _ hb; rw [if_neg (Ne.symm hb)]; ring
    · intro h; exact absurd (Finset.mem_univ p') h
  have hsecond : (∑ p : GrossGroup, f p * kerCorrection redP2 p p') = 0 := by
    refine Finset.sum_eq_zero fun p _ => ?_
    by_cases hpd : p ∈ dropSet
    · rw [hd p hpd]; ring
    · rw [kerCorrection_eq_zero_of_not_mem redP2 hpd]; ring
  rw [hfirst, hsecond, add_zero] at hA
  exact hA

/-- **Vertex block independence core**: a `cutMap`-kernel chain vanishing on
`dropSet` is `0`. -/
lemma vtx_kernel_trivial {s : GrossGroup → ZMod 2}
    (hs : grossComplex.cutMap s = 0) (hd : ∀ d ∈ dropSet, s d = 0) : s = 0 := by
  funext p'
  have hId : ∀ v, decodeZAt v p' = (if p' = v then 1 else 0) + kerCorrection redCM v p' :=
    fun v => by rw [← decoder_identity_Z v p', add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hA := sum_decodeZAt_eq_zero_of_cutMap hs p'
  simp_rw [hId, mul_add, Finset.sum_add_distrib] at hA
  have hfirst : (∑ v : GrossGroup, s v * (if p' = v then (1:ZMod 2) else 0)) = s p' := by
    rw [Finset.sum_eq_single p']
    · simp
    · intro b _ hb; rw [if_neg (Ne.symm hb)]; ring
    · intro h; exact absurd (Finset.mem_univ p') h
  have hsecond : (∑ v : GrossGroup, s v * kerCorrection redCM v p') = 0 := by
    refine Finset.sum_eq_zero fun v _ => ?_
    by_cases hvd : v ∈ dropSet
    · rw [hd v hvd]; ring
    · rw [kerCorrection_eq_zero_of_not_mem redCM hvd]; ring
  rw [hfirst, hsecond, add_zero] at hA
  exact hA

/-! ## §4  Closure equality (obligation 1)

The trimmed 132-generator list (66 kept vertex stabs ++ 66 kept face stabs)
generates the same subgroup as the full homological generator set. The dropped
generators re-enter via the reduced kernel relations `redP2` / `redCM`. -/

-- NB: list-mapped generators must be typed `List grossComplex.C2` / `.C0`, not
-- `List GrossGroup`: the projection `C2`/`C0` is defeq but not syntactically
-- `GrossGroup`, which silently breaks `rw`/`simp` list-lemma matching.

/-- Product of face stabs over a list = `chainXOperator (∂₂ (Σ indicators))`. -/
lemma faceStabOf_listProd (L : List grossComplex.C2) :
    (L.map grossComplex.faceStabOf).prod
      = grossComplex.chainXOperator
          (grossComplex.boundary2 ((L.map (fun f => grossComplex.singleFace f)).sum)) := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.sum_nil, map_zero,
      HomologicalCode.chainXOperator_zero]
  | cons f L ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.sum_cons, map_add,
      HomologicalCode.chainXOperator_add, HomologicalCode.chainXOperator_boundary2_singleFace, ih]

/-- Product of vertex stabs over a list = `chainZOperator (cutMap (Σ indicators))`. -/
lemma vertexStabOf_listProd (L : List grossComplex.C0) :
    (L.map grossComplex.vertexStabOf).prod
      = grossComplex.chainZOperator
          (grossComplex.cutMap ((L.map (fun v => grossComplex.singleVtx v)).sum)) := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.sum_nil, map_zero,
      HomologicalCode.chainZOperator_zero]
  | cons v L ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.sum_cons, map_add,
      HomologicalCode.chainZOperator_add, HomologicalCode.chainZOperator_cutMap_singleVtx, ih]

/-! ## §4b  Boundary-column bridges and the per-drop closure relations -/

lemma boundary2_singleFace_apply (d : GrossGroup) (h : GrossGroup) (j : Fin 2) :
    grossComplex.boundary2 (grossComplex.singleFace d) (h, j) = d2term d h j := by
  rw [boundary2_apply_eq_sum_d2term]
  have hpt : ∀ p : GrossGroup, grossComplex.singleFace d p = (if p = d then 1 else 0) :=
    fun p => by rw [HomologicalCode.singleFace]; exact Pi.single_apply d 1 p
  simp [hpt, Finset.sum_ite_eq']

lemma boundary2_listSum_singleFace_apply (L : List grossComplex.C2) (h : GrossGroup) (j : Fin 2) :
    grossComplex.boundary2 ((L.map (fun f => grossComplex.singleFace f)).sum) (h, j)
      = (L.map (fun f : grossComplex.C2 => d2term f h j)).sum := by
  induction L with
  | nil => simp only [List.map_nil, List.sum_nil, map_zero]; rfl
  | cons f L ih =>
    rw [List.map_cons, List.sum_cons, map_add, Pi.add_apply, boundary2_singleFace_apply, ih,
        List.map_cons, List.sum_cons]


def keptPartX : List (List GrossGroup) := [[((0 : ZMod 12), (4 : ZMod 6)), ((1 : ZMod 12),
  (2 : ZMod 6)), ((1 : ZMod 12), (4 : ZMod 6)), ((2 : ZMod 12), (3 : ZMod 6)), ((2 : ZMod 12),
  (5 : ZMod 6)), ((3 : ZMod 12), (0 : ZMod 6)), ((3 : ZMod 12), (1 : ZMod 6)), ((3 : ZMod 12),
  (2 : ZMod 6)), ((3 : ZMod 12), (5 : ZMod 6)), ((4 : ZMod 12), (0 : ZMod 6)), ((4 : ZMod 12),
  (3 : ZMod 6)), ((4 : ZMod 12), (4 : ZMod 6)), ((4 : ZMod 12), (5 : ZMod 6)), ((5 : ZMod 12),
  (0 : ZMod 6)), ((5 : ZMod 12), (1 : ZMod 6)), ((5 : ZMod 12), (4 : ZMod 6)), ((5 : ZMod 12),
  (5 : ZMod 6)), ((6 : ZMod 12), (0 : ZMod 6)), ((6 : ZMod 12), (4 : ZMod 6)), ((7 : ZMod 12),
  (2 : ZMod 6)), ((7 : ZMod 12), (4 : ZMod 6)), ((8 : ZMod 12), (3 : ZMod 6)), ((8 : ZMod 12),
  (5 : ZMod 6)), ((9 : ZMod 12), (0 : ZMod 6)), ((9 : ZMod 12), (1 : ZMod 6)), ((9 : ZMod 12),
  (2 : ZMod 6)), ((9 : ZMod 12), (5 : ZMod 6)), ((10 : ZMod 12), (0 : ZMod 6)), ((10 : ZMod 12),
  (3 : ZMod 6)), ((10 : ZMod 12), (4 : ZMod 6)), ((10 : ZMod 12), (5 : ZMod 6)), ((11 : ZMod 12),
  (0 : ZMod 6)), ((11 : ZMod 12), (1 : ZMod 6)), ((11 : ZMod 12), (4 : ZMod 6)), ((11 : ZMod 12),
  (5 : ZMod 6))], [((0 : ZMod 12), (5 : ZMod 6)), ((1 : ZMod 12), (3 : ZMod 6)), ((1 : ZMod 12),
  (5 : ZMod 6)), ((2 : ZMod 12), (0 : ZMod 6)), ((2 : ZMod 12), (4 : ZMod 6)), ((3 : ZMod 12),
  (0 : ZMod 6)), ((3 : ZMod 12), (1 : ZMod 6)), ((3 : ZMod 12), (2 : ZMod 6)), ((3 : ZMod 12),
  (3 : ZMod 6)), ((4 : ZMod 12), (0 : ZMod 6)), ((4 : ZMod 12), (1 : ZMod 6)), ((4 : ZMod 12),
  (4 : ZMod 6)), ((4 : ZMod 12), (5 : ZMod 6)), ((5 : ZMod 12), (0 : ZMod 6)), ((5 : ZMod 12),
  (1 : ZMod 6)), ((5 : ZMod 12), (2 : ZMod 6)), ((5 : ZMod 12), (5 : ZMod 6)), ((6 : ZMod 12),
  (1 : ZMod 6)), ((6 : ZMod 12), (5 : ZMod 6)), ((7 : ZMod 12), (3 : ZMod 6)), ((7 : ZMod 12),
  (5 : ZMod 6)), ((8 : ZMod 12), (0 : ZMod 6)), ((8 : ZMod 12), (4 : ZMod 6)), ((9 : ZMod 12),
  (0 : ZMod 6)), ((9 : ZMod 12), (1 : ZMod 6)), ((9 : ZMod 12), (2 : ZMod 6)), ((9 : ZMod 12),
  (3 : ZMod 6)), ((10 : ZMod 12), (0 : ZMod 6)), ((10 : ZMod 12), (1 : ZMod 6)), ((10 : ZMod 12),
  (4 : ZMod 6)), ((10 : ZMod 12), (5 : ZMod 6)), ((11 : ZMod 12), (0 : ZMod 6)), ((11 : ZMod 12),
  (1 : ZMod 6)), ((11 : ZMod 12), (2 : ZMod 6)), ((11 : ZMod 12), (5 : ZMod 6))], [((0 : ZMod 12),
  (4 : ZMod 6)), ((1 : ZMod 12), (3 : ZMod 6)), ((1 : ZMod 12), (5 : ZMod 6)), ((2 : ZMod 12),
  (0 : ZMod 6)), ((2 : ZMod 12), (1 : ZMod 6)), ((2 : ZMod 12), (2 : ZMod 6)), ((2 : ZMod 12),
  (5 : ZMod 6)), ((3 : ZMod 12), (0 : ZMod 6)), ((3 : ZMod 12), (3 : ZMod 6)), ((3 : ZMod 12),
  (4 : ZMod 6)), ((3 : ZMod 12), (5 : ZMod 6)), ((4 : ZMod 12), (0 : ZMod 6)), ((4 : ZMod 12),
  (1 : ZMod 6)), ((4 : ZMod 12), (4 : ZMod 6)), ((4 : ZMod 12), (5 : ZMod 6)), ((5 : ZMod 12),
  (0 : ZMod 6)), ((5 : ZMod 12), (4 : ZMod 6)), ((6 : ZMod 12), (2 : ZMod 6)), ((6 : ZMod 12),
  (4 : ZMod 6)), ((7 : ZMod 12), (3 : ZMod 6)), ((7 : ZMod 12), (5 : ZMod 6)), ((8 : ZMod 12),
  (0 : ZMod 6)), ((8 : ZMod 12), (1 : ZMod 6)), ((8 : ZMod 12), (2 : ZMod 6)), ((8 : ZMod 12),
  (5 : ZMod 6)), ((9 : ZMod 12), (0 : ZMod 6)), ((9 : ZMod 12), (3 : ZMod 6)), ((9 : ZMod 12),
  (4 : ZMod 6)), ((9 : ZMod 12), (5 : ZMod 6)), ((10 : ZMod 12), (0 : ZMod 6)), ((10 : ZMod 12),
  (1 : ZMod 6)), ((10 : ZMod 12), (4 : ZMod 6)), ((10 : ZMod 12), (5 : ZMod 6)), ((11 : ZMod 12),
  (0 : ZMod 6)), ((11 : ZMod 12), (4 : ZMod 6))], [((0 : ZMod 12), (5 : ZMod 6)), ((1 : ZMod 12),
  (2 : ZMod 6)), ((1 : ZMod 12), (3 : ZMod 6)), ((1 : ZMod 12), (4 : ZMod 6)), ((1 : ZMod 12),
  (5 : ZMod 6)), ((2 : ZMod 12), (1 : ZMod 6)), ((2 : ZMod 12), (5 : ZMod 6)), ((3 : ZMod 12),
  (0 : ZMod 6)), ((3 : ZMod 12), (1 : ZMod 6)), ((3 : ZMod 12), (4 : ZMod 6)), ((3 : ZMod 12),
  (5 : ZMod 6)), ((4 : ZMod 12), (1 : ZMod 6)), ((4 : ZMod 12), (3 : ZMod 6)), ((5 : ZMod 12),
  (0 : ZMod 6)), ((5 : ZMod 12), (1 : ZMod 6)), ((5 : ZMod 12), (2 : ZMod 6)), ((5 : ZMod 12),
  (3 : ZMod 6)), ((6 : ZMod 12), (3 : ZMod 6)), ((6 : ZMod 12), (5 : ZMod 6)), ((7 : ZMod 12),
  (2 : ZMod 6)), ((7 : ZMod 12), (3 : ZMod 6)), ((7 : ZMod 12), (4 : ZMod 6)), ((7 : ZMod 12),
  (5 : ZMod 6)), ((8 : ZMod 12), (1 : ZMod 6)), ((8 : ZMod 12), (5 : ZMod 6)), ((9 : ZMod 12),
  (0 : ZMod 6)), ((9 : ZMod 12), (1 : ZMod 6)), ((9 : ZMod 12), (4 : ZMod 6)), ((9 : ZMod 12),
  (5 : ZMod 6)), ((10 : ZMod 12), (1 : ZMod 6)), ((10 : ZMod 12), (3 : ZMod 6)), ((11 : ZMod 12),
  (0 : ZMod 6)), ((11 : ZMod 12), (1 : ZMod 6)), ((11 : ZMod 12), (2 : ZMod 6)), ((11 : ZMod 12),
  (3 : ZMod 6))], [((1 : ZMod 12), (2 : ZMod 6)), ((1 : ZMod 12), (3 : ZMod 6)), ((1 : ZMod 12),
  (5 : ZMod 6)), ((2 : ZMod 12), (0 : ZMod 6)), ((2 : ZMod 12), (2 : ZMod 6)), ((2 : ZMod 12),
  (3 : ZMod 6)), ((2 : ZMod 12), (5 : ZMod 6)), ((4 : ZMod 12), (0 : ZMod 6)), ((4 : ZMod 12),
  (2 : ZMod 6)), ((4 : ZMod 12), (3 : ZMod 6)), ((4 : ZMod 12), (5 : ZMod 6)), ((5 : ZMod 12),
  (0 : ZMod 6)), ((5 : ZMod 12), (2 : ZMod 6)), ((5 : ZMod 12), (3 : ZMod 6)), ((5 : ZMod 12),
  (5 : ZMod 6)), ((7 : ZMod 12), (0 : ZMod 6)), ((7 : ZMod 12), (2 : ZMod 6)), ((7 : ZMod 12),
  (3 : ZMod 6)), ((7 : ZMod 12), (5 : ZMod 6)), ((8 : ZMod 12), (0 : ZMod 6)), ((8 : ZMod 12),
  (2 : ZMod 6)), ((8 : ZMod 12), (3 : ZMod 6)), ((8 : ZMod 12), (5 : ZMod 6)), ((10 : ZMod 12),
  (0 : ZMod 6)), ((10 : ZMod 12), (2 : ZMod 6)), ((10 : ZMod 12), (3 : ZMod 6)), ((10 : ZMod 12),
  (5 : ZMod 6)), ((11 : ZMod 12), (0 : ZMod 6)), ((11 : ZMod 12), (2 : ZMod 6)), ((11 : ZMod 12),
  (3 : ZMod 6)), ((11 : ZMod 12), (5 : ZMod 6))], [((1 : ZMod 12), (2 : ZMod 6)), ((1 : ZMod 12),
  (4 : ZMod 6)), ((1 : ZMod 12), (5 : ZMod 6)), ((2 : ZMod 12), (1 : ZMod 6)), ((2 : ZMod 12),
  (2 : ZMod 6)), ((2 : ZMod 12), (4 : ZMod 6)), ((2 : ZMod 12), (5 : ZMod 6)), ((4 : ZMod 12),
  (1 : ZMod 6)), ((4 : ZMod 12), (2 : ZMod 6)), ((4 : ZMod 12), (4 : ZMod 6)), ((4 : ZMod 12),
  (5 : ZMod 6)), ((5 : ZMod 12), (1 : ZMod 6)), ((5 : ZMod 12), (2 : ZMod 6)), ((5 : ZMod 12),
  (4 : ZMod 6)), ((5 : ZMod 12), (5 : ZMod 6)), ((7 : ZMod 12), (1 : ZMod 6)), ((7 : ZMod 12),
  (2 : ZMod 6)), ((7 : ZMod 12), (4 : ZMod 6)), ((7 : ZMod 12), (5 : ZMod 6)), ((8 : ZMod 12),
  (1 : ZMod 6)), ((8 : ZMod 12), (2 : ZMod 6)), ((8 : ZMod 12), (4 : ZMod 6)), ((8 : ZMod 12),
  (5 : ZMod 6)), ((10 : ZMod 12), (1 : ZMod 6)), ((10 : ZMod 12), (2 : ZMod 6)), ((10 : ZMod 12),
  (4 : ZMod 6)), ((10 : ZMod 12), (5 : ZMod 6)), ((11 : ZMod 12), (1 : ZMod 6)), ((11 : ZMod 12),
  (2 : ZMod 6)), ((11 : ZMod 12), (4 : ZMod 6)), ((11 : ZMod 12), (5 : ZMod 6))]]

/-- Generic drop relation: if `df`'s boundary column equals the sum of `kp`'s
columns (a kernel relation) and each `kp` face stab is in `S`, then
`faceStabOf df ∈ closure S`. -/
lemma faceStab_drop_mem_closure {S : Set (NQubitPauliGroupElement grossComplex.numQubits)}
    (df : GrossGroup) (kp : List grossComplex.C2)
    (hrel : ∀ (h : GrossGroup) (j : Fin 2),
       d2term df h j = (kp.map (fun f : grossComplex.C2 => d2term f h j)).sum)
    (hkept : ∀ f ∈ kp, grossComplex.faceStabOf f ∈ S) :
    grossComplex.faceStabOf df ∈ Subgroup.closure S := by
  have hbd : grossComplex.boundary2 (grossComplex.singleFace df)
      = grossComplex.boundary2 ((kp.map (fun f => grossComplex.singleFace f)).sum) := by
    funext q; obtain ⟨h, j⟩ := q
    rw [boundary2_singleFace_apply, boundary2_listSum_singleFace_apply]
    exact hrel h j
  have heq : grossComplex.faceStabOf df = (kp.map grossComplex.faceStabOf).prod := by
    rw [faceStabOf_listProd, ← HomologicalCode.chainXOperator_boundary2_singleFace, hbd]
  rw [heq]
  exact Subgroup.list_prod_mem _ (fun g hg => by
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
    exact Subgroup.subset_closure (hkept f hf))

def keptPartZ : List (List GrossGroup) := [[((0 : ZMod 12), (4 : ZMod 6)), ((1 : ZMod 12),
  (2 : ZMod 6)), ((1 : ZMod 12), (4 : ZMod 6)), ((2 : ZMod 12), (1 : ZMod 6)), ((2 : ZMod 12),
  (2 : ZMod 6)), ((2 : ZMod 12), (3 : ZMod 6)), ((2 : ZMod 12), (4 : ZMod 6)), ((3 : ZMod 12),
  (2 : ZMod 6)), ((3 : ZMod 12), (3 : ZMod 6)), ((3 : ZMod 12), (4 : ZMod 6)), ((3 : ZMod 12),
  (5 : ZMod 6)), ((4 : ZMod 12), (0 : ZMod 6)), ((4 : ZMod 12), (1 : ZMod 6)), ((4 : ZMod 12),
  (2 : ZMod 6)), ((4 : ZMod 12), (3 : ZMod 6)), ((5 : ZMod 12), (3 : ZMod 6)), ((5 : ZMod 12),
  (5 : ZMod 6)), ((6 : ZMod 12), (0 : ZMod 6)), ((6 : ZMod 12), (4 : ZMod 6)), ((7 : ZMod 12),
  (2 : ZMod 6)), ((7 : ZMod 12), (4 : ZMod 6)), ((8 : ZMod 12), (1 : ZMod 6)), ((8 : ZMod 12),
  (2 : ZMod 6)), ((8 : ZMod 12), (3 : ZMod 6)), ((8 : ZMod 12), (4 : ZMod 6)), ((9 : ZMod 12),
  (2 : ZMod 6)), ((9 : ZMod 12), (3 : ZMod 6)), ((9 : ZMod 12), (4 : ZMod 6)), ((9 : ZMod 12),
  (5 : ZMod 6)), ((10 : ZMod 12), (0 : ZMod 6)), ((10 : ZMod 12), (1 : ZMod 6)), ((10 : ZMod 12),
  (2 : ZMod 6)), ((10 : ZMod 12), (3 : ZMod 6)), ((11 : ZMod 12), (3 : ZMod 6)), ((11 : ZMod 12),
  (5 : ZMod 6))], [((0 : ZMod 12), (5 : ZMod 6)), ((1 : ZMod 12), (3 : ZMod 6)), ((1 : ZMod 12),
  (5 : ZMod 6)), ((2 : ZMod 12), (2 : ZMod 6)), ((2 : ZMod 12), (3 : ZMod 6)), ((2 : ZMod 12),
  (4 : ZMod 6)), ((2 : ZMod 12), (5 : ZMod 6)), ((3 : ZMod 12), (0 : ZMod 6)), ((3 : ZMod 12),
  (3 : ZMod 6)), ((3 : ZMod 12), (4 : ZMod 6)), ((3 : ZMod 12), (5 : ZMod 6)), ((4 : ZMod 12),
  (1 : ZMod 6)), ((4 : ZMod 12), (2 : ZMod 6)), ((4 : ZMod 12), (3 : ZMod 6)), ((4 : ZMod 12),
  (4 : ZMod 6)), ((5 : ZMod 12), (0 : ZMod 6)), ((5 : ZMod 12), (4 : ZMod 6)), ((6 : ZMod 12),
  (1 : ZMod 6)), ((6 : ZMod 12), (5 : ZMod 6)), ((7 : ZMod 12), (3 : ZMod 6)), ((7 : ZMod 12),
  (5 : ZMod 6)), ((8 : ZMod 12), (2 : ZMod 6)), ((8 : ZMod 12), (3 : ZMod 6)), ((8 : ZMod 12),
  (4 : ZMod 6)), ((8 : ZMod 12), (5 : ZMod 6)), ((9 : ZMod 12), (0 : ZMod 6)), ((9 : ZMod 12),
  (3 : ZMod 6)), ((9 : ZMod 12), (4 : ZMod 6)), ((9 : ZMod 12), (5 : ZMod 6)), ((10 : ZMod 12),
  (1 : ZMod 6)), ((10 : ZMod 12), (2 : ZMod 6)), ((10 : ZMod 12), (3 : ZMod 6)), ((10 : ZMod 12),
  (4 : ZMod 6)), ((11 : ZMod 12), (0 : ZMod 6)), ((11 : ZMod 12), (4 : ZMod 6))], [((0 : ZMod 12),
  (4 : ZMod 6)), ((1 : ZMod 12), (3 : ZMod 6)), ((1 : ZMod 12), (5 : ZMod 6)), ((2 : ZMod 12),
  (1 : ZMod 6)), ((2 : ZMod 12), (3 : ZMod 6)), ((3 : ZMod 12), (0 : ZMod 6)), ((3 : ZMod 12),
  (1 : ZMod 6)), ((3 : ZMod 12), (2 : ZMod 6)), ((3 : ZMod 12), (3 : ZMod 6)), ((4 : ZMod 12),
  (1 : ZMod 6)), ((4 : ZMod 12), (2 : ZMod 6)), ((4 : ZMod 12), (3 : ZMod 6)), ((4 : ZMod 12),
  (4 : ZMod 6)), ((5 : ZMod 12), (0 : ZMod 6)), ((5 : ZMod 12), (1 : ZMod 6)), ((5 : ZMod 12),
  (2 : ZMod 6)), ((5 : ZMod 12), (5 : ZMod 6)), ((6 : ZMod 12), (2 : ZMod 6)), ((6 : ZMod 12),
  (4 : ZMod 6)), ((7 : ZMod 12), (3 : ZMod 6)), ((7 : ZMod 12), (5 : ZMod 6)), ((8 : ZMod 12),
  (1 : ZMod 6)), ((8 : ZMod 12), (3 : ZMod 6)), ((9 : ZMod 12), (0 : ZMod 6)), ((9 : ZMod 12),
  (1 : ZMod 6)), ((9 : ZMod 12), (2 : ZMod 6)), ((9 : ZMod 12), (3 : ZMod 6)), ((10 : ZMod 12),
  (1 : ZMod 6)), ((10 : ZMod 12), (2 : ZMod 6)), ((10 : ZMod 12), (3 : ZMod 6)), ((10 : ZMod 12),
  (4 : ZMod 6)), ((11 : ZMod 12), (0 : ZMod 6)), ((11 : ZMod 12), (1 : ZMod 6)), ((11 : ZMod 12),
  (2 : ZMod 6)), ((11 : ZMod 12), (5 : ZMod 6))], [((0 : ZMod 12), (5 : ZMod 6)), ((1 : ZMod 12),
  (2 : ZMod 6)), ((1 : ZMod 12), (3 : ZMod 6)), ((1 : ZMod 12), (4 : ZMod 6)), ((1 : ZMod 12),
  (5 : ZMod 6)), ((2 : ZMod 12), (0 : ZMod 6)), ((2 : ZMod 12), (3 : ZMod 6)), ((2 : ZMod 12),
  (4 : ZMod 6)), ((2 : ZMod 12), (5 : ZMod 6)), ((3 : ZMod 12), (1 : ZMod 6)), ((3 : ZMod 12),
  (2 : ZMod 6)), ((3 : ZMod 12), (3 : ZMod 6)), ((3 : ZMod 12), (4 : ZMod 6)), ((4 : ZMod 12),
  (0 : ZMod 6)), ((4 : ZMod 12), (4 : ZMod 6)), ((5 : ZMod 12), (1 : ZMod 6)), ((5 : ZMod 12),
  (5 : ZMod 6)), ((6 : ZMod 12), (3 : ZMod 6)), ((6 : ZMod 12), (5 : ZMod 6)), ((7 : ZMod 12),
  (2 : ZMod 6)), ((7 : ZMod 12), (3 : ZMod 6)), ((7 : ZMod 12), (4 : ZMod 6)), ((7 : ZMod 12),
  (5 : ZMod 6)), ((8 : ZMod 12), (0 : ZMod 6)), ((8 : ZMod 12), (3 : ZMod 6)), ((8 : ZMod 12),
  (4 : ZMod 6)), ((8 : ZMod 12), (5 : ZMod 6)), ((9 : ZMod 12), (1 : ZMod 6)), ((9 : ZMod 12),
  (2 : ZMod 6)), ((9 : ZMod 12), (3 : ZMod 6)), ((9 : ZMod 12), (4 : ZMod 6)), ((10 : ZMod 12),
  (0 : ZMod 6)), ((10 : ZMod 12), (4 : ZMod 6)), ((11 : ZMod 12), (1 : ZMod 6)), ((11 : ZMod 12),
  (5 : ZMod 6))], [((1 : ZMod 12), (2 : ZMod 6)), ((1 : ZMod 12), (3 : ZMod 6)), ((1 : ZMod 12),
  (5 : ZMod 6)), ((2 : ZMod 12), (0 : ZMod 6)), ((2 : ZMod 12), (2 : ZMod 6)), ((2 : ZMod 12),
  (3 : ZMod 6)), ((2 : ZMod 12), (5 : ZMod 6)), ((4 : ZMod 12), (0 : ZMod 6)), ((4 : ZMod 12),
  (2 : ZMod 6)), ((4 : ZMod 12), (3 : ZMod 6)), ((4 : ZMod 12), (5 : ZMod 6)), ((5 : ZMod 12),
  (0 : ZMod 6)), ((5 : ZMod 12), (2 : ZMod 6)), ((5 : ZMod 12), (3 : ZMod 6)), ((5 : ZMod 12),
  (5 : ZMod 6)), ((7 : ZMod 12), (0 : ZMod 6)), ((7 : ZMod 12), (2 : ZMod 6)), ((7 : ZMod 12),
  (3 : ZMod 6)), ((7 : ZMod 12), (5 : ZMod 6)), ((8 : ZMod 12), (0 : ZMod 6)), ((8 : ZMod 12),
  (2 : ZMod 6)), ((8 : ZMod 12), (3 : ZMod 6)), ((8 : ZMod 12), (5 : ZMod 6)), ((10 : ZMod 12),
  (0 : ZMod 6)), ((10 : ZMod 12), (2 : ZMod 6)), ((10 : ZMod 12), (3 : ZMod 6)), ((10 : ZMod 12),
  (5 : ZMod 6)), ((11 : ZMod 12), (0 : ZMod 6)), ((11 : ZMod 12), (2 : ZMod 6)), ((11 : ZMod 12),
  (3 : ZMod 6)), ((11 : ZMod 12), (5 : ZMod 6))], [((1 : ZMod 12), (2 : ZMod 6)), ((1 : ZMod 12),
  (4 : ZMod 6)), ((1 : ZMod 12), (5 : ZMod 6)), ((2 : ZMod 12), (1 : ZMod 6)), ((2 : ZMod 12),
  (2 : ZMod 6)), ((2 : ZMod 12), (4 : ZMod 6)), ((2 : ZMod 12), (5 : ZMod 6)), ((4 : ZMod 12),
  (1 : ZMod 6)), ((4 : ZMod 12), (2 : ZMod 6)), ((4 : ZMod 12), (4 : ZMod 6)), ((4 : ZMod 12),
  (5 : ZMod 6)), ((5 : ZMod 12), (1 : ZMod 6)), ((5 : ZMod 12), (2 : ZMod 6)), ((5 : ZMod 12),
  (4 : ZMod 6)), ((5 : ZMod 12), (5 : ZMod 6)), ((7 : ZMod 12), (1 : ZMod 6)), ((7 : ZMod 12),
  (2 : ZMod 6)), ((7 : ZMod 12), (4 : ZMod 6)), ((7 : ZMod 12), (5 : ZMod 6)), ((8 : ZMod 12),
  (1 : ZMod 6)), ((8 : ZMod 12), (2 : ZMod 6)), ((8 : ZMod 12), (4 : ZMod 6)), ((8 : ZMod 12),
  (5 : ZMod 6)), ((10 : ZMod 12), (1 : ZMod 6)), ((10 : ZMod 12), (2 : ZMod 6)), ((10 : ZMod 12),
  (4 : ZMod 6)), ((10 : ZMod 12), (5 : ZMod 6)), ((11 : ZMod 12), (1 : ZMod 6)), ((11 : ZMod 12),
  (2 : ZMod 6)), ((11 : ZMod 12), (4 : ZMod 6)), ((11 : ZMod 12), (5 : ZMod 6))]]

lemma cutMap_singleVtx_apply (v : GrossGroup) (h : GrossGroup) (j : Fin 2) :
    grossComplex.cutMap (grossComplex.singleVtx v) (h, j) = cmTerm v h j := by
  rw [cutMap_apply_eq_sum_cmTerm]
  have hpt : ∀ w : GrossGroup, grossComplex.singleVtx v w = (if w = v then 1 else 0) :=
    fun w => by rw [HomologicalCode.singleVtx]; exact Pi.single_apply v 1 w
  simp [hpt, Finset.sum_ite_eq']

lemma cutMap_listSum_singleVtx_apply (L : List grossComplex.C0) (h : GrossGroup) (j : Fin 2) :
    grossComplex.cutMap ((L.map (fun v => grossComplex.singleVtx v)).sum) (h, j)
      = (L.map (fun v : grossComplex.C0 => cmTerm v h j)).sum := by
  induction L with
  | nil => simp only [List.map_nil, List.sum_nil, map_zero]; rfl
  | cons v L ih =>
    rw [List.map_cons, List.sum_cons, map_add, Pi.add_apply, cutMap_singleVtx_apply, ih,
        List.map_cons, List.sum_cons]

lemma vertexStab_drop_mem_closure {S : Set (NQubitPauliGroupElement grossComplex.numQubits)}
    (dv : GrossGroup) (kp : List grossComplex.C0)
    (hrel : ∀ (h : GrossGroup) (j : Fin 2),
       cmTerm dv h j = (kp.map (fun v : grossComplex.C0 => cmTerm v h j)).sum)
    (hkept : ∀ v ∈ kp, grossComplex.vertexStabOf v ∈ S) :
    grossComplex.vertexStabOf dv ∈ Subgroup.closure S := by
  have hbd : grossComplex.cutMap (grossComplex.singleVtx dv)
      = grossComplex.cutMap ((kp.map (fun v => grossComplex.singleVtx v)).sum) := by
    funext q; obtain ⟨h, j⟩ := q
    rw [cutMap_singleVtx_apply, cutMap_listSum_singleVtx_apply]
    exact hrel h j
  have heq : grossComplex.vertexStabOf dv = (kp.map grossComplex.vertexStabOf).prod := by
    rw [vertexStabOf_listProd, ← HomologicalCode.chainZOperator_cutMap_singleVtx, hbd]
  rw [heq]
  exact Subgroup.list_prod_mem _ (fun g hg => by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hg
    exact Subgroup.subset_closure (hkept v hv))

/-! ## §4c  Trimmed generator lists and closure equality -/

noncomputable def genListX : List (NQubitPauliGroupElement grossComplex.numQubits) :=
  keptCoords.map grossComplex.faceStabOf

noncomputable def genListZ : List (NQubitPauliGroupElement grossComplex.numQubits) :=
  keptCoords.map grossComplex.vertexStabOf

noncomputable def genListPackaged : List (NQubitPauliGroupElement grossComplex.numQubits) :=
  genListZ ++ genListX

set_option maxRecDepth 40000 in
-- kernel decide needs more recursion headroom here.
lemma cover : ∀ f : GrossGroup, f ∈ keptCoords ∨ f ∈ dropSet := by decide

lemma faceStab_kept_mem {f : GrossGroup} (hk : f ∈ keptCoords) :
    grossComplex.faceStabOf f ∈ listToSet genListPackaged :=
  List.mem_append_right _ (List.mem_map.mpr ⟨f, hk, rfl⟩)

lemma vtxStab_kept_mem {v : GrossGroup} (hk : v ∈ keptCoords) :
    grossComplex.vertexStabOf v ∈ listToSet genListPackaged :=
  List.mem_append_left _ (List.mem_map.mpr ⟨v, hk, rfl⟩)

set_option maxRecDepth 40000 in
-- kernel decide needs more recursion headroom on the per-drop column relations.
lemma faceStabOf_mem_closure (f : GrossGroup) :
    grossComplex.faceStabOf f ∈ Subgroup.closure (listToSet genListPackaged) := by
  rcases cover f with hk | hd
  · exact Subgroup.subset_closure (faceStab_kept_mem hk)
  · simp only [dropSet, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    · exact faceStab_drop_mem_closure _ (keptPartX.getD 0 []) (by decide +kernel)
        (fun f' hf' => faceStab_kept_mem
          ((by decide +kernel : ∀ x ∈ keptPartX.getD 0 [], x ∈ keptCoords) f' hf'))
    · exact faceStab_drop_mem_closure _ (keptPartX.getD 1 []) (by decide +kernel)
        (fun f' hf' => faceStab_kept_mem
          ((by decide +kernel : ∀ x ∈ keptPartX.getD 1 [], x ∈ keptCoords) f' hf'))
    · exact faceStab_drop_mem_closure _ (keptPartX.getD 2 []) (by decide +kernel)
        (fun f' hf' => faceStab_kept_mem
          ((by decide +kernel : ∀ x ∈ keptPartX.getD 2 [], x ∈ keptCoords) f' hf'))
    · exact faceStab_drop_mem_closure _ (keptPartX.getD 3 []) (by decide +kernel)
        (fun f' hf' => faceStab_kept_mem
          ((by decide +kernel : ∀ x ∈ keptPartX.getD 3 [], x ∈ keptCoords) f' hf'))
    · exact faceStab_drop_mem_closure _ (keptPartX.getD 4 []) (by decide +kernel)
        (fun f' hf' => faceStab_kept_mem
          ((by decide +kernel : ∀ x ∈ keptPartX.getD 4 [], x ∈ keptCoords) f' hf'))
    · exact faceStab_drop_mem_closure _ (keptPartX.getD 5 []) (by decide +kernel)
        (fun f' hf' => faceStab_kept_mem
          ((by decide +kernel : ∀ x ∈ keptPartX.getD 5 [], x ∈ keptCoords) f' hf'))

set_option maxRecDepth 40000 in
-- kernel decide needs more recursion headroom on the per-drop column relations.
lemma vertexStabOf_mem_closure (v : GrossGroup) :
    grossComplex.vertexStabOf v ∈ Subgroup.closure (listToSet genListPackaged) := by
  rcases cover v with hk | hd
  · exact Subgroup.subset_closure (vtxStab_kept_mem hk)
  · simp only [dropSet, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
    · exact vertexStab_drop_mem_closure _ (keptPartZ.getD 0 []) (by decide +kernel)
        (fun v' hv' => vtxStab_kept_mem
          ((by decide +kernel : ∀ x ∈ keptPartZ.getD 0 [], x ∈ keptCoords) v' hv'))
    · exact vertexStab_drop_mem_closure _ (keptPartZ.getD 1 []) (by decide +kernel)
        (fun v' hv' => vtxStab_kept_mem
          ((by decide +kernel : ∀ x ∈ keptPartZ.getD 1 [], x ∈ keptCoords) v' hv'))
    · exact vertexStab_drop_mem_closure _ (keptPartZ.getD 2 []) (by decide +kernel)
        (fun v' hv' => vtxStab_kept_mem
          ((by decide +kernel : ∀ x ∈ keptPartZ.getD 2 [], x ∈ keptCoords) v' hv'))
    · exact vertexStab_drop_mem_closure _ (keptPartZ.getD 3 []) (by decide +kernel)
        (fun v' hv' => vtxStab_kept_mem
          ((by decide +kernel : ∀ x ∈ keptPartZ.getD 3 [], x ∈ keptCoords) v' hv'))
    · exact vertexStab_drop_mem_closure _ (keptPartZ.getD 4 []) (by decide +kernel)
        (fun v' hv' => vtxStab_kept_mem
          ((by decide +kernel : ∀ x ∈ keptPartZ.getD 4 [], x ∈ keptCoords) v' hv'))
    · exact vertexStab_drop_mem_closure _ (keptPartZ.getD 5 []) (by decide +kernel)
        (fun v' hv' => vtxStab_kept_mem
          ((by decide +kernel : ∀ x ∈ keptPartZ.getD 5 [], x ∈ keptCoords) v' hv'))

/-- **Closure equality**: the trimmed 132-generator list generates exactly the
gross homological stabilizer subgroup. -/
lemma closure_packaged_eq :
    Subgroup.closure (listToSet genListPackaged)
      = grossComplex.homologicalStabilizerGroup.toSubgroup := by
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
    · obtain ⟨v, rfl⟩ := hz; exact vertexStabOf_mem_closure v
    · obtain ⟨f, rfl⟩ := hx; exact faceStabOf_mem_closure f

/-! ## §5a  Symplectic-row bridges (for `rowsLinearIndependent`) -/

private lemma zmod2_dich (a : ZMod 2) : a = 0 ∨ a = 1 := by
  rcases Fin.exists_fin_two.mp ⟨a, rfl⟩ with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- Z-half symplectic entry of a vertex stab = the cutMap chain value at that edge. -/
lemma vertexStabOf_sympl_Z (v : grossComplex.C0) (i : Fin grossComplex.numQubits) :
    NQubitPauliOperator.toSymplectic (grossComplex.vertexStabOf v).operators
        (Fin.natAdd grossComplex.numQubits i)
      = grossComplex.cutMap (grossComplex.singleVtx v) (grossComplex.edgeEquiv.symm i) := by
  rw [NQubitPauliOperator.toSymplectic_Z_part]
  change ((grossComplex.chainZOperator (grossComplex.cutMap (grossComplex.singleVtx v))).operators
    i).toSymplecticSingle.2 = _
  rw [HomologicalCode.chainZOperator_op_at]
  set c := grossComplex.cutMap (grossComplex.singleVtx v) with hc
  by_cases h : ∃ e, grossComplex.edgeEquiv e = i ∧ c e = 1
  · obtain ⟨e, he, hce⟩ := h
    rw [if_pos ⟨e, he, hce⟩]
    have : grossComplex.edgeEquiv.symm i = e := by rw [← he, Equiv.symm_apply_apply]
    rw [this, hce]; rfl
  · rw [if_neg h]
    have hz : c (grossComplex.edgeEquiv.symm i) = 0 := by
      rcases zmod2_dich (c (grossComplex.edgeEquiv.symm i)) with h0 | h1
      · exact h0
      · exact absurd ⟨grossComplex.edgeEquiv.symm i, Equiv.apply_symm_apply _ _, h1⟩ h
    rw [hz]; rfl

/-- X-half symplectic entry of a face stab = the boundary2 chain value at that edge. -/
lemma faceStabOf_sympl_X (f : grossComplex.C2) (i : Fin grossComplex.numQubits) :
    NQubitPauliOperator.toSymplectic (grossComplex.faceStabOf f).operators
        (Fin.castAdd grossComplex.numQubits i)
      = grossComplex.boundary2 (grossComplex.singleFace f) (grossComplex.edgeEquiv.symm i) := by
  rw [NQubitPauliOperator.toSymplectic_X_part]
  change ((grossComplex.chainXOperator
      (grossComplex.boundary2 (grossComplex.singleFace f))).operators i).toSymplecticSingle.1 = _
  rw [HomologicalCode.chainXOperator_op_at]
  set c := grossComplex.boundary2 (grossComplex.singleFace f) with hc
  by_cases h : ∃ e, grossComplex.edgeEquiv e = i ∧ c e = 1
  · obtain ⟨e, he, hce⟩ := h
    rw [if_pos ⟨e, he, hce⟩]
    have : grossComplex.edgeEquiv.symm i = e := by rw [← he, Equiv.symm_apply_apply]
    rw [this, hce]; rfl
  · rw [if_neg h]
    have hz : c (grossComplex.edgeEquiv.symm i) = 0 := by
      rcases zmod2_dich (c (grossComplex.edgeEquiv.symm i)) with h0 | h1
      · exact h0
      · exact absurd ⟨grossComplex.edgeEquiv.symm i, Equiv.apply_symm_apply _ _, h1⟩ h
    rw [hz]; rfl

/-- A vertex stab (Z-type) has zero X-half symplectic entries. -/
lemma vertexStabOf_sympl_X_zero (v : grossComplex.C0) (i : Fin grossComplex.numQubits) :
    NQubitPauliOperator.toSymplectic (grossComplex.vertexStabOf v).operators
        (Fin.castAdd grossComplex.numQubits i) = 0 := by
  rw [NQubitPauliOperator.toSymplectic_X_part]
  rcases (HomologicalCode.vertexStabOf_isZType v).2 i with hI | hZ
  · rw [hI]; rfl
  · rw [hZ]; rfl

/-- A face stab (X-type) has zero Z-half symplectic entries. -/
lemma faceStabOf_sympl_Z_zero (f : grossComplex.C2) (i : Fin grossComplex.numQubits) :
    NQubitPauliOperator.toSymplectic (grossComplex.faceStabOf f).operators
        (Fin.natAdd grossComplex.numQubits i) = 0 := by
  rw [NQubitPauliOperator.toSymplectic_Z_part]
  rcases (HomologicalCode.faceStabOf_isXType f).2 i with hI | hX
  · rw [hI]; rfl
  · rw [hX]; rfl

/-! ## §5b  Coefficient-collapse helpers (consume the kernel-trivial cores) -/

set_option maxRecDepth 40000 in
-- kernel decide needs more recursion headroom here.
lemma keptCoords_nodup : keptCoords.Nodup := by decide

private lemma singleVtx_apply' (a b : GrossGroup) :
    grossComplex.singleVtx a b = if b = a then (1 : ZMod 2) else 0 := by
  rw [HomologicalCode.singleVtx]; exact Pi.single_apply a 1 b

private lemma singleFace_apply' (a b : GrossGroup) :
    grossComplex.singleFace a b = if b = a then (1 : ZMod 2) else 0 := by
  rw [HomologicalCode.singleFace]; exact Pi.single_apply a 1 b

set_option maxRecDepth 40000 in
-- kernel decide needs more recursion headroom here.
private lemma keptCoords_get_not_dropSet (i : Fin keptCoords.length) :
    (keptCoords.get i : GrossGroup) ∉ dropSet := by
  have hmem : (keptCoords.get i) ∈ keptCoords := List.get_mem _ _
  have hsub : ∀ x ∈ keptCoords, x ∉ dropSet := by decide
  exact hsub _ hmem

lemma combo_singleVtx_kernel_zero (c : Fin keptCoords.length → ZMod 2)
    (hker : grossComplex.cutMap
      (∑ i, c i • grossComplex.singleVtx (keptCoords.get i)) = 0) :
    ∀ i, c i = 0 := by
  set s := ∑ i, c i • grossComplex.singleVtx (keptCoords.get i) with hs
  have hd : ∀ d ∈ dropSet, s d = 0 := by
    intro d hdmem
    rw [hs, Finset.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hne : d ≠ keptCoords.get i := fun h => keptCoords_get_not_dropSet i (h ▸ hdmem)
    simp only [Pi.smul_apply, singleVtx_apply', smul_eq_mul, if_neg hne, mul_zero]
  have hs0 : s = 0 := vtx_kernel_trivial hker hd
  intro j
  have hsj := congr_fun hs0 (keptCoords.get j)
  rw [hs, Finset.sum_apply, Finset.sum_eq_single j] at hsj
  · simpa [singleVtx_apply'] using hsj
  · intro i _ hij
    have hne : keptCoords.get j ≠ keptCoords.get i :=
      fun h => hij (List.nodup_iff_injective_get.mp keptCoords_nodup h.symm)
    simp only [Pi.smul_apply, singleVtx_apply', smul_eq_mul, if_neg hne, mul_zero]
  · intro hc; exact absurd (Finset.mem_univ j) hc

lemma combo_singleFace_kernel_zero (c : Fin keptCoords.length → ZMod 2)
    (hker : grossComplex.boundary2
      (∑ i, c i • grossComplex.singleFace (keptCoords.get i)) = 0) :
    ∀ i, c i = 0 := by
  set s := ∑ i, c i • grossComplex.singleFace (keptCoords.get i) with hs
  have hd : ∀ d ∈ dropSet, s d = 0 := by
    intro d hdmem
    rw [hs, Finset.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hne : d ≠ keptCoords.get i := fun h => keptCoords_get_not_dropSet i (h ▸ hdmem)
    simp only [Pi.smul_apply, singleFace_apply', smul_eq_mul, if_neg hne, mul_zero]
  have hs0 : s = 0 := face_kernel_trivial hker hd
  intro j
  have hsj := congr_fun hs0 (keptCoords.get j)
  rw [hs, Finset.sum_apply, Finset.sum_eq_single j] at hsj
  · simpa [singleFace_apply'] using hsj
  · intro i _ hij
    have hne : keptCoords.get j ≠ keptCoords.get i :=
      fun h => hij (List.nodup_iff_injective_get.mp keptCoords_nodup h.symm)
    simp only [Pi.smul_apply, singleFace_apply', smul_eq_mul, if_neg hne, mul_zero]
  · intro hc; exact absurd (Finset.mem_univ j) hc

/-! ## §5c  Packaged-list indexing -/

lemma genListPackaged_length :
    genListPackaged.length = keptCoords.length + keptCoords.length := by
  have h : genListPackaged.length = (keptCoords.map grossComplex.vertexStabOf).length
    + (keptCoords.map grossComplex.faceStabOf).length := rfl
  simpa [List.length_map] using h

lemma get_packaged_Z (i : Fin keptCoords.length)
    (hi : i.val < genListPackaged.length) :
    genListPackaged.get ⟨i.val, hi⟩ = grossComplex.vertexStabOf (keptCoords.get i) := by
  have hlt : i.val < (keptCoords.map grossComplex.vertexStabOf).length := by
    rw [List.length_map]; exact i.isLt
  change (keptCoords.map grossComplex.vertexStabOf
    ++ keptCoords.map grossComplex.faceStabOf).get ⟨i.val, hi⟩ = _
  rw [List.get_eq_getElem, List.getElem_append_left hlt, List.getElem_map]
  rfl

set_option maxRecDepth 4096 in
lemma get_packaged_X (i : Fin keptCoords.length)
    (hi : keptCoords.length + i.val < genListPackaged.length) :
    genListPackaged.get ⟨keptCoords.length + i.val, hi⟩
      = grossComplex.faceStabOf (keptCoords.get i) := by
  have hZlen : (keptCoords.map grossComplex.vertexStabOf).length = keptCoords.length :=
    List.length_map _
  have hge : (keptCoords.map grossComplex.vertexStabOf).length ≤ keptCoords.length + i.val := by
    rw [hZlen]; omega
  have hidx : keptCoords.length + i.val - (keptCoords.map grossComplex.vertexStabOf).length
      = i.val := by rw [hZlen]; omega
  change (keptCoords.map grossComplex.vertexStabOf
    ++ keptCoords.map grossComplex.faceStabOf).get ⟨keptCoords.length + i.val, hi⟩ = _
  rw [List.get_eq_getElem, List.getElem_append_right hge, List.getElem_map]
  simp only [hidx]
  rfl

/-! ## §5d  rowsLinearIndependent (block-split) and generators_independent -/

private lemma zidx_lt (i : Fin keptCoords.length) : i.val < genListPackaged.length := by
  have := genListPackaged_length; have := i.isLt; omega

private lemma xidx_lt (i : Fin keptCoords.length) :
    keptCoords.length + i.val < genListPackaged.length := by
  have := genListPackaged_length; have := i.isLt; omega

set_option maxRecDepth 4096 in
private lemma sum_split_Z {M : Type*} [AddCommMonoid M]
    (F : Fin genListPackaged.length → M)
    (hX : ∀ i : Fin keptCoords.length, F ⟨keptCoords.length + i.val, xidx_lt i⟩ = 0) :
    ∑ k, F k = ∑ i : Fin keptCoords.length, F ⟨i.val, zidx_lt i⟩ := by
  have hlen := genListPackaged_length
  rw [← Equiv.sum_comp (finCongr hlen.symm) F, Fin.sum_univ_add]
  have hXsum : (∑ i : Fin keptCoords.length,
      F (finCongr hlen.symm (Fin.natAdd keptCoords.length i))) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← hX i]; congr 1
  rw [hXsum, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1

set_option maxRecDepth 4096 in
private lemma sum_split_X {M : Type*} [AddCommMonoid M]
    (F : Fin genListPackaged.length → M)
    (hZ : ∀ i : Fin keptCoords.length, F ⟨i.val, zidx_lt i⟩ = 0) :
    ∑ k, F k = ∑ i : Fin keptCoords.length, F ⟨keptCoords.length + i.val, xidx_lt i⟩ := by
  have hlen := genListPackaged_length
  rw [← Equiv.sum_comp (finCongr hlen.symm) F, Fin.sum_univ_add]
  have hZsum : (∑ i : Fin keptCoords.length,
      F (finCongr hlen.symm (Fin.castAdd keptCoords.length i))) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← hZ i]; congr 1
  rw [hZsum, zero_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
-- the block-split reduction unifies 132 check-matrix rows against the chain maps,
-- which exceeds the default heartbeat budget.
/-- The trimmed 132-generator list has linearly independent check-matrix rows. -/
theorem rowsLinearIndependent_packaged :
    NQubitPauliGroupElement.rowsLinearIndependent genListPackaged := by
  rw [NQubitPauliGroupElement.rowsLinearIndependent, Fintype.linearIndependent_iff]
  intro g hsum
  set n := grossComplex.numQubits with hn
  have hZchain : grossComplex.cutMap (∑ i : Fin keptCoords.length,
      g ⟨i.val, zidx_lt i⟩ • grossComplex.singleVtx (keptCoords.get i)) = 0 := by
    funext e
    rw [map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have hcol := congr_fun hsum (Fin.natAdd n (grossComplex.edgeEquiv e))
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcol
    rw [← hcol, sum_split_Z (fun k => g k *
      NQubitPauliGroupElement.checkMatrix genListPackaged k
        (Fin.natAdd n (grossComplex.edgeEquiv e)))]
    · refine Finset.sum_congr rfl fun i _ => ?_
      have hterm : NQubitPauliGroupElement.checkMatrix genListPackaged ⟨i.val, zidx_lt i⟩
          (Fin.natAdd n (grossComplex.edgeEquiv e))
          = grossComplex.cutMap (grossComplex.singleVtx (keptCoords.get i)) e := by
        unfold NQubitPauliGroupElement.checkMatrix
        rw [get_packaged_Z i, vertexStabOf_sympl_Z, Equiv.symm_apply_apply]
      rw [hterm]
    · intro i
      have hterm : NQubitPauliGroupElement.checkMatrix genListPackaged
          ⟨keptCoords.length + i.val, xidx_lt i⟩ (Fin.natAdd n (grossComplex.edgeEquiv e)) = 0 := by
        unfold NQubitPauliGroupElement.checkMatrix
        rw [get_packaged_X i, faceStabOf_sympl_Z_zero]
      rw [hterm, mul_zero]
  have hZ0 := combo_singleVtx_kernel_zero _ hZchain
  have hXchain : grossComplex.boundary2 (∑ i : Fin keptCoords.length,
      g ⟨keptCoords.length + i.val, xidx_lt i⟩ • grossComplex.singleFace (keptCoords.get i))
        = 0 := by
    funext e
    rw [map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have hcol := congr_fun hsum (Fin.castAdd n (grossComplex.edgeEquiv e))
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcol
    rw [← hcol, sum_split_X (fun k => g k *
      NQubitPauliGroupElement.checkMatrix genListPackaged k
        (Fin.castAdd n (grossComplex.edgeEquiv e)))]
    · refine Finset.sum_congr rfl fun i _ => ?_
      have hterm : NQubitPauliGroupElement.checkMatrix genListPackaged
          ⟨keptCoords.length + i.val, xidx_lt i⟩ (Fin.castAdd n (grossComplex.edgeEquiv e))
          = grossComplex.boundary2 (grossComplex.singleFace (keptCoords.get i)) e := by
        unfold NQubitPauliGroupElement.checkMatrix
        rw [get_packaged_X i, faceStabOf_sympl_X, Equiv.symm_apply_apply]
      rw [hterm]
    · intro i
      have hterm : NQubitPauliGroupElement.checkMatrix genListPackaged ⟨i.val, zidx_lt i⟩
          (Fin.castAdd n (grossComplex.edgeEquiv e)) = 0 := by
        unfold NQubitPauliGroupElement.checkMatrix
        rw [get_packaged_Z i, vertexStabOf_sympl_X_zero]
      rw [hterm, mul_zero]
  have hX0 := combo_singleFace_kernel_zero _ hXchain
  intro k
  by_cases hk : k.val < keptCoords.length
  · have hz := hZ0 ⟨k.val, hk⟩
    rwa [Fin.eta] at hz
  · push Not at hk
    have hlen := genListPackaged_length
    have hkl := k.isLt
    have hsub : k.val - keptCoords.length < keptCoords.length := by omega
    have hx := hX0 ⟨k.val - keptCoords.length, hsub⟩
    have hidx : (⟨keptCoords.length + (k.val - keptCoords.length), by omega⟩ :
        Fin genListPackaged.length) = k := by
      apply Fin.ext; change keptCoords.length + (k.val - keptCoords.length) = k.val; omega
    rwa [hidx] at hx

/-- The trimmed generator list is an independent generating set. -/
theorem generators_independent_packaged :
    Quantum.StabilizerGroup.GeneratorsIndependent grossComplex.numQubits genListPackaged :=
  Quantum.StabilizerGroup.GeneratorsIndependent_of_rowsLinearIndependent
    grossComplex.numQubits genListPackaged rowsLinearIndependent_packaged

/-! ## §6  Packaged stabilizer group, logical operators, the `StabilizerCode` + `HasCodeDistance`

The 12 logical-qubit operators are the `grossComplex.chainXOperator`/`chainZOperator`
of the offline-validated symplectic basis `logX`/`logZ` (identity `12×12`
intersection matrix). The performance trap — kernel `whnf` exploding through the
noncomputable `grossComplex` and the 132-element literal generator list when a
`centralizer`-transport `rw` or `commute_or_anticommute` runs against a *concrete*
chain operator — is dodged by proving every centralizer / (anti)commutation fact
in a helper lemma with the **chain held abstract** (a stuck variable that blocks
`chainXOperator c` from reducing and keeps `packagedSG` behind the precompiled
`packagedSG_toSubgroup_eq`). `logicalQubit` then only *applies* those helpers by
substitution, paying the heavy defeq once, generically. -/

open Quantum.StabilizerGroup

/-- The 132 trimmed generators all lie in the full homological generator set. -/
lemma listToSet_packaged_subset_homGens :
    listToSet genListPackaged ⊆ grossComplex.homologicalGenerators := by
  intro g hg
  have hg' : g ∈ genListZ ++ genListX := hg
  rcases List.mem_append.mp hg' with hz | hx
  · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hz
    exact HomologicalCode.ZGenerators_subset_homologicalGenerators ⟨v, rfl⟩
  · obtain ⟨f, _, rfl⟩ := List.mem_map.mp hx
    exact HomologicalCode.XGenerators_subset_homologicalGenerators ⟨f, rfl⟩

/-- The trimmed generators pairwise commute. -/
lemma gens_commute_packaged :
    ∀ g ∈ listToSet genListPackaged, ∀ h ∈ listToSet genListPackaged, g * h = h * g := by
  intro g hg h hh
  exact HomologicalCode.homologicalGenerators_commute g (listToSet_packaged_subset_homGens hg)
    h (listToSet_packaged_subset_homGens hh)

/-- `-I` is not in the closure of the trimmed generators. -/
lemma gens_no_neg_packaged :
    negIdentity grossComplex.numQubits ∉ Subgroup.closure (listToSet genListPackaged) := by
  rw [closure_packaged_eq]
  exact grossComplex.homologicalStabilizerGroup.no_neg_identity

/-- The packaged stabilizer group (closure of the trimmed 132-generator list). -/
noncomputable def packagedSG : StabilizerGroup grossComplex.numQubits :=
  mkStabilizerFromGenerators grossComplex.numQubits genListPackaged
    gens_commute_packaged gens_no_neg_packaged

/-- The packaged stabilizer subgroup equals the gross homological stabilizer
subgroup — the bridge transporting the chain-level distance theorems. -/
lemma packagedSG_toSubgroup_eq :
    packagedSG.toSubgroup = grossComplex.homologicalStabilizerGroup.toSubgroup := by
  change Subgroup.closure (listToSet genListPackaged) = _
  exact closure_packaged_eq

/-- Centralizer membership for an X-chain operator, **chain abstract**: the stuck
`c` blocks `grossComplex.chainXOperator` from reducing and `packagedSG` stays behind
`packagedSG_toSubgroup_eq`, so the `centralizer`-transport defeq is paid once here. -/
lemma chainXOperator_mem_centralizer_packagedSG (c : grossComplex.C1 → ZMod 2)
    (hc : grossComplex.boundary1 c = 0) :
    grossComplex.chainXOperator c ∈ centralizer packagedSG := by
  rw [centralizer_eq_of_toSubgroup_eq packagedSG grossComplex.homologicalStabilizerGroup
    packagedSG_toSubgroup_eq]
  exact (HomologicalCode.chainXOperator_mem_centralizer_iff_mem_cycles c).mpr
    ((grossComplex.mem_cycles_iff c).mpr hc)

/-- Centralizer membership for a Z-chain operator (chain abstract; mirror of the X case). -/
lemma chainZOperator_mem_centralizer_packagedSG (c : grossComplex.C1 → ZMod 2)
    (hc : grossComplex.dualBoundary c = 0) :
    grossComplex.chainZOperator c ∈ centralizer packagedSG := by
  rw [centralizer_eq_of_toSubgroup_eq packagedSG grossComplex.homologicalStabilizerGroup
    packagedSG_toSubgroup_eq]
  refine (HomologicalCode.chainZOperator_mem_centralizer_iff_mem_dualCycles c).mpr ?_
  change c ∈ LinearMap.ker grossComplex.dualBoundary
  rw [LinearMap.mem_ker]
  exact hc

/-- An X-chain and a Z-chain operator anticommute when their inner product is `1`
(chains abstract — `commute_or_anticommute` never reduces the concrete operators). -/
lemma chainXOperator_anticommute_chainZOperator (c c' : grossComplex.C1 → ZMod 2)
    (h : grossComplex.chainInnerProduct c c' = 1) :
    NQubitPauliGroupElement.Anticommute
      (grossComplex.chainXOperator c) (grossComplex.chainZOperator c') := by
  rcases NQubitPauliGroupElement.commute_or_anticommute
    (grossComplex.chainXOperator c) (grossComplex.chainZOperator c') with hcomm | ha
  · exfalso
    have hzero := (HomologicalCode.chainXOperator_commutes_chainZOperator_iff c c').mp hcomm
    rw [h] at hzero
    exact one_ne_zero hzero
  · exact ha

/-- An X-chain and a Z-chain operator commute when their inner product is `0`
(chains abstract). -/
lemma chainXOperator_commute_chainZOperator (c c' : grossComplex.C1 → ZMod 2)
    (h : grossComplex.chainInnerProduct c c' = 0) :
    grossComplex.chainXOperator c * grossComplex.chainZOperator c'
      = grossComplex.chainZOperator c' * grossComplex.chainXOperator c :=
  (HomologicalCode.chainXOperator_commutes_chainZOperator_iff c c').mpr h

/-- Indicator chain of the `i`-th X-logical support. -/
def logXchain (i : Fin 12) : GrossGroup × Fin 2 → ZMod 2 :=
  fun e => if e ∈ logX.getD i.val [] then 1 else 0

/-- Indicator chain of the `i`-th Z-logical support. -/
def logZchain (i : Fin 12) : GrossGroup × Fin 2 → ZMod 2 :=
  fun e => if e ∈ logZ.getD i.val [] then 1 else 0

/-- Computable form of `dualBoundary` on a 1-chain: the transpose of `∂₂`. -/
def dualBfn (c : GrossGroup × Fin 2 → ZMod 2) (f : GrossGroup) : ZMod 2 :=
  ∑ h : GrossGroup, (c (h, 0) * d2term f h 0 + c (h, 1) * d2term f h 1)

lemma dualBoundary_eq_dualBfn (c : GrossGroup × Fin 2 → ZMod 2) (f : GrossGroup) :
    grossComplex.dualBoundary c f = dualBfn c f := by
  rw [HomologicalCode.dualBoundary_apply]
  change (∑ e : GrossGroup × Fin 2,
    c e * grossComplex.boundary2 (grossComplex.singleFace f) e) = dualBfn c f
  unfold dualBfn
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Fin.sum_univ_two, boundary2_singleFace_apply, boundary2_singleFace_apply]

/-! ### §6a  Kernel-decide infrastructure for the logical-basis sweeps

`grossA`/`grossB` have three monomials each, so `∂₁`, the dual boundary, and
the chain inner product all collapse to six-term membership sums; the 12- and
144-case sweeps below are then cheap kernel `decide`s over `grossEnum`. -/

/-- `A = x³ + y + y²` as a sum of point masses. -/
private lemma grossA_eq_singles :
    grossA = Pi.single ((3 : ZMod 12), (0 : ZMod 6)) 1
      + Pi.single ((0 : ZMod 12), (1 : ZMod 6)) 1
      + Pi.single ((0 : ZMod 12), (2 : ZMod 6)) 1 := by decide

/-- `B = y³ + x + x²` as a sum of point masses. -/
private lemma grossB_eq_singles :
    grossB = Pi.single ((0 : ZMod 12), (3 : ZMod 6)) 1
      + Pi.single ((1 : ZMod 12), (0 : ZMod 6)) 1
      + Pi.single ((2 : ZMod 12), (0 : ZMod 6)) 1 := by decide

private lemma conv_grossB_apply (w : GrossGroup → ZMod 2) (g : GrossGroup) :
    (grossB ⋆ w) g
      = w (g - ((0 : ZMod 12), (3 : ZMod 6))) + w (g - ((1 : ZMod 12), (0 : ZMod 6)))
        + w (g - ((2 : ZMod 12), (0 : ZMod 6))) := by
  rw [grossB_eq_singles, conv_add_left, conv_add_left]
  simp only [Pi.add_apply, conv_single_left_apply]

private lemma conv_grossA_apply (w : GrossGroup → ZMod 2) (g : GrossGroup) :
    (grossA ⋆ w) g
      = w (g - ((3 : ZMod 12), (0 : ZMod 6))) + w (g - ((0 : ZMod 12), (1 : ZMod 6)))
        + w (g - ((0 : ZMod 12), (2 : ZMod 6))) := by
  rw [grossA_eq_singles, conv_add_left, conv_add_left]
  simp only [Pi.add_apply, conv_single_left_apply]

/-- Sparse 6-term form of `∂₁` (both convolutions are 3-monomial). -/
private lemma bbB1_sparse (c : GrossGroup × Fin 2 → ZMod 2) (g : GrossGroup) :
    bbBoundary1Fn grossA grossB c g
      = c (g - ((0 : ZMod 12), (3 : ZMod 6)), 0) + c (g - ((1 : ZMod 12), (0 : ZMod 6)), 0)
        + c (g - ((2 : ZMod 12), (0 : ZMod 6)), 0)
        + (c (g - ((3 : ZMod 12), (0 : ZMod 6)), 1) + c (g - ((0 : ZMod 12), (1 : ZMod 6)), 1)
          + c (g - ((0 : ZMod 12), (2 : ZMod 6)), 1)) := by
  simp only [bbBoundary1Fn]
  rw [conv_grossB_apply, conv_grossA_apply]
  rfl

/-- Point-mass-shift collapse: `∑ h, w h · δ_a (h − f) = w (f + a)`. -/
private lemma sum_mul_single_shift (w : GrossGroup → ZMod 2) (f a : GrossGroup) :
    (∑ h : GrossGroup, w h * (Pi.single a (1 : ZMod 2) : GrossGroup → ZMod 2) (h - f))
      = w (f + a) := by
  rw [Finset.sum_eq_single (f + a)]
  · rw [add_sub_cancel_left, Pi.single_eq_same, _root_.mul_one]
  · intro h _ hne
    have hna : h - f ≠ a := fun hh => hne ((sub_eq_iff_eq_add.mp hh).trans (add_comm a f))
    rw [Pi.single_eq_of_ne hna, mul_zero]
  · intro habs; exact absurd (Finset.mem_univ _) habs

/-- Sparse 6-term form of the dual boundary (transpose of `∂₂`). -/
private lemma dualBfn_sparse (c : GrossGroup × Fin 2 → ZMod 2) (f : GrossGroup) :
    dualBfn c f
      = c (f + ((3 : ZMod 12), (0 : ZMod 6)), 0) + c (f + ((0 : ZMod 12), (1 : ZMod 6)), 0)
        + c (f + ((0 : ZMod 12), (2 : ZMod 6)), 0)
        + (c (f + ((0 : ZMod 12), (3 : ZMod 6)), 1) + c (f + ((1 : ZMod 12), (0 : ZMod 6)), 1)
          + c (f + ((2 : ZMod 12), (0 : ZMod 6)), 1)) := by
  have hA : ∀ h : GrossGroup, d2term f h 0 = grossA (h - f) := fun _ => rfl
  have hB : ∀ h : GrossGroup, d2term f h 1 = grossB (h - f) := fun _ => rfl
  unfold dualBfn
  rw [Finset.sum_add_distrib]
  simp_rw [hA, hB, grossA_eq_singles, grossB_eq_singles, Pi.add_apply, mul_add,
    Finset.sum_add_distrib, sum_mul_single_shift]

set_option maxRecDepth 40000 in
-- kernel decide needs more recursion headroom on the 12×72 sweep.
private lemma logX_cycle_check : ∀ k : Fin 12, ∀ g ∈ grossEnum,
    logXchain k (g - ((0 : ZMod 12), (3 : ZMod 6)), 0)
      + logXchain k (g - ((1 : ZMod 12), (0 : ZMod 6)), 0)
      + logXchain k (g - ((2 : ZMod 12), (0 : ZMod 6)), 0)
      + (logXchain k (g - ((3 : ZMod 12), (0 : ZMod 6)), 1)
        + logXchain k (g - ((0 : ZMod 12), (1 : ZMod 6)), 1)
        + logXchain k (g - ((0 : ZMod 12), (2 : ZMod 6)), 1)) = 0 := by
  decide +kernel

set_option maxRecDepth 40000 in
-- kernel decide needs more recursion headroom on the 12×72 sweep.
private lemma logZ_dual_check : ∀ k : Fin 12, ∀ f ∈ grossEnum,
    logZchain k (f + ((3 : ZMod 12), (0 : ZMod 6)), 0)
      + logZchain k (f + ((0 : ZMod 12), (1 : ZMod 6)), 0)
      + logZchain k (f + ((0 : ZMod 12), (2 : ZMod 6)), 0)
      + (logZchain k (f + ((0 : ZMod 12), (3 : ZMod 6)), 1)
        + logZchain k (f + ((1 : ZMod 12), (0 : ZMod 6)), 1)
        + logZchain k (f + ((2 : ZMod 12), (0 : ZMod 6)), 1)) = 0 := by
  decide +kernel

/-- Indicator-sum collapse specialized to `logXchain` (instance-stable form). -/
private lemma sum_logXchain_mul (a : Fin 12) (w : GrossGroup × Fin 2 → ZMod 2)
    (hn : (logX.getD a.val []).Nodup) :
    (∑ e : GrossGroup × Fin 2, logXchain a e * w e) = ((logX.getD a.val []).map w).sum := by
  have h1 : ∀ e : GrossGroup × Fin 2, logXchain a e * w e
      = (if e ∈ (logX.getD a.val []).toFinset then w e else 0) := fun e => by
    simp [logXchain]
  simp_rw [h1]
  rw [Finset.sum_ite_mem, Finset.univ_inter, List.sum_toFinset w hn]

set_option maxRecDepth 40000 in
-- kernel decide needs more recursion headroom here.
private lemma logX_getD_nodup : ∀ a : Fin 12, (logX.getD a.val []).Nodup := by decide

set_option maxRecDepth 40000 in
-- kernel decide needs more recursion headroom on the 144-pair sweep.
private lemma inner_check : ∀ a b : Fin 12,
    ((logX.getD a.val []).map (logZchain b)).sum = (if a = b then 1 else 0) := by
  decide +kernel

/-- All 12 X-logicals are cycles (`∂₁ = 0`). -/
lemma logXchain_cycle (i : Fin 12) : grossComplex.boundary1 (logXchain i) = 0 := by
  have h : ∀ k : Fin 12, bbBoundary1Fn grossA grossB (logXchain k) = 0 := by
    intro k
    funext g
    show bbBoundary1Fn grossA grossB (logXchain k) g = 0
    rw [bbB1_sparse]
    exact logX_cycle_check k g (grossEnum_complete g)
  exact h i

/-- All 12 Z-logicals are dual cycles (`dualBoundary = 0`). -/
lemma logZchain_dualCycle (i : Fin 12) : grossComplex.dualBoundary (logZchain i) = 0 := by
  have h : ∀ k : Fin 12, ∀ f : GrossGroup, dualBfn (logZchain k) f = 0 := by
    intro k f
    rw [dualBfn_sparse]
    exact logZ_dual_check k f (grossEnum_complete f)
  funext f
  rw [dualBoundary_eq_dualBfn]
  exact h i f

/-- The `12×12` intersection matrix is the identity. -/
lemma logChain_inner (i j : Fin 12) :
    grossComplex.chainInnerProduct (logXchain i) (logZchain j) = (if i = j then 1 else 0) := by
  have h : ∀ a b : Fin 12,
      (∑ e : GrossGroup × Fin 2, logXchain a e * logZchain b e) = (if a = b then 1 else 0) := by
    intro a b
    rw [sum_logXchain_mul a (logZchain b) (logX_getD_nodup a)]
    exact inner_check a b
  exact h i j

set_option maxRecDepth 4096 in
/-- The `i`-th logical qubit operator pair: the abstract helpers above are simply
*applied* to the concrete chains, so no heavy defeq is re-run here. -/
noncomputable def logicalQubit (i : Fin 12) :
    LogicalQubitOps grossComplex.numQubits packagedSG where
  xOp := grossComplex.chainXOperator (logXchain i)
  zOp := grossComplex.chainZOperator (logZchain i)
  x_mem_centralizer := chainXOperator_mem_centralizer_packagedSG (logXchain i) (logXchain_cycle i)
  z_mem_centralizer :=
    chainZOperator_mem_centralizer_packagedSG (logZchain i) (logZchain_dualCycle i)
  anticommute := chainXOperator_anticommute_chainZOperator (logXchain i) (logZchain i)
    (by rw [logChain_inner i i, if_pos rfl])

set_option maxRecDepth 4096 in
/-- Logical operators for different logical qubits commute (the `12×12` matrix is
diagonal off the diagonal). -/
theorem logical_commute_cross : ∀ ℓ ℓ' : Fin 12, ℓ ≠ ℓ' →
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
/-- The gross `[[144, 12, 12]]` bivariate-bicycle code as a `StabilizerCode`. -/
noncomputable def grossStabilizerCode : StabilizerCode grossComplex.numQubits 12 where
  hk := by rw [grossComplex_numQubits]; omega
  generatorsList := genListPackaged
  generators_length := by
    have h66 : keptCoords.length = 66 := by decide
    have hn := grossComplex_numQubits
    rw [genListPackaged_length]; omega
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

/-- The packaged code's stabilizer subgroup is the gross homological stabilizer
subgroup — the bridge that transports the chain-level distance theorems. -/
theorem grossStabilizerCode_toSubgroup_eq :
    grossStabilizerCode.toStabilizerGroup.toSubgroup
      = grossComplex.homologicalStabilizerGroup.toSubgroup := by
  change Subgroup.closure (listToSet genListPackaged) = _
  exact closure_packaged_eq

/-- **Unconditional lower bound**: every nontrivial logical operator of the
packaged gross code has weight ≥ 6 (triple the Lin–Pryadko floor). -/
theorem grossStabilizerCode_logical_weight_ge_6
    (g : NQubitPauliGroupElement grossComplex.numQubits)
    (hg : IsNontrivialLogicalOperator g grossStabilizerCode.toStabilizerGroup) :
    6 ≤ NQubitPauliGroupElement.weight g :=
  gross_logical_weight_ge_6 g
    ((IsNontrivialLogicalOperator_of_toSubgroup_eq g grossStabilizerCode_toSubgroup_eq).mp hg)

/-- **`HasCodeDistance grossStabilizerCode 12`**, conditional only on `MImBound`.
The `LightStabilizerClassification` input (`hC`) is discharged by
`LightStab.lightStabilizerClassification_holds`; everything else — the packaging and
the chain-level distance — is unconditional.  `MImBound` itself is discharged in
`MImAssembly` (`LightStab.mimBound_holds`); for the fully unconditional statement see
`grossStabilizerCode_hasCodeDistance_12_uncond` there. -/
theorem grossStabilizerCode_hasCodeDistance_12 (hMim : MImBound) :
    HasCodeDistance grossStabilizerCode 12 := by
  have hleast := gross_pauli_distance_eq_12_of_engine
    LightStab.lightStabilizerClassification_holds hMim
  refine ⟨by norm_num, ?_, ?_⟩
  · intro g hg _
    exact hleast.2 ⟨g, (IsNontrivialLogicalOperator_of_toSubgroup_eq g
      grossStabilizerCode_toSubgroup_eq).mp hg, rfl⟩
  · obtain ⟨g, hg, hw⟩ := hleast.1
    exact ⟨g, (IsNontrivialLogicalOperator_of_toSubgroup_eq g
      grossStabilizerCode_toSubgroup_eq).mpr hg, hw⟩


-- TEMP AXIOM AUDIT (removed after check)
#print axioms decoder_identity_X
#print axioms decoder_identity_Z
#print axioms cover
#print axioms faceStabOf_mem_closure
#print axioms vertexStabOf_mem_closure
#print axioms keptCoords_nodup
#print axioms keptCoords_get_not_dropSet
#print axioms logXchain_cycle
#print axioms logZchain_dualCycle
#print axioms logChain_inner
#print axioms closure_packaged_eq
#print axioms rowsLinearIndependent_packaged
#print axioms grossStabilizerCode
#print axioms grossStabilizerCode_logical_weight_ge_6
#print axioms grossStabilizerCode_hasCodeDistance_12

end Quantum.Stabilizer.Homological.BB
