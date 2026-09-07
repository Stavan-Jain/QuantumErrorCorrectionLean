/-
# Phase 6: reducing `MImBound` to the confined-frame floor (§§0–7)

`MImBound` (`SafeSector.lean`, A4 Part II / Theorem D) was the last assumed `Prop` for an
unconditional `d(gross) = 12`: every base 1-cycle in a nonzero Smith class `[seamC ζ]`
(`ζ ∈ ker ∂₂`) has weight ≥ 12, even though the base `[[72,12,6]]` code has distance only 6.

This module performs the **algebraic reduction**: it rewrites the coset weight
`chainWeight (seamC ζ + ∂₂ f)` into the closed `costFromComps` form that the native-decidable
floor engine consumes.  The discharge is then completed downstream — `MImClassify` (reduction)
→ `MImFloorData` / `MImFloor` (engine + soundness) → `MImMembership` (Γ-membership + the
general per-orbit floor) → `MImTransport` (the y-translation symmetry) → `MImFloorY0..Y12`
(the 13 y-orbit-rep floors) → `MImAssembly` (`mimBound_holds`, and the unconditional distance
theorem).  Reuses the CRT frame (`CRTFrame.lean`) and the layer/Fourier machinery built for
the dangerous sector (`LightStab.lean`).

## Structure (the section numbers track A4 §§9–13)

* **§0 weight join** — `chainWeight w = bwt (leftHalf w) + bwt (rightHalf w)` and its layer-sum
  corollary, bridging the noncomputable `bb72Complex.chainWeight` to the per-block, per-`Z₂²`-
  layer `weight3 (slice …)` decomposition.  (The "join" the route hinges on; structural, since
  `seamC ζ + ∂₂ f` is a base 1-chain and `weight_bridge` already decomposes a block.)
* **§2 `ker ∂₂` basis, spanning, M-VANISH** — the systematic basis `kb0..kb5`, `kerBasis_spans`
  (every `ζ ∈ ker ∂₂` is reconstructed from its six free-cell coordinates via `recon`/`kcombo`),
  and A4 §9.4 Sharpening 1, `off_vanish` (CRT components 0 and 2 of `seamC ζ` vanish).
* **§2b coset block decomposition** — `leftHalf_coset`/`rightHalf_coset`: the coset splits as
  the seam profile plus `A⋆f` / `B⋆f`.
* **§3 coset CRT profile** — `Vcoset_L0..R4`: `Vⱼ(coset) = offⱼ(ζ) ⊕ P̂ⱼ · Vⱼ f` (the
  `f`-dependence, via `V_add` and the engine multipliers `Ahat1`/`Ahat4`/`Bhat2`/`unitHat`).
* **§5 exact per-slot weight** — `weight3_eq_wt5` (the Fourier bijection on `Z₃²`): `weight3`
  is an EXACT function of the five CRT components (`WT5_TABLE`, `native_decide`).
* **§6 closed weight form** — `chainWeight_eq_costFromComps`: `chainWeight` as the `Z₂²`-slot
  sum of the ten CRT components' `wt5OfComps`.
* **§7 coset weight in component form** — `chainWeight_coset_eq`: composes §6 with §3 to write
  the coset weight as `costFromComps` of `shifted (seam offset) multiplier (Vⱼ f)` — the exact
  input the floor engine ranges over.

## Convention bridge (lab notes → repo)

Repo `∂₂ f = (A⋆f | B⋆f)`: A-block at `j = 0`, B-block at `j = 1`.
**Repo-left = lab-right** (every "lighter block" reference in A4 §§9–14 flips).
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Gross.SafeSector
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.LightStab
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.LightStabClassify

open Quantum.Stabilizer.Homological.BB
open Quantum.Stabilizer.Homological.BB.CRTFrame
open Quantum.Stabilizer.Homological.BB.LightStab

namespace Quantum.Stabilizer.Homological.BB.LightStab

open scoped BigOperators

-- The seam/lift defeq chains unfold deep `Prod`/`ZMod` instance towers.
set_option maxRecDepth 4096

/-! ## §0 The weight join: `chainWeight` as a sum of per-block layer weights -/

/-- **Block split of the chain weight.**  A base 1-chain's weight is the sum of its
two blocks' weights (the `h ↦ (h,0)` / `h ↦ (h,1)` images partition the support). -/
theorem chainWeight_eq_bwt_blocks (w : BaseGroup × Fin 2 → ZMod 2) :
    bb72Complex.chainWeight w = bwt (leftHalf w) + bwt (rightHalf w) := by
  rw [bb72Complex_chainWeight_eq]
  unfold bwt
  have hz : ∀ a : ZMod 2, (a ≠ 0) ↔ (a = 1) := by decide
  have injA : Function.Injective (fun h : BaseGroup => (h, (0 : Fin 2))) :=
    fun a b h => (Prod.mk.injEq ..).mp h |>.1
  have injB : Function.Injective (fun h : BaseGroup => (h, (1 : Fin 2))) :=
    fun a b h => (Prod.mk.injEq ..).mp h |>.1
  rw [← Finset.card_image_of_injective _ injA, ← Finset.card_image_of_injective _ injB,
    ← Finset.card_union_of_disjoint ?_]
  · congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_image]
    constructor
    · intro hp
      rcases p with ⟨h, j⟩
      fin_cases j
      · exact Or.inl ⟨h, (hz _).mp hp, rfl⟩
      · exact Or.inr ⟨h, (hz _).mp hp, rfl⟩
    · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
      · exact (hz _).mpr ha
      · exact (hz _).mpr ha
  · rw [Finset.disjoint_left]
    intro p hpa hpb
    simp only [Finset.mem_image, Finset.mem_filter] at hpa hpb
    obtain ⟨a, _, rfl⟩ := hpa
    obtain ⟨b, _, hb⟩ := hpb
    exact absurd ((Prod.mk.injEq ..).mp hb).2 (by decide)

/-- **The layer-sum decomposition of the chain weight.**  Composes the block split
with the per-block `Z₂²`-layer decomposition `weight_bridge`.  This is the form the
A4 §10 slot frame bounds: each summand is the weight of a `Z₃²`-torus slice. -/
theorem chainWeight_eq_layer_sum (w : BaseGroup × Fin 2 → ZMod 2) :
    bb72Complex.chainWeight w
      = (∑ s : ZMod 2 × ZMod 2, weight3 (slice (leftHalf w) s))
        + (∑ s : ZMod 2 × ZMod 2, weight3 (slice (rightHalf w) s)) := by
  rw [chainWeight_eq_bwt_blocks, weight_bridge, weight_bridge]

/-! ## §2 The `ker ∂₂` basis, spanning, and M-VANISH (A4 §9.3–§9.4)

`ker ∂₂ = {ζ : conv baseA ζ = 0 ∧ conv baseB ζ = 0}` is 6-dimensional (64 elements,
63 nonzero in 5 translation orbits of weights 16/18/18/24/24 — matching A4 §9.3).  We
pin a systematic basis `kb0..kb5` (with `kbᵢ` supported so that `kbᵢ(freeCellⱼ) = δᵢⱼ`),
prove it spans `ker ∂₂` (every `ζ ∈ ker ∂₂` is reconstructed from its 6 free-cell
coordinates, `kerBasis_spans`), and deduce A4 §9.4 Sharpening 1 — the CRT components 0
and 2 of `seamC ζ` vanish (`off_vanish`) — by a `native_decide` over the 64 combinations. -/

/-- Indicator of a finite support set. -/
def mkZeta (supp : List BaseGroup) : BaseGroup → ZMod 2 := fun h => if h ∈ supp then 1 else 0

def kb0 : BaseGroup → ZMod 2 :=
  mkZeta [(0,0),(0,1),(0,3),(0,4),(1,0),(1,1),(1,3),(1,4),
          (3,0),(3,1),(3,3),(3,4),(4,0),(4,1),(4,3),(4,4)]
def kb1 : BaseGroup → ZMod 2 :=
  mkZeta [(0,0),(0,2),(0,3),(0,5),(1,0),(1,2),(1,3),(1,5),
          (3,0),(3,2),(3,3),(3,5),(4,0),(4,2),(4,3),(4,5)]
def kb2 : BaseGroup → ZMod 2 :=
  mkZeta [(0,0),(0,4),(1,1),(1,5),(2,1),(2,2),(2,3),(2,4),(3,0),
          (3,1),(3,2),(3,5),(4,0),(4,1),(4,2),(4,3),(5,0),(5,2)]
def kb3 : BaseGroup → ZMod 2 :=
  mkZeta [(0,0),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(2,2),
          (2,3),(2,4),(2,5),(3,2),(3,4),(4,0),(4,2),(5,1),(5,3)]
def kb4 : BaseGroup → ZMod 2 :=
  mkZeta [(0,1),(0,5),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),
          (2,5),(3,0),(3,1),(3,2),(3,3),(4,0),(4,2),(5,0),(5,4)]
def kb5 : BaseGroup → ZMod 2 :=
  mkZeta [(0,0),(0,2),(1,2),(1,3),(1,4),(1,5),(2,0),(2,1),(2,2),
          (2,3),(3,1),(3,2),(3,3),(3,4),(4,1),(4,3),(5,1),(5,5)]

/-! ### Packed seam masks (kernel-evaluation layer)

`seamC` and `∂₂` evaluate 72- and 36-term `Finset.sum`s through the bundled cover
tower — opaque to kernel reduction.  Everything the kernel must evaluate is
routed through 72-bit packed masks instead: `chainOfMask` reads a base 1-chain
off a `Nat` bitmask, the six `KBiMASK` literals are the `seamC` images of the
`ker ∂₂` basis (certified below through the sparse form `seamC_eq_sparse`),
and `seamC_kcombo_mask` gives every Smith class's seam profile as one XOR of
mask literals.  All kernel `decide`, no `native_decide`. -/

/-- Flat qubit index: `((a,b), j) ↦ a·6 + b + 36·j`. -/
def qidx (q : BaseGroup × Fin 2) : Nat := q.1.1.val * 6 + q.1.2.val + 36 * q.2.val

/-- The base 1-chain of a packed 72-bit mask. -/
def chainOfMask (m : Nat) : BaseGroup × Fin 2 → ZMod 2 :=
  fun q => if (m >>> qidx q) &&& 1 = 1 then 1 else 0

theorem chainOfMask_zero : chainOfMask 0 = 0 := by
  funext q
  simp [chainOfMask]

/-- Mask XOR is chain addition. -/
theorem chainOfMask_xor (a b : Nat) :
    chainOfMask (a ^^^ b) = chainOfMask a + chainOfMask b := by
  funext q
  have hbit : ∀ n : Nat, (n >>> qidx q) &&& 1 = if n.testBit (qidx q) then 1 else 0 := by
    intro n
    rcases hb : n.testBit (qidx q) with _ | _
    · simpa [Nat.testBit, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow] using hb
    · simpa [Nat.testBit, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow] using hb
  simp only [chainOfMask, Pi.add_apply, hbit, Nat.testBit_xor]
  rcases a.testBit (qidx q) <;> rcases b.testBit (qidx q) <;> decide

/-- `seamC` images of the six `ker ∂₂` basis vectors, as packed masks
(row order `qidx`; computed offline, certified by `seamC_kb0_mask`…). -/
def KB0MASK : Nat := 0x1b0000006db
def KB1MASK : Nat := 0x2d000000b6d
def KB2MASK : Nat := 0x14a0000053e7
def KB3MASK : Nat := 0x28f00000a154
def KB4MASK : Nat := 0x45400001114f
def KB5MASK : Nat := 0x8a800002229e

private theorem seamCSparse_kb0 : ∀ p : BaseGroup, ∀ j : Fin 2,
    seamCSparse kb0 (p, j) = chainOfMask KB0MASK (p, j) := by decide +kernel
private theorem seamCSparse_kb1 : ∀ p : BaseGroup, ∀ j : Fin 2,
    seamCSparse kb1 (p, j) = chainOfMask KB1MASK (p, j) := by decide +kernel
private theorem seamCSparse_kb2 : ∀ p : BaseGroup, ∀ j : Fin 2,
    seamCSparse kb2 (p, j) = chainOfMask KB2MASK (p, j) := by decide +kernel
private theorem seamCSparse_kb3 : ∀ p : BaseGroup, ∀ j : Fin 2,
    seamCSparse kb3 (p, j) = chainOfMask KB3MASK (p, j) := by decide +kernel
private theorem seamCSparse_kb4 : ∀ p : BaseGroup, ∀ j : Fin 2,
    seamCSparse kb4 (p, j) = chainOfMask KB4MASK (p, j) := by decide +kernel
private theorem seamCSparse_kb5 : ∀ p : BaseGroup, ∀ j : Fin 2,
    seamCSparse kb5 (p, j) = chainOfMask KB5MASK (p, j) := by decide +kernel

theorem seamC_kb0_mask : seamC kb0 = chainOfMask KB0MASK := by
  rw [seamC_eq_sparse]; funext q; obtain ⟨p, j⟩ := q; exact seamCSparse_kb0 p j
theorem seamC_kb1_mask : seamC kb1 = chainOfMask KB1MASK := by
  rw [seamC_eq_sparse]; funext q; obtain ⟨p, j⟩ := q; exact seamCSparse_kb1 p j
theorem seamC_kb2_mask : seamC kb2 = chainOfMask KB2MASK := by
  rw [seamC_eq_sparse]; funext q; obtain ⟨p, j⟩ := q; exact seamCSparse_kb2 p j
theorem seamC_kb3_mask : seamC kb3 = chainOfMask KB3MASK := by
  rw [seamC_eq_sparse]; funext q; obtain ⟨p, j⟩ := q; exact seamCSparse_kb3 p j
theorem seamC_kb4_mask : seamC kb4 = chainOfMask KB4MASK := by
  rw [seamC_eq_sparse]; funext q; obtain ⟨p, j⟩ := q; exact seamCSparse_kb4 p j
theorem seamC_kb5_mask : seamC kb5 = chainOfMask KB5MASK := by
  rw [seamC_eq_sparse]; funext q; obtain ⟨p, j⟩ := q; exact seamCSparse_kb5 p j

/-! ### Sparse `∂₂` and the basis kernel facts -/

/-- Sparse pointwise form of the base boundary: three translate terms per block. -/
theorem bb2_sparse (f : BaseGroup → ZMod 2) (p : BaseGroup) (j : Fin 2) :
    bbBoundary2Fn baseA baseB f (p, j)
      = if j = 0 then f (p - (3, 0)) + f (p - (0, 1)) + f (p - (0, 2))
        else f (p - (0, 3)) + f (p - (1, 0)) + f (p - (2, 0)) := by
  change (if j = 0 then (baseA ⋆ f) p else (baseB ⋆ f) p) = _
  have hA : (baseA ⋆ f) p
      = f (p - (3, 0)) + f (p - (0, 1)) + f (p - (0, 2)) :=
    conv_indicator3 ((3, 0) : BaseGroup) (0, 1) (0, 2)
      (by decide) (by decide) (by decide) f p
  have hB : (baseB ⋆ f) p
      = f (p - (0, 3)) + f (p - (1, 0)) + f (p - (2, 0)) :=
    conv_indicator3 ((0, 3) : BaseGroup) (1, 0) (2, 0)
      (by decide) (by decide) (by decide) f p
  by_cases hj : j = 0
  · rw [if_pos hj, if_pos hj, hA]
  · rw [if_neg hj, if_neg hj, hB]

private theorem bb2_kb_zero_aux :
    (∀ p : BaseGroup, ∀ j : Fin 2,
      (if j = 0 then kb0 (p - (3, 0)) + kb0 (p - (0, 1)) + kb0 (p - (0, 2))
       else kb0 (p - (0, 3)) + kb0 (p - (1, 0)) + kb0 (p - (2, 0))) = 0) ∧
    (∀ p : BaseGroup, ∀ j : Fin 2,
      (if j = 0 then kb1 (p - (3, 0)) + kb1 (p - (0, 1)) + kb1 (p - (0, 2))
       else kb1 (p - (0, 3)) + kb1 (p - (1, 0)) + kb1 (p - (2, 0))) = 0) ∧
    (∀ p : BaseGroup, ∀ j : Fin 2,
      (if j = 0 then kb2 (p - (3, 0)) + kb2 (p - (0, 1)) + kb2 (p - (0, 2))
       else kb2 (p - (0, 3)) + kb2 (p - (1, 0)) + kb2 (p - (2, 0))) = 0) ∧
    (∀ p : BaseGroup, ∀ j : Fin 2,
      (if j = 0 then kb3 (p - (3, 0)) + kb3 (p - (0, 1)) + kb3 (p - (0, 2))
       else kb3 (p - (0, 3)) + kb3 (p - (1, 0)) + kb3 (p - (2, 0))) = 0) ∧
    (∀ p : BaseGroup, ∀ j : Fin 2,
      (if j = 0 then kb4 (p - (3, 0)) + kb4 (p - (0, 1)) + kb4 (p - (0, 2))
       else kb4 (p - (0, 3)) + kb4 (p - (1, 0)) + kb4 (p - (2, 0))) = 0) ∧
    (∀ p : BaseGroup, ∀ j : Fin 2,
      (if j = 0 then kb5 (p - (3, 0)) + kb5 (p - (0, 1)) + kb5 (p - (0, 2))
       else kb5 (p - (0, 3)) + kb5 (p - (1, 0)) + kb5 (p - (2, 0))) = 0) := by
  decide +kernel

/-- Each basis vector lies in `ker ∂₂` (function form). -/
theorem bb2_kb0 : bbBoundary2Fn baseA baseB kb0 = 0 := by
  funext q; obtain ⟨p, j⟩ := q; rw [bb2_sparse]; exact bb2_kb_zero_aux.1 p j
theorem bb2_kb1 : bbBoundary2Fn baseA baseB kb1 = 0 := by
  funext q; obtain ⟨p, j⟩ := q; rw [bb2_sparse]; exact bb2_kb_zero_aux.2.1 p j
theorem bb2_kb2 : bbBoundary2Fn baseA baseB kb2 = 0 := by
  funext q; obtain ⟨p, j⟩ := q; rw [bb2_sparse]; exact bb2_kb_zero_aux.2.2.1 p j
theorem bb2_kb3 : bbBoundary2Fn baseA baseB kb3 = 0 := by
  funext q; obtain ⟨p, j⟩ := q; rw [bb2_sparse]; exact bb2_kb_zero_aux.2.2.2.1 p j
theorem bb2_kb4 : bbBoundary2Fn baseA baseB kb4 = 0 := by
  funext q; obtain ⟨p, j⟩ := q; rw [bb2_sparse]; exact bb2_kb_zero_aux.2.2.2.2.1 p j
theorem bb2_kb5 : bbBoundary2Fn baseA baseB kb5 = 0 := by
  funext q; obtain ⟨p, j⟩ := q; rw [bb2_sparse]; exact bb2_kb_zero_aux.2.2.2.2.2 p j

/-- The `ker ∂₂` basis as a list (for the membership check). -/
def kerBasis : List (BaseGroup → ZMod 2) := [kb0, kb1, kb2, kb3, kb4, kb5]

/-- Each basis vector lies in `ker ∂₂`. -/
theorem kerBasis_mem :
    kerBasis.all (fun v => decide (bbBoundary2Fn baseA baseB v = 0)) = true := by
  simp [kerBasis, bb2_kb0, bb2_kb1, bb2_kb2, bb2_kb3, bb2_kb4, bb2_kb5]

/-- `recon ζ = Σᵢ ζ(freeCellᵢ) • kbᵢ` (systematic basis: `kbᵢ(freeCellⱼ) = δᵢⱼ`). -/
def recon (z : BaseGroup → ZMod 2) : BaseGroup → ZMod 2 := fun h =>
  z (4,4) * kb0 h + z (4,5) * kb1 h + z (5,2) * kb2 h +
  z (5,3) * kb3 h + z (5,4) * kb4 h + z (5,5) * kb5 h

theorem recon_add (a b : BaseGroup → ZMod 2) : recon (a + b) = recon a + recon b := by
  funext h; simp only [recon, Pi.add_apply]; ring

theorem recon_zero : recon 0 = 0 := by funext h; simp [recon]

theorem bb2_zero_chain : bbBoundary2Fn baseA baseB (0 : BaseGroup → ZMod 2) = 0 := by
  funext p; obtain ⟨g, j⟩ := p
  simp only [bbBoundary2Fn, conv_apply, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  split <;> rfl

/-- The 6-parameter combination of basis vectors (the systematic form of `recon`). -/
def kcombo (c0 c1 c2 c3 c4 c5 : ZMod 2) : BaseGroup → ZMod 2 := fun h =>
  c0 * kb0 h + c1 * kb1 h + c2 * kb2 h + c3 * kb3 h + c4 * kb4 h + c5 * kb5 h

theorem recon_eq_kcombo (z : BaseGroup → ZMod 2) :
    recon z = kcombo (z (4,4)) (z (4,5)) (z (5,2)) (z (5,3)) (z (5,4)) (z (5,5)) := rfl

/-- ZMod-2 scalar action as an `if` (for the systematic-combination decomposition). -/
private theorem zmod2_mul_eq_ite (c x : ZMod 2) : c * x = if c = 1 then x else 0 := by
  revert c x; decide

/-- `kcombo` as a sum of gated basis vectors. -/
theorem kcombo_eq_sum (c0 c1 c2 c3 c4 c5 : ZMod 2) :
    kcombo c0 c1 c2 c3 c4 c5
      = (if c0 = 1 then kb0 else 0) + (if c1 = 1 then kb1 else 0)
        + (if c2 = 1 then kb2 else 0) + (if c3 = 1 then kb3 else 0)
        + (if c4 = 1 then kb4 else 0) + (if c5 = 1 then kb5 else 0) := by
  funext h
  simp only [kcombo, Pi.add_apply, zmod2_mul_eq_ite,
    apply_ite (f := fun v : BaseGroup → ZMod 2 => v h),
    Pi.zero_apply]

private theorem seamC_zero_fn : seamC 0 = 0 := by
  have h := seamC_add 0 0
  rw [add_zero] at h
  funext q
  have hq := congrFun h q
  have : ∀ a : ZMod 2, a = a + a → a = 0 := by decide
  exact this _ (by simpa using hq)

private theorem seamC_gated (c : ZMod 2) (kb : BaseGroup → ZMod 2) (m : Nat)
    (h : seamC kb = chainOfMask m) :
    seamC (if c = 1 then kb else 0) = chainOfMask (if c = 1 then m else 0) := by
  by_cases hc : c = 1
  · rw [if_pos hc, if_pos hc, h]
  · rw [if_neg hc, if_neg hc, seamC_zero_fn, chainOfMask_zero]

/-- The packed seam profile of the Smith class `kcombo c₀…c₅`. -/
def comboMask (c0 c1 c2 c3 c4 c5 : ZMod 2) : Nat :=
  (if c0 = 1 then KB0MASK else 0) ^^^ (if c1 = 1 then KB1MASK else 0)
    ^^^ (if c2 = 1 then KB2MASK else 0) ^^^ (if c3 = 1 then KB3MASK else 0)
    ^^^ (if c4 = 1 then KB4MASK else 0) ^^^ (if c5 = 1 then KB5MASK else 0)

/-- **Every Smith class's seam profile is a packed mask**: `seamC (kcombo c⃗) =
chainOfMask (comboMask c⃗)`.  The kernel-evaluation gateway for all seam-offset
read-offs and covariance certificates. -/
theorem seamC_kcombo_mask (c0 c1 c2 c3 c4 c5 : ZMod 2) :
    seamC (kcombo c0 c1 c2 c3 c4 c5) = chainOfMask (comboMask c0 c1 c2 c3 c4 c5) := by
  rw [kcombo_eq_sum, comboMask, seamC_add, seamC_add, seamC_add, seamC_add, seamC_add,
    chainOfMask_xor, chainOfMask_xor, chainOfMask_xor, chainOfMask_xor, chainOfMask_xor,
    seamC_gated c0 kb0 KB0MASK seamC_kb0_mask, seamC_gated c1 kb1 KB1MASK seamC_kb1_mask,
    seamC_gated c2 kb2 KB2MASK seamC_kb2_mask, seamC_gated c3 kb3 KB3MASK seamC_kb3_mask,
    seamC_gated c4 kb4 KB4MASK seamC_kb4_mask, seamC_gated c5 kb5 KB5MASK seamC_kb5_mask]

/-- Every Smith class `kcombo c⃗` lies in `ker ∂₂`. -/
theorem bb2_kcombo (c0 c1 c2 c3 c4 c5 : ZMod 2) :
    bbBoundary2Fn baseA baseB (kcombo c0 c1 c2 c3 c4 c5) = 0 := by
  have gate : ∀ (c : ZMod 2) (kb : BaseGroup → ZMod 2),
      bbBoundary2Fn baseA baseB kb = 0 →
      bbBoundary2Fn baseA baseB (if c = 1 then kb else 0) = 0 := by
    intro c kb h
    by_cases hc : c = 1
    · rwa [if_pos hc]
    · rw [if_neg hc]
      funext q; obtain ⟨p, j⟩ := q
      rw [bb2_sparse]
      simp
  rw [kcombo_eq_sum, bbBoundary2Fn_add, bbBoundary2Fn_add, bbBoundary2Fn_add,
    bbBoundary2Fn_add, bbBoundary2Fn_add,
    gate c0 kb0 bb2_kb0, gate c1 kb1 bb2_kb1, gate c2 kb2 bb2_kb2,
    gate c3 kb3 bb2_kb3, gate c4 kb4 bb2_kb4, gate c5 kb5 bb2_kb5]
  funext q
  simp


/-- **Spanning** (A4 §9.3): every `ker ∂₂` element equals its reconstruction from its
six free-cell coordinates.  Proved by **peeling**: `w := recon ζ + ζ` is again in
`ker ∂₂` and vanishes on the six free cells (the basis is systematic,
`kbᵢ(freeCellⱼ) = δᵢⱼ`), and the `∂₂`-rows then force `w` to vanish cell by cell —
thirty steps, each reading one row whose other two cells are already known zero.
This is Gaussian elimination on the `36`-cell system written out as its elimination
order, so neither a matrix inverse nor an enumeration is needed. -/
theorem kerBasis_spans (z : BaseGroup → ZMod 2)
    (hz : bbBoundary2Fn baseA baseB z = 0) : recon z = z := by
  have hself : ∀ a : ZMod 2, a + a = 0 := by decide
  have hw0 : bbBoundary2Fn baseA baseB (recon z + z) = 0 := by
    rw [bbBoundary2Fn_add, hz, add_zero, recon_eq_kcombo, bb2_kcombo]
  have hw : ∀ (p : BaseGroup) (j : Fin 2),
      (if j = 0 then
          (recon z + z) (p - (3,0)) + (recon z + z) (p - (0,1)) + (recon z + z) (p - (0,2))
        else
          (recon z + z) (p - (0,3)) + (recon z + z) (p - (1,0))
            + (recon z + z) (p - (2,0))) = 0 := by
    intro p j; rw [← bb2_sparse]; exact congrFun hw0 (p, j)
  have f0 : (recon z + z) ((4,4) : BaseGroup) = 0 := by
    show z (4,4) * kb0 ((4,4) : BaseGroup) + z (4,5) * kb1 ((4,4) : BaseGroup)
        + z (5,2) * kb2 ((4,4) : BaseGroup) + z (5,3) * kb3 ((4,4) : BaseGroup)
        + z (5,4) * kb4 ((4,4) : BaseGroup) + z (5,5) * kb5 ((4,4) : BaseGroup)
        + z (4,4) = 0
    rw [show kb0 ((4,4) : BaseGroup) = 1 from by decide,
      show kb1 ((4,4) : BaseGroup) = 0 from by decide,
      show kb2 ((4,4) : BaseGroup) = 0 from by decide,
      show kb3 ((4,4) : BaseGroup) = 0 from by decide,
      show kb4 ((4,4) : BaseGroup) = 0 from by decide,
      show kb5 ((4,4) : BaseGroup) = 0 from by decide]
    simp only [mul_one, mul_zero, add_zero]
    exact hself _
  have f1 : (recon z + z) ((4,5) : BaseGroup) = 0 := by
    show z (4,4) * kb0 ((4,5) : BaseGroup) + z (4,5) * kb1 ((4,5) : BaseGroup)
        + z (5,2) * kb2 ((4,5) : BaseGroup) + z (5,3) * kb3 ((4,5) : BaseGroup)
        + z (5,4) * kb4 ((4,5) : BaseGroup) + z (5,5) * kb5 ((4,5) : BaseGroup)
        + z (4,5) = 0
    rw [show kb0 ((4,5) : BaseGroup) = 0 from by decide,
      show kb1 ((4,5) : BaseGroup) = 1 from by decide,
      show kb2 ((4,5) : BaseGroup) = 0 from by decide,
      show kb3 ((4,5) : BaseGroup) = 0 from by decide,
      show kb4 ((4,5) : BaseGroup) = 0 from by decide,
      show kb5 ((4,5) : BaseGroup) = 0 from by decide]
    simp only [mul_one, mul_zero, add_zero, zero_add]
    exact hself _
  have f2 : (recon z + z) ((5,2) : BaseGroup) = 0 := by
    show z (4,4) * kb0 ((5,2) : BaseGroup) + z (4,5) * kb1 ((5,2) : BaseGroup)
        + z (5,2) * kb2 ((5,2) : BaseGroup) + z (5,3) * kb3 ((5,2) : BaseGroup)
        + z (5,4) * kb4 ((5,2) : BaseGroup) + z (5,5) * kb5 ((5,2) : BaseGroup)
        + z (5,2) = 0
    rw [show kb0 ((5,2) : BaseGroup) = 0 from by decide,
      show kb1 ((5,2) : BaseGroup) = 0 from by decide,
      show kb2 ((5,2) : BaseGroup) = 1 from by decide,
      show kb3 ((5,2) : BaseGroup) = 0 from by decide,
      show kb4 ((5,2) : BaseGroup) = 0 from by decide,
      show kb5 ((5,2) : BaseGroup) = 0 from by decide]
    simp only [mul_one, mul_zero, add_zero, zero_add]
    exact hself _
  have f3 : (recon z + z) ((5,3) : BaseGroup) = 0 := by
    show z (4,4) * kb0 ((5,3) : BaseGroup) + z (4,5) * kb1 ((5,3) : BaseGroup)
        + z (5,2) * kb2 ((5,3) : BaseGroup) + z (5,3) * kb3 ((5,3) : BaseGroup)
        + z (5,4) * kb4 ((5,3) : BaseGroup) + z (5,5) * kb5 ((5,3) : BaseGroup)
        + z (5,3) = 0
    rw [show kb0 ((5,3) : BaseGroup) = 0 from by decide,
      show kb1 ((5,3) : BaseGroup) = 0 from by decide,
      show kb2 ((5,3) : BaseGroup) = 0 from by decide,
      show kb3 ((5,3) : BaseGroup) = 1 from by decide,
      show kb4 ((5,3) : BaseGroup) = 0 from by decide,
      show kb5 ((5,3) : BaseGroup) = 0 from by decide]
    simp only [mul_one, mul_zero, add_zero, zero_add]
    exact hself _
  have f4 : (recon z + z) ((5,4) : BaseGroup) = 0 := by
    show z (4,4) * kb0 ((5,4) : BaseGroup) + z (4,5) * kb1 ((5,4) : BaseGroup)
        + z (5,2) * kb2 ((5,4) : BaseGroup) + z (5,3) * kb3 ((5,4) : BaseGroup)
        + z (5,4) * kb4 ((5,4) : BaseGroup) + z (5,5) * kb5 ((5,4) : BaseGroup)
        + z (5,4) = 0
    rw [show kb0 ((5,4) : BaseGroup) = 0 from by decide,
      show kb1 ((5,4) : BaseGroup) = 0 from by decide,
      show kb2 ((5,4) : BaseGroup) = 0 from by decide,
      show kb3 ((5,4) : BaseGroup) = 0 from by decide,
      show kb4 ((5,4) : BaseGroup) = 1 from by decide,
      show kb5 ((5,4) : BaseGroup) = 0 from by decide]
    simp only [mul_one, mul_zero, add_zero, zero_add]
    exact hself _
  have f5 : (recon z + z) ((5,5) : BaseGroup) = 0 := by
    show z (4,4) * kb0 ((5,5) : BaseGroup) + z (4,5) * kb1 ((5,5) : BaseGroup)
        + z (5,2) * kb2 ((5,5) : BaseGroup) + z (5,3) * kb3 ((5,5) : BaseGroup)
        + z (5,4) * kb4 ((5,5) : BaseGroup) + z (5,5) * kb5 ((5,5) : BaseGroup)
        + z (5,5) = 0
    rw [show kb0 ((5,5) : BaseGroup) = 0 from by decide,
      show kb1 ((5,5) : BaseGroup) = 0 from by decide,
      show kb2 ((5,5) : BaseGroup) = 0 from by decide,
      show kb3 ((5,5) : BaseGroup) = 0 from by decide,
      show kb4 ((5,5) : BaseGroup) = 0 from by decide,
      show kb5 ((5,5) : BaseGroup) = 1 from by decide]
    simp only [mul_one, mul_zero, add_zero, zero_add]
    exact hself _
  have s1 : (recon z + z) ((1,0) : BaseGroup) = 0 := by
    have h : (recon z + z) ((1,0) : BaseGroup) + (recon z + z) ((4,5) : BaseGroup)
        + (recon z + z) ((4,4) : BaseGroup) = 0 := hw (4,0) 0
    rw [f1, f0] at h
    simpa using h
  have s2 : (recon z + z) ((2,0) : BaseGroup) = 0 := by
    have h : (recon z + z) ((2,0) : BaseGroup) + (recon z + z) ((5,5) : BaseGroup)
        + (recon z + z) ((5,4) : BaseGroup) = 0 := hw (5,0) 0
    rw [f5, f4] at h
    simpa using h
  have s3 : (recon z + z) ((2,4) : BaseGroup) = 0 := by
    have h : (recon z + z) ((2,4) : BaseGroup) + (recon z + z) ((5,3) : BaseGroup)
        + (recon z + z) ((5,2) : BaseGroup) = 0 := hw (5,4) 0
    rw [f3, f2] at h
    simpa using h
  have s4 : (recon z + z) ((2,5) : BaseGroup) = 0 := by
    have h : (recon z + z) ((2,5) : BaseGroup) + (recon z + z) ((5,4) : BaseGroup)
        + (recon z + z) ((5,3) : BaseGroup) = 0 := hw (5,5) 0
    rw [f4, f3] at h
    simpa using h
  have s5 : (recon z + z) ((0,1) : BaseGroup) = 0 := by
    have h : (recon z + z) ((0,1) : BaseGroup) + (recon z + z) ((5,4) : BaseGroup)
        + (recon z + z) ((4,4) : BaseGroup) = 0 := hw (0,4) 1
    rw [f4, f0] at h
    simpa using h
  have s6 : (recon z + z) ((0,2) : BaseGroup) = 0 := by
    have h : (recon z + z) ((0,2) : BaseGroup) + (recon z + z) ((5,5) : BaseGroup)
        + (recon z + z) ((4,5) : BaseGroup) = 0 := hw (0,5) 1
    rw [f5, f1] at h
    simpa using h
  have s7 : (recon z + z) ((1,5) : BaseGroup) = 0 := by
    have h : (recon z + z) ((1,5) : BaseGroup) + (recon z + z) ((0,2) : BaseGroup)
        + (recon z + z) ((5,2) : BaseGroup) = 0 := hw (1,2) 1
    rw [s6, f2] at h
    simpa using h
  have s8 : (recon z + z) ((0,3) : BaseGroup) = 0 := by
    have h : (recon z + z) ((1,0) : BaseGroup) + (recon z + z) ((0,3) : BaseGroup)
        + (recon z + z) ((5,3) : BaseGroup) = 0 := hw (1,3) 1
    rw [s1, f3] at h
    simpa using h
  have s9 : (recon z + z) ((1,1) : BaseGroup) = 0 := by
    have h : (recon z + z) ((2,4) : BaseGroup) + (recon z + z) ((1,1) : BaseGroup)
        + (recon z + z) ((0,1) : BaseGroup) = 0 := hw (2,1) 1
    rw [s3, s5] at h
    simpa using h
  have s10 : (recon z + z) ((1,2) : BaseGroup) = 0 := by
    have h : (recon z + z) ((2,5) : BaseGroup) + (recon z + z) ((1,2) : BaseGroup)
        + (recon z + z) ((0,2) : BaseGroup) = 0 := hw (2,2) 1
    rw [s4, s6] at h
    simpa using h
  have s11 : (recon z + z) ((1,3) : BaseGroup) = 0 := by
    have h : (recon z + z) ((2,0) : BaseGroup) + (recon z + z) ((1,3) : BaseGroup)
        + (recon z + z) ((0,3) : BaseGroup) = 0 := hw (2,3) 1
    rw [s2, s8] at h
    simpa using h
  have s12 : (recon z + z) ((3,3) : BaseGroup) = 0 := by
    have h : (recon z + z) ((3,3) : BaseGroup) + (recon z + z) ((2,0) : BaseGroup)
        + (recon z + z) ((1,0) : BaseGroup) = 0 := hw (3,0) 1
    rw [s2, s1] at h
    simpa using h
  have s13 : (recon z + z) ((3,2) : BaseGroup) = 0 := by
    have h : (recon z + z) ((3,2) : BaseGroup) + (recon z + z) ((2,5) : BaseGroup)
        + (recon z + z) ((1,5) : BaseGroup) = 0 := hw (3,5) 1
    rw [s4, s7] at h
    simpa using h
  have s14 : (recon z + z) ((2,2) : BaseGroup) = 0 := by
    have h : (recon z + z) ((4,5) : BaseGroup) + (recon z + z) ((3,2) : BaseGroup)
        + (recon z + z) ((2,2) : BaseGroup) = 0 := hw (4,2) 1
    rw [f1, s13] at h
    simpa using h
  have s15 : (recon z + z) ((4,2) : BaseGroup) = 0 := by
    have h : (recon z + z) ((5,5) : BaseGroup) + (recon z + z) ((4,2) : BaseGroup)
        + (recon z + z) ((3,2) : BaseGroup) = 0 := hw (5,2) 1
    rw [f5, s13] at h
    simpa using h
  have s16 : (recon z + z) ((3,5) : BaseGroup) = 0 := by
    have h : (recon z + z) ((5,2) : BaseGroup) + (recon z + z) ((4,5) : BaseGroup)
        + (recon z + z) ((3,5) : BaseGroup) = 0 := hw (5,5) 1
    rw [f2, f1] at h
    simpa using h
  have s17 : (recon z + z) ((0,0) : BaseGroup) = 0 := by
    have h : (recon z + z) ((3,2) : BaseGroup) + (recon z + z) ((0,1) : BaseGroup)
        + (recon z + z) ((0,0) : BaseGroup) = 0 := hw (0,2) 0
    rw [s13, s5] at h
    simpa using h
  have s18 : (recon z + z) ((3,4) : BaseGroup) = 0 := by
    have h : (recon z + z) ((3,4) : BaseGroup) + (recon z + z) ((0,3) : BaseGroup)
        + (recon z + z) ((0,2) : BaseGroup) = 0 := hw (0,4) 0
    rw [s8, s6] at h
    simpa using h
  have s19 : (recon z + z) ((0,4) : BaseGroup) = 0 := by
    have h : (recon z + z) ((3,5) : BaseGroup) + (recon z + z) ((0,4) : BaseGroup)
        + (recon z + z) ((0,3) : BaseGroup) = 0 := hw (0,5) 0
    rw [s16, s8] at h
    simpa using h
  have s20 : (recon z + z) ((4,1) : BaseGroup) = 0 := by
    have h : (recon z + z) ((4,1) : BaseGroup) + (recon z + z) ((1,0) : BaseGroup)
        + (recon z + z) ((1,5) : BaseGroup) = 0 := hw (1,1) 0
    rw [s1, s7] at h
    simpa using h
  have s21 : (recon z + z) ((4,3) : BaseGroup) = 0 := by
    have h : (recon z + z) ((4,3) : BaseGroup) + (recon z + z) ((1,2) : BaseGroup)
        + (recon z + z) ((1,1) : BaseGroup) = 0 := hw (1,3) 0
    rw [s10, s9] at h
    simpa using h
  have s22 : (recon z + z) ((1,4) : BaseGroup) = 0 := by
    have h : (recon z + z) ((4,5) : BaseGroup) + (recon z + z) ((1,4) : BaseGroup)
        + (recon z + z) ((1,3) : BaseGroup) = 0 := hw (1,5) 0
    rw [f1, s11] at h
    simpa using h
  have s23 : (recon z + z) ((5,0) : BaseGroup) = 0 := by
    have h : (recon z + z) ((5,0) : BaseGroup) + (recon z + z) ((2,5) : BaseGroup)
        + (recon z + z) ((2,4) : BaseGroup) = 0 := hw (2,0) 0
    rw [s4, s3] at h
    simpa using h
  have s24 : (recon z + z) ((5,1) : BaseGroup) = 0 := by
    have h : (recon z + z) ((5,1) : BaseGroup) + (recon z + z) ((2,0) : BaseGroup)
        + (recon z + z) ((2,5) : BaseGroup) = 0 := hw (2,1) 0
    rw [s2, s4] at h
    simpa using h
  have s25 : (recon z + z) ((2,1) : BaseGroup) = 0 := by
    have h : (recon z + z) ((5,2) : BaseGroup) + (recon z + z) ((2,1) : BaseGroup)
        + (recon z + z) ((2,0) : BaseGroup) = 0 := hw (2,2) 0
    rw [f2, s2] at h
    simpa using h
  have s26 : (recon z + z) ((2,3) : BaseGroup) = 0 := by
    have h : (recon z + z) ((5,4) : BaseGroup) + (recon z + z) ((2,3) : BaseGroup)
        + (recon z + z) ((2,2) : BaseGroup) = 0 := hw (2,4) 0
    rw [f4, s14] at h
    simpa using h
  have s27 : (recon z + z) ((3,0) : BaseGroup) = 0 := by
    have h : (recon z + z) ((0,1) : BaseGroup) + (recon z + z) ((3,0) : BaseGroup)
        + (recon z + z) ((3,5) : BaseGroup) = 0 := hw (3,1) 0
    rw [s5, s16] at h
    simpa using h
  have s28 : (recon z + z) ((3,1) : BaseGroup) = 0 := by
    have h : (recon z + z) ((0,2) : BaseGroup) + (recon z + z) ((3,1) : BaseGroup)
        + (recon z + z) ((3,0) : BaseGroup) = 0 := hw (3,2) 0
    rw [s6, s27] at h
    simpa using h
  have s29 : (recon z + z) ((0,5) : BaseGroup) = 0 := by
    have h : (recon z + z) ((0,5) : BaseGroup) + (recon z + z) ((3,4) : BaseGroup)
        + (recon z + z) ((3,3) : BaseGroup) = 0 := hw (3,5) 0
    rw [s18, s12] at h
    simpa using h
  have s30 : (recon z + z) ((4,0) : BaseGroup) = 0 := by
    have h : (recon z + z) ((1,1) : BaseGroup) + (recon z + z) ((4,0) : BaseGroup)
        + (recon z + z) ((4,5) : BaseGroup) = 0 := hw (4,1) 0
    rw [s9, f1] at h
    simpa using h
  have hZ6 : ∀ x : ZMod 6, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 := by decide
  have hall : ∀ c : BaseGroup, (recon z + z) c = 0 := by
    intro c
    obtain ⟨a, b⟩ := c
    rcases hZ6 a with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hZ6 b with rfl | rfl | rfl | rfl | rfl | rfl
    · exact s17
    · exact s5
    · exact s6
    · exact s8
    · exact s19
    · exact s29
    · exact s1
    · exact s9
    · exact s10
    · exact s11
    · exact s22
    · exact s7
    · exact s2
    · exact s25
    · exact s14
    · exact s26
    · exact s3
    · exact s4
    · exact s27
    · exact s28
    · exact s13
    · exact s12
    · exact s18
    · exact s16
    · exact s30
    · exact s20
    · exact s15
    · exact s21
    · exact f0
    · exact f1
    · exact s23
    · exact s24
    · exact f2
    · exact f3
    · exact f4
    · exact f5
  funext h
  have hcancel : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  exact hcancel _ _ (hall h)

/-- M-VANISH on all 64 combinations: `off₀ = off₂ = 0` (both blocks). -/
theorem offVanish_combo : ∀ c0 c1 c2 c3 c4 c5 : ZMod 2, ∀ s : ZMod 2 × ZMod 2,
    V psi0 s (leftHalf (seamC (kcombo c0 c1 c2 c3 c4 c5))) = 0 ∧
    V psi0 s (rightHalf (seamC (kcombo c0 c1 c2 c3 c4 c5))) = 0 ∧
    V psi2 s (leftHalf (seamC (kcombo c0 c1 c2 c3 c4 c5))) = 0 ∧
    V psi2 s (rightHalf (seamC (kcombo c0 c1 c2 c3 c4 c5))) = 0 := by
  intro c0 c1 c2 c3 c4 c5 s
  rw [seamC_kcombo_mask]
  revert c0 c1 c2 c3 c4 c5 s
  decide +kernel

/-- **M-VANISH for all ζ ∈ ker ∂₂** (A4 §9.4 Sharpening 1): the CRT components 0 and 2
of `seamC ζ` vanish on both blocks.  (Spanning reduces `ζ` to one of 64 combos.) -/
theorem off_vanish (z : BaseGroup → ZMod 2) (hz : bbBoundary2Fn baseA baseB z = 0)
    (s : ZMod 2 × ZMod 2) :
    V psi0 s (leftHalf (seamC z)) = 0 ∧ V psi0 s (rightHalf (seamC z)) = 0 ∧
    V psi2 s (leftHalf (seamC z)) = 0 ∧ V psi2 s (rightHalf (seamC z)) = 0 := by
  rw [← kerBasis_spans z hz, recon_eq_kcombo]
  exact offVanish_combo _ _ _ _ _ _ s

/-! ## §2b The coset block decomposition

A Smith-coset element `seamC ζ + ∂₂ f` splits, block by block, into the seam profile
plus the `f`-convolution: the A-block (`j = 0`) is `leftHalf (seamC ζ) + conv baseA f`,
the B-block (`j = 1`) is `rightHalf (seamC ζ) + conv baseB f`.  Composed with the CRT
transform `V` (additive, multiplicative through `conv baseA/baseB`), this exposes the
coset's per-component data `off_j(ζ) ⊕ P̂_j · V_j f` that the §10 slot frame bounds. -/

/-- A-block of a coset element: `leftHalf (seamC ζ + ∂₂ f) = leftHalf (seamC ζ) + A⋆f`. -/
theorem leftHalf_coset (ζ f : BaseGroup → ZMod 2) :
    leftHalf (seamC ζ + bbBoundary2Fn baseA baseB f)
      = leftHalf (seamC ζ) + baseA ⋆ f := rfl

/-- B-block of a coset element: `rightHalf (seamC ζ + ∂₂ f) = rightHalf (seamC ζ) + B⋆f`. -/
theorem rightHalf_coset (ζ f : BaseGroup → ZMod 2) :
    rightHalf (seamC ζ + bbBoundary2Fn baseA baseB f)
      = rightHalf (seamC ζ) + baseB ⋆ f := rfl

/-! ## §3 The coset CRT profile: `V_j(coset) = off_j(ζ) ⊕ P̂_j · V_j f`

Composing the block split (§2b) with the additivity (`V_add`) and multiplicativity
(`mult_*`) of the CRT transform, the `j`-th component of a coset element is the seam
offset `off_j(ζ) = V_j(seamC ζ)` plus the engine-multiplied free datum `P̂_j · V_j f`
(`P̂ = Â` on the A-block `j=0`, `B̂` on the B-block `j=1`).  The radical multipliers are
`Â₁=Â₃=Ahat1`, `Â₄=Ahat4`, `B̂₂=B̂₃=B̂₄=Bhat2`; the rest are `unitHat`.  These are the
per-slot inputs the §10 slot frame minimizes over the free datum `t̂_j = V_j f`. -/

variable (ζ f : BaseGroup → ZMod 2) (s : ZMod 2 × ZMod 2)

theorem Vcoset_L0 : V psi0 s (leftHalf (seamC ζ + bbBoundary2Fn baseA baseB f))
    = fadd (V psi0 s (leftHalf (seamC ζ))) (rmul unitHat (fun s' => V psi0 s' f) s) := by
  rw [leftHalf_coset, V_add, mult_A0]
theorem Vcoset_L1 : V psi1 s (leftHalf (seamC ζ + bbBoundary2Fn baseA baseB f))
    = fadd (V psi1 s (leftHalf (seamC ζ))) (rmul Ahat1 (fun s' => V psi1 s' f) s) := by
  rw [leftHalf_coset, V_add, mult_A1]
theorem Vcoset_L2 : V psi2 s (leftHalf (seamC ζ + bbBoundary2Fn baseA baseB f))
    = fadd (V psi2 s (leftHalf (seamC ζ))) (rmul unitHat (fun s' => V psi2 s' f) s) := by
  rw [leftHalf_coset, V_add, mult_A2]
theorem Vcoset_L3 : V psi3 s (leftHalf (seamC ζ + bbBoundary2Fn baseA baseB f))
    = fadd (V psi3 s (leftHalf (seamC ζ))) (rmul Ahat1 (fun s' => V psi3 s' f) s) := by
  rw [leftHalf_coset, V_add, mult_A3]
theorem Vcoset_L4 : V psi4 s (leftHalf (seamC ζ + bbBoundary2Fn baseA baseB f))
    = fadd (V psi4 s (leftHalf (seamC ζ))) (rmul Ahat4 (fun s' => V psi4 s' f) s) := by
  rw [leftHalf_coset, V_add, mult_A4]
theorem Vcoset_R0 : V psi0 s (rightHalf (seamC ζ + bbBoundary2Fn baseA baseB f))
    = fadd (V psi0 s (rightHalf (seamC ζ))) (rmul unitHat (fun s' => V psi0 s' f) s) := by
  rw [rightHalf_coset, V_add, mult_B0]
theorem Vcoset_R1 : V psi1 s (rightHalf (seamC ζ + bbBoundary2Fn baseA baseB f))
    = fadd (V psi1 s (rightHalf (seamC ζ))) (rmul unitHat (fun s' => V psi1 s' f) s) := by
  rw [rightHalf_coset, V_add, mult_B1]
theorem Vcoset_R2 : V psi2 s (rightHalf (seamC ζ + bbBoundary2Fn baseA baseB f))
    = fadd (V psi2 s (rightHalf (seamC ζ))) (rmul Bhat2 (fun s' => V psi2 s' f) s) := by
  rw [rightHalf_coset, V_add, mult_B2]
theorem Vcoset_R3 : V psi3 s (rightHalf (seamC ζ + bbBoundary2Fn baseA baseB f))
    = fadd (V psi3 s (rightHalf (seamC ζ))) (rmul Bhat2 (fun s' => V psi3 s' f) s) := by
  rw [rightHalf_coset, V_add, mult_B3]
theorem Vcoset_R4 : V psi4 s (rightHalf (seamC ζ + bbBoundary2Fn baseA baseB f))
    = fadd (V psi4 s (rightHalf (seamC ζ))) (rmul Bhat2 (fun s' => V psi4 s' f) s) := by
  rw [rightHalf_coset, V_add, mult_B4]

/-! ## §5 The exact per-slot weight (the Fourier bijection)

The torus-Fourier map `g ↦ (V₀,…,V₄)` is a BIJECTION on the 512 layers (Z₃² is
coprime to char 2), so `weight3` is an EXACT function of the 5 CRT components:
`weight3 (slice b s) = wt5OfComps (V ψⱼ s b)`.  This exact per-slot weight is what the
confined-floor engine (`MImFloor`) minimizes over the coset's free data. -/

/-- The exact weight of a torus layer as a function of its 5 CRT-Fourier components
(`v₀ ∈ {0,1}`; index `v₀ + 2·(v₁ + 4·(v₂ + 4·(v₃ + 4·v₄)))`). -/
def WT5_TABLE : Array Nat :=
  #[0,9,6,3,6,3,6,3,6,3,4,5,4,5,4,5,6,3,4,5,4,5,4,5,6,3,4,5,4,5,4,5,6,3,4,5,4,5,4,5,4,5,2,7,6,3,
    6,3,4,5,6,3,6,3,2,7,4,5,6,3,2,7,6,3,6,3,4,5,4,5,4,5,4,5,6,3,2,7,6,3,4,5,2,7,6,3,6,3,4,5,6,3,
    6,3,2,7,6,3,4,5,4,5,4,5,4,5,6,3,6,3,2,7,4,5,6,3,2,7,6,3,4,5,2,7,6,3,6,3,6,3,4,5,4,5,4,5,4,5,
    2,7,6,3,6,3,4,5,6,3,2,7,6,3,4,5,6,3,6,3,2,7,4,5,2,7,6,3,6,3,2,7,8,1,4,5,4,5,6,3,4,5,4,5,4,5,
    6,3,4,5,4,5,4,5,4,5,6,3,6,3,2,7,6,3,4,5,4,5,4,5,6,3,4,5,4,5,4,5,2,7,4,5,4,5,8,1,4,5,6,3,2,7,
    6,3,6,3,4,5,4,5,4,5,2,7,4,5,8,1,4,5,6,3,4,5,4,5,4,5,6,3,4,5,4,5,4,5,4,5,6,3,6,3,2,7,4,5,2,7,
    6,3,6,3,4,5,6,3,2,7,6,3,4,5,6,3,2,7,6,3,6,3,4,5,4,5,4,5,6,3,4,5,4,5,4,5,2,7,4,5,8,1,4,5,4,5,
    2,7,6,3,6,3,6,3,4,5,4,5,4,5,2,7,8,1,4,5,4,5,6,3,4,5,4,5,4,5,4,5,6,3,6,3,2,7,2,7,4,5,4,5,8,1,
    6,3,4,5,4,5,4,5,6,3,4,5,4,5,4,5,6,3,4,5,4,5,4,5,4,5,6,3,2,7,6,3,4,5,6,3,6,3,2,7,4,5,2,7,6,3,
    6,3,4,5,6,3,6,3,2,7,6,3,4,5,4,5,4,5,2,7,4,5,4,5,8,1,6,3,4,5,4,5,4,5,4,5,6,3,2,7,6,3,2,7,4,5,
    8,1,4,5,6,3,4,5,4,5,4,5,6,3,4,5,4,5,4,5,4,5,2,7,6,3,6,3,6,3,4,5,4,5,4,5,6,3,4,5,4,5,4,5,2,7,
    8,1,4,5,4,5]

/-- `WT5_TABLE` packed into one `Nat` literal at 8 bits per entry, with the two
`getD`-default slots `99` appended at indices `512, 513` (reachable from `Fin 4`
arguments as `v0 + 2·255` for `v0 ∈ {2,3}`); `wt5OfComps_eq_wt5N` certifies
agreement with the `WT5_TABLE.getD` form on the whole `Fin 4⁵` domain.  Packed so
lookups are kernel-accelerated `Nat` ops, keeping the downstream `decide` walks
cheap.  (A numeric literal cannot wrap lines, hence the long line.) -/
def WT5_N : Nat :=
  0x63630504050401080702050405040504030605040504050403060306030607020504050405040504030605040504050403060504010805040702030607020306050405040504050403060108050405040702050405040504030607020306030605040306030607020504070203060306050403060702030605040504050405040306050405040504030605040504050403060108050405040702070203060306050405040504050403060504050401080702050405040504030603060306070205040504010805040702050405040504030605040504050403060306070203060504030607020306050403060306070205040702030603060504050405040504030605040504050403060504010805040702050405040504030603060702030605040108050405040702050405040504030605040504050403060702030603060504050405040504030605040504050403060504050401080702030603060702050407020306030605040306070203060504030603060702050405040504050403060306030607020504030607020306050407020306030605040504050405040306070203060306050403060306070205040306070203060504050405040504030603060702030605040702030603060504030603060702050405040504050403060504050405040306050405040504030605040504050403060306030603060900

/-- `weight3` read off the 5 CRT components. -/
def wt5OfComps (v0 v1 v2 v3 v4 : Fin 4) : Nat :=
  (WT5_N >>> (8 * (v0.val + 2*(v1.val + 4*(v2.val + 4*(v3.val + 4*v4.val)))))) &&& 255

/-- **The Fourier bijection**: `weight3` is the exact `wt5OfComps` of the layer's
five torus-Fourier coefficients (kernel `decide` over the 512 layers via `mkTorus`). -/
theorem weight3_eq_wt5 : ∀ g : ZMod 3 × ZMod 3 → ZMod 2,
    weight3 g = wt5OfComps (fhat3 g (0,0)) (fhat3 g (0,1)) (fhat3 g (1,0)) (fhat3 g (1,1))
      (fhat3 g (1,2)) := by
  have core : ∀ v00 v01 v02 v10 v11 v12 v20 v21 v22 : ZMod 2,
      weight3 (mkTorus v00 v01 v02 v10 v11 v12 v20 v21 v22)
        = wt5OfComps (fhat3 (mkTorus v00 v01 v02 v10 v11 v12 v20 v21 v22) (0,0))
            (fhat3 (mkTorus v00 v01 v02 v10 v11 v12 v20 v21 v22) (0,1))
            (fhat3 (mkTorus v00 v01 v02 v10 v11 v12 v20 v21 v22) (1,0))
            (fhat3 (mkTorus v00 v01 v02 v10 v11 v12 v20 v21 v22) (1,1))
            (fhat3 (mkTorus v00 v01 v02 v10 v11 v12 v20 v21 v22) (1,2)) := by
    decide +kernel
  intro g
  rw [eq_mkTorus g]
  exact core _ _ _ _ _ _ _ _ _

/-- The exact per-slot weight of a block-slice, in CRT components (`V ψⱼ`). -/
theorem weight3_eq_wt5_slice (b : BaseGroup → ZMod 2) (s : ZMod 2 × ZMod 2) :
    weight3 (slice b s)
      = wt5OfComps (V psi0 s b) (V psi1 s b) (V psi2 s b) (V psi3 s b) (V psi4 s b) := by
  rw [weight3_eq_wt5 (slice b s), ← fourier_bridge0, ← fourier_bridge1, ← fourier_bridge2,
    ← fourier_bridge3, ← fourier_bridge4]

/-! ## §6 The chain weight as a per-slot `wt5` sum of the ten CRT components

The exact per-slot weight (§5) lifts the layer-sum decomposition (§0) to a closed
form: `chainWeight` of any base 1-chain is the sum, over the four `Z₂²` slots, of
`wt5OfComps` applied to the chain's ten CRT components (five per block).  This is the
form the §10 slot frame minimizes over the coset's free data — composing it with the
`f`-dependence (§3) expresses the coset weight as `costFromComps` of the seam offsets
`⊕ Â/B̂·(Vⱼ f)`, the input to the confined-floor enumeration. -/

/-- The chain weight as a sum over `Z₂²` slots of the two blocks' per-slot `wt5`
of their five CRT components. -/
def costFromComps (vL0 vL1 vL2 vL3 vL4 vR0 vR1 vR2 vR3 vR4 : ZMod 2 × ZMod 2 → Fin 4) : Nat :=
  ∑ s : ZMod 2 × ZMod 2,
    (wt5OfComps (vL0 s) (vL1 s) (vL2 s) (vL3 s) (vL4 s)
     + wt5OfComps (vR0 s) (vR1 s) (vR2 s) (vR3 s) (vR4 s))

/-- **The closed weight form** (§0 ▸ §5): `chainWeight` is `costFromComps` of the chain's
ten CRT components (`V ψⱼ s` on each block).  Structural — `chainWeight_eq_layer_sum`
followed by `weight3_eq_wt5_slice` on each block-slice. -/
theorem chainWeight_eq_costFromComps (c : BaseGroup × Fin 2 → ZMod 2) :
    bb72Complex.chainWeight c = costFromComps
      (fun s => V psi0 s (leftHalf c)) (fun s => V psi1 s (leftHalf c))
      (fun s => V psi2 s (leftHalf c)) (fun s => V psi3 s (leftHalf c))
      (fun s => V psi4 s (leftHalf c))
      (fun s => V psi0 s (rightHalf c)) (fun s => V psi1 s (rightHalf c))
      (fun s => V psi2 s (rightHalf c)) (fun s => V psi3 s (rightHalf c))
      (fun s => V psi4 s (rightHalf c)) := by
  rw [chainWeight_eq_layer_sum]
  simp_rw [weight3_eq_wt5_slice]
  simp only [costFromComps, Finset.sum_add_distrib]

/-! ## §7 The coset weight in component form (the `f`-dependence)

Composing the closed weight form (§6) with the coset CRT profile (§3) writes the
safe-sector coset weight `chainWeight (seamC ζ + ∂₂ f)` as `costFromComps` of the ten
coset components `shifted (seam offset) multiplier (Vⱼ f)`: each component is the seam
offset `Vⱼ(seamC ζ)` plus the engine-multiplied free datum `P̂ⱼ · Vⱼ f`, with
`Â = (unitHat, Ahat1, unitHat, Ahat1, Ahat4)` on the A-block and
`B̂ = (unitHat, unitHat, Bhat2, Bhat2, Bhat2)` on the B-block.  The helpers
`seamOffL/R` (the per-orbit offsets) and `compF` (the free datum) are the data the
confined-floor enumeration ranges over. -/

/-- The `ζ`-seam offset of CRT component `ψ` on the A-block (`leftHalf (seamC ζ)`). -/
def seamOffL (ζ : BaseGroup → ZMod 2) (psi : BaseGroup → Fin 4) : Ring :=
  fun s => V psi s (leftHalf (seamC ζ))
/-- The `ζ`-seam offset of CRT component `ψ` on the B-block (`rightHalf (seamC ζ)`). -/
def seamOffR (ζ : BaseGroup → ZMod 2) (psi : BaseGroup → Fin 4) : Ring :=
  fun s => V psi s (rightHalf (seamC ζ))
/-! ### Seam offsets through the packed mask (the per-orbit evaluation gateway) -/

/-- A Smith class's A-block seam offsets, evaluated through the packed mask. -/
theorem seamOffL_mask (c0 c1 c2 c3 c4 c5 : ZMod 2) (psi : BaseGroup → Fin 4)
    (s : ZMod 2 × ZMod 2) :
    seamOffL (kcombo c0 c1 c2 c3 c4 c5) psi s
      = V psi s (leftHalf (chainOfMask (comboMask c0 c1 c2 c3 c4 c5))) := by
  change V psi s (leftHalf (seamC (kcombo c0 c1 c2 c3 c4 c5))) = _
  rw [seamC_kcombo_mask]

/-- A Smith class's B-block seam offsets, evaluated through the packed mask. -/
theorem seamOffR_mask (c0 c1 c2 c3 c4 c5 : ZMod 2) (psi : BaseGroup → Fin 4)
    (s : ZMod 2 × ZMod 2) :
    seamOffR (kcombo c0 c1 c2 c3 c4 c5) psi s
      = V psi s (rightHalf (chainOfMask (comboMask c0 c1 c2 c3 c4 c5))) := by
  change V psi s (rightHalf (seamC (kcombo c0 c1 c2 c3 c4 c5))) = _
  rw [seamC_kcombo_mask]

/-- Function-level sparse form of the base boundary (for rewriting under binders). -/
theorem bb2_fun_sparse (f : BaseGroup → ZMod 2) :
    bbBoundary2Fn baseA baseB f
      = fun q => if q.2 = 0 then f (q.1 - (3, 0)) + f (q.1 - (0, 1)) + f (q.1 - (0, 2))
                 else f (q.1 - (0, 3)) + f (q.1 - (1, 0)) + f (q.1 - (2, 0)) := by
  funext q; obtain ⟨p, j⟩ := q; exact bb2_sparse f p j

/-- The `j`-th CRT component of the free datum `f`. -/
def compF (f : BaseGroup → ZMod 2) (psi : BaseGroup → Fin 4) : Ring :=
  fun s => V psi s f
/-- A coset component: seam offset `⊕` engine-multiplied free datum. -/
def shifted (o mult vf : Ring) : Ring := fun s => fadd (o s) (rmul mult vf s)

/-- **The coset weight in component form**: `chainWeight (seamC ζ + ∂₂ f)` is
`costFromComps` of the ten coset components `shifted (seam offset) multiplier (Vⱼ f)`
(§6 ▸ §3).  The substitution is the per-block `Vcoset` profile; `rfl` matches the
`shifted` helpers definitionally. -/
theorem chainWeight_coset_eq (ζ f : BaseGroup → ZMod 2) :
    bb72Complex.chainWeight (seamC ζ + bbBoundary2Fn baseA baseB f)
      = costFromComps
        (shifted (seamOffL ζ psi0) unitHat (compF f psi0))
        (shifted (seamOffL ζ psi1) Ahat1 (compF f psi1))
        (shifted (seamOffL ζ psi2) unitHat (compF f psi2))
        (shifted (seamOffL ζ psi3) Ahat1 (compF f psi3))
        (shifted (seamOffL ζ psi4) Ahat4 (compF f psi4))
        (shifted (seamOffR ζ psi0) unitHat (compF f psi0))
        (shifted (seamOffR ζ psi1) unitHat (compF f psi1))
        (shifted (seamOffR ζ psi2) Bhat2 (compF f psi2))
        (shifted (seamOffR ζ psi3) Bhat2 (compF f psi3))
        (shifted (seamOffR ζ psi4) Bhat2 (compF f psi4)) := by
  rw [chainWeight_eq_costFromComps]
  simp_rw [Vcoset_L0, Vcoset_L1, Vcoset_L2, Vcoset_L3, Vcoset_L4,
           Vcoset_R0, Vcoset_R1, Vcoset_R2, Vcoset_R3, Vcoset_R4]
  rfl

end Quantum.Stabilizer.Homological.BB.LightStab
