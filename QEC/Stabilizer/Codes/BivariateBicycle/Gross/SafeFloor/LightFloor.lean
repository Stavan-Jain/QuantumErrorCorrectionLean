/-
# Phase 6: the light-orbit floor engine (A4 §§12-13, Props 30-32) — ANALYTIC

The three **light** Smith orbits (`Y0`, `Y1`, `Y4`; weights 16/18a/18b) do not
decouple per block: their per-block minima sum to only `8 / 6 / 6`, so the floor
`≥ 12` is genuinely coupled and the weight-24 route (`WtFloor24Bridge`) does not
apply.  This module supplies the coupled argument, as a **kernel-decidable
certificate** over the reduced spine frame:

* the spine reductions (`spine3_reduce`, `spine4_reduce`) collapse a coset's
  free comp-3/comp-4 data to a shared F₄ direction `(a₃, a₄)` with the
  `ω`-linkage `b₄ᴿ = ω·b₄ᴸ`, leaving `16 · 4³ = 1024` **spine cells**;
* on each cell, `minLP`/`minRP` are the per-block minima over that block's own
  knobs — the **Prop 30** floor `min_L + min_R ≥ 10`;
* the `10`-tight cells are killed by the **ρ-links** (Lemma 17): the comp-2
  datum `v₂` that the B-block's confined value forces is the *same* datum whose
  `unitHat`-image is the A-block's comp-2 value, so a tight A-block cannot
  realize the cost its minimum promises.  This is **Prop 31**, evaluated per
  cell rather than through the 118-achiever table.

`killOK` bundles all of it into one `Bool`; `floor_of_killOK` turns
`killOK = true` into the safe-sector floor for the orbit.  Everything is kernel
`decide` — the `2³⁰` `floorOK` enumeration of `MImFloor` is not used.

## The packed frame

Ring elements are indexed by `ringIdx` (two bits per slot, `natslot` order) and
the per-index data is read from `Nat` literals: `RMUU` (the `unitHat`-image),
`IC1T` / `IC2T` (the ideal coordinates of the `Ahat1`- / `Bhat2`-images).  The
per-orbit seam data enters as six 128-bit component tables plus the comp-1
right-block offset; `floor_of_killOK` takes their correctness as hypotheses, so
each orbit file supplies them by its own `decide`.
-/
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.SafeFloor.WtFloor1618
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.LightStabClassify

open Quantum.Stabilizer.Homological.BB
open Quantum.Stabilizer.Homological.BB.CRTFrame
open Quantum.Stabilizer.Homological.BB.LightStab

namespace Quantum.Stabilizer.Homological.BB.LightStab

set_option maxRecDepth 8192

/-! ## §1 The packed ring frame -/

/-- Flat slot index (`(0,0), (1,0), (0,1), (1,1)` ↦ `0, 1, 2, 3`). -/
def slotIdx (s : ZMod 2 × ZMod 2) : Nat := s.1.val + 2 * s.2.val

/-- Flat index of a ring element: two bits per slot, in `slotIdx` order. -/
def ringIdx (r : Ring) : Nat :=
  (r (0,0)).val + 4 * (r (1,0)).val + 16 * (r (0,1)).val + 64 * (r (1,1)).val

/-- Slot values of `rmul unitHat r`, packed two bits per `(index, slot)`. (A
numeric literal cannot wrap lines, hence the long lines in this section.) -/
def RMUU : Nat := 0xffead5c0baaf908575605f4a30251a0faebb8491ebfec1d424310e1b61744b5e5d487762180d3227d7c2fde89287b8ad0c192633495c63768693acb9c3d6e9fcabbe8194eefbc4d121340b1e64714e5bfaefd0c5bfaa958070655a4f35201f0a091c23364c5966738396a9bcc6d3ecf9584d72671d083722d2c7f8ed9782bda857427d681207382dddc8f7e2988db2a706132c394356697c8c99a6b3c9dce3f6f5e0dfcab0a59a8f7f6a55403a2f1005a4b18e9be1f4cbde2e3b04116b7e41540316293c46536c79899ca3b6ccd9e6f35247786d17023d28d8cdf2e79d88b7a2a1b48b9ee4f1cedb2b3e01146e7b4451f0e5dacfb5a09f8a7a6f50453f2a1500

/-- Ideal coordinates `a·4 + b` of `rmul Ahat1 r` (so
`rmul Ahat1 r = a·Â₁ + b·XY`). -/
def IC1T : Nat := 0x48c62eabf37d95151d937bfea628c04ae26c840159d73fbfb739d1540c826ae73fb159dc840ae2626ae40c89d15fb73d951bf3762ea048c8c04ea6237bf51d99d15fb7326ae40c8c840ae2673fb159d37bf51d98c04ea6262ea048cd951bf37ea628c0451d937bfbf37d951048c62ea40c826aefb739d15159d73fbae26c840

/-- Ideal coordinates `a·4 + b` of `rmul Bhat2 r`. -/
def IC2T : Nat := 0x48c51d9ae26fb7362ea37bfc8409d15bf37ea62159d40c8d9518c0473fb26ae73fb26aed9518c04159d40c8bf37ea62c8409d1562ea37bfae26fb73048c51d99d15c84037bf62eafb73ae2651d9048c26ae73fb8c04d95140c8159dea62bf37ea62bf3740c8159d8c04d95126ae73fb51d9048cfb73ae2637bf62ea9d15c840

/-- `wt5OfComps` on `Nat` arguments (same packed table, so the two agree by
`rfl`). -/
@[inline] def wt5P (v0 v1 v2 v3 v4 : Nat) : Nat :=
  (WT5_N >>> (8 * (v0 + 2 * (v1 + 4 * (v2 + 4 * (v3 + 4 * v4)))))) &&& 255

/-- The A/left per-slot cost (comp 2 freed), on `Nat` arguments. -/
@[inline] def mf2P (v0 v1 v3 v4 : Nat) : Nat :=
  min (min (wt5P v0 v1 0 v3 v4) (wt5P v0 v1 1 v3 v4))
      (min (wt5P v0 v1 2 v3 v4) (wt5P v0 v1 3 v3 v4))

/-- The B/right per-slot cost (comp 1 freed), on `Nat` arguments. -/
@[inline] def mf1P (v0 v2 v3 v4 : Nat) : Nat :=
  min (min (wt5P v0 0 v2 v3 v4) (wt5P v0 1 v2 v3 v4))
      (min (wt5P v0 2 v2 v3 v4) (wt5P v0 3 v2 v3 v4))

/-- `rmul unitHat` image of ring index `v` at slot `sn`. -/
@[inline] def ruP (v sn : Nat) : Nat := (RMUU >>> (2 * (v * 4 + sn))) &&& 3
/-- Packed ideal coordinates of the `Ahat1`-image of ring index `v`. -/
@[inline] def ic1P (v : Nat) : Nat := (IC1T >>> (4 * v)) &&& 15
/-- Packed ideal coordinates of the `Bhat2`-image of ring index `v`. -/
@[inline] def ic2P (v : Nat) : Nat := (IC2T >>> (4 * v)) &&& 15
/-- A per-orbit component table entry: knobs `(a, b)` at slot `sn`. -/
@[inline] def pcP (T a b sn : Nat) : Nat := (T >>> (2 * ((a * 4 + b) * 4 + sn))) &&& 3
/-- A per-orbit slot-offset entry. -/
@[inline] def ovP (t sn : Nat) : Nat := (t >>> (2 * sn)) &&& 3
/-- `fmul` on the `Nat` encoding. -/
@[inline] def fmulP (a b : Nat) : Nat := (0x9c78e400 >>> (2 * (a * 4 + b))) &&& 3

/-- `Nat` to `Fin 4` (used to read knobs back out of the packed tables). -/
@[inline] def fin4 (n : Nat) : Fin 4 := ⟨n % 4, Nat.mod_lt _ (by norm_num)⟩

/-- The `Ahat1`-ideal knobs of a ring element, read off `IC1T`. -/
def ia1 (r : Ring) : Fin 4 := fin4 (ic1P (ringIdx r) / 4)
def ib1 (r : Ring) : Fin 4 := fin4 (ic1P (ringIdx r))
/-- The `Bhat2`-ideal knobs of a ring element, read off `IC2T`. -/
def ia2 (r : Ring) : Fin 4 := fin4 (ic2P (ringIdx r) / 4)
def ib2 (r : Ring) : Fin 4 := fin4 (ic2P (ringIdx r))

/-! ## §2 The packed frame is correct (kernel sweeps over the 256 ring elements)
-/

private theorem ringIdx_lt_core : ∀ a b c d : Fin 4, ringIdx (mkRing a b c d) < 256 := by
  decide +kernel

theorem ringIdx_lt (r : Ring) : ringIdx r < 256 := by
  rw [ring_eq_mkRing r]; exact ringIdx_lt_core _ _ _ _

private theorem ruP_core : ∀ (a b c d : Fin 4) (s : ZMod 2 × ZMod 2),
    ruP (ringIdx (mkRing a b c d)) (slotIdx s) = (rmul unitHat (mkRing a b c d) s).val := by
  decide +kernel

/-- `RMUU` reads the `unitHat`-image. -/
theorem ruP_eq (r : Ring) (s : ZMod 2 × ZMod 2) :
    ruP (ringIdx r) (slotIdx s) = (rmul unitHat r s).val := by
  conv_lhs => rw [ring_eq_mkRing r]
  conv_rhs => rw [ring_eq_mkRing r]
  exact ruP_core _ _ _ _ s

private theorem ic1_core : ∀ (a b c d : Fin 4) (s : ZMod 2 × ZMod 2),
    rmul Ahat1 (mkRing a b c d) s
      = fadd (fmul (ia1 (mkRing a b c d)) (Ahat1 s)) (fmul (ib1 (mkRing a b c d)) (uv s)) := by
  decide +kernel

/-- `IC1T` reads the `Ahat1`-ideal coordinates. -/
theorem ic1_eq (r : Ring) :
    rmul Ahat1 r = fun s => fadd (fmul (ia1 r) (Ahat1 s)) (fmul (ib1 r) (uv s)) := by
  funext s
  conv_lhs => rw [ring_eq_mkRing r]
  conv_rhs => rw [ring_eq_mkRing r]
  exact ic1_core _ _ _ _ s

private theorem ic2_core : ∀ (a b c d : Fin 4) (s : ZMod 2 × ZMod 2),
    rmul Bhat2 (mkRing a b c d) s
      = fadd (fmul (ia2 (mkRing a b c d)) (Bhat2 s)) (fmul (ib2 (mkRing a b c d)) (uv s)) := by
  decide +kernel

/-- `IC2T` reads the `Bhat2`-ideal coordinates. -/
theorem ic2_eq (r : Ring) :
    rmul Bhat2 r = fun s => fadd (fmul (ia2 r) (Bhat2 s)) (fmul (ib2 r) (uv s)) := by
  funext s
  conv_lhs => rw [ring_eq_mkRing r]
  conv_rhs => rw [ring_eq_mkRing r]
  exact ic2_core _ _ _ _ s

private theorem ic1P_recompose_core : ∀ a b c d : Fin 4,
    (ia1 (mkRing a b c d)).val * 4 + (ib1 (mkRing a b c d)).val
      = ic1P (ringIdx (mkRing a b c d)) := by decide +kernel

/-- The packed `IC1T` entry recomposes from the two knobs it encodes. -/
theorem ic1P_recompose (r : Ring) : (ia1 r).val * 4 + (ib1 r).val = ic1P (ringIdx r) := by
  conv_lhs => rw [ring_eq_mkRing r]
  conv_rhs => rw [ring_eq_mkRing r]
  exact ic1P_recompose_core _ _ _ _

private theorem ic2P_recompose_core : ∀ a b c d : Fin 4,
    (ia2 (mkRing a b c d)).val * 4 + (ib2 (mkRing a b c d)).val
      = ic2P (ringIdx (mkRing a b c d)) := by decide +kernel

/-- The packed `IC2T` entry recomposes from the two knobs it encodes. -/
theorem ic2P_recompose (r : Ring) : (ia2 r).val * 4 + (ib2 r).val = ic2P (ringIdx r) := by
  conv_lhs => rw [ring_eq_mkRing r]
  conv_rhs => rw [ring_eq_mkRing r]
  exact ic2P_recompose_core _ _ _ _

/-- `wt5P` is `wt5OfComps` on the `Nat` encoding. -/
theorem wt5P_eq (v0 v1 v2 v3 v4 : Fin 4) :
    wt5P v0.val v1.val v2.val v3.val v4.val = wt5OfComps v0 v1 v2 v3 v4 := rfl

/-- `mf2P` is `mFree2` on the `Nat` encoding. -/
theorem mf2P_eq (v0 v1 v3 v4 : Fin 4) :
    mf2P v0.val v1.val v3.val v4.val = mFree2 v0 v1 v3 v4 := rfl

/-- `mf1P` is `mFree1` on the `Nat` encoding. -/
theorem mf1P_eq (v0 v2 v3 v4 : Fin 4) :
    mf1P v0.val v2.val v3.val v4.val = mFree1 v0 v2 v3 v4 := rfl

/-- `fmulP` is `fmul` on the `Nat` encoding. -/
theorem fmulP_eq (a b : Fin 4) : fmulP a.val b.val = (fmul a b).val := by
  revert a b; decide

/-- `fmulP` by the literal `ω`, as it appears in the comp-4 linkage. -/
theorem fmulP_two (b : Fin 4) : fmulP 2 b.val = (fmul 2 b).val := by revert b; decide

/-- `fadd` is `xor` on the `Nat` encoding. -/
theorem fadd_val (a b : Fin 4) : (fadd a b).val = a.val ^^^ b.val := by revert a b; decide

/-! ## §3 List helpers (the fold-min bound and the range sweep) -/

/-- The fold-min bound (`LightStabClassify.foldl_min_le`) specialized to
`List.range`. -/
theorem foldl_min_le_range (g : Nat → Nat) (n init k : Nat) (hk : k < n) :
    (List.range n).foldl (fun m i => min m (g i)) init ≤ g k :=
  foldl_min_le g _ init k (List.mem_range.mpr hk)

theorem range_all_apply {n : Nat} {p : Nat → Bool} (h : (List.range n).all p = true)
    {i : Nat} (hi : i < n) : p i = true :=
  (List.all_eq_true.mp h) i (List.mem_range.mpr hi)

/-! ## §4 The spine-cell checker

`w₀…w₃` are the four `F₂` slot values of the shared component-0 datum `V₀`;
`(a₃, a₄, b₄)` is the spine cell (`b₄ᴿ = ω·b₄` by the comp-4 linkage). The
A-block knobs are `(a₁, b₁, b₃ᴸ)`, the B-block's `(a₂, b₂, b₃ᴿ)`; `v₁`/`v₂` are
ring indices of the comp-1 / comp-2 free data, which link the two blocks. -/

/-- A/left-block cost with comp 2 freed (the `mFree2` per-slot sum). -/
def blockLP (T1 T3 T4 w0 w1 w2 w3 a1 b1 a3 b3 a4 b4 : Nat) : Nat :=
  mf2P w0 (pcP T1 a1 b1 0) (pcP T3 a3 b3 0) (pcP T4 a4 b4 0)
  + mf2P w1 (pcP T1 a1 b1 1) (pcP T3 a3 b3 1) (pcP T4 a4 b4 1)
  + mf2P w2 (pcP T1 a1 b1 2) (pcP T3 a3 b3 2) (pcP T4 a4 b4 2)
  + mf2P w3 (pcP T1 a1 b1 3) (pcP T3 a3 b3 3) (pcP T4 a4 b4 3)

/-- B/right-block cost with comp 1 freed (the `mFree1` per-slot sum). -/
def blockRP (U2 U3 U4 w0 w1 w2 w3 a2 b2 a3 b3 a4 b4R : Nat) : Nat :=
  mf1P w0 (pcP U2 a2 b2 0) (pcP U3 a3 b3 0) (pcP U4 a4 b4R 0)
  + mf1P w1 (pcP U2 a2 b2 1) (pcP U3 a3 b3 1) (pcP U4 a4 b4R 1)
  + mf1P w2 (pcP U2 a2 b2 2) (pcP U3 a3 b3 2) (pcP U4 a4 b4R 2)
  + mf1P w3 (pcP U2 a2 b2 3) (pcP U3 a3 b3 3) (pcP U4 a4 b4R 3)

/-- Exact A/left-block cost, with the comp-2 datum `v₂` supplied. -/
def exLP (T1 T3 T4 w0 w1 w2 w3 a1 b1 b3L a3 a4 b4 v2 : Nat) : Nat :=
  wt5P w0 (pcP T1 a1 b1 0) (ruP v2 0) (pcP T3 a3 b3L 0) (pcP T4 a4 b4 0)
  + wt5P w1 (pcP T1 a1 b1 1) (ruP v2 1) (pcP T3 a3 b3L 1) (pcP T4 a4 b4 1)
  + wt5P w2 (pcP T1 a1 b1 2) (ruP v2 2) (pcP T3 a3 b3L 2) (pcP T4 a4 b4 2)
  + wt5P w3 (pcP T1 a1 b1 3) (ruP v2 3) (pcP T3 a3 b3L 3) (pcP T4 a4 b4 3)

/-- Exact B/right-block cost, with the comp-1 datum `v₁` supplied. -/
def exRP (U2 U3 U4 O1R w0 w1 w2 w3 a2 b2 b3R a3 a4 b4R v1 : Nat) : Nat :=
  wt5P w0 (ovP O1R 0 ^^^ ruP v1 0) (pcP U2 a2 b2 0) (pcP U3 a3 b3R 0) (pcP U4 a4 b4R 0)
  + wt5P w1 (ovP O1R 1 ^^^ ruP v1 1) (pcP U2 a2 b2 1) (pcP U3 a3 b3R 1) (pcP U4 a4 b4R 1)
  + wt5P w2 (ovP O1R 2 ^^^ ruP v1 2) (pcP U2 a2 b2 2) (pcP U3 a3 b3R 2) (pcP U4 a4 b4R 2)
  + wt5P w3 (ovP O1R 3 ^^^ ruP v1 3) (pcP U2 a2 b2 3) (pcP U3 a3 b3R 3) (pcP U4 a4 b4R 3)

/-- A/left-block minimum over the block's own knobs `(a₁, b₁, b₃ᴸ)`. -/
def minLP (T1 T3 T4 w0 w1 w2 w3 a3 a4 b4 : Nat) : Nat :=
  (List.range 64).foldl
    (fun m k => min m (blockLP T1 T3 T4 w0 w1 w2 w3 (k >>> 4) ((k >>> 2) &&& 3) a3 (k &&& 3) a4 b4))
    99

/-- B/right-block minimum over `b₃ᴿ` at a fixed confined pair `(a₂, b₂)`. -/
def mR2P (U2 U3 U4 w0 w1 w2 w3 a2 b2 a3 a4 b4R : Nat) : Nat :=
  (List.range 4).foldl
    (fun m b3 => min m (blockRP U2 U3 U4 w0 w1 w2 w3 a2 b2 a3 b3 a4 b4R)) 99

/-- B/right-block minimum over the block's own knobs `(a₂, b₂, b₃ᴿ)`. -/
def minRP (U2 U3 U4 w0 w1 w2 w3 a3 a4 b4R : Nat) : Nat :=
  (List.range 16).foldl
    (fun m p => min m (mR2P U2 U3 U4 w0 w1 w2 w3 (p >>> 2) (p &&& 3) a3 a4 b4R)) 99

/-- **The per-cell certificate.** Either the cell's two block minima already sum
to `12`, or the cell is `10`-tight and every knob choice within `1` of the
minima is killed: by the exact comp-2 cost the ρ-link forces (`exLP … v₂`), or
failing that by the exact comp-1 cost on the other block (`exRP … v₁`). -/
def killCell (T1 T3 T4 U2 U3 U4 O1R w0 w1 w2 w3 a3 a4 b4 : Nat) : Bool :=
  let b4R := fmulP 2 b4
  let mL := minLP T1 T3 T4 w0 w1 w2 w3 a3 a4 b4
  let mR := minRP U2 U3 U4 w0 w1 w2 w3 a3 a4 b4R
  decide (12 ≤ mL + mR) ||
  (decide (10 ≤ mL + mR) &&
    (List.range 64).all fun kL =>
      decide (mL + 1
          < blockLP T1 T3 T4 w0 w1 w2 w3 (kL >>> 4) ((kL >>> 2) &&& 3) a3 (kL &&& 3) a4 b4)
      || (List.range 16).all fun p =>
        decide (mR + 1 < mR2P U2 U3 U4 w0 w1 w2 w3 (p >>> 2) (p &&& 3) a3 a4 b4R)
        || (List.range 256).all fun v2 =>
          decide (ic2P v2 ≠ p)
          || decide (12 ≤ exLP T1 T3 T4 w0 w1 w2 w3 (kL >>> 4) ((kL >>> 2) &&& 3) (kL &&& 3)
                            a3 a4 b4 v2 + mR)
          || (List.range 4).all fun b3R =>
            decide (mR + 1 < blockRP U2 U3 U4 w0 w1 w2 w3 (p >>> 2) (p &&& 3) a3 b3R a4 b4R)
            || (List.range 256).all fun v1 =>
              decide (ic1P v1 ≠ kL >>> 2)
              || decide (12 ≤ exLP T1 T3 T4 w0 w1 w2 w3 (kL >>> 4) ((kL >>> 2) &&& 3) (kL &&& 3)
                                a3 a4 b4 v2
                          + exRP U2 U3 U4 O1R w0 w1 w2 w3 (p >>> 2) (p &&& 3) b3R a3 a4 b4R v1))

/-- **The orbit certificate**: every one of the `16 · 4³ = 1024` spine cells is
killed. -/
def killOK (T1 T3 T4 U2 U3 U4 O1R : Nat) : Bool :=
  (List.range 2).all fun w0 => (List.range 2).all fun w1 => (List.range 2).all fun w2 =>
    (List.range 2).all fun w3 => (List.range 4).all fun a3 => (List.range 4).all fun a4 =>
      (List.range 4).all fun b4 => killCell T1 T3 T4 U2 U3 U4 O1R w0 w1 w2 w3 a3 a4 b4

/-! ## §5 Soundness of the certificate

The engine's per-slot quantities are lower bounds / exact values of the real
coset components, so a cell certificate transfers to the chain weight. -/

theorem and3_lt (n : Nat) : n &&& 3 < 4 := lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem xor_lt4 {a b : Nat} (ha : a < 4) (hb : b < 4) : a ^^^ b < 4 := by
  interval_cases a <;> interval_cases b <;> decide

theorem ruP_lt (v sn : Nat) : ruP v sn < 4 := and3_lt _
theorem ovP_lt (t sn : Nat) : ovP t sn < 4 := and3_lt _
theorem pcP_lt (T a b sn : Nat) : pcP T a b sn < 4 := and3_lt _

/-- `mFree2` (as `mf2P`) lower-bounds the exact per-slot cost, for any comp-2
value. -/
theorem mf2P_le (v0 v1 v3 v4 x : Nat) (hx : x < 4) : mf2P v0 v1 v3 v4 ≤ wt5P v0 v1 x v3 v4 := by
  interval_cases x <;> unfold mf2P <;> omega

/-- `mFree1` (as `mf1P`) lower-bounds the exact per-slot cost, for any comp-1
value. -/
theorem mf1P_le (v0 v2 v3 v4 x : Nat) (hx : x < 4) : mf1P v0 v2 v3 v4 ≤ wt5P v0 x v2 v3 v4 := by
  interval_cases x <;> unfold mf1P <;> omega

/-- The A-block minimum-form cost lower-bounds the exact one. -/
theorem blockLP_le_exLP (T1 T3 T4 w0 w1 w2 w3 a1 b1 b3L a3 a4 b4 v2 : Nat) :
    blockLP T1 T3 T4 w0 w1 w2 w3 a1 b1 a3 b3L a4 b4
      ≤ exLP T1 T3 T4 w0 w1 w2 w3 a1 b1 b3L a3 a4 b4 v2 := by
  have h0 := mf2P_le w0 (pcP T1 a1 b1 0) (pcP T3 a3 b3L 0) (pcP T4 a4 b4 0) (ruP v2 0) (ruP_lt _ _)
  have h1 := mf2P_le w1 (pcP T1 a1 b1 1) (pcP T3 a3 b3L 1) (pcP T4 a4 b4 1) (ruP v2 1) (ruP_lt _ _)
  have h2 := mf2P_le w2 (pcP T1 a1 b1 2) (pcP T3 a3 b3L 2) (pcP T4 a4 b4 2) (ruP v2 2) (ruP_lt _ _)
  have h3 := mf2P_le w3 (pcP T1 a1 b1 3) (pcP T3 a3 b3L 3) (pcP T4 a4 b4 3) (ruP v2 3) (ruP_lt _ _)
  unfold blockLP exLP
  omega

/-- The B-block minimum-form cost lower-bounds the exact one. -/
theorem blockRP_le_exRP (U2 U3 U4 O1R w0 w1 w2 w3 a2 b2 b3R a3 a4 b4R v1 : Nat) :
    blockRP U2 U3 U4 w0 w1 w2 w3 a2 b2 a3 b3R a4 b4R
      ≤ exRP U2 U3 U4 O1R w0 w1 w2 w3 a2 b2 b3R a3 a4 b4R v1 := by
  have h0 := mf1P_le w0 (pcP U2 a2 b2 0) (pcP U3 a3 b3R 0) (pcP U4 a4 b4R 0)
    (ovP O1R 0 ^^^ ruP v1 0) (xor_lt4 (ovP_lt _ _) (ruP_lt _ _))
  have h1 := mf1P_le w1 (pcP U2 a2 b2 1) (pcP U3 a3 b3R 1) (pcP U4 a4 b4R 1)
    (ovP O1R 1 ^^^ ruP v1 1) (xor_lt4 (ovP_lt _ _) (ruP_lt _ _))
  have h2 := mf1P_le w2 (pcP U2 a2 b2 2) (pcP U3 a3 b3R 2) (pcP U4 a4 b4R 2)
    (ovP O1R 2 ^^^ ruP v1 2) (xor_lt4 (ovP_lt _ _) (ruP_lt _ _))
  have h3 := mf1P_le w3 (pcP U2 a2 b2 3) (pcP U3 a3 b3R 3) (pcP U4 a4 b4R 3)
    (ovP O1R 3 ^^^ ruP v1 3) (xor_lt4 (ovP_lt _ _) (ruP_lt _ _))
  unfold blockRP exRP
  omega

/-- `fadd` has `0` as a left unit. -/
theorem fadd_zero_left (x : Fin 4) : fadd 0 x = x := by revert x; decide

/-- **Coset extraction.** Every Smith-coset element's weight is the exact
`exLP + exRP` of a spine cell, with the comp-1 / comp-2 free data appearing as
ring indices whose packed ideal coordinates are the two blocks' confined knobs —
the ρ-links, in the frame the certificate checks. -/
theorem coset_ex (ζ f : BaseGroup → ZMod 2) (hz : bbBoundary2Fn baseA baseB ζ = 0)
    (T1 T3 T4 U2 U3 U4 O1R : Nat)
    (hT1 : ∀ (a b : Fin 4) (s : ZMod 2 × ZMod 2), pcP T1 a.val b.val (slotIdx s)
      = (fadd (seamOffL ζ psi1 s) (fadd (fmul a (Ahat1 s)) (fmul b (uv s)))).val)
    (hT3 : ∀ (a b : Fin 4) (s : ZMod 2 × ZMod 2), pcP T3 a.val b.val (slotIdx s)
      = (fadd (seamOffL ζ psi3 s) (fadd (fmul a (Ahat1 s)) (fmul b (uv s)))).val)
    (hT4 : ∀ (a b : Fin 4) (s : ZMod 2 × ZMod 2), pcP T4 a.val b.val (slotIdx s)
      = (fadd (seamOffL ζ psi4 s) (fadd (fmul a (Ahat4 s)) (fmul b (uv s)))).val)
    (hU2 : ∀ (a b : Fin 4) (s : ZMod 2 × ZMod 2), pcP U2 a.val b.val (slotIdx s)
      = (fadd (seamOffR ζ psi2 s) (fadd (fmul a (Bhat2 s)) (fmul b (uv s)))).val)
    (hU3 : ∀ (a b : Fin 4) (s : ZMod 2 × ZMod 2), pcP U3 a.val b.val (slotIdx s)
      = (fadd (seamOffR ζ psi3 s) (fadd (fmul a (Bhat2 s)) (fmul b (uv s)))).val)
    (hU4 : ∀ (a b : Fin 4) (s : ZMod 2 × ZMod 2), pcP U4 a.val b.val (slotIdx s)
      = (fadd (seamOffR ζ psi4 s) (fadd (fmul a (Bhat2 s)) (fmul b (uv s)))).val)
    (hO1R : ∀ s : ZMod 2 × ZMod 2, ovP O1R (slotIdx s) = (seamOffR ζ psi1 s).val) :
    ∃ (w0 w1 w2 w3 a1 b1 b3L a3 a4 b4 a2 b2 b3R v1 v2 : Nat),
      w0 < 2 ∧ w1 < 2 ∧ w2 < 2 ∧ w3 < 2 ∧ a1 < 4 ∧ b1 < 4 ∧ b3L < 4 ∧ a3 < 4 ∧ a4 < 4 ∧
      b4 < 4 ∧ a2 < 4 ∧ b2 < 4 ∧ b3R < 4 ∧ v1 < 256 ∧ v2 < 256 ∧
      ic1P v1 = a1 * 4 + b1 ∧ ic2P v2 = a2 * 4 + b2 ∧
      bb72Complex.chainWeight (seamC ζ + bbBoundary2Fn baseA baseB f)
        = exLP T1 T3 T4 w0 w1 w2 w3 a1 b1 b3L a3 a4 b4 v2
          + exRP U2 U3 U4 O1R w0 w1 w2 w3 a2 b2 b3R a3 a4 (fmulP 2 b4) v1 := by
  obtain ⟨a3, b3L, b3R, h3L, h3R⟩ := spine3_reduce (compF f psi3)
  obtain ⟨a4, b4L, h4L, h4R⟩ := spine4_reduce (compF f psi4)
  refine ⟨(shifted (seamOffL ζ psi0) unitHat (compF f psi0) (0,0)).val,
    (shifted (seamOffL ζ psi0) unitHat (compF f psi0) (1,0)).val,
    (shifted (seamOffL ζ psi0) unitHat (compF f psi0) (0,1)).val,
    (shifted (seamOffL ζ psi0) unitHat (compF f psi0) (1,1)).val,
    (ia1 (compF f psi1)).val, (ib1 (compF f psi1)).val, b3L.val, a3.val, a4.val, b4L.val,
    (ia2 (compF f psi2)).val, (ib2 (compF f psi2)).val, b3R.val,
    ringIdx (compF f psi1), ringIdx (compF f psi2),
    comp0_lt2_L ζ f _, comp0_lt2_L ζ f _, comp0_lt2_L ζ f _, comp0_lt2_L ζ f _,
    (ia1 _).isLt, (ib1 _).isLt, b3L.isLt, a3.isLt, a4.isLt, b4L.isLt,
    (ia2 _).isLt, (ib2 _).isLt, b3R.isLt,
    ringIdx_lt _, ringIdx_lt _, (ic1P_recompose _).symm, (ic2P_recompose _).symm, ?_⟩
  have e1 : ∀ s, shifted (seamOffL ζ psi1) Ahat1 (compF f psi1) s
      = fadd (seamOffL ζ psi1 s)
          (fadd (fmul (ia1 (compF f psi1)) (Ahat1 s)) (fmul (ib1 (compF f psi1)) (uv s))) := by
    intro s; show fadd _ (rmul Ahat1 (compF f psi1) s) = _; rw [ic1_eq (compF f psi1)]
  have e2 : ∀ s, shifted (seamOffL ζ psi2) unitHat (compF f psi2) s
      = rmul unitHat (compF f psi2) s := by
    intro s
    show fadd (seamOffL ζ psi2 s) _ = _
    rw [show seamOffL ζ psi2 s = (0 : Fin 4) from (off_vanish ζ hz s).2.2.1, fadd_zero_left]
  have e3 : ∀ s, shifted (seamOffL ζ psi3) Ahat1 (compF f psi3) s
      = fadd (seamOffL ζ psi3 s) (fadd (fmul a3 (Ahat1 s)) (fmul b3L (uv s))) := by
    intro s; show fadd _ (rmul Ahat1 (compF f psi3) s) = _; rw [h3L]
  have e4 : ∀ s, shifted (seamOffL ζ psi4) Ahat4 (compF f psi4) s
      = fadd (seamOffL ζ psi4 s) (fadd (fmul a4 (Ahat4 s)) (fmul b4L (uv s))) := by
    intro s; show fadd _ (rmul Ahat4 (compF f psi4) s) = _; rw [h4L]
  have f0 : ∀ s, shifted (seamOffR ζ psi0) unitHat (compF f psi0) s
      = shifted (seamOffL ζ psi0) unitHat (compF f psi0) s := by
    intro s
    show fadd (seamOffR ζ psi0 s) _ = fadd (seamOffL ζ psi0 s) _
    rw [show seamOffR ζ psi0 s = (0 : Fin 4) from (off_vanish ζ hz s).2.1,
      show seamOffL ζ psi0 s = (0 : Fin 4) from (off_vanish ζ hz s).1]
  have f1 : ∀ s, shifted (seamOffR ζ psi1) unitHat (compF f psi1) s
      = fadd (seamOffR ζ psi1 s) (rmul unitHat (compF f psi1) s) := fun _ => rfl
  have f2 : ∀ s, shifted (seamOffR ζ psi2) Bhat2 (compF f psi2) s
      = fadd (seamOffR ζ psi2 s)
          (fadd (fmul (ia2 (compF f psi2)) (Bhat2 s)) (fmul (ib2 (compF f psi2)) (uv s))) := by
    intro s; show fadd _ (rmul Bhat2 (compF f psi2) s) = _; rw [ic2_eq (compF f psi2)]
  have f3 : ∀ s, shifted (seamOffR ζ psi3) Bhat2 (compF f psi3) s
      = fadd (seamOffR ζ psi3 s) (fadd (fmul a3 (Bhat2 s)) (fmul b3R (uv s))) := by
    intro s; show fadd _ (rmul Bhat2 (compF f psi3) s) = _; rw [h3R]
  have f4 : ∀ s, shifted (seamOffR ζ psi4) Bhat2 (compF f psi4) s
      = fadd (seamOffR ζ psi4 s) (fadd (fmul a4 (Bhat2 s)) (fmul (fmul 2 b4L) (uv s))) := by
    intro s; show fadd _ (rmul Bhat2 (compF f psi4) s) = _; rw [h4R]
  have q10 : pcP T1 (ia1 (compF f psi1)).val (ib1 (compF f psi1)).val 0
      = (fadd (seamOffL ζ psi1 (0,0)) (fadd (fmul (ia1 (compF f psi1)) (Ahat1 (0,0)))
          (fmul (ib1 (compF f psi1)) (uv (0,0))))).val := hT1 _ _ (0,0)
  have q30 : pcP T3 a3.val b3L.val 0
      = (fadd (seamOffL ζ psi3 (0,0)) (fadd (fmul a3 (Ahat1 (0,0))) (fmul b3L (uv (0,0))))).val :=
        hT3 _ _ (0,0)
  have q40 : pcP T4 a4.val b4L.val 0
      = (fadd (seamOffL ζ psi4 (0,0)) (fadd (fmul a4 (Ahat4 (0,0))) (fmul b4L (uv (0,0))))).val :=
        hT4 _ _ (0,0)
  have r20 : pcP U2 (ia2 (compF f psi2)).val (ib2 (compF f psi2)).val 0
      = (fadd (seamOffR ζ psi2 (0,0)) (fadd (fmul (ia2 (compF f psi2)) (Bhat2 (0,0)))
          (fmul (ib2 (compF f psi2)) (uv (0,0))))).val := hU2 _ _ (0,0)
  have r30 : pcP U3 a3.val b3R.val 0
      = (fadd (seamOffR ζ psi3 (0,0)) (fadd (fmul a3 (Bhat2 (0,0))) (fmul b3R (uv (0,0))))).val :=
        hU3 _ _ (0,0)
  have r40 : pcP U4 a4.val (fmulP 2 b4L.val) 0
      = (fadd (seamOffR ζ psi4 (0,0)) (fadd (fmul a4 (Bhat2 (0,0)))
          (fmul (fmul 2 b4L) (uv (0,0))))).val := by rw [fmulP_two]; exact hU4 _ _ (0,0)
  have o10 : ovP O1R 0 = (seamOffR ζ psi1 (0,0)).val := hO1R (0,0)
  have u20 : ruP (ringIdx (compF f psi2)) 0
      = (rmul unitHat (compF f psi2) (0,0)).val := ruP_eq _ (0,0)
  have u10 : ruP (ringIdx (compF f psi1)) 0
      = (rmul unitHat (compF f psi1) (0,0)).val := ruP_eq _ (0,0)
  have q11 : pcP T1 (ia1 (compF f psi1)).val (ib1 (compF f psi1)).val 1
      = (fadd (seamOffL ζ psi1 (1,0)) (fadd (fmul (ia1 (compF f psi1)) (Ahat1 (1,0)))
          (fmul (ib1 (compF f psi1)) (uv (1,0))))).val := hT1 _ _ (1,0)
  have q31 : pcP T3 a3.val b3L.val 1
      = (fadd (seamOffL ζ psi3 (1,0)) (fadd (fmul a3 (Ahat1 (1,0))) (fmul b3L (uv (1,0))))).val :=
        hT3 _ _ (1,0)
  have q41 : pcP T4 a4.val b4L.val 1
      = (fadd (seamOffL ζ psi4 (1,0)) (fadd (fmul a4 (Ahat4 (1,0))) (fmul b4L (uv (1,0))))).val :=
        hT4 _ _ (1,0)
  have r21 : pcP U2 (ia2 (compF f psi2)).val (ib2 (compF f psi2)).val 1
      = (fadd (seamOffR ζ psi2 (1,0)) (fadd (fmul (ia2 (compF f psi2)) (Bhat2 (1,0)))
          (fmul (ib2 (compF f psi2)) (uv (1,0))))).val := hU2 _ _ (1,0)
  have r31 : pcP U3 a3.val b3R.val 1
      = (fadd (seamOffR ζ psi3 (1,0)) (fadd (fmul a3 (Bhat2 (1,0))) (fmul b3R (uv (1,0))))).val :=
        hU3 _ _ (1,0)
  have r41 : pcP U4 a4.val (fmulP 2 b4L.val) 1
      = (fadd (seamOffR ζ psi4 (1,0)) (fadd (fmul a4 (Bhat2 (1,0)))
          (fmul (fmul 2 b4L) (uv (1,0))))).val := by rw [fmulP_two]; exact hU4 _ _ (1,0)
  have o11 : ovP O1R 1 = (seamOffR ζ psi1 (1,0)).val := hO1R (1,0)
  have u21 : ruP (ringIdx (compF f psi2)) 1
      = (rmul unitHat (compF f psi2) (1,0)).val := ruP_eq _ (1,0)
  have u11 : ruP (ringIdx (compF f psi1)) 1
      = (rmul unitHat (compF f psi1) (1,0)).val := ruP_eq _ (1,0)
  have q12 : pcP T1 (ia1 (compF f psi1)).val (ib1 (compF f psi1)).val 2
      = (fadd (seamOffL ζ psi1 (0,1)) (fadd (fmul (ia1 (compF f psi1)) (Ahat1 (0,1)))
          (fmul (ib1 (compF f psi1)) (uv (0,1))))).val := hT1 _ _ (0,1)
  have q32 : pcP T3 a3.val b3L.val 2
      = (fadd (seamOffL ζ psi3 (0,1)) (fadd (fmul a3 (Ahat1 (0,1))) (fmul b3L (uv (0,1))))).val :=
        hT3 _ _ (0,1)
  have q42 : pcP T4 a4.val b4L.val 2
      = (fadd (seamOffL ζ psi4 (0,1)) (fadd (fmul a4 (Ahat4 (0,1))) (fmul b4L (uv (0,1))))).val :=
        hT4 _ _ (0,1)
  have r22 : pcP U2 (ia2 (compF f psi2)).val (ib2 (compF f psi2)).val 2
      = (fadd (seamOffR ζ psi2 (0,1)) (fadd (fmul (ia2 (compF f psi2)) (Bhat2 (0,1)))
          (fmul (ib2 (compF f psi2)) (uv (0,1))))).val := hU2 _ _ (0,1)
  have r32 : pcP U3 a3.val b3R.val 2
      = (fadd (seamOffR ζ psi3 (0,1)) (fadd (fmul a3 (Bhat2 (0,1))) (fmul b3R (uv (0,1))))).val :=
        hU3 _ _ (0,1)
  have r42 : pcP U4 a4.val (fmulP 2 b4L.val) 2
      = (fadd (seamOffR ζ psi4 (0,1)) (fadd (fmul a4 (Bhat2 (0,1)))
          (fmul (fmul 2 b4L) (uv (0,1))))).val := by rw [fmulP_two]; exact hU4 _ _ (0,1)
  have o12 : ovP O1R 2 = (seamOffR ζ psi1 (0,1)).val := hO1R (0,1)
  have u22 : ruP (ringIdx (compF f psi2)) 2
      = (rmul unitHat (compF f psi2) (0,1)).val := ruP_eq _ (0,1)
  have u12 : ruP (ringIdx (compF f psi1)) 2
      = (rmul unitHat (compF f psi1) (0,1)).val := ruP_eq _ (0,1)
  have q13 : pcP T1 (ia1 (compF f psi1)).val (ib1 (compF f psi1)).val 3
      = (fadd (seamOffL ζ psi1 (1,1)) (fadd (fmul (ia1 (compF f psi1)) (Ahat1 (1,1)))
          (fmul (ib1 (compF f psi1)) (uv (1,1))))).val := hT1 _ _ (1,1)
  have q33 : pcP T3 a3.val b3L.val 3
      = (fadd (seamOffL ζ psi3 (1,1)) (fadd (fmul a3 (Ahat1 (1,1))) (fmul b3L (uv (1,1))))).val :=
        hT3 _ _ (1,1)
  have q43 : pcP T4 a4.val b4L.val 3
      = (fadd (seamOffL ζ psi4 (1,1)) (fadd (fmul a4 (Ahat4 (1,1))) (fmul b4L (uv (1,1))))).val :=
        hT4 _ _ (1,1)
  have r23 : pcP U2 (ia2 (compF f psi2)).val (ib2 (compF f psi2)).val 3
      = (fadd (seamOffR ζ psi2 (1,1)) (fadd (fmul (ia2 (compF f psi2)) (Bhat2 (1,1)))
          (fmul (ib2 (compF f psi2)) (uv (1,1))))).val := hU2 _ _ (1,1)
  have r33 : pcP U3 a3.val b3R.val 3
      = (fadd (seamOffR ζ psi3 (1,1)) (fadd (fmul a3 (Bhat2 (1,1))) (fmul b3R (uv (1,1))))).val :=
        hU3 _ _ (1,1)
  have r43 : pcP U4 a4.val (fmulP 2 b4L.val) 3
      = (fadd (seamOffR ζ psi4 (1,1)) (fadd (fmul a4 (Bhat2 (1,1)))
          (fmul (fmul 2 b4L) (uv (1,1))))).val := by rw [fmulP_two]; exact hU4 _ _ (1,1)
  have o13 : ovP O1R 3 = (seamOffR ζ psi1 (1,1)).val := hO1R (1,1)
  have u23 : ruP (ringIdx (compF f psi2)) 3
      = (rmul unitHat (compF f psi2) (1,1)).val := ruP_eq _ (1,1)
  have u13 : ruP (ringIdx (compF f psi1)) 3
      = (rmul unitHat (compF f psi1) (1,1)).val := ruP_eq _ (1,1)
  rw [chainWeight_coset_eq ζ f, costFromComps, sum_zmod2sq]
  unfold exLP exRP
  rw [q10, q30, q40, r20, r30, r40, o10, u20, u10, q11, q31, q41, r21, r31, r41, o11, u21, u11, q12, q32, q42, r22, r32, r42, o12, u22, u12, q13, q33, q43, r23, r33, r43, o13, u23, u13]
  rw [e1, e1, e1, e1, e2, e2, e2, e2, e3, e3, e3, e3, e4, e4, e4, e4,
      f0, f0, f0, f0, f1, f1, f1, f1, f2, f2, f2, f2, f3, f3, f3, f3, f4, f4, f4, f4]
  rw [← fadd_val, ← fadd_val, ← fadd_val, ← fadd_val]
  rw [wt5P_eq, wt5P_eq, wt5P_eq, wt5P_eq, wt5P_eq, wt5P_eq, wt5P_eq, wt5P_eq]
  omega

/-! ## §7 The certificate implies the floor -/

/-- **The light-orbit floor from the certificate.** A verified `killOK` bounds
every element of the Smith coset `[seamC ζ]` below by `12`. The case split is
the Prop 30 / Prop 31 dichotomy: a cell whose minima already reach `12` is done
by monotonicity; a `10`-tight cell is closed by the exact ρ-linked comp-2 cost,
or — when even that is `10` — by the exact comp-1 cost on the opposite block.
Knobs more than `1` above a block minimum are absorbed by the arithmetic. -/
theorem floor_of_killOK (ζ : BaseGroup → ZMod 2) (hz : bbBoundary2Fn baseA baseB ζ = 0)
    (T1 T3 T4 U2 U3 U4 O1R : Nat)
    (hT1 : ∀ (a b : Fin 4) (s : ZMod 2 × ZMod 2), pcP T1 a.val b.val (slotIdx s)
      = (fadd (seamOffL ζ psi1 s) (fadd (fmul a (Ahat1 s)) (fmul b (uv s)))).val)
    (hT3 : ∀ (a b : Fin 4) (s : ZMod 2 × ZMod 2), pcP T3 a.val b.val (slotIdx s)
      = (fadd (seamOffL ζ psi3 s) (fadd (fmul a (Ahat1 s)) (fmul b (uv s)))).val)
    (hT4 : ∀ (a b : Fin 4) (s : ZMod 2 × ZMod 2), pcP T4 a.val b.val (slotIdx s)
      = (fadd (seamOffL ζ psi4 s) (fadd (fmul a (Ahat4 s)) (fmul b (uv s)))).val)
    (hU2 : ∀ (a b : Fin 4) (s : ZMod 2 × ZMod 2), pcP U2 a.val b.val (slotIdx s)
      = (fadd (seamOffR ζ psi2 s) (fadd (fmul a (Bhat2 s)) (fmul b (uv s)))).val)
    (hU3 : ∀ (a b : Fin 4) (s : ZMod 2 × ZMod 2), pcP U3 a.val b.val (slotIdx s)
      = (fadd (seamOffR ζ psi3 s) (fadd (fmul a (Bhat2 s)) (fmul b (uv s)))).val)
    (hU4 : ∀ (a b : Fin 4) (s : ZMod 2 × ZMod 2), pcP U4 a.val b.val (slotIdx s)
      = (fadd (seamOffR ζ psi4 s) (fadd (fmul a (Bhat2 s)) (fmul b (uv s)))).val)
    (hO1R : ∀ s : ZMod 2 × ZMod 2, ovP O1R (slotIdx s) = (seamOffR ζ psi1 s).val)
    (hkill : killOK T1 T3 T4 U2 U3 U4 O1R = true)
    (f : BaseGroup → ZMod 2) :
    12 ≤ bb72Complex.chainWeight (seamC ζ + bbBoundary2Fn baseA baseB f) := by
  obtain ⟨w0, w1, w2, w3, a1, b1, b3L, a3, a4, b4, a2, b2, b3R, v1, v2,
    hw0, hw1, hw2, hw3, ha1, hb1, hb3L, ha3, ha4, hb4, ha2, hb2, hb3R, hv1, hv2,
    hic1, hic2, hcw⟩ := coset_ex ζ f hz T1 T3 T4 U2 U3 U4 O1R hT1 hT3 hT4 hU2 hU3 hU4 hO1R
  rw [hcw]
  set b4R := fmulP 2 b4 with hb4R
  set eL := exLP T1 T3 T4 w0 w1 w2 w3 a1 b1 b3L a3 a4 b4 v2 with heL
  set eR := exRP U2 U3 U4 O1R w0 w1 w2 w3 a2 b2 b3R a3 a4 b4R v1 with heR
  set mL := minLP T1 T3 T4 w0 w1 w2 w3 a3 a4 b4 with hmL
  set mR := minRP U2 U3 U4 w0 w1 w2 w3 a3 a4 b4R with hmR
  -- the actual knobs, as packed loop indices
  have hkL : a1 * 16 + b1 * 4 + b3L < 64 := by omega
  have hp : a2 * 4 + b2 < 16 := by omega
  have hkLd : (a1 * 16 + b1 * 4 + b3L) >>> 4 = a1 ∧ ((a1 * 16 + b1 * 4 + b3L) >>> 2) &&& 3 = b1
      ∧ (a1 * 16 + b1 * 4 + b3L) &&& 3 = b3L ∧ (a1 * 16 + b1 * 4 + b3L) >>> 2 = a1 * 4 + b1 := by
    interval_cases a1 <;> interval_cases b1 <;> interval_cases b3L <;> exact ⟨rfl, rfl, rfl, rfl⟩
  have hpd : (a2 * 4 + b2) >>> 2 = a2 ∧ (a2 * 4 + b2) &&& 3 = b2 := by
    interval_cases a2 <;> interval_cases b2 <;> exact ⟨rfl, rfl⟩
  -- the block bounds
  have hbL : blockLP T1 T3 T4 w0 w1 w2 w3 a1 b1 a3 b3L a4 b4 ≤ eL :=
    blockLP_le_exLP _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hbR : blockRP U2 U3 U4 w0 w1 w2 w3 a2 b2 a3 b3R a4 b4R ≤ eR :=
    blockRP_le_exRP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hmLle : mL ≤ blockLP T1 T3 T4 w0 w1 w2 w3 a1 b1 a3 b3L a4 b4 := by
    rw [hmL]
    have := foldl_min_le_range
      (fun k => blockLP T1 T3 T4 w0 w1 w2 w3 (k >>> 4) ((k >>> 2) &&& 3) a3 (k &&& 3) a4 b4)
      64 99 (a1 * 16 + b1 * 4 + b3L) hkL
    dsimp only at this
    rw [hkLd.1, hkLd.2.1, hkLd.2.2.1] at this
    exact this
  have hmR2le : mR2P U2 U3 U4 w0 w1 w2 w3 a2 b2 a3 a4 b4R
      ≤ blockRP U2 U3 U4 w0 w1 w2 w3 a2 b2 a3 b3R a4 b4R := by
    have := foldl_min_le_range
      (fun b3 => blockRP U2 U3 U4 w0 w1 w2 w3 a2 b2 a3 b3 a4 b4R) 4 99 b3R hb3R
    dsimp only at this
    exact this
  have hmRle : mR ≤ mR2P U2 U3 U4 w0 w1 w2 w3 a2 b2 a3 a4 b4R := by
    rw [hmR]
    have := foldl_min_le_range
      (fun p => mR2P U2 U3 U4 w0 w1 w2 w3 (p >>> 2) (p &&& 3) a3 a4 b4R) 16 99 (a2 * 4 + b2) hp
    dsimp only at this
    rw [hpd.1, hpd.2] at this
    exact this
  -- instantiate the certificate at this cell
  have hcell : killCell T1 T3 T4 U2 U3 U4 O1R w0 w1 w2 w3 a3 a4 b4 = true :=
    range_all_apply (range_all_apply (range_all_apply (range_all_apply
      (range_all_apply (range_all_apply (range_all_apply hkill hw0) hw1) hw2) hw3) ha3) ha4) hb4
  rw [killCell] at hcell
  simp only [← hb4R, ← hmL, ← hmR] at hcell
  rcases Bool.or_eq_true _ _ |>.mp hcell with h12 | hrest
  · have : 12 ≤ mL + mR := of_decide_eq_true h12
    omega
  · rw [Bool.and_eq_true] at hrest
    obtain ⟨h10, hkLoop⟩ := hrest
    have h10' : 10 ≤ mL + mR := of_decide_eq_true h10
    have hcL := range_all_apply hkLoop hkL
    rw [hkLd.1, hkLd.2.1, hkLd.2.2.1, hkLd.2.2.2] at hcL
    rcases Bool.or_eq_true _ _ |>.mp hcL with hskipL | hpLoop
    · have : mL + 1 < blockLP T1 T3 T4 w0 w1 w2 w3 a1 b1 a3 b3L a4 b4 := of_decide_eq_true hskipL
      omega
    · have hcP := range_all_apply hpLoop hp
      rw [hpd.1, hpd.2] at hcP
      rcases Bool.or_eq_true _ _ |>.mp hcP with hskipR | hv2Loop
      · have : mR + 1 < mR2P U2 U3 U4 w0 w1 w2 w3 a2 b2 a3 a4 b4R := of_decide_eq_true hskipR
        omega
      · have hcV2 := range_all_apply hv2Loop hv2
        rcases Bool.or_eq_true _ _ |>.mp hcV2 with hcV2' | hb3Loop
        · rcases Bool.or_eq_true _ _ |>.mp hcV2' with hne | hex
          · exact absurd hic2 (of_decide_eq_true hne)
          · have : 12 ≤ eL + mR := of_decide_eq_true hex
            omega
        · have hcB3 := range_all_apply hb3Loop hb3R
          rcases Bool.or_eq_true _ _ |>.mp hcB3 with hskipR2 | hv1Loop
          · have : mR + 1 < blockRP U2 U3 U4 w0 w1 w2 w3 a2 b2 a3 b3R a4 b4R :=
              of_decide_eq_true hskipR2
            omega
          · have hcV1 := range_all_apply hv1Loop hv1
            rcases Bool.or_eq_true _ _ |>.mp hcV1 with hne | hfin
            · exact absurd hic1 (of_decide_eq_true hne)
            · exact of_decide_eq_true hfin

end Quantum.Stabilizer.Homological.BB.LightStab
