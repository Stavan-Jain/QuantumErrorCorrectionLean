/-
FORMERLY GENERATED — now HAND-MAINTAINED.  Do NOT regenerate.
Originally emitted by qec-lab:experiments/bb_lab/scripts/gen_yrep_module.py (arg: 0),
then hand-evolved to the analytic Tier-3 form (kernel-decide certificate, no
`floorOK` engine leaf).  Rerunning the generator for this arg would revert that work.
-/
/-
# Phase 6: the safe-sector floor for y-orbit representative 0 — ANALYTIC (Tier 3, M2/M3)

Y-orbit rep 0 (`ker ∂₂` element `kcombo 1 0 0 0 0 0`) is a **weight-16** orbit: its two
CRT blocks do **not** decouple (per-block minima below `6`), so the weight-24 route
does not apply.  The floor is closed instead by the coupled spine certificate of
`LightFloor`: Prop 30 (`min_L + min_R ≥ 10` on every one of the `1024` spine cells)
together with Prop 31 (the ρ-link kill of the `10`-tight cells), packaged as the
single `Bool` `killOK` and discharged by kernel `decide`.

No `native_decide`, and no `2³⁰` `floorOK` enumeration: the seam offsets are read
through the packed mask (`seamC_kcombo_mask`) and the whole floor is one kernel walk.
-/
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.SafeFloor.LightFloor

open Quantum.Stabilizer.Homological.BB
open Quantum.Stabilizer.Homological.BB.CRTFrame
open Quantum.Stabilizer.Homological.BB.LightStab

namespace Quantum.Stabilizer.Homological.BB.LightStab.Y0

set_option maxRecDepth 8192

/-- Y-orbit-0 representative `ker ∂₂` element. -/
def zrep : BaseGroup → ZMod 2 := kcombo 1 0 0 0 0 0

/-! ### The orbit's packed component tables (A-block `T`, B-block `U`, comp-1
offset). -/

def T1 : Nat := 0x1e4bb4e1396c93c627728dd80055aaff
def T3 : Nat := 0x96c33c69b1e41b4eaffa055088dd2277
def T4 : Nat := 0x3c6996c30a5fa0f527728dd81144bbee
def U2 : Nat := 0xc99c6336d287782de4b14e1bffaa5500
def U3 : Nat := 0xfaaf5005e1b44b1ed7827d28cc996633
def U4 : Nat := 0xebbe4114f0a55a0fc6936c39dd887722
def O1R : Nat := 0x33

/-! ### The tables are the orbit's seam-shifted components (kernel sweeps over the
`4² · 4` knob/slot tuples, with the seam offsets read through the packed mask).
-/

theorem hT1 : ∀ (a b : Fin 4) (s : ZMod 2 × ZMod 2), pcP T1 a.val b.val (slotIdx s)
    = (fadd (seamOffL zrep psi1 s) (fadd (fmul a (Ahat1 s)) (fmul b (uv s)))).val := by
  intro a b s
  rw [show zrep = kcombo 1 0 0 0 0 0 from rfl, seamOffL_mask]
  revert a b s
  decide +kernel

theorem hT3 : ∀ (a b : Fin 4) (s : ZMod 2 × ZMod 2), pcP T3 a.val b.val (slotIdx s)
    = (fadd (seamOffL zrep psi3 s) (fadd (fmul a (Ahat1 s)) (fmul b (uv s)))).val := by
  intro a b s
  rw [show zrep = kcombo 1 0 0 0 0 0 from rfl, seamOffL_mask]
  revert a b s
  decide +kernel

theorem hT4 : ∀ (a b : Fin 4) (s : ZMod 2 × ZMod 2), pcP T4 a.val b.val (slotIdx s)
    = (fadd (seamOffL zrep psi4 s) (fadd (fmul a (Ahat4 s)) (fmul b (uv s)))).val := by
  intro a b s
  rw [show zrep = kcombo 1 0 0 0 0 0 from rfl, seamOffL_mask]
  revert a b s
  decide +kernel

theorem hU2 : ∀ (a b : Fin 4) (s : ZMod 2 × ZMod 2), pcP U2 a.val b.val (slotIdx s)
    = (fadd (seamOffR zrep psi2 s) (fadd (fmul a (Bhat2 s)) (fmul b (uv s)))).val := by
  intro a b s
  rw [show zrep = kcombo 1 0 0 0 0 0 from rfl, seamOffR_mask]
  revert a b s
  decide +kernel

theorem hU3 : ∀ (a b : Fin 4) (s : ZMod 2 × ZMod 2), pcP U3 a.val b.val (slotIdx s)
    = (fadd (seamOffR zrep psi3 s) (fadd (fmul a (Bhat2 s)) (fmul b (uv s)))).val := by
  intro a b s
  rw [show zrep = kcombo 1 0 0 0 0 0 from rfl, seamOffR_mask]
  revert a b s
  decide +kernel

theorem hU4 : ∀ (a b : Fin 4) (s : ZMod 2 × ZMod 2), pcP U4 a.val b.val (slotIdx s)
    = (fadd (seamOffR zrep psi4 s) (fadd (fmul a (Bhat2 s)) (fmul b (uv s)))).val := by
  intro a b s
  rw [show zrep = kcombo 1 0 0 0 0 0 from rfl, seamOffR_mask]
  revert a b s
  decide +kernel

theorem hO1R : ∀ s : ZMod 2 × ZMod 2, ovP O1R (slotIdx s) = (seamOffR zrep psi1 s).val := by
  intro s
  rw [show zrep = kcombo 1 0 0 0 0 0 from rfl, seamOffR_mask]
  revert s
  decide +kernel

/-- The orbit lies in `ker ∂₂`. -/
theorem zrep_ker : bbBoundary2Fn baseA baseB zrep = 0 := bb2_kcombo _ _ _ _ _ _

/-- **The spine certificate** (Props 30-31 for this orbit): every one of the
`1024` spine cells either clears `12` outright or has its `10`-tight
configurations killed by a ρ-link. Kernel `decide` — no `native_decide`, no
`2³⁰` walk. -/
theorem kill_holds : killOK T1 T3 T4 U2 U3 U4 O1R = true := by decide +kernel

/-- **Y-orbit-0 safe-sector floor** (analytic): every base 1-cycle in
`[seamC zrep]` has weight `≥ 12`. -/
theorem floor (f : BaseGroup → ZMod 2) :
    12 ≤ bb72Complex.chainWeight (seamC zrep + bbBoundary2Fn baseA baseB f) :=
  floor_of_killOK zrep zrep_ker T1 T3 T4 U2 U3 U4 O1R hT1 hT3 hT4 hU2 hU3 hU4 hO1R
    kill_holds f

end Quantum.Stabilizer.Homological.BB.LightStab.Y0
