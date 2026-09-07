/-
FORMERLY GENERATED — now HAND-MAINTAINED. Do NOT regenerate.
Originally emitted by qec-lab:experiments/bb_lab/scripts/gen_yrep_module.py (arg: 12),
then hand-evolved to the analytic Tier-3 form (PR #58: kernel-decide tables, no
floorOK `native_decide`). Rerunning the generator for arg 12 would revert that
work; the generator refuses args 11/12 without --force.
-/
/-
# Phase 6: the safe-sector floor for y-orbit representative 12 — ANALYTIC (Tier 3, M1)

Y-orbit rep 12 (`ker ∂₂` element `kcombo 1 1 0 1 1 0`) is a **weight-24** orbit:
its two CRT blocks **decouple**, each reaching the standard-form floor `6`
(`(min_R, min_L) = (6, 6)`), so the coset weight is `≥ 12` by
`costFromComps_ge_12_of_blocks` — **no `floorOK` / `2³⁰` `native_decide`** and no
`ρ`-link reduction.  See `MImFloorY11` for the structure; only the seam offsets
and the two `decide` tables differ.
-/
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.SafeFloor.WtFloor24Bridge

open Quantum.Stabilizer.Homological.BB
open Quantum.Stabilizer.Homological.BB.CRTFrame
open Quantum.Stabilizer.Homological.BB.LightStab

namespace Quantum.Stabilizer.Homological.BB.LightStab.Y12

set_option maxRecDepth 8192

/-- Y-orbit-12 representative `ker ∂₂` element. -/
def zrep : BaseGroup → ZMod 2 := kcombo 1 1 0 1 1 0

/-! ### Seam offsets, read off concretely (kernel `decide` through the packed mask).
A-block (`seamOffL`): comp1 `(1,1,1,1)`, comp3 `(0,2,0,2)`, comp4 `(2,2,2,2)`;
B-block (`seamOffR`): comp2 `(0,0,0,0)`, comp3 `(2,1,2,1)`, comp4 `(3,3,3,3)`.
Components 0,2 vanish (Lemma 17). -/

private theorem offs_eq :
    (∀ s, seamOffR zrep psi2 s = 0) ∧
    (∀ s, seamOffR zrep psi3 s
      = if s = (0,0) then 2 else if s = (1,0) then 1 else if s = (0,1) then 2 else 1) ∧
    (∀ s, seamOffR zrep psi4 s = 3) ∧ (∀ s, seamOffL zrep psi1 s = 1) ∧
    (∀ s, seamOffL zrep psi3 s
      = if s = (0,0) then 0 else if s = (1,0) then 2 else if s = (0,1) then 0 else 2) ∧
    (∀ s, seamOffL zrep psi4 s = 2) := by
  simp only [zrep, seamOffL_mask, seamOffR_mask]
  decide +kernel

theorem offR2_eq : seamOffR zrep psi2 = fun _ => 0 := funext offs_eq.1
theorem offR3_eq : seamOffR zrep psi3
    = fun s => if s = (0,0) then 2 else if s = (1,0) then 1 else if s = (0,1) then 2 else 1 :=
  funext offs_eq.2.1
theorem offR4_eq : seamOffR zrep psi4 = fun _ => 3 := funext offs_eq.2.2.1
theorem offL1_eq : seamOffL zrep psi1 = fun _ => 1 := funext offs_eq.2.2.2.1
theorem offL3_eq : seamOffL zrep psi3
    = fun s => if s = (0,0) then 0 else if s = (1,0) then 2 else if s = (0,1) then 0 else 2 :=
  funext offs_eq.2.2.2.2.1
theorem offL4_eq : seamOffL zrep psi4 = fun _ => 2 := funext offs_eq.2.2.2.2.2

/-! ### Per-block standard-form walks (kernel `decide`, `4⁶` knobs;
axiom-clean). -/

-- The 4⁶-knob walks stay kernel-checked (axiom-clean); `+kernel` and the
-- packed-`Nat` tables keep them cheap.
/-- B/right block `≥ 6`: comp2 `(0,0,0,0)`, comp3 `(2,1,2,1)`, comp4
`(3,3,3,3)`. -/
theorem Rdec : ∀ a2 b2 a3 b3 a4 b4 : Fin 4,
    6 ≤ slotCost (fadd 0 (fadd (fmul a2 3) (fmul b2 1)))
                 (fadd 2 (fadd (fmul a3 3) (fmul b3 1)))
                 (fadd 3 (fadd (fmul a4 3) (fmul b4 1)))
      + slotCost (fadd 0 (fadd (fmul a2 2) (fmul b2 1)))
                 (fadd 1 (fadd (fmul a3 2) (fmul b3 1)))
                 (fadd 3 (fadd (fmul a4 2) (fmul b4 1)))
      + slotCost (fadd 0 (fadd (fmul a2 1) (fmul b2 1)))
                 (fadd 2 (fadd (fmul a3 1) (fmul b3 1)))
                 (fadd 3 (fadd (fmul a4 1) (fmul b4 1)))
      + slotCost (fadd 0 (fadd (fmul a2 0) (fmul b2 1)))
                 (fadd 1 (fadd (fmul a3 0) (fmul b3 1)))
                 (fadd 3 (fadd (fmul a4 0) (fmul b4 1))) := by decide +kernel

-- Kernel `decide` (axiom-clean); see `Rdec`.
/-- A/left block `≥ 6`: comp1 `(1,1,1,1)`, comp3 `(0,2,0,2)`, comp4 `(2,2,2,2)`.
-/
theorem Ldec : ∀ a1 b1 a3 b3 a4 b4 : Fin 4,
    6 ≤ slotCostL (fadd 1 (fadd (fmul a1 3) (fmul b1 1)))
                  (fadd 0 (fadd (fmul a3 3) (fmul b3 1)))
                  (fadd 2 (fadd (fmul a4 2) (fmul b4 1)))
      + slotCostL (fadd 1 (fadd (fmul a1 1) (fmul b1 1)))
                  (fadd 2 (fadd (fmul a3 1) (fmul b3 1)))
                  (fadd 2 (fadd (fmul a4 1) (fmul b4 1)))
      + slotCostL (fadd 1 (fadd (fmul a1 2) (fmul b1 1)))
                  (fadd 0 (fadd (fmul a3 2) (fmul b3 1)))
                  (fadd 2 (fadd (fmul a4 3) (fmul b4 1)))
      + slotCostL (fadd 1 (fadd (fmul a1 0) (fmul b1 1)))
                  (fadd 2 (fadd (fmul a3 0) (fmul b3 1)))
                  (fadd 2 (fadd (fmul a4 0) (fmul b4 1))) := by decide +kernel

/-- B/right-block per-slot sum `≥ 6` for every coset (radical-ideal image ▸
`Rdec`). -/
theorem Rblock (f : BaseGroup → ZMod 2) :
    6 ≤ ∑ s, slotCost (shifted (seamOffR zrep psi2) Bhat2 (compF f psi2) s)
                      (shifted (seamOffR zrep psi3) Bhat2 (compF f psi3) s)
                      (shifted (seamOffR zrep psi4) Bhat2 (compF f psi4) s) := by
  obtain ⟨a2, b2, h2⟩ := inIdeal_to_exists Bhat2 _ (rmul_Bhat2_mem (compF f psi2))
  obtain ⟨a3, b3, h3⟩ := inIdeal_to_exists Bhat2 _ (rmul_Bhat2_mem (compF f psi3))
  obtain ⟨a4, b4, h4⟩ := inIdeal_to_exists Bhat2 _ (rmul_Bhat2_mem (compF f psi4))
  simp only [shifted, h2, h3, h4, offR2_eq, offR3_eq, offR4_eq]
  rw [sum_zmod2sq]
  exact Rdec a2 b2 a3 b3 a4 b4

/-- A/left-block per-slot sum `≥ 6` for every coset (radical-ideal image ▸
`Ldec`). -/
theorem Lblock (f : BaseGroup → ZMod 2) :
    6 ≤ ∑ s, slotCostL (shifted (seamOffL zrep psi1) Ahat1 (compF f psi1) s)
                       (shifted (seamOffL zrep psi3) Ahat1 (compF f psi3) s)
                       (shifted (seamOffL zrep psi4) Ahat4 (compF f psi4) s) := by
  obtain ⟨a1, b1, h1⟩ := inIdeal_to_exists Ahat1 _ (rmul_Ahat1_mem (compF f psi1))
  obtain ⟨a3, b3, h3⟩ := inIdeal_to_exists Ahat1 _ (rmul_Ahat1_mem (compF f psi3))
  obtain ⟨a4, b4, h4⟩ := inIdeal_to_exists Ahat4 _ (rmul_Ahat4_mem (compF f psi4))
  simp only [shifted, h1, h3, h4, offL1_eq, offL3_eq, offL4_eq]
  rw [sum_zmod2sq]
  exact Ldec a1 b1 a3 b3 a4 b4

/-- **Y-orbit-12 safe-sector floor** (analytic): every base 1-cycle in
`[seamC zrep]` has weight `≥ 12`. Discharged by the slot-frame walk — no
`floorOK`. -/
theorem floor (f : BaseGroup → ZMod 2) :
    12 ≤ bb72Complex.chainWeight (seamC zrep + bbBoundary2Fn baseA baseB f) :=
  floor_of_data_analytic zrep
    (fun f => costFromComps_ge_12_of_blocks zrep f (Lblock f) (Rblock f)) f

end Quantum.Stabilizer.Homological.BB.LightStab.Y12
