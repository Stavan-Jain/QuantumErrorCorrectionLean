/-
# The Z-distance floor: light `ker H_X` chains are `H_Z` rows

Chain plumbing for the `ker H_X` side of the `[[150,30,10]]` mitten
distance (triple instances X0/X1, verified in-build by
`FloorSweepX.lean`).  A dual cycle `c` (`dualBoundary c = 0`) of chain
weight ≤ 9 splits into the two triples `(c₀, c₂, c₄)` and `(c₁, c₃, c₄)`
solving `L(a₀)u + L(a₁)w = R(b_β)t`; each classifies into the census
list by the split sweeps, the `t`-join lands the packed pair on a row of
`H_Z`, and the row chain is a dual boundary (`cutMap` of a Z-check
singleton).  Hence

  `floorZ : dualBoundary c = 0 → chainWeight c ≤ 9 → c ∈ dualBoundaries`.

Everything decidable is either a 30-case kernel `decide` against the
generated tables (`FloorData.lean`) or one of two batched
`native_decide` leaves (basis-image bridge, census/row facts).  Design +
offline validation:
`qec-lab:pipeline/attempts/mitten_150_30_10/m4_findings.md`,
`scripts/a32_m4_bridge_check.py`.
-/

import QEC.Stabilizer.Codes.Mitten.M150.FloorBridge
import QEC.Stabilizer.Codes.Mitten.M150.FloorSweepX

namespace Quantum
namespace Stabilizer
namespace Homological
namespace LP
namespace M150

open scoped BigOperators

/-! ## §1  Row chains and the packed 150-bit layout -/

/-- Row `k` of `H_Z` as a 1-chain (`k < 60`, canonical check order). -/
def rowChainX (k : Nat) : Fin 5 × M150G → ZMod 2 :=
  fun q => cmTerm (checkOf k) q

/-- The X-side join packing of a 1-chain: blocks `(0,2,4 | 1,3,4)`. -/
def packX (c : Fin 5 × M150G → ZMod 2) : Nat :=
  pack5
    (packTriple (maskOf (blockOf c 0)) (maskOf (blockOf c 2))
      (maskOf (blockOf c 4)))
    (packTriple (maskOf (blockOf c 1)) (maskOf (blockOf c 3))
      (maskOf (blockOf c 4)))

/-! ## §2  The two `native_decide` leaves -/

set_option maxRecDepth 65536 in
/-- Basis images of the five block maps of both X-check rows match the
generated tables (`0` = the empty-table blocks). -/
private lemma bridgeX : ∀ i < 30,
    maskOf (blockMapped d2term 0 0 (deltaFn i)) = tRawAX.getD i 0
    ∧ maskOf (blockMapped d2term 0 1 (deltaFn i)) = 0
    ∧ maskOf (blockMapped d2term 0 2 (deltaFn i)) = tWCX0.getD i 0
    ∧ maskOf (blockMapped d2term 0 3 (deltaFn i)) = 0
    ∧ maskOf (blockMapped d2term 0 4 (deltaFn i)) = tTCX0.getD i 0
    ∧ maskOf (blockMapped d2term 1 0 (deltaFn i)) = 0
    ∧ maskOf (blockMapped d2term 1 1 (deltaFn i)) = tRawAX.getD i 0
    ∧ maskOf (blockMapped d2term 1 2 (deltaFn i)) = 0
    ∧ maskOf (blockMapped d2term 1 3 (deltaFn i)) = tWCX1.getD i 0
    ∧ maskOf (blockMapped d2term 1 4 (deltaFn i)) = tTCX1.getD i 0 := by
  native_decide

set_option maxRecDepth 65536 in
/-- Census/row facts: no classified triple has `t = 0`, and every listed
join row is the packing of an actual `H_Z` row chain. -/
private lemma clsX_facts :
    (∀ pk ∈ clsX0, pk >>> 60 ≠ 0) ∧ (∀ pk ∈ clsX1, pk >>> 60 ≠ 0)
    ∧ (∀ pk ∈ rowsXpk, ∃ k, k < 60 ∧ packX (rowChainX k) = pk) := by
  native_decide

/-! ## §3  Kernel decides against the generated tables -/

private lemma getD_nil (i : Nat) : ([] : List Nat).getD i 0 = 0 := by
  simp

private lemma dCinvC_X0 : ∀ i < 30,
    xorFold tCinvX0 (tTCX0.getD i 0) = 1 <<< i := by decide
private lemma dCinvA_X0 : ∀ i < 30,
    xorFold tCinvX0 (tRawAX.getD i 0) = tUTX0.getD i 0 := by decide
private lemma dCinvB_X0 : ∀ i < 30,
    xorFold tCinvX0 (tWCX0.getD i 0) = tWTX0.getD i 0 := by decide
private lemma dTWWT_X0 : ∀ i < 30,
    xorFold tTWX0 (tWTX0.getD i 0) = 1 <<< i := by decide
private lemma dTWUT_X0 : ∀ i < 30,
    xorFold tTWX0 (tUTX0.getD i 0) = tUWX0.getD i 0 := by decide
private lemma dCorr_X0 : ∀ i < 30,
    (1 <<< i ^^^ xorFold tPX0 (tRawAX.getD i 0)) ∈ annX0 := by decide
private lemma dAnn_X0 : (0 : Nat) ∈ annX0
    ∧ ∀ a ∈ annX0, ∀ b ∈ annX0, a ^^^ b ∈ annX0 := by decide
private lemma dLn0_X0 : ∀ i < 30,
    popCntGo 30 (m4TX0.ln0 &&& tRawAX.getD i 0) % 2 = 0 := by decide
private lemma dLn1_X0 : ∀ i < 30,
    popCntGo 30 (m4TX0.ln1 &&& tRawAX.getD i 0) % 2 = 0 := by decide
private lemma dBndB_X0 : ∀ x ∈ tWCX0, x < 2 ^ 30 := by decide
private lemma dBndC_X0 : ∀ x ∈ tTCX0, x < 2 ^ 30 := by decide

private lemma dCinvC_X1 : ∀ i < 30,
    xorFold tCinvX1 (tTCX1.getD i 0) = 1 <<< i := by decide
private lemma dCinvA_X1 : ∀ i < 30,
    xorFold tCinvX1 (tRawAX.getD i 0) = tUTX1.getD i 0 := by decide
private lemma dCinvB_X1 : ∀ i < 30,
    xorFold tCinvX1 (tWCX1.getD i 0) = tWTX1.getD i 0 := by decide
private lemma dTWWT_X1 : ∀ i < 30,
    xorFold tTWX1 (tWTX1.getD i 0) = 1 <<< i := by decide
private lemma dTWUT_X1 : ∀ i < 30,
    xorFold tTWX1 (tUTX1.getD i 0) = tUWX1.getD i 0 := by decide
private lemma dCorr_X1 : ∀ i < 30,
    (1 <<< i ^^^ xorFold tPX1 (tRawAX.getD i 0)) ∈ annX1 := by decide
private lemma dAnn_X1 : (0 : Nat) ∈ annX1
    ∧ ∀ a ∈ annX1, ∀ b ∈ annX1, a ^^^ b ∈ annX1 := by decide
private lemma dLn0_X1 : ∀ i < 30,
    popCntGo 30 (m4TX1.ln0 &&& tRawAX.getD i 0) % 2 = 0 := by decide
private lemma dLn1_X1 : ∀ i < 30,
    popCntGo 30 (m4TX1.ln1 &&& tRawAX.getD i 0) % 2 = 0 := by decide
private lemma dBndB_X1 : ∀ x ∈ tWCX1, x < 2 ^ 30 := by decide
private lemma dBndC_X1 : ∀ x ∈ tTCX1, x < 2 ^ 30 := by decide

private lemma dOddA_X : ∀ i < 30,
    popCntGo 30 (tRawAX.getD i 0) % 2 = 1 := by decide
private lemma dOddB_X0 : ∀ i < 30,
    popCntGo 30 (tWCX0.getD i 0) % 2 = 1 := by decide
private lemma dOddC_X0 : ∀ i < 30,
    popCntGo 30 (tTCX0.getD i 0) % 2 = 1 := by decide
private lemma dOddB_X1 : ∀ i < 30,
    popCntGo 30 (tWCX1.getD i 0) % 2 = 1 := by decide
private lemma dOddC_X1 : ∀ i < 30,
    popCntGo 30 (tTCX1.getD i 0) % 2 = 1 := by decide

private lemma covX0 : ∀ p < 9, ∀ q < 9, ∀ r < 9,
    p + q + r ≤ 8 → (p + q + r) % 2 = 0 →
    (splitsX0.contains (p, q, r, 0) || splitsX0.contains (p, q, r, 1)
      || splitsX0.contains (p, q, r, 2)) = true := by decide
private lemma covX1 : ∀ p < 9, ∀ q < 9, ∀ r < 9,
    p + q + r ≤ 8 → (p + q + r) % 2 = 0 →
    (splitsX1.contains (p, q, r, 0) || splitsX1.contains (p, q, r, 1)
      || splitsX1.contains (p, q, r, 2)) = true := by decide

/-! ## §4  XOR bookkeeping -/

private lemma xor_eq_zero' {a b : Nat} (h : a ^^^ b = 0) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hb := congrArg (fun x => x.testBit i) h
  simp only [Nat.testBit_xor, Nat.zero_testBit] at hb
  cases ha : a.testBit i <;> cases hb' : b.testBit i <;> simp_all

private lemma xor3_solve_a {a b c : Nat} (h : a ^^^ (b ^^^ c) = 0) :
    a = b ^^^ c :=
  xor_eq_zero' h

private lemma xor3_solve_c {a b c : Nat} (h : a ^^^ (b ^^^ c) = 0) :
    c = a ^^^ b := by
  rw [xor3_solve_a h, Nat.xor_comm b c, Nat.xor_assoc, Nat.xor_self,
    Nat.xor_zero]

/-! ## §5  Equation transfer -/

/-- Mask form of the X0 triple equation for a dual cycle. -/
private lemma eqX0 {c : Fin 5 × M150G → ZMod 2}
    (h : ∀ p : Fin 2 × M150G, dualBfn c p = 0) :
    xorFold tRawAX (maskOf (blockOf c 0))
      ^^^ (xorFold tWCX0 (maskOf (blockOf c 2))
      ^^^ xorFold tTCX0 (maskOf (blockOf c 4))) = 0 := by
  have h0 : maskOf (fun y => entrySum d2term c (0, y)) = 0 := by
    have hfn : (fun y => entrySum d2term c ((0 : Fin 2), y))
        = (0 : M150G → ZMod 2) := by
      funext y
      rw [← dualBfn_eq_entrySum]
      exact h (0, y)
    rw [hfn, maskOf_zero]
  rw [maskOf_entrySum_blocks] at h0
  rw [maskOf_op (blockMapped_add d2term 0 0) (fun i hi => (bridgeX i hi).1),
    maskOf_op (blockMapped_add d2term 0 1)
      (fun i hi => by rw [(bridgeX i hi).2.1, getD_nil]),
    maskOf_op (blockMapped_add d2term 0 2)
      (fun i hi => (bridgeX i hi).2.2.1),
    maskOf_op (blockMapped_add d2term 0 3)
      (fun i hi => by rw [(bridgeX i hi).2.2.2.1, getD_nil]),
    maskOf_op (blockMapped_add d2term 0 4)
      (fun i hi => (bridgeX i hi).2.2.2.2.1)] at h0
  simpa [xorFold_nil] using h0

/-- Mask form of the X1 triple equation for a dual cycle. -/
private lemma eqX1 {c : Fin 5 × M150G → ZMod 2}
    (h : ∀ p : Fin 2 × M150G, dualBfn c p = 0) :
    xorFold tRawAX (maskOf (blockOf c 1))
      ^^^ (xorFold tWCX1 (maskOf (blockOf c 3))
      ^^^ xorFold tTCX1 (maskOf (blockOf c 4))) = 0 := by
  have h0 : maskOf (fun y => entrySum d2term c (1, y)) = 0 := by
    have hfn : (fun y => entrySum d2term c ((1 : Fin 2), y))
        = (0 : M150G → ZMod 2) := by
      funext y
      rw [← dualBfn_eq_entrySum]
      exact h (1, y)
    rw [hfn, maskOf_zero]
  rw [maskOf_entrySum_blocks] at h0
  rw [maskOf_op (blockMapped_add d2term 1 0)
      (fun i hi => by rw [(bridgeX i hi).2.2.2.2.2.1, getD_nil]),
    maskOf_op (blockMapped_add d2term 1 1)
      (fun i hi => (bridgeX i hi).2.2.2.2.2.2.1),
    maskOf_op (blockMapped_add d2term 1 2)
      (fun i hi => by rw [(bridgeX i hi).2.2.2.2.2.2.2.1, getD_nil]),
    maskOf_op (blockMapped_add d2term 1 3)
      (fun i hi => (bridgeX i hi).2.2.2.2.2.2.2.2.1),
    maskOf_op (blockMapped_add d2term 1 4)
      (fun i hi => (bridgeX i hi).2.2.2.2.2.2.2.2.2)] at h0
  simpa [xorFold_nil] using h0

/-! ## §6  Classification of the two triples -/

/-- Every ≤9-light X0 triple of a dual cycle classifies. -/
private lemma classifyX0 {c : Fin 5 × M150G → ZMod 2}
    (h : ∀ p : Fin 2 × M150G, dualBfn c p = 0)
    (hw : popCntGo 30 (maskOf (blockOf c 0))
      + popCntGo 30 (maskOf (blockOf c 2))
      + popCntGo 30 (maskOf (blockOf c 4)) ≤ 9) :
    okTriple clsX0 (maskOf (blockOf c 0)) (maskOf (blockOf c 2))
      (maskOf (blockOf c 4)) = true := by
  set mu := maskOf (blockOf c 0) with hmu
  set mw := maskOf (blockOf c 2) with hmw
  set mt := maskOf (blockOf c 4) with hmt
  have hbu : mu < 2 ^ 30 := maskOf_lt _
  have hbw : mw < 2 ^ 30 := maskOf_lt _
  have hbt : mt < 2 ^ 30 := maskOf_lt _
  have hEq : xorFold tRawAX mu ^^^ (xorFold tWCX0 mw ^^^ xorFold tTCX0 mt)
      = 0 := eqX0 h
  -- parity: the triple weight is even
  have heven : (popCntGo 30 mu + popCntGo 30 mw + popCntGo 30 mt) % 2 = 0 := by
    have h0 : popCntGo 30 (xorFold tRawAX mu
        ^^^ (xorFold tWCX0 mw ^^^ xorFold tTCX0 mt)) % 2 = 0 := by
      rw [hEq, popCntGo_zero]
    have h1 := popCntGo_xor_mod2 30 (xorFold tRawAX mu)
      (xorFold tWCX0 mw ^^^ xorFold tTCX0 mt)
    have h2 := popCntGo_xor_mod2 30 (xorFold tWCX0 mw) (xorFold tTCX0 mt)
    have hA := parity_xorFold_odd dOddA_X mu hbu
    have hB := parity_xorFold_odd dOddB_X0 mw hbw
    have hC := parity_xorFold_odd dOddC_X0 mt hbt
    omega
  -- the split is covered
  have hcov := covX0 (popCntGo 30 mu) (by omega) (popCntGo 30 mw) (by omega)
    (popCntGo 30 mt) (by omega) (by omega) heven
  have hcases : (popCntGo 30 mu, popCntGo 30 mw, popCntGo 30 mt, 0) ∈ splitsX0
      ∨ (popCntGo 30 mu, popCntGo 30 mw, popCntGo 30 mt, 1) ∈ splitsX0
      ∨ (popCntGo 30 mu, popCntGo 30 mw, popCntGo 30 mt, 2) ∈ splitsX0 := by
    rcases Bool.or_eq_true_iff.mp hcov with h' | h2
    · rcases Bool.or_eq_true_iff.mp h' with h0 | h1
      · exact Or.inl (by simpa using h0)
      · exact Or.inr (Or.inl (by simpa using h1))
    · exact Or.inr (Or.inr (by simpa using h2))
  rcases hcases with hmem | hmem | hmem
  · -- mode 0: w derived
    have hchk : checkSplit m4TX0
        (popCntGo 30 mu, popCntGo 30 mw, popCntGo 30 mt, 0) = true :=
      List.all_eq_true.mp checkAll_X0 _ hmem
    -- mode-1 derived form first, then invert to the w-form
    have hder1 : mt = xorFold tUTX0 mu ^^^ xorFold tWTX0 mw := by
      have hC : xorFold tTCX0 mt = xorFold tRawAX mu ^^^ xorFold tWCX0 mw :=
        xor3_solve_c hEq
      have hstep := congrArg (xorFold tCinvX0) hC
      rw [xorFold_xor, xorFold_comp_id dCinvC_X0 mt hbt,
        xorFold_comp dCinvA_X0 mu hbu, xorFold_comp dCinvB_X0 mw hbw] at hstep
      exact hstep
    have hder0 : mw = xorFold tUWX0 mu ^^^ xorFold tTWX0 mt := by
      have h1 : xorFold tWTX0 mw = xorFold tUTX0 mu ^^^ mt := by
        rw [hder1, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      have hstep := congrArg (xorFold tTWX0) h1
      rw [xorFold_xor, xorFold_comp_id dTWWT_X0 mw hbw,
        xorFold_comp dTWUT_X0 mu hbu] at hstep
      exact hstep
    exact checkSplit_sound_ut hchk hbu hbt rfl rfl hbw hder0 rfl
  · -- mode 1: t derived
    have hchk : checkSplit m4TX0
        (popCntGo 30 mu, popCntGo 30 mw, popCntGo 30 mt, 1) = true :=
      List.all_eq_true.mp checkAll_X0 _ hmem
    have hder1 : mt = xorFold tUTX0 mu ^^^ xorFold tWTX0 mw := by
      have hC : xorFold tTCX0 mt = xorFold tRawAX mu ^^^ xorFold tWCX0 mw :=
        xor3_solve_c hEq
      have hstep := congrArg (xorFold tCinvX0) hC
      rw [xorFold_xor, xorFold_comp_id dCinvC_X0 mt hbt,
        xorFold_comp dCinvA_X0 mu hbu, xorFold_comp dCinvB_X0 mw hbw] at hstep
      exact hstep
    exact checkSplit_sound_uw hchk hbu hbw rfl rfl hbt hder1 rfl
  · -- mode 2: u in the Ann coset
    have hchk : checkSplit m4TX0
        (popCntGo 30 mu, popCntGo 30 mw, popCntGo 30 mt, 2) = true :=
      List.all_eq_true.mp checkAll_X0 _ hmem
    have hc' : xorFold tWCX0 mw ^^^ xorFold tTCX0 mt = xorFold tRawAX mu :=
      (xor3_solve_a hEq).symm
    have ha : (mu ^^^ xorFold tPX0 (xorFold tWCX0 mw ^^^ xorFold tTCX0 mt))
        ∈ annX0 := by
      rw [hc']
      have hFx : ∀ m₁ m₂ : Nat,
          (m₁ ^^^ m₂) ^^^ xorFold tPX0 (xorFold tRawAX (m₁ ^^^ m₂))
            = (m₁ ^^^ xorFold tPX0 (xorFold tRawAX m₁))
              ^^^ (m₂ ^^^ xorFold tPX0 (xorFold tRawAX m₂)) := by
        intro m₁ m₂
        rw [xorFold_xor, xorFold_xor, xor_xor_pair]
      have hP0 : ((0 : Nat) ^^^ xorFold tPX0 (xorFold tRawAX 0)) ∈ annX0 := by
        simpa using dAnn_X0.1
      have hbit : ∀ i < 30,
          ((1 <<< i) ^^^ xorFold tPX0 (xorFold tRawAX (1 <<< i))) ∈ annX0 := by
        intro i hi
        rw [xorFold_bit]
        exact dCorr_X0 i hi
      exact linear_pred
        (F := fun m => m ^^^ xorFold tPX0 (xorFold tRawAX m))
        (P := (· ∈ annX0)) 30 hFx hP0
        (fun a b ha hb => dAnn_X0.2 a ha b hb) hbit mu hbu
    have heq : mu = xorFold tPX0 (xorFold tWCX0 mw ^^^ xorFold tTCX0 mt)
        ^^^ (mu ^^^ xorFold tPX0 (xorFold tWCX0 mw ^^^ xorFold tTCX0 mt)) := by
      rw [← Nat.xor_assoc, Nat.xor_comm _ mu, Nat.xor_assoc, Nat.xor_self,
        Nat.xor_zero]
    have hln0 : popCntGo 30
        (m4TX0.ln0 &&& (xorFold tWCX0 mw ^^^ xorFold tTCX0 mt)) % 2 = 0 := by
      rw [hc']
      exact parity_and_xorFold dLn0_X0 mu hbu
    have hln1 : popCntGo 30
        (m4TX0.ln1 &&& (xorFold tWCX0 mw ^^^ xorFold tTCX0 mt)) % 2 = 0 := by
      rw [hc']
      exact parity_and_xorFold dLn1_X0 mu hbu
    exact checkSplit_sound_wt hchk hbw hbt rfl rfl hbu rfl ⟨_, ha, heq⟩
      (Nat.xor_lt_two_pow (xorFold_lt _ dBndB_X0 mw) (xorFold_lt _ dBndC_X0 mt))
      hln0 hln1

/-- Every ≤9-light X1 triple of a dual cycle classifies. -/
private lemma classifyX1 {c : Fin 5 × M150G → ZMod 2}
    (h : ∀ p : Fin 2 × M150G, dualBfn c p = 0)
    (hw : popCntGo 30 (maskOf (blockOf c 1))
      + popCntGo 30 (maskOf (blockOf c 3))
      + popCntGo 30 (maskOf (blockOf c 4)) ≤ 9) :
    okTriple clsX1 (maskOf (blockOf c 1)) (maskOf (blockOf c 3))
      (maskOf (blockOf c 4)) = true := by
  set mu := maskOf (blockOf c 1) with hmu
  set mw := maskOf (blockOf c 3) with hmw
  set mt := maskOf (blockOf c 4) with hmt
  have hbu : mu < 2 ^ 30 := maskOf_lt _
  have hbw : mw < 2 ^ 30 := maskOf_lt _
  have hbt : mt < 2 ^ 30 := maskOf_lt _
  have hEq : xorFold tRawAX mu ^^^ (xorFold tWCX1 mw ^^^ xorFold tTCX1 mt)
      = 0 := eqX1 h
  have heven : (popCntGo 30 mu + popCntGo 30 mw + popCntGo 30 mt) % 2 = 0 := by
    have h0 : popCntGo 30 (xorFold tRawAX mu
        ^^^ (xorFold tWCX1 mw ^^^ xorFold tTCX1 mt)) % 2 = 0 := by
      rw [hEq, popCntGo_zero]
    have h1 := popCntGo_xor_mod2 30 (xorFold tRawAX mu)
      (xorFold tWCX1 mw ^^^ xorFold tTCX1 mt)
    have h2 := popCntGo_xor_mod2 30 (xorFold tWCX1 mw) (xorFold tTCX1 mt)
    have hA := parity_xorFold_odd dOddA_X mu hbu
    have hB := parity_xorFold_odd dOddB_X1 mw hbw
    have hC := parity_xorFold_odd dOddC_X1 mt hbt
    omega
  have hcov := covX1 (popCntGo 30 mu) (by omega) (popCntGo 30 mw) (by omega)
    (popCntGo 30 mt) (by omega) (by omega) heven
  have hcases : (popCntGo 30 mu, popCntGo 30 mw, popCntGo 30 mt, 0) ∈ splitsX1
      ∨ (popCntGo 30 mu, popCntGo 30 mw, popCntGo 30 mt, 1) ∈ splitsX1
      ∨ (popCntGo 30 mu, popCntGo 30 mw, popCntGo 30 mt, 2) ∈ splitsX1 := by
    rcases Bool.or_eq_true_iff.mp hcov with h' | h2
    · rcases Bool.or_eq_true_iff.mp h' with h0 | h1
      · exact Or.inl (by simpa using h0)
      · exact Or.inr (Or.inl (by simpa using h1))
    · exact Or.inr (Or.inr (by simpa using h2))
  rcases hcases with hmem | hmem | hmem
  · have hchk : checkSplit m4TX1
        (popCntGo 30 mu, popCntGo 30 mw, popCntGo 30 mt, 0) = true :=
      List.all_eq_true.mp checkAll_X1 _ hmem
    have hder1 : mt = xorFold tUTX1 mu ^^^ xorFold tWTX1 mw := by
      have hC : xorFold tTCX1 mt = xorFold tRawAX mu ^^^ xorFold tWCX1 mw :=
        xor3_solve_c hEq
      have hstep := congrArg (xorFold tCinvX1) hC
      rw [xorFold_xor, xorFold_comp_id dCinvC_X1 mt hbt,
        xorFold_comp dCinvA_X1 mu hbu, xorFold_comp dCinvB_X1 mw hbw] at hstep
      exact hstep
    have hder0 : mw = xorFold tUWX1 mu ^^^ xorFold tTWX1 mt := by
      have h1 : xorFold tWTX1 mw = xorFold tUTX1 mu ^^^ mt := by
        rw [hder1, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      have hstep := congrArg (xorFold tTWX1) h1
      rw [xorFold_xor, xorFold_comp_id dTWWT_X1 mw hbw,
        xorFold_comp dTWUT_X1 mu hbu] at hstep
      exact hstep
    exact checkSplit_sound_ut hchk hbu hbt rfl rfl hbw hder0 rfl
  · have hchk : checkSplit m4TX1
        (popCntGo 30 mu, popCntGo 30 mw, popCntGo 30 mt, 1) = true :=
      List.all_eq_true.mp checkAll_X1 _ hmem
    have hder1 : mt = xorFold tUTX1 mu ^^^ xorFold tWTX1 mw := by
      have hC : xorFold tTCX1 mt = xorFold tRawAX mu ^^^ xorFold tWCX1 mw :=
        xor3_solve_c hEq
      have hstep := congrArg (xorFold tCinvX1) hC
      rw [xorFold_xor, xorFold_comp_id dCinvC_X1 mt hbt,
        xorFold_comp dCinvA_X1 mu hbu, xorFold_comp dCinvB_X1 mw hbw] at hstep
      exact hstep
    exact checkSplit_sound_uw hchk hbu hbw rfl rfl hbt hder1 rfl
  · have hchk : checkSplit m4TX1
        (popCntGo 30 mu, popCntGo 30 mw, popCntGo 30 mt, 2) = true :=
      List.all_eq_true.mp checkAll_X1 _ hmem
    have hc' : xorFold tWCX1 mw ^^^ xorFold tTCX1 mt = xorFold tRawAX mu :=
      (xor3_solve_a hEq).symm
    have ha : (mu ^^^ xorFold tPX1 (xorFold tWCX1 mw ^^^ xorFold tTCX1 mt))
        ∈ annX1 := by
      rw [hc']
      have hFx : ∀ m₁ m₂ : Nat,
          (m₁ ^^^ m₂) ^^^ xorFold tPX1 (xorFold tRawAX (m₁ ^^^ m₂))
            = (m₁ ^^^ xorFold tPX1 (xorFold tRawAX m₁))
              ^^^ (m₂ ^^^ xorFold tPX1 (xorFold tRawAX m₂)) := by
        intro m₁ m₂
        rw [xorFold_xor, xorFold_xor, xor_xor_pair]
      have hP0 : ((0 : Nat) ^^^ xorFold tPX1 (xorFold tRawAX 0)) ∈ annX1 := by
        simpa using dAnn_X1.1
      have hbit : ∀ i < 30,
          ((1 <<< i) ^^^ xorFold tPX1 (xorFold tRawAX (1 <<< i))) ∈ annX1 := by
        intro i hi
        rw [xorFold_bit]
        exact dCorr_X1 i hi
      exact linear_pred
        (F := fun m => m ^^^ xorFold tPX1 (xorFold tRawAX m))
        (P := (· ∈ annX1)) 30 hFx hP0
        (fun a b ha hb => dAnn_X1.2 a ha b hb) hbit mu hbu
    have heq : mu = xorFold tPX1 (xorFold tWCX1 mw ^^^ xorFold tTCX1 mt)
        ^^^ (mu ^^^ xorFold tPX1 (xorFold tWCX1 mw ^^^ xorFold tTCX1 mt)) := by
      rw [← Nat.xor_assoc, Nat.xor_comm _ mu, Nat.xor_assoc, Nat.xor_self,
        Nat.xor_zero]
    have hln0 : popCntGo 30
        (m4TX1.ln0 &&& (xorFold tWCX1 mw ^^^ xorFold tTCX1 mt)) % 2 = 0 := by
      rw [hc']
      exact parity_and_xorFold dLn0_X1 mu hbu
    have hln1 : popCntGo 30
        (m4TX1.ln1 &&& (xorFold tWCX1 mw ^^^ xorFold tTCX1 mt)) % 2 = 0 := by
      rw [hc']
      exact parity_and_xorFold dLn1_X1 mu hbu
    exact checkSplit_sound_wt hchk hbw hbt rfl rfl hbu rfl ⟨_, ha, heq⟩
      (Nat.xor_lt_two_pow (xorFold_lt _ dBndB_X1 mw) (xorFold_lt _ dBndC_X1 mt))
      hln0 hln1

/-! ## §7  Row reconstruction -/

/-- Equal X-side packings force equal chains. -/
private lemma packX_inj {c d : Fin 5 × M150G → ZMod 2}
    (h : packX c = packX d) : c = d := by
  have e0 := congrArg (· % 2 ^ 30) h
  have e1 := congrArg (fun x => (x >>> 30) % 2 ^ 30) h
  have e2 := congrArg (fun x => (x >>> 60) % 2 ^ 30) h
  have e3 := congrArg (fun x => (x >>> 90) % 2 ^ 30) h
  have e4 := congrArg (fun x => x >>> 120) h
  simp only [packX, pack5_mod, pack5_shr30_mod, pack5_shr60_mod,
    pack5_shr90_mod, pack5_shr120] at e0 e1 e2 e3 e4
  rw [packTriple_lo _ _ (maskOf_lt _), packTriple_lo _ _ (maskOf_lt _)] at e0
  rw [packTriple_mid _ (maskOf_lt _) (maskOf_lt _),
    packTriple_mid _ (maskOf_lt _) (maskOf_lt _)] at e1
  rw [packTriple_lo _ _ (maskOf_lt _), packTriple_lo _ _ (maskOf_lt _)] at e2
  rw [packTriple_mid _ (maskOf_lt _) (maskOf_lt _),
    packTriple_mid _ (maskOf_lt _) (maskOf_lt _)] at e3
  rw [packTriple_hi _ (maskOf_lt _) (maskOf_lt _),
    packTriple_hi _ (maskOf_lt _) (maskOf_lt _)] at e4
  have b0 := maskOf_inj e0
  have b2 := maskOf_inj e1
  have b1 := maskOf_inj e2
  have b3 := maskOf_inj e3
  have b4 := maskOf_inj e4
  funext q
  obtain ⟨m, g⟩ := q
  fin_cases m
  · exact congrFun b0 g
  · exact congrFun b1 g
  · exact congrFun b2 g
  · exact congrFun b3 g
  · exact congrFun b4 g

/-- Each `H_Z` row chain is a dual boundary. -/
private lemma rowChainX_mem_dualBoundaries (k : Nat) :
    rowChainX k ∈ m150Complex.dualBoundaries := by
  have key : ∀ q : Fin 5 × M150G,
      (∑ p : Fin 2 × M150G,
        (if p = checkOf k then (1 : ZMod 2) else 0) * cmTerm p q)
        = cmTerm (checkOf k) q := by
    intro q
    rw [Finset.sum_eq_single (checkOf k)]
    · rw [if_pos rfl, one_mul]
    · intro p _ hne
      rw [if_neg hne, zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  have hsingle : ∀ p : Fin 2 × M150G,
      m150Complex.singleVtx (checkOf k) p
        = if p = checkOf k then (1 : ZMod 2) else 0 := by
    intro p
    simp only [HomologicalCode.singleVtx]
    rw [Pi.single_apply]
    rfl
  have hfun : m150Complex.cutMap (m150Complex.singleVtx (checkOf k))
      = rowChainX k := by
    funext q
    rw [cutMap_apply_eq_sum_cmTerm]
    calc (∑ p : m150Complex.C0, m150Complex.singleVtx (checkOf k) p * cmTerm p q)
        = ∑ p : Fin 2 × M150G,
            (if p = checkOf k then (1 : ZMod 2) else 0) * cmTerm p q :=
          Finset.sum_congr rfl fun p _ => by rw [hsingle p]
      _ = cmTerm (checkOf k) q := key q
      _ = rowChainX k q := rfl
  exact ⟨m150Complex.singleVtx (checkOf k), hfun⟩

/-! ## §8  The floor -/

/-- **Z-distance floor**: every dual cycle of chain weight ≤ 9 is a dual
boundary — i.e. `d_Z ≥ 10` for the `[[150,30,10]]` mitten code. -/
theorem floorZ (c : m150Complex.C1 → ZMod 2)
    (hker : m150Complex.dualBoundary c = 0)
    (hw : m150Complex.chainWeight c ≤ 9) :
    c ∈ m150Complex.dualBoundaries := by
  have hker' : ∀ p : Fin 2 × M150G, dualBfn c p = 0 := by
    intro p
    rw [← dualBoundary_eq_dualBfn, hker]
    rfl
  have hwsum : suppCard (blockOf c 0) + suppCard (blockOf c 1)
      + suppCard (blockOf c 2) + suppCard (blockOf c 3)
      + suppCard (blockOf c 4) ≤ 9 := by
    have h := chainWeight_eq_sum_suppCard c
    rw [Fin.sum_univ_five] at h
    omega
  have hp0 := popCntGo_maskOf (blockOf c 0)
  have hp1 := popCntGo_maskOf (blockOf c 1)
  have hp2 := popCntGo_maskOf (blockOf c 2)
  have hp3 := popCntGo_maskOf (blockOf c 3)
  have hp4 := popCntGo_maskOf (blockOf c 4)
  have hok0 := classifyX0 hker' (by omega)
  have hok1 := classifyX1 hker' (by omega)
  rcases okTriple_cases hok0 with ⟨hz0u, hz0w, hz0t⟩ | hmem0
  · rcases okTriple_cases hok1 with ⟨hz1u, hz1w, _⟩ | hmem1
    · -- both triples zero: c = 0
      have hb0 := eq_zero_of_maskOf_eq_zero hz0u
      have hb1 := eq_zero_of_maskOf_eq_zero hz1u
      have hb2 := eq_zero_of_maskOf_eq_zero hz0w
      have hb3 := eq_zero_of_maskOf_eq_zero hz1w
      have hb4 := eq_zero_of_maskOf_eq_zero hz0t
      have hc0 : c = 0 := by
        funext q
        obtain ⟨m, g⟩ := q
        fin_cases m
        · exact congrFun hb0 g
        · exact congrFun hb1 g
        · exact congrFun hb2 g
        · exact congrFun hb3 g
        · exact congrFun hb4 g
      rw [hc0]
      exact Submodule.zero_mem _
    · -- X0 zero, X1 listed: its t-part would be 0
      exfalso
      have ht := clsX_facts.2.1 _ hmem1
      rw [packTriple_hi _ (maskOf_lt _) (maskOf_lt _)] at ht
      exact ht hz0t
  · rcases okTriple_cases hok1 with ⟨_, _, hz1t⟩ | hmem1
    · exfalso
      have ht := clsX_facts.1 _ hmem0
      rw [packTriple_hi _ (maskOf_lt _) (maskOf_lt _)] at ht
      exact ht hz1t
    · -- both listed: join to a row
      have hjoin := checkJoin_sound checkJoin_X (maskOf_lt _) (maskOf_lt _)
        (maskOf_lt _) (maskOf_lt _) (maskOf_lt _) hmem0 hmem1 (by omega)
      obtain ⟨k, -, hkpack⟩ := clsX_facts.2.2 _ hjoin
      have hceq : c = rowChainX k := (packX_inj hkpack).symm
      rw [hceq]
      exact rowChainX_mem_dualBoundaries k
end M150
end LP
end Homological
end Stabilizer
end Quantum
