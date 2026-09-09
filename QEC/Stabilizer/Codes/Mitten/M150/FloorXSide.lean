/-
# The X-distance floor: light `ker H_Z` chains are `H_X` rows

Mirror of `FloorZSide.lean` for the `ker H_Z` side (triple instances
Z0/Z1, verified in-build by `FloorSweepZ.lean`).  A cycle `c`
(`∂₁ c = 0`) of chain weight ≤ 9 splits into the triples `(c₀, c₁, c₄)`
and `(c₂, c₃, c₄)` solving `u·R(b₀~) + w·R(b₁~) = L(a_α~)t`; the sweeps
classify them, the `t`-join lands on a row of `H_X`, and the row chain
is a boundary (`∂₂` of an X-check singleton).  Hence

  `floorX : ∂₁ c = 0 → chainWeight c ≤ 9 → c ∈ boundaries`.
-/

import QEC.Stabilizer.Codes.Mitten.M150.FloorBridge
import QEC.Stabilizer.Codes.Mitten.M150.FloorSweepZ

namespace Quantum
namespace Stabilizer
namespace Homological
namespace LP
namespace M150

open scoped BigOperators

/-! ## §1  Row chains and the packed 150-bit layout -/

/-- Row `k` of `H_X` as a 1-chain (`k < 60`, canonical check order). -/
def rowChainZ (k : Nat) : Fin 5 × M150G → ZMod 2 :=
  fun q => d2term (checkOf k) q

/-- The Z-side join packing of a 1-chain: blocks `(0,1,4 | 2,3,4)`. -/
def packZ (c : Fin 5 × M150G → ZMod 2) : Nat :=
  pack5
    (packTriple (maskOf (blockOf c 0)) (maskOf (blockOf c 1))
      (maskOf (blockOf c 4)))
    (packTriple (maskOf (blockOf c 2)) (maskOf (blockOf c 3))
      (maskOf (blockOf c 4)))

/-! ## §2  The two `native_decide` leaves -/

set_option maxRecDepth 65536 in
/-- Basis images of the five block maps of both Z-check rows match the
generated tables (`0` = the empty-table blocks). -/
private lemma bridgeZ : ∀ i < 30,
    maskOf (blockMapped cmTerm 0 0 (deltaFn i)) = tUCZ0.getD i 0
    ∧ maskOf (blockMapped cmTerm 0 1 (deltaFn i)) = tWC2Z0.getD i 0
    ∧ maskOf (blockMapped cmTerm 0 2 (deltaFn i)) = 0
    ∧ maskOf (blockMapped cmTerm 0 3 (deltaFn i)) = 0
    ∧ maskOf (blockMapped cmTerm 0 4 (deltaFn i)) = tRawCZ0.getD i 0
    ∧ maskOf (blockMapped cmTerm 1 0 (deltaFn i)) = 0
    ∧ maskOf (blockMapped cmTerm 1 1 (deltaFn i)) = 0
    ∧ maskOf (blockMapped cmTerm 1 2 (deltaFn i)) = tUCZ1.getD i 0
    ∧ maskOf (blockMapped cmTerm 1 3 (deltaFn i)) = tWC2Z1.getD i 0
    ∧ maskOf (blockMapped cmTerm 1 4 (deltaFn i)) = tRawCZ1.getD i 0 := by
  native_decide

set_option maxRecDepth 65536 in
/-- Census/row facts: no classified triple has `t = 0`, and every listed
join row is the packing of an actual `H_X` row chain. -/
private lemma clsZ_facts :
    (∀ pk ∈ clsZ0, pk >>> 60 ≠ 0) ∧ (∀ pk ∈ clsZ1, pk >>> 60 ≠ 0)
    ∧ (∀ pk ∈ rowsZpk, ∃ k, k < 60 ∧ packZ (rowChainZ k) = pk) := by
  native_decide

/-! ## §3  Kernel decides against the generated tables -/

private lemma getD_nil (i : Nat) : ([] : List Nat).getD i 0 = 0 := by
  simp

private lemma dAinvA_Z0 : ∀ i < 30,
    xorFold tAinvZ (tUCZ0.getD i 0) = 1 <<< i := by decide
private lemma dAinvB_Z0 : ∀ i < 30,
    xorFold tAinvZ (tWC2Z0.getD i 0) = tWCZ0.getD i 0 := by decide
private lemma dAinvC_Z0 : ∀ i < 30,
    xorFold tAinvZ (tRawCZ0.getD i 0) = tTCZ0.getD i 0 := by decide
private lemma dUWWC_Z0 : ∀ i < 30,
    xorFold tUWZ0 (tWCZ0.getD i 0) = 1 <<< i := by decide
private lemma dUWTC_Z0 : ∀ i < 30,
    xorFold tUWZ0 (tTCZ0.getD i 0) = tTWZ0.getD i 0 := by decide
private lemma dPid_Z0 : ∀ i < 30, tPZ0.getD i 0 = 1 <<< i := by decide
private lemma dCorrT_Z0 : ∀ i < 30,
    (1 <<< i ^^^ xorFold tPTZ0 (tRawCZ0.getD i 0)) ∈ annTZ0 := by decide
private lemma dAnnT_Z0 : (0 : Nat) ∈ annTZ0
    ∧ ∀ a ∈ annTZ0, ∀ b ∈ annTZ0, a ^^^ b ∈ annTZ0 := by decide
private lemma dAnn0_Z0 : (0 : Nat) ∈ annZ0 := by decide
private lemma dLnT0_Z0 : ∀ i < 30,
    popCntGo 30 (m4TZ0.lnT0 &&& tRawCZ0.getD i 0) % 2 = 0 := by decide
private lemma dLnT1_Z0 : ∀ i < 30,
    popCntGo 30 (m4TZ0.lnT1 &&& tRawCZ0.getD i 0) % 2 = 0 := by decide
private lemma dBndA_Z0 : ∀ x ∈ tUCZ0, x < 2 ^ 30 := by decide
private lemma dBndB_Z0 : ∀ x ∈ tWC2Z0, x < 2 ^ 30 := by decide
private lemma dBndWC_Z0 : ∀ x ∈ tWCZ0, x < 2 ^ 30 := by decide
private lemma dBndTC_Z0 : ∀ x ∈ tTCZ0, x < 2 ^ 30 := by decide

private lemma dAinvA_Z1 : ∀ i < 30,
    xorFold tAinvZ (tUCZ1.getD i 0) = 1 <<< i := by decide
private lemma dAinvB_Z1 : ∀ i < 30,
    xorFold tAinvZ (tWC2Z1.getD i 0) = tWCZ1.getD i 0 := by decide
private lemma dAinvC_Z1 : ∀ i < 30,
    xorFold tAinvZ (tRawCZ1.getD i 0) = tTCZ1.getD i 0 := by decide
private lemma dUWWC_Z1 : ∀ i < 30,
    xorFold tUWZ1 (tWCZ1.getD i 0) = 1 <<< i := by decide
private lemma dUWTC_Z1 : ∀ i < 30,
    xorFold tUWZ1 (tTCZ1.getD i 0) = tTWZ1.getD i 0 := by decide
private lemma dPid_Z1 : ∀ i < 30, tPZ1.getD i 0 = 1 <<< i := by decide
private lemma dCorrT_Z1 : ∀ i < 30,
    (1 <<< i ^^^ xorFold tPTZ1 (tRawCZ1.getD i 0)) ∈ annTZ1 := by decide
private lemma dAnnT_Z1 : (0 : Nat) ∈ annTZ1
    ∧ ∀ a ∈ annTZ1, ∀ b ∈ annTZ1, a ^^^ b ∈ annTZ1 := by decide
private lemma dAnn0_Z1 : (0 : Nat) ∈ annZ1 := by decide
private lemma dLnT0_Z1 : ∀ i < 30,
    popCntGo 30 (m4TZ1.lnT0 &&& tRawCZ1.getD i 0) % 2 = 0 := by decide
private lemma dLnT1_Z1 : ∀ i < 30,
    popCntGo 30 (m4TZ1.lnT1 &&& tRawCZ1.getD i 0) % 2 = 0 := by decide
private lemma dBndA_Z1 : ∀ x ∈ tUCZ1, x < 2 ^ 30 := by decide
private lemma dBndB_Z1 : ∀ x ∈ tWC2Z1, x < 2 ^ 30 := by decide
private lemma dBndWC_Z1 : ∀ x ∈ tWCZ1, x < 2 ^ 30 := by decide
private lemma dBndTC_Z1 : ∀ x ∈ tTCZ1, x < 2 ^ 30 := by decide

private lemma dOddA_Z0 : ∀ i < 30,
    popCntGo 30 (tUCZ0.getD i 0) % 2 = 1 := by decide
private lemma dOddB_Z0 : ∀ i < 30,
    popCntGo 30 (tWC2Z0.getD i 0) % 2 = 1 := by decide
private lemma dOddC_Z0 : ∀ i < 30,
    popCntGo 30 (tRawCZ0.getD i 0) % 2 = 1 := by decide
private lemma dOddA_Z1 : ∀ i < 30,
    popCntGo 30 (tUCZ1.getD i 0) % 2 = 1 := by decide
private lemma dOddB_Z1 : ∀ i < 30,
    popCntGo 30 (tWC2Z1.getD i 0) % 2 = 1 := by decide
private lemma dOddC_Z1 : ∀ i < 30,
    popCntGo 30 (tRawCZ1.getD i 0) % 2 = 1 := by decide

private lemma covZ0 : ∀ p < 9, ∀ q < 9, ∀ r < 9,
    p + q + r ≤ 8 → (p + q + r) % 2 = 0 →
    (splitsZ0.contains (p, q, r, 0) || splitsZ0.contains (p, q, r, 2)
      || splitsZ0.contains (p, q, r, 3)) = true := by decide
private lemma covZ1 : ∀ p < 9, ∀ q < 9, ∀ r < 9,
    p + q + r ≤ 8 → (p + q + r) % 2 = 0 →
    (splitsZ1.contains (p, q, r, 0) || splitsZ1.contains (p, q, r, 2)
      || splitsZ1.contains (p, q, r, 3)) = true := by decide

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

/-- Mask form of the Z0 triple equation for a cycle. -/
private lemma eqZ0 {c : Fin 5 × M150G → ZMod 2}
    (h : ∀ p : Fin 2 × M150G, entrySum cmTerm c p = 0) :
    xorFold tUCZ0 (maskOf (blockOf c 0))
      ^^^ (xorFold tWC2Z0 (maskOf (blockOf c 1))
      ^^^ xorFold tRawCZ0 (maskOf (blockOf c 4))) = 0 := by
  have h0 : maskOf (fun y => entrySum cmTerm c (0, y)) = 0 := by
    have hfn : (fun y => entrySum cmTerm c ((0 : Fin 2), y))
        = (0 : M150G → ZMod 2) := by
      funext y
      exact h (0, y)
    rw [hfn, maskOf_zero]
  rw [maskOf_entrySum_blocks] at h0
  rw [maskOf_op (blockMapped_add cmTerm 0 0) (fun i hi => (bridgeZ i hi).1),
    maskOf_op (blockMapped_add cmTerm 0 1) (fun i hi => (bridgeZ i hi).2.1),
    maskOf_op (blockMapped_add cmTerm 0 2)
      (fun i hi => by rw [(bridgeZ i hi).2.2.1, getD_nil]),
    maskOf_op (blockMapped_add cmTerm 0 3)
      (fun i hi => by rw [(bridgeZ i hi).2.2.2.1, getD_nil]),
    maskOf_op (blockMapped_add cmTerm 0 4)
      (fun i hi => (bridgeZ i hi).2.2.2.2.1)] at h0
  simpa [xorFold_nil] using h0

/-- Mask form of the Z1 triple equation for a cycle. -/
private lemma eqZ1 {c : Fin 5 × M150G → ZMod 2}
    (h : ∀ p : Fin 2 × M150G, entrySum cmTerm c p = 0) :
    xorFold tUCZ1 (maskOf (blockOf c 2))
      ^^^ (xorFold tWC2Z1 (maskOf (blockOf c 3))
      ^^^ xorFold tRawCZ1 (maskOf (blockOf c 4))) = 0 := by
  have h0 : maskOf (fun y => entrySum cmTerm c (1, y)) = 0 := by
    have hfn : (fun y => entrySum cmTerm c ((1 : Fin 2), y))
        = (0 : M150G → ZMod 2) := by
      funext y
      exact h (1, y)
    rw [hfn, maskOf_zero]
  rw [maskOf_entrySum_blocks] at h0
  rw [maskOf_op (blockMapped_add cmTerm 1 0)
      (fun i hi => by rw [(bridgeZ i hi).2.2.2.2.2.1, getD_nil]),
    maskOf_op (blockMapped_add cmTerm 1 1)
      (fun i hi => by rw [(bridgeZ i hi).2.2.2.2.2.2.1, getD_nil]),
    maskOf_op (blockMapped_add cmTerm 1 2)
      (fun i hi => (bridgeZ i hi).2.2.2.2.2.2.2.1),
    maskOf_op (blockMapped_add cmTerm 1 3)
      (fun i hi => (bridgeZ i hi).2.2.2.2.2.2.2.2.1),
    maskOf_op (blockMapped_add cmTerm 1 4)
      (fun i hi => (bridgeZ i hi).2.2.2.2.2.2.2.2.2)] at h0
  simpa [xorFold_nil] using h0

/-! ## §6  Classification of the two triples -/

/-- Every ≤9-light Z0 triple of a cycle classifies. -/
private lemma classifyZ0 {c : Fin 5 × M150G → ZMod 2}
    (h : ∀ p : Fin 2 × M150G, entrySum cmTerm c p = 0)
    (hw : popCntGo 30 (maskOf (blockOf c 0))
      + popCntGo 30 (maskOf (blockOf c 1))
      + popCntGo 30 (maskOf (blockOf c 4)) ≤ 9) :
    okTriple clsZ0 (maskOf (blockOf c 0)) (maskOf (blockOf c 1))
      (maskOf (blockOf c 4)) = true := by
  set mu := maskOf (blockOf c 0) with hmu
  set mw := maskOf (blockOf c 1) with hmw
  set mt := maskOf (blockOf c 4) with hmt
  have hbu : mu < 2 ^ 30 := maskOf_lt _
  have hbw : mw < 2 ^ 30 := maskOf_lt _
  have hbt : mt < 2 ^ 30 := maskOf_lt _
  have hEq : xorFold tUCZ0 mu ^^^ (xorFold tWC2Z0 mw ^^^ xorFold tRawCZ0 mt)
      = 0 := eqZ0 h
  have heven : (popCntGo 30 mu + popCntGo 30 mw + popCntGo 30 mt) % 2 = 0 := by
    have h0 : popCntGo 30 (xorFold tUCZ0 mu
        ^^^ (xorFold tWC2Z0 mw ^^^ xorFold tRawCZ0 mt)) % 2 = 0 := by
      rw [hEq, popCntGo_zero]
    have h1 := popCntGo_xor_mod2 30 (xorFold tUCZ0 mu)
      (xorFold tWC2Z0 mw ^^^ xorFold tRawCZ0 mt)
    have h2 := popCntGo_xor_mod2 30 (xorFold tWC2Z0 mw) (xorFold tRawCZ0 mt)
    have hA := parity_xorFold_odd dOddA_Z0 mu hbu
    have hB := parity_xorFold_odd dOddB_Z0 mw hbw
    have hC := parity_xorFold_odd dOddC_Z0 mt hbt
    omega
  -- shared derivations
  have hAeq : xorFold tUCZ0 mu = xorFold tWC2Z0 mw ^^^ xorFold tRawCZ0 mt :=
    xor3_solve_a hEq
  have huniq : mu = xorFold tWCZ0 mw ^^^ xorFold tTCZ0 mt := by
    calc mu = xorFold tAinvZ (xorFold tUCZ0 mu) :=
          (xorFold_comp_id dAinvA_Z0 mu hbu).symm
      _ = xorFold tAinvZ (xorFold tWC2Z0 mw ^^^ xorFold tRawCZ0 mt) := by
          rw [hAeq]
      _ = xorFold tAinvZ (xorFold tWC2Z0 mw)
          ^^^ xorFold tAinvZ (xorFold tRawCZ0 mt) := by
          rw [xorFold_xor]
      _ = xorFold tWCZ0 mw ^^^ xorFold tTCZ0 mt := by
          rw [xorFold_comp dAinvB_Z0 mw hbw, xorFold_comp dAinvC_Z0 mt hbt]
  have hcbound : xorFold tWCZ0 mw ^^^ xorFold tTCZ0 mt < 2 ^ 30 :=
    Nat.xor_lt_two_pow (xorFold_lt _ dBndWC_Z0 mw) (xorFold_lt _ dBndTC_Z0 mt)
  have hcov := covZ0 (popCntGo 30 mu) (by omega) (popCntGo 30 mw) (by omega)
    (popCntGo 30 mt) (by omega) (by omega) heven
  have hcases : (popCntGo 30 mu, popCntGo 30 mw, popCntGo 30 mt, 0) ∈ splitsZ0
      ∨ (popCntGo 30 mu, popCntGo 30 mw, popCntGo 30 mt, 2) ∈ splitsZ0
      ∨ (popCntGo 30 mu, popCntGo 30 mw, popCntGo 30 mt, 3) ∈ splitsZ0 := by
    rcases Bool.or_eq_true_iff.mp hcov with h' | h3
    · rcases Bool.or_eq_true_iff.mp h' with h0 | h2
      · exact Or.inl (by simpa using h0)
      · exact Or.inr (Or.inl (by simpa using h2))
    · exact Or.inr (Or.inr (by simpa using h3))
  rcases hcases with hmem | hmem | hmem
  · -- mode 0: w derived
    have hchk : checkSplit m4TZ0
        (popCntGo 30 mu, popCntGo 30 mw, popCntGo 30 mt, 0) = true :=
      List.all_eq_true.mp checkAll_Z0 _ hmem
    have hder0 : mw = xorFold tUWZ0 mu ^^^ xorFold tTWZ0 mt := by
      have h1 : xorFold tWCZ0 mw = mu ^^^ xorFold tTCZ0 mt := by
        rw [huniq, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      have hstep := congrArg (xorFold tUWZ0) h1
      rw [xorFold_xor, xorFold_comp_id dUWWC_Z0 mw hbw,
        xorFold_comp dUWTC_Z0 mt hbt] at hstep
      exact hstep
    exact checkSplit_sound_ut hchk hbu hbt rfl rfl hbw hder0 rfl
  · -- mode 2: u derived (trivial coset)
    have hchk : checkSplit m4TZ0
        (popCntGo 30 mu, popCntGo 30 mw, popCntGo 30 mt, 2) = true :=
      List.all_eq_true.mp checkAll_Z0 _ hmem
    have heq : mu = xorFold tPZ0 (xorFold tWCZ0 mw ^^^ xorFold tTCZ0 mt)
        ^^^ 0 := by
      rw [Nat.xor_zero, xorFold_id dPid_Z0 _ hcbound]
      exact huniq
    have hln0 : popCntGo 30
        (m4TZ0.ln0 &&& (xorFold tWCZ0 mw ^^^ xorFold tTCZ0 mt)) % 2 = 0 := by
      have hz : m4TZ0.ln0 = 0 := rfl
      rw [hz, Nat.zero_and, popCntGo_zero]
    have hln1 : popCntGo 30
        (m4TZ0.ln1 &&& (xorFold tWCZ0 mw ^^^ xorFold tTCZ0 mt)) % 2 = 0 := by
      have hz : m4TZ0.ln1 = 0 := rfl
      rw [hz, Nat.zero_and, popCntGo_zero]
    exact checkSplit_sound_wt hchk hbw hbt rfl rfl hbu rfl
      ⟨0, dAnn0_Z0, heq⟩ hcbound hln0 hln1
  · -- mode 3: t in the AnnT coset
    have hchk : checkSplit m4TZ0
        (popCntGo 30 mu, popCntGo 30 mw, popCntGo 30 mt, 3) = true :=
      List.all_eq_true.mp checkAll_Z0 _ hmem
    have hc' : xorFold tUCZ0 mu ^^^ xorFold tWC2Z0 mw = xorFold tRawCZ0 mt :=
      (xor3_solve_c hEq).symm
    have ha : (mt ^^^ xorFold tPTZ0 (xorFold tUCZ0 mu ^^^ xorFold tWC2Z0 mw))
        ∈ annTZ0 := by
      rw [hc']
      have hFx : ∀ m₁ m₂ : Nat,
          (m₁ ^^^ m₂) ^^^ xorFold tPTZ0 (xorFold tRawCZ0 (m₁ ^^^ m₂))
            = (m₁ ^^^ xorFold tPTZ0 (xorFold tRawCZ0 m₁))
              ^^^ (m₂ ^^^ xorFold tPTZ0 (xorFold tRawCZ0 m₂)) := by
        intro m₁ m₂
        rw [xorFold_xor, xorFold_xor, xor_xor_pair]
      have hP0 : ((0 : Nat) ^^^ xorFold tPTZ0 (xorFold tRawCZ0 0)) ∈ annTZ0 := by
        simpa using dAnnT_Z0.1
      have hbit : ∀ i < 30,
          ((1 <<< i) ^^^ xorFold tPTZ0 (xorFold tRawCZ0 (1 <<< i))) ∈ annTZ0 := by
        intro i hi
        rw [xorFold_bit]
        exact dCorrT_Z0 i hi
      exact linear_pred
        (F := fun m => m ^^^ xorFold tPTZ0 (xorFold tRawCZ0 m))
        (P := (· ∈ annTZ0)) 30 hFx hP0
        (fun a b ha hb => dAnnT_Z0.2 a ha b hb) hbit mt hbt
    have heq : mt = xorFold tPTZ0 (xorFold tUCZ0 mu ^^^ xorFold tWC2Z0 mw)
        ^^^ (mt ^^^ xorFold tPTZ0 (xorFold tUCZ0 mu ^^^ xorFold tWC2Z0 mw)) := by
      rw [← Nat.xor_assoc, Nat.xor_comm _ mt, Nat.xor_assoc, Nat.xor_self,
        Nat.xor_zero]
    have hln0 : popCntGo 30
        (m4TZ0.lnT0 &&& (xorFold tUCZ0 mu ^^^ xorFold tWC2Z0 mw)) % 2 = 0 := by
      rw [hc']
      exact parity_and_xorFold dLnT0_Z0 mt hbt
    have hln1 : popCntGo 30
        (m4TZ0.lnT1 &&& (xorFold tUCZ0 mu ^^^ xorFold tWC2Z0 mw)) % 2 = 0 := by
      rw [hc']
      exact parity_and_xorFold dLnT1_Z0 mt hbt
    exact checkSplit_sound_uwT hchk hbu hbw rfl rfl hbt rfl ⟨_, ha, heq⟩
      (Nat.xor_lt_two_pow (xorFold_lt _ dBndA_Z0 mu) (xorFold_lt _ dBndB_Z0 mw))
      hln0 hln1

/-- Every ≤9-light Z1 triple of a cycle classifies. -/
private lemma classifyZ1 {c : Fin 5 × M150G → ZMod 2}
    (h : ∀ p : Fin 2 × M150G, entrySum cmTerm c p = 0)
    (hw : popCntGo 30 (maskOf (blockOf c 2))
      + popCntGo 30 (maskOf (blockOf c 3))
      + popCntGo 30 (maskOf (blockOf c 4)) ≤ 9) :
    okTriple clsZ1 (maskOf (blockOf c 2)) (maskOf (blockOf c 3))
      (maskOf (blockOf c 4)) = true := by
  set mu := maskOf (blockOf c 2) with hmu
  set mw := maskOf (blockOf c 3) with hmw
  set mt := maskOf (blockOf c 4) with hmt
  have hbu : mu < 2 ^ 30 := maskOf_lt _
  have hbw : mw < 2 ^ 30 := maskOf_lt _
  have hbt : mt < 2 ^ 30 := maskOf_lt _
  have hEq : xorFold tUCZ1 mu ^^^ (xorFold tWC2Z1 mw ^^^ xorFold tRawCZ1 mt)
      = 0 := eqZ1 h
  have heven : (popCntGo 30 mu + popCntGo 30 mw + popCntGo 30 mt) % 2 = 0 := by
    have h0 : popCntGo 30 (xorFold tUCZ1 mu
        ^^^ (xorFold tWC2Z1 mw ^^^ xorFold tRawCZ1 mt)) % 2 = 0 := by
      rw [hEq, popCntGo_zero]
    have h1 := popCntGo_xor_mod2 30 (xorFold tUCZ1 mu)
      (xorFold tWC2Z1 mw ^^^ xorFold tRawCZ1 mt)
    have h2 := popCntGo_xor_mod2 30 (xorFold tWC2Z1 mw) (xorFold tRawCZ1 mt)
    have hA := parity_xorFold_odd dOddA_Z1 mu hbu
    have hB := parity_xorFold_odd dOddB_Z1 mw hbw
    have hC := parity_xorFold_odd dOddC_Z1 mt hbt
    omega
  have hAeq : xorFold tUCZ1 mu = xorFold tWC2Z1 mw ^^^ xorFold tRawCZ1 mt :=
    xor3_solve_a hEq
  have huniq : mu = xorFold tWCZ1 mw ^^^ xorFold tTCZ1 mt := by
    calc mu = xorFold tAinvZ (xorFold tUCZ1 mu) :=
          (xorFold_comp_id dAinvA_Z1 mu hbu).symm
      _ = xorFold tAinvZ (xorFold tWC2Z1 mw ^^^ xorFold tRawCZ1 mt) := by
          rw [hAeq]
      _ = xorFold tAinvZ (xorFold tWC2Z1 mw)
          ^^^ xorFold tAinvZ (xorFold tRawCZ1 mt) := by
          rw [xorFold_xor]
      _ = xorFold tWCZ1 mw ^^^ xorFold tTCZ1 mt := by
          rw [xorFold_comp dAinvB_Z1 mw hbw, xorFold_comp dAinvC_Z1 mt hbt]
  have hcbound : xorFold tWCZ1 mw ^^^ xorFold tTCZ1 mt < 2 ^ 30 :=
    Nat.xor_lt_two_pow (xorFold_lt _ dBndWC_Z1 mw) (xorFold_lt _ dBndTC_Z1 mt)
  have hcov := covZ1 (popCntGo 30 mu) (by omega) (popCntGo 30 mw) (by omega)
    (popCntGo 30 mt) (by omega) (by omega) heven
  have hcases : (popCntGo 30 mu, popCntGo 30 mw, popCntGo 30 mt, 0) ∈ splitsZ1
      ∨ (popCntGo 30 mu, popCntGo 30 mw, popCntGo 30 mt, 2) ∈ splitsZ1
      ∨ (popCntGo 30 mu, popCntGo 30 mw, popCntGo 30 mt, 3) ∈ splitsZ1 := by
    rcases Bool.or_eq_true_iff.mp hcov with h' | h3
    · rcases Bool.or_eq_true_iff.mp h' with h0 | h2
      · exact Or.inl (by simpa using h0)
      · exact Or.inr (Or.inl (by simpa using h2))
    · exact Or.inr (Or.inr (by simpa using h3))
  rcases hcases with hmem | hmem | hmem
  · have hchk : checkSplit m4TZ1
        (popCntGo 30 mu, popCntGo 30 mw, popCntGo 30 mt, 0) = true :=
      List.all_eq_true.mp checkAll_Z1 _ hmem
    have hder0 : mw = xorFold tUWZ1 mu ^^^ xorFold tTWZ1 mt := by
      have h1 : xorFold tWCZ1 mw = mu ^^^ xorFold tTCZ1 mt := by
        rw [huniq, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      have hstep := congrArg (xorFold tUWZ1) h1
      rw [xorFold_xor, xorFold_comp_id dUWWC_Z1 mw hbw,
        xorFold_comp dUWTC_Z1 mt hbt] at hstep
      exact hstep
    exact checkSplit_sound_ut hchk hbu hbt rfl rfl hbw hder0 rfl
  · have hchk : checkSplit m4TZ1
        (popCntGo 30 mu, popCntGo 30 mw, popCntGo 30 mt, 2) = true :=
      List.all_eq_true.mp checkAll_Z1 _ hmem
    have heq : mu = xorFold tPZ1 (xorFold tWCZ1 mw ^^^ xorFold tTCZ1 mt)
        ^^^ 0 := by
      rw [Nat.xor_zero, xorFold_id dPid_Z1 _ hcbound]
      exact huniq
    have hln0 : popCntGo 30
        (m4TZ1.ln0 &&& (xorFold tWCZ1 mw ^^^ xorFold tTCZ1 mt)) % 2 = 0 := by
      have hz : m4TZ1.ln0 = 0 := rfl
      rw [hz, Nat.zero_and, popCntGo_zero]
    have hln1 : popCntGo 30
        (m4TZ1.ln1 &&& (xorFold tWCZ1 mw ^^^ xorFold tTCZ1 mt)) % 2 = 0 := by
      have hz : m4TZ1.ln1 = 0 := rfl
      rw [hz, Nat.zero_and, popCntGo_zero]
    exact checkSplit_sound_wt hchk hbw hbt rfl rfl hbu rfl
      ⟨0, dAnn0_Z1, heq⟩ hcbound hln0 hln1
  · have hchk : checkSplit m4TZ1
        (popCntGo 30 mu, popCntGo 30 mw, popCntGo 30 mt, 3) = true :=
      List.all_eq_true.mp checkAll_Z1 _ hmem
    have hc' : xorFold tUCZ1 mu ^^^ xorFold tWC2Z1 mw = xorFold tRawCZ1 mt :=
      (xor3_solve_c hEq).symm
    have ha : (mt ^^^ xorFold tPTZ1 (xorFold tUCZ1 mu ^^^ xorFold tWC2Z1 mw))
        ∈ annTZ1 := by
      rw [hc']
      have hFx : ∀ m₁ m₂ : Nat,
          (m₁ ^^^ m₂) ^^^ xorFold tPTZ1 (xorFold tRawCZ1 (m₁ ^^^ m₂))
            = (m₁ ^^^ xorFold tPTZ1 (xorFold tRawCZ1 m₁))
              ^^^ (m₂ ^^^ xorFold tPTZ1 (xorFold tRawCZ1 m₂)) := by
        intro m₁ m₂
        rw [xorFold_xor, xorFold_xor, xor_xor_pair]
      have hP0 : ((0 : Nat) ^^^ xorFold tPTZ1 (xorFold tRawCZ1 0)) ∈ annTZ1 := by
        simpa using dAnnT_Z1.1
      have hbit : ∀ i < 30,
          ((1 <<< i) ^^^ xorFold tPTZ1 (xorFold tRawCZ1 (1 <<< i))) ∈ annTZ1 := by
        intro i hi
        rw [xorFold_bit]
        exact dCorrT_Z1 i hi
      exact linear_pred
        (F := fun m => m ^^^ xorFold tPTZ1 (xorFold tRawCZ1 m))
        (P := (· ∈ annTZ1)) 30 hFx hP0
        (fun a b ha hb => dAnnT_Z1.2 a ha b hb) hbit mt hbt
    have heq : mt = xorFold tPTZ1 (xorFold tUCZ1 mu ^^^ xorFold tWC2Z1 mw)
        ^^^ (mt ^^^ xorFold tPTZ1 (xorFold tUCZ1 mu ^^^ xorFold tWC2Z1 mw)) := by
      rw [← Nat.xor_assoc, Nat.xor_comm _ mt, Nat.xor_assoc, Nat.xor_self,
        Nat.xor_zero]
    have hln0 : popCntGo 30
        (m4TZ1.lnT0 &&& (xorFold tUCZ1 mu ^^^ xorFold tWC2Z1 mw)) % 2 = 0 := by
      rw [hc']
      exact parity_and_xorFold dLnT0_Z1 mt hbt
    have hln1 : popCntGo 30
        (m4TZ1.lnT1 &&& (xorFold tUCZ1 mu ^^^ xorFold tWC2Z1 mw)) % 2 = 0 := by
      rw [hc']
      exact parity_and_xorFold dLnT1_Z1 mt hbt
    exact checkSplit_sound_uwT hchk hbu hbw rfl rfl hbt rfl ⟨_, ha, heq⟩
      (Nat.xor_lt_two_pow (xorFold_lt _ dBndA_Z1 mu) (xorFold_lt _ dBndB_Z1 mw))
      hln0 hln1

/-! ## §7  Row reconstruction -/

/-- Equal Z-side packings force equal chains. -/
private lemma packZ_inj {c d : Fin 5 × M150G → ZMod 2}
    (h : packZ c = packZ d) : c = d := by
  have e0 := congrArg (· % 2 ^ 30) h
  have e1 := congrArg (fun x => (x >>> 30) % 2 ^ 30) h
  have e2 := congrArg (fun x => (x >>> 60) % 2 ^ 30) h
  have e3 := congrArg (fun x => (x >>> 90) % 2 ^ 30) h
  have e4 := congrArg (fun x => x >>> 120) h
  simp only [packZ, pack5_mod, pack5_shr30_mod, pack5_shr60_mod,
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
  have b1 := maskOf_inj e1
  have b2 := maskOf_inj e2
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

/-- Each `H_X` row chain is a boundary. -/
private lemma rowChainZ_mem_boundaries (k : Nat) :
    rowChainZ k ∈ m150Complex.boundaries := by
  have hfun : m150Complex.boundary2 (m150Complex.singleFace (checkOf k))
      = rowChainZ k := by
    funext q
    simp only [HomologicalCode.singleFace]
    exact boundary2_single_apply (checkOf k) q
  exact ⟨m150Complex.singleFace (checkOf k), hfun⟩

/-! ## §8  The floor -/

/-- **X-distance floor**: every cycle of chain weight ≤ 9 is a boundary
— i.e. `d_X ≥ 10` for the `[[150,30,10]]` mitten code. -/
theorem floorX (c : m150Complex.C1 → ZMod 2)
    (hker : m150Complex.boundary1 c = 0)
    (hw : m150Complex.chainWeight c ≤ 9) :
    c ∈ m150Complex.boundaries := by
  have hker' : ∀ p : Fin 2 × M150G, entrySum cmTerm c p = 0 := by
    intro p
    rw [← boundary1_eq_entrySum, hker]
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
  have hok0 := classifyZ0 hker' (by omega)
  have hok1 := classifyZ1 hker' (by omega)
  rcases okTriple_cases hok0 with ⟨hz0u, hz0w, hz0t⟩ | hmem0
  · rcases okTriple_cases hok1 with ⟨hz1u, hz1w, _⟩ | hmem1
    · have hb0 := eq_zero_of_maskOf_eq_zero hz0u
      have hb1 := eq_zero_of_maskOf_eq_zero hz0w
      have hb2 := eq_zero_of_maskOf_eq_zero hz1u
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
    · exfalso
      have ht := clsZ_facts.2.1 _ hmem1
      rw [packTriple_hi _ (maskOf_lt _) (maskOf_lt _)] at ht
      exact ht hz0t
  · rcases okTriple_cases hok1 with ⟨_, _, hz1t⟩ | hmem1
    · exfalso
      have ht := clsZ_facts.1 _ hmem0
      rw [packTriple_hi _ (maskOf_lt _) (maskOf_lt _)] at ht
      exact ht hz1t
    · have hjoin := checkJoin_sound checkJoin_Z (maskOf_lt _) (maskOf_lt _)
        (maskOf_lt _) (maskOf_lt _) (maskOf_lt _) hmem0 hmem1 (by omega)
      obtain ⟨k, -, hkpack⟩ := clsZ_facts.2.2 _ hjoin
      have hceq : c = rowChainZ k := (packZ_inj hkpack).symm
      rw [hceq]
      exact rowChainZ_mem_boundaries k
end M150
end LP
end Homological
end Stabilizer
end Quantum
