/-
# M4 floor machinery — generic packed-mask sweep layer

The `[[150,30,10]]` distance floors reduce to classifying light solutions
of four triple equations over `𝔽₂[C₅×S₃]` and joining them along the
shared block (design + offline validation:
`qec-lab:pipeline/attempts/mitten_150_30_10/m4_findings.md`).  This file
is the *instance-independent* layer: 30-bit masks as `Nat`s, the fueled
popcount and its table-driven fast form, XOR-fold table application with
its linearity/extension theory, weight-`k` mask enumeration with
completeness, and the three-mode split-sweep driver with one soundness
lemma per derivation mode.

The driver is engineered for `native_decide` throughput (measured 6.4 s
for a full instance sweep of 8.57M classes): table folds are hoisted to
the per-element lists (`foldedPairs`), the quadratic body is xor +
table-popcount + compare only, and the classification lists are packed
90-bit `Nat`s.  Everything the sweeps trust is either proved here
symbolically or supplied by the instance files as small `decide`/
`native_decide` facts (table bounds, basis identities, coset data).
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Bitwise

namespace Quantum
namespace Stabilizer
namespace Homological
namespace LP
namespace M150

private lemma xor_left_comm (a b c : Nat) :
    a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← Nat.xor_assoc, Nat.xor_comm a b, Nat.xor_assoc]

lemma testBit_one' (k : Nat) : Nat.testBit 1 k = decide (k = 0) := by
  cases k with
  | zero => rfl
  | succ k =>
    have h : (1 : Nat) >>> (k + 1) = 0 := by
      rw [Nat.shiftRight_eq_div_pow]
      refine Nat.div_eq_of_lt ?_
      calc (1 : Nat) < 2 := by omega
        _ ≤ 2 ^ (k + 1) := Nat.le_self_pow (by omega) 2
    simp [Nat.testBit, h]

/-! ## §1  Popcount: fueled (proof-facing) and table-driven (driver) -/

/-- Fueled popcount: number of set bits among the low `f` bits. -/
def popCntGo : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, m => (m &&& 1) + popCntGo f (m >>> 1)

/-- 15-bit popcount table (computed, not a literal — correct by
construction). -/
def popTbl : Array Nat := (Array.range 32768).map (popCntGo 15)

/-- Driver popcount for masks `< 2^30`: two table lookups. -/
def popCnt (m : Nat) : Nat :=
  popTbl.getD (m &&& 32767) 0 + popTbl.getD (m >>> 15) 0

/-- Driver parity of a mask. -/
def parity (m : Nat) : Bool := popCnt m % 2 = 1

lemma popTbl_getD {i : Nat} (hi : i < 32768) : popTbl.getD i 0 = popCntGo 15 i := by
  have hsz : popTbl.size = 32768 := by
    simp [popTbl]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)]
  simp [popTbl]

/-- Fuel splitting for the fueled popcount. -/
lemma popCntGo_add (a b m : Nat) :
    popCntGo (a + b) m = popCntGo a (m % 2 ^ a) + popCntGo b (m >>> a) := by
  induction a generalizing m with
  | zero => simp [popCntGo]
  | succ a ih =>
    have hstep : a + 1 + b = (a + b) + 1 := by omega
    rw [hstep]
    change (m &&& 1) + popCntGo (a + b) (m >>> 1) = _
    rw [ih (m >>> 1)]
    have h1 : (m % 2 ^ (a + 1)) &&& 1 = m &&& 1 := by
      rw [Nat.and_one_is_mod, Nat.and_one_is_mod, Nat.mod_mod_of_dvd]
      exact ⟨2 ^ a, by ring⟩
    have h2 : (m % 2 ^ (a + 1)) >>> 1 = (m >>> 1) % 2 ^ a := by
      apply Nat.eq_of_testBit_eq
      intro i
      simp only [Nat.testBit_shiftRight, Nat.testBit_mod_two_pow]
      by_cases hia : 1 + i < a + 1 <;> by_cases hia' : i < a <;>
        simp [hia, hia'] <;> omega
    have hrhs : popCntGo (a + 1) (m % 2 ^ (a + 1))
        = (m &&& 1) + popCntGo a ((m >>> 1) % 2 ^ a) := by
      change ((m % 2 ^ (a + 1)) &&& 1) + popCntGo a ((m % 2 ^ (a + 1)) >>> 1) = _
      rw [h1, h2]
    have hsh : m >>> (a + 1) = (m >>> 1) >>> a := by
      rw [Nat.add_comm, Nat.shiftRight_add]
    rw [hrhs, hsh]
    omega

/-- The driver popcount agrees with the fueled one on 30-bit masks. -/
lemma popCnt_eq {m : Nat} (hm : m < 2 ^ 30) : popCnt m = popCntGo 30 m := by
  have hlo : m &&& 32767 < 32768 := by
    have := Nat.and_le_right (n := m) (m := 32767)
    omega
  have hhi : m >>> 15 < 32768 := by
    rw [Nat.shiftRight_eq_div_pow]
    have : m / 2 ^ 15 < 2 ^ 15 := Nat.div_lt_of_lt_mul (by norm_num at hm ⊢; omega)
    simpa using this
  rw [popCnt, popTbl_getD hlo, popTbl_getD hhi]
  have hmask : m &&& 32767 = m % 2 ^ 15 := by
    have : (32767 : Nat) = 2 ^ 15 - 1 := by norm_num
    rw [this, Nat.and_two_pow_sub_one_eq_mod]
  rw [hmask, show (30 : Nat) = 15 + 15 from rfl, popCntGo_add]

/-- Fueled popcount as a filter cardinality (the bridge to chain
weights). -/
lemma popCntGo_eq_card (f : Nat) :
    ∀ m : Nat, popCntGo f m = ((Finset.range f).filter (fun i => m.testBit i)).card := by
  induction f with
  | zero => intro m; simp [popCntGo]
  | succ f ih =>
    intro m
    rw [Finset.card_filter, Finset.sum_range_succ']
    change (m &&& 1) + popCntGo f (m >>> 1) = _
    rw [ih (m >>> 1)]
    rw [Finset.card_filter]
    have hbit : ∀ i, (m >>> 1).testBit i = m.testBit (i + 1) := by
      intro i
      rw [Nat.testBit_shiftRight, Nat.add_comm]
    have hsum : (∑ i ∈ Finset.range f, if (m >>> 1).testBit i then 1 else 0)
        = ∑ i ∈ Finset.range f, if m.testBit (i + 1) then 1 else 0 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hbit]
    have hzero : (m &&& 1) = if m.testBit 0 then 1 else 0 := by
      rw [Nat.and_one_is_mod]
      rcases Nat.mod_two_eq_zero_or_one m with h | h <;>
        simp [Nat.testBit_zero, h]
    omega

/-! ## §2  XOR-fold: applying a packed column table to a mask -/

/-- `xorFold tbl m` = XOR of `tbl[i]` over the set bits `i` of `m` (the
`𝔽₂`-linear map with columns `tbl`, applied to `m`). -/
def xorFold : List Nat → Nat → Nat
  | [], _ => 0
  | c :: rest, m => (if m &&& 1 = 1 then c else 0) ^^^ xorFold rest (m >>> 1)

@[simp] lemma xorFold_nil (m : Nat) : xorFold [] m = 0 := rfl

@[simp] lemma xorFold_zero (tbl : List Nat) : xorFold tbl 0 = 0 := by
  induction tbl with
  | nil => rfl
  | cons c rest ih => simp [xorFold, ih]

/-- `xorFold` is `𝔽₂`-linear in the mask. -/
lemma xorFold_xor (tbl : List Nat) (m₁ m₂ : Nat) :
    xorFold tbl (m₁ ^^^ m₂) = xorFold tbl m₁ ^^^ xorFold tbl m₂ := by
  induction tbl generalizing m₁ m₂ with
  | nil => simp
  | cons c rest ih =>
    change (if (m₁ ^^^ m₂) &&& 1 = 1 then c else 0) ^^^ xorFold rest ((m₁ ^^^ m₂) >>> 1) = _
    have hsh : (m₁ ^^^ m₂) >>> 1 = m₁ >>> 1 ^^^ m₂ >>> 1 := by
      apply Nat.eq_of_testBit_eq
      intro i
      simp [Nat.testBit_shiftRight, Nat.testBit_xor]
    have hand : (m₁ ^^^ m₂) &&& 1 = (m₁ &&& 1) ^^^ (m₂ &&& 1) :=
      Nat.and_xor_distrib_right
    rw [hsh, ih, hand]
    change _ = ((if m₁ &&& 1 = 1 then c else 0) ^^^ xorFold rest (m₁ >>> 1))
      ^^^ ((if m₂ &&& 1 = 1 then c else 0) ^^^ xorFold rest (m₂ >>> 1))
    have h1 : m₁ &&& 1 = m₁ % 2 := Nat.and_one_is_mod m₁
    have h2 : m₂ &&& 1 = m₂ % 2 := Nat.and_one_is_mod m₂
    rcases Nat.mod_two_eq_zero_or_one m₁ with e1 | e1 <;>
      rcases Nat.mod_two_eq_zero_or_one m₂ with e2 | e2 <;>
      simp [h1, h2, e1, e2, Nat.xor_assoc, Nat.xor_comm, xor_left_comm]

/-- `xorFold` on a basis mask picks out the table column. -/
lemma xorFold_bit (tbl : List Nat) (i : Nat) :
    xorFold tbl (1 <<< i) = tbl.getD i 0 := by
  induction tbl generalizing i with
  | nil => simp
  | cons c rest ih =>
    cases i with
    | zero =>
      change (if (1 <<< 0) &&& 1 = 1 then c else 0) ^^^ xorFold rest ((1 <<< 0) >>> 1) = c
      have h0 : (1 : Nat) <<< 0 = 1 := Nat.shiftLeft_zero
      rw [h0]
      change (if 1 &&& 1 = 1 then c else 0) ^^^ xorFold rest 0 = c
      rw [xorFold_zero]
      simp
    | succ i =>
      have hand : (1 <<< (i + 1)) &&& 1 = 0 := by
        rw [Nat.and_one_is_mod, Nat.shiftLeft_eq, Nat.one_mul, Nat.pow_succ]
        omega
      have hsh : (1 <<< (i + 1)) >>> 1 = 1 <<< i := by
        rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul, Nat.one_mul,
          Nat.shiftRight_eq_div_pow, Nat.pow_succ, Nat.pow_one]
        exact Nat.mul_div_cancel _ (by omega)
      change (if (1 <<< (i + 1)) &&& 1 = 1 then c else 0)
          ^^^ xorFold rest ((1 <<< (i + 1)) >>> 1) = rest.getD i 0
      rw [hand, hsh, ih]
      simp

/-- Bounded tables give bounded folds. -/
lemma xorFold_lt (tbl : List Nat) (hb : ∀ x ∈ tbl, x < 2 ^ 30) (m : Nat) :
    xorFold tbl m < 2 ^ 30 := by
  induction tbl generalizing m with
  | nil => simp
  | cons c rest ih =>
    change (if m &&& 1 = 1 then c else 0) ^^^ xorFold rest (m >>> 1) < 2 ^ 30
    refine Nat.xor_lt_two_pow ?_ (ih (fun x hx => hb x (List.mem_cons_of_mem _ hx)) _)
    split
    · exact hb c List.mem_cons_self
    · positivity

/-- Nonzero masks have a set bit (their top bit). -/
private lemma testBit_log2_self {m : Nat} (hm : m ≠ 0) : m.testBit m.log2 = true := by
  have h1 : 2 ^ m.log2 ≤ m := Nat.log2_self_le hm
  have h2 : m < 2 ^ (m.log2 + 1) := Nat.lt_log2_self
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
  have : m / 2 ^ m.log2 = 1 := by
    have hlt : m / 2 ^ m.log2 < 2 := by
      apply Nat.div_lt_of_lt_mul
      calc m < 2 ^ (m.log2 + 1) := h2
        _ = 2 ^ m.log2 * 2 := by ring
    have hge : 1 ≤ m / 2 ^ m.log2 := (Nat.one_le_div_iff (by positivity)).mpr h1
    omega
  simp [this]

/-- Clearing the top bit strictly decreases. -/
private lemma xor_top_bit_lt {m : Nat} (hm : m ≠ 0) : m ^^^ 1 <<< m.log2 < m := by
  have htop : m.testBit m.log2 = true := testBit_log2_self hm
  have hlt2 : m < 2 ^ (m.log2 + 1) := Nat.lt_log2_self
  have hbits : ∀ i, m.log2 ≤ i → (m ^^^ 1 <<< m.log2).testBit i = false := by
    intro i hi
    rcases Nat.lt_or_ge i (m.log2 + 1) with hcase | hcase
    · have : i = m.log2 := by omega
      subst this
      simp [Nat.testBit_xor, htop, Nat.testBit_shiftLeft]
    · have hmi : m.testBit i = false :=
        Nat.testBit_eq_false_of_lt
          (lt_of_lt_of_le hlt2 (Nat.pow_le_pow_right (by norm_num) hcase))
      have hne : ¬(i - m.log2 = 0) := by omega
      simp [Nat.testBit_xor, hmi, Nat.testBit_shiftLeft, testBit_one', hne, hi]
  have hbound : m ^^^ 1 <<< m.log2 < 2 ^ m.log2 := by
    set x := m ^^^ 1 <<< m.log2 with hx
    have hxeq : x = x % 2 ^ m.log2 := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_mod_two_pow]
      by_cases hilt : i < m.log2
      · simp [hilt]
      · have := hbits i (by omega)
        simp [hilt, this]
    rw [hxeq]
    exact Nat.mod_lt _ (by positivity)
  calc m ^^^ 1 <<< m.log2 < 2 ^ m.log2 := hbound
    _ ≤ m := Nat.log2_self_le hm

/-- **Linear extension**: two xor-linear maps sending `0 ↦ 0` and agreeing
on the basis masks `1 <<< i` (`i < n`) agree on all masks `< 2^n`. -/
lemma linear_ext {F G : Nat → Nat} (n : Nat)
    (hF0 : F 0 = 0) (hG0 : G 0 = 0)
    (hFx : ∀ m₁ m₂, F (m₁ ^^^ m₂) = F m₁ ^^^ F m₂)
    (hGx : ∀ m₁ m₂, G (m₁ ^^^ m₂) = G m₁ ^^^ G m₂)
    (hbit : ∀ i < n, F (1 <<< i) = G (1 <<< i)) :
    ∀ m < 2 ^ n, F m = G m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · rw [hF0, hG0]
    · have hm0 : m ≠ 0 := by omega
      have hlog : m.log2 < n := by
        have h1 : 2 ^ m.log2 ≤ m := Nat.log2_self_le hm0
        by_contra hcon
        push Not at hcon
        have : 2 ^ n ≤ 2 ^ m.log2 := Nat.pow_le_pow_right (by norm_num) hcon
        omega
      set m' := m ^^^ 1 <<< m.log2 with hm'
      have hlt : m' < m := xor_top_bit_lt hm0
      have hm'2 : m' < 2 ^ n := lt_trans hlt hm
      have hsplit : m = m' ^^^ 1 <<< m.log2 := by
        rw [hm', Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      rw [hsplit, hFx, hGx, ih m' hlt hm'2, hbit _ hlog]

/-! ## §3  Weight-`k` mask enumeration -/

/-- All `n`-bit masks of fueled popcount `k`. -/
def masksOfWt : Nat → Nat → List Nat
  | _, 0 => [0]
  | 0, _ + 1 => []
  | n + 1, k + 1 =>
      masksOfWt n (k + 1) ++ (masksOfWt n k).map (fun m => m ||| 1 <<< n)

/-- **Completeness**: every mask `< 2^n` of weight `k` is enumerated. -/
lemma mem_masksOfWt : ∀ (n k m : Nat), m < 2 ^ n → popCntGo n m = k →
    m ∈ masksOfWt n k := by
  intro n
  induction n with
  | zero =>
    intro k m hm hk
    interval_cases m
    simp only [popCntGo] at hk
    subst hk
    simp [masksOfWt]
  | succ n ih =>
    intro k m hm hk
    have hsplit : popCntGo (n + 1) m = popCntGo n (m % 2 ^ n) + popCntGo 1 (m >>> n) := by
      rw [← popCntGo_add]
    have hbit : popCntGo 1 (m >>> n) = if m.testBit n then 1 else 0 := by
      change (m >>> n) &&& 1 + 0 = _
      rw [Nat.and_one_is_mod]
      have : m.testBit n = decide ((m >>> n) % 2 = 1) := by
        rw [Nat.testBit, Nat.and_comm, Nat.and_one_is_mod]
        rcases Nat.mod_two_eq_zero_or_one (m >>> n) with h | h <;> simp [h]
      rcases Nat.mod_two_eq_zero_or_one (m >>> n) with h | h <;> simp [this, h]
    by_cases htop : m.testBit n
    · -- top bit set: strip it and recurse into the mapped branch
      have hk' : k = popCntGo n (m % 2 ^ n) + 1 := by
        rw [← hk, hsplit, hbit, if_pos htop]
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨popCntGo n (m % 2 ^ n), by omega⟩
      have hk'' : popCntGo n (m % 2 ^ n) = k' := by omega
      have hdecomp : m = m % 2 ^ n ||| 1 <<< n := by
        apply Nat.eq_of_testBit_eq
        intro i
        simp only [Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft,
          testBit_one']
        rcases Nat.lt_trichotomy i n with hi | rfl | hi
        · have : ¬(i ≥ n) := by omega
          simp [hi, this]
        · simp [htop]
        · have h1 : ¬(i < n) := by omega
          have h2 : m.testBit i = false :=
            Nat.testBit_eq_false_of_lt
              (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by omega)))
          have h3 : ¬(i - n = 0) := by omega
          simp [h1, h2, h3]
      rw [hdecomp]
      change _ ∈ masksOfWt (n + 1) (k' + 1)
      simp only [masksOfWt, List.mem_append, List.mem_map]
      exact Or.inr ⟨m % 2 ^ n, ih k' (m % 2 ^ n) (Nat.mod_lt _ (by positivity)) hk'', rfl⟩
    · -- top bit clear: m < 2^n, recurse into the left branch
      have hmn : m < 2 ^ n := by
        rcases Nat.lt_or_ge m (2 ^ n) with h | h
        · exact h
        · exfalso
          have : m.testBit n = true := by
            rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
            have hdiv : m / 2 ^ n = 1 := by
              have : m / 2 ^ n < 2 := by
                apply Nat.div_lt_of_lt_mul
                calc m < 2 ^ (n + 1) := hm
                  _ = 2 ^ n * 2 := by ring
              have : 1 ≤ m / 2 ^ n := (Nat.one_le_div_iff (by positivity)).mpr h
              omega
            simp [hdiv]
          simp [htop] at this
      have hmod : m % 2 ^ n = m := Nat.mod_eq_of_lt hmn
      have hk' : popCntGo n m = k := by
        rw [← hk, hsplit, hbit, if_neg htop, hmod]
        omega
      cases k with
      | zero =>
        have : m ∈ masksOfWt n 0 := ih 0 m hmn hk'
        simp only [masksOfWt] at this ⊢
        cases n <;> simpa [masksOfWt] using this
      | succ k =>
        change m ∈ masksOfWt (n + 1) (k + 1)
        simp only [masksOfWt, List.mem_append]
        exact Or.inl (ih (k + 1) m hmn hk')

/-! ## §4  The three-mode split-sweep driver -/

/-- Pair each mask with its folded table image (hoists the fold out of
the quadratic pair loop). -/
def foldedPairs (tbl : List Nat) (ms : List Nat) : List (Nat × Nat) :=
  ms.map fun m => (m, xorFold tbl m)

/-- Packed 90-bit triple. -/
def packTriple (mu mw mt : Nat) : Nat := mu ||| (mw <<< 30) ||| (mt <<< 60)

/-- Classification check: zero or listed. -/
def okTriple (cls : List Nat) (mu mw mt : Nat) : Bool :=
  (mu ||| mw ||| mt) == 0 || cls.contains (packTriple mu mw mt)

/-- The tables of one triple instance.  Modes: `0` sweeps `(u,t)` and
derives `w` (unique); `1` sweeps `(u,w)` and derives `t` (unique);
`2` sweeps `(w,t)` and scans the `Ann`-coset of the derived `u` (fields
`tWC/tTC/tP/ln*/ann`; a trivial coset — `tP` = identity columns,
`ln* = 0`, `ann = [0]` — recovers a unique `u`-derivation); `3` sweeps
`(u,w)` and scans the `Ann`-coset of the derived `t` (fields
`tUC/tWC2/tPT/lnT*/annT`).  Unused fields of an instance are `[]`/`0`. -/
structure SweepTables where
  tUW : List Nat
  tTW : List Nat
  tUT : List Nat
  tWT : List Nat
  tWC : List Nat
  tTC : List Nat
  tP : List Nat
  ln0 : Nat
  ln1 : Nat
  ann : List Nat
  tUC : List Nat
  tWC2 : List Nat
  tPT : List Nat
  lnT0 : Nat
  lnT1 : Nat
  annT : List Nat
  cls : List Nat

/-- One split of one instance (`(p, q, r, mode)`). -/
def checkSplit (T : SweepTables) : Nat × Nat × Nat × Nat → Bool
  | (p, q, r, 0) =>
      let ups := foldedPairs T.tUW (masksOfWt 30 p)
      let tps := foldedPairs T.tTW (masksOfWt 30 r)
      ups.all fun uw =>
        tps.all fun tw =>
          let mw := uw.2 ^^^ tw.2
          popCnt mw != q || okTriple T.cls uw.1 mw tw.1
  | (p, q, r, 1) =>
      let ups := foldedPairs T.tUT (masksOfWt 30 p)
      let wps := foldedPairs T.tWT (masksOfWt 30 q)
      ups.all fun ut =>
        wps.all fun wt =>
          let mt := ut.2 ^^^ wt.2
          popCnt mt != r || okTriple T.cls ut.1 wt.1 mt
  | (p, q, r, 2) =>
      let wps := foldedPairs T.tWC (masksOfWt 30 q)
      let tps := foldedPairs T.tTC (masksOfWt 30 r)
      wps.all fun wc =>
        tps.all fun tc =>
          let c := wc.2 ^^^ tc.2
          parity (T.ln0 &&& c) || parity (T.ln1 &&& c) ||
            (let up := xorFold T.tP c
             T.ann.all fun a =>
               let mu := up ^^^ a
               popCnt mu != p || okTriple T.cls mu wc.1 tc.1)
  | (p, q, r, _) =>
      let ups := foldedPairs T.tUC (masksOfWt 30 p)
      let wps := foldedPairs T.tWC2 (masksOfWt 30 q)
      ups.all fun uc =>
        wps.all fun wc =>
          let c := uc.2 ^^^ wc.2
          parity (T.lnT0 &&& c) || parity (T.lnT1 &&& c) ||
            (let tp := xorFold T.tPT c
             T.annT.all fun a =>
               let mt := tp ^^^ a
               popCnt mt != r || okTriple T.cls uc.1 wc.1 mt)

/-- All splits of one instance — the single `native_decide` obligation. -/
def checkAll (T : SweepTables) (splits : List (Nat × Nat × Nat × Nat)) : Bool :=
  splits.all (checkSplit T)

/-! ### Driver soundness -/

private lemma all_pairs_true {f : Nat × Nat → Nat × Nat → Bool}
    {tbl₁ tbl₂ : List Nat} {ms₁ ms₂ : List Nat} {m₁ m₂ : Nat}
    (hall : (foldedPairs tbl₁ ms₁).all
      (fun x => (foldedPairs tbl₂ ms₂).all (fun y => f x y)) = true)
    (h₁ : m₁ ∈ ms₁) (h₂ : m₂ ∈ ms₂) :
    f (m₁, xorFold tbl₁ m₁) (m₂, xorFold tbl₂ m₂) = true := by
  have hx : (m₁, xorFold tbl₁ m₁) ∈ foldedPairs tbl₁ ms₁ :=
    List.mem_map_of_mem h₁
  have hy : (m₂, xorFold tbl₂ m₂) ∈ foldedPairs tbl₂ ms₂ :=
    List.mem_map_of_mem h₂
  exact List.all_eq_true.mp (List.all_eq_true.mp hall _ hx) _ hy

private lemma of_bne_or {a b : Nat} {c : Bool} (h : (a != b || c) = true)
    (hab : a = b) : c = true := by
  rcases Bool.or_eq_true_iff.mp h with h' | h'
  · exact absurd hab (by simpa using h')
  · exact h'

/-- Soundness, mode `0` (`(u,t)` swept, `w` derived). -/
theorem checkSplit_sound_ut {T : SweepTables} {p q r : Nat}
    (hchk : checkSplit T (p, q, r, 0) = true)
    {mu mw mt : Nat} (hmu : mu < 2 ^ 30) (hmt : mt < 2 ^ 30)
    (hpu : popCntGo 30 mu = p) (hpt : popCntGo 30 mt = r)
    (hbw : mw < 2 ^ 30)
    (hder : mw = xorFold T.tUW mu ^^^ xorFold T.tTW mt)
    (hpw : popCntGo 30 mw = q) :
    okTriple T.cls mu mw mt = true := by
  have h := all_pairs_true hchk
    (mem_masksOfWt 30 p mu hmu hpu) (mem_masksOfWt 30 r mt hmt hpt)
  rw [← hder] at h
  exact of_bne_or h (by rw [popCnt_eq hbw, hpw])

/-- Soundness, mode `1` (`(u,w)` swept, `t` derived). -/
theorem checkSplit_sound_uw {T : SweepTables} {p q r : Nat}
    (hchk : checkSplit T (p, q, r, 1) = true)
    {mu mw mt : Nat} (hmu : mu < 2 ^ 30) (hmw : mw < 2 ^ 30)
    (hpu : popCntGo 30 mu = p) (hpw : popCntGo 30 mw = q)
    (hbt : mt < 2 ^ 30)
    (hder : mt = xorFold T.tUT mu ^^^ xorFold T.tWT mw)
    (hpt : popCntGo 30 mt = r) :
    okTriple T.cls mu mw mt = true := by
  have h := all_pairs_true hchk
    (mem_masksOfWt 30 p mu hmu hpu) (mem_masksOfWt 30 q mw hmw hpw)
  rw [← hder] at h
  exact of_bne_or h (by rw [popCnt_eq hbt, hpt])

/-- Soundness, mode `2` (`(w,t)` swept, `u` in the derived `Ann`-coset;
the side file supplies the coset membership and the passing solvability
filters). -/
theorem checkSplit_sound_wt {T : SweepTables} {p q r : Nat}
    (hchk : checkSplit T (p, q, r, 2) = true)
    {mu mw mt : Nat} (hmw : mw < 2 ^ 30) (hmt : mt < 2 ^ 30)
    (hpw : popCntGo 30 mw = q) (hpt : popCntGo 30 mt = r)
    (hbu : mu < 2 ^ 30) (hpu : popCntGo 30 mu = p)
    (hcoset : ∃ a ∈ T.ann,
      mu = xorFold T.tP (xorFold T.tWC mw ^^^ xorFold T.tTC mt) ^^^ a)
    (hc : xorFold T.tWC mw ^^^ xorFold T.tTC mt < 2 ^ 30)
    (hln0 : popCntGo 30 (T.ln0 &&& (xorFold T.tWC mw ^^^ xorFold T.tTC mt)) % 2 = 0)
    (hln1 : popCntGo 30 (T.ln1 &&& (xorFold T.tWC mw ^^^ xorFold T.tTC mt)) % 2 = 0) :
    okTriple T.cls mu mw mt = true := by
  obtain ⟨a, ha, hadef⟩ := hcoset
  have h := all_pairs_true hchk
    (mem_masksOfWt 30 q mw hmw hpw) (mem_masksOfWt 30 r mt hmt hpt)
  set c := xorFold T.tWC mw ^^^ xorFold T.tTC mt with hcdef
  -- zeta/beta-reduce the sweep body by defeq restatement
  have h' : (parity (T.ln0 &&& c) || parity (T.ln1 &&& c) ||
      T.ann.all fun a' => popCnt (xorFold T.tP c ^^^ a') != p
        || okTriple T.cls (xorFold T.tP c ^^^ a') mw mt) = true := h
  have hb0 : T.ln0 &&& c < 2 ^ 30 :=
    lt_of_le_of_lt (Nat.and_le_right) hc
  have hb1 : T.ln1 &&& c < 2 ^ 30 :=
    lt_of_le_of_lt (Nat.and_le_right) hc
  have hpar0 : parity (T.ln0 &&& c) = false := by
    rw [parity, popCnt_eq hb0]
    simp [hln0]
  have hpar1 : parity (T.ln1 &&& c) = false := by
    rw [parity, popCnt_eq hb1]
    simp [hln1]
  rw [hpar0, hpar1] at h'
  simp only [Bool.false_or] at h'
  have hann : (popCnt (xorFold T.tP c ^^^ a) != p
      || okTriple T.cls (xorFold T.tP c ^^^ a) mw mt) = true :=
    List.all_eq_true.mp h' a ha
  rw [← hadef] at hann
  exact of_bne_or hann (by rw [popCnt_eq hbu, hpu])

/-- Soundness, mode `3` (`(u,w)` swept, `t` in the derived `Ann`-coset). -/
theorem checkSplit_sound_uwT {T : SweepTables} {p q r : Nat}
    (hchk : checkSplit T (p, q, r, 3) = true)
    {mu mw mt : Nat} (hmu : mu < 2 ^ 30) (hmw : mw < 2 ^ 30)
    (hpu : popCntGo 30 mu = p) (hpw : popCntGo 30 mw = q)
    (hbt : mt < 2 ^ 30) (hpt : popCntGo 30 mt = r)
    (hcoset : ∃ a ∈ T.annT,
      mt = xorFold T.tPT (xorFold T.tUC mu ^^^ xorFold T.tWC2 mw) ^^^ a)
    (hc : xorFold T.tUC mu ^^^ xorFold T.tWC2 mw < 2 ^ 30)
    (hln0 : popCntGo 30 (T.lnT0 &&& (xorFold T.tUC mu ^^^ xorFold T.tWC2 mw)) % 2 = 0)
    (hln1 : popCntGo 30 (T.lnT1 &&& (xorFold T.tUC mu ^^^ xorFold T.tWC2 mw)) % 2 = 0) :
    okTriple T.cls mu mw mt = true := by
  obtain ⟨a, ha, hadef⟩ := hcoset
  have h := all_pairs_true hchk
    (mem_masksOfWt 30 p mu hmu hpu) (mem_masksOfWt 30 q mw hmw hpw)
  set c := xorFold T.tUC mu ^^^ xorFold T.tWC2 mw with hcdef
  have h' : (parity (T.lnT0 &&& c) || parity (T.lnT1 &&& c) ||
      T.annT.all fun a' => popCnt (xorFold T.tPT c ^^^ a') != r
        || okTriple T.cls mu mw (xorFold T.tPT c ^^^ a')) = true := h
  have hb0 : T.lnT0 &&& c < 2 ^ 30 :=
    lt_of_le_of_lt (Nat.and_le_right) hc
  have hb1 : T.lnT1 &&& c < 2 ^ 30 :=
    lt_of_le_of_lt (Nat.and_le_right) hc
  have hpar0 : parity (T.lnT0 &&& c) = false := by
    rw [parity, popCnt_eq hb0]
    simp [hln0]
  have hpar1 : parity (T.lnT1 &&& c) = false := by
    rw [parity, popCnt_eq hb1]
    simp [hln1]
  rw [hpar0, hpar1] at h'
  simp only [Bool.false_or] at h'
  have hann : (popCnt (xorFold T.tPT c ^^^ a) != r
      || okTriple T.cls mu mw (xorFold T.tPT c ^^^ a)) = true :=
    List.all_eq_true.mp h' a ha
  rw [← hadef] at hann
  exact of_bne_or hann (by rw [popCnt_eq hbt, hpt])

/-! ## §4b  The join driver (two instances of a side, glued along `t`) -/

/-- Hoisted join data per classification entry: `(packed, t, pair-weight)`. -/
def joinPairs (cls : List Nat) : List (Nat × Nat × Nat) :=
  cls.map fun pk =>
    (pk, pk >>> 60, popCnt (pk &&& 1073741823) + popCnt ((pk >>> 30) &&& 1073741823))

/-- Packed 150-bit joined vector `(u₀, w₀, u₁, w₁, t)`. -/
def pack5 (pk0 pk1 : Nat) : Nat :=
  (pk0 &&& 1152921504606846975) ||| ((pk1 &&& 1152921504606846975) <<< 60)
    ||| ((pk0 >>> 60) <<< 120)

/-- Every `t`-compatible, weight-≤9 pair of classified triples joins to a
listed generator row — the per-side join obligation (`native_decide`). -/
def checkJoin (cls0 cls1 rows : List Nat) : Bool :=
  let j0 := joinPairs cls0
  let j1 := joinPairs cls1
  j0.all fun a =>
    j1.all fun b =>
      a.2.1 != b.2.1 || decide (9 < a.2.2 + b.2.2 + popCnt a.2.1)
        || rows.contains (pack5 a.1 b.1)

/-! ## §5  Packed-triple extraction (for the join layer) -/

lemma packTriple_lo {mu : Nat} (mw mt : Nat) (hmu : mu < 2 ^ 30) :
    packTriple mu mw mt % 2 ^ 30 = mu := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [packTriple, Nat.testBit_mod_two_pow, Nat.testBit_or,
    Nat.testBit_shiftLeft]
  by_cases hi : i < 30
  · have h30 : ¬(i ≥ 30) := by omega
    have h60 : ¬(i ≥ 60) := by omega
    simp [hi, h30, h60]
  · have hmub : mu.testBit i = false :=
      Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le hmu (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [hi, hmub]

lemma packTriple_mid {mu mw : Nat} (mt : Nat) (hmu : mu < 2 ^ 30)
    (hmw : mw < 2 ^ 30) :
    (packTriple mu mw mt >>> 30) % 2 ^ 30 = mw := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [packTriple, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
    Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hi : i < 30
  · have hmub : mu.testBit (30 + i) = false :=
      Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le hmu (Nat.pow_le_pow_right (by norm_num) (by omega)))
    have h30 : 30 + i ≥ 30 := by omega
    have h60 : ¬(30 + i ≥ 60) := by omega
    have hsub : 30 + i - 30 = i := by omega
    simp [hi, hmub, h30, h60, hsub]
  · have hmwb : mw.testBit i = false :=
      Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le hmw (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [hi, hmwb]

lemma packTriple_hi {mu mw : Nat} (mt : Nat) (hmu : mu < 2 ^ 30)
    (hmw : mw < 2 ^ 30) :
    packTriple mu mw mt >>> 60 = mt := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [packTriple, Nat.testBit_shiftRight, Nat.testBit_or,
    Nat.testBit_shiftLeft]
  have hmub : mu.testBit (60 + i) = false :=
    Nat.testBit_eq_false_of_lt
      (lt_of_lt_of_le hmu (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hmwb : mw.testBit (60 + i - 30) = false :=
    Nat.testBit_eq_false_of_lt
      (lt_of_lt_of_le hmw (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have h30 : 60 + i ≥ 30 := by omega
  have h60 : 60 + i ≥ 60 := by omega
  have hsub : 60 + i - 60 = i := by omega
  simp [hmub, hmwb, h30, h60, hsub]

/-- Four-way XOR regrouping. -/
lemma xor_xor_pair (a b x y : Nat) :
    (a ^^^ b) ^^^ (x ^^^ y) = (a ^^^ x) ^^^ (b ^^^ y) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases x.testBit i <;>
    cases y.testBit i <;> rfl

/-- **Predicate extension**: a XOR-closed predicate holding at the images
of `0` and the basis masks under a XOR-linear map holds on all images of
masks `< 2^n`.  (The membership analog of `linear_ext`; used for the
`Ann`-coset arguments.) -/
lemma linear_pred {F : Nat → Nat} {P : Nat → Prop} (n : Nat)
    (hFx : ∀ m₁ m₂, F (m₁ ^^^ m₂) = F m₁ ^^^ F m₂)
    (hP0 : P (F 0))
    (hPcl : ∀ a b, P a → P b → P (a ^^^ b))
    (hbit : ∀ i < n, P (F (1 <<< i))) :
    ∀ m < 2 ^ n, P (F m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · exact hP0
    · have hm0 : m ≠ 0 := by omega
      have hlog : m.log2 < n := by
        have h1 : 2 ^ m.log2 ≤ m := Nat.log2_self_le hm0
        by_contra hcon
        push Not at hcon
        have : 2 ^ n ≤ 2 ^ m.log2 := Nat.pow_le_pow_right (by norm_num) hcon
        omega
      set m' := m ^^^ 1 <<< m.log2 with hm'
      have hlt : m' < m := xor_top_bit_lt hm0
      have hm'2 : m' < 2 ^ n := lt_trans hlt hm
      have hsplit : m = m' ^^^ 1 <<< m.log2 := by
        rw [hm', Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      rw [hsplit, hFx]
      exact hPcl _ _ (ih m' hlt hm'2) (hbit _ hlog)

/-! ## §6  Parity functionals -/

lemma popCntGo_zero (f : Nat) : popCntGo f 0 = 0 := by
  induction f with
  | zero => rfl
  | succ f ih =>
    change (0 &&& 1) + popCntGo f (0 >>> 1) = 0
    simpa using ih

/-- Parity of a XOR is the mod-2 sum of parities (low `f` bits). -/
lemma popCntGo_xor_mod2 (f : Nat) : ∀ a b : Nat,
    popCntGo f (a ^^^ b) % 2 = (popCntGo f a + popCntGo f b) % 2 := by
  induction f with
  | zero => intro a b; simp [popCntGo]
  | succ f ih =>
    intro a b
    have hsh : (a ^^^ b) >>> 1 = a >>> 1 ^^^ b >>> 1 := by
      apply Nat.eq_of_testBit_eq
      intro i
      simp [Nat.testBit_shiftRight, Nat.testBit_xor]
    have hand : (a ^^^ b) &&& 1 = (a &&& 1) ^^^ (b &&& 1) :=
      Nat.and_xor_distrib_right
    change (((a ^^^ b) &&& 1) + popCntGo f ((a ^^^ b) >>> 1)) % 2
        = (((a &&& 1) + popCntGo f (a >>> 1)) + ((b &&& 1) + popCntGo f (b >>> 1))) % 2
    rw [hsh, hand]
    have hih := ih (a >>> 1) (b >>> 1)
    have h1 : a &&& 1 = a % 2 := Nat.and_one_is_mod a
    have h2 : b &&& 1 = b % 2 := Nat.and_one_is_mod b
    rw [h1, h2]
    rcases Nat.mod_two_eq_zero_or_one a with e1 | e1 <;>
      rcases Nat.mod_two_eq_zero_or_one b with e2 | e2 <;>
      · rw [e1, e2]
        first
        | (rw [Nat.zero_xor]; omega)
        | (rw [Nat.xor_zero]; omega)
        | (rw [Nat.xor_self]; omega)

/-- `{0,1}`-valued mod-2 sums are XORs. -/
private lemma mod2_add_eq_xor {x y : Nat} (hx : x < 2) (hy : y < 2) :
    (x + y) % 2 = x ^^^ y := by
  interval_cases x <;> interval_cases y <;> rfl

/-- A single set bit has popcount 1. -/
lemma popCntGo_one_shiftLeft {n i : Nat} (hi : i < n) :
    popCntGo n (1 <<< i) = 1 := by
  rw [popCntGo_eq_card]
  have hset : (Finset.range n).filter (fun j => (1 <<< i).testBit j) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton,
      Nat.testBit_shiftLeft, testBit_one', Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨-, hge, hsub⟩
      omega
    · rintro rfl
      exact ⟨hi, by omega, by omega⟩
  rw [hset, Finset.card_singleton]

/-- Tables with odd-weight columns give parity-preserving folds. -/
lemma parity_xorFold_odd {tbl : List Nat} {n : Nat}
    (hodd : ∀ i < n, popCntGo n (tbl.getD i 0) % 2 = 1) :
    ∀ m < 2 ^ n, popCntGo n (xorFold tbl m) % 2 = popCntGo n m % 2 := by
  have hF0 : popCntGo n (xorFold tbl 0) % 2 = 0 := by
    rw [xorFold_zero, popCntGo_zero]
  have hG0 : popCntGo n (0 : Nat) % 2 = 0 := by
    rw [popCntGo_zero]
  have hFx : ∀ m₁ m₂ : Nat, popCntGo n (xorFold tbl (m₁ ^^^ m₂)) % 2
      = popCntGo n (xorFold tbl m₁) % 2 ^^^ popCntGo n (xorFold tbl m₂) % 2 := by
    intro m₁ m₂
    rw [xorFold_xor, popCntGo_xor_mod2, Nat.add_mod,
      mod2_add_eq_xor (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))]
  have hGx : ∀ m₁ m₂ : Nat, popCntGo n (m₁ ^^^ m₂) % 2
      = popCntGo n m₁ % 2 ^^^ popCntGo n m₂ % 2 := by
    intro m₁ m₂
    rw [popCntGo_xor_mod2, Nat.add_mod,
      mod2_add_eq_xor (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))]
  have hbit : ∀ i < n, popCntGo n (xorFold tbl (1 <<< i)) % 2
      = popCntGo n (1 <<< i) % 2 := by
    intro i hi
    rw [xorFold_bit, hodd i hi, popCntGo_one_shiftLeft hi]
  exact linear_ext n hF0 hG0 hFx hGx hbit

/-- Left-null filters vanishing on the columns vanish on the image. -/
lemma parity_and_xorFold {tbl : List Nat} {ln : Nat} {n : Nat}
    (hb : ∀ i < n, popCntGo n (ln &&& tbl.getD i 0) % 2 = 0) :
    ∀ m < 2 ^ n, popCntGo n (ln &&& xorFold tbl m) % 2 = 0 := by
  have hF0 : popCntGo n (ln &&& xorFold tbl 0) % 2 = 0 := by
    rw [xorFold_zero, Nat.and_zero, popCntGo_zero]
  have hFx : ∀ m₁ m₂ : Nat, popCntGo n (ln &&& xorFold tbl (m₁ ^^^ m₂)) % 2
      = popCntGo n (ln &&& xorFold tbl m₁) % 2
        ^^^ popCntGo n (ln &&& xorFold tbl m₂) % 2 := by
    intro m₁ m₂
    rw [xorFold_xor, Nat.and_xor_distrib_left, popCntGo_xor_mod2, Nat.add_mod,
      mod2_add_eq_xor (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))]
  have hbit : ∀ i < n, popCntGo n (ln &&& xorFold tbl (1 <<< i)) % 2 = 0 := by
    intro i hi
    rw [xorFold_bit]
    exact hb i hi
  exact linear_ext (G := fun _ => 0) n hF0 rfl hFx
    (fun _ _ => by simp) hbit

/-! ## §7  Composite-fold transfer (basis facts → map identities) -/

/-- Basis composition facts extend to all masks: `t2 ∘ t1 = t3`. -/
lemma xorFold_comp {t1 t2 t3 : List Nat} {n : Nat}
    (hb : ∀ i < n, xorFold t2 (t1.getD i 0) = t3.getD i 0) :
    ∀ m < 2 ^ n, xorFold t2 (xorFold t1 m) = xorFold t3 m := by
  have hFx : ∀ m₁ m₂ : Nat, xorFold t2 (xorFold t1 (m₁ ^^^ m₂))
      = xorFold t2 (xorFold t1 m₁) ^^^ xorFold t2 (xorFold t1 m₂) := by
    intro m₁ m₂
    rw [xorFold_xor, xorFold_xor]
  have hbit : ∀ i < n, xorFold t2 (xorFold t1 (1 <<< i))
      = xorFold t3 (1 <<< i) := by
    intro i hi
    rw [xorFold_bit, xorFold_bit]
    exact hb i hi
  exact linear_ext n (by simp) (by simp) hFx (xorFold_xor t3) hbit

/-- Basis inverse facts extend to all masks: `t2 ∘ t1 = id`. -/
lemma xorFold_comp_id {t1 t2 : List Nat} {n : Nat}
    (hb : ∀ i < n, xorFold t2 (t1.getD i 0) = 1 <<< i) :
    ∀ m < 2 ^ n, xorFold t2 (xorFold t1 m) = m := by
  have hFx : ∀ m₁ m₂ : Nat, xorFold t2 (xorFold t1 (m₁ ^^^ m₂))
      = xorFold t2 (xorFold t1 m₁) ^^^ xorFold t2 (xorFold t1 m₂) := by
    intro m₁ m₂
    rw [xorFold_xor, xorFold_xor]
  have hbit : ∀ i < n, xorFold t2 (xorFold t1 (1 <<< i)) = 1 <<< i := by
    intro i hi
    rw [xorFold_bit]
    exact hb i hi
  exact linear_ext (G := fun m => m) n (by simp) rfl hFx (fun _ _ => rfl) hbit

/-- Identity-column tables fold to the identity. -/
lemma xorFold_id {t1 : List Nat} {n : Nat}
    (hb : ∀ i < n, t1.getD i 0 = 1 <<< i) :
    ∀ m < 2 ^ n, xorFold t1 m = m := by
  have hbit : ∀ i < n, xorFold t1 (1 <<< i) = 1 <<< i := by
    intro i hi
    rw [xorFold_bit]
    exact hb i hi
  exact linear_ext (G := fun m => m) n (by simp) rfl (xorFold_xor t1)
    (fun _ _ => rfl) hbit

/-- Folding a table whose columns lie in a XOR-closed list stays in it. -/
lemma xorFold_mem_closed {ann : List Nat} (h0 : (0 : Nat) ∈ ann)
    (hcl : ∀ a ∈ ann, ∀ b ∈ ann, a ^^^ b ∈ ann) :
    ∀ {tbl : List Nat}, (∀ c ∈ tbl, c ∈ ann) → ∀ m, xorFold tbl m ∈ ann := by
  intro tbl
  induction tbl with
  | nil => intro _ m; simpa using h0
  | cons c rest ih =>
    intro hc m
    change (if m &&& 1 = 1 then c else 0) ^^^ xorFold rest (m >>> 1) ∈ ann
    refine hcl _ ?_ _ (ih (fun x hx => hc x (List.mem_cons_of_mem _ hx)) _)
    split
    · exact hc c List.mem_cons_self
    · exact h0

/-! ## §8  Classification and join consumption -/

private lemma or3_eq_zero {a b c : Nat} (h : a ||| b ||| c = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have hbit : ∀ i, a.testBit i = false ∧ b.testBit i = false
      ∧ c.testBit i = false := by
    intro i
    have h0 := congrArg (fun x => x.testBit i) h
    simp only [Nat.testBit_or, Nat.zero_testBit, Bool.or_eq_false_iff] at h0
    exact ⟨h0.1.1, h0.1.2, h0.2⟩
  refine ⟨Nat.eq_of_testBit_eq fun i => ?_, Nat.eq_of_testBit_eq fun i => ?_,
    Nat.eq_of_testBit_eq fun i => ?_⟩
  · rw [(hbit i).1, Nat.zero_testBit]
  · rw [(hbit i).2.1, Nat.zero_testBit]
  · rw [(hbit i).2.2, Nat.zero_testBit]

/-- `okTriple = true` means the triple is zero or classified. -/
lemma okTriple_cases {cls : List Nat} {mu mw mt : Nat}
    (h : okTriple cls mu mw mt = true) :
    (mu = 0 ∧ mw = 0 ∧ mt = 0) ∨ packTriple mu mw mt ∈ cls := by
  rcases Bool.or_eq_true_iff.mp h with h' | h'
  · left
    exact or3_eq_zero (by simpa using h')
  · right
    simpa using h'

/-- **Join soundness**: two classified triples sharing `t` with total weight
`≤ 9` pack to a listed generator row. -/
theorem checkJoin_sound {cls0 cls1 rows : List Nat}
    (hchk : checkJoin cls0 cls1 rows = true)
    {mu0 mw0 mu1 mw1 mt : Nat}
    (hu0 : mu0 < 2 ^ 30) (hw0 : mw0 < 2 ^ 30)
    (hu1 : mu1 < 2 ^ 30) (hw1 : mw1 < 2 ^ 30) (hmt : mt < 2 ^ 30)
    (h0 : packTriple mu0 mw0 mt ∈ cls0) (h1 : packTriple mu1 mw1 mt ∈ cls1)
    (hwt : popCntGo 30 mu0 + popCntGo 30 mw0 + popCntGo 30 mu1
        + popCntGo 30 mw1 + popCntGo 30 mt ≤ 9) :
    pack5 (packTriple mu0 mw0 mt) (packTriple mu1 mw1 mt) ∈ rows := by
  set pk0 := packTriple mu0 mw0 mt with hpk0
  set pk1 := packTriple mu1 mw1 mt with hpk1
  have hj0 : (pk0, pk0 >>> 60,
      popCnt (pk0 &&& 1073741823) + popCnt ((pk0 >>> 30) &&& 1073741823))
      ∈ joinPairs cls0 := List.mem_map_of_mem h0
  have hj1 : (pk1, pk1 >>> 60,
      popCnt (pk1 &&& 1073741823) + popCnt ((pk1 >>> 30) &&& 1073741823))
      ∈ joinPairs cls1 := List.mem_map_of_mem h1
  have h := List.all_eq_true.mp (List.all_eq_true.mp hchk _ hj0) _ hj1
  have h' : ((pk0 >>> 60) != (pk1 >>> 60)
      || decide (9 < (popCnt (pk0 &&& 1073741823)
            + popCnt ((pk0 >>> 30) &&& 1073741823)
          + (popCnt (pk1 &&& 1073741823)
            + popCnt ((pk1 >>> 30) &&& 1073741823))
          + popCnt (pk0 >>> 60)))
      || rows.contains (pack5 pk0 pk1)) = true := h
  have hand : ∀ x : Nat, x &&& 1073741823 = x % 2 ^ 30 := by
    intro x
    have h30 : (1073741823 : Nat) = 2 ^ 30 - 1 := by norm_num
    rw [h30, Nat.and_two_pow_sub_one_eq_mod]
  have ht0 : pk0 >>> 60 = mt := packTriple_hi mt hu0 hw0
  have ht1 : pk1 >>> 60 = mt := packTriple_hi mt hu1 hw1
  have hwsum : (popCnt (pk0 &&& 1073741823) + popCnt ((pk0 >>> 30) &&& 1073741823)
      + (popCnt (pk1 &&& 1073741823) + popCnt ((pk1 >>> 30) &&& 1073741823))
      + popCnt (pk0 >>> 60)) ≤ 9 := by
    rw [ht0, hand pk0, hand pk1, hand (pk0 >>> 30), hand (pk1 >>> 30),
      packTriple_lo mw0 mt hu0, packTriple_lo mw1 mt hu1,
      packTriple_mid mt hu0 hw0, packTriple_mid mt hu1 hw1,
      popCnt_eq hu0, popCnt_eq hu1, popCnt_eq hw0, popCnt_eq hw1,
      popCnt_eq hmt]
    omega
  rcases Bool.or_eq_true_iff.mp h' with h'' | hcont
  · exfalso
    rcases Bool.or_eq_true_iff.mp h'' with hb | hd
    · rw [ht0, ht1] at hb
      simp at hb
    · exact absurd (of_decide_eq_true hd) (by omega)
  · simpa using hcont

/-! ## §9  `pack5` extraction (for the row-reconstruction step) -/

private lemma m60_testBit (i : Nat) :
    (1152921504606846975 : Nat).testBit i = decide (i < 60) := by
  have h : (1152921504606846975 : Nat) = 2 ^ 60 - 1 := by norm_num
  rw [h, Nat.testBit_two_pow_sub_one]

lemma pack5_mod (pk0 pk1 : Nat) : pack5 pk0 pk1 % 2 ^ 30 = pk0 % 2 ^ 30 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [pack5, Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_and,
    Nat.testBit_shiftLeft, m60_testBit]
  by_cases hi : i < 30
  · have h60 : ¬(i ≥ 60) := by omega
    have h120 : ¬(i ≥ 120) := by omega
    have hlt : i < 60 := by omega
    simp [hi, h60, h120, hlt]
  · simp [hi]

lemma pack5_shr30_mod (pk0 pk1 : Nat) :
    (pack5 pk0 pk1 >>> 30) % 2 ^ 30 = (pk0 >>> 30) % 2 ^ 30 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [pack5, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
    Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, m60_testBit]
  by_cases hi : i < 30
  · have h60 : ¬(30 + i ≥ 60) := by omega
    have h120 : ¬(30 + i ≥ 120) := by omega
    have hlt : 30 + i < 60 := by omega
    simp [hi, h60, h120, hlt]
  · simp [hi]

lemma pack5_shr60_mod (pk0 pk1 : Nat) :
    (pack5 pk0 pk1 >>> 60) % 2 ^ 30 = pk1 % 2 ^ 30 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [pack5, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
    Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, m60_testBit]
  by_cases hi : i < 30
  · have hm : ¬(60 + i < 60) := by omega
    have h60 : 60 + i ≥ 60 := by omega
    have h120 : ¬(60 + i ≥ 120) := by omega
    have hsub : 60 + i - 60 = i := by omega
    have hlt : i < 60 := by omega
    simp [hi, hm, h60, h120, hsub, hlt]
  · simp [hi]

lemma pack5_shr90_mod (pk0 pk1 : Nat) :
    (pack5 pk0 pk1 >>> 90) % 2 ^ 30 = (pk1 >>> 30) % 2 ^ 30 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [pack5, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
    Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, m60_testBit]
  by_cases hi : i < 30
  · have hm : ¬(90 + i < 60) := by omega
    have h60 : 90 + i ≥ 60 := by omega
    have h120 : ¬(90 + i ≥ 120) := by omega
    have hsub : 90 + i - 60 = 30 + i := by omega
    have hlt : 30 + i < 60 := by omega
    simp [hi, hm, h60, h120, hsub, hlt]
  · simp [hi]

lemma pack5_shr120 (pk0 pk1 : Nat) :
    pack5 pk0 pk1 >>> 120 = pk0 >>> 60 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [pack5, Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_and,
    Nat.testBit_shiftLeft, m60_testBit]
  have hm : ¬(120 + i < 60) := by omega
  have h60 : 120 + i ≥ 60 := by omega
  have h120 : 120 + i ≥ 120 := by omega
  have hsub60 : 120 + i - 60 = 60 + i := by omega
  have hm2 : ¬(60 + i < 60) := by omega
  have hsub120 : 120 + i - 120 = i := by omega
  simp [hm, h60, h120, hsub60, hm2, hsub120]

end M150
end LP
end Homological
end Stabilizer
end Quantum
