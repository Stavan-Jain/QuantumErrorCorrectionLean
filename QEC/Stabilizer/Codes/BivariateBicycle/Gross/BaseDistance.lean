/-
# Phase 2 (tier 1): d(base) ≥ 6 — discharging `BaseDistanceGe6`

The small-cycle theorem for the bb72 base complex, in its strong form:
**every nonzero 1-cycle has weight ≥ 6** (A4 Theorem A).  Consequences
assembled here:

* `base_distance_ge_6 : BaseDistanceGe6` — the Phase-1 hypothesis (A) is a
  theorem;
* `base_chain_distance_eq_6` — chain-level d(base) = 6 (Corollary A′; the
  weight-6 witness is `u*` from `Witness.lean`);
* **unconditional d(gross) ≥ 6** at the chain, dual-chain, and Pauli levels
  (A4 Theorem B): the safe and nonzero-dangerous sectors bound by 6 via the
  strong small-cycle theorem applied to `p(v)`, and the `b = 0` sector by 12
  via the Phase-1 rung.

## Proof shape (tier 1: verified-finite leaf, analytic frame)

Two analytic inputs are formalized here: the translation symmetry (`∂₁` is
translation-equivariant, so any small cycle can be normalized to put a
support point at group-origin) and **the parity lemma (PAR)** of A4 §4 —
cycles have even weight, by applying the augmentation `ε` to the cycle
condition (`ε(A) = ε(B) = 1`).  Parity kills all odd-weight supports, so
the normalized finite sweep only covers `((0,0), b)` plus exactly 1 or 3
further qubits — `2·(C(71,1) + C(71,3)) ≈ 1.2·10⁵` cases, swept by kernel
`decide` (`smallCycleCheck_*`) with the boundary evaluated
through the sparse syndrome form `syndAt` (the hand-proven bridge
`bbBoundary1Fn_indicator` turns `∂₁(χ_S) = 0` into 36 few-term sums; the
weight-4 sweep runs on packed-`Nat` syndrome masks with a perfect-hash
membership refuter, bridged back through `termAt_eq_testBit`).
Replacing this finite leaf with the per-split CRT-engine analysis of
A4 §§3–4 (the fully analytic Theorem A) is the tier-2 upgrade; the
statement `base_distance_ge_6` is already in its final form, so the
upgrade is invisible downstream.

## Convention bridge (lab notes → repo)

Repo convention: `∂₂ f = (A⋆f | B⋆f)`, `∂₁ c = B⋆c_L + A⋆c_R`; cycle
condition `B⋆v_L = A⋆v_R`.  **Repo-left = lab-right.**
-/

import QEC.Stabilizer.Codes.BivariateBicycle.Gross.Assembly

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open scoped BigOperators

/-! ## Support plumbing -/

/-- A `ZMod 2` chain is the indicator function of its support. -/
lemma eq_indicator_support {I : Type} [Fintype I] [DecidableEq I]
    (u : I → ZMod 2) :
    u = fun p => if p ∈ (Finset.univ.filter fun q => u q ≠ 0) then 1 else 0 := by
  have hdichot : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  funext p
  by_cases h : u p = 0
  · simp [h]
  · simp [hdichot _ h]

/-- Translation preserves support size (1-chains over the base group). -/
lemma card_support_translate1 (c : BaseGroup) (u : BaseGroup × Fin 2 → ZMod 2) :
    (Finset.univ.filter fun p => translate1 c u p ≠ 0).card
      = (Finset.univ.filter fun p => u p ≠ 0).card :=
  card_filter_comp_equiv ((Equiv.addRight c).prodCongr (Equiv.refl (Fin 2)))
    (fun p => u p ≠ 0)

/-! ## The sparse syndrome form

For an indicator chain `χ_S`, the boundary `∂₁(χ_S)(h)` is the
`|S|`-term sum `syndAt S h` — far cheaper to evaluate than the
convolution form during the kernel `decide` sweep. -/

/-- The syndrome contribution of a single qubit at a check position. -/
def termAt (q : BaseGroup × Fin 2) (h : BaseGroup) : ZMod 2 :=
  if q.2 = 0 then baseB (h - q.1) else baseA (h - q.1)

/-- Sparse syndrome of a support set at a check position. -/
def syndAt (S : Finset (BaseGroup × Fin 2)) (h : BaseGroup) : ZMod 2 :=
  ∑ q ∈ S, termAt q h

/-- `∂₁` of a point mass, in either block. -/
lemma bbBoundary1Fn_single_point (q : BaseGroup × Fin 2) (h : BaseGroup) :
    bbBoundary1Fn baseA baseB (Pi.single q 1) h = termAt q h := by
  obtain ⟨g, j⟩ := q
  by_cases hj : j = 0
  · subst hj
    exact bbBoundary1Fn_single_left baseA baseB g h
  · have hj1 : j = 1 := by omega
    subst hj1
    exact bbBoundary1Fn_single_right baseA baseB g h

/-- Indicator of `insert` decomposes as indicator plus a point mass. -/
lemma indicator_insert {I : Type} [DecidableEq I] (a : I) (S : Finset I)
    (ha : a ∉ S) :
    (fun p => if p ∈ insert a S then (1 : ZMod 2) else 0)
      = (fun p => if p ∈ S then 1 else 0) + Pi.single a 1 := by
  funext p
  by_cases hp : p = a
  · subst hp
    simp [Finset.mem_insert, ha]
  · simp [Finset.mem_insert, hp]

/-- **The sparse-syndrome bridge**: on indicator chains, `∂₁` evaluates to
`syndAt`. -/
lemma bbBoundary1Fn_indicator (S : Finset (BaseGroup × Fin 2)) :
    ∀ h : BaseGroup,
      bbBoundary1Fn baseA baseB (fun q => if q ∈ S then 1 else 0) h
        = syndAt S h := by
  classical
  induction S using Finset.induction with
  | empty =>
      intro h
      have hzero : (fun q : BaseGroup × Fin 2 =>
          if q ∈ (∅ : Finset (BaseGroup × Fin 2)) then (1 : ZMod 2) else 0)
          = 0 := by
        funext q
        simp
      rw [hzero]
      simp [bbBoundary1Fn, leftHalf, rightHalf, conv_apply, syndAt]
  | insert a S ha ih =>
      intro h
      rw [indicator_insert a S ha, bbBoundary1Fn_add, Pi.add_apply, ih h,
        bbBoundary1Fn_single_point]
      simp only [syndAt]
      rw [Finset.sum_insert ha]
      ring

/-! ## The parity lemma (PAR)

Every cycle has even weight: applying the augmentation `ε(w) = Σ_g w(g)`
to `B⋆u_L + A⋆u_R = 0` gives `ε(u_L) + ε(u_R) = 0` since
`ε(A) = ε(B) = 1`.  This kills all odd-weight supports analytically, so the
finite sweep below only needs the (normalized) weight-2 and weight-4
configurations. -/

/-- The augmentation is multiplicative on convolutions. -/
lemma sum_conv {G : Type} [Fintype G] [AddCommGroup G] (a b : G → ZMod 2) :
    ∑ g : G, (a ⋆ b) g = (∑ h : G, a h) * (∑ g : G, b g) := by
  simp only [conv_apply]
  rw [Finset.sum_comm]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  exact Equiv.sum_comp (Equiv.subRight h) b

/-- **(PAR)**: cycles of the base complex have zero total parity. -/
lemma cycle_total_parity (u : BaseGroup × Fin 2 → ZMod 2)
    (hcyc : bbBoundary1Fn baseA baseB u = 0) :
    ∑ p : BaseGroup × Fin 2, u p = 0 := by
  have h0 : ∑ g : BaseGroup, bbBoundary1Fn baseA baseB u g = 0 := by
    rw [hcyc]
    simp
  have hexp : ∑ g : BaseGroup, bbBoundary1Fn baseA baseB u g
      = (∑ h : BaseGroup, baseB h) * (∑ g : BaseGroup, leftHalf u g)
        + (∑ h : BaseGroup, baseA h) * (∑ g : BaseGroup, rightHalf u g) := by
    rw [show (fun g => bbBoundary1Fn baseA baseB u g)
        = fun g => (baseB ⋆ leftHalf u) g + (baseA ⋆ rightHalf u) g
      from rfl]
    rw [Finset.sum_add_distrib, sum_conv, sum_conv]
  have hA : (∑ h : BaseGroup, baseA h) = 1 := by decide +kernel
  have hB : (∑ h : BaseGroup, baseB h) = 1 := by decide +kernel
  rw [hexp, hA, hB, one_mul, one_mul] at h0
  rw [Fintype.sum_prod_type]
  calc ∑ g : BaseGroup, ∑ j : Fin 2, u (g, j)
      = ∑ g : BaseGroup, (u (g, 0) + u (g, 1)) := by
        refine Finset.sum_congr rfl fun g _ => ?_
        exact Fin.sum_univ_two _
    _ = (∑ g : BaseGroup, leftHalf u g) + (∑ g : BaseGroup, rightHalf u g) :=
        Finset.sum_add_distrib
    _ = 0 := h0

/-- Cycles have even weight. -/
lemma cycle_weight_even (u : BaseGroup × Fin 2 → ZMod 2)
    (hcyc : bbBoundary1Fn baseA baseB u = 0) :
    (Finset.univ.filter fun p => u p ≠ 0).card % 2 = 0 := by
  have hdichot : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  have hcast : (((Finset.univ.filter fun p => u p ≠ 0).card : ℕ) : ZMod 2)
      = ∑ p : BaseGroup × Fin 2, u p := by
    rw [← Finset.sum_filter_ne_zero Finset.univ]
    rw [Finset.sum_congr rfl fun p hp => hdichot (u p)
      (Finset.mem_filter.mp hp).2]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have h0 := cycle_total_parity u hcyc
  rw [← hcast] at h0
  have heven := ZMod.natCast_eq_zero_iff_even.mp h0
  exact Nat.even_iff.mp heven

/-! ## The normalized finite check

Every normalized configuration — `((0,0), b)` plus one or three further
qubits (by (PAR) those are the only sizes a small cycle could have) — has a
nonzero syndrome.  Quantified over plain tuples (no `Finset.powersetCard`
in the decided statement: its compiled decision procedure is prohibitively
expensive), so repeated/colliding tuples are allowed; the statements remain
true since any such chain is nonzero of weight ≤ 4. -/

/-- No normalized weight-2 chain is a cycle. -/
lemma smallCycleCheck_two : ∀ b : Fin 2, ∀ q : BaseGroup × Fin 2,
    q ≠ (((0, 0) : BaseGroup), b) →
    ∃ h : BaseGroup,
      termAt ((((0, 0) : BaseGroup)), b) h + termAt q h ≠ 0 := by
  decide +kernel

/-! ### Packed-mask engine for the weight-4 sweep

The `2·72³ ≈ 7.5·10⁵` weight-4 configurations are too many for a kernel
`decide` through `ZMod` arithmetic, so the sweep runs on GMP-fast `Nat`
bit operations instead: each qubit's three-check syndrome is a 36-bit mask
(packed into the single literal `synTable`), the four-qubit syndrome is the
XOR of four masks, and the innermost quantifier disappears —
`m₀ ^^^ m₁ ^^^ m₂ ^^^ m₃ = 0` forces `m₃ = m₀ ^^^ m₁ ^^^ m₂`, so it
suffices that the XOR of three masks never *is* another qubit's mask,
checked by a perfect-hash membership refuter (`synInvTable`; modulus 351 is
injective on the 72 masks).  `termAt_eq_testBit` (a small kernel `decide`)
bridges each mask bit back to `termAt`, keeping the public statement of
`smallCycleCheck_four` unchanged. -/

/-- Qubit index `(g, j) ↦ (6·g₁ + g₂)·2 + j ∈ [0, 72)`. -/
private def encQubit (q : BaseGroup × Fin 2) : Nat :=
  (q.1.1.val * 6 + q.1.2.val) * 2 + q.2.val

/-- Check index `h ↦ 6·h₁ + h₂ ∈ [0, 36)`. -/
private def encCheck (h : BaseGroup) : Nat := h.1.val * 6 + h.2.val

/-- Inverse of `encCheck` on `[0, 36)`. -/
private def decCheck (k : Nat) : BaseGroup :=
  (((k / 6 : ℕ) : ZMod 6), ((k % 6 : ℕ) : ZMod 6))

/-- Packed syndrome table: bit `36·i + k` is `termAt` of qubit index `i` at
check index `k` (72 lanes of 36 bits; certified by `termAt_eq_testBit`). -/
private def synTable : Nat :=
  0x0c0020000100000820840010000080000410c00008000040000208600004000800000104 <<< 2304 +
  0x300002000400000082180001000200000041003000800804000020021000400402000010 <<< 2016 +
  0x03000020020100000801800010012000000400c000080090000002006000040048000001 <<< 1728 +
  0x0000c0020820100000000840010410080000000c00008208040000000600004104800000 <<< 1440 +
  0x000300002082400000000180001041200000800003000020804000400021000010402000 <<< 1152 +
  0x20003000000820100010001800000412000008000c000002090000040006000001048000 <<< 864 +
  0x0200000c0000820100010000840000410080008000c00000208040004000600000104800 <<< 576 +
  0x002000300000082400001000180000041200000800003000020804000400021000010402 <<< 288 +
  0x00020003000000820100010001800000412000008000c000002090000040006000001048

/-- The 36-bit syndrome mask of qubit index `i`. -/
private def synMask (i : Nat) : Nat := (synTable >>> (36 * i)) % 2 ^ 36

private lemma synMask_lt (i : Nat) : synMask i < 2 ^ 36 :=
  Nat.mod_lt _ (Nat.two_pow_pos 36)

/-- Perfect-hash inverse table: byte `synMask i % 351` holds `i + 1`, and
`0` marks "no mask hashes here". -/
private def synInvTable : Nat :=
  0x000000000000000000434500470000000d004839000000000f00000000003b0000080000 <<< 2592 +
  0x0000000011000000000000000000000001000002001000000000003c0000003500000000 <<< 2304 +
  0x0700000000000036000000000000002c0000003e00000000030000000000044600001200 <<< 2016 +
  0x000000000000000000000000000a000000002b15002f00000025003009000000003f0000 <<< 1728 +
  0x000000230000380000000000002900000000000000000000001900001a00400000000000 <<< 1440 +
  0x240000000500000000370000000000000600000000000000140000000e00000000330000 <<< 1152 +
  0x000000341600002a00000000000000000000000000002200000000132d00170000003d00 <<< 864 +
  0x1821000000002700000000000b0000200000000000004100000000000000000000003100 <<< 576 +
  0x0032002800000000000c0000001d000000001f0000000000001e00000000000000440000 <<< 288 +
  0x0026000000001b00000000001c2e00004200000000000000000000000000003a00000000

/-- Membership refuter: `synNotHit b v = true` certifies that no mask
`synMask i` with `i < 72`, `i ≠ b` equals `v` (via `synInv_sound`). -/
private def synNotHit (b v : Nat) : Bool :=
  let e := (synInvTable >>> (8 * (v % 351))) &&& 255
  (e == 0) || (e == b + 1) || (synMask (e - 1) != v)

/-- Bool core of the weight-4 sweep, one shard per origin index `b`. -/
private def sweepOK (b : Nat) : Bool :=
  (List.range 72).all fun i₁ =>
    (i₁ == b) ||
    (List.range 72).all fun i₂ =>
      (i₂ == b) || synNotHit b (synMask b ^^^ synMask i₁ ^^^ synMask i₂)

private lemma sweepOK_zero : sweepOK 0 = true := by decide +kernel

private lemma sweepOK_one : sweepOK 1 = true := by decide +kernel

/-- Lookup soundness: each mask hashes to its own slot of `synInvTable`. -/
private lemma synInv_sound : ∀ i < 72,
    (synInvTable >>> (8 * (synMask i % 351))) &&& 255 = i + 1 := by
  decide +kernel

private lemma nat_eq_of_xor_eq_zero {x y : Nat} (h : x ^^^ y = 0) : x = y := by
  have h1 : (x ^^^ y) ^^^ y = y := by rw [h, Nat.zero_xor]
  rwa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at h1

/-- The mask-level sweep, back in quantified form. -/
private lemma mask_sweep (b i₁ i₂ i₃ : Nat) (hb : b < 2) (h₁ : i₁ < 72)
    (h₂ : i₂ < 72) (h₃ : i₃ < 72) :
    i₁ = b ∨ i₂ = b ∨ i₃ = b ∨
    synMask b ^^^ synMask i₁ ^^^ synMask i₂ ^^^ synMask i₃ ≠ 0 := by
  have hOK : sweepOK b = true := by
    have hb2 : b = 0 ∨ b = 1 := by omega
    rcases hb2 with rfl | rfl
    · exact sweepOK_zero
    · exact sweepOK_one
  simp only [sweepOK, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq] at hOK
  rcases hOK i₁ h₁ with h | hOK1
  · exact Or.inl h
  rcases hOK1 i₂ h₂ with h | hHit
  · exact Or.inr (Or.inl h)
  by_cases hib : i₃ = b
  · exact Or.inr (Or.inr (Or.inl hib))
  refine Or.inr (Or.inr (Or.inr fun h0 => ?_))
  have hv : synMask b ^^^ synMask i₁ ^^^ synMask i₂ = synMask i₃ :=
    nat_eq_of_xor_eq_zero h0
  rw [hv] at hHit
  have hsound := synInv_sound i₃ h₃
  simp only [synNotHit, Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at hHit
  rw [hsound] at hHit
  rcases hHit with (hc | hc) | hc
  · omega
  · exact hib (by omega)
  · rw [Nat.add_sub_cancel] at hc
    exact hc rfl

/-- The `termAt` ↔ mask-bit bridge. -/
private lemma termAt_eq_testBit : ∀ q : BaseGroup × Fin 2, ∀ h : BaseGroup,
    termAt q h
      = if (synMask (encQubit q)).testBit (encCheck h) then 1 else 0 := by
  decide +kernel

private lemma encQubit_lt : ∀ q : BaseGroup × Fin 2, encQubit q < 72 := by
  decide +kernel

private lemma encQubit_origin : ∀ b : Fin 2,
    encQubit (((0, 0) : BaseGroup), b) = b.val := by
  decide +kernel

private lemma eq_origin_of_encQubit_eq : ∀ b : Fin 2, ∀ q : BaseGroup × Fin 2,
    encQubit q = b.val → q = (((0, 0) : BaseGroup), b) := by
  decide +kernel

private lemma encCheck_decCheck : ∀ k < 36, encCheck (decCheck k) = k := by
  decide +kernel

private lemma testBit_false_of_lt {x n i : Nat} (hx : x < 2 ^ n) (hi : n ≤ i) :
    x.testBit i = false :=
  Nat.testBit_lt_two_pow
    (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hi))

/-- A nonzero `Nat` with only-zero bits at positions `≥ n` has a set bit
below `n`. -/
private lemma exists_testBit_of_ne_zero {n x : Nat}
    (hhigh : ∀ i, n ≤ i → x.testBit i = false) (hne : x ≠ 0) :
    ∃ k, k < n ∧ x.testBit k = true := by
  by_contra hcon
  push Not at hcon
  apply hne
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.zero_testBit]
  by_cases hi : i < n
  · cases hb : x.testBit i with
    | false => rfl
    | true => exact absurd hb (hcon i hi)
  · exact hhigh i (Nat.le_of_not_lt hi)

private lemma sum_ne_zero_of_xor : ∀ b₀ b₁ b₂ b₃ : Bool,
    (((b₀ ^^ b₁) ^^ b₂) ^^ b₃) = true →
    ((if b₀ then 1 else 0) + (if b₁ then 1 else 0) + (if b₂ then 1 else 0)
      + (if b₃ then 1 else 0) : ZMod 2) ≠ 0 := by
  decide

/-- No normalized weight-≤4 chain containing the origin qubit is a cycle
(disjunctive form: the hypotheses `qᵢ ≠ origin` are folded into the
conclusion; proven by the packed-mask engine — `mask_sweep` plus the
`termAt_eq_testBit` bridge, with `exists_testBit_of_ne_zero` extracting the
witness check position from the nonzero XOR mask). -/
lemma smallCycleCheck_four : ∀ b : Fin 2, ∀ q₁ q₂ q₃ : BaseGroup × Fin 2,
    q₁ = (((0, 0) : BaseGroup), b) ∨ q₂ = (((0, 0) : BaseGroup), b) ∨
    q₃ = (((0, 0) : BaseGroup), b) ∨
    ∃ h : BaseGroup,
      termAt ((((0, 0) : BaseGroup)), b) h + termAt q₁ h + termAt q₂ h
        + termAt q₃ h ≠ 0 := by
  intro b q₁ q₂ q₃
  rcases mask_sweep b.val (encQubit q₁) (encQubit q₂) (encQubit q₃) b.isLt
      (encQubit_lt q₁) (encQubit_lt q₂) (encQubit_lt q₃) with h | h | h | hxor
  · exact Or.inl (eq_origin_of_encQubit_eq b q₁ h)
  · exact Or.inr (Or.inl (eq_origin_of_encQubit_eq b q₂ h))
  · exact Or.inr (Or.inr (Or.inl (eq_origin_of_encQubit_eq b q₃ h)))
  · refine Or.inr (Or.inr (Or.inr ?_))
    obtain ⟨k, hk, hbit⟩ := exists_testBit_of_ne_zero (n := 36)
      (fun i hi => by
        simp only [Nat.testBit_xor]
        rw [testBit_false_of_lt (synMask_lt _) hi,
          testBit_false_of_lt (synMask_lt _) hi,
          testBit_false_of_lt (synMask_lt _) hi,
          testBit_false_of_lt (synMask_lt _) hi]
        rfl)
      hxor
    refine ⟨decCheck k, ?_⟩
    have hb0 := termAt_eq_testBit (((0, 0) : BaseGroup), b) (decCheck k)
    have hb1 := termAt_eq_testBit q₁ (decCheck k)
    have hb2 := termAt_eq_testBit q₂ (decCheck k)
    have hb3 := termAt_eq_testBit q₃ (decCheck k)
    rw [encQubit_origin b] at hb0
    rw [encCheck_decCheck k hk] at hb0 hb1 hb2 hb3
    rw [hb0, hb1, hb2, hb3]
    apply sum_ne_zero_of_xor
    simpa only [Nat.testBit_xor] using hbit

/-! ## The small-cycle theorem (strong form) -/

/-- **Small-cycle theorem** (A4 Theorem A, repo form): every nonzero 1-cycle
of the bb72 base complex has weight ≥ 6 — boundaries included. -/
theorem base_cycle_weight_ge_6
    (u : BaseGroup × Fin 2 → ZMod 2)
    (hcyc : bbBoundary1Fn baseA baseB u = 0) (hne : u ≠ 0) :
    6 ≤ (Finset.univ.filter fun p => u p ≠ 0).card := by
  by_contra hlt
  push Not at hlt
  -- a support point
  have hex : ∃ p, u p ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (funext hall)
  obtain ⟨p, hp⟩ := hex
  -- normalize its group coordinate to the origin
  have hp' : translate1 p.1 u ((0, 0), p.2) ≠ 0 := by
    change u ((0 : BaseGroup) + p.1, p.2) ≠ 0
    rw [zero_add]
    exact hp
  have hcyc' : bbBoundary1Fn baseA baseB (translate1 p.1 u) = 0 := by
    rw [bbBoundary1Fn_translate1, hcyc]
    rfl
  have hcard' :
      (Finset.univ.filter fun q => translate1 p.1 u q ≠ 0).card ≤ 5 := by
    rw [card_support_translate1]
    omega
  -- decompose the normalized support
  have hxS : (((0, 0) : BaseGroup), p.2)
      ∈ Finset.univ.filter fun q => translate1 p.1 u q ≠ 0 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp'⟩
  have hxs : (((0, 0) : BaseGroup), p.2)
      ∉ (Finset.univ.filter fun q => translate1 p.1 u q ≠ 0).erase
          (((0, 0) : BaseGroup), p.2) :=
    Finset.notMem_erase _ _
  have hins : insert ((((0, 0) : BaseGroup)), p.2)
      ((Finset.univ.filter fun q => translate1 p.1 u q ≠ 0).erase
        (((0, 0) : BaseGroup), p.2))
      = Finset.univ.filter fun q => translate1 p.1 u q ≠ 0 :=
    Finset.insert_erase hxS
  -- (PAR): the normalized support has even size, and it is nonempty
  have hpar := cycle_weight_even (translate1 p.1 u) hcyc'
  have hpos : 0 < (Finset.univ.filter fun q => translate1 p.1 u q ≠ 0).card :=
    Finset.card_pos.mpr ⟨_, hxS⟩
  have hscard :
      ((Finset.univ.filter fun q => translate1 p.1 u q ≠ 0).erase
        (((0, 0) : BaseGroup), p.2)).card = 1
      ∨ ((Finset.univ.filter fun q => translate1 p.1 u q ≠ 0).erase
        (((0, 0) : BaseGroup), p.2)).card = 3 := by
    rw [Finset.card_erase_of_mem hxS]
    omega
  -- the normalized chain is the indicator of `insert x s`
  have hind : translate1 p.1 u
      = fun q => if q ∈ insert ((((0, 0) : BaseGroup)), p.2)
          ((Finset.univ.filter fun q => translate1 p.1 u q ≠ 0).erase
            (((0, 0) : BaseGroup), p.2)) then 1 else 0 := by
    rw [hins]
    exact eq_indicator_support (translate1 p.1 u)
  -- contradict the finite check
  have hcheck : ∃ h : BaseGroup, syndAt (insert ((((0, 0) : BaseGroup)), p.2)
      ((Finset.univ.filter fun q => translate1 p.1 u q ≠ 0).erase
        (((0, 0) : BaseGroup), p.2))) h ≠ 0 := by
    rcases hscard with hk | hk
    · obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hk
      rw [hq] at hxs
      rw [Finset.mem_singleton] at hxs
      obtain ⟨h, hh⟩ := smallCycleCheck_two p.2 q (Ne.symm hxs)
      refine ⟨h, ?_⟩
      rw [hq, syndAt,
        Finset.sum_insert (by rw [Finset.mem_singleton]; exact hxs),
        Finset.sum_singleton]
      exact hh
    · obtain ⟨q₁, q₂, q₃, h12, h13, h23, hs3⟩ := Finset.card_eq_three.mp hk
      rw [hs3, Finset.mem_insert, Finset.mem_insert,
        Finset.mem_singleton] at hxs
      push Not at hxs
      obtain ⟨hx1, hx2, hx3⟩ := hxs
      have hfour := smallCycleCheck_four p.2 q₁ q₂ q₃
      rcases hfour with hc | hc | hc | ⟨h, hh⟩
      · exact absurd hc.symm hx1
      · exact absurd hc.symm hx2
      · exact absurd hc.symm hx3
      refine ⟨h, ?_⟩
      rw [hs3, syndAt,
        Finset.sum_insert (by
          rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
          push Not
          exact ⟨hx1, hx2, hx3⟩),
        Finset.sum_insert (by
          rw [Finset.mem_insert, Finset.mem_singleton]
          push Not
          exact ⟨h12, h13⟩),
        Finset.sum_insert (by rw [Finset.mem_singleton]; exact h23),
        Finset.sum_singleton, ← add_assoc, ← add_assoc]
      exact hh
  obtain ⟨h, hsynd⟩ := hcheck
  apply hsynd
  rw [← bbBoundary1Fn_indicator, ← hind]
  exact congrFun hcyc' h

/-! ## `BaseDistanceGe6` is a theorem -/

/-- The Phase-1 hypothesis (A): chain-level d(base) ≥ 6. -/
theorem base_distance_ge_6 : BaseDistanceGe6 := by
  intro u hu hnb
  have hne : u ≠ 0 := by
    rintro rfl
    exact hnb ⟨0, map_zero _⟩
  have hcyc : bbBoundary1Fn baseA baseB u = 0 := hu
  have h6 := base_cycle_weight_ge_6 u hcyc hne
  rw [bb72Complex_chainWeight_eq]
  exact h6

/-- `u*` is not a base boundary (else its pullback `τ(u*)` would be a gross
boundary, contradicting the Phase-0 dual-witness certificate). -/
theorem uStar_not_mem_base_boundaries : uStar ∉ bb72Complex.boundaries :=
  fun h => tauUStar_not_mem_boundaries (coverPull1_mem_boundaries h)

/-- **Chain-level d(base) = 6** (Corollary A′): 6 is attained (by `u*`) and
minimal. -/
theorem base_chain_distance_eq_6 :
    IsLeast {w : ℕ | ∃ u : BaseGroup × Fin 2 → ZMod 2,
      u ∈ bb72Complex.cycles ∧ u ∉ bb72Complex.boundaries ∧
      bb72Complex.chainWeight u = w} 6 := by
  constructor
  · exact ⟨uStar, uStar_mem_cycles, uStar_not_mem_base_boundaries,
      chainWeight_uStar⟩
  · rintro w ⟨u, hu, hnb, rfl⟩
    exact base_distance_ge_6 u hu hnb

/-! ## Unconditional d(gross) ≥ 6 (A4 Theorem B)

Sector split on `b := p(v)`: if `b ≠ 0` then `b` is a nonzero base *cycle*
(boundary or not), so `|v| ≥ |b| ≥ 6` by the strong small-cycle theorem;
if `b = 0` the Phase-1 rung gives `|v| ≥ 12`. -/

/-- Every nontrivial cycle of the gross complex has chain weight ≥ 6 —
**unconditionally**. -/
theorem gross_chainWeight_ge_6 :
    ∀ v : GrossGroup × Fin 2 → ZMod 2,
      v ∈ grossComplex.cycles → v ∉ grossComplex.boundaries →
      6 ≤ grossComplex.chainWeight v := by
  intro v hv hnb
  by_cases h0 : coverPush1 v = 0
  · have h12 := gross_chainWeight_ge_12_of_coverPush_eq_zero
      base_distance_ge_6 hv hnb h0
    omega
  · have hcyc : bbBoundary1Fn baseA baseB (coverPush1 v) = 0 :=
      coverPush1_mem_cycles hv
    have h6 := base_cycle_weight_ge_6 (coverPush1 v) hcyc h0
    have hle := chainWeight_coverPush_le v
    rw [bb72Complex_chainWeight_eq] at hle
    omega

/-- Dual-side mirror, via the Φ duality. -/
theorem gross_dual_chainWeight_ge_6 :
    ∀ c ∈ grossComplex.dualCycles, c ∉ grossComplex.dualBoundaries →
      6 ≤ grossComplex.chainWeight c := by
  have hX : ∀ c ∈ (bbChainComplex grossA grossB).cycles,
      c ∉ (bbChainComplex grossA grossB).boundaries →
      6 ≤ (bbChainComplex grossA grossB).chainWeight c := fun c hc hnb =>
    gross_chainWeight_ge_6 c hc hnb
  exact (bb_cycle_bound_iff_dual_bound grossA grossB 6).mp hX

/-- **Unconditional d(gross) ≥ 6 at the Pauli level** (A4 Theorem B): every
nontrivial logical operator of the gross homological stabilizer group has
weight ≥ 6 — triple the published Lin–Pryadko floor of 2. -/
theorem gross_logical_weight_ge_6
    (g : NQubitPauliGroupElement grossComplex.numQubits)
    (hg : Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
      grossComplex.homologicalStabilizerGroup) :
    6 ≤ NQubitPauliGroupElement.weight g :=
  HomologicalCode.chainWeight_lower_bound_transfers grossComplex 6
    (fun c hc hnb => gross_chainWeight_ge_6 c hc hnb)
    gross_dual_chainWeight_ge_6 g hg

/-! ## The narrowed Phase-1 interface

With (A) discharged, the conditional `d(gross) = 12` needs only the two
sector inputs. -/

/-- Conditional Pauli-level `d(gross) = 12`, now from the two remaining
sector hypotheses (A4 Theorems C and D; Phases 3–4). -/
theorem gross_pauli_distance_eq_12_of_two_sectors
    (hM : DangerousSectorGe12) (hMim : SafeSectorGe12) :
    IsLeast {w : ℕ | ∃ g : NQubitPauliGroupElement grossComplex.numQubits,
      Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
        grossComplex.homologicalStabilizerGroup ∧
      NQubitPauliGroupElement.weight g = w} 12 :=
  gross_pauli_distance_eq_12_of_sectors base_distance_ge_6 hM hMim

end BB
end Homological
end Stabilizer
end Quantum
