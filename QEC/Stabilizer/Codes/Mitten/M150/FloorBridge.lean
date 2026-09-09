/-
# M4 chain↔mask bridge — generic layer

Connects `ZMod 2` chains on the mitten qubit cells to the packed 30-bit
masks the M4 sweep layer (`FloorCore`/`FloorData`/`FloorSweep*`)
operates on.  Provides:

* `maskOf` — the canonical (GAP-ordered, little-endian) mask of a
  `M150G → ZMod 2` block chain, with its `testBit` anatomy, bounds,
  additivity, inverse `comask`, and injectivity;
* `maskOf_op` — the transfer principle: an additive chain operator whose
  basis images match a packed column table acts as `xorFold tbl` on
  masks (via `linear_ext`);
* `entrySum`/`blockMapped` — the sparse-entry form of the two check maps
  (`d2term` for `H_X`, `cmTerm` for `H_Z`) restricted to qubit blocks,
  and the 5-block XOR split of a check-row mask;
* the weight bridges: `popCntGo 30 (maskOf f) = suppCard f` and the
  block split of `chainWeight`.

The per-instance equation-transfer facts (basis-image natives, derived
forms, classification consumption) live in `FloorZSide.lean` /
`FloorXSide.lean`; design and offline validation:
`qec-lab:pipeline/attempts/mitten_150_30_10/m4_findings.md` and
`scripts/a32_m4_bridge_check.py`.
-/

import QEC.Stabilizer.Codes.Mitten.M150.StabilizerCode
import QEC.Stabilizer.Codes.Mitten.M150.FloorData

namespace Quantum
namespace Stabilizer
namespace Homological
namespace LP
namespace M150

open scoped BigOperators

/-! ## §1  `ZMod 2` micro-facts (kernel-decided) -/

private lemma zmod2_ite_decide : ∀ a : ZMod 2,
    (if decide (a = 1) = true then (1 : ZMod 2) else 0) = a := by decide

private lemma zmod2_val_eq_one : ∀ a : ZMod 2, a.val = 1 ↔ a = 1 := by decide

private lemma zmod2_decide_add : ∀ a b : ZMod 2,
    decide (a + b = 1) = xor (decide (a = 1)) (decide (b = 1)) := by decide

private lemma zmod2_ne_zero : ∀ a : ZMod 2, a ≠ 0 ↔ a = 1 := by decide

/-! ## §2  The canonical block mask -/

/-- Little-endian packing of `fuel` bits starting at element index `k`. -/
def maskGo (f : M150G → ZMod 2) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, k => (f (elemOf k)).val + 2 * maskGo f fuel (k + 1)

/-- The canonical 30-bit mask of a block chain: bit `i` is `f (elemOf i)`
in the GAP element order of `Data.lean`. -/
def maskOf (f : M150G → ZMod 2) : Nat := maskGo f 30 0

lemma maskGo_lt (f : M150G → ZMod 2) : ∀ fuel k, maskGo f fuel k < 2 ^ fuel := by
  intro fuel
  induction fuel with
  | zero => intro k; change 0 < 1; omega
  | succ fuel ih =>
    intro k
    change (f (elemOf k)).val + 2 * maskGo f fuel (k + 1) < 2 ^ (fuel + 1)
    have h1 : (f (elemOf k)).val < 2 := ZMod.val_lt _
    have h2 := ih (k + 1)
    have h3 : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by ring
    omega

lemma maskOf_lt (f : M150G → ZMod 2) : maskOf f < 2 ^ 30 := maskGo_lt f 30 0

lemma maskGo_testBit (f : M150G → ZMod 2) :
    ∀ fuel k i, (maskGo f fuel k).testBit i
      = (decide (i < fuel) && decide (f (elemOf (k + i)) = 1)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro k i
    change (0 : Nat).testBit i = _
    simp [Nat.zero_testBit]
  | succ fuel ih =>
    intro k i
    change ((f (elemOf k)).val + 2 * maskGo f fuel (k + 1)).testBit i = _
    have hval : (f (elemOf k)).val < 2 := ZMod.val_lt _
    cases i with
    | zero =>
      have hmod : ((f (elemOf k)).val + 2 * maskGo f fuel (k + 1)) % 2
          = (f (elemOf k)).val := by omega
      rw [Nat.testBit_zero, hmod]
      have hlt : decide (0 < fuel + 1) = true := by simp
      rw [hlt, Bool.true_and, Nat.add_zero, decide_eq_decide]
      exact zmod2_val_eq_one (f (elemOf k))
    | succ i =>
      rw [Nat.testBit_add_one]
      have hdiv : ((f (elemOf k)).val + 2 * maskGo f fuel (k + 1)) / 2
          = maskGo f fuel (k + 1) := by omega
      rw [hdiv, ih (k + 1) i]
      have hidx : k + 1 + i = k + (i + 1) := by omega
      have hlt : decide (i < fuel) = decide (i + 1 < fuel + 1) := by
        rw [decide_eq_decide]
        omega
      rw [hidx, hlt]

lemma maskOf_testBit (f : M150G → ZMod 2) (i : Nat) :
    (maskOf f).testBit i = (decide (i < 30) && decide (f (elemOf i) = 1)) := by
  have h := maskGo_testBit f 30 0 i
  rw [maskOf, h]
  simp

/-- The zero chain has mask 0. -/
lemma maskOf_zero : maskOf (0 : M150G → ZMod 2) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [maskOf_testBit, Nat.zero_testBit]
  simp

/-- `maskOf` turns pointwise sum into XOR. -/
lemma maskOf_add (f g : M150G → ZMod 2) :
    maskOf (f + g) = maskOf f ^^^ maskOf g := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, maskOf_testBit, maskOf_testBit, maskOf_testBit]
  by_cases hi : i < 30
  · simp only [hi, decide_true, Bool.true_and, Pi.add_apply]
    rw [zmod2_decide_add]
  · simp [hi]

/-! ## §3  The inverse chain of a mask -/

/-- Index of a carrier element in the GAP order. -/
def idxOfG (g : M150G) : Nat := gapElems.idxOf g

lemma elemOf_idxOfG : ∀ g : M150G, elemOf (idxOfG g) = g := by decide

lemma idxOfG_lt : ∀ g : M150G, idxOfG g < 30 := by decide

lemma idxOfG_elemOf : ∀ i < 30, idxOfG (elemOf i) = i := by decide

private lemma elemOf_inj : ∀ i < 30, ∀ j < 30, elemOf i = elemOf j → i = j := by
  decide

/-- The chain with the given mask. -/
def comask (m : Nat) : M150G → ZMod 2 :=
  fun g => if m.testBit (idxOfG g) then 1 else 0

/-- The delta chain at canonical index `i`. -/
def deltaFn (i : Nat) : M150G → ZMod 2 :=
  fun g => if g = elemOf i then 1 else 0

lemma comask_maskOf (f : M150G → ZMod 2) : comask (maskOf f) = f := by
  funext g
  rw [comask, maskOf_testBit]
  have h1 : decide (idxOfG g < 30) = true := by simp [idxOfG_lt g]
  rw [elemOf_idxOfG g, h1, Bool.true_and]
  exact zmod2_ite_decide (f g)

lemma maskOf_comask {m : Nat} (hm : m < 2 ^ 30) : maskOf (comask m) = m := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [maskOf_testBit]
  by_cases hi : i < 30
  · simp only [hi, decide_true, Bool.true_and, comask, idxOfG_elemOf i hi]
    cases hb : m.testBit i <;> simp
  · have : m.testBit i = false :=
      Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [hi, this]

lemma comask_zero : comask 0 = (0 : M150G → ZMod 2) := by
  funext g
  simp [comask, Nat.zero_testBit]

lemma comask_xor (m₁ m₂ : Nat) :
    comask (m₁ ^^^ m₂) = comask m₁ + comask m₂ := by
  funext g
  simp only [comask, Nat.testBit_xor, Pi.add_apply]
  cases h1 : m₁.testBit (idxOfG g) <;> cases h2 : m₂.testBit (idxOfG g) <;>
    decide

lemma comask_bit {i : Nat} (hi : i < 30) : comask (1 <<< i) = deltaFn i := by
  funext g
  have hbit : (1 <<< i).testBit (idxOfG g) = decide (idxOfG g = i) := by
    rw [Nat.testBit_shiftLeft, testBit_one']
    rcases Nat.lt_or_ge (idxOfG g) i with h | h
    · have h1 : decide (idxOfG g ≥ i) = false := by
        rw [decide_eq_false_iff_not]
        omega
      have h2 : decide (idxOfG g = i) = false := by
        rw [decide_eq_false_iff_not]
        omega
      rw [h1, h2, Bool.false_and]
    · have h1 : decide (idxOfG g ≥ i) = true := by simpa using h
      rw [h1, Bool.true_and, decide_eq_decide]
      omega
  simp only [comask, deltaFn, hbit]
  by_cases hg : g = elemOf i
  · subst hg
    rw [idxOfG_elemOf i hi]
    simp
  · have hidx : idxOfG g ≠ i := by
      intro h
      exact hg (by rw [← h, elemOf_idxOfG g])
    simp [hg, hidx]

/-- `maskOf` is injective. -/
lemma maskOf_inj {f g : M150G → ZMod 2} (h : maskOf f = maskOf g) : f = g := by
  rw [← comask_maskOf f, h, comask_maskOf g]

/-- A zero mask means the zero chain. -/
lemma eq_zero_of_maskOf_eq_zero {f : M150G → ZMod 2} (h : maskOf f = 0) :
    f = 0 := by
  rw [← comask_maskOf f, h, comask_zero]

/-! ## §4  The operator-transfer principle -/

/-- An additive chain operator whose basis images match a packed table
acts as `xorFold tbl` on masks. -/
lemma maskOf_op {op : (M150G → ZMod 2) → (M150G → ZMod 2)}
    (hadd : ∀ f g, op (f + g) = op f + op g)
    {tbl : List Nat}
    (hbasis : ∀ i < 30, maskOf (op (deltaFn i)) = tbl.getD i 0)
    (f : M150G → ZMod 2) :
    maskOf (op f) = xorFold tbl (maskOf f) := by
  have hop0 : op 0 = 0 := by
    have h := hadd 0 0
    rw [add_zero] at h
    have h' : op 0 + 0 = op 0 + op 0 := by
      rw [add_zero]
      exact h
    exact (add_left_cancel h').symm
  have hF0 : maskOf (op (comask 0)) = 0 := by
    rw [comask_zero, hop0, maskOf_zero]
  have hFx : ∀ m₁ m₂ : Nat, maskOf (op (comask (m₁ ^^^ m₂)))
      = maskOf (op (comask m₁)) ^^^ maskOf (op (comask m₂)) := by
    intro m₁ m₂
    rw [comask_xor, hadd, maskOf_add]
  have hbit : ∀ i < 30, maskOf (op (comask (1 <<< i)))
      = xorFold tbl (1 <<< i) := by
    intro i hi
    rw [comask_bit hi, xorFold_bit]
    exact hbasis i hi
  have key : ∀ m < 2 ^ 30, maskOf (op (comask m)) = xorFold tbl m :=
    linear_ext 30 hF0 (by simp) hFx (xorFold_xor tbl) hbit
  calc maskOf (op f) = maskOf (op (comask (maskOf f))) := by
        rw [comask_maskOf]
    _ = xorFold tbl (maskOf f) := key _ (maskOf_lt f)

/-! ## §5  Blocks, embeddings, and the sparse-entry check maps -/

/-- Block `m` of a qubit chain. -/
def blockOf (c : Fin 5 × M150G → ZMod 2) (m : Fin 5) : M150G → ZMod 2 :=
  fun g => c (m, g)

/-- Embed a block chain at block `m` (zero elsewhere). -/
def embed (m : Fin 5) (f : M150G → ZMod 2) : Fin 5 × M150G → ZMod 2 :=
  fun q => if q.1 = m then f q.2 else 0

lemma embed_add (m : Fin 5) (f g : M150G → ZMod 2) :
    embed m (f + g) = embed m f + embed m g := by
  funext q
  simp only [embed, Pi.add_apply]
  split
  · rfl
  · rw [add_zero]

/-- Sparse-entry application of a check matrix (`E = d2term` gives the
`H_X` action `dualBfn`, `E = cmTerm` the `H_Z` action `∂₁`). -/
def entrySum (E : Fin 2 × M150G → Fin 5 × M150G → ZMod 2)
    (c : Fin 5 × M150G → ZMod 2) (p : Fin 2 × M150G) : ZMod 2 :=
  ∑ q : Fin 5 × M150G, c q * E p q

lemma entrySum_add (E) (c c' : Fin 5 × M150G → ZMod 2) (p : Fin 2 × M150G) :
    entrySum E (c + c') p = entrySum E c p + entrySum E c' p := by
  simp only [entrySum, Pi.add_apply, add_mul]
  exact Finset.sum_add_distrib

/-- `dualBfn` is the `d2term` entry sum. -/
lemma dualBfn_eq_entrySum (c : Fin 5 × M150G → ZMod 2) (p : Fin 2 × M150G) :
    dualBfn c p = entrySum d2term c p := rfl

/-- `∂₁` is the `cmTerm` entry sum. -/
lemma boundary1_eq_entrySum (c : Fin 5 × M150G → ZMod 2) (p : Fin 2 × M150G) :
    m150Complex.boundary1 c p = entrySum cmTerm c p := by
  rw [HomologicalCode.boundary1_apply_eq_sum]
  exact Finset.sum_congr rfl fun q _ => by rw [boundary1_single_apply]

/-- The block decomposition of a qubit chain, pointwise. -/
lemma sum_embed_blockOf (c : Fin 5 × M150G → ZMod 2) (q : Fin 5 × M150G) :
    c q = ∑ m : Fin 5, embed m (blockOf c m) q := by
  obtain ⟨mq, g⟩ := q
  simp only [embed, blockOf]
  rw [Finset.sum_ite_eq]
  simp

/-- Entry sums split over the five blocks. -/
lemma entrySum_sum_blocks (E) (c : Fin 5 × M150G → ZMod 2)
    (p : Fin 2 × M150G) :
    entrySum E c p = ∑ m : Fin 5, entrySum E (embed m (blockOf c m)) p := by
  have h1 : entrySum E c p
      = ∑ q : Fin 5 × M150G, (∑ m : Fin 5, embed m (blockOf c m) q) * E p q := by
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← sum_embed_blockOf]
  rw [h1]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

/-- Check-row map of one block through the entry function. -/
def blockMapped (E : Fin 2 × M150G → Fin 5 × M150G → ZMod 2) (idx : Fin 2)
    (m : Fin 5) (f : M150G → ZMod 2) : M150G → ZMod 2 :=
  fun y => entrySum E (embed m f) (idx, y)

lemma blockMapped_add (E) (idx : Fin 2) (m : Fin 5)
    (f g : M150G → ZMod 2) :
    blockMapped E idx m (f + g) = blockMapped E idx m f + blockMapped E idx m g := by
  funext y
  simp only [blockMapped, Pi.add_apply]
  rw [embed_add, entrySum_add]

/-- `maskOf`-level 5-block split of a check row. -/
lemma maskOf_entrySum_blocks (E) (idx : Fin 2) (c : Fin 5 × M150G → ZMod 2) :
    maskOf (fun y => entrySum E c (idx, y))
      = maskOf (blockMapped E idx 0 (blockOf c 0))
        ^^^ (maskOf (blockMapped E idx 1 (blockOf c 1))
        ^^^ (maskOf (blockMapped E idx 2 (blockOf c 2))
        ^^^ (maskOf (blockMapped E idx 3 (blockOf c 3))
        ^^^ maskOf (blockMapped E idx 4 (blockOf c 4))))) := by
  have h1 : (fun y => entrySum E c (idx, y))
      = blockMapped E idx 0 (blockOf c 0)
        + (blockMapped E idx 1 (blockOf c 1)
        + (blockMapped E idx 2 (blockOf c 2)
        + (blockMapped E idx 3 (blockOf c 3)
        + blockMapped E idx 4 (blockOf c 4)))) := by
    funext y
    rw [entrySum_sum_blocks]
    simp only [Pi.add_apply, blockMapped]
    rw [Fin.sum_univ_five]
    ring
  rw [h1, maskOf_add, maskOf_add, maskOf_add, maskOf_add]

/-! ## §6  Weight bridges -/

/-- Support size of a block chain. -/
def suppCard (f : M150G → ZMod 2) : ℕ :=
  (Finset.univ.filter fun g => f g ≠ 0).card

/-- The fueled popcount of a block mask is the block's support size. -/
lemma popCntGo_maskOf (f : M150G → ZMod 2) :
    popCntGo 30 (maskOf f) = suppCard f := by
  rw [popCntGo_eq_card, suppCard]
  refine Finset.card_bij (fun i _ => elemOf i) ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨hir, hib⟩ := hi
    rw [maskOf_testBit] at hib
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have := Bool.and_eq_true_iff.mp hib
    rw [zmod2_ne_zero]
    exact of_decide_eq_true this.2
  · intro i hi j hj hij
    rw [Finset.mem_filter, Finset.mem_range] at hi hj
    exact elemOf_inj i hi.1 j hj.1 hij
  · intro g hg
    rw [Finset.mem_filter] at hg
    refine ⟨idxOfG g, ?_, elemOf_idxOfG g⟩
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨idxOfG_lt g, ?_⟩
    rw [maskOf_testBit]
    have h1 : decide (idxOfG g < 30) = true := by simp [idxOfG_lt g]
    have h2 : f (elemOf (idxOfG g)) = 1 := by
      rw [elemOf_idxOfG g]
      exact (zmod2_ne_zero _).mp hg.2
    simp [h1, h2]

/-- The chain weight splits over the five blocks. -/
lemma chainWeight_eq_sum_suppCard (c : Fin 5 × M150G → ZMod 2) :
    m150Complex.chainWeight c = ∑ m : Fin 5, suppCard (blockOf c m) := by
  have h0 : m150Complex.chainWeight c
      = (Finset.univ.filter fun q : Fin 5 × M150G => c q ≠ 0).card := rfl
  rw [h0, Finset.card_filter]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [suppCard, Finset.card_filter]
  rfl

end M150
end LP
end Homological
end Stabilizer
end Quantum
