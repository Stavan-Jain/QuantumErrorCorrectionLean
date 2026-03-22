import Mathlib.Tactic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Bitwise
import QEC.Stabilizer.Core.StabilizerGroup
import QEC.Stabilizer.Core.StabilizerCode
import QEC.Stabilizer.Core.SubgroupLemmas
import QEC.Stabilizer.Core.CSSNoNegI
import QEC.Stabilizer.Core.Centralizer
import QEC.Stabilizer.PauliGroup.Commutation
import QEC.Stabilizer.PauliGroup.CommutationTactics
import QEC.Stabilizer.BinarySymplectic.SymplecticInner
import QEC.Stabilizer.BinarySymplectic.CheckMatrix
import QEC.Stabilizer.BinarySymplectic.CheckMatrixDecidable
import QEC.Stabilizer.BinarySymplectic.Core
import QEC.Stabilizer.BinarySymplectic.IndependentEquiv
import QEC.Stabilizer.PauliGroup.NQubitOperator

namespace Quantum
open scoped BigOperators

namespace StabilizerGroup
namespace QuantumHamming

/-!
# Quantum Hamming codes [[2^r − 1, 2^r − 1 − 2r, 3]]

The quantum Hamming code family is a CSS construction based on the classical
[2^r − 1, 2^r − 1 − r, 3] Hamming code.

For parameter `r ≥ 3`:
- Physical qubits: `n = 2^r − 1`
- Z-generators: for each row `a : Fin r` of the Hamming parity-check matrix,
  apply Z to qubits in the support of that row (r generators)
- X-generators: same supports, but apply X instead (r generators)
- Total generators: 2r, encoding `2^r − 1 − 2r` logical qubits

The Hamming parity-check matrix has columns indexed by `Fin (2^r − 1)`, where
column `k` represents the binary expansion of `k + 1` (all nonzero r-bit vectors).

Cross-commutation holds because any two rows of the Hamming parity-check matrix
overlap in an even number of positions: specifically `2^(r−2)` for distinct rows
and `2^(r−1)` for equal rows, both even when `r ≥ 3`.

The Steane [[7, 1, 3]] code is the special case `r = 3`.
-/

open NQubitPauliGroupElement

variable (r : ℕ)

/-!
## Hamming parity-check matrix

The `r × (2^r − 1)` Hamming parity-check matrix has columns that enumerate all
nonzero binary vectors of length `r`. Column `k` (0-indexed) is the binary
expansion of `k + 1`.
-/

/-- Entry `(a, k)` of the Hamming parity-check matrix: bit `a` of `k + 1`.
    Row `a` has a 1 at column `k` iff the `(k+1)`-th nonzero vector has its `a`-th bit set. -/
def hammingEntry (a : Fin r) (k : Fin (2 ^ r - 1)) : ZMod 2 :=
  if (k.val + 1).testBit a.val then 1 else 0

/-- The number of columns where rows `a` and `b` both have a 1. Over ZMod 2, this is the
    dot product of rows `a` and `b` of the parity-check matrix. -/
def hammingRowDot (a b : Fin r) : ZMod 2 :=
  ∑ k : Fin (2 ^ r - 1), hammingEntry r a k * hammingEntry r b k

/-- Even cardinality from a fixed-point-free involution on a Finset. -/
private lemma even_card_of_fpf_involution {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → α) (hf_mem : ∀ x ∈ S, f x ∈ S)
    (hf_inv : ∀ x ∈ S, f (f x) = x) (hf_ne : ∀ x ∈ S, f x ≠ x) :
    Even S.card := by
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hS : S = ∅
    · simp [hS]
    · obtain ⟨x, hx⟩ := Finset.nonempty_of_ne_empty hS
      have hfx := hf_mem x hx
      have hne : f x ≠ x := hf_ne x hx
      let S' := (S.erase (f x)).erase x
      have hS_eq : S.card = S'.card + 2 := by
        have h1 : (S.erase (f x)).card = S.card - 1 :=
          Finset.card_erase_of_mem hfx
        have h2 : x ∈ S.erase (f x) := Finset.mem_erase.mpr ⟨hne.symm, hx⟩
        have h3 : S'.card = (S.erase (f x)).card - 1 :=
          Finset.card_erase_of_mem h2
        have h5 : 1 < S.card := by
          rw [Finset.one_lt_card]
          exact ⟨x, hx, f x, hfx, hne.symm⟩
        omega
      have hS'_sub : S' ⊂ S :=
        Finset.ssubset_of_subset_of_ssubset
          (Finset.erase_subset _ _) (Finset.erase_ssubset hfx)
      rw [hS_eq]
      have hS'_even := ih S' hS'_sub (fun y hy => by
          simp only [S', Finset.mem_erase] at hy ⊢
          refine ⟨fun h => ?_, fun h => ?_, hf_mem y hy.2.2⟩
          · have hinv := hf_inv y hy.2.2
            rw [h] at hinv
            exact hy.2.1 hinv.symm
          · have : f (f y) = f (f x) := by rw [h]
            rw [hf_inv y hy.2.2, hf_inv x hx] at this
            exact hy.1 this)
        (fun y hy => by simp only [S', Finset.mem_erase] at hy; exact hf_inv y hy.2.2)
        (fun y hy => by simp only [S', Finset.mem_erase] at hy; exact hf_ne y hy.2.2)
      obtain ⟨k, hk⟩ := hS'_even
      exact ⟨k + 1, by omega⟩

/-- XOR with `2^c` preserves `testBit` at positions other than `c`. -/
private lemma testBit_xor_two_pow (m c i : ℕ) (hic : i ≠ c) :
    (m ^^^ 2 ^ c).testBit i = m.testBit i := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  simp [Ne.symm hic]

/-- If `m < 2^r` and `c < r`, then `m ^^^ 2^c < 2^r`. -/
private lemma xor_pow_lt_pow {m c r : ℕ} (hm : m < 2 ^ r) (hc : c < r) :
    m ^^^ 2 ^ c < 2 ^ r := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  have hmi : m.testBit i = false := Nat.testBit_lt_two_pow (by
    calc m < 2 ^ r := hm
    _ ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) hi)
  simp [show ¬ (c = i) from by omega, hmi]

/-- For `k : Fin (2^r - 1)` with bit `a` set (where `a ≠ c`), `(k+1) ⊕ 2^c - 1` is
    a valid element of `Fin (2^r - 1)`. -/
private lemma xor_flip_val_lt {r c : ℕ} (hc : c < r) {k : Fin (2 ^ r - 1)}
    {a : ℕ} (hac : a ≠ c) (ha : (k.val + 1).testBit a = true) :
    (k.val + 1 ^^^ 2 ^ c) - 1 < 2 ^ r - 1 := by
  have hk_lt : k.val + 1 < 2 ^ r := by omega
  have hxor_lt : k.val + 1 ^^^ 2 ^ c < 2 ^ r := xor_pow_lt_pow hk_lt hc
  have hxor_pos : 0 < k.val + 1 ^^^ 2 ^ c := by
    rw [Nat.pos_iff_ne_zero]
    intro h
    have hbad : (k.val + 1 ^^^ 2 ^ c).testBit a = (k.val + 1).testBit a :=
      testBit_xor_two_pow _ _ _ hac
    rw [h] at hbad
    simp at hbad
    rw [ha] at hbad
    exact absurd hbad (by simp)
  omega

/-- The XOR-flip function on `Fin (2^r - 1)`, defined for elements where bit `a` is set. -/
private def xorFlip (r c : ℕ) (hc : c < r) (a : ℕ) (hac : a ≠ c)
    (k : Fin (2 ^ r - 1)) (ha : (k.val + 1).testBit a = true) : Fin (2 ^ r - 1) :=
  ⟨(k.val + 1 ^^^ 2 ^ c) - 1, xor_flip_val_lt hc hac ha⟩

/-- The XOR result is positive when bit `a ≠ c` is set. -/
private lemma xor_pos_of_testBit {m c a : ℕ} (hac : a ≠ c)
    (ha : m.testBit a = true) : 0 < m ^^^ 2 ^ c := by
  rw [Nat.pos_iff_ne_zero]
  intro h
  have := testBit_xor_two_pow m c a hac
  rw [h] at this; simp at this; rw [ha] at this; simp at this

/-- The dot product of any two rows of the Hamming parity-check matrix is 0 (mod 2)
    for `r ≥ 3`.

    **Proof sketch:** We find a bit position `c` distinct from `a` and `b` (possible
    since `r ≥ 3`), then define an involution on the overlap set by XORing with `2^c`.
    This involution is fixed-point-free, so the overlap set has even cardinality. -/
theorem hammingRowDot_eq_zero (hr : 3 ≤ r) (a b : Fin r) :
    hammingRowDot r a b = 0 := by
  -- Step 1: Rewrite as card of a filter set
  simp only [hammingRowDot, hammingEntry]
  conv_lhs =>
    arg 2; ext k
    rw [show (if (k.val + 1).testBit a.val then (1 : ZMod 2) else 0) *
        (if (k.val + 1).testBit b.val then (1 : ZMod 2) else 0) =
        if ((k.val + 1).testBit a.val = true ∧ (k.val + 1).testBit b.val = true) then 1 else 0
      by split_ifs <;> simp_all]
  rw [Finset.sum_boole]
  rw [ZMod.natCast_eq_zero_iff_even]
  -- Step 2: Find bit c < r with c ≠ a and c ≠ b (possible since r ≥ 3)
  have hc_exists : ∃ c : ℕ, c < r ∧ c ≠ a.val ∧ c ≠ b.val := by
    by_contra hall; push_neg at hall
    have h0 := hall 0 (by omega); have h1 := hall 1 (by omega); have h2 := hall 2 (by omega)
    omega
  obtain ⟨c, hc_lt, hca, hcb⟩ := hc_exists
  -- Step 3: Define the XOR involution and show even cardinality
  let S := Finset.univ.filter (fun k : Fin (2 ^ r - 1) =>
    (k.val + 1).testBit a.val = true ∧ (k.val + 1).testBit b.val = true)
  -- Define f on all of Fin (2^r - 1); on S it will be the XOR map
  let f : Fin (2 ^ r - 1) → Fin (2 ^ r - 1) := fun k =>
    if ha : (k.val + 1).testBit a.val = true then
      xorFlip r c hc_lt a.val hca.symm k ha
    else k
  apply even_card_of_fpf_involution S f
  -- f maps S to S: XOR with 2^c preserves bits a and b (since c ≠ a, c ≠ b)
  · intro k hk
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    have hka := hk.1; have hkb := hk.2
    simp only [f, dif_pos hka, xorFlip]
    have hxor_pos := xor_pos_of_testBit hca.symm hka
    constructor
    · show ((k.val + 1 ^^^ 2 ^ c) - 1 + 1).testBit a.val = true
      rw [Nat.sub_one_add_one_eq_of_pos hxor_pos]
      rwa [testBit_xor_two_pow _ _ _ hca.symm]
    · show ((k.val + 1 ^^^ 2 ^ c) - 1 + 1).testBit b.val = true
      rw [Nat.sub_one_add_one_eq_of_pos hxor_pos]
      rwa [testBit_xor_two_pow _ _ _ hcb.symm]
  -- f is an involution on S
  · intro k hk
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    have hka := hk.1
    simp only [f]
    rw [dif_pos hka]
    simp only [xorFlip]
    have hxor_pos := xor_pos_of_testBit hca.symm hka
    have hbit_a : ((k.val + 1 ^^^ 2 ^ c) - 1 + 1).testBit a.val = true := by
      rw [Nat.sub_one_add_one_eq_of_pos hxor_pos]
      rwa [testBit_xor_two_pow _ _ _ hca.symm]
    rw [dif_pos hbit_a]
    ext
    change ((k.val + 1 ^^^ 2 ^ c) - 1 + 1 ^^^ 2 ^ c) - 1 = k.val
    rw [Nat.sub_one_add_one_eq_of_pos hxor_pos, Nat.xor_cancel_right]; omega
  -- f has no fixed points on S
  · intro k hk
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    have hka := hk.1
    simp only [f]
    rw [dif_pos hka]
    intro h
    have heq := congr_arg Fin.val h
    simp only [xorFlip] at heq
    have hxor_pos := xor_pos_of_testBit hca.symm hka
    have h1 : k.val + 1 ^^^ 2 ^ c = k.val + 1 := by omega
    have h2 := Nat.xor_cancel_left (k.val + 1) (2 ^ c)
    rw [h1, Nat.xor_self] at h2
    exact absurd h2.symm (by positivity)

/-!
## Generators

For each row `a : Fin r`, we have a Z-generator and an X-generator.
The support of generator `a` is the set of qubits `k` where row `a` has a 1.
-/

/-- Z-generator for row `a`: Z on qubits where bit `a` of `(k+1)` is set. -/
def ZGen (a : Fin r) : NQubitPauliGroupElement (2 ^ r - 1) :=
  ⟨0, fun k => if (k.val + 1).testBit a.val then PauliOperator.Z else PauliOperator.I⟩

/-- X-generator for row `a`: X on qubits where bit `a` of `(k+1)` is set. -/
def XGen (a : Fin r) : NQubitPauliGroupElement (2 ^ r - 1) :=
  ⟨0, fun k => if (k.val + 1).testBit a.val then PauliOperator.X else PauliOperator.I⟩

/-- The set of Z-generators (one per parity-check row). -/
def ZGenerators : Set (NQubitPauliGroupElement (2 ^ r - 1)) :=
  Set.range (ZGen r)

/-- The set of X-generators (one per parity-check row). -/
def XGenerators : Set (NQubitPauliGroupElement (2 ^ r - 1)) :=
  Set.range (XGen r)

/-- The full generator set: Z-generators ∪ X-generators. -/
def generators : Set (NQubitPauliGroupElement (2 ^ r - 1)) :=
  ZGenerators r ∪ XGenerators r

/-- The quantum Hamming stabilizer subgroup: closure of the 2r generators. -/
def subgroup : Subgroup (NQubitPauliGroupElement (2 ^ r - 1)) :=
  Subgroup.closure (generators r)

/-!
## Generator list

We combine the Z-generators and X-generators into a single function on `Fin (2 * r)`,
mapping the first `r` indices to Z-generators and the last `r` to X-generators.
-/

/-- Combined generator function: indices `[0, r)` map to Z-generators,
    indices `[r, 2r)` map to X-generators. -/
def allGen (i : Fin (2 * r)) : NQubitPauliGroupElement (2 ^ r - 1) :=
  if h : i.val < r then ZGen r ⟨i.val, h⟩ else XGen r ⟨i.val - r, by omega⟩

/-- Generators as a list (for check-matrix and independence arguments). -/
def generatorsList : List (NQubitPauliGroupElement (2 ^ r - 1)) :=
  List.ofFn (allGen r)

lemma generatorsList_length : (generatorsList r).length = 2 * r := by
  simp [generatorsList, List.length_ofFn]

/-- Every element of the generators list has phase power 0. -/
lemma AllPhaseZero_generatorsList :
    NQubitPauliGroupElement.AllPhaseZero (generatorsList r) := by
  rw [generatorsList]
  apply NQubitPauliGroupElement.AllPhaseZero_ofFn
  intro i
  simp only [allGen]
  split_ifs <;> rfl

/-- The list of generators has the same elements as the generator set. -/
lemma listToSet_generatorsList :
    NQubitPauliGroupElement.listToSet (generatorsList r) = generators r := by
  rw [generatorsList, NQubitPauliGroupElement.listToSet_ofFn]
  ext g
  simp only [Set.mem_range, generators, ZGenerators, XGenerators, Set.mem_union]
  constructor
  · rintro ⟨i, rfl⟩
    simp only [allGen]
    split_ifs with h
    · exact Or.inl ⟨⟨i.val, h⟩, rfl⟩
    · exact Or.inr ⟨⟨i.val - r, by omega⟩, rfl⟩
  · rintro (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact ⟨⟨a.val, by omega⟩, by simp [allGen, a.isLt]⟩
    · exact ⟨⟨r + a.val, by omega⟩, by simp [allGen, show ¬(r + a.val < r) from by omega]⟩

/-!
## Typing: Z-type / X-type generators
-/

/-- Each Z-generator is Z-type (phase 0, each qubit is I or Z). -/
lemma ZGenerators_are_ZType :
    ∀ g, g ∈ ZGenerators r → NQubitPauliGroupElement.IsZTypeElement g := by
  intro g hg
  obtain ⟨a, rfl⟩ := hg
  refine ⟨rfl, fun k => ?_⟩
  simp only [ZGen]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- Each X-generator is X-type (phase 0, each qubit is I or X). -/
lemma XGenerators_are_XType :
    ∀ g, g ∈ XGenerators r → NQubitPauliGroupElement.IsXTypeElement g := by
  intro g hg
  obtain ⟨a, rfl⟩ := hg
  refine ⟨rfl, fun k => ?_⟩
  simp only [XGen]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-!
## Cross-commutation: Z-generators commute with X-generators

The symplectic inner product between `ZGen a` and `XGen b` reduces to the dot product
of rows `a` and `b` of the Hamming parity-check matrix (over ZMod 2), which is 0.
-/

/-- The symplectic inner product of `ZGen a` and `XGen b` equals the Hamming row dot
    product of rows `a` and `b`. -/
lemma ZGen_XGen_symplectic_eq_hammingRowDot (a b : Fin r) :
    NQubitPauliOperator.symplecticInner (ZGen r a).operators (XGen r b).operators =
      hammingRowDot r a b := by
  simp only [NQubitPauliOperator.symplecticInner, hammingRowDot, hammingEntry, ZGen, XGen]
  congr 1
  ext k
  simp only [PauliOperator.symplecticProductSingle]
  split_ifs with ha hb hb
  · simp [PauliOperator.toSymplecticSingle]
  · simp [PauliOperator.toSymplecticSingle]
  · simp [PauliOperator.toSymplecticSingle]
  · simp [PauliOperator.toSymplecticSingle]

/-- Every Z-generator commutes with every X-generator. -/
theorem ZGenerators_commute_XGenerators (hr : 3 ≤ r) :
    ∀ z ∈ ZGenerators r, ∀ x ∈ XGenerators r, z * x = x * z := by
  intro z hz x hx
  obtain ⟨a, rfl⟩ := hz
  obtain ⟨b, rfl⟩ := hx
  rw [NQubitPauliOperator.commutes_iff_symplectic_inner_zero]
  rw [ZGen_XGen_symplectic_eq_hammingRowDot]
  exact hammingRowDot_eq_zero r hr a b

/-!
## Pairwise commutation of all generators
-/

private lemma ZType_commutes {m : ℕ} {g h : NQubitPauliGroupElement m}
    (hg : NQubitPauliGroupElement.IsZTypeElement g)
    (hh : NQubitPauliGroupElement.IsZTypeElement h) :
    g * h = h * g := by
  apply NQubitPauliGroupElement.commutes_of_componentwise_commutes
  intro k
  have hg' := hg.2 k
  have hh' := hh.2 k
  rcases hg' with hgI | hgZ <;> rcases hh' with hhI | hhZ
  · simp [PauliOperator.mulOp, hgI, hhI]
  · simp [PauliOperator.mulOp, hgI, hhZ]
  · simp [PauliOperator.mulOp, hgZ, hhI]
  · simp [PauliOperator.mulOp, hgZ, hhZ]

private lemma XType_commutes {m : ℕ} {g h : NQubitPauliGroupElement m}
    (hg : NQubitPauliGroupElement.IsXTypeElement g)
    (hh : NQubitPauliGroupElement.IsXTypeElement h) :
    g * h = h * g := by
  apply NQubitPauliGroupElement.commutes_of_componentwise_commutes
  intro k
  have hg' := hg.2 k
  have hh' := hh.2 k
  rcases hg' with hgI | hgX <;> rcases hh' with hhI | hhX
  · simp [PauliOperator.mulOp, hgI, hhI]
  · simp [PauliOperator.mulOp, hgI, hhX]
  · simp [PauliOperator.mulOp, hgX, hhI]
  · simp [PauliOperator.mulOp, hgX, hhX]

/-- All generators pairwise commute. -/
theorem generators_commute (hr : 3 ≤ r) :
    ∀ g ∈ generators r, ∀ h ∈ generators r, g * h = h * g := by
  intro g hg h hh
  have hg' : g ∈ ZGenerators r ∨ g ∈ XGenerators r := by simpa [generators] using hg
  have hh' : h ∈ ZGenerators r ∨ h ∈ XGenerators r := by simpa [generators] using hh
  rcases hg' with hgZ | hgX <;> rcases hh' with hhZ | hhX
  · exact ZType_commutes (ZGenerators_are_ZType r g hgZ) (ZGenerators_are_ZType r h hhZ)
  · exact ZGenerators_commute_XGenerators r hr g hgZ h hhX
  · simpa using (ZGenerators_commute_XGenerators r hr h hhZ g hgX).symm
  · exact XType_commutes (XGenerators_are_XType r g hgX) (XGenerators_are_XType r h hhX)

/-!
## No `−I` in the stabilizer (CSS lemma)
-/

/-- The quantum Hamming stabilizer does not contain −I. -/
theorem negIdentity_not_mem (hr : 3 ≤ r) :
    negIdentity (2 ^ r - 1) ∉ subgroup r := by
  simpa [subgroup, generators] using
    CSS.negIdentity_not_mem_closure_union (ZGenerators r) (XGenerators r)
      (ZGenerators_are_ZType r) (XGenerators_are_XType r) (ZGenerators_commute_XGenerators r hr)

/-!
## Bundled `StabilizerGroup`
-/

/-- The quantum Hamming code as a `StabilizerGroup (2^r − 1)`. -/
noncomputable def stabilizerGroup (hr : 3 ≤ r) : StabilizerGroup (2 ^ r - 1) :=
  mkStabilizerFromGenerators (2 ^ r - 1) (generatorsList r)
    (by rw [listToSet_generatorsList]; exact generators_commute r hr)
    (by rw [listToSet_generatorsList]; exact negIdentity_not_mem r hr)

lemma stabilizerGroup_toSubgroup_eq (hr : 3 ≤ r) :
    (stabilizerGroup r hr).toSubgroup = subgroup r := by
  simp only [stabilizerGroup, mkStabilizerFromGenerators, subgroup]
  rw [listToSet_generatorsList]

/-!
## Linear independence of generators

The check-matrix rows of the 2r generators are linearly independent over ZMod 2.
This ensures the stabilizer has exactly 2r independent generators, giving a code
encoding `2^r − 1 − 2r` logical qubits.
-/

/-- `testBit (2^a) a = true` -/
private lemma testBit_two_pow_self (a : ℕ) : (2 ^ a).testBit a = true := by
  rw [Nat.testBit_two_pow]; simp

/-- `testBit (2^a) b = false` when `b ≠ a` -/
private lemma testBit_two_pow_ne {a b : ℕ} (h : b ≠ a) : (2 ^ a).testBit b = false := by
  rw [Nat.testBit_two_pow]; simp [Ne.symm h]

/-- `2^a - 1 < 2^r - 1` when `a < r` (so `2^a - 1` is a valid column index). -/
private lemma two_pow_sub_one_lt_two_pow_sub_one {a r : ℕ} (h : a < r) :
    2 ^ a - 1 < 2 ^ r - 1 := by
  exact Nat.sub_lt_sub_right Nat.one_le_two_pow (Nat.pow_lt_pow_right (by omega) h)

/-- The pivot entry: `hammingEntry r a (2^a - 1) = 1`. -/
private lemma hammingEntry_pivot (a : Fin r) :
    hammingEntry r a ⟨2 ^ a.val - 1, two_pow_sub_one_lt_two_pow_sub_one a.isLt⟩ = 1 := by
  simp only [hammingEntry]
  rw [Nat.sub_one_add_one_eq_of_pos (by positivity), testBit_two_pow_self]; rfl

/-- Off-pivot entries: `hammingEntry r b (2^a - 1) = 0` when `b ≠ a`. -/
private lemma hammingEntry_off_pivot {a b : Fin r} (hab : b ≠ a) :
    hammingEntry r b ⟨2 ^ a.val - 1, two_pow_sub_one_lt_two_pow_sub_one a.isLt⟩ = 0 := by
  simp only [hammingEntry]
  rw [Nat.sub_one_add_one_eq_of_pos (by positivity), testBit_two_pow_ne (Fin.val_ne_of_ne hab)]
  simp

/-- The rows of the Hamming parity-check matrix are linearly independent.
    Proved by showing that column `2^a - 1` serves as a pivot for row `a`. -/
private lemma hammingRows_linearIndependent :
    ∀ f : Fin r → ZMod 2,
      (∀ k : Fin (2 ^ r - 1), ∑ a : Fin r, f a * hammingEntry r a k = 0) →
      f = 0 := by
  intro f hf
  funext a
  simp only [Pi.zero_apply]
  -- Evaluate at the pivot column k = 2^a - 1
  have hbound := two_pow_sub_one_lt_two_pow_sub_one a.isLt
  have hpivot := hf ⟨2 ^ a.val - 1, hbound⟩
  -- In this sum, all terms with b ≠ a vanish (off-pivot = 0), leaving f(a) * 1 = 0
  have hsplit : ∑ b : Fin r, f b * hammingEntry r b ⟨2 ^ a.val - 1, hbound⟩ =
      f a * 1 + ∑ b ∈ Finset.univ.erase a, f b * hammingEntry r b ⟨2 ^ a.val - 1, hbound⟩ := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
    congr 1
    rw [hammingEntry_pivot]
  rw [hsplit] at hpivot
  have hrest : ∑ b ∈ Finset.univ.erase a, f b * hammingEntry r b ⟨2 ^ a.val - 1, hbound⟩ = 0 := by
    apply Finset.sum_eq_zero
    intro b hb
    rw [Finset.mem_erase] at hb
    rw [hammingEntry_off_pivot (hab := hb.1), mul_zero]
  rw [hrest, add_zero, _root_.mul_one] at hpivot
  exact hpivot

/-- The check matrix entry for a ZGen generator at a Z-component column equals hammingEntry.
    For ZGen a, the Z-component (column n + k) is hammingEntry r a k. -/
private lemma checkMatrix_ZGen_Z_part (a : Fin r) (k : Fin (2 ^ r - 1)) :
    NQubitPauliOperator.toSymplectic (ZGen r a).operators (Fin.natAdd (2 ^ r - 1) k) =
      hammingEntry r a k := by
  rw [NQubitPauliOperator.toSymplectic_Z_part]
  simp only [ZGen, hammingEntry]
  split_ifs with h
  · simp [PauliOperator.toSymplecticSingle]
  · simp [PauliOperator.toSymplecticSingle]

/-- The check matrix entry for a ZGen generator at an X-component column is 0. -/
private lemma checkMatrix_ZGen_X_part (a : Fin r) (k : Fin (2 ^ r - 1)) :
    NQubitPauliOperator.toSymplectic (ZGen r a).operators (Fin.castAdd (2 ^ r - 1) k) = 0 := by
  rw [NQubitPauliOperator.toSymplectic_X_part]
  simp only [ZGen]
  split_ifs with h
  · simp [PauliOperator.toSymplecticSingle]
  · simp [PauliOperator.toSymplecticSingle]

/-- The check matrix entry for an XGen generator at an X-component column equals hammingEntry. -/
private lemma checkMatrix_XGen_X_part (a : Fin r) (k : Fin (2 ^ r - 1)) :
    NQubitPauliOperator.toSymplectic (XGen r a).operators (Fin.castAdd (2 ^ r - 1) k) =
      hammingEntry r a k := by
  rw [NQubitPauliOperator.toSymplectic_X_part]
  simp only [XGen, hammingEntry]
  split_ifs with h
  · simp [PauliOperator.toSymplecticSingle]
  · simp [PauliOperator.toSymplecticSingle]

/-- The check matrix entry for an XGen generator at a Z-component column is 0. -/
private lemma checkMatrix_XGen_Z_part (a : Fin r) (k : Fin (2 ^ r - 1)) :
    NQubitPauliOperator.toSymplectic (XGen r a).operators (Fin.natAdd (2 ^ r - 1) k) = 0 := by
  rw [NQubitPauliOperator.toSymplectic_Z_part]
  simp only [XGen]
  split_ifs with h
  · simp [PauliOperator.toSymplecticSingle]
  · simp [PauliOperator.toSymplecticSingle]


/-- The check matrix entry for the Z-component column of a generatorsList entry. -/
private lemma checkMatrix_generatorsList_Z
    (idx : Fin (generatorsList r).length) (k : Fin (2 ^ r - 1)) :
    NQubitPauliGroupElement.checkMatrix (generatorsList r) idx
      (Fin.natAdd (2 ^ r - 1) k) =
      if hlt : idx.val < r then hammingEntry r ⟨idx.val, hlt⟩ k else 0 := by
  have hlen := generatorsList_length r
  simp only [NQubitPauliGroupElement.checkMatrix]
  by_cases hlt : idx.val < r
  · have : (generatorsList r).get idx = ZGen r ⟨idx.val, hlt⟩ := by
      simp only [generatorsList, List.get_ofFn, allGen]; simp [hlt]
    rw [this, dif_pos hlt, checkMatrix_ZGen_Z_part]
  · have h_idx : idx.val - r < r := by omega
    have : (generatorsList r).get idx = XGen r ⟨idx.val - r, h_idx⟩ := by
      simp only [generatorsList, List.get_ofFn, allGen]
      simp [show ¬(idx.val < r) from hlt]
    rw [this, dif_neg hlt, checkMatrix_XGen_Z_part]

/-- The check matrix entry for the X-component column of a generatorsList entry. -/
private lemma checkMatrix_generatorsList_X
    (idx : Fin (generatorsList r).length) (k : Fin (2 ^ r - 1)) :
    NQubitPauliGroupElement.checkMatrix (generatorsList r) idx
      (Fin.castAdd (2 ^ r - 1) k) =
      if hlt : idx.val < r then 0
      else hammingEntry r ⟨idx.val - r,
        by have := generatorsList_length r; omega⟩ k := by
  have hlen := generatorsList_length r
  simp only [NQubitPauliGroupElement.checkMatrix]
  by_cases hlt : idx.val < r
  · have : (generatorsList r).get idx = ZGen r ⟨idx.val, hlt⟩ := by
      simp only [generatorsList, List.get_ofFn, allGen]; simp [hlt]
    rw [this, dif_pos hlt, checkMatrix_ZGen_X_part]
  · have h_idx : idx.val - r < r := by omega
    have : (generatorsList r).get idx = XGen r ⟨idx.val - r, h_idx⟩ := by
      simp only [generatorsList, List.get_ofFn, allGen]
      simp [show ¬(idx.val < r) from hlt]
    rw [this, dif_neg hlt, checkMatrix_XGen_X_part]

/-- The sum ∑_{idx} f(idx) * checkMatrix(idx, Z-col k) = ∑_{a:Fin r} f(a) * hammingEntry(a,k). -/
private lemma sum_checkMatrix_Z_eq
    (f : Fin (generatorsList r).length → ZMod 2)
    (k : Fin (2 ^ r - 1)) :
    ∑ idx, f idx * NQubitPauliGroupElement.checkMatrix
      (generatorsList r) idx (Fin.natAdd (2 ^ r - 1) k) =
    ∑ a : Fin r, f ⟨a.val,
      by rw [generatorsList_length]; omega⟩ * hammingEntry r a k := by
  have hrewrite :
      (∑ idx, f idx * NQubitPauliGroupElement.checkMatrix
        (generatorsList r) idx (Fin.natAdd (2 ^ r - 1) k)) =
      ∑ idx, if hlt : idx.val < r
        then f idx * hammingEntry r ⟨idx.val, hlt⟩ k
        else 0 := by
    apply Finset.sum_congr rfl
    intro idx _
    rw [checkMatrix_generatorsList_Z]
    split_ifs <;> simp
  rw [hrewrite, Finset.sum_dite]
  simp only [Finset.sum_const_zero]
  let p : Fin (generatorsList r).length → Prop := fun i => i.val < r
  let s : Finset (Fin (generatorsList r).length) :=
    Finset.filter p Finset.univ
  have hs : ∀ x : Fin (generatorsList r).length, x ∈ s ↔ p x := by
    intro x; simp [s, p, Finset.mem_filter]
  sorry

/-- The sum ∑_{idx} f(idx) * checkMatrix(idx, X-col k) = ∑_{a:Fin r} f(r+a) * hammingEntry(a,k). -/
private lemma sum_checkMatrix_X_eq
    (f : Fin (generatorsList r).length → ZMod 2)
    (k : Fin (2 ^ r - 1)) :
    ∑ idx, f idx * NQubitPauliGroupElement.checkMatrix
      (generatorsList r) idx (Fin.castAdd (2 ^ r - 1) k) =
    ∑ a : Fin r, f ⟨r + a.val,
      by rw [generatorsList_length]; omega⟩ * hammingEntry r a k := by
  have hrewrite :
      (∑ idx, f idx * NQubitPauliGroupElement.checkMatrix
        (generatorsList r) idx (Fin.castAdd (2 ^ r - 1) k)) =
      ∑ idx, if hlt : idx.val < r
        then 0
        else f idx * hammingEntry r
          ⟨idx.val - r, by have := generatorsList_length r; omega⟩ k := by
    apply Finset.sum_congr rfl
    intro idx _
    rw [checkMatrix_generatorsList_X]
    split_ifs <;> simp
  rw [hrewrite, Finset.sum_dite]
  simp only [Finset.sum_const_zero]
  let p : Fin (generatorsList r).length → Prop := fun i => r ≤ i.val
  let s : Finset (Fin (generatorsList r).length) :=
    Finset.filter p Finset.univ
  have hs : ∀ x : Fin (generatorsList r).length, x ∈ s ↔ p x := by
    intro x; simp [s, p, Finset.mem_filter]
  sorry

/-- The check-matrix rows of the quantum Hamming generators are linearly independent. -/
theorem rowsLinearIndependent_generatorsList :
    NQubitPauliGroupElement.rowsLinearIndependent (generatorsList r) := by
  rw [NQubitPauliGroupElement.rowsLinearIndependent_iff_forall]
  intro f hf
  have hlen : (generatorsList r).length = 2 * r := generatorsList_length r
  -- Extract pointwise zero condition
  have hzero : ∀ j, ∑ idx, f idx *
      NQubitPauliGroupElement.checkMatrix (generatorsList r) idx j = 0 := by
    intro j; have := congr_fun hf j
    simp only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this; exact this
  -- Step 1: f(a) = 0 for a < r (ZGen coefficients)
  have hfZ : ∀ a : Fin r, f ⟨a.val, by rw [hlen]; omega⟩ = 0 := by
    have key : ∀ k : Fin (2 ^ r - 1),
        ∑ a : Fin r, f ⟨a.val, by rw [hlen]; omega⟩ * hammingEntry r a k = 0 := by
      intro k; rw [← sum_checkMatrix_Z_eq]; exact hzero _
    exact congr_fun (hammingRows_linearIndependent r _ key)
  -- Step 2: f(r + a) = 0 for a < r (XGen coefficients)
  have hfX : ∀ a : Fin r, f ⟨r + a.val, by rw [hlen]; omega⟩ = 0 := by
    have key : ∀ k : Fin (2 ^ r - 1),
        ∑ a : Fin r, f ⟨r + a.val, by rw [hlen]; omega⟩ * hammingEntry r a k = 0 := by
      intro k; rw [← sum_checkMatrix_X_eq]; exact hzero _
    exact congr_fun (hammingRows_linearIndependent r _ key)
  -- Combine: every coefficient is zero
  funext idx
  simp only [Pi.zero_apply]
  by_cases hlt : idx.val < r
  · exact hfZ ⟨idx.val, hlt⟩
  · have h_idx : idx.val - r < r := by omega
    have := hfX ⟨idx.val - r, h_idx⟩
    convert this using 2
    simp [Fin.ext_iff]; omega
/-- The quantum Hamming generator list is an independent generating set. -/
theorem GeneratorsIndependent_generatorsList :
    GeneratorsIndependent (2 ^ r - 1) (generatorsList r) :=
  GeneratorsIndependent_of_rowsLinearIndependent _ _ (rowsLinearIndependent_generatorsList r)

/-!
## Logical operators

Logical X̄ = X on all qubits, logical Z̄ = Z on all qubits. These commute with
every stabilizer and anticommute with each other (since `2^r − 1` is odd).

These define one logical qubit pair. The full set of `2^r − 1 − 2r` logical
qubit pairs requires the codeword structure of the underlying Hamming code.
-/

/-- Logical X: X on all `2^r − 1` qubits. -/
def logicalX : NQubitPauliGroupElement (2 ^ r - 1) :=
  ⟨0, NQubitPauliOperator.X (2 ^ r - 1)⟩

/-- Logical Z: Z on all `2^r − 1` qubits. -/
def logicalZ : NQubitPauliGroupElement (2 ^ r - 1) :=
  ⟨0, NQubitPauliOperator.Z (2 ^ r - 1)⟩

/-- `2^r − 1` is odd for `r ≥ 1`. -/
lemma two_pow_sub_one_odd (hr1 : 1 ≤ r) : Odd (2 ^ r - 1) := by
  rw [Nat.odd_sub (Nat.one_le_two_pow)]
  simp [Nat.even_pow]
  omega

/-- Logical X and logical Z anticommute (`2^r − 1` is odd). -/
theorem logicalX_anticommutes_logicalZ (hr1 : 1 ≤ r) :
    NQubitPauliGroupElement.Anticommute (logicalX r) (logicalZ r) :=
  NQubitPauliOperator.allX_allZ_anticommute (2 ^ r - 1) (two_pow_sub_one_odd r hr1)

/-- Logical X commutes with every Z-generator (each Z-row has `2^(r−1)` ones, which is even).
    Since X commutes with X trivially, logical X is in the centralizer. -/
private lemma logicalX_commutes_ZGen (hr : 3 ≤ r) (a : Fin r) :
    logicalX r * ZGen r a = ZGen r a * logicalX r := by
  rw [NQubitPauliOperator.commutes_iff_symplectic_inner_zero]
  have key : (logicalX r).operators.symplecticInner
      (ZGen r a).operators = hammingRowDot r a a := by
    simp only [NQubitPauliOperator.symplecticInner, logicalX, ZGen,
      NQubitPauliOperator.X, hammingRowDot, hammingEntry,
      PauliOperator.symplecticProductSingle, PauliOperator.toSymplecticSingle]
    congr 1; ext k; split_ifs <;> simp
  rw [key]; exact hammingRowDot_eq_zero r hr a a

/-- Logical Z commutes with every X-generator (same even-overlap argument).
    Since Z commutes with Z trivially, logical Z is in the centralizer. -/
private lemma logicalZ_commutes_XGen (hr : 3 ≤ r) (a : Fin r) :
    logicalZ r * XGen r a = XGen r a * logicalZ r := by
  rw [NQubitPauliOperator.commutes_iff_symplectic_inner_zero]
  have key : (logicalZ r).operators.symplecticInner
      (XGen r a).operators = hammingRowDot r a a := by
    simp only [NQubitPauliOperator.symplecticInner, logicalZ, XGen,
      NQubitPauliOperator.Z, hammingRowDot, hammingEntry,
      PauliOperator.symplecticProductSingle, PauliOperator.toSymplecticSingle]
    congr 1; ext k; split_ifs <;> simp
  rw [key]; exact hammingRowDot_eq_zero r hr a a

private lemma logicalX_commutes_XGen (a : Fin r) :
    logicalX r * XGen r a = XGen r a * logicalX r := by
  apply NQubitPauliGroupElement.commutes_of_componentwise_commutes
  intro k
  simp only [logicalX, XGen, NQubitPauliOperator.X]
  split_ifs
  · simp [PauliOperator.mulOp]
  · simp [PauliOperator.mulOp]

private lemma logicalZ_commutes_ZGen (a : Fin r) :
    logicalZ r * ZGen r a = ZGen r a * logicalZ r := by
  apply NQubitPauliGroupElement.commutes_of_componentwise_commutes
  intro k
  simp only [logicalZ, ZGen, NQubitPauliOperator.Z]
  split_ifs
  · simp [PauliOperator.mulOp]
  · simp [PauliOperator.mulOp]

/-- Logical X commutes with every element of the stabilizer. -/
theorem logicalX_mem_centralizer (hr : 3 ≤ r) :
    logicalX r ∈ centralizer (stabilizerGroup r hr) := by
  rw [StabilizerGroup.mem_centralizer_iff_closure (logicalX r) (stabilizerGroup r hr)
    (generators r) (stabilizerGroup_toSubgroup_eq r hr)]
  intro s hs
  simp only [generators, ZGenerators, XGenerators, Set.mem_union, Set.mem_range] at hs
  rcases hs with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · exact (logicalX_commutes_ZGen r hr a).symm
  · exact (logicalX_commutes_XGen r a).symm

/-- Logical Z commutes with every element of the stabilizer. -/
theorem logicalZ_mem_centralizer (hr : 3 ≤ r) :
    logicalZ r ∈ centralizer (stabilizerGroup r hr) := by
  rw [StabilizerGroup.mem_centralizer_iff_closure (logicalZ r) (stabilizerGroup r hr)
    (generators r) (stabilizerGroup_toSubgroup_eq r hr)]
  intro s hs
  simp only [generators, ZGenerators, XGenerators, Set.mem_union, Set.mem_range] at hs
  rcases hs with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · exact (logicalZ_commutes_ZGen r a).symm
  · exact (logicalZ_commutes_XGen r hr a).symm

/-!
## Steane code as special case

When `r = 3`, the quantum Hamming code has `2^3 − 1 = 7` qubits and `2 × 3 = 6`
generators, recovering the Steane [[7, 1, 3]] code.
-/

-- TODO: prove that QuantumHamming with r = 3 generates the same stabilizer as Steane7

end QuantumHamming
end StabilizerGroup

end Quantum
