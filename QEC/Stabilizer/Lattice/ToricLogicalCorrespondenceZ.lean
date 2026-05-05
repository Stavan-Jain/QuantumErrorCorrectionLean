import Mathlib.Tactic
import QEC.Stabilizer.Lattice.ToricOperatorChains
import QEC.Stabilizer.Lattice.ToricH1Dimension
import QEC.Stabilizer.Codes.ToricCodeN
import QEC.Stabilizer.Core.LogicalOperators

namespace Quantum
namespace Stabilizer
namespace Lattice

open scoped BigOperators

/-!
# Z-type logical correspondence for the toric code

Mirror of `ToricLogicalCorrespondenceX` for Z-type operators.  The roles of
primal and dual structures are swapped:

  primal cycles   (ker ∂₁)  ←→  dual boundaries  (im cutMap = im ∂₁ᵀ)
  primal boundary (im ∂₂)   ←→  dual cycles      (ker ∂₂ᵀ)

The dual boundary map `toricDualBoundary : C1 → C2` checks commutation with
every face stabilizer:

  (toricDualBoundary c) (x, y)
    = c(H x y) + c(H x (next y)) + c(V x y) + c(V (next x) y)

Dual cycles  = ker(toricDualBoundary)  = Z-chains commuting with all face stabs.
Dual boundaries = range(toricVertexCutMap) = Z-chains that are products of vertex stabs.
-/

-- ---------------------------------------------------------------------------
-- 1.  Z-operator encoding
-- ---------------------------------------------------------------------------

/-- Build a Z-type Pauli element from a 1-chain (dual to `toricXOperatorOfChain`). -/
def toricZOperatorOfChain (L : ℕ) (c : C1 L) :
    NQubitPauliGroupElement (toricNumQubits L) :=
  ⟨0, fun q =>
    if ∃ e : EdgeIdx L, edgeToQubitIdx L e = q ∧ c e = 1
    then PauliOperator.Z else PauliOperator.I⟩

/-- Recover a 1-chain from a Z-type Pauli element. -/
def chainOfZOperator (L : ℕ) (g : NQubitPauliGroupElement (toricNumQubits L)) : C1 L :=
  fun e => if g.operators (edgeToQubitIdx L e) = PauliOperator.Z then 1 else 0

/-- Roundtrip: chain → Z-operator → chain. -/
theorem chainOfZOperator_toricZOperatorOfChain (L : ℕ) (c : C1 L) :
    chainOfZOperator L (toricZOperatorOfChain L c) = c := by
  by_cases hL : 0 < L
  · letI : Fact (0 < L) := ⟨hL⟩
    ext e
    by_cases hce : c e = 1
    · have hex : ∃ e' : EdgeIdx L, edgeToQubitIdx L e' = edgeToQubitIdx L e ∧ c e' = 1 :=
        ⟨e, rfl, hce⟩
      simp [chainOfZOperator, toricZOperatorOfChain, hex, hce]
    · have hnot :
          ¬ ∃ e' : EdgeIdx L, edgeToQubitIdx L e' = edgeToQubitIdx L e ∧ c e' = 1 := by
        intro hx
        rcases hx with ⟨e', heq, he1⟩
        exact hce ((edgeToQubitIdx_injective (L := L) heq) ▸ he1)
      have hce0 : c e = 0 := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ (c e).val_lt) with h0 | h1
        · calc c e = ((c e).val : ZMod 2) := (ZMod.natCast_zmod_val (c e)).symm
               _ = 0 := by simp [h0]
        · exact absurd (by calc
              c e = ((c e).val : ZMod 2) := (ZMod.natCast_zmod_val (c e)).symm
              _ = 1 := by simp [h1]) hce
      simp [chainOfZOperator, toricZOperatorOfChain, hnot, hce0]
  · have hL0 : L = 0 := Nat.eq_zero_of_not_pos hL
    subst hL0
    ext e
    cases e with
    | h x y => exact (Fin.elim0 x)
    | v x y => exact (Fin.elim0 x)

/-- Support membership of `toricZOperatorOfChain` at an indexed edge qubit. -/
lemma mem_support_toricZOperatorOfChain_edgeToQubitIdx_iff
    (L : ℕ) [Fact (0 < L)] (c : C1 L) (e : EdgeIdx L) :
    edgeToQubitIdx L e ∈ (toricZOperatorOfChain L c).operators.support ↔ c e = 1 := by
  constructor
  · intro hmem
    by_contra hne
    have hnot :
        ¬ ∃ e' : EdgeIdx L, edgeToQubitIdx L e' = edgeToQubitIdx L e ∧ c e' = 1 := by
      intro hex
      rcases hex with ⟨e', heq, he1⟩
      have he' : e' = e := edgeToQubitIdx_injective L heq
      exact hne (he' ▸ he1)
    have hI : (toricZOperatorOfChain L c).operators (edgeToQubitIdx L e) = PauliOperator.I := by
      simp [toricZOperatorOfChain, hnot]
    have hneqI : (toricZOperatorOfChain L c).operators (edgeToQubitIdx L e) ≠ PauliOperator.I := by
      simpa [NQubitPauliOperator.support] using hmem
    exact hneqI hI
  · intro he1
    have hex : ∃ e' : EdgeIdx L, edgeToQubitIdx L e' = edgeToQubitIdx L e ∧ c e' = 1 :=
      ⟨e, rfl, he1⟩
    have hZ : (toricZOperatorOfChain L c).operators (edgeToQubitIdx L e) = PauliOperator.Z := by
      simp [toricZOperatorOfChain, hex]
    simp [NQubitPauliOperator.support, hZ]

-- ---------------------------------------------------------------------------
-- 2.  Dual cycle map and submodules
-- ---------------------------------------------------------------------------

/-- `toricDualBoundary`: the transpose of ∂₂, checking commutation with face stabs.
    A chain `c` is a dual cycle iff this map vanishes identically. -/
def toricDualBoundary (L : ℕ) [Fact (0 < L)] : C1 L →ₗ[ZMod 2] C2 L where
  toFun c := fun ⟨x, y⟩ =>
    c (EdgeIdx.h x y) + c (EdgeIdx.h x (next L y)) +
    c (EdgeIdx.v x y) + c (EdgeIdx.v (next L x) y)
  map_add' := by intro c d; ext ⟨x, y⟩; simp [add_assoc, add_comm, add_left_comm]
  map_smul' := by intro a c; ext ⟨x, y⟩; simp [mul_add]

/-- Dual cycles: Z-chains that commute with every face stabilizer. -/
def toricDualCycles (L : ℕ) [Fact (0 < L)] : Submodule (ZMod 2) (C1 L) :=
  LinearMap.ker (toricDualBoundary L)

/-- Dual boundaries: Z-chains that are products of vertex stabilizers. -/
noncomputable def toricDualBoundaries (L : ℕ) [Fact (0 < L)] : Submodule (ZMod 2) (C1 L) :=
  LinearMap.range (toricVertexCutMap (L := L))

/-- Every dual boundary is a dual cycle (∂₂ᵀ ∘ ∂₁ᵀ = 0). -/
theorem toricDualBoundaries_le_toricDualCycles (L : ℕ) [Fact (0 < L)] :
    toricDualBoundaries (L := L) ≤ toricDualCycles (L := L) := by
  intro c hc
  simp only [toricDualBoundaries, LinearMap.mem_range] at hc
  obtain ⟨s, rfl⟩ := hc
  simp only [toricDualCycles, LinearMap.mem_ker]
  ext ⟨x, y⟩
  -- Each edge-value appears twice in the sum; a + a = 0 in ZMod 2.
  simp [toricDualBoundary, toricVertexCutMap]
  grind

-- ---------------------------------------------------------------------------
-- 3.  Z-type predicates
-- ---------------------------------------------------------------------------

/-- Predicate: Z-chain operator commutes with every X face generator. -/
def zCommutesWithXChecks (L : ℕ) [Fact (2 ≤ L)] (c : C1 L) : Prop :=
  let g := toricZOperatorOfChain L c
  ∀ x ∈ StabilizerGroup.ToricCodeN.XGenerators L, x * g = g * x

/-- Predicate: Z-chain operator is a product of vertex (Z) generators. -/
def zIsStarProduct (L : ℕ) [Fact (2 ≤ L)] (c : C1 L) : Prop :=
  let g := toricZOperatorOfChain L c
  g ∈ Subgroup.closure (StabilizerGroup.ToricCodeN.ZGenerators L)

-- ---------------------------------------------------------------------------
-- 4.  Anticommutation API (mirrors the X version)
-- ---------------------------------------------------------------------------

set_option maxHeartbeats 800000 in
/-- Single-face commutation criterion: `toricZOperatorOfChain c` commutes with
    `faceStab x y` iff the dual-boundary value at `(x,y)` is zero. -/
theorem faceCheckCommutes_iff_dualBoundaryAt
    (L : ℕ) [Fact (2 ≤ L)] (c : C1 L) (x y : Fin L) :
    StabilizerGroup.ToricCodeN.faceStab L x y * toricZOperatorOfChain L c =
      toricZOperatorOfChain L c * StabilizerGroup.ToricCodeN.faceStab L x y
      ↔ toricDualBoundary L c (x, y) = 0 := by
  have hL0 : 0 < L := Nat.lt_of_lt_of_le (by decide : 0 < 2) (Fact.out : 2 ≤ L)
  haveI hL0f : Fact (0 < L) := ⟨hL0⟩
  -- Z-type predicate for toricZOperatorOfChain
  have hztype : NQubitPauliOperator.IsZType (toricZOperatorOfChain L c).operators := fun j => by
    simp only [toricZOperatorOfChain]
    by_cases h : ∃ e : EdgeIdx L, edgeToQubitIdx L e = j ∧ c e = 1
    · exact Or.inr (by simp [h])
    · exact Or.inl (by simp [h])
  -- Anticommutation criterion: XZ-type → anticommutes iff both in support
  have hanti_iff : ∀ i : Fin (StabilizerGroup.ToricCodeN.numQubits L),
      NQubitPauliGroupElement.anticommutesAt
          (StabilizerGroup.ToricCodeN.faceStab L x y).operators
          (toricZOperatorOfChain L c).operators i ↔
        i ∈ (StabilizerGroup.ToricCodeN.faceStab L x y).operators.support ∧
          i ∈ (toricZOperatorOfChain L c).operators.support :=
    fun i => NQubitPauliGroupElement.anticommutesAt_iff_mem_support_both_of_XZType
      (StabilizerGroup.ToricCodeN.faceStab_is_XType L x y).2 hztype i
  -- Equalities between edgeToQubitIdx and hEdge/vEdge
  have hh : ∀ (a b : Fin L), edgeToQubitIdx L (EdgeIdx.h a b) =
      StabilizerGroup.ToricCodeN.hEdge L a b :=
    fun a b => Fin.ext (by simp [edgeToQubitIdx, StabilizerGroup.ToricCodeN.hEdge])
  have hv : ∀ (a b : Fin L), edgeToQubitIdx L (EdgeIdx.v a b) =
      StabilizerGroup.ToricCodeN.vEdge L a b :=
    fun a b => Fin.ext (by simp [edgeToQubitIdx, StabilizerGroup.ToricCodeN.vEdge])
  -- Rewrite anticommutation filter to 4 conditions
  have hfilt_eq : ∀ i : Fin (StabilizerGroup.ToricCodeN.numQubits L),
      NQubitPauliGroupElement.anticommutesAt
          (StabilizerGroup.ToricCodeN.faceStab L x y).operators
          (toricZOperatorOfChain L c).operators i ↔
        (i = StabilizerGroup.ToricCodeN.hEdge L x y ∧ c (EdgeIdx.h x y) = 1) ∨
        (i = StabilizerGroup.ToricCodeN.hEdge L x (StabilizerGroup.ToricCodeN.next L y) ∧
          c (EdgeIdx.h x (StabilizerGroup.ToricCodeN.next L y)) = 1) ∨
        (i = StabilizerGroup.ToricCodeN.vEdge L x y ∧ c (EdgeIdx.v x y) = 1) ∨
        (i = StabilizerGroup.ToricCodeN.vEdge L (StabilizerGroup.ToricCodeN.next L x) y ∧
          c (EdgeIdx.v (StabilizerGroup.ToricCodeN.next L x) y) = 1) := by
    intro i
    rw [hanti_iff i]
    constructor
    · rintro ⟨hf, hz⟩
      rcases (StabilizerGroup.ToricCodeN.mem_support_faceStab_iff L x y i).mp hf
        with h1 | h2 | h3 | h4
      · left; refine ⟨h1, ?_⟩; subst h1
        rw [← hh x y] at hz
        exact (mem_support_toricZOperatorOfChain_edgeToQubitIdx_iff L c (EdgeIdx.h x y)).mp hz
      · right; left; refine ⟨h2, ?_⟩; subst h2
        rw [← hh x (StabilizerGroup.ToricCodeN.next L y)] at hz
        exact (mem_support_toricZOperatorOfChain_edgeToQubitIdx_iff L c
          (EdgeIdx.h x (StabilizerGroup.ToricCodeN.next L y))).mp hz
      · right; right; left; refine ⟨h3, ?_⟩; subst h3
        rw [← hv x y] at hz
        exact (mem_support_toricZOperatorOfChain_edgeToQubitIdx_iff L c (EdgeIdx.v x y)).mp hz
      · right; right; right; refine ⟨h4, ?_⟩; subst h4
        rw [← hv (StabilizerGroup.ToricCodeN.next L x) y] at hz
        exact (mem_support_toricZOperatorOfChain_edgeToQubitIdx_iff L c
          (EdgeIdx.v (StabilizerGroup.ToricCodeN.next L x) y)).mp hz
    · rintro (⟨h1, hc1⟩ | ⟨h2, hc2⟩ | ⟨h3, hc3⟩ | ⟨h4, hc4⟩)
      · constructor
        · exact (StabilizerGroup.ToricCodeN.mem_support_faceStab_iff L x y i).mpr (Or.inl h1)
        · subst h1; rw [← hh x y]
          exact (mem_support_toricZOperatorOfChain_edgeToQubitIdx_iff L c (EdgeIdx.h x y)).mpr hc1
      · constructor
        · exact (StabilizerGroup.ToricCodeN.mem_support_faceStab_iff L x y i).mpr
            (Or.inr (Or.inl h2))
        · subst h2; rw [← hh x (StabilizerGroup.ToricCodeN.next L y)]
          exact (mem_support_toricZOperatorOfChain_edgeToQubitIdx_iff L c
            (EdgeIdx.h x (StabilizerGroup.ToricCodeN.next L y))).mpr hc2
      · constructor
        · exact (StabilizerGroup.ToricCodeN.mem_support_faceStab_iff L x y i).mpr
            (Or.inr (Or.inr (Or.inl h3)))
        · subst h3; rw [← hv x y]
          exact (mem_support_toricZOperatorOfChain_edgeToQubitIdx_iff L c (EdgeIdx.v x y)).mpr hc3
      · constructor
        · exact (StabilizerGroup.ToricCodeN.mem_support_faceStab_iff L x y i).mpr
            (Or.inr (Or.inr (Or.inr h4)))
        · subst h4; rw [← hv (StabilizerGroup.ToricCodeN.next L x) y]
          exact (mem_support_toricZOperatorOfChain_edgeToQubitIdx_iff L c
            (EdgeIdx.v (StabilizerGroup.ToricCodeN.next L x) y)).mpr hc4
  -- Distinctness of the 4 face-edge qubits
  have h_distinct :
      StabilizerGroup.ToricCodeN.hEdge L x y ≠
        StabilizerGroup.ToricCodeN.hEdge L x (StabilizerGroup.ToricCodeN.next L y) ∧
      StabilizerGroup.ToricCodeN.hEdge L x y ≠ StabilizerGroup.ToricCodeN.vEdge L x y ∧
      StabilizerGroup.ToricCodeN.hEdge L x y ≠
        StabilizerGroup.ToricCodeN.vEdge L (StabilizerGroup.ToricCodeN.next L x) y ∧
      StabilizerGroup.ToricCodeN.hEdge L x (StabilizerGroup.ToricCodeN.next L y) ≠
        StabilizerGroup.ToricCodeN.vEdge L x y ∧
      StabilizerGroup.ToricCodeN.hEdge L x (StabilizerGroup.ToricCodeN.next L y) ≠
        StabilizerGroup.ToricCodeN.vEdge L (StabilizerGroup.ToricCodeN.next L x) y ∧
      StabilizerGroup.ToricCodeN.vEdge L x y ≠
        StabilizerGroup.ToricCodeN.vEdge L (StabilizerGroup.ToricCodeN.next L x) y :=
    ⟨fun h => next_ne_self L y
        ((StabilizerGroup.ToricCodeN.hEdge_eq_iff L x y x _).mp h).2.symm,
     StabilizerGroup.ToricCodeN.hEdge_ne_vEdge L x y x y,
     StabilizerGroup.ToricCodeN.hEdge_ne_vEdge L x y _ y,
     StabilizerGroup.ToricCodeN.hEdge_ne_vEdge L x _ x y,
     StabilizerGroup.ToricCodeN.hEdge_ne_vEdge L x _ _ y,
     fun h => next_ne_self L x
       ((StabilizerGroup.ToricCodeN.vEdge_eq_iff L x y _ y).mp h).1.symm⟩
  -- Enable classical instances for DecidablePred in the filter
  classical
  -- Compute cardinality of anticommuting qubits
  have hcard :
      (Finset.univ.filter (fun i : Fin (StabilizerGroup.ToricCodeN.numQubits L) =>
        NQubitPauliGroupElement.anticommutesAt
          (StabilizerGroup.ToricCodeN.faceStab L x y).operators
          (toricZOperatorOfChain L c).operators i)).card =
      (((if c (EdgeIdx.h x y) = 1 then 1 else 0) +
        (if c (EdgeIdx.h x (StabilizerGroup.ToricCodeN.next L y)) = 1 then 1 else 0) +
        (if c (EdgeIdx.v x y) = 1 then 1 else 0) +
        (if c (EdgeIdx.v (StabilizerGroup.ToricCodeN.next L x) y) = 1 then 1 else 0)) : ℕ) := by
    obtain ⟨hd1, hd2, hd3, hd4, hd5, hd6⟩ := h_distinct
    have hd1' := hd1.symm; have hd2' := hd2.symm; have hd3' := hd3.symm
    have hd4' := hd4.symm; have hd5' := hd5.symm; have hd6' := hd6.symm
    simp_rw [hfilt_eq]
    clear hfilt_eq hanti_iff
    split_ifs <;>
      simp_all +decide [Finset.filter_eq', Finset.filter_or, Finset.card_insert_of_notMem,
        Finset.mem_insert, Finset.mem_singleton,
        hd1, hd2, hd3, hd4, hd5, hd6, hd1', hd2', hd3', hd4', hd5', hd6']
  -- Parity bridge: even indicator sum ↔ ZMod 2 sum = 0
  have hbridge : ∀ (a b c d : ZMod 2),
      Even (((if a = 1 then 1 else 0) + (if b = 1 then 1 else 0) +
             (if c = 1 then 1 else 0) + (if d = 1 then 1 else 0)) : ℕ) ↔ a + b + c + d = 0 := by
    intro a b c d; fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide
  -- Assemble the proof
  rw [NQubitPauliGroupElement.commutes_iff_even_anticommutes, hcard]
  rw [show toricDualBoundary L c (x, y) =
      c (EdgeIdx.h x y) + c (EdgeIdx.h x (StabilizerGroup.ToricCodeN.next L y)) +
      c (EdgeIdx.v x y) + c (EdgeIdx.v (StabilizerGroup.ToricCodeN.next L x) y) from rfl]
  exact hbridge _ _ _ _

-- ---------------------------------------------------------------------------
-- 5.  Global commutation and cycle membership
-- ---------------------------------------------------------------------------

/-- Commutation with all face-X checks is equivalent to dual-cycle membership. -/
theorem zCommutesWithXChecks_iff_dualBoundary_pointwise_zero
    (L : ℕ) [Fact (2 ≤ L)] (c : C1 L) :
    zCommutesWithXChecks L c ↔
      ∀ p : FaceIdx L, toricDualBoundary L c p = 0 := by
  constructor
  · intro h ⟨xf, yf⟩
    have hx :
        StabilizerGroup.ToricCodeN.faceStab L xf yf ∈
          StabilizerGroup.ToricCodeN.XGenerators L :=
      ⟨(xf, yf), rfl⟩
    have hcomm := h (StabilizerGroup.ToricCodeN.faceStab L xf yf) hx
    exact (faceCheckCommutes_iff_dualBoundaryAt L c xf yf).mp hcomm
  · intro h z hz
    rcases hz with ⟨⟨xf, yf⟩, rfl⟩
    exact (faceCheckCommutes_iff_dualBoundaryAt L c xf yf).mpr (h (xf, yf))

/-- Dual-cycle membership iff dual boundary map vanishes. -/
theorem dualBoundary_pointwise_zero_iff_mem_toricDualCycles
    (L : ℕ) [Fact (2 ≤ L)] (c : C1 L) :
    (∀ p : FaceIdx L, toricDualBoundary L c p = 0) ↔
      c ∈ toricDualCycles (L := L) := by
  constructor
  · intro h
    change toricDualBoundary L c = 0
    ext p; exact h p
  · intro h p
    exact congrArg (fun f => f p) h

/-- Z-chain commutes with all face checks iff it is a dual cycle. -/
theorem zCommutesWithXChecks_iff_mem_toricDualCycles (L : ℕ) [Fact (2 ≤ L)] (c : C1 L) :
    zCommutesWithXChecks L c ↔ c ∈ toricDualCycles (L := L) :=
  (zCommutesWithXChecks_iff_dualBoundary_pointwise_zero L c).trans
    (dualBoundary_pointwise_zero_iff_mem_toricDualCycles L c)

-- ---------------------------------------------------------------------------
-- 6.  Vertex-stabilizer criterion (star product ↔ dual boundary)
-- ---------------------------------------------------------------------------

/-- `toricZOperatorOfChain` maps the zero chain to the identity element. -/
lemma toricZOperatorOfChain_zero (L : ℕ) :
    toricZOperatorOfChain L 0 = 1 := by
  unfold toricZOperatorOfChain
  aesop

set_option maxHeartbeats 1000000 in
/-- `toricZOperatorOfChain` maps chain addition to Pauli multiplication. -/
lemma toricZOperatorOfChain_add (L : ℕ) (c c' : C1 L) :
    toricZOperatorOfChain L (c + c') =
      toricZOperatorOfChain L c * toricZOperatorOfChain L c' := by
  simp [toricZOperatorOfChain] at *
  simp +decide [NQubitPauliGroupElement.mul, NQubitPauliGroupElement.mulOp]
  constructor
  · rw [Finset.sum_eq_zero]; aesop
  · ext q
    split_ifs <;> simp_all +decide [Fin.ext_iff, ZMod]
    · rename_i h₁ h₂ h₃
      obtain ⟨e₁, he₁, he₂⟩ := h₁
      obtain ⟨e₂, he₃, he₄⟩ := h₂
      obtain ⟨e₃, he₅, he₆⟩ := h₃
      have h_eq : e₁ = e₂ ∧ e₂ = e₃ := by
        have h_eq : ∀ e₁ e₂ : EdgeIdx L,
            edgeToQubitIdx L e₁ = edgeToQubitIdx L e₂ → e₁ = e₂ := by
          intros e₁ e₂ h_eq
          have h_eq' : edgeToQubitIdx L e₁ = edgeToQubitIdx L e₂ := h_eq
          simp [edgeToQubitIdx] at h_eq'
          rcases e₁ with (_ | _) <;> rcases e₂ with (_ | _) <;> norm_num at h_eq' ⊢
          · rename_i a b c d
            have h_eq' : b = d := by
              exact Fin.ext (by nlinarith [Fin.is_lt a, Fin.is_lt b, Fin.is_lt c, Fin.is_lt d])
            aesop
          · rename_i a b c d
            exact absurd h_eq'
              (by nlinarith only [Fin.is_lt a, Fin.is_lt b, Fin.is_lt c, Fin.is_lt d])
          · rename_i a b c d
            exact absurd h_eq'
              (by nlinarith [Fin.is_lt a, Fin.is_lt b, Fin.is_lt c, Fin.is_lt d])
          · rename_i a b c d
            have h_eq' : b = d := by
              exact Fin.ext (by nlinarith [Fin.is_lt a, Fin.is_lt b, Fin.is_lt c, Fin.is_lt d])
            aesop
        exact ⟨h_eq e₁ e₂ (Fin.ext <| by aesop), h_eq e₂ e₃ (Fin.ext <| by aesop)⟩
      grind
    · grind
    · grind
    · grind

/-- Helper: every 0-chain is a sum of single-vertex indicators. -/
private lemma c0_eq_sum_singleVtx (L : ℕ) (s : C0 L) :
    s = ∑ v ∈ Finset.univ.filter (fun v : VtxIdx L => s v = 1), singleVtx v := by
  ext v
  unfold singleVtx
  cases Fin.exists_fin_two.mp ⟨s v, rfl⟩ <;> simp +decide [*] <;>
    split_ifs <;> simp_all (config := {decide := true}) <;>
    first | rfl | exact absurd rfl ‹_›

set_option maxHeartbeats 800000 in
/-- `toricZOperatorOfChain` applied to `toricVertexCutMap (singleVtx (xv, yv))`
    equals the vertex stabilizer at `(xv, yv)`. -/
lemma toricZOperatorOfChain_cutMap_singleVtx (L : ℕ) [Fact (2 ≤ L)]
    (xv yv : Fin L) :
    toricZOperatorOfChain L (toricVertexCutMap (L := L) (singleVtx (xv, yv))) =
      StabilizerGroup.ToricCodeN.vertexStab L xv yv := by
  have hL0 : 0 < L := Nat.lt_of_lt_of_le (by decide : 0 < 2) (Fact.out : 2 ≤ L)
  haveI : Fact (0 < L) := ⟨hL0⟩
  unfold toricZOperatorOfChain StabilizerGroup.ToricCodeN.vertexStab
  congr with q
  split_ifs <;> simp_all +decide [NQubitPauliOperator.set]
  · rename_i h
    obtain ⟨e, rfl, he⟩ := h
    rcases e with ⟨ex, ey⟩ | ⟨ex, ey⟩
    · -- h-edge case: cutMap (singleVtx (xv,yv)) at h(ex,ey) = 1 means
      -- ((ex,ey) = (xv,yv)) XOR (next L ex = xv ∧ ey = yv)
      simp only [toricVertexCutMap, singleVtx] at he
      have hxL : (xv : ℕ) < L := xv.isLt
      have hyL : (yv : ℕ) < L := yv.isLt
      have hexL : (ex : ℕ) < L := ex.isLt
      have heyL : (ey : ℕ) < L := ey.isLt
      -- he is essentially Σ over the 2 disjuncts, but in ZMod 2.
      -- Decompose into cases by `decide`.
      by_cases h1 : (ex, ey) = (xv, yv)
      · obtain ⟨hex, hey⟩ := Prod.mk_inj.mp h1
        subst hex; subst hey
        unfold edgeToQubitIdx
        simp_all +decide [Fin.ext_iff, StabilizerGroup.ToricCodeN.hEdge,
          StabilizerGroup.ToricCodeN.vEdge, StabilizerGroup.ToricCodeN.prev,
          NQubitPauliOperator.identity]
      · by_cases h2 : (StabilizerGroup.ToricCodeN.next L ex, ey) = (xv, yv)
        · obtain ⟨hnex, hey⟩ := Prod.mk_inj.mp h2
          subst hey
          have hex_eq : ex = StabilizerGroup.ToricCodeN.prev L xv :=
            (Stabilizer.Lattice.eq_prev_iff_next_eq L ex xv).mpr hnex
          subst hex_eq
          unfold edgeToQubitIdx
          simp_all +decide [Fin.ext_iff, StabilizerGroup.ToricCodeN.hEdge,
            StabilizerGroup.ToricCodeN.vEdge, StabilizerGroup.ToricCodeN.prev,
            NQubitPauliOperator.identity]
        · exfalso
          simp [h1, h2] at he
    · -- v-edge case: cutMap (singleVtx (xv,yv)) at v(ex,ey) = 1 means
      -- ((ex,ey) = (xv,yv)) XOR (ex = xv ∧ next L ey = yv)
      simp only [toricVertexCutMap, singleVtx] at he
      have hxL : (xv : ℕ) < L := xv.isLt
      have hyL : (yv : ℕ) < L := yv.isLt
      have hexL : (ex : ℕ) < L := ex.isLt
      have heyL : (ey : ℕ) < L := ey.isLt
      by_cases h1 : (ex, ey) = (xv, yv)
      · obtain ⟨hex, hey⟩ := Prod.mk_inj.mp h1
        subst hex; subst hey
        unfold edgeToQubitIdx
        simp_all +decide [Fin.ext_iff, StabilizerGroup.ToricCodeN.hEdge,
          StabilizerGroup.ToricCodeN.vEdge, StabilizerGroup.ToricCodeN.prev,
          NQubitPauliOperator.identity]
      · by_cases h2 : (ex, StabilizerGroup.ToricCodeN.next L ey) = (xv, yv)
        · obtain ⟨hex, hney⟩ := Prod.mk_inj.mp h2
          subst hex
          have hey_eq : ey = StabilizerGroup.ToricCodeN.prev L yv :=
            (Stabilizer.Lattice.eq_prev_iff_next_eq L ey yv).mpr hney
          subst hey_eq
          unfold edgeToQubitIdx
          simp_all +decide [Fin.ext_iff, StabilizerGroup.ToricCodeN.hEdge,
            StabilizerGroup.ToricCodeN.vEdge, StabilizerGroup.ToricCodeN.prev,
            NQubitPauliOperator.identity]
        · exfalso
          simp [h1, h2] at he
  · -- neg case: q not in support of cutMap(singleVtx), must show vertexStab q = I
    split_ifs <;> simp_all +decide [toricNumQubits]
    · rename_i h₁ h₂
      contrapose! h₁
      refine ⟨EdgeIdx.v xv (StabilizerGroup.ToricCodeN.prev L yv), ?_, ?_⟩
      · rfl
      · have hne : (StabilizerGroup.ToricCodeN.prev L yv) ≠ yv :=
          Stabilizer.Lattice.prev_ne_self L yv
        simp [toricVertexCutMap, singleVtx, StabilizerGroup.ToricCodeN.prev,
          Stabilizer.Lattice.next_prev, hne, hne.symm]
    · rename_i h₁ h₂ h₃
      contrapose! h₁
      refine ⟨EdgeIdx.v xv yv, ?_, ?_⟩
      · rfl
      · have hne : StabilizerGroup.ToricCodeN.next L yv ≠ yv :=
          Stabilizer.Lattice.next_ne_self L yv
        simp [toricVertexCutMap, singleVtx, hne, hne.symm]
    · rename_i h₁ h₂ h₃ h₄
      contrapose! h₁
      refine ⟨EdgeIdx.h (StabilizerGroup.ToricCodeN.prev L xv) yv, ?_, ?_⟩
      · rfl
      · have hne : (StabilizerGroup.ToricCodeN.prev L xv) ≠ xv :=
          Stabilizer.Lattice.prev_ne_self L xv
        simp [toricVertexCutMap, singleVtx, StabilizerGroup.ToricCodeN.prev,
          Stabilizer.Lattice.next_prev, hne, hne.symm]
    · rename_i h₁ h₂ h₃ h₄ h₅
      contrapose! h₁
      refine ⟨EdgeIdx.h xv yv, ?_, ?_⟩
      · rfl
      · have hne : StabilizerGroup.ToricCodeN.next L xv ≠ xv :=
          Stabilizer.Lattice.next_ne_self L xv
        simp [toricVertexCutMap, singleVtx, hne, hne.symm]
    · unfold NQubitPauliOperator.identity; aesop

/-- Z-chain is a star product iff the chain is a dual boundary. -/
theorem zIsStarProduct_iff_mem_toricDualBoundaries (L : ℕ) [Fact (2 ≤ L)] (c : C1 L) :
    zIsStarProduct L c ↔ c ∈ toricDualBoundaries (L := L) := by
  constructor <;> intro hc <;>
    simp_all +decide [zIsStarProduct, toricDualBoundaries]
  · -- → direction: from closure(ZGen) to range(cutMap)
    have h_closure :
        ∀ g ∈ Subgroup.closure (StabilizerGroup.ToricCodeN.ZGenerators L),
          ∃ s : C0 L, toricZOperatorOfChain L (toricVertexCutMap (L := L) s) = g := by
      intro g hg
      induction' hg using Subgroup.closure_induction with g hg ih
      · rcases hg with ⟨⟨xv, yv⟩, rfl⟩
        exact ⟨singleVtx (xv, yv), toricZOperatorOfChain_cutMap_singleVtx L xv yv⟩
      · use 0
        simp only [map_zero, toricZOperatorOfChain_zero]
      · rename_i h₁ h₂ h₃ h₄
        obtain ⟨s₁, hs₁⟩ := h₃
        obtain ⟨s₂, hs₂⟩ := h₄
        use s₁ + s₂
        simp only [map_add]
        simp +decide [hs₁, hs₂, toricZOperatorOfChain_add]
      · obtain ⟨s, hs⟩ := ‹_›
        use s
        simp_all +decide [toricZOperatorOfChain]
        rw [← hs]
        ext <;> simp +decide [NQubitPauliGroupElement.inv]
    have hroundtrip := @chainOfZOperator_toricZOperatorOfChain L
    grind +splitImp
  · -- ← direction: from range(cutMap) to closure(ZGen)
    obtain ⟨s, rfl⟩ := hc
    rw [c0_eq_sum_singleVtx L s]
    simp only [map_sum]
    induction' (Finset.univ.filter fun v : VtxIdx L => s v = 1) using Finset.induction
      with a fs ha ih
    · simp only [Finset.sum_empty, map_zero, toricZOperatorOfChain_zero]
      exact OneMemClass.one_mem _
    · simp only [Finset.sum_insert ha, map_add, toricZOperatorOfChain_add]
      exact Subgroup.mul_mem _
        (by rcases a with ⟨xv, yv⟩
            rw [toricZOperatorOfChain_cutMap_singleVtx]
            exact Subgroup.subset_closure ⟨(xv, yv), rfl⟩)
        ih

-- ---------------------------------------------------------------------------
-- 7.  Centralizer membership
-- ---------------------------------------------------------------------------

/-- Z-type operators commute with all vertex stabs (Z-Z type commute). -/
lemma toricZOperatorOfChain_commutes_vertexStab
    (L : ℕ) [Fact (2 ≤ L)] (c : C1 L) (xv yv : Fin L) :
    StabilizerGroup.ToricCodeN.vertexStab L xv yv * toricZOperatorOfChain L c =
      toricZOperatorOfChain L c * StabilizerGroup.ToricCodeN.vertexStab L xv yv := by
  have hL0 : 0 < L := Nat.lt_of_lt_of_le (by decide : 0 < 2) (Fact.out : 2 ≤ L)
  haveI : Fact (0 < L) := ⟨hL0⟩
  have hzZtype : NQubitPauliGroupElement.IsZTypeElement (toricZOperatorOfChain L c) :=
    ⟨rfl, fun j => by
      simp only [toricZOperatorOfChain]
      by_cases h : ∃ e : EdgeIdx L, edgeToQubitIdx L e = j ∧ c e = 1
      · exact Or.inr (by simp [h])
      · exact Or.inl (by simp [h])⟩
  exact StabilizerGroup.CSSCommutationLemmas.ZType_commutes
    (StabilizerGroup.ToricCodeN.vertexStab_is_ZType L xv yv) hzZtype

/-- Centralizer membership for Z-chain operator ↔ dual-cycle membership. -/
lemma toricZOperatorOfChain_mem_centralizer_iff_dualCycle
    (L : ℕ) [Fact (2 ≤ L)] (c : C1 L) :
    toricZOperatorOfChain L c ∈
      StabilizerGroup.centralizer (StabilizerGroup.ToricCodeN.stabilizerGroup L) ↔
        c ∈ toricDualCycles (L := L) := by
  constructor
  · intro h
    apply (zCommutesWithXChecks_iff_mem_toricDualCycles L c).mp
    intro x hx
    apply h
    exact Subgroup.subset_closure
      (by rw [StabilizerGroup.ToricCodeN.listToSet_generatorsList]
          exact Set.mem_union_right _ hx)
  · intro hc
    have h_commX : zCommutesWithXChecks L c :=
      (zCommutesWithXChecks_iff_mem_toricDualCycles L c).mpr hc
    intro g hg
    have h_closure :
        g ∈ Subgroup.closure (StabilizerGroup.ToricCodeN.generators L) := by
      rw [StabilizerGroup.ToricCodeN.stabilizerGroup_toSubgroup_eq] at hg
      exact hg
    refine' Subgroup.closure_induction (fun x hx => _) _ _ _ h_closure
    · cases hx with
      | inl hx =>
          obtain ⟨⟨xv, yv⟩, rfl⟩ := hx
          exact toricZOperatorOfChain_commutes_vertexStab L c xv yv
      | inr hx =>
          obtain ⟨⟨xf, yf⟩, rfl⟩ := hx
          exact h_commX (StabilizerGroup.ToricCodeN.faceStab L xf yf) ⟨(xf, yf), rfl⟩
    · norm_num
    · grind
    · simp_all +decide [NQubitPauliGroupElement.mul, NQubitPauliGroupElement.inv]
      grind

-- ---------------------------------------------------------------------------
-- 8.  Stabilizer membership helpers
-- ---------------------------------------------------------------------------

/-- Any element with Z/I-only operators in the stabilizer has phase 0 (is Z-type). -/
private lemma zTypeOps_in_stabilizer_has_phase_zero
    (L : ℕ) [Fact (2 ≤ L)]
    (s : NQubitPauliGroupElement (StabilizerGroup.ToricCodeN.numQubits L))
    (hs : s ∈ (StabilizerGroup.ToricCodeN.stabilizerGroup L).toSubgroup)
    (hops : ∀ i, s.operators i = PauliOperator.Z ∨ s.operators i = PauliOperator.I) :
    NQubitPauliGroupElement.IsZTypeElement s := by
  have hs_cl : s ∈ Subgroup.closure
      (StabilizerGroup.ToricCodeN.ZGenerators L ∪
       StabilizerGroup.ToricCodeN.XGenerators L) := by
    rw [StabilizerGroup.ToricCodeN.stabilizerGroup_toSubgroup_eq] at hs; exact hs
  obtain ⟨z, hz, x, hx, hzx⟩ :=
    Subgroup.mem_closure_union_exists_mul_of_commute_generators
      (StabilizerGroup.ToricCodeN.ZGenerators_commute_XGenerators L) s hs_cl
  have hz_ty : NQubitPauliGroupElement.IsZTypeElement z :=
    NQubitPauliGroupElement.IsZTypeElement_of_mem_closure
      (StabilizerGroup.ToricCodeN.ZGenerators_are_ZType L) z hz
  have hx_ty : NQubitPauliGroupElement.IsXTypeElement x :=
    NQubitPauliGroupElement.IsXTypeElement_of_mem_closure
      (StabilizerGroup.ToricCodeN.XGenerators_are_XType L) x hx
  -- x must be identity: if z[i] ∈ {I,Z}, x[i] ∈ {I,X}, s[i] = z[i]*x[i] ∈ {Z,I},
  -- then x[i] must be I (Y and X are ruled out by s-type constraint)
  have hx_id : x = 1 := by
    have hx_ops_I : ∀ i, x.operators i = PauliOperator.I := by
      intro i
      have hsi := hops i
      rw [hzx] at hsi
      rcases hz_ty.2 i with hz_I | hz_Z
      · rcases hx_ty.2 i with hx_I | hx_X
        · exact hx_I
        · exfalso
          simp [NQubitPauliGroupElement.mul, NQubitPauliGroupElement.mulOp] at hsi
          rw [hz_I, hx_X] at hsi
          cases hsi with
          | inl h => simp [PauliOperator.mulOp] at h
          | inr h => simp [PauliOperator.mulOp] at h
      · rcases hx_ty.2 i with hx_I | hx_X
        · exact hx_I
        · exfalso
          simp [NQubitPauliGroupElement.mul, NQubitPauliGroupElement.mulOp] at hsi
          rw [hz_Z, hx_X] at hsi
          cases hsi with
          | inl h => simp [PauliOperator.mulOp] at h
          | inr h => simp [PauliOperator.mulOp] at h
    exact NQubitPauliGroupElement.ext x 1 hx_ty.1 (by ext i; simp [NQubitPauliOperator.identity, hx_ops_I i])
  rw [hzx, hx_id, mul_one]
  exact hz_ty

set_option maxHeartbeats 1000000 in
/-- Any Z-type element of the stabilizer is in `closure(ZGenerators)`. -/
lemma zType_in_stabilizerGroup_implies_in_ZClosure
    (L : ℕ) [Fact (2 ≤ L)]
    (g : NQubitPauliGroupElement (StabilizerGroup.ToricCodeN.numQubits L))
    (hg : g ∈ (StabilizerGroup.ToricCodeN.stabilizerGroup L).toSubgroup)
    (hzt : NQubitPauliGroupElement.IsZTypeElement g) :
    g ∈ Subgroup.closure (StabilizerGroup.ToricCodeN.ZGenerators L) := by
  have hg_closure :
      g ∈ Subgroup.closure
        ((StabilizerGroup.ToricCodeN.ZGenerators L) ∪
          (StabilizerGroup.ToricCodeN.XGenerators L)) := by
    rw [StabilizerGroup.ToricCodeN.stabilizerGroup_toSubgroup_eq] at hg
    exact hg
  obtain ⟨z, hz, x, hx, rfl⟩ :=
    Subgroup.mem_closure_union_exists_mul_of_commute_generators
      (StabilizerGroup.ToricCodeN.ZGenerators_commute_XGenerators L) g hg_closure
  have hz_ty : NQubitPauliGroupElement.IsZTypeElement z :=
    NQubitPauliGroupElement.IsZTypeElement_of_mem_closure
      (StabilizerGroup.ToricCodeN.ZGenerators_are_ZType L) z hz
  have hx_ty : NQubitPauliGroupElement.IsXTypeElement x :=
    NQubitPauliGroupElement.IsXTypeElement_of_mem_closure
      (StabilizerGroup.ToricCodeN.XGenerators_are_XType L) x hx
  -- x must be I since z*x is Z-type and z is Z-type
  have hx_zt : NQubitPauliGroupElement.IsZTypeElement x := by
    refine ⟨hx_ty.1, fun i => ?_⟩
    rcases hx_ty.2 i with hI | hX
    · exact Or.inl hI
    · exfalso
      rcases hz_ty.2 i with hz_I | hz_Z
      · have hgi := hzt.2 i
        simp [NQubitPauliGroupElement.mul, NQubitPauliGroupElement.mulOp] at hgi
        rw [hz_I, hX] at hgi
        cases hgi with
        | inl h => simp [PauliOperator.mulOp] at h
        | inr h => simp [PauliOperator.mulOp] at h
      · have hgi := hzt.2 i
        simp [NQubitPauliGroupElement.mul, NQubitPauliGroupElement.mulOp] at hgi
        rw [hz_Z, hX] at hgi
        cases hgi with
        | inl h => simp [PauliOperator.mulOp] at h
        | inr h => simp [PauliOperator.mulOp] at h
  have hx_id : x = 1 := by
    expose_names
    exact NQubitPauliGroupElement.eq_one_of_IsZTypeElement_and_IsXTypeElement
      hx_zt hx_ty
  rw [hx_id]; norm_num; assumption

/-- If `s ∈ stab` has the same operators as `toricZOperatorOfChain c`, then
    `c ∈ toricDualBoundaries`. -/
lemma stabilizer_same_ops_implies_dualBoundary
    (L : ℕ) [Fact (2 ≤ L)] (c : C1 L)
    (s : NQubitPauliGroupElement (StabilizerGroup.ToricCodeN.numQubits L))
    (hs : s ∈ (StabilizerGroup.ToricCodeN.stabilizerGroup L).toSubgroup)
    (heq : s.operators = (toricZOperatorOfChain L c).operators) :
    c ∈ toricDualBoundaries (L := L) := by
  have hops : ∀ i, s.operators i = PauliOperator.Z ∨ s.operators i = PauliOperator.I := by
    intro i; rw [heq]; simp only [toricZOperatorOfChain]
    by_cases h : ∃ e : EdgeIdx L, edgeToQubitIdx L e = i ∧ c e = 1
    · simp [h]
    · simp [h]
  have hzt : NQubitPauliGroupElement.IsZTypeElement s :=
    zTypeOps_in_stabilizer_has_phase_zero L s hs hops
  have hzcl : s ∈ Subgroup.closure (StabilizerGroup.ToricCodeN.ZGenerators L) :=
    zType_in_stabilizerGroup_implies_in_ZClosure L s hs hzt
  have h_eq : s = toricZOperatorOfChain L c :=
    NQubitPauliGroupElement.ext s (toricZOperatorOfChain L c)
      hzt.1 (by ext i; exact congrFun heq i)
  rw [h_eq] at hzcl
  exact (zIsStarProduct_iff_mem_toricDualBoundaries L c).mp hzcl

-- ---------------------------------------------------------------------------
-- 9.  Nontrivial logical ↔ dual cycle but not dual boundary
-- ---------------------------------------------------------------------------

set_option maxHeartbeats 1000000 in
/-- Z nontrivial logical iff corresponding chain is a dual-cycle-not-dual-boundary. -/
theorem zNontrivialLogical_iff_dualCycle_not_dualBoundary
    (L : ℕ) [Fact (2 ≤ L)] (c : C1 L) :
    StabilizerGroup.IsNontrivialLogicalOperator
        (toricZOperatorOfChain L c) (StabilizerGroup.ToricCodeN.stabilizerGroup L) ↔
      c ∈ toricDualCycles (L := L) ∧ c ∉ toricDualBoundaries (L := L) := by
  constructor <;> intro h
  · -- mp: nontrivial logical → dual cycle not dual boundary
    rw [StabilizerGroup.IsNontrivialLogicalOperator_iff] at h
    constructor
    · exact toricZOperatorOfChain_mem_centralizer_iff_dualCycle L c |>.1 h.1
    · intro hc
      have h_star :
          toricZOperatorOfChain L c ∈
            Subgroup.closure (StabilizerGroup.ToricCodeN.ZGenerators L) :=
        (zIsStarProduct_iff_mem_toricDualBoundaries L c).2 hc
      have h_in_stab :
          toricZOperatorOfChain L c ∈
            (StabilizerGroup.ToricCodeN.stabilizerGroup L).toSubgroup := by
        refine' Subgroup.closure_induction (fun x hx => _) _ _ _ h_star
        · exact Subgroup.subset_closure
            (by rw [StabilizerGroup.ToricCodeN.listToSet_generatorsList]
                exact Set.mem_union_left _ hx)
        · exact OneMemClass.one_mem _
        · exact fun x y _ _ hx hy => Subgroup.mul_mem _ hx hy
        · exact fun x _ hx => Subgroup.inv_mem _ hx
      exact h.2.1 h_in_stab
  · -- mpr: dual cycle not dual boundary → nontrivial logical
    rw [StabilizerGroup.IsNontrivialLogicalOperator_iff]
    refine ⟨?_, ?_, ?_⟩
    · exact toricZOperatorOfChain_mem_centralizer_iff_dualCycle L c |>.2 h.1
    · intro hg
      exact h.2 (stabilizer_same_ops_implies_dualBoundary L c
        (toricZOperatorOfChain L c) hg rfl)
    · intro s hs hEq
      exact h.2 (stabilizer_same_ops_implies_dualBoundary L c s hs hEq)

end Lattice
end Stabilizer
end Quantum
