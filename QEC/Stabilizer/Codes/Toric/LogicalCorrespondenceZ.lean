import Mathlib.Tactic
import QEC.Stabilizer.Codes.Toric.ChainOps
import QEC.Stabilizer.Codes.Toric.H1Dimension
import QEC.Stabilizer.Codes.Toric.ChainComplex
import QEC.Stabilizer.Framework.Homological.LogicalCorrespondence
import QEC.Stabilizer.Framework.Core.Logical.LogicalOperators

namespace Quantum
namespace Stabilizer
namespace Lattice

open scoped BigOperators
open scoped ToricChain

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
-- 1.  Dual cycle map and submodules (Z-operator encoding lives in
--     `ToricChainOps.lean` so the bridges in `ToricChainComplex.lean` can use it).
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
  LinearMap.range (δ⁰ (L := L))

/-- `Z¹ L` is the toric dual 1-cycle submodule `toricDualCycles L` (kernel of the dual
boundary). Scoped: `open scoped ToricChain`. -/
scoped[ToricChain] notation "Z¹" => Quantum.Stabilizer.Lattice.toricDualCycles

/-- `B¹ L` is the toric dual 1-boundary submodule `toricDualBoundaries L` (range of the
vertex cut map). Scoped: `open scoped ToricChain`. -/
scoped[ToricChain] notation "B¹" => Quantum.Stabilizer.Lattice.toricDualBoundaries


/-- Every dual boundary is a dual cycle (∂₂ᵀ ∘ ∂₁ᵀ = 0). -/
theorem toricDualBoundaries_le_toricDualCycles (L : ℕ) [Fact (0 < L)] :
    B¹ L ≤ Z¹ L := by
  intro c hc
  simp only [toricDualBoundaries, LinearMap.mem_range] at hc
  obtain ⟨s, rfl⟩ := hc
  simp only [toricDualCycles, LinearMap.mem_ker]
  ext ⟨x, y⟩
  -- Each edge-value appears twice in the sum; a + a = 0 in ZMod 2.
  simp [toricDualBoundary, toricVertexCutMap]
  grind

/-! ## §E bridges: lattice ↔ abstract dual structures

These bridges allow Z-side iff theorems to be delegated to the generic
`Homological.LogicalCorrespondence` theorems.  The bridges live here (rather
than in `ToricChainComplex.lean`) because `toricDualBoundary`,
`toricDualCycles`, `toricDualBoundaries` are defined in this file. -/

section DualBridges

variable (L : ℕ) [Fact (0 < L)]

/-- Bridge: the abstract `dualBoundaries` (range of `cutMap`) equals the lattice
`toricDualBoundaries` (range of `toricVertexCutMap`).  Follows directly from
`toricHomologicalCode_cutMap_eq`. -/
theorem toricHomologicalCode_dualBoundaries_eq :
    (toricHomologicalCode L).dualBoundaries = B¹ L := by
  unfold Homological.HomologicalCode.dualBoundaries toricDualBoundaries
  rw [toricHomologicalCode_cutMap_eq]
  rfl

/-- Bridge: the abstract `dualBoundary` linear map equals the lattice
`toricDualBoundary`.

Both are the `𝔽₂`-transpose of `toricBoundary2`.  The abstract one is defined
as `c ↦ λ p, ∑ e, c e * ∂₂(δ_p)(e)`; the toric one is the explicit 4-term sum
`c (h x y) + c (h x (next y)) + c (v x y) + c (v (next x) y)`.  We prove the
equality pointwise by splitting `EdgeIdx` into h-edges and v-edges and
identifying the four nonzero `∂₂(Pi.single (x, y) 1)` contributions. -/
theorem toricHomologicalCode_dualBoundary_eq :
    (toricHomologicalCode L).dualBoundary = toricDualBoundary (L := L) := by
  classical
  refine LinearMap.ext fun c => ?_
  funext ⟨x, y⟩
  -- LHS = ∑ e, c e * toricBoundary2 (Pi.single (x, y) 1) e
  -- RHS = c (h x y) + c (h x (next y)) + c (v x y) + c (v (next x) y)
  -- Strategy: split EdgeIdx into h and v via `edgeIdxEquivSum`, expand
  -- `toricBoundary2 (Pi.single (x, y) 1)` pointwise, and identify the 4 nonzero terms.
  change ∑ e : EdgeIdx L,
        c e * ∂₂ (L := L) (Pi.single (x, y) (1 : ZMod 2)) e
    = c (EdgeIdx.h x y) + c (EdgeIdx.h x (StabilizerGroup.ToricCodeN.next L y))
      + c (EdgeIdx.v x y) + c (EdgeIdx.v (StabilizerGroup.ToricCodeN.next L x) y)
  -- Step 1: rewrite the EdgeIdx-sum as a `Sum`-sum via `edgeIdxEquivSum`.
  rw [← Equiv.sum_comp (edgeIdxEquivSum L).symm
        (fun e : EdgeIdx L =>
          c e * ∂₂ (L := L) (Pi.single (x, y) (1 : ZMod 2)) e),
      Fintype.sum_sum_type]
  -- Step 2: reduce each VtxIdx-sum.
  -- h-edges:
  --   ∑ p, c (h p.1 p.2) * (Pi.single (x, y) 1 (p.1, p.2) +
  --                          Pi.single (x, y) 1 (p.1, prev p.2))
  --   = c (h x y) + c (h x (next y))   (by Pi.single isolates one term in each)
  have h_eq_prev_iff : ∀ {a b : Fin L},
      StabilizerGroup.ToricCodeN.prev L a = b
        ↔ a = StabilizerGroup.ToricCodeN.next L b := by
    intros a b
    constructor
    · intro h
      subst h
      exact (Stabilizer.Lattice.next_prev L a).symm
    · intro h
      subst h
      exact Stabilizer.Lattice.prev_next L b
  have hh :
      ∑ p : VtxIdx L,
          (fun e : EdgeIdx L =>
              c e * ∂₂ (L := L) (Pi.single (x, y) (1 : ZMod 2)) e)
            ((edgeIdxEquivSum L).symm (Sum.inl p))
      = c (EdgeIdx.h x y) + c (EdgeIdx.h x (StabilizerGroup.ToricCodeN.next L y)) := by
    -- Rewrite `(edgeIdxEquivSum L).symm (Sum.inl p) = h p.1 p.2`
    simp only [show ∀ p : VtxIdx L,
        (edgeIdxEquivSum L).symm (Sum.inl p) = EdgeIdx.h p.1 p.2 by
      rintro ⟨_, _⟩; rfl]
    -- Unfold `toricBoundary2 (Pi.single (x, y) 1) (h p.1 p.2)`.
    have heval : ∀ p : VtxIdx L,
        ∂₂ (L := L) (Pi.single (x, y) (1 : ZMod 2)) (EdgeIdx.h p.1 p.2)
          = (if (p.1, p.2) = (x, y) then (1 : ZMod 2) else 0)
            + (if (p.1, StabilizerGroup.ToricCodeN.prev L p.2) = (x, y)
                then 1 else 0) := by
      intro p; simp [toricBoundary2, Pi.single_apply]
    simp_rw [heval, mul_add, Finset.sum_add_distrib]
    -- Now we have two sums to evaluate.
    -- First: ∑ p, c (h p.1 p.2) * [(p.1, p.2) = (x, y)] = c (h x y)
    have h1 :
        ∑ p : VtxIdx L,
            c (EdgeIdx.h p.1 p.2) * (if (p.1, p.2) = (x, y) then (1 : ZMod 2) else 0)
        = c (EdgeIdx.h x y) := by
      rw [Finset.sum_eq_single ((x, y) : VtxIdx L)]
      · simp
      · intros p _ hne; rw [if_neg hne]; ring
      · intro h; exact absurd (Finset.mem_univ _) h
    -- Second: ∑ p, c (h p.1 p.2) * [(p.1, prev p.2) = (x, y)] = c (h x (next y))
    have h2 :
        ∑ p : VtxIdx L,
            c (EdgeIdx.h p.1 p.2)
              * (if (p.1, StabilizerGroup.ToricCodeN.prev L p.2) = (x, y)
                  then (1 : ZMod 2) else 0)
        = c (EdgeIdx.h x (StabilizerGroup.ToricCodeN.next L y)) := by
      rw [Finset.sum_eq_single ((x, StabilizerGroup.ToricCodeN.next L y) : VtxIdx L)]
      · -- The indicator at (x, next y) is 1 (since prev (next y) = y).
        rw [if_pos]
        · ring
        · refine Prod.mk.injEq _ _ _ _ |>.mpr ⟨rfl, ?_⟩
          exact Stabilizer.Lattice.prev_next L y
      · intros p _ hne
        rw [if_neg]
        · ring
        · intro hcontra
          apply hne
          have hp1 : p.1 = x := (Prod.mk.injEq _ _ _ _).mp hcontra |>.1
          have hp2 : StabilizerGroup.ToricCodeN.prev L p.2 = y :=
            (Prod.mk.injEq _ _ _ _).mp hcontra |>.2
          refine Prod.mk.injEq _ _ _ _ |>.mpr ⟨hp1, ?_⟩
          exact h_eq_prev_iff.mp hp2
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [h1, h2]
  -- v-edges: symmetric.
  have hv :
      ∑ p : VtxIdx L,
          (fun e : EdgeIdx L =>
              c e * ∂₂ (L := L) (Pi.single (x, y) (1 : ZMod 2)) e)
            ((edgeIdxEquivSum L).symm (Sum.inr p))
      = c (EdgeIdx.v x y) + c (EdgeIdx.v (StabilizerGroup.ToricCodeN.next L x) y) := by
    simp only [show ∀ p : VtxIdx L,
        (edgeIdxEquivSum L).symm (Sum.inr p) = EdgeIdx.v p.1 p.2 by
      rintro ⟨_, _⟩; rfl]
    have heval : ∀ p : VtxIdx L,
        ∂₂ (L := L) (Pi.single (x, y) (1 : ZMod 2)) (EdgeIdx.v p.1 p.2)
          = (if (p.1, p.2) = (x, y) then (1 : ZMod 2) else 0)
            + (if (StabilizerGroup.ToricCodeN.prev L p.1, p.2) = (x, y)
                then 1 else 0) := by
      intro p; simp [toricBoundary2, Pi.single_apply]
    simp_rw [heval, mul_add, Finset.sum_add_distrib]
    have h1 :
        ∑ p : VtxIdx L,
            c (EdgeIdx.v p.1 p.2) * (if (p.1, p.2) = (x, y) then (1 : ZMod 2) else 0)
        = c (EdgeIdx.v x y) := by
      rw [Finset.sum_eq_single ((x, y) : VtxIdx L)]
      · simp
      · intros p _ hne; rw [if_neg hne]; ring
      · intro h; exact absurd (Finset.mem_univ _) h
    have h2 :
        ∑ p : VtxIdx L,
            c (EdgeIdx.v p.1 p.2)
              * (if (StabilizerGroup.ToricCodeN.prev L p.1, p.2) = (x, y)
                  then (1 : ZMod 2) else 0)
        = c (EdgeIdx.v (StabilizerGroup.ToricCodeN.next L x) y) := by
      rw [Finset.sum_eq_single ((StabilizerGroup.ToricCodeN.next L x, y) : VtxIdx L)]
      · rw [if_pos]
        · ring
        · refine Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, rfl⟩
          exact Stabilizer.Lattice.prev_next L x
      · intros p _ hne
        rw [if_neg]
        · ring
        · intro hcontra
          apply hne
          have hp1 : StabilizerGroup.ToricCodeN.prev L p.1 = x :=
            (Prod.mk.injEq _ _ _ _).mp hcontra |>.1
          have hp2 : p.2 = y := (Prod.mk.injEq _ _ _ _).mp hcontra |>.2
          refine Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, hp2⟩
          exact h_eq_prev_iff.mp hp1
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [h1, h2]
  rw [hh, hv]
  ring

/-- Bridge: the abstract `dualCycles` (kernel of abstract `dualBoundary`) equals
the lattice `toricDualCycles` (kernel of `toricDualBoundary`). -/
theorem toricHomologicalCode_dualCycles_eq :
    (toricHomologicalCode L).dualCycles = Z¹ L := by
  unfold Homological.HomologicalCode.dualCycles toricDualCycles
  rw [toricHomologicalCode_dualBoundary_eq]
  rfl

end DualBridges

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
-- maxHeartbeats bumped: pointwise commutation reasoning over all qubits in the lattice,
-- with `simp_all +decide` over many `PauliOperator` cases.
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
        Finset.mem_insert, Finset.mem_singleton]
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
      c ∈ Z¹ L := by
  constructor
  · intro h
    change toricDualBoundary L c = 0
    ext p; exact h p
  · intro h p
    exact congrArg (fun f => f p) h

/-- Z-chain commutes with all face checks iff it is a dual cycle.

Delegates to the generic `chainZOperator_commutes_XGenerators_iff_mem_dualCycles`
via the X-generator and dual-cycle bridges. -/
theorem zCommutesWithXChecks_iff_mem_toricDualCycles (L : ℕ) [Fact (2 ≤ L)] (c : C1 L) :
    zCommutesWithXChecks L c ↔ c ∈ Z¹ L := by
  haveI : Fact (0 < L) := ⟨Nat.lt_of_lt_of_le (by decide : 0 < 2) Fact.out⟩
  unfold zCommutesWithXChecks
  rw [← toricHomologicalCode_XGenerators_eq, ← toricHomologicalCode_dualCycles_eq]
  exact (toricHomologicalCode L).chainZOperator_commutes_XGenerators_iff_mem_dualCycles c

-- ---------------------------------------------------------------------------
-- 6.  Vertex-stabilizer criterion (star product ↔ dual boundary)
-- ---------------------------------------------------------------------------

/-- Helper: every 0-chain is a sum of single-vertex indicators. -/
private lemma c0_eq_sum_singleVtx (L : ℕ) (s : C0 L) :
    s = ∑ v ∈ Finset.univ.filter (fun v : VtxIdx L => s v = 1), singleVtx v := by
  ext v
  unfold singleVtx
  cases Fin.exists_fin_two.mp ⟨s v, rfl⟩ <;> simp +decide [*] <;>
    split_ifs <;> simp_all (config := {decide := true}) <;>
    first | rfl | exact absurd rfl ‹_›

/-- Z-chain is a star product iff the chain is a dual boundary.

Delegates to the generic `chainZOperator_mem_ZClosure_iff_mem_dualBoundaries`
via the Z-generator and dual-boundary bridges. -/
theorem zIsStarProduct_iff_mem_toricDualBoundaries (L : ℕ) [Fact (2 ≤ L)] (c : C1 L) :
    zIsStarProduct L c ↔ c ∈ B¹ L := by
  haveI : Fact (0 < L) := ⟨Nat.lt_of_lt_of_le (by decide : 0 < 2) Fact.out⟩
  unfold zIsStarProduct
  rw [← toricHomologicalCode_ZGenerators_eq, ← toricHomologicalCode_dualBoundaries_eq]
  exact (toricHomologicalCode L).chainZOperator_mem_ZClosure_iff_mem_dualBoundaries c

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
        c ∈ Z¹ L := by
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
    refine Subgroup.closure_induction (fun x hx => ?_) ?_ ?_ ?_ h_closure
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
    exact NQubitPauliGroupElement.ext x 1 hx_ty.1
      (by ext i; simp [NQubitPauliOperator.identity, hx_ops_I i])
  rw [hzx, hx_id, mul_one]
  exact hz_ty

set_option maxHeartbeats 1000000 in
-- maxHeartbeats bumped: closure-membership argument reduces to commutation checks
-- across the full Z-generator set.
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
    c ∈ B¹ L := by
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

/-- Z nontrivial logical iff corresponding chain is a dual-cycle-not-dual-boundary.

Delegates to the generic `chainZOperator_isNontrivialLogical_iff` via the
stabilizer-subgroup bridge and the dual cycle/boundary bridges. -/
theorem zNontrivialLogical_iff_dualCycle_not_dualBoundary
    (L : ℕ) [Fact (2 ≤ L)] (c : C1 L) :
    StabilizerGroup.IsNontrivialLogicalOperator
        (toricZOperatorOfChain L c) (StabilizerGroup.ToricCodeN.stabilizerGroup L) ↔
      c ∈ Z¹ L ∧ c ∉ B¹ L := by
  haveI : Fact (0 < L) := ⟨Nat.lt_of_lt_of_le (by decide : 0 < 2) Fact.out⟩
  -- Translate the lattice `IsNontrivialLogicalOperator` to the abstract one
  -- via the subgroup bridge.
  have h_sub_eq :
      (StabilizerGroup.ToricCodeN.stabilizerGroup L).toSubgroup =
        (toricHomologicalCode L).homologicalStabilizerGroup.toSubgroup :=
    (toricHomologicalCode_homologicalStabilizerGroup_toSubgroup_eq L).symm
  rw [StabilizerGroup.IsNontrivialLogicalOperator_of_toSubgroup_eq _ h_sub_eq,
      ← toricHomologicalCode_dualCycles_eq, ← toricHomologicalCode_dualBoundaries_eq]
  -- `toricZOperatorOfChain L c = (toricHomologicalCode L).chainZOperator c` by `rfl`.
  exact (toricHomologicalCode L).chainZOperator_isNontrivialLogical_iff c

end Lattice
end Stabilizer
end Quantum
