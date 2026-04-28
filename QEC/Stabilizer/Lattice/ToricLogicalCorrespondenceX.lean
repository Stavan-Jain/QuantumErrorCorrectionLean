import Mathlib.Tactic
import QEC.Stabilizer.Lattice.ToricOperatorChains
import QEC.Stabilizer.Lattice.ToricHomology
import QEC.Stabilizer.Codes.ToricCodeN
import QEC.Stabilizer.Core.LogicalOperators


namespace Quantum
namespace Stabilizer
namespace Lattice

open scoped BigOperators

/-- Support membership of `toricXOperatorOfChain` at an indexed edge qubit. -/
lemma mem_support_toricXOperatorOfChain_edgeToQubitIdx_iff
    (L : ℕ) [Fact (0 < L)] (c : C1 L) (e : EdgeIdx L) :
    edgeToQubitIdx L e ∈ (toricXOperatorOfChain L c).operators.support ↔ c e = 1 := by
  constructor
  · intro hmem
    by_contra hne
    have hnot :
        ¬ ∃ e' : EdgeIdx L, edgeToQubitIdx L e' = edgeToQubitIdx L e ∧ c e' = 1 := by
      intro hex
      rcases hex with ⟨e', heq, he1⟩
      have he' : e' = e := edgeToQubitIdx_injective L heq
      exact hne (he' ▸ he1)
    have hI : (toricXOperatorOfChain L c).operators (edgeToQubitIdx L e) = PauliOperator.I := by
      simp [toricXOperatorOfChain, hnot]
    have hneqI : (toricXOperatorOfChain L c).operators (edgeToQubitIdx L e) ≠ PauliOperator.I := by
      simpa [NQubitPauliOperator.support] using hmem
    exact hneqI hI
  · intro he1
    have hex : ∃ e' : EdgeIdx L, edgeToQubitIdx L e' = edgeToQubitIdx L e ∧ c e' = 1 :=
      ⟨e, rfl, he1⟩
    have hX : (toricXOperatorOfChain L c).operators (edgeToQubitIdx L e) = PauliOperator.X := by
      simp [toricXOperatorOfChain, hex]
    simp [NQubitPauliOperator.support, hX]

/-- Predicate: encoded X-chain operator commutes with every Z-check (vertex) generator. -/
def xCommutesWithZChecks (L : ℕ) [Fact (2 ≤ L)] (c : C1 L) : Prop :=
  let g := toricXOperatorOfChain L c
  ∀ z ∈ StabilizerGroup.ToricCodeN.ZGenerators L, z * g = g * z

/-- Predicate: encoded X-chain operator is a product of X plaquette (face) generators. -/
def xIsPlaquetteProduct (L : ℕ) [Fact (2 ≤ L)] (c : C1 L) : Prop :=
  let g := toricXOperatorOfChain L c
  g ∈ Subgroup.closure (StabilizerGroup.ToricCodeN.XGenerators L)

/-- First incident qubit index at vertex `(xv,yv)` (horizontal, outgoing). -/
abbrev incidentQubitIdx1 (L : ℕ) [Fact (2 ≤ L)] (xv yv : Fin L) :
    Fin (StabilizerGroup.ToricCodeN.numQubits L) :=
  StabilizerGroup.ToricCodeN.hEdge L xv yv

/-- Second incident qubit index at vertex `(xv,yv)` (horizontal, incoming). -/
abbrev incidentQubitIdx2 (L : ℕ) [Fact (2 ≤ L)] (xv yv : Fin L) :
    Fin (StabilizerGroup.ToricCodeN.numQubits L) :=
  StabilizerGroup.ToricCodeN.hEdge L (StabilizerGroup.ToricCodeN.prev L xv) yv

/-- Third incident qubit index at vertex `(xv,yv)` (vertical, outgoing). -/
abbrev incidentQubitIdx3 (L : ℕ) [Fact (2 ≤ L)] (xv yv : Fin L) :
    Fin (StabilizerGroup.ToricCodeN.numQubits L) :=
  StabilizerGroup.ToricCodeN.vEdge L xv yv

/-- Fourth incident qubit index at vertex `(xv,yv)` (vertical, incoming). -/
abbrev incidentQubitIdx4 (L : ℕ) [Fact (2 ≤ L)] (xv yv : Fin L) :
    Fin (StabilizerGroup.ToricCodeN.numQubits L) :=
  StabilizerGroup.ToricCodeN.vEdge L xv (StabilizerGroup.ToricCodeN.prev L yv)

/-- Mid-level API: pointwise anticommutation criterion against a fixed vertex check. -/
theorem anticommutesAt_vertexStab_toricX_iff
    (L : ℕ) [Fact (2 ≤ L)] (c : C1 L) (xv yv : Fin L)
    (i : Fin (StabilizerGroup.ToricCodeN.numQubits L)) :
    NQubitPauliGroupElement.anticommutesAt
        (StabilizerGroup.ToricCodeN.vertexStab L xv yv).operators
        (toricXOperatorOfChain L c).operators i
      ↔
        i ∈ (StabilizerGroup.ToricCodeN.vertexStab L xv yv).operators.support ∧
        i ∈ (toricXOperatorOfChain L c).operators.support := by
  have hL0 : 0 < L := Nat.lt_of_lt_of_le (by decide : 0 < 2) (Fact.out : 2 ≤ L)
  haveI : Fact (0 < L) := ⟨hL0⟩
  have hxType : NQubitPauliOperator.IsXType (toricXOperatorOfChain L c).operators := by
    intro j
    by_cases h : ∃ e : EdgeIdx L, edgeToQubitIdx L e = j ∧ c e = 1
    · right
      simp [toricXOperatorOfChain, h]
    · left
      simp [toricXOperatorOfChain, h]
  exact NQubitPauliGroupElement.anticommutesAt_iff_mem_support_both_of_ZXType
    (StabilizerGroup.ToricCodeN.vertexStab_is_ZType L xv yv).2 hxType i

/-- Mid-level API: anticommutation occurs exactly on the four incident qubits
whose corresponding chain coordinates are active. -/
theorem anticommutesAt_vertexStab_toricX_iff_oneOfFour
    (L : ℕ) [Fact (2 ≤ L)] (c : C1 L) (xv yv : Fin L)
    (i : Fin (StabilizerGroup.ToricCodeN.numQubits L)) :
    NQubitPauliGroupElement.anticommutesAt
        (StabilizerGroup.ToricCodeN.vertexStab L xv yv).operators
        (toricXOperatorOfChain L c).operators i
      ↔
        (i = incidentQubitIdx1 L xv yv ∧ c (EdgeIdx.h xv yv) = 1) ∨
        (i = incidentQubitIdx2 L xv yv ∧
          c (EdgeIdx.h (StabilizerGroup.ToricCodeN.prev L xv) yv) = 1) ∨
        (i = incidentQubitIdx3 L xv yv ∧ c (EdgeIdx.v xv yv) = 1) ∨
        (i = incidentQubitIdx4 L xv yv ∧
          c (EdgeIdx.v xv (StabilizerGroup.ToricCodeN.prev L yv)) = 1) := by
  have hL0 : 0 < L := Nat.lt_of_lt_of_le (by decide : 0 < 2) (Fact.out : 2 ≤ L)
  haveI : Fact (0 < L) := ⟨hL0⟩
  rw [anticommutesAt_vertexStab_toricX_iff]
  rw [StabilizerGroup.ToricCodeN.mem_support_vertexStab_iff]
  constructor
  · rintro ⟨hV, hX⟩
    rcases hV with h1 | h2 | h3 | h4
    · left
      refine ⟨h1, ?_⟩
      subst h1
      simpa [incidentQubitIdx1, StabilizerGroup.ToricCodeN.hEdge, edgeToQubitIdx] using
        (mem_support_toricXOperatorOfChain_edgeToQubitIdx_iff L c (EdgeIdx.h xv yv)).1 hX
    · right
      left
      refine ⟨h2, ?_⟩
      subst h2
      simpa [incidentQubitIdx2, StabilizerGroup.ToricCodeN.hEdge, edgeToQubitIdx] using
        (mem_support_toricXOperatorOfChain_edgeToQubitIdx_iff L c
          (EdgeIdx.h (StabilizerGroup.ToricCodeN.prev L xv) yv)).1 hX
    · right
      right
      left
      refine ⟨h3, ?_⟩
      subst h3
      simpa [incidentQubitIdx3, StabilizerGroup.ToricCodeN.vEdge, edgeToQubitIdx] using
        (mem_support_toricXOperatorOfChain_edgeToQubitIdx_iff L c (EdgeIdx.v xv yv)).1 hX
    · right
      right
      right
      refine ⟨h4, ?_⟩
      subst h4
      simpa [incidentQubitIdx4, StabilizerGroup.ToricCodeN.vEdge, edgeToQubitIdx] using
        (mem_support_toricXOperatorOfChain_edgeToQubitIdx_iff L c
          (EdgeIdx.v xv (StabilizerGroup.ToricCodeN.prev L yv))).1 hX
  · intro h
    rcases h with h1 | h2 | h3 | h4
    · rcases h1 with ⟨h1, hc1⟩
      refine ⟨Or.inl h1, ?_⟩
      subst h1
      simpa [incidentQubitIdx1, StabilizerGroup.ToricCodeN.hEdge, edgeToQubitIdx] using
        (mem_support_toricXOperatorOfChain_edgeToQubitIdx_iff L c (EdgeIdx.h xv yv)).2 hc1
    · rcases h2 with ⟨h2, hc2⟩
      refine ⟨Or.inr (Or.inl h2), ?_⟩
      subst h2
      simpa [incidentQubitIdx2, StabilizerGroup.ToricCodeN.hEdge, edgeToQubitIdx] using
        (mem_support_toricXOperatorOfChain_edgeToQubitIdx_iff L c
          (EdgeIdx.h (StabilizerGroup.ToricCodeN.prev L xv) yv)).2 hc2
    · rcases h3 with ⟨h3, hc3⟩
      refine ⟨Or.inr (Or.inr (Or.inl h3)), ?_⟩
      subst h3
      simpa [incidentQubitIdx3, StabilizerGroup.ToricCodeN.vEdge, edgeToQubitIdx] using
        (mem_support_toricXOperatorOfChain_edgeToQubitIdx_iff L c (EdgeIdx.v xv yv)).2 hc3
    · rcases h4 with ⟨h4, hc4⟩
      refine ⟨Or.inr (Or.inr (Or.inr h4)), ?_⟩
      subst h4
      simpa [incidentQubitIdx4, StabilizerGroup.ToricCodeN.vEdge, edgeToQubitIdx] using
        (mem_support_toricXOperatorOfChain_edgeToQubitIdx_iff L c
          (EdgeIdx.v xv (StabilizerGroup.ToricCodeN.prev L yv))).2 hc4

/-- Mid-level API: global anticommutation set equals a filtered four-point set. -/
theorem anticommute_filter_eq_four_filter
    (L : ℕ) [Fact (2 ≤ L)] (c : C1 L) (xv yv : Fin L) :
    ∀ i : Fin (StabilizerGroup.ToricCodeN.numQubits L),
      NQubitPauliGroupElement.anticommutesAt
          (StabilizerGroup.ToricCodeN.vertexStab L xv yv).operators
          (toricXOperatorOfChain L c).operators i
      ↔
        (i = incidentQubitIdx1 L xv yv ∨ i = incidentQubitIdx2 L xv yv ∨
          i = incidentQubitIdx3 L xv yv ∨ i = incidentQubitIdx4 L xv yv) ∧
        NQubitPauliGroupElement.anticommutesAt
          (StabilizerGroup.ToricCodeN.vertexStab L xv yv).operators
          (toricXOperatorOfChain L c).operators i := by
  intro i
  constructor
  · intro hanti
    have hone := (anticommutesAt_vertexStab_toricX_iff_oneOfFour L c xv yv i).1 hanti
    rcases hone with h1 | h2 | h3 | h4
    · exact ⟨Or.inl h1.1, hanti⟩
    · exact ⟨Or.inr (Or.inl h2.1), hanti⟩
    · exact ⟨Or.inr (Or.inr (Or.inl h3.1)), hanti⟩
    · exact ⟨Or.inr (Or.inr (Or.inr h4.1)), hanti⟩
  · intro h
    exact h.2

/-
Mid-level API: cardinality of the four-point anticommutation filter equals the
sum of the corresponding edge-indicators.
-/
set_option maxHeartbeats 1000000 in
-- The distinct-incident-edge case split is arithmetic-heavy and needs extra heartbeats.
theorem four_filter_card_eq_indicator_sum
    (L : ℕ) [Fact (2 ≤ L)] (c : C1 L) (xv yv : Fin L) :
    (Finset.univ.filter
      (fun i : Fin (StabilizerGroup.ToricCodeN.numQubits L) =>
      (i = incidentQubitIdx1 L xv yv ∧ c (EdgeIdx.h xv yv) = 1) ∨
      (i = incidentQubitIdx2 L xv yv ∧
        c (EdgeIdx.h (StabilizerGroup.ToricCodeN.prev L xv) yv) = 1) ∨
      (i = incidentQubitIdx3 L xv yv ∧ c (EdgeIdx.v xv yv) = 1) ∨
      (i = incidentQubitIdx4 L xv yv ∧
        c (EdgeIdx.v xv (StabilizerGroup.ToricCodeN.prev L yv)) = 1))).card
      =
    (((if c (EdgeIdx.h xv yv) = 1 then 1 else 0) +
      (if c (EdgeIdx.h (StabilizerGroup.ToricCodeN.prev L xv) yv) = 1 then 1 else 0) +
      (if c (EdgeIdx.v xv yv) = 1 then 1 else 0) +
      (if c (EdgeIdx.v xv (StabilizerGroup.ToricCodeN.prev L yv)) = 1 then 1 else 0)) : ℕ) := by
  have h_distinct :
      incidentQubitIdx1 L xv yv ≠ incidentQubitIdx2 L xv yv ∧
      incidentQubitIdx1 L xv yv ≠ incidentQubitIdx3 L xv yv ∧
      incidentQubitIdx1 L xv yv ≠ incidentQubitIdx4 L xv yv ∧
      incidentQubitIdx2 L xv yv ≠ incidentQubitIdx3 L xv yv ∧
      incidentQubitIdx2 L xv yv ≠ incidentQubitIdx4 L xv yv ∧
      incidentQubitIdx3 L xv yv ≠ incidentQubitIdx4 L xv yv := by
    refine' ⟨_, _, _, _, _, _⟩
      <;> intro h
      <;> simp_all +decide
        [Fin.ext_iff, StabilizerGroup.ToricCodeN.hEdge, StabilizerGroup.ToricCodeN.vEdge]
    any_goals
      nlinarith
        [ Fin.is_lt xv,
          Fin.is_lt yv,
          Nat.sub_add_cancel (by linarith [Fact.out (p := 2 ≤ L)] : 1 ≤ L),
          Nat.zero_le ((xv + (L - 1)) % L),
          Nat.zero_le ((yv + (L - 1)) % L),
          Nat.mod_lt (xv + (L - 1)) (by linarith [Fact.out (p := 2 ≤ L)] : 0 < L),
          Nat.mod_lt (yv + (L - 1)) (by linarith [Fact.out (p := 2 ≤ L)] : 0 < L) ]
    · rw [ eq_comm, Nat.mod_eq_of_lt ] at h;
      · linarith [ Nat.sub_pos_of_lt ( Fact.out : 2 ≤ L ) ];
      · contrapose! h;
        rw [ Nat.mod_eq_sub_mod h ];
        rw [ Nat.mod_eq_of_lt ] <;> omega;
    · rcases L with ( _ | _ | L ) <;> simp_all +decide;
      rcases yv with ⟨ _ | yv, hyv ⟩ <;> simp_all +arith +decide;
      norm_num [ ( by ring : L + yv + 2 = L + 2 + yv ) ] at h;
      rw [ Nat.mod_eq_of_lt ] at h <;> linarith;
  split_ifs <;> simp_all +decide [ Finset.filter_eq', Finset.filter_or ];
  all_goals grind



/-
Step 1a scaffold: commutation with a fixed vertex check equals even overlap on its four
incident edges.
-/
theorem vertexCheckCommutes_iff_evenIncidentOverlap
    (L : ℕ) [Fact (2 ≤ L)] (c : C1 L) (xv yv : Fin L) :
    StabilizerGroup.ToricCodeN.vertexStab L xv yv * toricXOperatorOfChain L c =
      toricXOperatorOfChain L c * StabilizerGroup.ToricCodeN.vertexStab L xv yv
      ↔ Even
        (((if c (EdgeIdx.h xv yv) = 1 then 1 else 0) +
          (if c (EdgeIdx.h (StabilizerGroup.ToricCodeN.prev L xv) yv) = 1 then 1 else 0) +
          (if c (EdgeIdx.v xv yv) = 1 then 1 else 0) +
          (if c (EdgeIdx.v xv (StabilizerGroup.ToricCodeN.prev L yv)) = 1 then 1 else 0)) : ℕ) := by
  rw [ NQubitPauliGroupElement.commutes_iff_even_anticommutes ];
  convert Iff.rfl using 2;
  convert four_filter_card_eq_indicator_sum L c xv yv |> Eq.symm using 2;
  ext i; simp [anticommutesAt_vertexStab_toricX_iff_oneOfFour]

/-- Parity bridge over `ZMod 2`: even indicator count equals zero sum in `ZMod 2`. -/
lemma even_indicator_sum4_iff_zmod2_zero (a b c d : ZMod 2) :
    Even (((if a = 1 then 1 else 0) +
      (if b = 1 then 1 else 0) +
      (if c = 1 then 1 else 0) +
      (if d = 1 then 1 else 0)) : ℕ) ↔ a + b + c + d = 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide

/-- Step 1b scaffold: even overlap on incident edges is equivalent to vanishing `∂₁` at that
vertex. -/
theorem evenIncidentOverlap_iff_boundary1_zero_at
    (L : ℕ) [Fact (2 ≤ L)] (c : C1 L) (xv yv : Fin L) :
    Even
      (((if c (EdgeIdx.h xv yv) = 1 then 1 else 0) +
        (if c (EdgeIdx.h (StabilizerGroup.ToricCodeN.prev L xv) yv) = 1 then 1 else 0) +
        (if c (EdgeIdx.v xv yv) = 1 then 1 else 0) +
        (if c (EdgeIdx.v xv (StabilizerGroup.ToricCodeN.prev L yv)) = 1 then 1 else 0)) : ℕ)
      ↔ toricBoundary1 (L := L) c (xv, yv) = 0 := by
  simpa [toricBoundary1] using even_indicator_sum4_iff_zmod2_zero
    (c (EdgeIdx.h xv yv))
    (c (EdgeIdx.h (StabilizerGroup.ToricCodeN.prev L xv) yv))
    (c (EdgeIdx.v xv yv))
    (c (EdgeIdx.v xv (StabilizerGroup.ToricCodeN.prev L yv)))

/-- Step 1 bridge: for a fixed vertex check, commutation with the encoded X-chain operator
is equivalent to vanishing primal boundary at that vertex. -/
theorem vertexCheckCommutes_iff_boundary1_zero_at
    (L : ℕ) [Fact (2 ≤ L)] (c : C1 L) (xv yv : Fin L) :
    StabilizerGroup.ToricCodeN.vertexStab L xv yv * toricXOperatorOfChain L c =
      toricXOperatorOfChain L c * StabilizerGroup.ToricCodeN.vertexStab L xv yv
      ↔ toricBoundary1 (L := L) c (xv, yv) = 0 := by
  exact (vertexCheckCommutes_iff_evenIncidentOverlap L c xv yv).trans
    (evenIncidentOverlap_iff_boundary1_zero_at L c xv yv)

/-- Step 2 bridge: commutation with all vertex-Z generators is equivalent to pointwise
vanishing of the primal boundary map. -/
theorem xCommutesWithZChecks_iff_boundary1_pointwise_zero
    (L : ℕ) [Fact (2 ≤ L)] (c : C1 L) :
    xCommutesWithZChecks L c ↔ ∀ v : VtxIdx L, toricBoundary1 (L := L) c v = 0 := by
  constructor
  · intro h v
    rcases v with ⟨xv, yv⟩
    have hz :
        StabilizerGroup.ToricCodeN.vertexStab L xv yv ∈
          StabilizerGroup.ToricCodeN.ZGenerators L := by
      exact ⟨(xv, yv), rfl⟩
    have hcomm := h (StabilizerGroup.ToricCodeN.vertexStab L xv yv) hz
    exact (vertexCheckCommutes_iff_boundary1_zero_at L c xv yv).mp hcomm
  · intro h z hz
    rcases hz with ⟨⟨xv, yv⟩, rfl⟩
    exact (vertexCheckCommutes_iff_boundary1_zero_at L c xv yv).mpr (h (xv, yv))

/-- Step 3 bridge: pointwise vanishing of `∂₁` is equivalent to kernel membership,
i.e. cycle membership. -/
theorem boundary1_pointwise_zero_iff_mem_toricCycles
    (L : ℕ) [Fact (2 ≤ L)] (c : C1 L) :
    (∀ v : VtxIdx L, toricBoundary1 (L := L) c v = 0) ↔ c ∈ toricCycles (L := L) := by
  constructor
  · intro h
    change toricBoundary1 (L := L) c = 0
    ext v
    exact h v
  · intro h v
    exact congrArg (fun f => f v) h

/-- Commutation criterion: X-chain commutes with all Z checks iff it is a cycle. -/
theorem xCommutesWithZChecks_iff_mem_toricCycles (L : ℕ) [Fact (2 ≤ L)] (c : C1 L) :
    xCommutesWithZChecks L c ↔ c ∈ toricCycles (L := L) := by
  exact
    (xCommutesWithZChecks_iff_boundary1_pointwise_zero L c).trans
      (boundary1_pointwise_zero_iff_mem_toricCycles L c)

/-
`toricXOperatorOfChain` maps the zero chain to the identity Pauli element.
-/
lemma toricXOperatorOfChain_zero (L : ℕ) :
    toricXOperatorOfChain L 0 = 1 := by
  unfold toricXOperatorOfChain;
  aesop

/-
`toricXOperatorOfChain` maps chain addition to Pauli multiplication (ZMod 2 ↔ X²=I).
-/
set_option maxHeartbeats 1000000 in
-- This pointwise-to-global proof unfolds many dependent equalities and case splits.
lemma toricXOperatorOfChain_add (L : ℕ) (c c' : C1 L) :
    toricXOperatorOfChain L (c + c') =
      toricXOperatorOfChain L c * toricXOperatorOfChain L c' := by
  -- By definition of toricXOperatorOfChain, the operators are determined by input 1-entries.
  simp [toricXOperatorOfChain] at *;
  simp +decide [ NQubitPauliGroupElement.mul, NQubitPauliGroupElement.mulOp ];
  constructor;
  · rw [ Finset.sum_eq_zero ] ; aesop;
  · ext q;
    split_ifs <;> simp_all +decide [ Fin.ext_iff, ZMod ];
    · rename_i h₁ h₂ h₃;
      obtain ⟨ e₁, he₁, he₂ ⟩ := h₁
      obtain ⟨ e₂, he₃, he₄ ⟩ := h₂
      obtain ⟨ e₃, he₅, he₆ ⟩ := h₃
      have h_eq : e₁ = e₂ ∧ e₂ = e₃ := by
        have h_eq : ∀ e₁ e₂ : EdgeIdx L, edgeToQubitIdx L e₁ = edgeToQubitIdx L e₂ → e₁ = e₂ := by
          intros e₁ e₂ h_eq
          have h_eq' : edgeToQubitIdx L e₁ = edgeToQubitIdx L e₂ := h_eq
          simp [edgeToQubitIdx] at h_eq';
          rcases e₁ with ( _ | _ ) <;> rcases e₂ with ( _ | _ ) <;> norm_num at h_eq' ⊢;
          · rename_i a b c d;
            have h_eq' : b = d := by
              exact Fin.ext ( by nlinarith [ Fin.is_lt a, Fin.is_lt b, Fin.is_lt c, Fin.is_lt d ] );
            aesop;
          · rename_i a b c d
            exact absurd h_eq'
              (by nlinarith only [Fin.is_lt a, Fin.is_lt b, Fin.is_lt c, Fin.is_lt d])
          · rename_i a b c d
            exact absurd h_eq'
              (by nlinarith [Fin.is_lt a, Fin.is_lt b, Fin.is_lt c, Fin.is_lt d])
          · rename_i a b c d;
            have h_eq' : b = d := by
              exact Fin.ext ( by nlinarith [ Fin.is_lt a, Fin.is_lt b, Fin.is_lt c, Fin.is_lt d ] );
            aesop;
        exact ⟨ h_eq e₁ e₂ ( Fin.ext <| by aesop ), h_eq e₂ e₃ ( Fin.ext <| by aesop ) ⟩;
      grind;
    · grind;
    · grind;
    · grind

/-
`toricXOperatorOfChain` maps the boundary of a single face to the corresponding face stabilizer.
-/
lemma toricXOperatorOfChain_boundary_singleFace (L : ℕ) [Fact (2 ≤ L)] (x y : Fin L) :
    toricXOperatorOfChain L (toricBoundary2 (L := L) (singleFace (x, y))) =
      StabilizerGroup.ToricCodeN.faceStab L x y := by
  unfold toricXOperatorOfChain StabilizerGroup.ToricCodeN.faceStab;
  congr with q;
  split_ifs <;> simp_all +decide [ NQubitPauliOperator.set ];
  · rename_i h
    obtain ⟨e, rfl, he⟩ := h
    rcases e with (_ | _) <;> simp_all +decide [toricBoundary2, singleFace]
    · unfold edgeToQubitIdx; split_ifs at he <;> simp_all +decide [ Fin.ext_iff ] ;
    · split_ifs at he <;> simp_all +decide [ Fin.ext_iff, StabilizerGroup.ToricCodeN.next ];
  · split_ifs <;> simp_all +decide [ toricNumQubits ];
    · rename_i h₁ h₂;
      contrapose! h₁;
      use EdgeIdx.v (StabilizerGroup.ToricCodeN.next L x) y;
      unfold edgeToQubitIdx; simp +decide [ StabilizerGroup.ToricCodeN.next ] ;
      constructor;
      · exact rfl
      · exact next_ne_self L x
    · rename_i h₁ h₂ h₃;
      contrapose! h₁;
      use EdgeIdx.v x y;
      unfold edgeToQubitIdx; simp +decide [ StabilizerGroup.ToricCodeN.vEdge ] ;
      grind;
    · rename_i h₁ h₂ h₃ h₄;
      contrapose! h₁;
      use EdgeIdx.h x (StabilizerGroup.ToricCodeN.next L y); simp +decide [ edgeToQubitIdx ] ;
      unfold StabilizerGroup.ToricCodeN.next; simp +decide [ Fin.ext_iff ] ;
      by_cases hy : y.val = L - 1;
      · rcases L with ( _ | _ | L ) <;> simp_all +decide;
        exact absurd ( Fact.out ( p := 2 ≤ 0 + 1 ) ) ( by decide );
      · rw [ Nat.mod_eq_of_lt ] <;> omega;
    · rename_i h₁ h₂ h₃ h₄ h₅;
      contrapose! h₁;
      use EdgeIdx.h x y;
      unfold toricBoundary2; simp +decide [ singleFace ] ;
      exact
        Decidable.not_imp_iff_and_not.mp fun a ↦
          h₄ (congrArg (StabilizerGroup.ToricCodeN.hEdge L x) (a rfl));
    · unfold NQubitPauliOperator.identity; aesop;

/-
Every 2-chain is a sum of single-face indicators.
-/
lemma c2_eq_sum_singleFace (L : ℕ) (f : C2 L) :
    f = ∑ p ∈ Finset.univ.filter (fun p : FaceIdx L => f p = 1), singleFace p := by
  ext p;
  unfold singleFace;
  cases Fin.exists_fin_two.mp ⟨ f p, rfl ⟩ <;> simp +decide [ * ]

/-
Stabilizer criterion: X-chain is plaquette product iff it is a boundary.
-/
theorem xIsPlaquetteProduct_iff_mem_toricBoundaries (L : ℕ) [Fact (2 ≤ L)] (c : C1 L) :
    xIsPlaquetteProduct L c ↔ c ∈ toricBoundaries (L := L) := by
  constructor <;> intro hc <;> simp_all +decide [ xIsPlaquetteProduct, toricBoundaries ];
  · have h_closure :
        ∀ g ∈ Subgroup.closure (StabilizerGroup.ToricCodeN.XGenerators L),
          ∃ f : C2 L, toricXOperatorOfChain L (toricBoundary2 (L := L) f) = g := by
      intro g hg
      induction' hg using Subgroup.closure_induction with g hg ih;
      · rcases hg with ⟨⟨x, y⟩, rfl⟩
        exact ⟨singleFace (x, y), toricXOperatorOfChain_boundary_singleFace L x y⟩
      · use 0; simp [toricXOperatorOfChain_zero];
      · rename_i h₁ h₂ h₃ h₄
        obtain ⟨f₁, hf₁⟩ := h₃
        obtain ⟨f₂, hf₂⟩ := h₄
        use f₁ + f₂
        simp +decide [hf₁, hf₂, toricXOperatorOfChain_add]
      · obtain ⟨f, hf⟩ := ‹_›
        use f
        simp_all +decide [toricXOperatorOfChain]
        rw [← hf]
        ext <;> simp +decide [NQubitPauliGroupElement.inv]
    have := @chainOfXOperator_toricXOperatorOfChain L;
    grind +splitImp;
  · obtain ⟨ f, rfl ⟩ := hc;
    rw [ c2_eq_sum_singleFace L f ];
    induction' (Finset.univ.filter fun p : FaceIdx L => f p = 1) using Finset.induction <;>
      simp_all +decide [Finset.sum_insert]
    · rw [ toricXOperatorOfChain_zero ] ; exact OneMemClass.one_mem _;
    · rw [ toricXOperatorOfChain_add ];
      exact Subgroup.mul_mem _
        (by
          rw [toricXOperatorOfChain_boundary_singleFace]
          exact Subgroup.subset_closure <| Set.mem_range_self _)
        ‹_›

/-
X-type operators commute with the toric X-type chain encoding.
-/
lemma toricXOperatorOfChain_commutes_faceStab
    (L : ℕ) [Fact (2 ≤ L)] (c : C1 L) (xf yf : Fin L) :
    StabilizerGroup.ToricCodeN.faceStab L xf yf * toricXOperatorOfChain L c =
      toricXOperatorOfChain L c * StabilizerGroup.ToricCodeN.faceStab L xf yf := by
  -- Both `faceStab` and `toricXOperatorOfChain` are X-type, so they commute.
  have h_comm :
      ∀ (g h : NQubitPauliGroupElement (StabilizerGroup.ToricCodeN.numQubits L)),
        NQubitPauliGroupElement.IsXTypeElement g →
        NQubitPauliGroupElement.IsXTypeElement h →
        g * h = h * g := by
    exact fun g h a a_1 ↦ StabilizerGroup.CSSCommutationLemmas.XType_commutes a a_1;
  apply h_comm;
  · exact StabilizerGroup.ToricCodeN.faceStab_is_XType L xf yf;
  · -- By definition of toricXOperatorOfChain, it is an X-type operator.
    simp [NQubitPauliGroupElement.IsXTypeElement, toricXOperatorOfChain];
    intro q
    by_cases h : ∃ e : EdgeIdx L, edgeToQubitIdx L e = q ∧ c e = 1 <;> simp +decide [h]
    · exact PauliOperator.IsXType_X;
    · exact PauliOperator.IsXType_I

/-
Centralizer membership for X-chain operator is equivalent to cycle membership.
-/
lemma toricXOperatorOfChain_mem_centralizer_iff_cycle
    (L : ℕ) [Fact (2 ≤ L)] (c : C1 L) :
    toricXOperatorOfChain L c ∈
    StabilizerGroup.centralizer (StabilizerGroup.ToricCodeN.stabilizerGroup L) ↔
        c ∈ toricCycles (L := L) := by
  constructor;
  · intro h;
    apply (xCommutesWithZChecks_iff_mem_toricCycles L c).mp;
    intro z hz;
    apply h;
    exact Subgroup.subset_closure
      (by
        rw [StabilizerGroup.ToricCodeN.listToSet_generatorsList]
        exact Set.mem_union_left _ hz)
  · intro hc;
    -- Since $c \in \text{toricCycles } L$, we have that $xCommutesWithZChecks L c$ holds.
    have h_comm : xCommutesWithZChecks L c := by
      exact?;
    intro g hg;
    -- Since `g ∈ stabilizerGroup L`, we have `g` in the closure of generators.
    have h_closure :
        g ∈ Subgroup.closure (StabilizerGroup.ToricCodeN.generators L) := by
      exact hg |>
        fun h => by
          rw [StabilizerGroup.ToricCodeN.stabilizerGroup_toSubgroup_eq] at h
          exact h
    refine' Subgroup.closure_induction ( fun x hx => _ ) _ _ _ h_closure;
    · cases hx with
      | inl hx => exact h_comm x hx
      | inr hx =>
          obtain ⟨ p, rfl ⟩ := hx
          exact toricXOperatorOfChain_commutes_faceStab L c p.1 p.2
    · norm_num;
    · grind;
    · simp_all +decide [ NQubitPauliGroupElement.mul, NQubitPauliGroupElement.inv ];
      grind

/-
Any X-type element of the full toric stabilizer group lies in
    `Subgroup.closure (XGenerators L)`.
-/
set_option maxHeartbeats 1000000 in
-- The closure decomposition over mixed Z/X generators needs extra heartbeats.
lemma xType_in_stabilizerGroup_implies_in_XClosure
    (L : ℕ) [Fact (2 ≤ L)] (g : NQubitPauliGroupElement
      (StabilizerGroup.ToricCodeN.numQubits L))
    (hg : g ∈ (StabilizerGroup.ToricCodeN.stabilizerGroup L).toSubgroup)
    (hxt : NQubitPauliGroupElement.IsXTypeElement g) :
    g ∈ Subgroup.closure (StabilizerGroup.ToricCodeN.XGenerators L) := by
  -- By `stabilizerGroup_toSubgroup_eq`, `g` lies in closure of `ZGenerators ∪ XGenerators`.
  have hg_closure :
      g ∈ Subgroup.closure
        ((StabilizerGroup.ToricCodeN.ZGenerators L) ∪
          (StabilizerGroup.ToricCodeN.XGenerators L)) := by
    -- By definition of the stabilizer group, we know that g is in the closure of the generators.
    have h_closure : g ∈ (StabilizerGroup.ToricCodeN.stabilizerGroup L).toSubgroup := by
      exact hg;
    rw [ StabilizerGroup.ToricCodeN.stabilizerGroup_toSubgroup_eq ] at h_closure;
    exact h_closure;
  -- Decompose `g = z * x` with `z` in Z-closure and `x` in X-closure.
  obtain ⟨z, hz, x, hx, rfl⟩ :
      ∃ z ∈ Subgroup.closure (StabilizerGroup.ToricCodeN.ZGenerators L),
      ∃ x ∈ Subgroup.closure (StabilizerGroup.ToricCodeN.XGenerators L),
        g = z * x := by
    apply Subgroup.mem_closure_union_exists_mul_of_commute_generators;
    · exact fun s a t a_1 ↦
        StabilizerGroup.ToricCodeN.ZGenerators_commute_XGenerators L s a t a_1
    · exact hg_closure;
  have hz_id : z.IsXTypeElement := by
    have hz_id : x.IsXTypeElement := by
      exact NQubitPauliGroupElement.IsXTypeElement_of_mem_closure
        (StabilizerGroup.ToricCodeN.XGenerators_are_XType L) x hx
    have hz_id : z = (z * x) * x⁻¹ := by
      exact eq_mul_inv_of_mul_eq rfl;
    exact hz_id.symm ▸ NQubitPauliGroupElement.IsXTypeElement_mul hxt
      (by
        expose_names
        exact NQubitPauliGroupElement.IsXTypeElement_inv hz_id_1)
  have hz_id : z.IsZTypeElement := by
    exact NQubitPauliGroupElement.IsZTypeElement_of_mem_closure
      (StabilizerGroup.ToricCodeN.ZGenerators_are_ZType L) z hz
  have hz_id : z = 1 := by
    expose_names
    exact NQubitPauliGroupElement.eq_one_of_IsZTypeElement_and_IsXTypeElement
      hz_id hz_id_1
  rw [hz_id]; norm_num; assumption

/-- Any element of the stabilizer with X/I-only operators is X-type (phasePower = 0). -/
lemma xTypeOps_in_stabilizer_has_phase_zero
    (L : ℕ) [Fact (2 ≤ L)]
    (s : NQubitPauliGroupElement (StabilizerGroup.ToricCodeN.numQubits L))
    (hs : s ∈ (StabilizerGroup.ToricCodeN.stabilizerGroup L).toSubgroup)
    (hops : ∀ i, s.operators i = PauliOperator.X ∨ s.operators i = PauliOperator.I) :
    NQubitPauliGroupElement.IsXTypeElement s := by
  -- s ∈ closure(ZGenerators ∪ XGenerators)
  have hs_cl : s ∈ Subgroup.closure
      (StabilizerGroup.ToricCodeN.ZGenerators L ∪
       StabilizerGroup.ToricCodeN.XGenerators L) := by
    rw [StabilizerGroup.ToricCodeN.stabilizerGroup_toSubgroup_eq] at hs
    exact hs
  -- CSS decompose: s = z * x
  obtain ⟨z, hz, x, hx, hzx⟩ :=
    Subgroup.mem_closure_union_exists_mul_of_commute_generators
      (StabilizerGroup.ToricCodeN.ZGenerators_commute_XGenerators L) s hs_cl
  have hz_ty : NQubitPauliGroupElement.IsZTypeElement z :=
    NQubitPauliGroupElement.IsZTypeElement_of_mem_closure
      (StabilizerGroup.ToricCodeN.ZGenerators_are_ZType L) z hz
  have hx_ty : NQubitPauliGroupElement.IsXTypeElement x :=
    NQubitPauliGroupElement.IsXTypeElement_of_mem_closure
      (StabilizerGroup.ToricCodeN.XGenerators_are_XType L) x hx
  -- z has identity operators (proven from operator constraints)
  have hz_id : z = 1 := by
    have hz_ops_I : ∀ i, z.operators i = PauliOperator.I := by
      intro i
      have hsi := hops i
      rw [hzx] at hsi
      rcases hz_ty.2 i with hz_I | hz_Z <;> rcases hx_ty.2 i with hx_I | hx_X
      · exact hz_I
      · exact hz_I
      · -- z[i] = Z, x[i] = I, so (z*x)[i] = Z, contradicts s[i] ∈ {X, I}
        exfalso
        simp [NQubitPauliGroupElement.mul, NQubitPauliGroupElement.mulOp] at hsi
        rw [hz_Z, hx_I] at hsi
        cases hsi with
        | inl h => simp [PauliOperator.mulOp] at h
        | inr h => simp [PauliOperator.mulOp] at h
      · -- z[i] = Z, x[i] = X, so (z*x)[i] = Y, contradicts s[i] ∈ {X, I}
        exfalso
        simp [NQubitPauliGroupElement.mul, NQubitPauliGroupElement.mulOp] at hsi
        rw [hz_Z, hx_X] at hsi
        cases hsi with
        | inl h => simp [PauliOperator.mulOp] at h
        | inr h => simp [PauliOperator.mulOp] at h
    exact NQubitPauliGroupElement.ext z 1 hz_ty.1 (by ext i; exact hz_ops_I i)
  -- Therefore s = x which is X-type
  rw [hzx, hz_id, one_mul]
  exact hx_ty

/-- If `s` is in the toric stabilizer and has the same operators as an X-chain encoding,
    then the corresponding chain is a boundary. -/
lemma stabilizer_same_ops_implies_boundary
    (L : ℕ) [Fact (2 ≤ L)] (c : C1 L)
    (s : NQubitPauliGroupElement (StabilizerGroup.ToricCodeN.numQubits L))
    (hs : s ∈ (StabilizerGroup.ToricCodeN.stabilizerGroup L).toSubgroup)
    (heq : s.operators = (toricXOperatorOfChain L c).operators) :
    c ∈ toricBoundaries (L := L) := by
  have hops : ∀ i, s.operators i = PauliOperator.X ∨ s.operators i = PauliOperator.I := by
    intro i; rw [heq]; simp only [toricXOperatorOfChain]
    by_cases h : ∃ e : EdgeIdx L, edgeToQubitIdx L e = i ∧ c e = 1
    · simp [h]
    · simp [h]
  have hxt : NQubitPauliGroupElement.IsXTypeElement s :=
    xTypeOps_in_stabilizer_has_phase_zero L s hs hops
  have hxcl : s ∈ Subgroup.closure (StabilizerGroup.ToricCodeN.XGenerators L) :=
    xType_in_stabilizerGroup_implies_in_XClosure L s hs hxt
  have h_eq : s = toricXOperatorOfChain L c :=
    NQubitPauliGroupElement.ext s (toricXOperatorOfChain L c)
      hxt.1 (by ext i; exact congrFun heq i)
  rw [h_eq] at hxcl
  exact (xIsPlaquetteProduct_iff_mem_toricBoundaries L c).mp hxcl

/-
X nontrivial logical iff corresponding chain is cycle-not-boundary.
-/
set_option maxHeartbeats 1000000 in
-- This theorem combines closure induction with nontrivial-coset conditions.
theorem xNontrivialLogical_iff_cycle_not_boundary (L : ℕ) [Fact (2 ≤ L)] (c : C1 L) :
    StabilizerGroup.IsNontrivialLogicalOperator
        (toricXOperatorOfChain L c) (StabilizerGroup.ToricCodeN.stabilizerGroup L) ↔
      c ∈ toricCycles (L := L) ∧ c ∉ toricBoundaries (L := L) := by
  constructor <;> intro h;
  · constructor;
    · exact toricXOperatorOfChain_mem_centralizer_iff_cycle L c |>.1 h.1;
    · intro hc
      have h_plaquette :
          toricXOperatorOfChain L c ∈
            Subgroup.closure (StabilizerGroup.ToricCodeN.XGenerators L) := by
        exact xIsPlaquetteProduct_iff_mem_toricBoundaries L c |>.2 hc
      have h_in_stabilizer :
          toricXOperatorOfChain L c ∈
            (StabilizerGroup.ToricCodeN.stabilizerGroup L).toSubgroup := by
        refine' Subgroup.closure_induction ( fun x hx => _ ) _ _ _ h_plaquette;
        · exact Subgroup.subset_closure
            (by
              rw [StabilizerGroup.ToricCodeN.listToSet_generatorsList]
              exact Set.mem_union_right _ hx)
        · exact OneMemClass.one_mem _;
        · exact fun x y hx hy hx' hy' => Subgroup.mul_mem _ hx' hy';
        · exact fun x hx₁ hx₂ => Subgroup.inv_mem _ hx₂
      exact h.2.1 h_in_stabilizer;
  · constructor;
    · exact toricXOperatorOfChain_mem_centralizer_iff_cycle L c |>.2 h.1;
    · have h_1 := h.1
      have h_2 := h.2
      constructor;
      · intro hg
        exact h_2 (stabilizer_same_ops_implies_boundary L c
          (toricXOperatorOfChain L c) hg rfl)
      · intro s hs hEq
        exact h_2 (stabilizer_same_ops_implies_boundary L c s hs hEq)


end Lattice
end Stabilizer
end Quantum
