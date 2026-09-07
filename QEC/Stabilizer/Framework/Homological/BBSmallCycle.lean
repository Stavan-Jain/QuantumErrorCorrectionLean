/-
# The parametric small-cycle bundle for BB base floors (T2 layer)

`SmallCycleData G` packages a BB code over `G` (polynomials `A`, `B`)
together with the four finite obligations from which the strong `d ≥ 6`
floor follows *generically*:

* `epsA`, `epsB` — the augmentations are 1 (odd polynomial weights);
* `check_two`, `check_four` — no *normalized* weight-2 / weight-4 cycle
  (origin qubit plus one / three further qubits has nonzero syndrome).

From the bundle, `cycle_weight_ge_6` derives the strong small-cycle floor
— every nonzero 1-cycle has weight ≥ 6 — by the argument of
`Codes/BivariateBicycle/BaseDistance.lean` (the gross base), parametrized:
translation-normalize a support point to the group origin
(`bbBoundary1Fn_translate1`), kill odd weights with the parity lemma
(augmentation of the cycle condition), and hand the two even supports to
the finite checks through the sparse-syndrome bridge.  Downstream
corollaries are packaged once: the chain floor on nontrivial cycles, the
dual floor (`bb_cycle_bound_iff_dual_bound`), the Pauli-level logical
floor (`chainWeight_lower_bound_transfers`), the stabilizer-weight floor,
and the doubling-template bridge
(`XDoubleCoverData.strongBaseFloor_of_smallCycle`).

## Two discharge grades (A15 §T2 design)

The obligations are plain `Prop`s, so an instance can discharge them
either by `native_decide` (engineering grade — what the generated
`BaseFloors/` instances did before they were parked on branch
`claude/z3z6-parked`; provenance
`qec-lab:experiments/bb_lab/scripts/gen_base_floor_lean.py`) or, eventually, by
the analytic class small-cycle theorem (A16 write-up of record), whose
hypotheses (D1 ∧ D2 ∧ (iii) ∧ (a), floor-bearing frame) imply exactly
these statements.  Both routes fit the same fields, so upgrading a member
from engineering to analytic grade is invisible downstream.

## Convention bridge (lab notes → repo)

Repo convention (`BBChainComplex.lean`): `∂₂ f = (A⋆f | B⋆f)`,
`∂₁ c = B⋆c_L + A⋆c_R`; cycle condition `B⋆v_L = A⋆v_R`.
**Repo-left = lab-right.**  The syndrome of a left-block qubit at `g` is
`h ↦ B(h−g)`, of a right-block qubit `h ↦ A(h−g)`.
-/

import QEC.Stabilizer.Framework.Homological.BBDoubling

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open scoped BigOperators

/-! ## Sparse-syndrome helpers

For an indicator chain `χ_S`, the boundary `∂₁(χ_S)(h)` is the `|S|`-term
sum `syndAt A B S h` — far cheaper to evaluate than the convolution form
during a `native_decide` sweep.  The `SmallCycle` namespace keeps these
generic helpers clear of the instance-specific machinery of
`Codes/BivariateBicycle/BaseDistance.lean` (which predates this layer). -/

namespace SmallCycle

/-- A `ZMod 2` chain is the indicator function of its support. -/
lemma eq_indicator_support {I : Type} [Fintype I] [DecidableEq I]
    (u : I → ZMod 2) :
    u = fun p => if p ∈ (Finset.univ.filter fun q => u q ≠ 0) then 1 else 0 := by
  have hdichot : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  funext p
  by_cases h : u p = 0
  · simp [h]
  · simp [hdichot _ h]

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

variable {G : Type} [Fintype G] [AddCommGroup G]

/-- Translation preserves support size (1-chains). -/
lemma card_support_translate1 (c : G) (u : G × Fin 2 → ZMod 2) :
    (Finset.univ.filter fun p => translate1 c u p ≠ 0).card
      = (Finset.univ.filter fun p => u p ≠ 0).card :=
  card_filter_comp_equiv ((Equiv.addRight c).prodCongr (Equiv.refl (Fin 2)))
    (fun p => u p ≠ 0)

/-- The augmentation is multiplicative on convolutions. -/
lemma sum_conv (a b : G → ZMod 2) :
    ∑ g : G, (a ⋆ b) g = (∑ h : G, a h) * (∑ g : G, b g) := by
  simp only [conv_apply]
  rw [Finset.sum_comm]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  exact Equiv.sum_comp (Equiv.subRight h) b

variable [DecidableEq G] (A B : G → ZMod 2)

/-- The syndrome contribution of a single qubit at a check position. -/
def termAt (q : G × Fin 2) (h : G) : ZMod 2 :=
  if q.2 = 0 then B (h - q.1) else A (h - q.1)

/-- Sparse syndrome of a support set at a check position. -/
def syndAt (S : Finset (G × Fin 2)) (h : G) : ZMod 2 :=
  ∑ q ∈ S, termAt A B q h

/-- `∂₁` of a point mass, in either block. -/
lemma bbBoundary1Fn_single_point (q : G × Fin 2) (h : G) :
    bbBoundary1Fn A B (Pi.single q 1) h = termAt A B q h := by
  obtain ⟨g, j⟩ := q
  by_cases hj : j = 0
  · subst hj
    exact bbBoundary1Fn_single_left A B g h
  · have hj1 : j = 1 := by omega
    subst hj1
    exact bbBoundary1Fn_single_right A B g h

/-- **The sparse-syndrome bridge**: on indicator chains, `∂₁` evaluates to
`syndAt`. -/
lemma bbBoundary1Fn_indicator (S : Finset (G × Fin 2)) :
    ∀ h : G,
      bbBoundary1Fn A B (fun q => if q ∈ S then 1 else 0) h
        = syndAt A B S h := by
  classical
  induction S using Finset.induction with
  | empty =>
      intro h
      have hzero : (fun q : G × Fin 2 =>
          if q ∈ (∅ : Finset (G × Fin 2)) then (1 : ZMod 2) else 0)
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

end SmallCycle

/-! ## The bundle -/

/-- The data of a BB code over `G` together with the four finite
obligations of the small-cycle floor: odd polynomial augmentations and the
normalized weight-2 / weight-4 kills.  The checks are stated over *tuples*
(colliding tuples cancel in char 2 down to the weight-2 shape, so the
statements stay true and the `Decidable` instances synthesize
structurally). -/
structure SmallCycleData (G : Type)
    [Fintype G] [AddCommGroup G] [DecidableEq G] where
  /-- The polynomial `A`. -/
  A : G → ZMod 2
  /-- The polynomial `B`. -/
  B : G → ZMod 2
  /-- `ε(A) = 1`: the support of `A` has odd size. -/
  epsA : ∑ h : G, A h = 1
  /-- `ε(B) = 1`: the support of `B` has odd size. -/
  epsB : ∑ h : G, B h = 1
  /-- No normalized weight-2 cycle: the origin qubit of either block plus
  any other qubit has nonzero syndrome. -/
  check_two : ∀ b : Fin 2, ∀ q : G × Fin 2, q ≠ ((0 : G), b) →
    ∃ h : G, SmallCycle.termAt A B ((0 : G), b) h
      + SmallCycle.termAt A B q h ≠ 0
  /-- No normalized weight-4 cycle: the origin qubit of either block plus
  any three qubits has nonzero syndrome (disjunctive form: the
  `qᵢ ≠ origin` hypotheses are folded into the conclusion). -/
  check_four : ∀ b : Fin 2, ∀ q₁ q₂ q₃ : G × Fin 2,
    q₁ = ((0 : G), b) ∨ q₂ = ((0 : G), b) ∨ q₃ = ((0 : G), b) ∨
    ∃ h : G, SmallCycle.termAt A B ((0 : G), b) h
      + SmallCycle.termAt A B q₁ h + SmallCycle.termAt A B q₂ h
      + SmallCycle.termAt A B q₃ h ≠ 0

namespace SmallCycleData

variable {G : Type} [Fintype G] [AddCommGroup G] [DecidableEq G]
  (D : SmallCycleData G)

/-! ## The parity lemma (PAR)

Every cycle has even weight: applying the augmentation `ε(w) = Σ_g w(g)`
to `B⋆u_L + A⋆u_R = 0` gives `ε(u_L) + ε(u_R) = 0` since
`ε(A) = ε(B) = 1`.  This kills all odd-weight supports analytically, so
the finite checks only cover the (normalized) weight-2 and weight-4
configurations. -/

/-- **(PAR)**: cycles have zero total parity. -/
lemma cycle_total_parity (u : G × Fin 2 → ZMod 2)
    (hcyc : bbBoundary1Fn D.A D.B u = 0) :
    ∑ p : G × Fin 2, u p = 0 := by
  have h0 : ∑ g : G, bbBoundary1Fn D.A D.B u g = 0 := by
    rw [hcyc]
    simp
  have hexp : ∑ g : G, bbBoundary1Fn D.A D.B u g
      = (∑ h : G, D.B h) * (∑ g : G, leftHalf u g)
        + (∑ h : G, D.A h) * (∑ g : G, rightHalf u g) := by
    rw [show (fun g => bbBoundary1Fn D.A D.B u g)
        = fun g => (D.B ⋆ leftHalf u) g + (D.A ⋆ rightHalf u) g
      from rfl]
    rw [Finset.sum_add_distrib, SmallCycle.sum_conv, SmallCycle.sum_conv]
  rw [hexp, D.epsA, D.epsB, one_mul, one_mul] at h0
  rw [Fintype.sum_prod_type]
  calc ∑ g : G, ∑ j : Fin 2, u (g, j)
      = ∑ g : G, (u (g, 0) + u (g, 1)) := by
        refine Finset.sum_congr rfl fun g _ => ?_
        exact Fin.sum_univ_two _
    _ = (∑ g : G, leftHalf u g) + (∑ g : G, rightHalf u g) :=
        Finset.sum_add_distrib
    _ = 0 := h0

/-- Cycles have even weight. -/
lemma cycle_weight_even (u : G × Fin 2 → ZMod 2)
    (hcyc : bbBoundary1Fn D.A D.B u = 0) :
    (Finset.univ.filter fun p => u p ≠ 0).card % 2 = 0 := by
  have hdichot : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  have hcast : (((Finset.univ.filter fun p => u p ≠ 0).card : ℕ) : ZMod 2)
      = ∑ p : G × Fin 2, u p := by
    rw [← Finset.sum_filter_ne_zero Finset.univ]
    rw [Finset.sum_congr rfl fun p hp => hdichot (u p)
      (Finset.mem_filter.mp hp).2]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have h0 := D.cycle_total_parity u hcyc
  rw [← hcast] at h0
  have heven := ZMod.natCast_eq_zero_iff_even.mp h0
  exact Nat.even_iff.mp heven

/-! ## The small-cycle theorem (strong form) -/

/-- **Small-cycle floor** (strong form): every nonzero 1-cycle of the BB
complex has weight ≥ 6 — boundaries included. -/
theorem cycle_weight_ge_6
    (u : G × Fin 2 → ZMod 2)
    (hcyc : bbBoundary1Fn D.A D.B u = 0) (hne : u ≠ 0) :
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
  have hp' : translate1 p.1 u ((0 : G), p.2) ≠ 0 := by
    change u ((0 : G) + p.1, p.2) ≠ 0
    rw [zero_add]
    exact hp
  have hcyc' : bbBoundary1Fn D.A D.B (translate1 p.1 u) = 0 := by
    rw [bbBoundary1Fn_translate1, hcyc]
    rfl
  have hcard' :
      (Finset.univ.filter fun q => translate1 p.1 u q ≠ 0).card ≤ 5 := by
    rw [SmallCycle.card_support_translate1]
    omega
  -- decompose the normalized support
  have hxS : (((0 : G)), p.2)
      ∈ Finset.univ.filter fun q => translate1 p.1 u q ≠ 0 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp'⟩
  have hxs : (((0 : G)), p.2)
      ∉ (Finset.univ.filter fun q => translate1 p.1 u q ≠ 0).erase
          ((0 : G), p.2) :=
    Finset.notMem_erase _ _
  have hins : insert (((0 : G)), p.2)
      ((Finset.univ.filter fun q => translate1 p.1 u q ≠ 0).erase
        ((0 : G), p.2))
      = Finset.univ.filter fun q => translate1 p.1 u q ≠ 0 :=
    Finset.insert_erase hxS
  -- (PAR): the normalized support has even size, and it is nonempty
  have hpar := D.cycle_weight_even (translate1 p.1 u) hcyc'
  have hpos : 0 < (Finset.univ.filter fun q => translate1 p.1 u q ≠ 0).card :=
    Finset.card_pos.mpr ⟨_, hxS⟩
  have hscard :
      ((Finset.univ.filter fun q => translate1 p.1 u q ≠ 0).erase
        ((0 : G), p.2)).card = 1
      ∨ ((Finset.univ.filter fun q => translate1 p.1 u q ≠ 0).erase
        ((0 : G), p.2)).card = 3 := by
    rw [Finset.card_erase_of_mem hxS]
    omega
  -- the normalized chain is the indicator of `insert x s`
  have hind : translate1 p.1 u
      = fun q => if q ∈ insert (((0 : G)), p.2)
          ((Finset.univ.filter fun q => translate1 p.1 u q ≠ 0).erase
            ((0 : G), p.2)) then 1 else 0 := by
    rw [hins]
    exact SmallCycle.eq_indicator_support (translate1 p.1 u)
  -- contradict the finite check
  have hcheck : ∃ h : G,
      SmallCycle.syndAt D.A D.B (insert (((0 : G)), p.2)
        ((Finset.univ.filter fun q => translate1 p.1 u q ≠ 0).erase
          ((0 : G), p.2))) h ≠ 0 := by
    rcases hscard with hk | hk
    · obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hk
      rw [hq] at hxs
      rw [Finset.mem_singleton] at hxs
      obtain ⟨h, hh⟩ := D.check_two p.2 q (Ne.symm hxs)
      refine ⟨h, ?_⟩
      rw [hq, SmallCycle.syndAt,
        Finset.sum_insert (by rw [Finset.mem_singleton]; exact hxs),
        Finset.sum_singleton]
      exact hh
    · obtain ⟨q₁, q₂, q₃, h12, h13, h23, hs3⟩ := Finset.card_eq_three.mp hk
      rw [hs3, Finset.mem_insert, Finset.mem_insert,
        Finset.mem_singleton] at hxs
      push Not at hxs
      obtain ⟨hx1, hx2, hx3⟩ := hxs
      have hfour := D.check_four p.2 q₁ q₂ q₃
      rcases hfour with hc | hc | hc | ⟨h, hh⟩
      · exact absurd hc.symm hx1
      · exact absurd hc.symm hx2
      · exact absurd hc.symm hx3
      refine ⟨h, ?_⟩
      rw [hs3, SmallCycle.syndAt,
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
  rw [← SmallCycle.bbBoundary1Fn_indicator, ← hind]
  exact congrFun hcyc' h

/-! ## Packaged corollaries -/

/-- The BB chain complex of the bundle. -/
noncomputable def complex : HomologicalCode := bbChainComplex D.A D.B

/-- `chainWeight` on the bundle's complex, in raw `Finset` form. -/
lemma complex_chainWeight_eq (u : G × Fin 2 → ZMod 2) :
    D.complex.chainWeight u
      = (Finset.univ.filter fun p : G × Fin 2 => u p ≠ 0).card := rfl

/-- Chain-level d ≥ 6 on nontrivial cycles. -/
theorem chain_floor :
    ∀ u ∈ D.complex.cycles, u ∉ D.complex.boundaries →
      6 ≤ D.complex.chainWeight u := by
  intro u hu hnb
  have hne : u ≠ 0 := by
    rintro rfl
    exact hnb ⟨0, map_zero _⟩
  have hcyc : bbBoundary1Fn D.A D.B u = 0 := hu
  rw [D.complex_chainWeight_eq]
  exact D.cycle_weight_ge_6 u hcyc hne

/-- Dual-side chain floor, via the Φ duality (`d_X = d_Z` for BB codes). -/
theorem dual_chain_floor :
    ∀ c ∈ D.complex.dualCycles, c ∉ D.complex.dualBoundaries →
      6 ≤ D.complex.chainWeight c := by
  have hX : ∀ c ∈ (bbChainComplex D.A D.B).cycles,
      c ∉ (bbChainComplex D.A D.B).boundaries →
      6 ≤ (bbChainComplex D.A D.B).chainWeight c := fun c hc hnb =>
    D.chain_floor c hc hnb
  exact (bb_cycle_bound_iff_dual_bound D.A D.B 6).mp hX

/-- **Pauli-level logical floor**: every nontrivial logical operator of
the bundle's homological stabilizer group has weight ≥ 6. -/
theorem logical_weight_ge_6
    (g : NQubitPauliGroupElement D.complex.numQubits)
    (hg : Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
      D.complex.homologicalStabilizerGroup) :
    6 ≤ NQubitPauliGroupElement.weight g :=
  HomologicalCode.chainWeight_lower_bound_transfers D.complex 6
    (fun c hc hnb => D.chain_floor c hc hnb)
    (fun c hc hnb => D.dual_chain_floor c hc hnb) g hg

/-- Nonzero stabilizer chains (images of `∂₂`) also weigh ≥ 6 — the
`μ ≥ 6` half of the class theorem's conclusion. -/
theorem stab_weight_ge_6 (f : G → ZMod 2)
    (hne : bbBoundary2Fn D.A D.B f ≠ 0) :
    6 ≤ (Finset.univ.filter
      fun p => bbBoundary2Fn D.A D.B f p ≠ 0).card :=
  D.cycle_weight_ge_6 _ (bbBoundaryFn_comp D.A D.B f) hne

end SmallCycleData

/-! ## Bridge into the doubling template -/

/-- A small-cycle bundle on the base of a free ℤ₂ cover discharges the
doubling template's `StrongBaseFloor 6` hypothesis (Theorem-B transfer and
the rung theorems of `BBDoubling.lean` then apply). -/
theorem XDoubleCoverData.strongBaseFloor_of_smallCycle
    {G H : Type} [Fintype G] [AddCommGroup G] [DecidableEq G]
    [Fintype H] [AddCommGroup H] [DecidableEq H]
    (C : XDoubleCoverData G H) (D : SmallCycleData H)
    (hA : C.Ab = D.A) (hB : C.Bb = D.B) :
    C.StrongBaseFloor 6 := by
  intro u hcyc hne
  rw [hA, hB] at hcyc
  rw [C.baseComplex_chainWeight_eq]
  exact D.cycle_weight_ge_6 u hcyc hne

end BB
end Homological
end Stabilizer
end Quantum
