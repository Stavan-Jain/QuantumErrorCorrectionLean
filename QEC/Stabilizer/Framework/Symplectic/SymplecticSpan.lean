import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.NoncommProd
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic
import QEC.Stabilizer.Foundations.BinarySymplectic.Core
import QEC.Stabilizer.Foundations.BinarySymplectic.SymplecticInner
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrix
import QEC.Stabilizer.Framework.Symplectic.IndependentEquiv
import QEC.Stabilizer.Foundations.PauliGroup.NQubitOperator
import QEC.Stabilizer.Foundations.PauliGroup.NQubitElement
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerGroup

namespace Quantum

variable {n : ℕ}

/-!
# Symplectic span and closure

For phase-0 stabilizer generators given as a list `L`, the subgroup closure
equals (the operator parts corresponding to) the F₂-linear span of their
symplectic vectors. So "logical L ∉ subgroup" reduces to "symp(L.operators) ∉
sympSpan(generators)".
-/

namespace NQubitPauliGroupElement

open NQubitPauliOperator
open Submodule

/-- The F₂-submodule spanned by the symplectic vectors (rows) of the check
matrix of `L`. -/
def sympSpan (L : List (NQubitPauliGroupElement n)) : Submodule (ZMod 2) (Fin (n + n) → ZMod 2) :=
  span (ZMod 2) (Set.range (checkMatrix L))

/-- The span of the check-matrix rows equals the span of the symplectic image of
`listToSet L`. -/
lemma sympSpan_eq_span_listToSet (L : List (NQubitPauliGroupElement n)) :
    sympSpan L = span (ZMod 2)
      ((fun g => NQubitPauliOperator.toSymplectic g.operators) '' listToSet L) := by
  rw [sympSpan]
  congr 1
  ext v
  simp only [listToSet, Set.mem_range, Set.mem_image, Set.mem_setOf, List.mem_iff_get]
  constructor
  · rintro ⟨i, hi⟩
    use L.get i
    constructor
    · use i
    · rw [← hi]
      ext j; rfl
  · rintro ⟨g, ⟨i, rfl⟩, hg⟩
    use i
    rw [← hg]
    ext j; rfl

/-- If `g` is in the list `L`, then its symplectic vector is a row of the check
matrix. -/
lemma mem_listToSet_symp_in_range (L : List (NQubitPauliGroupElement n))
    (g : NQubitPauliGroupElement n) (hg : g ∈ listToSet L) :
    NQubitPauliOperator.toSymplectic g.operators ∈ Set.range (checkMatrix L) := by
  rw [listToSet, Set.mem_setOf] at hg
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hg
  use i
  have h_row : checkMatrix L i = NQubitPauliOperator.toSymplectic (L.get i).operators := by
    ext j; rfl
  rw [h_row, congr_arg (fun e => NQubitPauliOperator.toSymplectic e.operators) hi]

/-- For phase-0 generators, closure is contained in the symplectic span: if
`g ∈ Subgroup.closure (listToSet L)` then
`NQubitPauliOperator.toSymplectic g.operators ∈ sympSpan L`. -/
theorem mem_closure_implies_symp_in_span (L : List (NQubitPauliGroupElement n))
    (_ : AllPhaseZero L) (g : NQubitPauliGroupElement n)
    (hg : g ∈ Subgroup.closure (listToSet L)) :
    NQubitPauliOperator.toSymplectic g.operators ∈ sympSpan L := by
  rw [sympSpan_eq_span_listToSet]
  exact Quantum.toSymplectic_mem_span_of_mem_closure hg

/-- Linear relation on the span: zero/add/smul cases are handled once. To prove
∀ v ∈ sympSpan L, (Finset.sum indices fun j => v j) = 0, it suffices to prove
that each row of the check matrix sums to 0 on `indices` (the mem case). -/
theorem sympSpan_sum_eq_zero (L : List (NQubitPauliGroupElement n)) (indices : Finset (Fin (n + n)))
    (h_mem : ∀ k : Fin L.length, Finset.sum indices (fun j => (checkMatrix L k) j) = 0) :
    ∀ v ∈ sympSpan L, Finset.sum indices (fun j => v j) = 0 := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := hx
    rw [← hk]
    exact h_mem k
  | zero => simp only [Pi.zero_apply, Finset.sum_const_zero]
  | add x y _ _ hx hy =>
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib, hx, hy, zero_add]
  | smul a x _ hx =>
    simp only [Pi.smul_apply]
    rw [Finset.sum_congr rfl fun j _ => smul_eq_mul (a := a) (x j)]
    rw [← Finset.mul_sum]
    rw [hx, mul_zero]

/-- Generic "logical not in subgroup" via symplectic span: if `L` has phase 0
and its symplectic vector is not in the span of the generators' symplectic
vectors, then `L` is not in the subgroup closure. -/
theorem not_mem_closure_of_symp_not_in_span (L : List (NQubitPauliGroupElement n))
    (hPhase : AllPhaseZero L) (g : NQubitPauliGroupElement n) (_ : g.phasePower = 0)
    (hg_symp : NQubitPauliOperator.toSymplectic g.operators ∉ sympSpan L) :
    g ∉ Subgroup.closure (listToSet L) := by
  intro h
  exact hg_symp (mem_closure_implies_symp_in_span L hPhase g h)

/-- When `Subgroup.closure (listToSet L) = H`, use this to reduce "g ∉ H" to
"g's symplectic vector is not in sympSpan L". Cuts boilerplate per code. -/
theorem not_mem_subgroup_of_symp_not_in_span (L : List (NQubitPauliGroupElement n))
    (H : Subgroup (NQubitPauliGroupElement n)) (h_eq : Subgroup.closure (listToSet L) = H)
    (hPhase : AllPhaseZero L) (g : NQubitPauliGroupElement n) (hg_phase : g.phasePower = 0)
    (hg_symp : NQubitPauliOperator.toSymplectic g.operators ∉ sympSpan L) : g ∉ H := by
  rw [← h_eq]
  exact not_mem_closure_of_symp_not_in_span L hPhase g hg_phase hg_symp

/-- If the symplectic vector of an operator is in the symplectic span of the
generators, there exists an element of the subgroup closure with that operator
part. -/
theorem exists_mem_closure_of_symp_in_span (L : List (NQubitPauliGroupElement n))
    (op : NQubitPauliOperator n)
    (h_in_span : NQubitPauliOperator.toSymplectic op ∈ sympSpan L) :
    ∃ s ∈ Subgroup.closure (listToSet L), s.operators = op := by
  obtain ⟨s, hs⟩ : ∃ s ∈ Subgroup.closure (listToSet L),
      s.operators.toSymplectic = op.toSymplectic := by
    revert h_in_span
    rw [sympSpan]
    refine Submodule.span_induction ?_ ?_ ?_ ?_
    · intro v ⟨a, ha⟩
      use L.get a
      have h_row : checkMatrix L a = NQubitPauliOperator.toSymplectic (L.get a).operators := by
        ext j; rfl
      simp only [listToSet]
      exact ⟨Subgroup.subset_closure (List.mem_iff_get.mpr ⟨a, rfl⟩),
        (ha.symm.trans h_row).symm⟩
    · use 1
      exact ⟨Subgroup.one_mem _, Quantum.toSymplectic_one_operators⟩
    · rintro x y _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
      use s * t
      refine ⟨Subgroup.mul_mem _ hs ht, ?_⟩
      ext j
      exact Quantum.toSymplectic_mul s t j
    · rintro a x hx ⟨s, hs, rfl⟩
      fin_cases a
      · use 1
        exact ⟨Subgroup.one_mem _,
          by rw [Quantum.toSymplectic_one_operators]; exact (zero_smul _ _).symm⟩
      · exact ⟨s, hs, (one_smul _ _).symm⟩
  exact ⟨s, hs.1, NQubitPauliOperator.toSymplectic_injective hs.2⟩

/-!
## No `-I` for general (non-CSS) phase-0 commuting independent generators

Generalises `CSS.negIdentity_not_mem_closure_union` (which requires Z-type /
X-type partition) to any phase-0 pairwise-commuting generator list with
linearly- independent symplectic rows. First used by the [[5,1,3]] five-qubit
perfect code (`Codes/FiveQubit_5_1_3.lean`), the first non-CSS code in the repo.

Proof outline: the closure of phase-0 commuting generators with `Lᵢ² = 1` is
elementary abelian — every element factors as a `Finset.noncommProd` over a
unique subset of indices (`subsetProd`). Symplectic independence pins down the
subset from the operator part: if the operator part is identity, the subset is
empty, so the element is `1` (not `-I`).
-/

variable (L : List (NQubitPauliGroupElement n))

/-- The subset-product of `L` over a Finset `S`, using `Finset.noncommProd`. -/
private noncomputable def subsetProd
    (hC : ∀ g ∈ listToSet L, ∀ h ∈ listToSet L, g * h = h * g)
    (S : Finset (Fin L.length)) : NQubitPauliGroupElement n :=
  S.noncommProd L.get
    (fun i _ j _ _ => hC (L.get i) (List.mem_iff_get.mpr ⟨i, rfl⟩)
                          (L.get j) (List.mem_iff_get.mpr ⟨j, rfl⟩))

@[simp] private lemma subsetProd_empty
    (hC : ∀ g ∈ listToSet L, ∀ h ∈ listToSet L, g * h = h * g) :
    subsetProd L hC ∅ = 1 := by
  simp [subsetProd]

private lemma subsetProd_singleton
    (hC : ∀ g ∈ listToSet L, ∀ h ∈ listToSet L, g * h = h * g) (i : Fin L.length) :
    subsetProd L hC {i} = L.get i := by
  simp [subsetProd]

private lemma subsetProd_insert
    (hC : ∀ g ∈ listToSet L, ∀ h ∈ listToSet L, g * h = h * g)
    {i : Fin L.length} {S : Finset (Fin L.length)} (hi : i ∉ S) :
    subsetProd L hC (insert i S) = L.get i * subsetProd L hC S := by
  unfold subsetProd
  rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hi]

/-- For phase-0 generators, each generator is self-inverse (squares to 1). -/
private lemma get_sq_eq_one_of_phase_zero
    (hPhase : AllPhaseZero L) (i : Fin L.length) :
    L.get i * L.get i = 1 := by
  have hp : (L.get i).phasePower = 0 := hPhase _ (List.mem_iff_get.mpr ⟨i, rfl⟩)
  -- Use g * g⁻¹ = 1 and show g⁻¹ = g (for phase-0 Paulis: phase = -0 = 0 and ops unchanged).
  have h_inv : (L.get i)⁻¹ = L.get i := by
    apply NQubitPauliGroupElement.ext
    · change -((L.get i).phasePower) = (L.get i).phasePower
      rw [hp]; rfl
    · exact NQubitPauliGroupElement.inv_operators _
  calc L.get i * L.get i = L.get i * (L.get i)⁻¹ := by rw [h_inv]
    _ = 1 := NQubitPauliGroupElement.mul_right_inv _

/-- The symplectic image of `subsetProd` is the sum of selected rows. -/
private lemma toSymplectic_subsetProd
    (hC : ∀ g ∈ listToSet L, ∀ h ∈ listToSet L, g * h = h * g)
    (S : Finset (Fin L.length)) :
    NQubitPauliOperator.toSymplectic (subsetProd L hC S).operators =
      ∑ i ∈ S, NQubitPauliOperator.toSymplectic (L.get i).operators := by
  classical
  refine S.induction_on ?_ ?_
  · rw [subsetProd_empty, Finset.sum_empty]
    exact Quantum.toSymplectic_one_operators
  · intro i T hi ih
    rw [subsetProd_insert L hC hi, Finset.sum_insert hi]
    funext j
    rw [Quantum.toSymplectic_mul]
    have := congrFun ih j
    simp only [Pi.add_apply, this]

/-- If `subsetProd L hC S` has identity operators, the symplectic rows on `S`
sum to 0. -/
private lemma sum_symp_zero_of_subsetProd_operators_identity
    (hC : ∀ g ∈ listToSet L, ∀ h ∈ listToSet L, g * h = h * g)
    {S : Finset (Fin L.length)}
    (h : (subsetProd L hC S).operators = NQubitPauliOperator.identity n) :
    ∑ i ∈ S, NQubitPauliOperator.toSymplectic (L.get i).operators = 0 := by
  rw [← toSymplectic_subsetProd L hC S, h]
  funext j
  unfold NQubitPauliOperator.toSymplectic NQubitPauliOperator.identity
  split_ifs <;> rfl

/-- For linearly independent rows, a sum of selected rows being zero forces
empty selection. -/
private lemma empty_of_sum_symp_zero
    (hIndep : rowsLinearIndependent L)
    {S : Finset (Fin L.length)}
    (h : ∑ i ∈ S, NQubitPauliOperator.toSymplectic (L.get i).operators = 0) :
    S = ∅ := by
  classical
  -- Build the Finsupp with all-1's support on S; linear combination = 0; independence forces 0.
  let l : Fin L.length →₀ ZMod 2 :=
    { support := S
      toFun := fun i => if i ∈ S then 1 else 0
      mem_support_toFun := fun i => by
        constructor
        · intro hi; rw [if_pos hi]; exact one_ne_zero
        · intro hne; by_contra hi; rw [if_neg hi] at hne; exact hne rfl }
  have h_eq : Finsupp.linearCombination (ZMod 2) (checkMatrix L) l = 0 := by
    rw [Finsupp.linearCombination_apply]
    simp only [Finsupp.sum, l, Finsupp.coe_mk]
    have heq_sum : ∑ i ∈ S, (if i ∈ S then (1 : ZMod 2) else 0) • checkMatrix L i =
        ∑ i ∈ S, NQubitPauliOperator.toSymplectic (L.get i).operators := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [if_pos hi, one_smul]
      rfl
    rw [heq_sum, h]
  have hl_zero : l = 0 := hIndep.finsuppLinearCombination_injective
    (h_eq.trans (LinearMap.map_zero _).symm)
  ext i
  constructor
  · intro hi
    have : l i = 1 := by simp [l, hi]
    have : (0 : Fin L.length →₀ ZMod 2) i = 1 := by rw [← hl_zero]; exact this
    simp at this
  · intro hi; exact absurd hi (Finset.notMem_empty i)

/-- The subset-products commute with each generator (and with each other). -/
private lemma subsetProd_commute_get
    (hC : ∀ g ∈ listToSet L, ∀ h ∈ listToSet L, g * h = h * g)
    (S : Finset (Fin L.length)) (i : Fin L.length) :
    subsetProd L hC S * L.get i = L.get i * subsetProd L hC S := by
  unfold subsetProd
  apply Finset.noncommProd_induction S L.get _ (fun x => x * L.get i = L.get i * x)
  · intro a b ha hb
    calc (a * b) * L.get i = a * (b * L.get i) := by rw [mul_assoc]
      _ = a * (L.get i * b) := by rw [hb]
      _ = (a * L.get i) * b := by rw [mul_assoc]
      _ = (L.get i * a) * b := by rw [ha]
      _ = L.get i * (a * b) := by rw [mul_assoc]
  · rw [one_mul, mul_one]
  · intros j _hj
    exact hC (L.get j) (List.mem_iff_get.mpr ⟨j, rfl⟩)
              (L.get i) (List.mem_iff_get.mpr ⟨i, rfl⟩)

/-- Pre-step: multiplication by a single generator from the right shifts
membership of that generator's index in the subset by symmetric difference with
`{i}`. -/
private lemma subsetProd_mul_get
    (hPhase : AllPhaseZero L)
    (hC : ∀ g ∈ listToSet L, ∀ h ∈ listToSet L, g * h = h * g)
    (S : Finset (Fin L.length)) (i : Fin L.length) :
    subsetProd L hC S * L.get i = subsetProd L hC (symmDiff S {i}) := by
  classical
  by_cases hi_S : i ∈ S
  · -- i ∈ S: S Δ {i} = S.erase i.
    have hSym : symmDiff S {i} = S.erase i := by
      ext j
      simp only [Finset.mem_erase, Finset.mem_singleton, Finset.mem_symmDiff]
      rcases eq_or_ne j i with rfl | hji
      · simp [hi_S]
      · simp [hji]
    rw [hSym]
    have hS_eq : S = insert i (S.erase i) := (Finset.insert_erase hi_S).symm
    nth_rewrite 1 [hS_eq]
    rw [subsetProd_insert L hC (Finset.notMem_erase i S)]
    rw [mul_assoc, subsetProd_commute_get L hC (S.erase i) i]
    rw [← mul_assoc, get_sq_eq_one_of_phase_zero L hPhase i, one_mul]
  · -- i ∉ S: S Δ {i} = insert i S.
    have hSym : symmDiff S {i} = insert i S := by
      ext j
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_symmDiff]
      rcases eq_or_ne j i with rfl | hji
      · simp [hi_S]
      · simp [hji]
    rw [hSym, subsetProd_insert L hC hi_S]
    exact subsetProd_commute_get L hC S i

/-- Multiplication law for `subsetProd`:
`subsetProd S * subsetProd T = subsetProd (S Δ T)`. -/
private lemma subsetProd_mul_eq_symmDiff
    (hPhase : AllPhaseZero L)
    (hC : ∀ g ∈ listToSet L, ∀ h ∈ listToSet L, g * h = h * g)
    (S T : Finset (Fin L.length)) :
    subsetProd L hC S * subsetProd L hC T = subsetProd L hC (symmDiff S T) := by
  classical
  -- Generalize over S, then induct on T.
  revert S
  induction T using Finset.induction_on with
  | empty =>
    intro S
    rw [subsetProd_empty, mul_one]
    congr 1
    exact (symmDiff_bot S).symm
  | insert i T' hi ih =>
    intro S
    rw [subsetProd_insert L hC hi]
    rw [show subsetProd L hC S * (L.get i * subsetProd L hC T') =
        (subsetProd L hC S * L.get i) * subsetProd L hC T' from (mul_assoc _ _ _).symm]
    rw [subsetProd_mul_get L hPhase hC S i]
    rw [ih]
    congr 1
    -- (S Δ {i}) Δ T' = S Δ (insert i T').
    have h1 : symmDiff (symmDiff S {i}) T' = symmDiff S (symmDiff {i} T') :=
      symmDiff_assoc S {i} T'
    have h2 : symmDiff {i} T' = insert i T' := by
      ext j
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_symmDiff]
      rcases eq_or_ne j i with rfl | hji
      · simp [hi]
      · simp [hji]
    rw [h1, h2]

private lemma subsetProd_self_inv
    (hPhase : AllPhaseZero L)
    (hC : ∀ g ∈ listToSet L, ∀ h ∈ listToSet L, g * h = h * g)
    (S : Finset (Fin L.length)) :
    subsetProd L hC S * subsetProd L hC S = 1 := by
  rw [subsetProd_mul_eq_symmDiff L hPhase hC S S, symmDiff_self, Finset.bot_eq_empty,
    subsetProd_empty]

private lemma subsetProd_inv_eq
    (hPhase : AllPhaseZero L)
    (hC : ∀ g ∈ listToSet L, ∀ h ∈ listToSet L, g * h = h * g)
    (S : Finset (Fin L.length)) :
    (subsetProd L hC S)⁻¹ = subsetProd L hC S := by
  have h := subsetProd_self_inv L hPhase hC S
  exact (eq_inv_of_mul_eq_one_right h).symm

/-- The image of `subsetProd` is a subgroup containing all generators. -/
private noncomputable def subsetProdSubgroup
    (hPhase : AllPhaseZero L)
    (hC : ∀ g ∈ listToSet L, ∀ h ∈ listToSet L, g * h = h * g) :
    Subgroup (NQubitPauliGroupElement n) where
  carrier := Set.range (subsetProd L hC)
  one_mem' := ⟨∅, subsetProd_empty L hC⟩
  mul_mem' := by
    rintro x y ⟨S, rfl⟩ ⟨T, rfl⟩
    exact ⟨symmDiff S T, (subsetProd_mul_eq_symmDiff L hPhase hC S T).symm⟩
  inv_mem' := by
    rintro x ⟨S, rfl⟩
    refine ⟨S, ?_⟩
    exact (subsetProd_inv_eq L hPhase hC S).symm

/-- For phase-0 pairwise-commuting Pauli generators with linearly-independent
symplectic rows, `-I` is not in the closure of the generators.

Non-CSS analogue of `CSS.negIdentity_not_mem_closure_union`. -/
theorem negIdentity_not_mem_of_indep_phase_zero_commute
    (hPhase : AllPhaseZero L)
    (hIndep : rowsLinearIndependent L)
    (hC : ∀ g ∈ listToSet L, ∀ h ∈ listToSet L, g * h = h * g) :
    StabilizerGroup.negIdentity n ∉ Subgroup.closure (listToSet L) := by
  intro hneg
  -- Closure ⊆ subsetProdSubgroup, since each generator equals a subsetProd of a singleton.
  have h_le : Subgroup.closure (listToSet L) ≤ subsetProdSubgroup L hPhase hC := by
    refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hg
    exact ⟨{i}, by rw [subsetProd_singleton]; exact hi⟩
  obtain ⟨S, hS⟩ := h_le hneg
  -- hS : subsetProd L hC S = negIdentity n.
  have h_ops : (subsetProd L hC S).operators = NQubitPauliOperator.identity n := by
    rw [hS]; exact StabilizerGroup.negIdentity_operators n
  have hS_empty : S = ∅ :=
    empty_of_sum_symp_zero L hIndep
      (sum_symp_zero_of_subsetProd_operators_identity L hC h_ops)
  rw [hS_empty, subsetProd_empty] at hS
  exact StabilizerGroup.negIdentity_ne_one n hS.symm

end NQubitPauliGroupElement

end Quantum
