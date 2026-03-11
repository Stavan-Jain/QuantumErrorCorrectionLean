import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import QEC.Stabilizer.BinarySymplectic.Core
import QEC.Stabilizer.BinarySymplectic.SymplecticInner
import QEC.Stabilizer.BinarySymplectic.CheckMatrix
import QEC.Stabilizer.BinarySymplectic.IndependentEquiv
import QEC.Stabilizer.PauliGroup.NQubitOperator
import QEC.Stabilizer.PauliGroup.NQubitElement

namespace Quantum

variable {n : ℕ}

/-!
# Symplectic span and closure

For phase-0 stabilizer generators given as a list `L`, the subgroup closure equals
(the operator parts corresponding to) the F₂-linear span of their symplectic vectors.
So "logical L ∉ subgroup" reduces to "symp(L.operators) ∉ sympSpan(generators)".
-/

namespace NQubitPauliGroupElement

open NQubitPauliOperator
open Submodule

/-- The F₂-submodule spanned by the symplectic vectors (rows) of the check matrix of `L`. -/
def sympSpan (L : List (NQubitPauliGroupElement n)) : Submodule (ZMod 2) (Fin (n + n) → ZMod 2) :=
  span (ZMod 2) (Set.range (checkMatrix L))

/-- The span of the check-matrix rows equals the span of the symplectic image of `listToSet L`. -/
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

/-- If `g` is in the list `L`, then its symplectic vector is a row of the check matrix. -/
lemma mem_listToSet_symp_in_range (L : List (NQubitPauliGroupElement n))
    (g : NQubitPauliGroupElement n) (hg : g ∈ listToSet L) :
    NQubitPauliOperator.toSymplectic g.operators ∈ Set.range (checkMatrix L) := by
  rw [listToSet, Set.mem_setOf] at hg
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hg
  use i
  have h_row : checkMatrix L i = NQubitPauliOperator.toSymplectic (L.get i).operators := by
    ext j; rfl
  rw [h_row, congr_arg (fun e => NQubitPauliOperator.toSymplectic e.operators) hi]

/-- For phase-0 generators, closure is contained in the symplectic span:
  if `g ∈ Subgroup.closure (listToSet L)` then
  `NQubitPauliOperator.toSymplectic g.operators ∈ sympSpan L`. -/
theorem mem_closure_implies_symp_in_span (L : List (NQubitPauliGroupElement n))
    (_ : AllPhaseZero L) (g : NQubitPauliGroupElement n)
    (hg : g ∈ Subgroup.closure (listToSet L)) :
    NQubitPauliOperator.toSymplectic g.operators ∈ sympSpan L := by
  rw [sympSpan_eq_span_listToSet]
  exact Quantum.toSymplectic_mem_span_of_mem_closure hg

/-- Linear relation on the span: zero/add/smul cases are handled once. To prove
  ∀ v ∈ sympSpan L, (Finset.sum indices fun j => v j) = 0, it suffices to prove that
  each row of the check matrix sums to 0 on `indices` (the mem case). -/
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

/-- Generic "logical not in subgroup" via symplectic span: if `L` has phase 0 and its
  symplectic vector is not in the span of the generators' symplectic vectors, then
  `L` is not in the subgroup closure. -/
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

/-- If the symplectic vector of an operator is in the symplectic span of the generators,
  there exists an element of the subgroup closure with that operator part. -/
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

end NQubitPauliGroupElement

end Quantum
