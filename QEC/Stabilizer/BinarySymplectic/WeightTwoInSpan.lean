import Mathlib.Data.Finset.Card
import QEC.Stabilizer.BinarySymplectic.SymplecticSpan
import QEC.Stabilizer.BinarySymplectic.SymplecticInner
import QEC.Stabilizer.PauliGroup.NQubitOperator
import QEC.Stabilizer.PauliGroup.NQubitElement

namespace Quantum

variable {n : ℕ}

/-!
# Weight-2 "in span" reduction

If for every pair of distinct qubits (i, j), every operator with support exactly {i, j}
that commutes with all generators has its symplectic vector in sympSpan L, then every
weight-2 operator that commutes with all generators is in the span. This reduces
weight_2_operators_in_span to 36 per-pair lemmas (for n = 9).
-/

namespace NQubitPauliGroupElement

open NQubitPauliOperator Submodule

/-- Reduction: if for every pair of distinct qubits (i, j), every operator with
    support {i, j} that commutes with all generators is in the symplectic span,
    then every weight-2 operator that commutes with all generators is in the span. -/
theorem weight_two_in_span_of_per_pair (L : List (NQubitPauliGroupElement n))
    (h_per_pair : ∀ i j : Fin n, i ≠ j →
      ∀ op : NQubitPauliOperator n,
        NQubitPauliOperator.support op = {i, j} →
          (∀ g ∈ L, NQubitPauliOperator.symplecticInner op g.operators = 0) →
            NQubitPauliOperator.toSymplectic op ∈ sympSpan L)
    (op : NQubitPauliOperator n) (h_weight : NQubitPauliOperator.weight op = 2)
    (h_comm : ∀ g ∈ L, NQubitPauliOperator.symplecticInner op g.operators = 0) :
    NQubitPauliOperator.toSymplectic op ∈ sympSpan L := by
  obtain ⟨i, j, hij, h_supp⟩ :=
    Finset.card_eq_two.mp (by rw [← NQubitPauliOperator.weight, h_weight])
  exact h_per_pair i j hij op h_supp h_comm

/-- Reduce a per-pair weight-2 proof to enumeration over PauliOperator × PauliOperator.
    Instead of quantifying over all NQubitPauliOperator n (4^n elements), the hypothesis `h`
    only quantifies over PauliOperator × PauliOperator (16 elements), making `decide` feasible. -/
theorem weight_2_pair_by_enum (L : List (NQubitPauliGroupElement n)) (i j : Fin n) (hij : i ≠ j)
    (h : ∀ (pi pj : PauliOperator), pi ≠ .I → pj ≠ .I →
      let op : NQubitPauliOperator n := fun k => if k = i then pi else if k = j then pj else .I
      (∀ g ∈ L, NQubitPauliOperator.symplecticInner op g.operators = 0) →
      NQubitPauliOperator.toSymplectic op ∈ sympSpan L)
    (op : NQubitPauliOperator n) (h_supp : NQubitPauliOperator.support op = {i, j})
    (h_comm : ∀ g ∈ L, NQubitPauliOperator.symplecticInner op g.operators = 0) :
    NQubitPauliOperator.toSymplectic op ∈ sympSpan L := by
  have hi : op i ≠ .I := by
    have : i ∈ NQubitPauliOperator.support op := by
      rw [h_supp]; exact Finset.mem_insert_self i {j}
    exact (NQubitPauliOperator.mem_support op i).mp this
  have hj : op j ≠ .I := by
    have : j ∈ NQubitPauliOperator.support op := by
      rw [h_supp]; exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self j))
    exact (NQubitPauliOperator.mem_support op j).mp this
  have hop : op = fun k => if k = i then op i else if k = j then op j else .I := by
    ext k
    by_cases hki : k = i
    · simp [hki]
    · by_cases hkj : k = j
      · subst hkj; simp [hki]
      · have hk_not_supp : k ∉ NQubitPauliOperator.support op := by
          rw [h_supp, Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨hki, hkj⟩
        have : op k = .I := by
          by_contra h_ne; exact hk_not_supp ((NQubitPauliOperator.mem_support op k).mpr h_ne)
        simp [hki, hkj, this]
  rw [hop]
  exact h (op i) (op j) hi hj (by rwa [← hop])

/-- Combined helper: proves all weight-2 operators are in span by enumerating PauliOperator pairs.
    For each pair (i,j), the hypothesis only checks 9 non-identity PauliOperator assignments.
    This is the main entry point for concrete codes — the `h` hypothesis is designed to be
    closed by a single `decide` (quantifies over Fin n × Fin n × PauliOperator × PauliOperator,
    which for n=9 is ~648 cases instead of ~67M). -/
theorem weight_2_in_span_by_enum (L : List (NQubitPauliGroupElement n))
    (h : ∀ (i j : Fin n), i ≠ j → ∀ (pi pj : PauliOperator), pi ≠ .I → pj ≠ .I →
      let op : NQubitPauliOperator n := fun k => if k = i then pi else if k = j then pj else .I
      (∀ g ∈ L, NQubitPauliOperator.symplecticInner op g.operators = 0) →
      NQubitPauliOperator.toSymplectic op ∈ sympSpan L)
    (op : NQubitPauliOperator n) (h_weight : NQubitPauliOperator.weight op = 2)
    (h_comm : ∀ g ∈ L, NQubitPauliOperator.symplecticInner op g.operators = 0) :
    NQubitPauliOperator.toSymplectic op ∈ sympSpan L :=
  weight_two_in_span_of_per_pair L
    (fun i j hij op h_supp h_comm => weight_2_pair_by_enum L i j hij (h i j hij) op h_supp h_comm)
    op h_weight h_comm

end NQubitPauliGroupElement

end Quantum
