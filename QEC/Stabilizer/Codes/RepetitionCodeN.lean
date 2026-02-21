import Mathlib.Tactic
import Mathlib.Data.List.OfFn
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
import QEC.Stabilizer.PauliGroup.NQubitOperator
import QEC.Stabilizer.PauliGroupSingle.Operator

namespace Quantum
open scoped BigOperators

namespace StabilizerGroup
namespace RepetitionCodeN

/-!
# Parametric repetition code (Z-only CSS) on `n+2` qubits

This is a parametric version of `RepetitionCode3`, defined on **`n+2` qubits** to make the
adjacent-pair indexing clean.

Generators (Z-checks):
`Z_i Z_{i+1}` for `i : Fin (n+1)`, acting on qubits `i` and `i+1`.

We show the generated subgroup is a `StabilizerGroup (n+2)`:
- **abelian**: all generators are Z-type
- **no `-I`**: apply the reusable CSS lemma with `XGenerators = ∅`
-/

open NQubitPauliGroupElement

/-!
## Generators
-/

/-- The adjacent Z-check `Z_i Z_{i+1}` on `n+2` qubits, indexed by `i : Fin (n+1)`. -/
def ZPair (n : ℕ) (i : Fin (n + 1)) : NQubitPauliGroupElement (n + 2) :=
  ⟨0,
    ((NQubitPauliOperator.identity (n + 2)).set (Fin.castSucc i) PauliOperator.Z)
      |>.set (Fin.succ i) PauliOperator.Z⟩

def ZGenerators (n : ℕ) : Set (NQubitPauliGroupElement (n + 2)) :=
  Set.range (ZPair n)

def XGenerators (n : ℕ) : Set (NQubitPauliGroupElement (n + 2)) :=
  (∅ : Set (NQubitPauliGroupElement (n + 2)))

def generators (n : ℕ) : Set (NQubitPauliGroupElement (n + 2)) :=
  ZGenerators n ∪ XGenerators n

/-- Generators as a list (for check-matrix and independence arguments). -/
def generatorsList (n : ℕ) : List (NQubitPauliGroupElement (n + 2)) :=
  List.ofFn (ZPair n)

lemma generatorsList_length (n : ℕ) : (generatorsList n).length = n + 1 := by
  simp only [generatorsList, List.length_ofFn]

lemma generatorsList_get (n : ℕ) (i : Fin (generatorsList n).length) :
    (generatorsList n).get i = ZPair n (Fin.cast (generatorsList_length n) i) := by
  simp only [generatorsList, List.get_ofFn]

/-- The list of generators has the same elements as `ZGenerators n`. -/
lemma listToSet_generatorsList (n : ℕ) :
    listToSet (generatorsList n) = ZGenerators n := by
  ext g
  simp only [listToSet, Set.mem_setOf, ZGenerators, Set.mem_range]
  rw [List.mem_iff_get]
  constructor
  · intro ⟨i, hi⟩
    use Fin.cast (generatorsList_length n) i
    rw [← hi, generatorsList_get]
  · intro ⟨i, hi⟩
    use Fin.cast (generatorsList_length n).symm i
    rw [generatorsList_get (i := Fin.cast (generatorsList_length n).symm i),
      (Fin.rightInverse_cast (generatorsList_length n)) i, hi]

/-- Every element of the generators list has phase power 0. -/
lemma AllPhaseZero_generatorsList (n : ℕ) :
    NQubitPauliGroupElement.AllPhaseZero (generatorsList n) := by
  intro g hg
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hg
  rw [generatorsList_get]
  rfl

def subgroup (n : ℕ) : Subgroup (NQubitPauliGroupElement (n + 2)) :=
  Subgroup.closure (generators n)

/-- `ZPair n i` has Z at qubits `castSucc i` and `succ i`, and I elsewhere. -/
lemma ZPair_operators_at (n : ℕ) (i : Fin (n + 1)) (k : Fin (n + 2)) :
    (ZPair n i).operators k =
      if k = Fin.castSucc i ∨ k = Fin.succ i then PauliOperator.Z else PauliOperator.I := by
  simp only [ZPair, NQubitPauliOperator.set, NQubitPauliOperator.identity]
  by_cases hk1 : k = Fin.succ i <;> by_cases hk2 : k = Fin.castSucc i <;> simp [hk1, hk2]

/-- Z-column of the check matrix: row `i` has 1 at Z-qubit `k` iff `k` is one of the two qubits. -/
lemma checkMatrix_ZColumn (n : ℕ) (i : Fin (generatorsList n).length) (k : Fin (n + 2)) :
    checkMatrix (generatorsList n) i (Fin.natAdd (n + 2) k) =
      if k = Fin.castSucc (Fin.cast (generatorsList_length n) i)
          ∨ k = Fin.succ (Fin.cast (generatorsList_length n) i)
      then (1 : ZMod 2) else 0 := by
  simp only [checkMatrix, generatorsList_get, NQubitPauliOperator.toSymplectic_Z_part,
    ZPair_operators_at]
  split_ifs <;> simp only [PauliOperator.toSymplecticSingle_Z, PauliOperator.toSymplecticSingle_I]

/-- Row index for generator `j`: `(generatorsList n).get (rowIdx n j) = ZPair n j`. -/
def rowIdx (n : ℕ) (j : Fin (n + 1)) : Fin (generatorsList n).length :=
  Fin.cast (generatorsList_length n).symm j

lemma rowIdx_cast (n : ℕ) (j : Fin (n + 1)) :
    Fin.cast (generatorsList_length n) (rowIdx n j) = j :=
  (Fin.rightInverse_cast (generatorsList_length n)) j

lemma rowIdx_injective (n : ℕ) (j j' : Fin (n + 1)) (h : rowIdx n j = rowIdx n j') : j = j' := by
  rw [← rowIdx_cast n j, ← rowIdx_cast n j', h]

/-- At Z-column for qubit `0`, only row `rowIdx n 0` contributes. -/
lemma sum_ZColumn_zero (n : ℕ) (f : Fin (generatorsList n).length → ZMod 2) :
    (∑ i : Fin (generatorsList n).length,
        f i * checkMatrix (generatorsList n) i (Fin.natAdd (n + 2) ⟨0, Nat.zero_lt_succ (n + 1)⟩)) =
      f (rowIdx n ⟨0, Nat.zero_lt_succ n⟩) := by
  set a := rowIdx n ⟨0, Nat.zero_lt_succ n⟩
  set col0 := Fin.natAdd (n + 2) ⟨0, Nat.zero_lt_succ (n + 1)⟩
  have key (i : Fin (generatorsList n).length) :
      checkMatrix (generatorsList n) i col0 = if i = a then (1 : ZMod 2) else 0 := by
    rw [checkMatrix_ZColumn]
    congr 1
    apply propext
    constructor
    · intro h
      rcases h with h0 | h1
      · have hval : (Fin.cast (generatorsList_length n) i).val = 0 := by
          have h0val := congr_arg Fin.val h0
          have hzero : (⟨0, Nat.zero_lt_succ (n + 1)⟩ : Fin (n + 2)).val = 0 := rfl
          rw [hzero] at h0val
          have castSucc_val : (Fin.castSucc (Fin.cast (generatorsList_length n) i)).val =
              (Fin.cast (generatorsList_length n) i).val % (n + 2) := by
            simp only [← Fin.coe_eq_castSucc, Fin.val_natCast]
          rw [castSucc_val] at h0val
          have hlt := Nat.lt.step (Fin.cast (generatorsList_length n) i).2
          rw [Nat.mod_eq_of_lt hlt] at h0val
          exact h0val.symm
        have hcast : Fin.cast (generatorsList_length n) i = ⟨0, Nat.zero_lt_succ n⟩ := Fin.ext hval
        rw [← (Fin.leftInverse_cast (generatorsList_length n)) i, hcast]
        rfl
      · exfalso
        exact Fin.succ_ne_zero (Fin.cast (generatorsList_length n) i) h1.symm
    · intro heq
      left
      rw [heq, rowIdx_cast]
      exact Fin.castSucc_zero.symm
  rw [Finset.sum_congr rfl (fun i _ => by rw [key i])]
  simp only [mul_ite, mul_zero]
  have sum_eq : (∑ x, if x = a then f x * 1 else 0) = (∑ x, if x = a then f x else 0) :=
    Finset.sum_congr rfl (fun x _ => by split_ifs <;> simp [*])
  rw [sum_eq, Finset.sum_ite_eq' Finset.univ a f, if_pos (Finset.mem_univ a)]

/-- At Z-column for qubit `n+1`, only row `rowIdx n ⟨n, _⟩` contributes. -/
lemma sum_ZColumn_last (n : ℕ) (f : Fin (generatorsList n).length → ZMod 2) :
    (∑ i : Fin (generatorsList n).length,
        f i * checkMatrix (generatorsList n) i
          (Fin.natAdd (n + 2) ⟨n + 1, Nat.lt_succ_self (n + 1)⟩)) =
      f (rowIdx n ⟨n, Nat.lt_succ_self n⟩) := by
  set a := rowIdx n ⟨n, Nat.lt_succ_self n⟩
  set colLast := Fin.natAdd (n + 2) ⟨n + 1, Nat.lt_succ_self (n + 1)⟩
  have key (i : Fin (generatorsList n).length) :
      checkMatrix (generatorsList n) i colLast = if i = a then (1 : ZMod 2) else 0 := by
    rw [checkMatrix_ZColumn]
    congr 1
    apply propext
    constructor
    · intro h
      rcases h with h0 | h1
      · exfalso
        have h0val := congr_arg Fin.val h0
        have castSucc_eq : (Fin.castSucc (Fin.cast (generatorsList_length n) i)).val =
            (Fin.cast (generatorsList_length n) i).val := by
          simp only [← Fin.coe_eq_castSucc, Fin.val_natCast,
            Nat.mod_eq_of_lt (Nat.lt.step (Fin.cast (generatorsList_length n) i).2)]
        rw [castSucc_eq] at h0val
        have hlt : (Fin.cast (generatorsList_length n) i).val < n + 1 := (Fin.cast _ i).2
        rw [← h0val] at hlt
        exact Nat.lt_irrefl (n + 1) hlt
      · have hval : (Fin.cast (generatorsList_length n) i).val = n := by
          have h1val := congr_arg Fin.val h1
          simp only [Fin.val_succ] at h1val
          omega
        have hcast : Fin.cast (generatorsList_length n) i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hval
        rw [← (Fin.leftInverse_cast (generatorsList_length n)) i, hcast]
        rfl
    · intro heq
      right
      rw [heq, rowIdx_cast]
      exact Fin.ext rfl
  rw [Finset.sum_congr rfl (fun i _ => by rw [key i])]
  simp only [mul_ite, mul_zero]
  have sum_eq : (∑ x, if x = a then f x * 1 else 0) = (∑ x, if x = a then f x else 0) :=
    Finset.sum_congr rfl (fun x _ => by split_ifs <;> simp [*])
  rw [sum_eq, Finset.sum_ite_eq' Finset.univ a f, if_pos (Finset.mem_univ a)]

/-- At Z-column for qubit `j` with `1 ≤ j ≤ n`, rows `rowIdx n (j-1)` and
`rowIdx n j` contribute. -/
lemma sum_ZColumn_mid (n : ℕ) (f : Fin (generatorsList n).length → ZMod 2) (j : ℕ)
    (hj : j < n + 2) (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    (∑ i : Fin (generatorsList n).length,
        f i * checkMatrix (generatorsList n) i (Fin.natAdd (n + 2) ⟨j, hj⟩)) =
      f (rowIdx n ⟨j - 1, by omega⟩) + f (rowIdx n ⟨j, by omega⟩) := by
  have h_rows : ∀ i : Fin (generatorsList n).length,
      checkMatrix (generatorsList n) i (Fin.natAdd (n + 2) ⟨j, hj⟩) =
      if i = rowIdx n ⟨j - 1, by omega⟩ ∨ i = rowIdx n ⟨j, by grind⟩ then 1 else 0 := by
    intros i
    rw [checkMatrix_ZColumn];
    simp +decide [ Fin.ext_iff, rowIdx ];
    grind +ring
  generalize_proofs at *;
  simp_all +decide [ Finset.sum_ite ];
  rw [Finset.sum_eq_add (rowIdx n ⟨j - 1, by assumption⟩) (rowIdx n ⟨j, by assumption⟩)] <;>
    norm_num [Fin.ext_iff]
  · simp +decide [ Quantum.StabilizerGroup.RepetitionCodeN.rowIdx ];
    omega;
  · tauto

/-- The check-matrix rows of the parametric repetition-code generators are linearly independent. -/
theorem rowsLinearIndependent_generatorsList (n : ℕ) :
    NQubitPauliGroupElement.rowsLinearIndependent (generatorsList n) := by
  unfold Quantum.NQubitPauliGroupElement.rowsLinearIndependent;
  have h_check_matrix_rows_lin_indep :
      ∀ (f : Fin (generatorsList n).length → ZMod 2),
      (∀ i, ∑ j, f j * checkMatrix (generatorsList n) j i = 0) → f = 0 := by
    intro f hf
    have h_zero : ∀ j : Fin (n + 1), f (rowIdx n j) = 0 := by
      intro j
      induction j using Fin.induction with
      | zero =>
        specialize hf (Fin.natAdd (n + 2) ⟨0, Nat.zero_lt_succ (n + 1)⟩)
        rw [sum_ZColumn_zero] at hf; aesop
      | succ j ih =>
        have := hf (Fin.natAdd (n + 2) (Fin.castSucc j.succ))
        rw [sum_ZColumn_mid] at this <;> norm_num at *
        refine (eq_zero_iff_eq_zero_of_add_eq_zero this).mp ih
        exact Nat.succ_le_of_lt j.2
    ext i; specialize h_zero ( Fin.cast ( generatorsList_length n ) i ) ; aesop;
  rw [ Fintype.linearIndependent_iff ];
  intro g hg i
  specialize h_check_matrix_rows_lin_indep g
  simp_all +decide [funext_iff, Finset.sum_apply]

/-- The parametric repetition-code generator list is an independent generating set. -/
theorem GeneratorsIndependent_generatorsList (n : ℕ) :
    GeneratorsIndependent (n + 2) (generatorsList n) :=
  GeneratorsIndependent_of_rowsLinearIndependent (n + 2) (generatorsList n)
    (rowsLinearIndependent_generatorsList n)

/-!
## Typing: Z-type generators
-/

lemma ZGenerators_are_ZType (n : ℕ) :
    ∀ g, g ∈ ZGenerators n → NQubitPauliGroupElement.IsZTypeElement g := by
  classical
  intro g hg
  rcases hg with ⟨i, rfl⟩
  refine ⟨rfl, ?_⟩
  intro j
  -- The operator is `Z` at `i` and `i+1`, and `I` elsewhere.
  by_cases h1 : j = Fin.succ i
  · subst h1
    exact Or.inr (by simp [ZPair, NQubitPauliOperator.set])
  · by_cases h2 : j = Fin.castSucc i
    · subst h2
      -- Here we use `h1 : castSucc i ≠ succ i` to simplify the outer `set`.
      exact Or.inr (by simp [ZPair, NQubitPauliOperator.set, h1])
    · -- Otherwise the operator is `I`.
      simp [ZPair, NQubitPauliOperator.set, NQubitPauliOperator.identity, h1, h2,
        PauliOperator.IsZType]

/-!
## Abelian: commutation of the generated subgroup
-/

private lemma ZType_commutes {m : ℕ} {g h : NQubitPauliGroupElement m}
    (hg : NQubitPauliGroupElement.IsZTypeElement g)
    (hh : NQubitPauliGroupElement.IsZTypeElement h) :
    g * h = h * g := by
  classical
  apply NQubitPauliGroupElement.commutes_of_componentwise_commutes
  intro k
  have hg' := hg.2 k
  have hh' := hh.2 k
  rcases hg' with hgI | hgZ <;> rcases hh' with hhI | hhZ
  · simp [PauliOperator.mulOp, hgI, hhI]
  · simp [PauliOperator.mulOp, hgI, hhZ]
  · simp [PauliOperator.mulOp, hgZ, hhI]
  · simp [PauliOperator.mulOp, hgZ, hhZ]

theorem generators_commute (n : ℕ) :
    ∀ g ∈ generators n, ∀ h ∈ generators n, g * h = h * g := by
  classical
  intro g hg h hh
  -- Since `XGenerators = ∅`, membership reduces to `ZGenerators`.
  simp [generators, XGenerators] at hg hh
  exact ZType_commutes (ZGenerators_are_ZType n g hg) (ZGenerators_are_ZType n h hh)

theorem subgroup_is_abelian (n : ℕ) :
    ∀ g ∈ subgroup n, ∀ h ∈ subgroup n, g * h = h * g := by
  simpa [subgroup] using
    (Subgroup.abelian_closure_of_pairwise_commute (G := NQubitPauliGroupElement (n + 2))
      (generators n) (generators_commute n))

/-!
## No `-I` in the generated subgroup (CSS lemma with empty X-generators)
-/

theorem negIdentity_not_mem (n : ℕ) :
    negIdentity (n + 2) ∉ subgroup n := by
  have hX :
      ∀ x, x ∈ XGenerators n → NQubitPauliGroupElement.IsXTypeElement x := by
    intro x hx
    simp [XGenerators] at hx
  have hZX :
      ∀ z ∈ ZGenerators n, ∀ x ∈ XGenerators n, z * x = x * z := by
    intro z hz x hx
    simp [XGenerators] at hx
  simpa [subgroup, generators] using
    (CSS.negIdentity_not_mem_closure_union (ZGenerators n) (XGenerators n)
      (ZGenerators_are_ZType n) hX hZX)

/-!
## Logical operators (one logical qubit when `n+2` is odd)

Logical X = X on all `n+2` qubits, logical Z = Z on all `n+2` qubits. They commute with
every stabilizer (each ZPair has exactly two qubits where X and Z meet, so even
anticommutes) and anticommute with each other when `n+2` is odd.
-/

/-- Logical X: X on all `n+2` qubits. -/
def logicalX (n : ℕ) : NQubitPauliGroupElement (n + 2) :=
  ⟨0, NQubitPauliOperator.X (n + 2)⟩

/-- Logical Z: Z on all `n+2` qubits. -/
def logicalZ (n : ℕ) : NQubitPauliGroupElement (n + 2) :=
  ⟨0, NQubitPauliOperator.Z (n + 2)⟩

/-- Logical X and logical Z anticommute when the number of physical qubits `n+2` is odd. -/
theorem logicalX_anticommutes_logicalZ (n : ℕ) (hn : Odd (n + 2)) :
    NQubitPauliGroupElement.Anticommute (logicalX n) (logicalZ n) :=
  NQubitPauliOperator.allX_allZ_anticommute (n + 2) hn

private lemma logicalX_commutes_ZPair (n : ℕ) (i : Fin (n + 1)) :
    logicalX n * ZPair n i = ZPair n i * logicalX n := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (logicalX n).operators (ZPair n i).operators)) =
        ({Fin.castSucc i, Fin.succ i} : Finset (Fin (n + 2))) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ,
      true_and, logicalX, ZPair, NQubitPauliOperator.X, NQubitPauliOperator.set,
      NQubitPauliOperator.identity, NQubitPauliGroupElement.anticommutesAt]
    by_cases hj1 : j = Fin.castSucc i <;> by_cases hj2 : j = Fin.succ i
    · -- j = castSucc i and j = succ i: contradiction
      subst hj1
      exact False.elim ((Fin.castSucc_lt_succ i).ne hj2)
    · -- j = castSucc i only
      subst hj1
      simp only [if_neg (Fin.castSucc_lt_succ i).ne, if_true, PauliOperator.mulOp_X_Z,
        PauliOperator.mulOp_Z_X]
      simp
    · -- j = succ i only
      subst hj2
      simp only [if_neg (Fin.castSucc_lt_succ i).ne.symm, if_true, PauliOperator.mulOp_X_Z,
        PauliOperator.mulOp_Z_X]
      simp only [Fin.isValue, Fin.reduceAdd, or_true]
    · -- j ≠ both: (ZPair n i).operators j = I, so 0 = 0+2 is false
      simp only [if_neg hj1, if_neg hj2, PauliOperator.mulOp_X_I, PauliOperator.mulOp_I_X]
      omega
  rw [hfilter]
  -- {a, b} = insert a {b}; need castSucc i ∉ {succ i}
  have hne : Fin.castSucc i ∉ {Fin.succ i} :=
    fun h => (Fin.castSucc_lt_succ i).ne (Finset.mem_singleton.mp h)
  rw [Finset.card_insert_of_notMem hne, Finset.card_singleton]
  exact even_two

private lemma logicalZ_commutes_ZPair (n : ℕ) (i : Fin (n + 1)) :
    logicalZ n * ZPair n i = ZPair n i * logicalZ n := by
  apply NQubitPauliGroupElement.commutes_of_componentwise_commutes
  intro j
  by_cases hj1 : j = Fin.castSucc i <;> by_cases hj2 : j = Fin.succ i
  · subst hj1; exact False.elim ((Fin.castSucc_lt_succ i).ne hj2)
  · subst hj1
    simp only [logicalZ, ZPair, NQubitPauliOperator.Z, NQubitPauliOperator.set,
      NQubitPauliOperator.identity, if_neg (Fin.castSucc_lt_succ i).ne, if_true,
      PauliOperator.mulOp_Z_Z]
  · subst hj2
    simp only [logicalZ, ZPair, NQubitPauliOperator.Z, NQubitPauliOperator.set,
      NQubitPauliOperator.identity, if_neg (Fin.castSucc_lt_succ i).ne.symm, if_true,
      PauliOperator.mulOp_Z_Z]
  · simp only [logicalZ, ZPair, NQubitPauliOperator.Z, NQubitPauliOperator.set,
      NQubitPauliOperator.identity, if_neg hj1, if_neg hj2, PauliOperator.mulOp_Z_I,
      PauliOperator.mulOp_I_Z]

/-!
## Bundled `StabilizerGroup (n+2)`
-/

noncomputable def stabilizerGroup (n : ℕ) : StabilizerGroup (n + 2) :=
{ toSubgroup := subgroup n
, is_abelian := by
    intro g h hg hh
    exact subgroup_is_abelian n g hg h hh
, no_neg_identity := by
    simpa using negIdentity_not_mem n }

/-- Logical X commutes with every element of the stabilizer. -/
theorem logicalX_mem_centralizer (n : ℕ) :
    logicalX n ∈ centralizer (stabilizerGroup n) := by
  rw [StabilizerGroup.mem_centralizer_iff]
  intro _ hh
  refine Subgroup.closure_induction (p := fun g _ => g * logicalX n = logicalX n * g)
    (fun g hg => ?_)
    (by simp only [NQubitPauliGroupElement.one_mul, NQubitPauliGroupElement.mul_one])
    (fun x y _ _ hx hy => ?_) (fun x _ h => ?_) hh
  · simp only [generators, XGenerators, Set.mem_union, Set.mem_empty_iff_false] at hg
    rcases hg with ⟨i, rfl⟩ | hEmp
    · exact (logicalX_commutes_ZPair n i).symm
    · exact False.elim hEmp
  · calc (x * y) * logicalX n = x * (y * logicalX n) := by rw [NQubitPauliGroupElement.mul_assoc]
      _ = x * (logicalX n * y) := by rw [hy]
      _ = (x * logicalX n) * y := by rw [← NQubitPauliGroupElement.mul_assoc]
      _ = (logicalX n * x) * y := by rw [hx]
      _ = logicalX n * (x * y) := by rw [NQubitPauliGroupElement.mul_assoc]
  · have H : (x⁻¹ * logicalX n) * x = (logicalX n * x⁻¹) * x := by
      rw [NQubitPauliGroupElement.mul_assoc, ← h, inv_mul_cancel_left,
        NQubitPauliGroupElement.mul_assoc, inv_mul_cancel, NQubitPauliGroupElement.mul_one]
    exact mul_right_cancel H

/-- Logical Z commutes with every element of the stabilizer. -/
theorem logicalZ_mem_centralizer (n : ℕ) :
    logicalZ n ∈ centralizer (stabilizerGroup n) := by
  rw [StabilizerGroup.mem_centralizer_iff]
  intro _ hh
  refine Subgroup.closure_induction (p := fun g _ => g * logicalZ n = logicalZ n * g)
    (fun g hg => ?_)
    (by simp only [NQubitPauliGroupElement.one_mul, NQubitPauliGroupElement.mul_one])
    (fun x y _ _ hx hy => ?_) (fun x _ h => ?_) hh
  · simp only [generators, XGenerators, Set.mem_union, Set.mem_empty_iff_false] at hg
    rcases hg with ⟨i, rfl⟩ | hEmp
    · exact (logicalZ_commutes_ZPair n i).symm
    · exact False.elim hEmp
  · calc (x * y) * logicalZ n = x * (y * logicalZ n) := by rw [NQubitPauliGroupElement.mul_assoc]
      _ = x * (logicalZ n * y) := by rw [hy]
      _ = (x * logicalZ n) * y := by rw [← NQubitPauliGroupElement.mul_assoc]
      _ = (logicalZ n * x) * y := by rw [hx]
      _ = logicalZ n * (x * y) := by rw [NQubitPauliGroupElement.mul_assoc]
  · have H : (x⁻¹ * logicalZ n) * x = (logicalZ n * x⁻¹) * x := by
      rw [NQubitPauliGroupElement.mul_assoc, ← h, inv_mul_cancel_left,
        NQubitPauliGroupElement.mul_assoc, inv_mul_cancel, NQubitPauliGroupElement.mul_one]
    exact mul_right_cancel H

/-!
## StabilizerCode [[n+2, 1]] for odd n

The repetition code encodes one logical qubit. Logical X̄ = X on all qubits and Z̄ = Z on all
qubits; they anticommute only when the number of physical qubits `n+2` is odd, so the code
is defined only for odd `n` (i.e. `Odd (n + 2)`).
-/

/-- The parametric repetition code as a stabilizer code [[n+2, 1]] when `n+2` is odd. -/
noncomputable def stabilizerCode (n : ℕ) (hn : Odd (n + 2)) :
    StabilizerCode (n + 2) 1 where
  hk := Nat.succ_le_succ (Nat.zero_le (n + 1))
  toStabilizerGroup := stabilizerGroup n
  generatorsList := generatorsList n
  subgroup_eq_closure := by
    rw [listToSet_generatorsList]
    simp only [stabilizerGroup, subgroup, generators, XGenerators, Set.union_empty]
  generators_length := by rw [generatorsList_length]; omega
  generators_phaseZero := AllPhaseZero_generatorsList n
  generators_independent := GeneratorsIndependent_generatorsList n
  logicalX := fun _ => logicalX n
  logicalZ := fun _ => logicalZ n
  logicalX_mem_centralizer := fun _ => logicalX_mem_centralizer n
  logicalZ_mem_centralizer := fun _ => logicalZ_mem_centralizer n
  logicalX_anticommute_logicalZ := fun _ => logicalX_anticommutes_logicalZ n hn
  logical_commute_cross := fun ℓ ℓ' h => (h (Subsingleton.elim ℓ ℓ')).elim

end RepetitionCodeN
end StabilizerGroup

end Quantum
