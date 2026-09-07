import Mathlib.Tactic
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerGroup
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerCode
import QEC.Stabilizer.Framework.Core.Stabilizer.SubgroupLemmas
import QEC.Stabilizer.Framework.Core.CSS.CSSPredicates
import QEC.Stabilizer.Framework.Core.CSS.CSSNoNegI
import QEC.Stabilizer.Framework.Core.CSS.CSSCommutationLemmas
import QEC.Stabilizer.Framework.Core.CSS.CSSDistance
import QEC.Stabilizer.Framework.Core.Stabilizer.Centralizer
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance
import QEC.Stabilizer.Framework.Core.Logical.LogicalOperators
import QEC.Stabilizer.Foundations.PauliGroup.Commutation
import QEC.Stabilizer.Foundations.PauliGroup.CommutationTactics
import QEC.Stabilizer.Foundations.PauliGroup.NQubitOperator
import QEC.Stabilizer.Foundations.PauliGroup.NQubitElement
import QEC.Stabilizer.Foundations.BinarySymplectic.Core
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrix
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrixDecidable
import QEC.Stabilizer.Foundations.BinarySymplectic.SymplecticInner
import QEC.Stabilizer.Framework.Symplectic.IndependentEquiv

namespace Quantum
open scoped BigOperators

namespace StabilizerGroup
namespace Iceberg

/-!
# The iceberg / generalized parity code family `[[2m, 2m−2, 2]]`

A parametric, self-complementary, self-dual CSS detection code on `n = 2m`
physical qubits with `k = 2m − 2` logical qubits and distance `d = 2`.
Originally analyzed in [Steane 1996, `arxiv:quant-ph/9605021`] and
[Gottesman 1997, `arxiv:quant-ph/9702029`]; see also EC Zoo:
`https://errorcorrectionzoo.org/c/iceberg`.

## Parameters

- Physical qubits: `n = 2m`
- Logical qubits: `k = 2m − 2`
- Distance: `d = 2`
- Family: CSS, self-dual (X- and Z-stabilizers share the same full
  support).
- Parameter constraint: `[Fact (2 ≤ m)]` (`m = 1` would give a trivial
  `[[2, 0, 2]]` code with zero logical qubits, which we exclude).

## Stabilizer generators

Exactly two generators, `n − k = 2`:

```
S_Z := Z Z Z ... Z   (Z on all 2m qubits)
S_X := X X X ... X   (X on all 2m qubits)
```

They commute because the symplectic inner product `⟨S_X, S_Z⟩ = 2m mod 2 = 0`
when `n = 2m` is even (this is the **defining property** of the iceberg
family: the all-X / all-Z stabilizers commute precisely when `n` is even,
which is why the iceberg is a `[[2m, *, *]]` rather than `[[2m+1, *, *]]`
family — the odd-n version gives the Shor / Steane / repetition codes).

## Logical operators (split-anchor convention)

For each logical qubit `i : Fin (2m − 2)`:

- Qubit `i.val` (= 0, 1, …, 2m − 3) is the "individual" position
- Qubit `2m − 1` is the global "X-anchor" (in every `X̄_i`)
- Qubit `2m − 2` is the global "Z-anchor" (in every `Z̄_i`)

```
X̄_i := X at qubits {i.val, 2m − 1}     (weight 2)
Z̄_i := Z at qubits {i.val, 2m − 2}     (weight 2)
```

This convention makes the (anti)commutation table clean:

- `X̄_i Z̄_i`: anticomm at qubit `i.val` only (count 1, odd) ⇒ anticommute
- `X̄_i Z̄_j` for `i ≠ j`: disjoint supports ⇒ commute
- `X̄_i S_Z`: anticomm at `{i.val, 2m-1}` (count 2, even) ⇒ commute
- `Z̄_i S_X`: anticomm at `{i.val, 2m-2}` (count 2, even) ⇒ commute

## Relation to `Codes/Small/FourQubit_4_2_2.lean`

This parametric family at `m = 2` is the **same code** as the existing
`FourQubit_4_2_2.lean`, but uses a **different** logical-operator basis
(see `qec-lab:pipeline/attempts/iceberg/informal_spec.md` § "Relation to
FourQubit_4_2_2.lean"). Both formalizations coexist as separate Lean
objects, mirroring the `RepetitionCode3.lean` / `RepetitionCodeN.lean`
pattern: we do NOT prove equivalence between the two.

## File status

**Stage-2 skeleton.** Every theorem ends in a `sorry` tagged
`TODO(iceberg-T<n>): <one-line hint>`. Stage 4 closes them following the
`FourQubit_4_2_2.lean` template, scaled up for parametric `m` and
generalized for k = 2m − 2 logical qubits.
-/

open NQubitPauliGroupElement
open scoped Pauli

/-! ## Local convenience -/

/-- Lift a logical-qubit index `Fin (2m − 2)` into the physical-qubit index
`Fin (2m)`. The `[Fact (2 ≤ m)]` instance discharges the bound proof
`i.val < 2m` via `omega`. -/
@[inline] private def logIdx {m : ℕ} [Fact (2 ≤ m)] (i : Fin (2 * m - 2)) :
    Fin (2 * m) :=
  ⟨i.val, by
    have h : 2 ≤ m := Fact.out
    have hi : i.val < 2 * m - 2 := i.isLt
    omega⟩

/-- Z-anchor qubit (always part of every `Z̄_i`): qubit `2m − 2`. -/
@[inline] private def zAnchor (m : ℕ) [Fact (2 ≤ m)] : Fin (2 * m) :=
  ⟨2 * m - 2, by have h : 2 ≤ m := Fact.out; omega⟩

/-- X-anchor qubit (always part of every `X̄_i`): qubit `2m − 1`. -/
@[inline] private def xAnchor (m : ℕ) [Fact (2 ≤ m)] : Fin (2 * m) :=
  ⟨2 * m - 1, by have h : 2 ≤ m := Fact.out; omega⟩

/-! ## §1 — Generators -/

/-- The Z-type stabilizer generator: `Z Z Z … Z` on all `2m` qubits. -/
def S_Z (m : ℕ) [Fact (2 ≤ m)] : NQubitPauliGroupElement (2 * m) :=
  ⟨0, NQubitPauliOperator.Z (2 * m)⟩

/-- The X-type stabilizer generator: `X X X … X` on all `2m` qubits. -/
def S_X (m : ℕ) [Fact (2 ≤ m)] : NQubitPauliGroupElement (2 * m) :=
  ⟨0, NQubitPauliOperator.X (2 * m)⟩

/-! ## §2 — Generator sets and subgroup -/

/-- The single Z-check generator. -/
def ZGenerators (m : ℕ) [Fact (2 ≤ m)] : Set (NQubitPauliGroupElement (2 * m)) :=
  {S_Z m}

/-- The single X-check generator. -/
def XGenerators (m : ℕ) [Fact (2 ≤ m)] : Set (NQubitPauliGroupElement (2 * m)) :=
  {S_X m}

/-- The full generator set: one Z-check and one X-check. -/
def generators (m : ℕ) [Fact (2 ≤ m)] : Set (NQubitPauliGroupElement (2 * m)) :=
  ZGenerators m ∪ XGenerators m

/-- The iceberg stabilizer subgroup: closure of `{ZZ…Z, XX…X}`. -/
noncomputable def subgroup (m : ℕ) [Fact (2 ≤ m)] :
    Subgroup (NQubitPauliGroupElement (2 * m)) :=
  Subgroup.closure (generators m)

/-! ## §3 — Z-type / X-type predicates -/

/-- T1: the Z-generator `S_Z m` is Z-type (Z on every qubit, hence I-or-Z
on every qubit trivially). -/
lemma ZGenerators_are_ZType (m : ℕ) [Fact (2 ≤ m)] :
    ∀ g, g ∈ ZGenerators m → NQubitPauliGroupElement.IsZTypeElement g := by
  classical
  intro g hg
  rcases (by simpa [ZGenerators] using hg) with rfl
  refine ⟨rfl, ?_⟩
  intro i
  exact Or.inr (by simp [S_Z, NQubitPauliOperator.Z])

/-- T2: the X-generator `S_X m` is X-type. -/
lemma XGenerators_are_XType (m : ℕ) [Fact (2 ≤ m)] :
    ∀ g, g ∈ XGenerators m → NQubitPauliGroupElement.IsXTypeElement g := by
  classical
  intro g hg
  rcases (by simpa [XGenerators] using hg) with rfl
  refine ⟨rfl, ?_⟩
  intro i
  exact Or.inr (by simp [S_X, NQubitPauliOperator.X])

/-! ## §4 — Cross-commutation (the iceberg-defining property)

`S_Z m` and `S_X m` anticommute at every one of the `2m` qubits — count
`2m`, even (since `2m = 2 * m`), so they **commute**. This is why the
iceberg family lives on an even number of physical qubits.
-/

private lemma S_Z_comm_S_X (m : ℕ) [Fact (2 ≤ m)] :
    S_Z m * S_X m = S_X m * S_Z m := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
        (NQubitPauliGroupElement.anticommutesAt (n := 2 * m)
          (S_Z m).operators (S_X m).operators)) =
        (Finset.univ : Finset (Fin (2 * m))) := by
    ext i
    simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt,
      S_Z, S_X, NQubitPauliOperator.Z, NQubitPauliOperator.X, PauliOperator.mulOp]
  rw [hfilter, Finset.card_univ, Fintype.card_fin]
  exact ⟨m, by ring⟩

/-- T3 packaged: every Z-generator commutes with every X-generator. -/
lemma ZGenerators_commute_XGenerators (m : ℕ) [Fact (2 ≤ m)] :
    ∀ z ∈ ZGenerators m, ∀ x ∈ XGenerators m, z * x = x * z := by
  classical
  intro z hz x hx
  rcases (by simpa [ZGenerators] using hz) with rfl
  rcases (by simpa [XGenerators] using hx) with rfl
  exact S_Z_comm_S_X m

/-! ## §5 — All-pair commutation -/

private lemma ZType_commutes {m : ℕ} {g h : NQubitPauliGroupElement (2 * m)}
    (hg : NQubitPauliGroupElement.IsZTypeElement g)
    (hh : NQubitPauliGroupElement.IsZTypeElement h) :
    g * h = h * g :=
  CSSCommutationLemmas.ZType_commutes hg hh

private lemma XType_commutes {m : ℕ} {g h : NQubitPauliGroupElement (2 * m)}
    (hg : NQubitPauliGroupElement.IsXTypeElement g)
    (hh : NQubitPauliGroupElement.IsXTypeElement h) :
    g * h = h * g :=
  CSSCommutationLemmas.XType_commutes hg hh

/-- T4: all generators pairwise commute. -/
theorem generators_commute (m : ℕ) [Fact (2 ≤ m)] :
    ∀ g ∈ generators m, ∀ h ∈ generators m, g * h = h * g := by
  classical
  intro g hg h hh
  have hg' : g ∈ ZGenerators m ∨ g ∈ XGenerators m := by simpa [generators] using hg
  have hh' : h ∈ ZGenerators m ∨ h ∈ XGenerators m := by simpa [generators] using hh
  rcases hg' with hgZ | hgX <;> rcases hh' with hhZ | hhX
  · exact ZType_commutes (ZGenerators_are_ZType m g hgZ) (ZGenerators_are_ZType m h hhZ)
  · exact ZGenerators_commute_XGenerators m g hgZ h hhX
  · simpa using (ZGenerators_commute_XGenerators m h hhZ g hgX).symm
  · exact XType_commutes (XGenerators_are_XType m g hgX) (XGenerators_are_XType m h hhX)

/-! ## §6 — `−I` is not in the stabilizer subgroup -/

/-- T5: `−I` is not in the iceberg stabilizer subgroup (CSS argument with
T1, T2, T3 + `CSS.negIdentity_not_mem_closure_union`). -/
theorem negIdentity_not_mem (m : ℕ) [Fact (2 ≤ m)] :
    negIdentity (2 * m) ∉ subgroup m := by
  have hZX : ∀ z ∈ ZGenerators m, ∀ x ∈ XGenerators m, z * x = x * z :=
    ZGenerators_commute_XGenerators m
  simpa [subgroup, generators] using
    (CSS.negIdentity_not_mem_closure_union (n := 2 * m) (ZGenerators m) (XGenerators m)
      (ZGenerators_are_ZType m) (XGenerators_are_XType m) hZX)

/-! ## §7 — Generator list and `listToSet` equality -/

/-- The generator list, canonical order Z then X. Length = 2 = n − k. -/
def generatorsList (m : ℕ) [Fact (2 ≤ m)] :
    List (NQubitPauliGroupElement (2 * m)) :=
  [S_Z m, S_X m]

/-- T6: the generator list and the generator set agree. -/
lemma listToSet_generatorsList (m : ℕ) [Fact (2 ≤ m)] :
    NQubitPauliGroupElement.listToSet (generatorsList m) = generators m := by
  simp only [generatorsList, generators, ZGenerators, XGenerators,
    NQubitPauliGroupElement.listToSet_cons, NQubitPauliGroupElement.listToSet_nil]
  ext g
  simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff, Set.mem_empty_iff_false,
    or_false]

/-- T7: all generators have phase 0. -/
lemma AllPhaseZero_generatorsList (m : ℕ) [Fact (2 ≤ m)] :
    NQubitPauliGroupElement.AllPhaseZero (generatorsList m) := by
  rw [generatorsList, NQubitPauliGroupElement.AllPhaseZero_cons]
  exact ⟨rfl, (NQubitPauliGroupElement.AllPhaseZero_cons _ _).mpr
    ⟨rfl, NQubitPauliGroupElement.AllPhaseZero_nil⟩⟩

/-! ## §9 — Generator independence (linear independence of check-matrix rows)

The check matrix of `[S_Z m, S_X m]` has 2 rows × 4m columns. Row 0 has
all-zeros on the X-half and all-ones on the Z-half; row 1 is its mirror.
Both nonzero, neither a `ZMod 2`-multiple of the other (the only nonzero
multiple is itself; sum of the two has all-ones everywhere, also nonzero).
-/

/-- T8: the check-matrix rows of `[S_Z m, S_X m]` are linearly independent. -/
theorem rowsLinearIndependent_generatorsList (m : ℕ) [Fact (2 ≤ m)] :
    NQubitPauliGroupElement.rowsLinearIndependent (generatorsList m) := by
  classical
  have hm : 2 ≤ m := Fact.out
  have h2m_pos : 0 < 2 * m := by omega
  have hlen : (generatorsList m).length = 2 := by simp [generatorsList]
  rw [NQubitPauliGroupElement.rowsLinearIndependent_iff_forall]
  intro f hf
  -- Length-2 row indices.
  have h0lt : 0 < (generatorsList m).length := by simp [generatorsList]
  have h1lt : 1 < (generatorsList m).length := by simp [generatorsList]
  set i0 : Fin (generatorsList m).length := ⟨0, h0lt⟩ with hi0_def
  set i1 : Fin (generatorsList m).length := ⟨1, h1lt⟩ with hi1_def
  have hi01 : i0 ≠ i1 := by simp [hi0_def, hi1_def, Fin.ext_iff]
  let q0 : Fin (2 * m) := ⟨0, h2m_pos⟩
  -- Z-column values.
  have hZ_i0 : NQubitPauliGroupElement.checkMatrix (generatorsList m) i0
      (Fin.natAdd (2 * m) q0) = 1 := by
    simp only [NQubitPauliGroupElement.checkMatrix, generatorsList, List.get, hi0_def, S_Z]
    rw [NQubitPauliOperator.toSymplectic_Z_part]
    simp [NQubitPauliOperator.Z]
  have hZ_i1 : NQubitPauliGroupElement.checkMatrix (generatorsList m) i1
      (Fin.natAdd (2 * m) q0) = 0 := by
    simp only [NQubitPauliGroupElement.checkMatrix, generatorsList, List.get, hi1_def, S_X]
    rw [NQubitPauliOperator.toSymplectic_Z_part]
    simp [NQubitPauliOperator.X]
  -- X-column values.
  have hX_i0 : NQubitPauliGroupElement.checkMatrix (generatorsList m) i0
      (Fin.castAdd (2 * m) q0) = 0 := by
    simp only [NQubitPauliGroupElement.checkMatrix, generatorsList, List.get, hi0_def, S_Z]
    rw [NQubitPauliOperator.toSymplectic_X_part]
    simp [NQubitPauliOperator.Z]
  have hX_i1 : NQubitPauliGroupElement.checkMatrix (generatorsList m) i1
      (Fin.castAdd (2 * m) q0) = 1 := by
    simp only [NQubitPauliGroupElement.checkMatrix, generatorsList, List.get, hi1_def, S_X]
    rw [NQubitPauliOperator.toSymplectic_X_part]
    simp [NQubitPauliOperator.X]
  -- Evaluate hf at the two columns. The sum over Fin 2 splits as i0 + i1.
  have hsum_Z := congrArg (fun (φ : Fin (2 * m + 2 * m) → ZMod 2) =>
    φ (Fin.natAdd (2 * m) q0)) hf
  have hsum_X := congrArg (fun (φ : Fin (2 * m + 2 * m) → ZMod 2) =>
    φ (Fin.castAdd (2 * m) q0)) hf
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hsum_Z hsum_X
  -- The Fin 2 sum is i0 + i1 (since these are the only two elements).
  have hfi_iff : ∀ (g : Fin (generatorsList m).length → ZMod 2),
      ∑ i, g i = g i0 + g i1 := by
    intro g
    rw [show (Finset.univ : Finset (Fin (generatorsList m).length)) = {i0, i1} by
      ext k
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      have hkval : k.val < 2 := by have := k.2; omega
      rcases Nat.lt_or_ge k.val 1 with h | h
      · left
        apply Fin.ext
        show k.val = i0.val
        simp [hi0_def]; omega
      · right
        apply Fin.ext
        show k.val = i1.val
        simp [hi1_def]; omega]
    rw [Finset.sum_pair hi01]
  rw [hfi_iff (fun i => f i * NQubitPauliGroupElement.checkMatrix (generatorsList m) i
    (Fin.natAdd (2 * m) q0))] at hsum_Z
  rw [hfi_iff (fun i => f i * NQubitPauliGroupElement.checkMatrix (generatorsList m) i
    (Fin.castAdd (2 * m) q0))] at hsum_X
  rw [hZ_i0, hZ_i1] at hsum_Z
  rw [hX_i0, hX_i1] at hsum_X
  have hf0 : f i0 = 0 := by simpa using hsum_Z
  have hf1 : f i1 = 0 := by simpa using hsum_X
  -- Conclude f = 0.
  funext i
  have hival : i.val < 2 := by have := i.2; omega
  interval_cases hi : i.val
  · have : i = i0 := by apply Fin.ext; show i.val = i0.val; simp [hi0_def, hi]
    rw [this]; exact hf0
  · have : i = i1 := by apply Fin.ext; show i.val = i1.val; simp [hi1_def, hi]
    rw [this]; exact hf1

theorem GeneratorsIndependent_generatorsList (m : ℕ) [Fact (2 ≤ m)] :
    GeneratorsIndependent (2 * m) (generatorsList m) :=
  GeneratorsIndependent_of_rowsLinearIndependent (2 * m) (generatorsList m)
    (rowsLinearIndependent_generatorsList m)

/-! ## §8 — Bundled `StabilizerGroup (2 * m)` -/

/-- T9: the iceberg stabilizer group, from the generator list. -/
noncomputable def stabilizerGroup (m : ℕ) [Fact (2 ≤ m)] :
    StabilizerGroup (2 * m) :=
  mkStabilizerFromGenerators (2 * m) (generatorsList m)
    (by rw [listToSet_generatorsList]; exact generators_commute m)
    (by rw [listToSet_generatorsList]; exact negIdentity_not_mem m)

/-- T10: the bundled stabilizer group's subgroup equals the set-form closure. -/
lemma stabilizerGroup_toSubgroup_eq (m : ℕ) [Fact (2 ≤ m)] :
    (stabilizerGroup m).toSubgroup = subgroup m := by
  simp only [stabilizerGroup, mkStabilizerFromGenerators, subgroup]
  rw [listToSet_generatorsList]

/-! ## §10 — Logical operators

For each `i : Fin (2m − 2)`:
- `logicalX m i`: X at qubits `logIdx i` and `xAnchor m`
- `logicalZ m i`: Z at qubits `logIdx i` and `zAnchor m`
-/

/-- Logical X for logical qubit `i`: X on qubits `i` and `2m − 1`. -/
def logicalX (m : ℕ) [Fact (2 ≤ m)] (i : Fin (2 * m - 2)) :
    NQubitPauliGroupElement (2 * m) :=
  σ[2 * m | logIdx i ↦ X, xAnchor m ↦ X]

/-- Logical Z for logical qubit `i`: Z on qubits `i` and `2m − 2`. -/
def logicalZ (m : ℕ) [Fact (2 ≤ m)] (i : Fin (2 * m - 2)) :
    NQubitPauliGroupElement (2 * m) :=
  σ[2 * m | logIdx i ↦ Z, zAnchor m ↦ Z]

/-! ## §11 — Logical (anti)commutation -/

/-- Internal helper: the three anchor positions are pairwise distinct. -/
private lemma logIdx_ne_xAnchor (m : ℕ) [Fact (2 ≤ m)] (i : Fin (2 * m - 2)) :
    logIdx i ≠ xAnchor m := by
  have h : 2 ≤ m := Fact.out
  intro heq
  have := congrArg Fin.val heq
  simp [logIdx, xAnchor] at this
  omega

private lemma logIdx_ne_zAnchor (m : ℕ) [Fact (2 ≤ m)] (i : Fin (2 * m - 2)) :
    logIdx i ≠ zAnchor m := by
  have h : 2 ≤ m := Fact.out
  intro heq
  have := congrArg Fin.val heq
  simp [logIdx, zAnchor] at this
  omega

private lemma xAnchor_ne_zAnchor (m : ℕ) [Fact (2 ≤ m)] :
    xAnchor m ≠ zAnchor m := by
  have h : 2 ≤ m := Fact.out
  intro heq
  have := congrArg Fin.val heq
  simp [xAnchor, zAnchor] at this
  omega

/-- T11: diagonal anticommutation `X̄_i Z̄_i = − Z̄_i X̄_i`. -/
theorem logicalX_anticommutes_logicalZ_diag (m : ℕ) [Fact (2 ≤ m)]
    (i : Fin (2 * m - 2)) :
    NQubitPauliGroupElement.Anticommute (logicalX m i) (logicalZ m i) := by
  classical
  pauli_anticomm_odd_anticommutes
  have hxa : logIdx i ≠ xAnchor m := logIdx_ne_xAnchor m i
  have hza : logIdx i ≠ zAnchor m := logIdx_ne_zAnchor m i
  have hax : xAnchor m ≠ zAnchor m := xAnchor_ne_zAnchor m
  have hfilter :
      (Finset.univ.filter
        (NQubitPauliGroupElement.anticommutesAt (n := 2 * m)
          (logicalX m i).operators (logicalZ m i).operators)) =
        ({logIdx i} : Finset (Fin (2 * m))) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      NQubitPauliGroupElement.anticommutesAt, logicalX, logicalZ,
      NQubitPauliOperator.set, NQubitPauliOperator.identity]
    by_cases hj1 : j = logIdx i
    · subst hj1
      simp [PauliOperator.mulOp]
    · by_cases hj2 : j = xAnchor m
      · subst hj2
        simp [hax, PauliOperator.mulOp,
          (show (xAnchor m : Fin (2 * m)) ≠ logIdx i from fun h => hxa h.symm)]
      · by_cases hj3 : j = zAnchor m
        · subst hj3
          simp [PauliOperator.mulOp,
            (show (zAnchor m : Fin (2 * m)) ≠ logIdx i from fun h => hza h.symm),
            (show (zAnchor m : Fin (2 * m)) ≠ xAnchor m from fun h => hax h.symm)]
        · simp [hj1, hj2, hj3, PauliOperator.mulOp]
  rw [hfilter, Finset.card_singleton]
  decide

/-- T12a: X̄_i and X̄_j always commute (both X-type). -/
theorem logicalX_commutes_logicalX (m : ℕ) [Fact (2 ≤ m)]
    (i j : Fin (2 * m - 2)) :
    logicalX m i * logicalX m j = logicalX m j * logicalX m i := by
  apply NQubitPauliGroupElement.commutes_of_componentwise_commutes
  intro k
  -- At every qubit, both operators are I or X. I·X = X·I, X·X = X·X.
  simp only [logicalX, NQubitPauliOperator.set, NQubitPauliOperator.identity]
  split_ifs <;> simp [PauliOperator.mulOp]

/-- T12b: Z̄_i and Z̄_j always commute (both Z-type). -/
theorem logicalZ_commutes_logicalZ (m : ℕ) [Fact (2 ≤ m)]
    (i j : Fin (2 * m - 2)) :
    logicalZ m i * logicalZ m j = logicalZ m j * logicalZ m i := by
  apply NQubitPauliGroupElement.commutes_of_componentwise_commutes
  intro k
  simp only [logicalZ, NQubitPauliOperator.set, NQubitPauliOperator.identity]
  split_ifs <;> simp [PauliOperator.mulOp]

/-- T12c: X̄_i and Z̄_j commute when i ≠ j (disjoint supports). -/
theorem logicalX_commutes_logicalZ_offdiag (m : ℕ) [Fact (2 ≤ m)]
    {i j : Fin (2 * m - 2)} (hij : i ≠ j) :
    logicalX m i * logicalZ m j = logicalZ m j * logicalX m i := by
  apply NQubitPauliGroupElement.commutes_of_componentwise_commutes
  intro k
  -- At every qubit, only one of {X̄ at logIdx i / xAnchor} or {Z̄ at logIdx j / zAnchor}
  -- can be non-I (since their supports are disjoint when i ≠ j).
  have hij_idx : logIdx i ≠ logIdx j := by
    intro heq
    apply hij
    have := congrArg Fin.val heq
    simp only [logIdx] at this
    exact Fin.ext this
  have hxa_i : logIdx i ≠ xAnchor m := logIdx_ne_xAnchor m i
  have hxa_j : logIdx j ≠ xAnchor m := logIdx_ne_xAnchor m j
  have hza_i : logIdx i ≠ zAnchor m := logIdx_ne_zAnchor m i
  have hza_j : logIdx j ≠ zAnchor m := logIdx_ne_zAnchor m j
  have hax : xAnchor m ≠ zAnchor m := xAnchor_ne_zAnchor m
  simp only [logicalX, logicalZ, NQubitPauliOperator.set, NQubitPauliOperator.identity]
  split_ifs <;> simp_all [PauliOperator.mulOp]

/-! ## §12 — Logicals in the centralizer

Per-generator commutation lemmas — used by T13 and T14 below.
-/

private lemma logicalX_commutes_S_Z (m : ℕ) [Fact (2 ≤ m)]
    (i : Fin (2 * m - 2)) :
    logicalX m i * S_Z m = S_Z m * logicalX m i := by
  classical
  pauli_comm_even_anticommutes
  have hxa : logIdx i ≠ xAnchor m := logIdx_ne_xAnchor m i
  have hfilter :
      (Finset.univ.filter
        (NQubitPauliGroupElement.anticommutesAt (n := 2 * m)
          (logicalX m i).operators (S_Z m).operators)) =
        ({logIdx i, xAnchor m} : Finset (Fin (2 * m))) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton,
      NQubitPauliGroupElement.anticommutesAt, logicalX, S_Z,
      NQubitPauliOperator.set, NQubitPauliOperator.identity, NQubitPauliOperator.Z]
    by_cases hj1 : k = logIdx i
    · subst hj1
      simp [PauliOperator.mulOp]
    · by_cases hj2 : k = xAnchor m
      · subst hj2
        simp [PauliOperator.mulOp,
          (show (xAnchor m : Fin (2 * m)) ≠ logIdx i from fun h => hxa h.symm)]
      · simp [hj1, hj2, PauliOperator.mulOp]
  rw [hfilter]
  rw [Finset.card_insert_of_notMem (by simp [hxa]), Finset.card_singleton]
  exact even_two

private lemma logicalX_commutes_S_X (m : ℕ) [Fact (2 ≤ m)]
    (i : Fin (2 * m - 2)) :
    logicalX m i * S_X m = S_X m * logicalX m i := by
  apply NQubitPauliGroupElement.commutes_of_componentwise_commutes
  intro k
  simp only [logicalX, S_X, NQubitPauliOperator.set, NQubitPauliOperator.identity,
    NQubitPauliOperator.X]
  split_ifs <;> simp [PauliOperator.mulOp]

private lemma logicalZ_commutes_S_Z (m : ℕ) [Fact (2 ≤ m)]
    (i : Fin (2 * m - 2)) :
    logicalZ m i * S_Z m = S_Z m * logicalZ m i := by
  apply NQubitPauliGroupElement.commutes_of_componentwise_commutes
  intro k
  simp only [logicalZ, S_Z, NQubitPauliOperator.set, NQubitPauliOperator.identity,
    NQubitPauliOperator.Z]
  split_ifs <;> simp [PauliOperator.mulOp]

private lemma logicalZ_commutes_S_X (m : ℕ) [Fact (2 ≤ m)]
    (i : Fin (2 * m - 2)) :
    logicalZ m i * S_X m = S_X m * logicalZ m i := by
  classical
  pauli_comm_even_anticommutes
  have hza : logIdx i ≠ zAnchor m := logIdx_ne_zAnchor m i
  have hfilter :
      (Finset.univ.filter
        (NQubitPauliGroupElement.anticommutesAt (n := 2 * m)
          (logicalZ m i).operators (S_X m).operators)) =
        ({logIdx i, zAnchor m} : Finset (Fin (2 * m))) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton,
      NQubitPauliGroupElement.anticommutesAt, logicalZ, S_X,
      NQubitPauliOperator.set, NQubitPauliOperator.identity, NQubitPauliOperator.X]
    by_cases hj1 : k = logIdx i
    · subst hj1
      simp [PauliOperator.mulOp]
    · by_cases hj2 : k = zAnchor m
      · subst hj2
        simp [PauliOperator.mulOp,
          (show (zAnchor m : Fin (2 * m)) ≠ logIdx i from fun h => hza h.symm)]
      · simp [hj1, hj2, PauliOperator.mulOp]
  rw [hfilter]
  rw [Finset.card_insert_of_notMem (by simp [hza]), Finset.card_singleton]
  exact even_two

/-- T13: every `logicalX m i` is in the centralizer of the stabilizer. -/
theorem logicalX_mem_centralizer (m : ℕ) [Fact (2 ≤ m)]
    (i : Fin (2 * m - 2)) :
    logicalX m i ∈ centralizer (stabilizerGroup m) := by
  rw [StabilizerGroup.mem_centralizer_iff, stabilizerGroup_toSubgroup_eq, subgroup]
  rw [Subgroup.forall_comm_closure_iff]
  intro s hs
  simp only [generators, Set.mem_union] at hs
  rcases hs with hgZ | hgX
  · rcases (by simpa [ZGenerators] using hgZ) with rfl
    exact (logicalX_commutes_S_Z m i).symm
  · rcases (by simpa [XGenerators] using hgX) with rfl
    exact (logicalX_commutes_S_X m i).symm

/-- T14: every `logicalZ m i` is in the centralizer of the stabilizer. -/
theorem logicalZ_mem_centralizer (m : ℕ) [Fact (2 ≤ m)]
    (i : Fin (2 * m - 2)) :
    logicalZ m i ∈ centralizer (stabilizerGroup m) := by
  rw [StabilizerGroup.mem_centralizer_iff, stabilizerGroup_toSubgroup_eq, subgroup]
  rw [Subgroup.forall_comm_closure_iff]
  intro s hs
  simp only [generators, Set.mem_union] at hs
  rcases hs with hgZ | hgX
  · rcases (by simpa [ZGenerators] using hgZ) with rfl
    exact (logicalZ_commutes_S_Z m i).symm
  · rcases (by simpa [XGenerators] using hgX) with rfl
    exact (logicalZ_commutes_S_X m i).symm

/-! ## §13 — `StabilizerCode (2 * m) (2 * m - 2)` packaging -/

/-- The `(2m - 2)`-many-logical-qubit data for the iceberg code. -/
private def logicalOpsIceberg (m : ℕ) [Fact (2 ≤ m)] :
    Fin (2 * m - 2) → LogicalQubitOps (2 * m) (stabilizerGroup m) :=
  fun i => ⟨logicalX m i, logicalZ m i,
    logicalX_mem_centralizer m i, logicalZ_mem_centralizer m i,
    logicalX_anticommutes_logicalZ_diag m i⟩

/-- T15: the iceberg code as a stabilizer code `[[2m, 2m-2]]`. -/
noncomputable def stabilizerCode (m : ℕ) [Fact (2 ≤ m)] :
    StabilizerCode (2 * m) (2 * m - 2) where
  hk := by have h : 2 ≤ m := Fact.out; omega
  generatorsList := generatorsList m
  generators_length := by
    -- |[S_Z, S_X]| = 2 = 2m - (2m - 2)
    have h : 2 ≤ m := Fact.out
    simp [generatorsList]
    omega
  generators_phaseZero := AllPhaseZero_generatorsList m
  generators_independent := GeneratorsIndependent_generatorsList m
  generators_commute := by
    rw [listToSet_generatorsList]; exact generators_commute m
  closure_no_neg_identity := by
    rw [listToSet_generatorsList]; exact negIdentity_not_mem m
  logicalOps := logicalOpsIceberg m
  logical_commute_cross := by
    intro ℓ ℓ' hne
    refine ⟨logicalX_commutes_logicalX m ℓ ℓ', ?_, ?_, logicalZ_commutes_logicalZ m ℓ ℓ'⟩
    · exact logicalX_commutes_logicalZ_offdiag m hne
    · exact (logicalX_commutes_logicalZ_offdiag m (Ne.symm hne)).symm

/-! ## §14 — Code distance = 2 -/

/-- T16: bridge between `stabilizerCode`'s and the set-form generators. -/
private lemma stabilizerCode_toSubgroup_eq (m : ℕ) [Fact (2 ≤ m)] :
    (stabilizerCode m).toStabilizerGroup.toSubgroup =
      Subgroup.closure (generators m) := by
  change (Subgroup.closure (NQubitPauliGroupElement.listToSet (generatorsList m)) : _) =
    Subgroup.closure (generators m)
  rw [listToSet_generatorsList]

/-- Weight-1 X-anchored Pauli at qubit `i` anticommutes with `S_Z m` (all-Z).
The anticomm filter is exactly `{i}`, cardinality 1, odd. -/
private lemma weightOneAt_X_anticomm_S_Z (m : ℕ) [Fact (2 ≤ m)] (i : Fin (2 * m)) :
    NQubitPauliGroupElement.Anticommute (weightOneAt i PauliOperator.X) (S_Z m) := by
  classical
  pauli_anticomm_odd_anticommutes
  have hfilter :
      (Finset.univ.filter
        (NQubitPauliGroupElement.anticommutesAt (n := 2 * m)
          (weightOneAt i PauliOperator.X).operators (S_Z m).operators)) =
        ({i} : Finset (Fin (2 * m))) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      NQubitPauliGroupElement.anticommutesAt, weightOneAt,
      NQubitPauliGroupElement.ofOperator_operators, S_Z, NQubitPauliOperator.Z]
    by_cases hk : k = i
    · subst hk; simp [PauliOperator.mulOp]
    · simp [hk, PauliOperator.mulOp]
  rw [hfilter, Finset.card_singleton]
  decide

/-- Weight-1 Y-anchored Pauli at qubit `i` anticommutes with `S_Z m`. -/
private lemma weightOneAt_Y_anticomm_S_Z (m : ℕ) [Fact (2 ≤ m)] (i : Fin (2 * m)) :
    NQubitPauliGroupElement.Anticommute (weightOneAt i PauliOperator.Y) (S_Z m) := by
  classical
  pauli_anticomm_odd_anticommutes
  have hfilter :
      (Finset.univ.filter
        (NQubitPauliGroupElement.anticommutesAt (n := 2 * m)
          (weightOneAt i PauliOperator.Y).operators (S_Z m).operators)) =
        ({i} : Finset (Fin (2 * m))) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      NQubitPauliGroupElement.anticommutesAt, weightOneAt,
      NQubitPauliGroupElement.ofOperator_operators, S_Z, NQubitPauliOperator.Z]
    by_cases hk : k = i
    · subst hk; simp [PauliOperator.mulOp]
    · simp [hk, PauliOperator.mulOp]
  rw [hfilter, Finset.card_singleton]
  decide

/-- Weight-1 Z-anchored Pauli at qubit `i` anticommutes with `S_X m` (all-X). -/
private lemma weightOneAt_Z_anticomm_S_X (m : ℕ) [Fact (2 ≤ m)] (i : Fin (2 * m)) :
    NQubitPauliGroupElement.Anticommute (weightOneAt i PauliOperator.Z) (S_X m) := by
  classical
  pauli_anticomm_odd_anticommutes
  have hfilter :
      (Finset.univ.filter
        (NQubitPauliGroupElement.anticommutesAt (n := 2 * m)
          (weightOneAt i PauliOperator.Z).operators (S_X m).operators)) =
        ({i} : Finset (Fin (2 * m))) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      NQubitPauliGroupElement.anticommutesAt, weightOneAt,
      NQubitPauliGroupElement.ofOperator_operators, S_X, NQubitPauliOperator.X]
    by_cases hk : k = i
    · subst hk; simp [PauliOperator.mulOp]
    · simp [hk, PauliOperator.mulOp]
  rw [hfilter, Finset.card_singleton]
  decide

/-- T17: every weight-1 single-qubit Pauli anticommutes with one of the
two generators. Z-anchored Pauli at any qubit anticomms with `S_X m`;
X- or Y-anchored Pauli at any qubit anticomms with `S_Z m`. -/
private lemma weight_one_anticomm_witness (m : ℕ) [Fact (2 ≤ m)] :
    ∀ i : Fin (2 * m), ∀ P : PauliOperator, P ≠ PauliOperator.I →
      ∃ g ∈ generators m, NQubitPauliGroupElement.Anticommute
        (weightOneAt i P) g := by
  intro i P hP
  match P, hP with
  | PauliOperator.X, _ =>
    exact ⟨S_Z m, by simp [generators, ZGenerators], weightOneAt_X_anticomm_S_Z m i⟩
  | PauliOperator.Y, _ =>
    exact ⟨S_Z m, by simp [generators, ZGenerators], weightOneAt_Y_anticomm_S_Z m i⟩
  | PauliOperator.Z, _ =>
    exact ⟨S_X m, by simp [generators, XGenerators], weightOneAt_Z_anticomm_S_X m i⟩
  | PauliOperator.I, hP => exact (hP rfl).elim

/-- Weight of `logicalX m i` equals 2 (parametric — the support is exactly
`{logIdx i, xAnchor m}` and these are distinct). -/
private lemma weight_logicalX (m : ℕ) [Fact (2 ≤ m)] (i : Fin (2 * m - 2)) :
    NQubitPauliGroupElement.weight (logicalX m i) = 2 := by
  classical
  have hxa : logIdx i ≠ xAnchor m := logIdx_ne_xAnchor m i
  -- Compute the support: precisely {logIdx i, xAnchor m}.
  have hsupp : NQubitPauliOperator.support (logicalX m i).operators =
      ({logIdx i, xAnchor m} : Finset (Fin (2 * m))) := by
    ext k
    simp only [NQubitPauliOperator.mem_support, Finset.mem_insert, Finset.mem_singleton,
      logicalX, NQubitPauliOperator.set, NQubitPauliOperator.identity]
    by_cases hk1 : k = logIdx i
    · subst hk1; simp
    · by_cases hk2 : k = xAnchor m
      · subst hk2; simp
      · simp [hk1, hk2]
  -- The support has cardinality 2.
  change NQubitPauliOperator.weight (logicalX m i).operators = 2
  unfold NQubitPauliOperator.weight
  rw [hsupp]
  rw [Finset.card_insert_of_notMem (by simp [hxa]), Finset.card_singleton]

/-- T18: the iceberg `[[2m, 2m − 2, 2]]` code has distance exactly 2. -/
theorem code_has_distance_two (m : ℕ) [Fact (2 ≤ m)] :
    HasCodeDistance (stabilizerCode m) 2 := by
  have h2 : 2 ≤ m := Fact.out
  have h0lt : 0 < 2 * m - 2 := by omega
  refine hasCodeDistance_two_of_anticommute_witness (stabilizerCode m) (generators m)
    (stabilizerCode_toSubgroup_eq m) (weight_one_anticomm_witness m) ?_
  refine ⟨logicalX m ⟨0, h0lt⟩, ?_, ?_⟩
  · exact (logicalOpsIceberg m ⟨0, h0lt⟩).xOp_nontrivial
  · exact weight_logicalX m ⟨0, h0lt⟩

/-- T19: the iceberg code packaged with its distance. -/
noncomputable def stabilizerCodeWithDistance (m : ℕ) [Fact (2 ≤ m)] :
    StabilizerCodeWithDistance (2 * m) (2 * m - 2) 2 where
  toStabilizerCode := stabilizerCode m
  hasDistance      := code_has_distance_two m

end Iceberg
end StabilizerGroup
end Quantum
