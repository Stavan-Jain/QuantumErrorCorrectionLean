import Mathlib.Tactic
import QEC.Stabilizer.Core.StabilizerGroup
import QEC.Stabilizer.Core.SubgroupLemmas
import QEC.Stabilizer.Core.CSS
import QEC.Stabilizer.Core.CSSNoNegI
import QEC.Stabilizer.PauliGroup.Commutation
import QEC.Stabilizer.PauliGroup.CommutationTactics

namespace Quantum
open scoped BigOperators

namespace StabilizerGroup
namespace Shor9

/-!
# Shor’s 9-qubit code (stabilizer generators)

This file defines a clean, reusable formalization of Shor’s 9-qubit stabilizer subgroup:

- Z-type generators `M1`–`M6` (pairwise Z checks within blocks)
- X-type generators `M7`,`M8` (blockwise X checks)

and proves:
- the generated subgroup is **abelian**
- it does **not** contain `negIdentity 9`

The `no_neg_identity` proof uses the generic CSS lemma in `CSSNoNegI.lean`.
-/

open NQubitPauliGroupElement

/-!
## Generator definitions

Qubits are indexed `0..8` in three blocks `{0,1,2}`, `{3,4,5}`, `{6,7,8}`.
`M1`–`M6` are **intra-block** Z⊗Z on adjacent pairs within each block of three.
`M7` is X on all qubits `0..5`; `M8` is X on all qubits `3..8` (standard Shor CSS
presentation; overlapping supports).
-/

/-- Z⊗Z on qubits 0 and 1 (first block, adjacent pair). -/
def M1 : NQubitPauliGroupElement 9 :=
  ⟨0, ((NQubitPauliOperator.identity 9).set 0 PauliOperator.Z).set 1 PauliOperator.Z⟩

/-- Z⊗Z on qubits 1 and 2 (first block, adjacent pair). -/
def M2 : NQubitPauliGroupElement 9 :=
  ⟨0, ((NQubitPauliOperator.identity 9).set 1 PauliOperator.Z).set 2 PauliOperator.Z⟩

/-- Z⊗Z on qubits 3 and 4 (second block). -/
def M3 : NQubitPauliGroupElement 9 :=
  ⟨0, ((NQubitPauliOperator.identity 9).set 3 PauliOperator.Z).set 4 PauliOperator.Z⟩

/-- Z⊗Z on qubits 4 and 5 (second block). -/
def M4 : NQubitPauliGroupElement 9 :=
  ⟨0, ((NQubitPauliOperator.identity 9).set 4 PauliOperator.Z).set 5 PauliOperator.Z⟩

/-- Z⊗Z on qubits 6 and 7 (third block). -/
def M5 : NQubitPauliGroupElement 9 :=
  ⟨0, ((NQubitPauliOperator.identity 9).set 6 PauliOperator.Z).set 7 PauliOperator.Z⟩

/-- Z⊗Z on qubits 7 and 8 (third block). -/
def M6 : NQubitPauliGroupElement 9 :=
  ⟨0, ((NQubitPauliOperator.identity 9).set 7 PauliOperator.Z).set 8 PauliOperator.Z⟩

/-- X on each of qubits 0–5 (six-qubit X stabilizer, overlapping first two blocks). -/
def M7 : NQubitPauliGroupElement 9 :=
  ⟨0,
    ((((((NQubitPauliOperator.identity 9).set 0 PauliOperator.X).set 1 PauliOperator.X).set 2
                PauliOperator.X).set 3 PauliOperator.X).set 4 PauliOperator.X).set 5
      PauliOperator.X⟩

/-- X on each of qubits 3–8 (six-qubit X stabilizer, overlapping last two blocks). -/
def M8 : NQubitPauliGroupElement 9 :=
  ⟨0,
    ((((((NQubitPauliOperator.identity 9).set 3 PauliOperator.X).set 4 PauliOperator.X).set 5
                PauliOperator.X).set 6 PauliOperator.X).set 7 PauliOperator.X).set 8
      PauliOperator.X⟩

/-- The six Z-type generators `M1`–`M6`. -/
def ZGenerators : Set (NQubitPauliGroupElement 9) :=
  {M1, M2, M3, M4, M5, M6}

/-- The two X-type generators `M7`, `M8`. -/
def XGenerators : Set (NQubitPauliGroupElement 9) :=
  {M7, M8}

/-- Full generating set: ZGenerators ∪ XGenerators. -/
def generators : Set (NQubitPauliGroupElement 9) :=
  ZGenerators ∪ XGenerators

def subgroup : Subgroup (NQubitPauliGroupElement 9) :=
  Subgroup.closure generators

/-!
## Typing facts for the generators
-/

lemma ZGenerators_are_ZType :
    ∀ g, g ∈ ZGenerators → NQubitPauliGroupElement.IsZTypeElement g := by
  classical
  intro g hg
  -- Each `Mi` is by construction phase-0 with only I/Z entries.
  rcases (by simpa [ZGenerators] using hg) with rfl | rfl | rfl | rfl | rfl | rfl <;>
    · constructor
      · rfl
      · intro i
        fin_cases i <;> simp [PauliOperator.IsZType, M1, M2, M3, M4, M5, M6,
          NQubitPauliOperator.set, NQubitPauliOperator.identity]

lemma XGenerators_are_XType :
    ∀ g, g ∈ XGenerators → NQubitPauliGroupElement.IsXTypeElement g := by
  classical
  intro g hg
  rcases (by simpa [XGenerators] using hg) with rfl | rfl <;>
    · constructor
      · rfl
      · intro i
        fin_cases i <;> simp [PauliOperator.IsXType, M7, M8,
          NQubitPauliOperator.set, NQubitPauliOperator.identity]

/-!
## Commutation: Z generators commute with X generators

We use the parity characterization from `PauliGroup/Commutation.lean` and discharge the
finite parity goals by explicitly identifying the anticommute positions (n = 9).
-/

private lemma M1_comm_M7 : M1 * M7 = M7 * M1 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 9) M1.operators M7.operators)) =
        ({0, 1} : Finset (Fin 9)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, M1, M7,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  simp [hfilter]

private lemma M1_comm_M8 : M1 * M8 = M8 * M1 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 9) M1.operators M8.operators)) =
        (∅ : Finset (Fin 9)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, M1, M8,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  simp [hfilter]

private lemma M2_comm_M7 : M2 * M7 = M7 * M2 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 9) M2.operators M7.operators)) =
        ({1, 2} : Finset (Fin 9)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, M2, M7,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  simp [hfilter]

private lemma M2_comm_M8 : M2 * M8 = M8 * M2 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 9) M2.operators M8.operators)) =
        (∅ : Finset (Fin 9)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, M2, M8,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  simp [hfilter]

private lemma M3_comm_M7 : M3 * M7 = M7 * M3 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 9) M3.operators M7.operators)) =
        ({3, 4} : Finset (Fin 9)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, M3, M7,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  simp [hfilter]

private lemma M3_comm_M8 : M3 * M8 = M8 * M3 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 9) M3.operators M8.operators)) =
        ({3, 4} : Finset (Fin 9)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, M3, M8,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  simp [hfilter]

private lemma M4_comm_M7 : M4 * M7 = M7 * M4 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 9) M4.operators M7.operators)) =
        ({4, 5} : Finset (Fin 9)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, M4, M7,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  simp [hfilter]

private lemma M4_comm_M8 : M4 * M8 = M8 * M4 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 9) M4.operators M8.operators)) =
        ({4, 5} : Finset (Fin 9)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, M4, M8,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  simp [hfilter]

private lemma M5_comm_M7 : M5 * M7 = M7 * M5 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 9) M5.operators M7.operators)) =
        (∅ : Finset (Fin 9)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, M5, M7,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  simp [hfilter]

private lemma M5_comm_M8 : M5 * M8 = M8 * M5 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 9) M5.operators M8.operators)) =
        ({6, 7} : Finset (Fin 9)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, M5, M8,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  simp [hfilter]

private lemma M6_comm_M7 : M6 * M7 = M7 * M6 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 9) M6.operators M7.operators)) =
        (∅ : Finset (Fin 9)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, M6, M7,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  simp [hfilter]

private lemma M6_comm_M8 : M6 * M8 = M8 * M6 := by
  classical
  pauli_comm_even_anticommutes
  have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt (n := 9) M6.operators M8.operators)) =
        ({7, 8} : Finset (Fin 9)) := by
    ext i; fin_cases i <;>
      simp [Finset.mem_filter, NQubitPauliGroupElement.anticommutesAt, M6, M8,
        NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp]
  simp [hfilter]

lemma ZGenerators_commute_XGenerators :
    ∀ z ∈ ZGenerators, ∀ x ∈ XGenerators, z * x = x * z := by
  classical
  intro z hz x hx
  rcases (by simpa [ZGenerators] using hz) with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases (by simpa [XGenerators] using hx) with rfl | rfl
  · exact M1_comm_M7
  · exact M1_comm_M8
  · exact M2_comm_M7
  · exact M2_comm_M8
  · exact M3_comm_M7
  · exact M3_comm_M8
  · exact M4_comm_M7
  · exact M4_comm_M8
  · exact M5_comm_M7
  · exact M5_comm_M8
  · exact M6_comm_M7
  · exact M6_comm_M8

/-!
## Commutation: generators commute pairwise

We organize this by cases:
- Z/Z commute (componentwise, since only I/Z appear)
- X/X commute (componentwise, since only I/X appear)
- Z/X commute (lemma above)
-/

private lemma ZType_commutes {g h : NQubitPauliGroupElement 9}
    (hg : NQubitPauliGroupElement.IsZTypeElement g)
    (hh : NQubitPauliGroupElement.IsZTypeElement h) :
    g * h = h * g := by
  classical
  apply NQubitPauliGroupElement.commutes_of_componentwise_commutes
  intro i
  -- At each qubit, both operators are `I` or `Z`, so `mulOp` commutes.
  have hg' := hg.2 i
  have hh' := hh.2 i
  rcases hg' with hgI | hgZ <;> rcases hh' with hhI | hhZ
  · simp [PauliOperator.mulOp, hgI, hhI]
  · simp [PauliOperator.mulOp, hgI, hhZ]
  · simp [PauliOperator.mulOp, hgZ, hhI]
  · simp [PauliOperator.mulOp, hgZ, hhZ]

private lemma XType_commutes {g h : NQubitPauliGroupElement 9}
    (hg : NQubitPauliGroupElement.IsXTypeElement g)
    (hh : NQubitPauliGroupElement.IsXTypeElement h) :
    g * h = h * g := by
  classical
  apply NQubitPauliGroupElement.commutes_of_componentwise_commutes
  intro i
  have hg' := hg.2 i
  have hh' := hh.2 i
  rcases hg' with hgI | hgX <;> rcases hh' with hhI | hhX
  · simp [PauliOperator.mulOp, hgI, hhI]
  · simp [PauliOperator.mulOp, hgI, hhX]
  · simp [PauliOperator.mulOp, hgX, hhI]
  · simp [PauliOperator.mulOp, hgX, hhX]

theorem generators_commute :
    ∀ g ∈ generators, ∀ h ∈ generators, g * h = h * g := by
  classical
  intro g hg h hh
  have hg' : g ∈ ZGenerators ∨ g ∈ XGenerators := by simpa [generators] using hg
  have hh' : h ∈ ZGenerators ∨ h ∈ XGenerators := by simpa [generators] using hh
  rcases hg' with hgZ | hgX <;> rcases hh' with hhZ | hhX
  · exact ZType_commutes (ZGenerators_are_ZType g hgZ) (ZGenerators_are_ZType h hhZ)
  · exact ZGenerators_commute_XGenerators g hgZ h hhX
  · simpa using (ZGenerators_commute_XGenerators h hhZ g hgX).symm
  · exact XType_commutes (XGenerators_are_XType g hgX) (XGenerators_are_XType h hhX)

/-!
## `-I` is not in the Shor-9 stabilizer subgroup
-/

theorem negIdentity_not_mem :
    negIdentity 9 ∉ subgroup := by
  -- `subgroup = closure (ZGenerators ∪ XGenerators)` and `generators = ZGenerators ∪ XGenerators`.
  have hZX : ∀ z ∈ ZGenerators, ∀ x ∈ XGenerators, z * x = x * z :=
    ZGenerators_commute_XGenerators
  -- Use the reusable CSS lemma.
  simpa [subgroup, generators] using
    (CSS.negIdentity_not_mem_closure_union (n := 9) ZGenerators XGenerators
      ZGenerators_are_ZType XGenerators_are_XType hZX)

/-!
## Bundled `StabilizerGroup 9`
-/

noncomputable def stabilizerGroup : StabilizerGroup 9 :=
{ toSubgroup := subgroup
, is_abelian := by
    intro g h hg hh
    -- Abelian closure from commuting generators.
    have hcomm :=
      Subgroup.abelian_closure_of_pairwise_commute (G := NQubitPauliGroupElement 9)
        generators generators_commute
    simpa [subgroup] using hcomm g (by simpa [subgroup] using hg) h (by simpa [subgroup] using hh)
, no_neg_identity := by
    simpa using negIdentity_not_mem }

end Shor9
end StabilizerGroup

end Quantum

