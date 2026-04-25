import Mathlib.Tactic
import QEC.Stabilizer.Core.Centralizer
import QEC.Stabilizer.BinarySymplectic.IndependentEquiv

namespace Quantum
namespace StabilizerGroup
namespace CentralizerLemmas

open NQubitPauliGroupElement

variable {n : ℕ}

/-- Convenience constructor: commute with all generators in `genSet` to conclude centralizer
membership when `S.toSubgroup = closure genSet`. -/
lemma mem_centralizer_of_commutes_genSet
    (g : NQubitPauliGroupElement n) (S : StabilizerGroup n)
    (genSet : Set (NQubitPauliGroupElement n))
    (h_closure : S.toSubgroup = Subgroup.closure genSet)
    (h_comm : ∀ s ∈ genSet, s * g = g * s) :
    g ∈ centralizer S := by
  exact (mem_centralizer_iff_closure g S genSet h_closure).2 h_comm

/-- Convenience constructor from a generator list. -/
lemma mem_centralizer_of_commutes_list
    (g : NQubitPauliGroupElement n) (S : StabilizerGroup n)
    (L : List (NQubitPauliGroupElement n))
    (h_closure : S.toSubgroup = Subgroup.closure (NQubitPauliGroupElement.listToSet L))
    (h_comm : ∀ s ∈ NQubitPauliGroupElement.listToSet L, s * g = g * s) :
    g ∈ centralizer S := by
  exact mem_centralizer_of_commutes_genSet g S (NQubitPauliGroupElement.listToSet L)
    h_closure h_comm

/-- Eliminate centralizer membership back to generator-set commutation under closure equality. -/
lemma commutes_genSet_of_mem_centralizer
    (g : NQubitPauliGroupElement n) (S : StabilizerGroup n)
    (genSet : Set (NQubitPauliGroupElement n))
    (h_closure : S.toSubgroup = Subgroup.closure genSet)
    (hg : g ∈ centralizer S) :
    ∀ s ∈ genSet, s * g = g * s := by
  exact (mem_centralizer_iff_closure g S genSet h_closure).1 hg

end CentralizerLemmas
end StabilizerGroup
end Quantum

