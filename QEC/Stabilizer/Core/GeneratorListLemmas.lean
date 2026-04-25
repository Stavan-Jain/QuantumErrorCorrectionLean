import Mathlib.Tactic
import Mathlib.Data.List.OfFn
import QEC.Stabilizer.BinarySymplectic.IndependentEquiv

namespace Quantum
namespace StabilizerGroup
namespace GeneratorListLemmas

open NQubitPauliGroupElement

/-- Every coordinate pair belongs to `finRange × finRange`. -/
lemma mem_finRange_product (L : ℕ) (p : Fin L × Fin L) :
    p ∈ (List.finRange L).product (List.finRange L) := by
  rcases p with ⟨x, y⟩
  simp

/-- Mapping a complete `L×L` coordinate list gives exactly the range of the map in `listToSet`. -/
lemma listToSet_map_product_finRange_eq_range {n L : ℕ}
    (f : Fin L × Fin L → NQubitPauliGroupElement n) :
    NQubitPauliGroupElement.listToSet
        (((List.finRange L).product (List.finRange L)).map f) =
      Set.range f := by
  ext g
  rw [NQubitPauliGroupElement.listToSet, Set.mem_setOf, Set.mem_range]
  constructor
  · intro hg
    rcases List.mem_map.mp hg with ⟨a, ha, hag⟩
    exact ⟨a, hag⟩
  · intro hg
    rcases hg with ⟨a, hag⟩
    exact List.mem_map.mpr ⟨a, mem_finRange_product L a, hag⟩

end GeneratorListLemmas
end StabilizerGroup
end Quantum

