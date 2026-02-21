import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Tactic
import QEC.Stabilizer.BinarySymplectic.CheckMatrix

namespace Quantum

variable {n : ℕ}

open scoped BigOperators

namespace NQubitPauliGroupElement

/-!
# Decidability of rowsLinearIndependent

For a list `L` of n-qubit Pauli group elements, `rowsLinearIndependent L` is equivalent to:
the only F₂-coefficient combination of the check-matrix rows that equals zero is the zero
combination. We decide this by checking all `f : Fin L.length → ZMod 2` (finitely many).
-/

/-- Rows are linearly independent iff the only coefficient vector giving the zero combination
    is the zero vector. -/
theorem rowsLinearIndependent_iff_forall (L : List (NQubitPauliGroupElement n)) :
    rowsLinearIndependent L ↔
      ∀ f : Fin L.length → ZMod 2, (∑ i, f i • checkMatrix L i) = 0 → f = 0 := by
  rw [rowsLinearIndependent, Fintype.linearIndependent_iffₛ]
  constructor
  · intro h f hf
    exact funext (h f 0 (by simp [hf]))
  · intro h f g hfg i
    have hsum : (∑ j, (f j + g j) • checkMatrix L j) = 0 := by
      simp only [add_smul, Finset.sum_add_distrib, hfg]
      rw [← two_smul (ZMod 2) (∑ i, g i • checkMatrix L i)]
      have h2 : (2 : ZMod 2) = 0 := rfl
      rw [h2, zero_smul]
    have hfgz := h (f + g) hsum
    have heq := congr_fun hfgz i
    simp only [Pi.zero_apply, Pi.add_apply] at heq
    rw [← ZModModule.add_self (f i)] at heq
    exact (add_left_cancel heq).symm

/-- Decidability of row linear independence: we check exhaustively over all coefficient
    vectors in (ZMod 2)^(L.length). -/
instance (L : List (NQubitPauliGroupElement n)) : Decidable (rowsLinearIndependent L) :=
  decidable_of_iff' (∀ f : Fin L.length → ZMod 2, (∑ i, f i • checkMatrix L i) = 0 → f = 0)
    (rowsLinearIndependent_iff_forall L)

end NQubitPauliGroupElement

end Quantum
