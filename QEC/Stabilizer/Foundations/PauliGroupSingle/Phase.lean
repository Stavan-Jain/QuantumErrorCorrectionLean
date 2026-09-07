import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic
import QEC.Foundations.Foundations
import QEC.Stabilizer.Foundations.PauliGroupSingle.Core

namespace Quantum

namespace PauliGroupElement

/-!
# Phase Utilities (Fin 4 → ℂ / UnitComplex)
-/

/-- Convert a phase power (0-3) to the corresponding complex phase. -/
def phasePowerToComplex (k : Fin 4) : ℂ :=
  Complex.I ^ (k : ℕ)

@[simp] lemma phasePowerToComplex_0 : phasePowerToComplex 0 = 1 := by
  simp [phasePowerToComplex]

@[simp] lemma phasePowerToComplex_1 : phasePowerToComplex 1 = Complex.I := by
  simp [phasePowerToComplex]

@[simp] lemma phasePowerToComplex_2 : phasePowerToComplex 2 = -1 := by
  simp [phasePowerToComplex]

@[simp] lemma phasePowerToComplex_3 : phasePowerToComplex 3 = -Complex.I := by
  simp [phasePowerToComplex]

/-- Product of phase powers: phasePowerToComplex a * phasePowerToComplex b =
phasePowerToComplex (a + b). -/
lemma phasePowerToComplex_add (a b : Fin 4) :
  phasePowerToComplex a * phasePowerToComplex b = phasePowerToComplex (a + b) := by
  fin_cases a <;> fin_cases b <;> simp [phasePowerToComplex]

/-- Phase powers multiply as i^a * i^b * i^c = i^{a+b+c}. -/
lemma phasePowerToComplex_add3 (a b c : Fin 4) :
  phasePowerToComplex a * phasePowerToComplex b * phasePowerToComplex c =
  phasePowerToComplex (a + b + c) := by
  rw [phasePowerToComplex_add, phasePowerToComplex_add, add_assoc]

/-- The conjugate of a phase power equals the negative phase power: star(i^k) =
i^(-k). -/
lemma phasePowerToComplex_star (k : Fin 4) :
  star (phasePowerToComplex k) = phasePowerToComplex (-k) := by
  fin_cases k <;> simp [phasePowerToComplex]
  · rw [← Complex.I_sq]
    rfl
  · symm
    have h : (-3 : Fin 4) = 1 := by decide
    simp [h]

/-- Convert a phase power to the corresponding unit complex number. -/
def phasePowerToUnitComplex (k : Fin 4) : UnitComplex :=
  match k with
  | 0 => UnitComplex.one
  | 1 => UnitComplex.I
  | 2 => UnitComplex.negOne
  | 3 => UnitComplex.negI

@[simp] lemma phasePowerToUnitComplex_coe (k : Fin 4) :
  (phasePowerToUnitComplex k : ℂ) = phasePowerToComplex k := by
  fin_cases k <;> simp [phasePowerToUnitComplex, phasePowerToComplex,
    UnitComplex.one_coe, UnitComplex.negOne_coe, UnitComplex.I_coe, UnitComplex.negI_coe]

end PauliGroupElement

end Quantum

