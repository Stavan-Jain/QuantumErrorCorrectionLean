import Mathlib.Tactic
import QEC.Stabilizer.Lattice.ToricChains
import QEC.Stabilizer.PauliGroup
import QEC.Stabilizer.PauliGroup.NQubitOperator

namespace Quantum
namespace Stabilizer
namespace Lattice

open scoped BigOperators

/-- Number of edge qubits for an `L × L` toric lattice. -/
abbrev toricNumQubits (L : ℕ) : ℕ := 2 * L * L

/-- Encode an edge index as the corresponding qubit index in `[0, 2L²)`. -/
def edgeToQubitIdx (L : ℕ) : EdgeIdx L → Fin (toricNumQubits L)
  | EdgeIdx.h x y =>
      ⟨y.val * L + x.val, by
        have hx := x.isLt
        have hy := y.isLt
        dsimp [toricNumQubits]
        nlinarith⟩
  | EdgeIdx.v x y =>
      ⟨L * L + y.val * L + x.val, by
        have hx := x.isLt
        have hy := y.isLt
        dsimp [toricNumQubits]
        nlinarith⟩

/-- Build an X-type Pauli group element from a 1-chain (support encoding). -/
def toricXOperatorOfChain (L : ℕ) (c : C1 L) :
    NQubitPauliGroupElement (toricNumQubits L) :=
  ⟨0, fun q =>
    if ∃ e : EdgeIdx L, edgeToQubitIdx L e = q ∧ c e = 1
    then PauliOperator.X else PauliOperator.I⟩

/-- Recover an edge 1-chain from an X-support Pauli element. -/
def chainOfXOperator (L : ℕ) (g : NQubitPauliGroupElement (toricNumQubits L)) : C1 L :=
  fun e => if g.operators (edgeToQubitIdx L e) = PauliOperator.X then 1 else 0

/-- Roundtrip (`chain -> operator -> chain`) on this encoding. -/
theorem chainOfXOperator_toricXOperatorOfChain (L : ℕ) (c : C1 L) :
    chainOfXOperator L (toricXOperatorOfChain L c) = c := by
  sorry

/-- Support/weight compatibility placeholder for future distance proofs. -/
theorem edgeWeight_eq_operatorSupportWeight (L : ℕ) (c : C1 L) :
    edgeWeight (L := L) c =
      (NQubitPauliOperator.support (toricXOperatorOfChain L c).operators).card := by
  sorry

end Lattice
end Stabilizer
end Quantum

