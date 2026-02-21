import QEC.Stabilizer.BinarySymplectic.Core
import QEC.Stabilizer.BinarySymplectic.SymplecticInner
import QEC.Stabilizer.BinarySymplectic.CheckMatrix
import QEC.Stabilizer.BinarySymplectic.CheckMatrixDecidable
import QEC.Stabilizer.BinarySymplectic.IndependentEquiv
import QEC.Stabilizer.BinarySymplectic.SymplecticSpan

/-!
# Binary symplectic representation and check matrix

This module re-exports:

- **Core**: `PauliOperator.toSymplecticSingle`, `NQubitPauliOperator.toSymplectic`
- **SymplecticInner**: `symplecticInner`, `commutes_iff_symplectic_inner_zero`, `toSymplectic_add`
- **CheckMatrix**: `NQubitPauliGroupElement.checkMatrix`, `rowsLinearIndependent`
- **CheckMatrixDecidable**: `Decidable (rowsLinearIndependent L)` and
  `rowsLinearIndependent_iff_forall`
- **IndependentEquiv**: `listToSet`, `rowsLinearIndependent_implies_independentGenerators`
-/
