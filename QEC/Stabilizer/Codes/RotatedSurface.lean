import QEC.Stabilizer.Codes.RotatedSurface.N
import QEC.Stabilizer.Codes.RotatedSurface.CellComplex
import QEC.Stabilizer.Codes.RotatedSurface.BoundaryMaps
import QEC.Stabilizer.Codes.RotatedSurface.ChainComplex
import QEC.Stabilizer.Codes.RotatedSurface.H1Dimension
import QEC.Stabilizer.Codes.RotatedSurface.Distance
import QEC.Stabilizer.Codes.RotatedSurface.DistanceX
import QEC.Stabilizer.Codes.RotatedSurface.DistanceZ
import QEC.Stabilizer.Codes.RotatedSurface.StabilizerCode

/-!
# Rotated surface code family

The parametric `L × L` rotated-surface code, with lattice geometry + chain
complex + distance. The distance-3 specialization (`Three.lean`) is **parked on
branch `claude/z3z6-parked`** pending de-nativization.
-/
