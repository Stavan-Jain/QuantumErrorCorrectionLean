import QEC.Stabilizer.Codes.Small.Shor9
import QEC.Stabilizer.Codes.Small.Steane7
import QEC.Stabilizer.Codes.Small.Steane7Distance
import QEC.Stabilizer.Codes.Small.Steane7TransversalGates
import QEC.Stabilizer.Codes.Small.FourQubit_4_2_2
import QEC.Stabilizer.Codes.Small.QuantumHamming
import QEC.Stabilizer.Codes.Small.FiveQubit_5_1_3
import QEC.Stabilizer.Codes.Small.CSS_4_1_2
import QEC.Stabilizer.Codes.Small.SixQubit_6_2_2

/-!
# Small concrete codes

Single-instance stabilizer codes: Shor's [[9,1,3]], Steane [[7,1,3]] (with
transversal gates, and its distance-3 proof in `Steane7Distance.lean` via the
Hamming-column condition), the [[4,2,2]] code, quantum Hamming, the [[5,1,3]]
perfect code (the first non-CSS code in the repo), the [[4,1,2]]
LNCY CSS detection code, and Knill's C_6 [[6,2,2]] CSS detection code.
-/
