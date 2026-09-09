/-
GENERATED FILE — DO NOT HAND-EDIT.
Emitted by qec-lab:experiments/bb_lab/scripts/m150_gen_lean_data.py (mode: instance)
from instances/mitten_groups/group_30_1.txt + arXiv:2607.28795 Table XIII sets;
all facts validated in numpy before emission (dictionary hom, closed-form H vs
a26_mitten_descent.mitten_code, pivot inverses, symplectic basis, witness).
Regen: uv run python scripts/m150_gen_lean_data.py instance --out <M150 dir> --force
Attempt state: qec-lab:pipeline/attempts/mitten_150_30_10/.
-/
import QEC.Stabilizer.Framework.Homological.LiftedProduct
import Mathlib.GroupTheory.SpecificGroups.Dihedral

namespace Quantum
namespace Stabilizer
namespace Homological
namespace LP
namespace M150

/-- The `[[150,30,10]]` mitten group carrier: C₅ (multiplicative) × S₃. -/
abbrev M150G : Type := Multiplicative (ZMod 5) × DihedralGroup 3

/-- GAP `Elements(SmallGroup(30,1))` order → carrier (z^i·r^j·s^k
parameterization; z = idx 2, r = idx 3, s = idx 1). -/
def gapElems : List M150G := [
  (Multiplicative.ofAdd (0 : ZMod 5), DihedralGroup.r 0),
  (Multiplicative.ofAdd (0 : ZMod 5), DihedralGroup.sr 0),
  (Multiplicative.ofAdd (1 : ZMod 5), DihedralGroup.r 0),
  (Multiplicative.ofAdd (0 : ZMod 5), DihedralGroup.r 1),
  (Multiplicative.ofAdd (1 : ZMod 5), DihedralGroup.sr 0),
  (Multiplicative.ofAdd (0 : ZMod 5), DihedralGroup.sr 1),
  (Multiplicative.ofAdd (2 : ZMod 5), DihedralGroup.r 0),
  (Multiplicative.ofAdd (1 : ZMod 5), DihedralGroup.r 1),
  (Multiplicative.ofAdd (0 : ZMod 5), DihedralGroup.r 2),
  (Multiplicative.ofAdd (2 : ZMod 5), DihedralGroup.sr 0),
  (Multiplicative.ofAdd (1 : ZMod 5), DihedralGroup.sr 1),
  (Multiplicative.ofAdd (0 : ZMod 5), DihedralGroup.sr 2),
  (Multiplicative.ofAdd (3 : ZMod 5), DihedralGroup.r 0),
  (Multiplicative.ofAdd (2 : ZMod 5), DihedralGroup.r 1),
  (Multiplicative.ofAdd (1 : ZMod 5), DihedralGroup.r 2),
  (Multiplicative.ofAdd (3 : ZMod 5), DihedralGroup.sr 0),
  (Multiplicative.ofAdd (2 : ZMod 5), DihedralGroup.sr 1),
  (Multiplicative.ofAdd (1 : ZMod 5), DihedralGroup.sr 2),
  (Multiplicative.ofAdd (4 : ZMod 5), DihedralGroup.r 0),
  (Multiplicative.ofAdd (3 : ZMod 5), DihedralGroup.r 1),
  (Multiplicative.ofAdd (2 : ZMod 5), DihedralGroup.r 2),
  (Multiplicative.ofAdd (4 : ZMod 5), DihedralGroup.sr 0),
  (Multiplicative.ofAdd (3 : ZMod 5), DihedralGroup.sr 1),
  (Multiplicative.ofAdd (2 : ZMod 5), DihedralGroup.sr 2),
  (Multiplicative.ofAdd (4 : ZMod 5), DihedralGroup.r 1),
  (Multiplicative.ofAdd (3 : ZMod 5), DihedralGroup.r 2),
  (Multiplicative.ofAdd (4 : ZMod 5), DihedralGroup.sr 1),
  (Multiplicative.ofAdd (3 : ZMod 5), DihedralGroup.sr 2),
  (Multiplicative.ofAdd (4 : ZMod 5), DihedralGroup.r 2),
  (Multiplicative.ofAdd (4 : ZMod 5), DihedralGroup.sr 2)]

/-- Carrier element of a GAP index (junk-total via identity). -/
def elemOf (i : Nat) : M150G := gapElems.getD i 1

/-- Qubit cell of a canonical qubit index `30·m + g`. -/
def qubitOf (c : Nat) : Fin 5 × M150G :=
  (⟨(c / 30) % 5, Nat.mod_lt _ (by omega)⟩, elemOf (c % 30))

/-- Check cell of a canonical check index `30·i + g`. -/
def checkOf (k : Nat) : Fin 2 × M150G :=
  (⟨(k / 30) % 2, Nat.mod_lt _ (by omega)⟩, elemOf (k % 30))

/-- Table XIII sets (paper order a0, a1, b0, b1). -/
def a0 : List M150G := [
  (Multiplicative.ofAdd (0 : ZMod 5), DihedralGroup.r 0),
  (Multiplicative.ofAdd (1 : ZMod 5), DihedralGroup.r 2),
  (Multiplicative.ofAdd (2 : ZMod 5), DihedralGroup.sr 2)]
def a1 : List M150G := [
  (Multiplicative.ofAdd (0 : ZMod 5), DihedralGroup.r 0),
  (Multiplicative.ofAdd (1 : ZMod 5), DihedralGroup.r 0),
  (Multiplicative.ofAdd (0 : ZMod 5), DihedralGroup.sr 2)]
def b0 : List M150G := [
  (Multiplicative.ofAdd (1 : ZMod 5), DihedralGroup.r 1),
  (Multiplicative.ofAdd (2 : ZMod 5), DihedralGroup.r 2),
  (Multiplicative.ofAdd (4 : ZMod 5), DihedralGroup.r 1)]
def b1 : List M150G := [
  (Multiplicative.ofAdd (0 : ZMod 5), DihedralGroup.r 0),
  (Multiplicative.ofAdd (1 : ZMod 5), DihedralGroup.r 0),
  (Multiplicative.ofAdd (4 : ZMod 5), DihedralGroup.sr 2)]

/-- Pivot qubit indices for `H_X` (canonical `30·m + g`). -/
def pivX : List Nat := [
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14,
  15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 27, 28, 30, 31,
  32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46,
  47, 48, 49, 50, 51, 52, 53, 54, 55, 57, 58, 60, 63, 90, 93]

/-- Pivot qubit indices for `H_Z`. -/
def pivZ : List Nat := [
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14,
  15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
  60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74,
  75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89]

/-- Rows of `(H_X[:,pivX])⁻¹`, packed little-endian 60-bit Nats. -/
def wX : List Nat := [
  461002194, 717054240, 1071001615, 303631590,
  628021345, 644374075, 453015045, 892037995,
  793330703, 540697559, 864014477, 774577454,
  65284547, 835146994, 460985810, 497970740,
  170302574, 841182513, 340341514, 1019786837,
  430861876, 202897555, 989885957, 679839071,
  189121887, 713008776, 1039182945, 432190893,
  494997336653561856, 769931127564533760, 1149979227597045760, 326021937270620160,
  674332784491233280, 691891394628812800, 486421200717742080, 957818503828602880,
  851832356074422272, 580569583233007616, 927728480496386048, 831696208287236096,
  70098748574793728, 896732256645677056, 494979744467517440, 534692010666229760,
  182860996438654976, 903212845825523712, 365438918025281536, 1094987778451570688,
  462634416628301824, 217859590790840320, 1062881953021165568, 729971644122005504,
  203068079905701888, 765587343670247424, 1115814190833991680, 464061437766008832,
  768556269, 376821623, 825231010122694656, 404609136802660352]

/-- Rows of `(H_Z[:,pivZ])⁻¹`. -/
def wZ : List Nat := [
  319308228, 742526480, 286290248, 302280837,
  612600352, 673416210, 35410312, 270278981,
  18632844, 149064736, 551619090, 81953840,
  320102529, 50876741, 51650761, 748880898,
  205687314, 211879458, 303571213, 286543948,
  302526605, 683739186, 614629936, 675382322,
  34869705, 286007748, 144739874, 610340368,
  17330505, 71535138, 342854599150927872, 797281737003499520,
  307401813080932352, 324571577280626688, 657774619339522048, 723075149636567040,
  38021532995289088, 290209846047801344, 20006863902867456, 160057041526718464,
  592296487849820160, 87997265645404160, 343707473355472896, 54628484680515584,
  55459582327128064, 804104741377277952, 220855071708020736, 227503835701051392,
  325957107960512512, 307674221381681152, 324835468661227520, 734159360715915264,
  659953868565643264, 725186246321635328, 37441060649041920, 307098481015652352,
  155413256314290176, 655347979997151232, 18608488049541120, 76810269556211712]

/-- Supports of the 30 logical-Z chains (rows of `Lz`, ⊂ ker H_X). -/
def logZsup : List (List Nat) := [
  [
   0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 12, 13, 15, 16,
   18, 19, 21, 22, 24, 26],
  [
   0, 1, 2, 4, 6, 8, 9, 11, 12, 14, 15, 17, 18, 20,
   21, 23, 25, 27, 28, 29],
  [
   3, 5, 10, 12, 15, 17, 19, 20, 23, 24, 25, 28, 60, 61],
  [
   6, 8, 9, 12, 16, 17, 21, 22, 25, 27, 60, 62],
  [
   0, 1, 2, 4, 5, 13, 15, 16, 17, 19, 21, 23, 26, 28,
   60, 64],
  [
   0, 1, 2, 14, 15, 19, 20, 21, 22, 23, 27, 29, 63, 65],
  [
   1, 3, 4, 10, 13, 16, 18, 19, 24, 25, 27, 28, 61, 62,
   63, 64, 65, 66],
  [
   1, 2, 3, 5, 7, 8, 10, 12, 16, 17, 18, 23, 24, 25,
   60, 62, 63, 67],
  [
   0, 1, 2, 3, 5, 6, 7, 8, 10, 11, 13, 16, 18, 21,
   23, 28, 29, 60, 64, 65, 66, 68],
  [
   1, 4, 6, 10, 12, 14, 16, 17, 19, 21, 22, 23, 27, 60,
   62, 67, 68, 69],
  [
   1, 4, 5, 7, 9, 10, 11, 13, 20, 21, 22, 25, 26, 29,
   61, 62, 63, 65, 66, 67, 69, 70],
  [
   0, 3, 6, 7, 9, 10, 11, 16, 21, 22, 24, 27, 28, 62,
   64, 65, 67, 69, 70, 71],
  [
   2, 4, 5, 6, 9, 10, 11, 12, 14, 16, 17, 19, 21, 24,
   27, 29, 60, 62, 65, 66, 67, 68, 71, 72],
  [
   0, 3, 6, 7, 9, 15, 16, 19, 22, 25, 26, 28, 62, 63,
   64, 66, 67, 68, 70, 71, 72, 73],
  [
   1, 5, 7, 9, 11, 14, 15, 16, 17, 19, 21, 23, 24, 26,
   27, 28, 60, 62, 66, 69, 70, 71, 73, 74],
  [
   0, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 16, 18, 20,
   25, 29, 62, 63, 64, 65, 66, 68, 69, 70, 71, 72, 73, 75],
  [
   1, 4, 5, 6, 8, 9, 10, 11, 14, 17, 18, 19, 22, 24,
   60, 61, 62, 63, 65, 66, 70, 76],
  [
   0, 1, 2, 5, 8, 9, 10, 11, 12, 14, 15, 22, 23, 25,
   26, 28, 29, 62, 64, 71, 72, 74, 76, 77],
  [
   2, 3, 6, 7, 9, 13, 15, 16, 17, 20, 22, 25, 27, 28,
   29, 60, 62, 63, 66, 68, 70, 71, 72, 73, 77, 78],
  [
   3, 6, 8, 10, 13, 16, 19, 22, 23, 24, 28, 29, 60, 61,
   62, 63, 64, 67, 69, 70, 71, 72, 73, 74, 75, 76, 78, 79],
  [
   0, 1, 2, 3, 6, 7, 10, 11, 12, 17, 18, 20, 25, 26,
   28, 29, 65, 66, 67, 70, 71, 72, 74, 77, 79, 80],
  [
   0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 13, 14, 15, 17,
   18, 19, 25, 26, 27, 29, 60, 61, 62, 63, 65, 67, 68, 69,
   70, 71, 73, 74, 75, 76, 77, 81],
  [
   0, 4, 7, 8, 9, 10, 13, 16, 19, 21, 22, 23, 24, 25,
   26, 27, 28, 29, 60, 63, 64, 65, 66, 67, 68, 70, 76, 80,
   81, 82],
  [
   0, 2, 3, 4, 7, 8, 9, 10, 14, 15, 18, 19, 23, 24,
   26, 27, 61, 62, 63, 64, 66, 70, 71, 72, 73, 77, 79, 80,
   81, 83],
  [
   0, 1, 4, 8, 11, 12, 17, 21, 23, 28, 29, 62, 64, 67,
   68, 78, 79, 84],
  [
   0, 2, 8, 10, 12, 16, 19, 20, 24, 25, 27, 28, 60, 61,
   63, 68, 69, 72, 73, 75, 81, 82, 84, 85],
  [
   1, 5, 13, 14, 15, 16, 19, 22, 25, 26, 61, 63, 65, 66,
   67, 69, 71, 73, 76, 78, 82, 83, 84, 86],
  [
   0, 1, 2, 8, 11, 14, 15, 18, 20, 28, 29, 61, 63, 65,
   68, 69, 71, 72, 73, 74, 80, 83, 85, 87],
  [
   1, 3, 5, 7, 8, 13, 14, 21, 22, 24, 28, 61, 63, 68,
   70, 72, 73, 74, 75, 76, 77, 78, 80, 81, 83, 85, 86, 88],
  [
   0, 3, 5, 10, 11, 16, 17, 18, 19, 26, 29, 60, 61, 62,
   64, 65, 67, 72, 73, 75, 79, 80, 81, 82, 85, 89]]

/-- Supports of the 30 logical-X chains (rows of `Lx`, ⊂ ker H_Z);
`Lx·Lzᵀ = I₃₀` (validated offline, re-checked in Lean). -/
def logXsup : List (List Nat) := [
  [
   1, 4, 5, 6, 8, 9, 11, 13, 15, 16, 18, 19, 20, 22,
   25, 28, 29, 30],
  [
   0, 4, 8, 12, 16, 17, 19, 22, 23, 24, 26, 27, 28, 29,
   30, 33],
  [
   0, 1, 2, 3, 4, 5, 12, 15, 18, 20, 21, 23, 25, 27,
   30, 31],
  [
   0, 1, 5, 6, 10, 12, 13, 14, 16, 17, 18, 20, 21, 24,
   26, 29, 30, 32],
  [
   0, 1, 2, 4, 8, 11, 12, 13, 14, 15, 16, 17, 20, 23,
   25, 27, 30, 31, 33, 35],
  [
   0, 1, 2, 3, 4, 5, 10, 11, 12, 16, 18, 19, 20, 22,
   23, 25, 32, 36],
  [
   0, 1, 3, 7, 9, 13, 14, 15, 16, 17, 18, 21, 23, 24,
   26, 28, 31, 34],
  [
   0, 2, 3, 4, 5, 9, 11, 12, 14, 16, 17, 18, 19, 28,
   30, 32, 33, 37],
  [
   4, 5, 6, 7, 8, 9, 14, 18, 19, 20, 21, 22, 23, 24,
   27, 28, 29, 32, 33, 34, 36, 38],
  [
   1, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21,
   22, 23, 27, 28, 30, 32, 33, 34, 37, 39],
  [
   4, 6, 8, 12, 13, 16, 17, 23, 25, 26, 29, 31, 34, 35,
   37, 38, 39, 40],
  [
   3, 5, 6, 7, 9, 13, 16, 21, 23, 24, 26, 30, 31, 32,
   34, 36, 37, 38, 40, 43],
  [
   0, 1, 3, 7, 8, 9, 11, 12, 13, 14, 16, 17, 19, 22,
   23, 28, 30, 33, 34, 35, 36, 37, 38, 39, 40, 41],
  [
   0, 1, 2, 6, 7, 9, 11, 13, 15, 19, 21, 22, 23, 26,
   28, 30, 31, 33, 34, 35, 37, 39, 41, 42],
  [
   1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 13, 15, 16, 17,
   19, 20, 21, 24, 25, 26, 28, 32, 36, 41, 43, 45],
  [
   6, 9, 13, 14, 16, 17, 20, 23, 25, 27, 30, 31, 33, 35,
   36, 37, 38, 39, 40, 41, 42, 43, 45, 46],
  [
   0, 1, 4, 5, 6, 7, 9, 10, 11, 13, 15, 21, 23, 25,
   26, 28, 29, 31, 32, 33, 36, 37, 39, 42, 43, 44],
  [
   0, 3, 4, 7, 8, 9, 10, 11, 12, 13, 17, 18, 19, 20,
   21, 25, 26, 28, 31, 34, 37, 38, 41, 44, 46, 47],
  [
   2, 5, 6, 8, 9, 14, 15, 17, 19, 22, 26, 27, 34, 35,
   39, 40, 42, 51],
  [
   2, 3, 4, 7, 8, 9, 11, 12, 14, 16, 17, 18, 19, 22,
   24, 25, 26, 27, 29, 33, 34, 35, 36, 38, 41, 42, 43, 44,
   45, 48],
  [
   1, 3, 5, 6, 8, 14, 16, 17, 18, 19, 22, 23, 24, 25,
   26, 28, 29, 31, 32, 34, 35, 36, 37, 39, 40, 42, 43, 44,
   48, 49],
  [
   0, 1, 2, 4, 5, 7, 12, 15, 16, 20, 22, 23, 25, 29,
   34, 35, 36, 38, 43, 50],
  [
   1, 5, 6, 10, 11, 14, 15, 16, 20, 21, 22, 24, 25, 26,
   27, 29, 39, 40, 41, 43, 46, 48, 50, 52],
  [
   1, 2, 5, 10, 11, 12, 14, 16, 18, 19, 21, 23, 24, 25,
   28, 32, 35, 38, 39, 40, 46, 50, 51, 53],
  [
   1, 2, 4, 5, 6, 7, 10, 11, 12, 14, 15, 16, 17, 21,
   26, 27, 28, 30, 31, 33, 34, 35, 38, 39, 40, 42, 44, 45,
   47, 50, 51, 52, 53, 54],
  [
   1, 2, 3, 6, 10, 12, 14, 16, 17, 18, 21, 22, 24, 25,
   26, 27, 30, 36, 40, 41, 42, 43, 44, 45, 46, 48, 49, 51,
   53, 55],
  [
   5, 8, 18, 21, 22, 25, 30, 31, 32, 34, 35, 36, 40, 41,
   42, 44, 46, 49, 55, 57],
  [
   0, 6, 11, 12, 22, 24, 26, 27, 29, 32, 34, 35, 41, 42,
   46, 47, 55, 56],
  [
   0, 1, 8, 10, 14, 18, 22, 26, 28, 32, 35, 38, 39, 40,
   41, 44, 46, 47, 49, 51, 52, 53, 57, 59],
  [
   2, 3, 5, 11, 12, 17, 18, 26, 29, 35, 36, 39, 40, 47,
   48, 52, 53, 58]]

/-- Support of the weight-10 distance witness (∈ ker H_X, ∉ rowspace H_Z). -/
def witSup : List Nat := [
  59, 90, 96, 105, 108, 109, 111, 113, 117, 119]

/-- Support of its dual pairing (∈ ker H_Z, ⟨·, wit⟩ = 1). -/
def witPairSup : List Nat := [
  3, 4, 7, 9, 10, 12, 13, 14, 16, 17, 18, 20, 22, 24,
  26, 27, 28, 59]

end M150
end LP
end Homological
end Stabilizer
end Quantum
