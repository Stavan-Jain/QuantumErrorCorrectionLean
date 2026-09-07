import QEC.Stabilizer.Codes.BivariateBicycle.Gross.SafeFloor.MImClassify
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.SafeFloor.MImTransport
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.SafeFloor.MImFloorY0
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.SafeFloor.MImFloorY1
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.SafeFloor.MImFloorY4
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.SafeFloor.MImFloorY11
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.SafeFloor.MImFloorY12
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.SafeFloor.MImAssembly
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.SafeFloor.SlotFrame
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.SafeFloor.WtFloor24
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.SafeFloor.WtFloor24Bridge
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.SafeFloor.WtFloor1618
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.SafeFloor.LightFloor

/-!
# Gross safe floor — everything discharging `MImBound`

What a small instance does in one file (discharging its `SeamCosetFloor`), gross
needs this directory for (discharging `MImBound` — the safe-sector coset floor
at weight 12). Every orbit is discharged by the **Tier-3 analytic** track; the
old `native_decide` confined-floor engine (`MImFloor`, `MImFloorData`,
`MImMembership`, the `2³⁰` `floorOK` walk) has been retired (status board:
`../../README.md`).

- `MImClassify` — the safe-sector confined-frame floor *reduction* (A4 §§9–13):
  the weight join (`chainWeight` as a per-block per-layer sum), the `ker ∂₂`
  basis with M-VANISH (`off₀ = off₂ = 0`), the exact per-slot weight (Fourier
  bijection), and the closed coset weight form `chainWeight_coset_eq` (=
  `costFromComps` of the seam offsets ⊕ engine-multiplied free datum)
- `MImTransport` — the translation symmetry: `seamC` y-covariance, the x
  cut-shift defect, and the general `floor_transfer` (§17) lifting a class's
  floor to any `(j,k)`-translate
- `LightFloor` — **(Tier 3, A4 §§12–13)** the coupled light-orbit certificate:
  the packed ring frame, the spine-cell checker (`killOK`) carrying Prop 30
  (`min_L + min_R ≥ 10` on all `1024` cells) and Prop 31 (the ρ-link kill of the
  `10`-tight cells), the coset extraction (`coset_ex`) and the soundness bridge
  (`floor_of_killOK`)
- `MImFloorY{0,1,4,11,12}` — the safe-sector floor proven for the 5
  full-translation-orbit representatives, **all analytic**: the **light orbits**
  `Y0, Y1, Y4` (weights 16/18a/18b) by the coupled spine certificate
  (`LightFloor.floor_of_killOK`), the **weight-24 orbits** `Y11, Y12` by the
  decoupled slot-frame walk (`WtFloor24Bridge.costFromComps_ge_12_of_blocks`).
  No `floorOK` leaf
- `MImAssembly` — **discharges `MImBound`** (`mimBound_holds`): the 64-case
  2-D-orbit dispatch (`floor_kcombo`) reduces every `ker ∂₂` class to one of the
  5 reps; then the **unconditional**
  `grossStabilizerCode_hasCodeDistance_12_uncond` and the bundled
  `grossStabilizerCodeWithDistance : StabilizerCodeWithDistance 144 12 12`
- `SlotFrame` — **(Tier 3, A4 §10)** analytic slot-frame infrastructure that
  replaces the `native_decide` confined-floor engine: `floor_of_data_analytic`,
  the slot algebra (`kappa`, `ellL`/`ellR`, `theta`), Lemma 19, the per-slot
  cost bounds `mFree1`/`mFree2` (Lemma 20, axiom-clean), the link-free block
  bound, and the affine-pencil / hyperbolic-quadruple facts (Lemmas 21, 24)
- `WtFloor24` — **(Tier 3, A4 §11)** the weight-24 standard-form walk (M1a):
  `slotCost` + soundness, the standard form `Sab` (Def 26), and Proposition 29
  `Sab_ge_6` (kernel `decide`, axiom-clean)
- `WtFloor24Bridge` — **(Tier 3, A4 §§10–11)** the weight-24 floor close (M1 —
  DONE): connects `costFromComps` to the `slotCost` machinery;
  `costFromComps_ge_12_of_blocks` discharges `MImFloorY{11,12}` analytically
- `WtFloor1618` — **(Tier 3, A4 §§12–13)** the light-orbit parity layer
  (`chainWeight_coset_even`, `blockCost_parity`, Prop 32
  `chainWeight_coset_ge12_of_floor10`) plus the spine reductions
  (`spine3_reduce`, `spine4_reduce`) that fix `LightFloor`'s cell frame.
-/
