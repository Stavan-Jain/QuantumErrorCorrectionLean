/-
# BB Chain Complex (Bivariate Bicycle CSS code) as a `HomologicalCode`

Given polynomial coefficient functions
`A B : (ZMod ℓ × ZMod m) → ZMod 2` representing elements of
`F_2[Z_ℓ × Z_m]`, we construct the length-3 chain complex underlying
the CSS code with check matrices

  H_X = [A | B]      (X-checks; matrix indexed by face-group entries × qubits)
  H_Z = [B^T | A^T]  (Z-checks; transposed)

In our convolution convention (defined below), the resulting code's
Z-checks are *reflected* compared to the literal transpose
(`b(g-h)` instead of `b(h-g)`).  Since the BB code is invariant under
the relabeling `g ↦ -g` on the group, this gives the same code up to
qubit relabeling — i.e. same parameters `(n, k, d)`.

The chain-complex law `∂₁ ∘ ∂₂ = 0` reduces to commutativity of
convolution on the abelian group `Z_ℓ × Z_m` combined with `char F_2 = 2`:
in char 2, `(a * b) + (b * a) = 2(a * b) = 0`.  Clean, no
transpose-juggling.

## What this file provides

* `conv (a b : G → ZMod 2) : G → ZMod 2` — convolution on abelian `G`, with the
  scoped infix `a ⋆ b`
* `poly[x^3 + y + y^2]` — scoped literal for the indicator-function polynomials
* `conv_comm`, `conv_assoc` — algebraic properties
* `bbBoundary1`, `bbBoundary2` — concrete boundary maps
* `bbChainComplex ℓ m A B : HomologicalCode` — the CSS chain complex
-/

import QEC.Stabilizer.Framework.Homological.Distance

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB

open scoped BigOperators

/-! ## Convolution on a finite abelian group

We work over `G = ZMod ℓ × ZMod m`, but for generality the convolution
definition only needs `G` to be a `Fintype` with `Sub`. -/

variable {G : Type} [Fintype G] [AddCommGroup G]

/-- Convolution of two `ZMod 2`-valued functions on a finite group `G`:
`(a * b)(g) = ∑_h a(h) · b(g - h)`. -/
def conv (a b : G → ZMod 2) : G → ZMod 2 :=
  fun g => ∑ h : G, a h * b (g - h)

/-- `a ⋆ b` is the convolution `conv a b` (the group-algebra product of `𝔽₂[G]`). Scoped
to `Quantum.Stabilizer.Homological.BB`: active inside that namespace, and elsewhere under
`open scoped Quantum.Stabilizer.Homological.BB`. Multiplicative precedence (`70`), so
`(a ⋆ b) g` needs its parentheses and `a ⋆ b + c` does not. The `simp`/`rw`/`unfold`
lists keep the bare name `conv`. -/
scoped infixl:70 " ⋆ " => conv

section PolyNotation

open Lean

/-! ### Polynomial literals

The polynomials `A`, `B` of a bivariate bicycle code are `ZMod 2`-valued indicator
functions on `G = ZMod ℓ × ZMod m`, the monomial `xᵃyᵇ` standing for the point `(a, b)`.
`poly[x^3 + y + y^2]` writes such a function the way the papers do and expands to exactly

```lean
fun g => if g = (3, 0) ∨ g = (0, 1) ∨ g = (0, 2) then 1 else 0
```

(the monomials in the written order, `∨` nested to the right as usual), the form the
kernel `decide`s downstream run through. Monomials are `1`, `x`, `y`, `x^i`, `y^j`,
`x^i*y^j` (with `x*y^j`, `x^i*y`, `x*y` for exponent `1`). Scoped like `⋆`. -/

declare_syntax_cat bbPoly (behavior := both)

/-- The constant monomial `1` (the point `(0, 0)`); other numerals are rejected. -/
scoped syntax num : bbPoly
/-- The monomial `x` or `x^i` (the point `(i, 0)`). -/
scoped syntax &"x" ("^" num)? : bbPoly
/-- The monomial `y` or `y^j` (the point `(0, j)`). -/
scoped syntax &"y" ("^" num)? : bbPoly
/-- The monomial `x^i*y^j` (the point `(i, j)`), either exponent optional. -/
scoped syntax &"x" ("^" num)? "*" &"y" ("^" num)? : bbPoly
/-- Polynomial sum, left-associative. -/
scoped syntax:65 bbPoly:65 " + " bbPoly:66 : bbPoly

/-- `poly[x^3 + y + y^2]` is the indicator function
`fun g => if g = (3, 0) ∨ g = (0, 1) ∨ g = (0, 2) then 1 else 0` of the monomials'
exponent points, for use as a bivariate-bicycle polynomial `G → ZMod 2`. Scoped to
`Quantum.Stabilizer.Homological.BB`.

The `+` is a union of *distinct* exponent points, not addition in `𝔽₂[G]`: the literal is
the polynomial it spells only when the written monomials are pairwise distinct modulo the
group orders. A syntactically repeated monomial is rejected, but a coincidence modulo the
orders cannot be seen at macro time — `poly[1 + x^6]` is `1 + x⁶` over `ZMod 12 × ZMod 6`
but the constant `1` (not `0`) over `ZMod 6 × ZMod 6` — so check the exponents against the
intended group. There is no literal for the zero polynomial; write `0`. -/
scoped syntax:max (name := polyLit) "poly[" bbPoly "]" : term

/-- The exponent points `(a, b)` of a `bbPoly` sum, in the written order. -/
partial def monomialsOf : TSyntax `bbPoly → MacroM (List (Nat × Nat))
  | `(bbPoly| $p + $q) => do return (← monomialsOf p) ++ (← monomialsOf q)
  | `(bbPoly| $n:num) =>
    if n.getNat == 1 then return [(0, 0)]
    else Macro.throwErrorAt n "expected the monomial 1"
  | `(bbPoly| x) => return [(1, 0)]
  | `(bbPoly| x ^ $a:num) => return [(a.getNat, 0)]
  | `(bbPoly| y) => return [(0, 1)]
  | `(bbPoly| y ^ $b:num) => return [(0, b.getNat)]
  | `(bbPoly| x * y) => return [(1, 1)]
  | `(bbPoly| x ^ $a:num * y) => return [(a.getNat, 1)]
  | `(bbPoly| x * y ^ $b:num) => return [(1, b.getNat)]
  | `(bbPoly| x ^ $a:num * y ^ $b:num) => return [(a.getNat, b.getNat)]
  | stx => Macro.throwErrorAt stx "expected a monomial 1, x^i, y^j, or x^i*y^j"

macro_rules
  | `(poly[$p]) => do
    let mons ← monomialsOf p
    if let some d := mons.find? fun m => mons.count m > 1 then
      Macro.throwErrorAt p
        s!"repeated monomial x^{d.1}*y^{d.2}: `+` in `poly[…]` is a union of distinct points"
    let g := mkIdent `g
    let some (last, init) := mons.getLast?.map fun l => (l, mons.dropLast) | Macro.throwUnsupported
    let mkEq : Nat × Nat → MacroM Term := fun (a, b) =>
      `($g = ($(quote a), $(quote b)))
    let mut disj : Term ← mkEq last
    for m in init.reverse do
      disj ← `($(← mkEq m) ∨ $disj)
    `(fun $g => if $disj then 1 else 0)

section PolyDelab

open PrettyPrinter Delaborator SubExpr

/-- A literal natural number: a raw literal or the `OfNat.ofNat` form numerals elaborate to. -/
private def numeral? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal k) => some k
  | _ =>
    if e.isAppOfArity ``OfNat.ofNat 3 then
      match e.getArg! 1 with
      | .lit (.natVal k) => some k
      | _ => none
    else none

/-- The exponent point of the disjunct `g = (a, b)` with `g` the loose bound variable `0`
and literal `a`, `b`. -/
private def exponentPoint? (e : Expr) : Option (Nat × Nat) := do
  guard (e.isAppOfArity ``Eq 3)
  guard (e.getArg! 1 == .bvar 0)
  let pt := e.getArg! 2
  guard (pt.isAppOfArity ``Prod.mk 4)
  let a ← numeral? (pt.getArg! 2)
  let b ← numeral? (pt.getArg! 3)
  return (a, b)

/-- The exponent points of a right-nested `∨` chain of such disjuncts. -/
private partial def exponentPoints? (e : Expr) : Option (List (Nat × Nat)) :=
  if e.isAppOfArity ``Or 2 then do
    let m ← exponentPoint? (e.getArg! 0)
    let ms ← exponentPoints? (e.getArg! 1)
    return m :: ms
  else
    (exponentPoint? e).map ([·])

/-- The `bbPoly` monomial for an exponent point. -/
private def monomialSyntax (m : Nat × Nat) : DelabM (TSyntax `bbPoly) := do
  let lit (k : Nat) : TSyntax `num := Syntax.mkNumLit (toString k)
  match m with
  | (0, 0) => `(bbPoly| 1)
  | (1, 0) => `(bbPoly| x)
  | (a, 0) => `(bbPoly| x ^ $(lit a))
  | (0, 1) => `(bbPoly| y)
  | (0, b) => `(bbPoly| y ^ $(lit b))
  | (1, 1) => `(bbPoly| x * y)
  | (a, 1) => `(bbPoly| x ^ $(lit a) * y)
  | (1, b) => `(bbPoly| x * y ^ $(lit b))
  | (a, b) => `(bbPoly| x ^ $(lit a) * y ^ $(lit b))

/-- Delaborate `fun g => if g = (a₁, b₁) ∨ … then 1 else 0` back to `poly[…]`. Fires only on
a lambda of exactly that shape, of type `ZMod ℓ × ZMod m → ZMod 2`, with literal exponents
and without a `Classical` decidability instance (a `classical` indicator would print the
same but re-elaborate to a different term); every other lambda is left to the default
printer. Scoped with the notation. -/
@[scoped delab lam]
def delabPolyLit : Delab :=
  whenPPOption getPPNotation <| whenNotPPOption getPPExplicit do
    let e ← getExpr
    let .lam _ dom body _ := e | failure
    unless body.isAppOfArity ``ite 5 do failure
    let dom ← Meta.whnfR dom
    unless dom.isAppOfArity ``Prod 2 && (dom.getArg! 0).isAppOfArity ``ZMod 1 &&
        (dom.getArg! 1).isAppOfArity ``ZMod 1 do failure
    let cod ← Meta.whnfR (body.getArg! 0)
    unless cod.isAppOfArity ``ZMod 1 && numeral? (cod.getArg! 0) == some 2 do failure
    if ((body.getArg! 2).find? fun c => c.isConstOf ``Classical.propDecidable).isSome then
      failure
    unless numeral? (body.getArg! 3) == some 1 && numeral? (body.getArg! 4) == some 0 do
      failure
    let some mons := exponentPoints? (body.getArg! 1) | failure
    let some first := mons.head? | failure
    let mut p ← monomialSyntax first
    for m in mons.tail do
      p ← `(bbPoly| $p + $(← monomialSyntax m))
    `(poly[$p])

end PolyDelab

end PolyNotation

@[simp] lemma conv_apply (a b : G → ZMod 2) (g : G) :
    (a ⋆ b) g = ∑ h : G, a h * b (g - h) := rfl

/-- Convolution is commutative on an abelian group. -/
lemma conv_comm (a b : G → ZMod 2) : a ⋆ b = b ⋆ a := by
  funext g
  simp only [conv_apply]
  -- ∑_h a h * b (g - h) = ∑_h b h * a (g - h)
  -- reindex via h ↦ g - h
  refine Finset.sum_bij' (fun h _ => g - h) (fun h _ => g - h)
    (fun h _ => Finset.mem_univ _) (fun h _ => Finset.mem_univ _)
    ?_ ?_ ?_
  · intro h _; simp
  · intro h _; simp
  · intro h _
    have : g - (g - h) = h := by simp
    rw [this, mul_comm]

/-- Convolution is associative. -/
lemma conv_assoc (a b c : G → ZMod 2) : (a ⋆ b) ⋆ c = a ⋆ (b ⋆ c) := by
  funext g
  -- We'll show both sides equal `∑_h ∑_k, a h * b k * c (g - h - k)`.
  -- LHS = ∑_h (conv a b) h * c (g - h) = ∑_h (∑_k a k * b (h - k)) * c (g - h)
  -- Reindex inner sum k ↦ h - k' so that the argument of b becomes k', and
  -- of a becomes h - k'.  Then renaming the outer variable to h_new = h - k'
  -- to align with RHS.  Cleanest: reindex jointly via the bijection
  -- (h, k) ↦ (h - k, k) on G × G.
  have lhs_expand :
      ((a ⋆ b) ⋆ c) g = ∑ h : G, ∑ k : G, a h * b k * c (g - h - k) := by
    simp only [conv_apply, Finset.sum_mul]
    -- LHS now: ∑ h, ∑ k, (a k * b (h - k)) * c (g - h)
    -- Goal: ∑ h, ∑ k, a h * b k * c (g - h - k)
    -- Reindex per outer h by k' = h - k, so a k = a (h - k'), b (h - k) = b k'
    -- Then swap outer/inner via sum_comm.
    rw [Finset.sum_comm]
    -- ∑ k, ∑ h, (a k * b (h - k)) * c (g - h)
    -- Now reindex inner h ↦ h + k:  (h - k) ↦ h, (g - h) ↦ g - h - k
    have step : ∀ k : G, (∑ h : G, a k * b (h - k) * c (g - h)) =
        ∑ h : G, a k * b h * c (g - k - h) := by
      intro k
      refine Finset.sum_bij' (fun h _ => h - k) (fun h _ => h + k)
        (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
      · intro h _
        change h - k + k = h
        abel
      · intro h _
        change h + k - k = h
        abel
      · intro h _
        have h1 : g - h = g - k - (h - k) := by abel
        rw [h1]
    rw [Finset.sum_congr rfl (fun k _ => step k)]
  have rhs_expand :
      (a ⋆ (b ⋆ c)) g = ∑ h : G, ∑ k : G, a h * b k * c (g - h - k) := by
    simp only [conv_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have : (g - h) - k = g - h - k := by abel
    rw [← this]
    ring
  rw [lhs_expand, rhs_expand]

/-- Convolution distributes over addition (left). -/
lemma conv_add_left (a b c : G → ZMod 2) :
    (a + b) ⋆ c = a ⋆ c + b ⋆ c := by
  funext g
  simp only [conv_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- Convolution distributes over addition (right). -/
lemma conv_add_right (a b c : G → ZMod 2) :
    a ⋆ (b + c) = a ⋆ b + a ⋆ c := by
  funext g
  simp only [conv_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- Convolution scales (left). -/
lemma conv_smul_left (s : ZMod 2) (a b : G → ZMod 2) :
    (s • a) ⋆ b = s • (a ⋆ b) := by
  funext g
  simp only [conv_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- Convolution scales (right). -/
lemma conv_smul_right (s : ZMod 2) (a b : G → ZMod 2) :
    a ⋆ (s • b) = s • (a ⋆ b) := by
  funext g
  simp only [conv_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1; funext h
  ring

/-- In char 2, for any commuting `a, b`, `conv a b + conv b a = 0`.
By commutativity of `conv`, this is just `2 (conv a b) = 0`. -/
lemma conv_add_swap_eq_zero (a b : G → ZMod 2) :
    a ⋆ b + b ⋆ a = 0 := by
  rw [conv_comm a b]
  ext g
  simp [Pi.add_apply, CharTwo.add_self_eq_zero]

/-- Convolving with a point mass on the left translates: `δ_a ⋆ b = b (· - a)`. -/
lemma conv_single_left [DecidableEq G] (a : G) (b : G → ZMod 2) :
    Pi.single a 1 ⋆ b = fun g => b (g - a) := by
  funext g
  rw [conv_apply, Finset.sum_eq_single a]
  · simp
  · intro h _ hne
    rw [Pi.single_eq_of_ne hne, zero_mul]
  · intro habs
    exact absurd (Finset.mem_univ a) habs

/-- Pointwise form of `conv_single_left` (avoids beta-redex residue when
rewriting at an applied occurrence). -/
@[simp] lemma conv_single_left_apply [DecidableEq G] (a : G) (b : G → ZMod 2)
    (g : G) :
    (Pi.single a 1 ⋆ b) g = b (g - a) := by
  rw [conv_single_left]

/-! ## Translation of chains -/

/-- Translation of a chain by a group element: `(translate c v) g = v (g + c)`. -/
def translate (c : G) (v : G → ZMod 2) : G → ZMod 2 := fun g => v (g + c)

omit [Fintype G] in
@[simp] lemma translate_apply (c : G) (v : G → ZMod 2) (g : G) :
    translate c v g = v (g + c) := rfl

/-- Convolution commutes with translation of the right factor. -/
lemma conv_translate (a v : G → ZMod 2) (c : G) :
    a ⋆ translate c v = translate c (a ⋆ v) := by
  funext g
  simp only [conv_apply, translate_apply]
  refine Finset.sum_congr rfl fun h _ => ?_
  congr 1
  abel_nf

/-! ## Boundary maps for BB chain complex

Cells:
* `C0 := G` (Z-stabilizer positions = "vertices")
* `C1 := G × Fin 2` (qubits, indexed by group element and L/R block)
* `C2 := G` (X-stabilizer positions = "faces")

Boundary maps:
* `∂₂(f) (h, 0) := conv A f h`,  `∂₂(f) (h, 1) := conv B f h`
* `∂₁(c) (g)    := conv B c_L g + conv A c_R g`
  where `c_L h = c (h, 0)`, `c_R h = c (h, 1)`.

Then `∂₁ ∘ ∂₂ = 0` reduces to `conv B (conv A f) + conv A (conv B f) = 0`
via `conv_assoc` and `conv_add_swap_eq_zero` (char 2 + commutativity). -/

variable (A B : G → ZMod 2)

/-- The "left half" of a 1-chain. -/
def leftHalf (c : G × Fin 2 → ZMod 2) : G → ZMod 2 := fun g => c (g, 0)

/-- The "right half" of a 1-chain. -/
def rightHalf (c : G × Fin 2 → ZMod 2) : G → ZMod 2 := fun g => c (g, 1)

/-- Underlying function of `∂₂`. -/
def bbBoundary2Fn (f : G → ZMod 2) : G × Fin 2 → ZMod 2 :=
  fun ⟨h, j⟩ => if j = 0 then (A ⋆ f) h else (B ⋆ f) h

/-- Underlying function of `∂₁`. -/
def bbBoundary1Fn (c : G × Fin 2 → ZMod 2) : G → ZMod 2 :=
  fun g => (B ⋆ leftHalf c) g + (A ⋆ rightHalf c) g

/-- `∂₂` as a `ZMod 2`-linear map. -/
noncomputable def bbBoundary2 :
    (G → ZMod 2) →ₗ[ZMod 2] (G × Fin 2 → ZMod 2) where
  toFun := bbBoundary2Fn A B
  map_add' f₁ f₂ := by
    ext ⟨h, j⟩
    have key : ∀ (p : G → ZMod 2),
        (∑ x : G, p x * ((f₁ + f₂) (h - x))) =
          (∑ x : G, p x * f₁ (h - x)) + (∑ x : G, p x * f₂ (h - x)) := by
      intro p
      simp [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    by_cases hj : j = 0
    · simp only [bbBoundary2Fn, hj, if_true, Pi.add_apply, conv_apply]
      exact key A
    · simp only [bbBoundary2Fn, hj, if_false, Pi.add_apply, conv_apply]
      exact key B
  map_smul' s f := by
    ext ⟨h, j⟩
    have key : ∀ (p : G → ZMod 2),
        (∑ x : G, p x * ((s • f) (h - x))) = s * (∑ x : G, p x * f (h - x)) := by
      intro p
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x _ => ?_); ring
    by_cases hj : j = 0
    · simp only [bbBoundary2Fn, hj, if_true, RingHom.id_apply, Pi.smul_apply,
        smul_eq_mul, conv_apply]
      exact key A
    · simp only [bbBoundary2Fn, hj, if_false, RingHom.id_apply, Pi.smul_apply,
        smul_eq_mul, conv_apply]
      exact key B

/-- `∂₁` as a `ZMod 2`-linear map. -/
noncomputable def bbBoundary1 :
    (G × Fin 2 → ZMod 2) →ₗ[ZMod 2] (G → ZMod 2) where
  toFun := bbBoundary1Fn A B
  map_add' c₁ c₂ := by
    ext g
    -- Goal: bbBoundary1Fn A B (c₁ + c₂) g = bbBoundary1Fn A B c₁ g + bbBoundary1Fn A B c₂ g
    -- Both sides expand via `conv` definition; reduces to ring arithmetic
    -- in `ZMod 2` after splitting sums.
    simp only [bbBoundary1Fn, leftHalf, rightHalf, conv_apply, Pi.add_apply]
    -- Now goal is a `(∑ + ∑) = (∑ + ∑) + (∑ + ∑)` shape — split sums.
    have hL : ∀ p : G → ZMod 2,
        (∑ h : G, p h * (c₁ (g - h, 0) + c₂ (g - h, 0))) =
        (∑ h : G, p h * c₁ (g - h, 0)) + (∑ h : G, p h * c₂ (g - h, 0)) := by
      intro p
      simp [mul_add, Finset.sum_add_distrib]
    have hR : ∀ p : G → ZMod 2,
        (∑ h : G, p h * (c₁ (g - h, 1) + c₂ (g - h, 1))) =
        (∑ h : G, p h * c₁ (g - h, 1)) + (∑ h : G, p h * c₂ (g - h, 1)) := by
      intro p
      simp [mul_add, Finset.sum_add_distrib]
    rw [hL B, hR A]
    ring
  map_smul' s c := by
    ext g
    simp only [bbBoundary1Fn, leftHalf, rightHalf, conv_apply, RingHom.id_apply,
      Pi.smul_apply, smul_eq_mul]
    have hL : (∑ h : G, B h * (s * c (g - h, 0))) =
        s * (∑ h : G, B h * c (g - h, 0)) := by
      simp only [Finset.mul_sum]; refine Finset.sum_congr rfl (fun x _ => ?_); ring
    have hR : (∑ h : G, A h * (s * c (g - h, 1))) =
        s * (∑ h : G, A h * c (g - h, 1)) := by
      simp only [Finset.mul_sum]; refine Finset.sum_congr rfl (fun x _ => ?_); ring
    rw [hL, hR]
    ring

/-- Translation of a 1-chain by a group element (qubit blocks fixed). -/
def translate1 (c : G) (v : G × Fin 2 → ZMod 2) : G × Fin 2 → ZMod 2 :=
  fun p => v (p.1 + c, p.2)

omit [Fintype G] in
@[simp] lemma translate1_apply (c : G) (v : G × Fin 2 → ZMod 2)
    (p : G × Fin 2) :
    translate1 c v p = v (p.1 + c, p.2) := rfl

omit [Fintype G] in
lemma leftHalf_translate1 (c : G) (v : G × Fin 2 → ZMod 2) :
    leftHalf (translate1 c v) = translate c (leftHalf v) := rfl

omit [Fintype G] in
lemma rightHalf_translate1 (c : G) (v : G × Fin 2 → ZMod 2) :
    rightHalf (translate1 c v) = translate c (rightHalf v) := rfl

/-- `∂₁` is translation-equivariant. -/
lemma bbBoundary1Fn_translate1 (c : G) (v : G × Fin 2 → ZMod 2) :
    bbBoundary1Fn A B (translate1 c v) = translate c (bbBoundary1Fn A B v) := by
  funext g
  rw [bbBoundary1Fn, leftHalf_translate1, rightHalf_translate1,
    conv_translate, conv_translate]
  rfl

/-- `∂₂` is translation-equivariant. -/
lemma bbBoundary2Fn_translate (c : G) (f : G → ZMod 2) :
    bbBoundary2Fn A B (translate c f) = translate1 c (bbBoundary2Fn A B f) := by
  funext p
  obtain ⟨h, j⟩ := p
  by_cases hj : j = 0
  · subst hj
    change (A ⋆ translate c f) h = bbBoundary2Fn A B f (h + c, 0)
    rw [conv_translate]
    rfl
  · have hj1 : j = 1 := by omega
    subst hj1
    change (B ⋆ translate c f) h = bbBoundary2Fn A B f (h + c, 1)
    rw [conv_translate]
    rfl

/-- `rfl` bridge from the LinearMap `∂₂` to its computable underlying function. -/
@[simp] lemma bbBoundary2_apply (f : G → ZMod 2) :
    bbBoundary2 A B f = bbBoundary2Fn A B f := rfl

/-- `rfl` bridge from the LinearMap `∂₁` to its computable underlying function. -/
@[simp] lemma bbBoundary1_apply (c : G × Fin 2 → ZMod 2) :
    bbBoundary1 A B c = bbBoundary1Fn A B c := rfl

/-- `∂₂` (computable form) is additive. -/
lemma bbBoundary2Fn_add (f₁ f₂ : G → ZMod 2) :
    bbBoundary2Fn A B (f₁ + f₂) = bbBoundary2Fn A B f₁ + bbBoundary2Fn A B f₂ := by
  have h := map_add (bbBoundary2 A B) f₁ f₂
  simpa [bbBoundary2_apply] using h

/-- `∂₁` (computable form) is additive. -/
lemma bbBoundary1Fn_add (c₁ c₂ : G × Fin 2 → ZMod 2) :
    bbBoundary1Fn A B (c₁ + c₂) = bbBoundary1Fn A B c₁ + bbBoundary1Fn A B c₂ := by
  have h := map_add (bbBoundary1 A B) c₁ c₂
  simpa [bbBoundary1_apply] using h

/-- The chain-complex law `∂₁ ∘ ∂₂ = 0`. -/
lemma bbBoundary_comp : (bbBoundary1 A B).comp (bbBoundary2 A B) = 0 := by
  refine LinearMap.ext (fun f => ?_)
  ext g
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply]
  change bbBoundary1Fn A B (bbBoundary2Fn A B f) g = 0
  unfold bbBoundary1Fn bbBoundary2Fn leftHalf rightHalf
  -- ∂₁(∂₂ f)(g) = conv B (h ↦ conv A f h) g + conv A (h ↦ conv B f h) g
  have hL : (fun h => (if (0 : Fin 2) = 0 then (A ⋆ f) h else (B ⋆ f) h)) =
      A ⋆ f := by funext h; simp
  have hR : (fun h => (if (1 : Fin 2) = 0 then (A ⋆ f) h else (B ⋆ f) h)) =
      B ⋆ f := by funext h; simp
  rw [hL, hR]
  -- Goal: conv B (conv A f) g + conv A (conv B f) g = 0
  -- Use conv_assoc (right-to-left) to fold: conv B (conv A f) = conv (conv B A) f
  rw [← conv_assoc B A f, ← conv_assoc A B f]
  -- Goal: conv (conv B A) f g + conv (conv A B) f g = 0
  rw [conv_comm B A]
  -- Goal: conv (conv A B) f g + conv (conv A B) f g = 0
  -- That's `x + x = 0` in `ZMod 2` (i.e. `char F_2 = 2`).
  exact CharTwo.add_self_eq_zero _

/-- The chain-complex law in computable form: `∂₁ (∂₂ f) = 0`. -/
lemma bbBoundaryFn_comp (f : G → ZMod 2) :
    bbBoundary1Fn A B (bbBoundary2Fn A B f) = 0 := by
  have h := LinearMap.congr_fun (bbBoundary_comp A B) f
  simpa [bbBoundary1_apply, bbBoundary2_apply] using h

/-! ## Packaging as a `HomologicalCode`

Given `[Fintype G] [DecidableEq G] [AddCommGroup G]` and polynomials
`A, B : G → ZMod 2`, build the chain complex
`C0 = G,  C1 = G × Fin 2,  C2 = G`
with `bbBoundary1`, `bbBoundary2`. -/

variable [DecidableEq G]

/-- Number of qubits = `2 * Fintype.card G`. -/
def bbNumQubits (G : Type) [Fintype G] : ℕ := 2 * Fintype.card G

/-- Bijection between `G × Fin 2` and `Fin (bbNumQubits G)`. -/
noncomputable def bbEdgeEquiv :
    (G × Fin 2) ≃ Fin (bbNumQubits G) := by
  classical
  -- Use the equiv G × Fin 2 ≃ Fin (card G) × Fin 2 ≃ Fin (2 * card G)
  refine (((Fintype.equivFin G).prodCongr (Equiv.refl (Fin 2))).trans
    (finProdFinEquiv (m := Fintype.card G) (n := 2))).trans ?_
  -- Fin (card G * 2) → Fin (2 * card G)
  exact finCongr (by unfold bbNumQubits; ring)

omit [AddCommGroup G] [DecidableEq G] in
lemma bbCard_C1 :
    Fintype.card (G × Fin 2) = bbNumQubits G := by
  unfold bbNumQubits
  rw [Fintype.card_prod, Fintype.card_fin, mul_comm]

/-- The BB chain complex packaged as a `HomologicalCode`. -/
noncomputable def bbChainComplex (A B : G → ZMod 2) : HomologicalCode where
  C0 := G
  C1 := G × Fin 2
  C2 := G
  decEq0 := inferInstance
  decEq1 := inferInstance
  decEq2 := inferInstance
  fin0 := inferInstance
  fin1 := inferInstance
  fin2 := inferInstance
  boundary1 := bbBoundary1 A B
  boundary2 := bbBoundary2 A B
  boundary_comp := bbBoundary_comp A B
  numQubits := bbNumQubits G
  numQubits_eq := bbCard_C1
  edgeEquiv := bbEdgeEquiv

/-! ## Round-trip tests

`poly[…]` expands to exactly the indicator-function normal form, and `⋆` to `conv`. -/

section RoundTrip

example :
    (poly[x^3 + y + y^2] : ZMod 12 × ZMod 6 → ZMod 2) =
      fun g => if g = (3, 0) ∨ g = (0, 1) ∨ g = (0, 2) then 1 else 0 :=
  rfl

example :
    (poly[y^3 + x + x^2] : ZMod 12 × ZMod 6 → ZMod 2) =
      fun g => if g = (0, 3) ∨ g = (1, 0) ∨ g = (2, 0) then 1 else 0 :=
  rfl

example :
    (poly[1 + x^2] : ZMod 12 × ZMod 6 → ZMod 2) =
      fun g => if g = (0, 0) ∨ g = (2, 0) then 1 else 0 :=
  rfl

example : (poly[x^6] : ZMod 12 × ZMod 6 → ZMod 2) = fun g => if g = (6, 0) then 1 else 0 :=
  rfl

example :
    (poly[x*y^2 + x^2*y + x*y] : ZMod 3 × ZMod 3 → ZMod 2) =
      fun g => if g = (1, 2) ∨ g = (2, 1) ∨ g = (1, 1) then 1 else 0 :=
  rfl

example (a b : G → ZMod 2) : a ⋆ b = conv a b := rfl

example (a b c : G → ZMod 2) : a ⋆ b ⋆ c = conv (conv a b) c := rfl

example (a b : G → ZMod 2) (g : G) : (a ⋆ b) g = conv a b g := rfl

open Lean Elab Command in
/-- Display test: elaborate `stx` and check that its pretty-printed text is `expected`
(`exact := false`: contains `expected`). Run through `run_cmd` so no `#`-command is needed. -/
private def checkDisplay (stx : Syntax) (expected : String) (exact : Bool := true) :
    CommandElabM Unit :=
  liftTermElabM do
    let e ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVarsNoPostponing
    let s := toString (← Meta.ppExpr (← instantiateMVars e))
    unless (if exact then s == expected else (s.splitOn expected).length > 1) do
      throwError "display test failed:{indentD s}\nexpected{indentD expected}"

run_cmd do
  checkDisplay (← `((poly[x^3 + y + y^2] : ZMod 12 × ZMod 6 → ZMod 2)))
    "poly[x^3 + y + y^2]"
run_cmd do
  checkDisplay (← `((poly[1 + x*y^2] : ZMod 3 × ZMod 3 → ZMod 2))) "poly[1 + x*y^2]"
-- an indicator of the same shape over another type is not a bivariate-bicycle polynomial
run_cmd do
  checkDisplay (← `(fun p : ℕ × ℕ => if p = (1, 2) ∨ p = (0, 3) then (1 : ℕ) else 0))
    "if p = (1, 2) ∨ p = (0, 3) then 1 else 0" (exact := false)
run_cmd do
  checkDisplay (← `(fun (a b : ZMod 12 × ZMod 6 → ZMod 2) => a ⋆ b))
    "a ⋆ b" (exact := false)

end RoundTrip

end BB
end Homological
end Stabilizer
end Quantum
