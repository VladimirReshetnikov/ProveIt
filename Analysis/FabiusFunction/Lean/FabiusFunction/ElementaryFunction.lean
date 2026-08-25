import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Topology.GDelta.Basic

/-!
# Elementary functions of one real variable and their analytic locus

This file is independent of the Fabius function; it isolates the only property
of the class of elementary functions that the non-elementarity proof needs.

## The class

`Fabius.IsElementary` is an inductive predicate on `ℝ → ℝ` generating the
class described at <https://en.wikipedia.org/wiki/Elementary_function>: the
smallest class containing the constants and the identity and closed under
sums, products, negation, reciprocals, Mathlib real powers with a fixed
exponent (hence principal `n`-th roots on nonnegative inputs for positive
`n`), `Real.exp`, `Real.log`, `Real.sin`, `Real.cos`, `Real.arcsin` and
`Real.arctan`.  Classical odd roots are derived separately through
`Fabius.IsElementary.signedRpow` and checked by `Fabius.signedRoot_pow`.
Closure under *composition* is not a constructor: it is proved in
`Fabius.IsElementary.comp`, by induction on the derivation of the outer
function.  Polynomials, rational functions, `Real.sqrt`, `|·|`, `Real.tan`,
the hyperbolic functions, `Real.arccos` and `Real.arsinh` are all derived.

Every generator here is a *total* function `ℝ → ℝ`: `Mathlib` gives `x⁻¹`,
`Real.log`, `Real.rpow` and `Real.arcsin` junk values outside their classical
domains.  This makes the class *larger*, and hence the non-elementarity
theorem *stronger*: a classical elementary expression that happens to be well
formed on an open set agrees there with the total function built by the same
derivation, because the junk values are never consulted.

## The theorem

`Fabius.IsElementary.dense_analyticLocus`: for an elementary `f` the set

`Fabius.analyticLocus f = {x | AnalyticAt ℝ f x}`

is a *dense* open subset of `ℝ`.  Density — rather than "analytic
everywhere" — is exactly right: `fun x => x⁻¹` and `|·|` are elementary and
fail to be analytic at `0`.

Equivalently, the exceptional set is nowhere dense.  The reusable obstruction
`Fabius.IsElementary.not_eqOn_of_interior_nonempty` packages the consequence
used by the Fabius application: an elementary function cannot agree on a set
with nonempty interior with a function that is nonanalytic throughout that
interior.

The proof is a single induction.  The interesting step is the unary one, and
it is isolated as `Fabius.dense_analyticLocus_comp`: if `g` is analytic off a
finite set `B` of *values*, and `f` has dense analytic locus, then `g ∘ f`
has dense analytic locus.  At a point `x₀` where `f` is analytic, either `f`
is constant equal to some `c ∈ B` near `x₀` — and then `g ∘ f` is constant,
hence analytic, at `x₀` itself — or, by the isolated-zeros theorem applied to
`f - c` for each of the finitely many `c ∈ B`, the value `f t` avoids `B` for
all `t` in some punctured neighbourhood of `x₀`, and `g ∘ f` is analytic at
each such `t`.

## What is not claimed

For positive `n`, `IsElementary.rpow` gives the principal `n`-th root on
nonnegative inputs.  Bare `Real.rpow` is not the signed odd root on a negative
base.  For positive odd `n`, the classical signed root on all of `ℝ` is instead
represented by `(x * |x|⁻¹) * |x| ^ (1 / n)`:
`IsElementary.signedRpow` proves that this expression is elementary, and
`signedRoot_pow` verifies that its `n`-th power is `x`.  The formula also gives
zero at `x = 0` because its sign factor is zero there.  The class is not closed
under passage to an arbitrary algebraic function: `IsElementary` has no
constructor for a continuous branch of `P (x, y) = 0` with elementary
coefficients.
-/

set_option autoImplicit false

open Filter Set
open scoped Topology ContDiff

namespace Fabius

/-! ## Analyticity of the generators

Every generator below is real analytic away from a finite set of arguments.
`Mathlib` states these facts as `ContDiffAt ℝ n` for `n : WithTop ℕ∞`; taking
`n = ω` and applying `ContDiffAt.analyticAt` turns them into analyticity. -/

/-- `Real.log` is real analytic at every nonzero real number.  It is analytic
at negative arguments as well, because `Mathlib`'s `Real.log` is even. -/
theorem analyticAt_log_of_ne_zero {x : ℝ} (hx : x ≠ 0) : AnalyticAt ℝ Real.log x :=
  ((Real.contDiffAt_log (n := ω)).2 hx).analyticAt

/-- `fun t => t ^ r` is real analytic at every nonzero real number, for every
real exponent `r`.  At a negative base `Mathlib`'s `Real.rpow` equals
`|t| ^ r * cos (π r)`, which is analytic there too. -/
theorem analyticAt_rpow_const {x : ℝ} (hx : x ≠ 0) (r : ℝ) :
    AnalyticAt ℝ (fun t : ℝ => t ^ r) x :=
  (Real.contDiffAt_rpow_const_of_ne (p := r) (n := ω) hx).analyticAt

/-- `Real.sqrt` is real analytic at every nonzero real number. -/
theorem analyticAt_sqrt_of_ne_zero {x : ℝ} (hx : x ≠ 0) : AnalyticAt ℝ Real.sqrt x :=
  (Real.contDiffAt_sqrt (n := ω) hx).analyticAt

/-- `Real.arctan` is real analytic at every real number. -/
theorem analyticAt_arctan (x : ℝ) : AnalyticAt ℝ Real.arctan x :=
  (Real.contDiff_arctan (n := ω)).contDiffAt.analyticAt

/-- `Real.arcsin` is real analytic away from the two branch points `±1`. -/
theorem analyticAt_arcsin {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) :
    AnalyticAt ℝ Real.arcsin x :=
  (Real.contDiffAt_arcsin (n := ω) h₁ h₂).analyticAt

/-! ## The class of elementary functions -/

/-- Elementary functions of one real variable, in the sense of
<https://en.wikipedia.org/wiki/Elementary_function>: the smallest class of
functions `ℝ → ℝ` containing the constants and the identity and closed under
sums, products, negation, reciprocals, fixed real powers, the exponential,
the logarithm, the two basic trigonometric functions and two inverse
trigonometric functions.

Closure under composition is not assumed; it is the theorem
`Fabius.IsElementary.comp`.  Subtraction, division, natural powers, principal
`n`-th roots on nonnegative inputs for positive `n`, classical signed odd
roots, `Real.sqrt`, the absolute value, `Real.tan`, the hyperbolic functions,
`Real.arccos`, `Real.arsinh` and all polynomial and rational functions are
derived below. -/
inductive IsElementary : (ℝ → ℝ) → Prop
  /-- Every constant function is elementary. -/
  | const (c : ℝ) : IsElementary fun _ => c
  /-- The identity is elementary. -/
  | id : IsElementary fun x => x
  /-- Elementary functions are closed under addition. -/
  | add {f g : ℝ → ℝ} : IsElementary f → IsElementary g → IsElementary fun x => f x + g x
  /-- Elementary functions are closed under multiplication. -/
  | mul {f g : ℝ → ℝ} : IsElementary f → IsElementary g → IsElementary fun x => f x * g x
  /-- Elementary functions are closed under negation. -/
  | neg {f : ℝ → ℝ} : IsElementary f → IsElementary fun x => -f x
  /-- Elementary functions are closed under taking reciprocals. -/
  | inv {f : ℝ → ℝ} : IsElementary f → IsElementary fun x => (f x)⁻¹
  /-- Elementary functions are closed under Mathlib's real power with a fixed
  exponent.  At a nonnegative input and for positive `n`, taking
  `r = (n : ℝ)⁻¹` gives the principal `n`-th root; negative inputs follow
  `Real.rpow`'s cosine convention instead. -/
  | rpow {f : ℝ → ℝ} (r : ℝ) : IsElementary f → IsElementary fun x => f x ^ r
  /-- Elementary functions are closed under the exponential. -/
  | exp {f : ℝ → ℝ} : IsElementary f → IsElementary fun x => Real.exp (f x)
  /-- Elementary functions are closed under the logarithm. -/
  | log {f : ℝ → ℝ} : IsElementary f → IsElementary fun x => Real.log (f x)
  /-- Elementary functions are closed under the sine. -/
  | sin {f : ℝ → ℝ} : IsElementary f → IsElementary fun x => Real.sin (f x)
  /-- Elementary functions are closed under the cosine. -/
  | cos {f : ℝ → ℝ} : IsElementary f → IsElementary fun x => Real.cos (f x)
  /-- Elementary functions are closed under the arcsine. -/
  | arcsin {f : ℝ → ℝ} : IsElementary f → IsElementary fun x => Real.arcsin (f x)
  /-- Elementary functions are closed under the arctangent. -/
  | arctan {f : ℝ → ℝ} : IsElementary f → IsElementary fun x => Real.arctan (f x)

namespace IsElementary

/-- The class of elementary functions is closed under composition.  This is a
theorem rather than a constructor: every constructor commutes with
precomposition, so the statement follows by induction on the derivation of the
outer function. -/
theorem comp {f h : ℝ → ℝ} (hf : IsElementary f) (hh : IsElementary h) :
    IsElementary fun x => f (h x) := by
  induction hf with
  | const c => exact IsElementary.const c
  | id => exact hh
  | add _ _ ih₁ ih₂ => exact ih₁.add ih₂
  | mul _ _ ih₁ ih₂ => exact ih₁.mul ih₂
  | neg _ ih => exact ih.neg
  | inv _ ih => exact ih.inv
  | rpow r _ ih => exact ih.rpow r
  | exp _ ih => exact ih.exp
  | log _ ih => exact ih.log
  | sin _ ih => exact ih.sin
  | cos _ ih => exact ih.cos
  | arcsin _ ih => exact ih.arcsin
  | arctan _ ih => exact ih.arctan

/-- Elementary functions are closed under subtraction. -/
theorem sub {f g : ℝ → ℝ} (hf : IsElementary f) (hg : IsElementary g) :
    IsElementary fun x => f x - g x := by
  have h : (fun x => f x - g x) = fun x => f x + -g x := by
    funext x; ring
  rw [h]
  exact hf.add hg.neg

/-- Elementary functions are closed under division. -/
theorem div {f g : ℝ → ℝ} (hf : IsElementary f) (hg : IsElementary g) :
    IsElementary fun x => f x / g x := by
  have h : (fun x => f x / g x) = fun x => f x * (g x)⁻¹ := by
    funext x; rw [div_eq_mul_inv]
  rw [h]
  exact hf.mul hg.inv

/-- Elementary functions are closed under natural powers. -/
theorem npow {f : ℝ → ℝ} (hf : IsElementary f) (n : ℕ) :
    IsElementary fun x => f x ^ n := by
  induction n with
  | zero =>
      have h : (fun x => f x ^ (0 : ℕ)) = fun _ : ℝ => (1 : ℝ) := by
        funext x; exact pow_zero _
      rw [h]
      exact IsElementary.const 1
  | succ n ih =>
      have h : (fun x => f x ^ (n + 1)) = fun x => f x ^ n * f x := by
        funext x; exact pow_succ _ _
      rw [h]
      exact ih.mul hf

/-- Multiplication by a constant preserves elementarity. -/
theorem const_mul {f : ℝ → ℝ} (hf : IsElementary f) (c : ℝ) :
    IsElementary fun x => c * f x :=
  (IsElementary.const c).mul hf

/-- Every polynomial function is elementary. -/
theorem polynomial (p : Polynomial ℝ) : IsElementary fun x => p.eval x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      have h : (fun x => (p + q).eval x) = fun x => p.eval x + q.eval x := by
        funext x; exact Polynomial.eval_add
      rw [h]
      exact hp.add hq
  | monomial n a =>
      have h : (fun x => (Polynomial.monomial n a).eval x) = fun x => a * x ^ n := by
        funext x; exact Polynomial.eval_monomial
      rw [h]
      exact (IsElementary.id.npow n).const_mul a

/-- `Real.sqrt ∘ f` is elementary whenever `f` is: `Mathlib`'s square root is
the real power `t ↦ t ^ (1 / 2 : ℝ)`; both sides totalize to zero at negative
arguments. -/
theorem sqrt {f : ℝ → ℝ} (hf : IsElementary f) :
    IsElementary fun x => Real.sqrt (f x) := by
  have h : (fun x => Real.sqrt (f x)) = fun x => f x ^ (1 / (2 : ℝ)) := by
    funext x; exact Real.sqrt_eq_rpow _
  rw [h]
  exact hf.rpow _

/-- The absolute value of an elementary function is elementary. -/
theorem abs {f : ℝ → ℝ} (hf : IsElementary f) : IsElementary fun x => |f x| := by
  have h : (fun x => |f x|) = fun x => Real.sqrt (f x ^ 2) := by
    funext x; exact (Real.sqrt_sq_eq_abs _).symm
  rw [h]
  exact (hf.npow 2).sqrt

/-- The *signed* real power `x ↦ (f x / |f x|) * |f x| ^ r`.

For positive `n`, the constructor `IsElementary.rpow` with
`r = (n : ℝ)⁻¹` supplies the usual `n`-th roots only on `[0, ∞)`:
`Mathlib`'s `Real.rpow` at a negative base is
`|x| ^ r * cos (π r)`, so `(-8 : ℝ) ^ (1/3 : ℝ) = 1`, not `-2`.  When
`r = (n : ℝ)⁻¹` for odd `n`, the expression below is the classical odd root,
and it is elementary by a different derivation — division, absolute value,
real power.
`Fabius.signedRoot_pow` checks that for odd `n` its `n`-th power really is
the identity. -/
theorem signedRpow {f : ℝ → ℝ} (hf : IsElementary f) (r : ℝ) :
    IsElementary fun x => f x / |f x| * |f x| ^ r :=
  (hf.div hf.abs).mul (hf.abs.rpow r)

/-- Elementary functions are closed under the tangent. -/
theorem tan {f : ℝ → ℝ} (hf : IsElementary f) :
    IsElementary fun x => Real.tan (f x) := by
  have h : (fun x => Real.tan (f x)) = fun x => Real.sin (f x) / Real.cos (f x) := by
    funext x; exact Real.tan_eq_sin_div_cos _
  rw [h]
  exact hf.sin.div hf.cos

/-- Elementary functions are closed under the hyperbolic sine. -/
theorem sinh {f : ℝ → ℝ} (hf : IsElementary f) :
    IsElementary fun x => Real.sinh (f x) := by
  have h : (fun x => Real.sinh (f x))
      = fun x => (Real.exp (f x) - Real.exp (-f x)) / 2 := by
    funext x; exact Real.sinh_eq _
  rw [h]
  exact (hf.exp.sub hf.neg.exp).div (IsElementary.const 2)

/-- Elementary functions are closed under the hyperbolic cosine. -/
theorem cosh {f : ℝ → ℝ} (hf : IsElementary f) :
    IsElementary fun x => Real.cosh (f x) := by
  have h : (fun x => Real.cosh (f x))
      = fun x => (Real.exp (f x) + Real.exp (-f x)) / 2 := by
    funext x; exact Real.cosh_eq _
  rw [h]
  exact (hf.exp.add hf.neg.exp).div (IsElementary.const 2)

/-- Elementary functions are closed under the hyperbolic tangent. -/
theorem tanh {f : ℝ → ℝ} (hf : IsElementary f) :
    IsElementary fun x => Real.tanh (f x) := by
  have h : (fun x => Real.tanh (f x))
      = fun x => Real.sinh (f x) / Real.cosh (f x) := by
    funext x; exact Real.tanh_eq_sinh_div_cosh _
  rw [h]
  exact hf.sinh.div hf.cosh

/-- Elementary functions are closed under the arccosine. -/
theorem arccos {f : ℝ → ℝ} (hf : IsElementary f) :
    IsElementary fun x => Real.arccos (f x) := by
  have h : (fun x => Real.arccos (f x)) = fun x => Real.pi / 2 - Real.arcsin (f x) := by
    funext x; exact Real.arccos_eq_pi_div_two_sub_arcsin _
  rw [h]
  exact (IsElementary.const (Real.pi / 2)).sub hf.arcsin

/-- Variable exponents, at a positive base.  Where `f` is positive,
`f ^ g` is the elementary function `exp (log f * g)`; in particular
`fun x => x ^ x` is elementary on any set where the base is positive.

The unrestricted two-variable power is not a constructor of `IsElementary`.
The simple positive-base formula below does not cover negative bases, where
`Mathlib`'s `Real.rpow` is sign-dependent
(`x ^ y = |x| ^ y * cos (π y)`), and its zero-base convention is exceptional.
On an interval on which `f` has fixed nonzero sign, however, `f ^ g` does agree
with a member of the class, so nothing is lost for the purposes of
`Fabius.not_isElementary_eqOn`. -/
theorem rpow_of_pos {f g : ℝ → ℝ} (hf : IsElementary f) (hg : IsElementary g)
    (hpos : ∀ x, 0 < f x) : IsElementary fun x => f x ^ g x := by
  have h : (fun x => f x ^ g x) = fun x => Real.exp (Real.log (f x) * g x) := by
    funext x; exact Real.rpow_def_of_pos (hpos x) _
  rw [h]
  exact (hf.log.mul hg).exp

/-- Elementary functions are closed under the inverse hyperbolic sine. -/
theorem arsinh {f : ℝ → ℝ} (hf : IsElementary f) :
    IsElementary fun x => Real.arsinh (f x) := by
  have h : (fun x => Real.arsinh (f x))
      = fun x => Real.log (f x + Real.sqrt (1 + f x ^ 2)) := rfl
  rw [h]
  exact (hf.add ((IsElementary.const 1).add (hf.npow 2)).sqrt).log

end IsElementary

/-- For odd `n`, the elementary expression `t ↦ (t / |t|) * |t| ^ (n : ℝ)⁻¹`
of `Fabius.IsElementary.signedRpow` is a genuine real `n`-th root: raising it
to the `n`-th power returns the argument, at negative arguments and at zero as
well as at positive ones.

This substantiates closure under classical odd roots.  The constructor
`IsElementary.rpow` on its own does not give it: with `Mathlib`'s convention
`t ^ (n : ℝ)⁻¹ = |t| ^ (n : ℝ)⁻¹ * cos (π / n)` for `t < 0`, whose `n`-th
power is not `t`. -/
theorem signedRoot_pow {n : ℕ} (hn : Odd n) (t : ℝ) :
    (t / |t| * |t| ^ ((n : ℝ))⁻¹) ^ n = t := by
  have hn0 : n ≠ 0 := hn.pos.ne'
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have ht0 : t ≠ 0 := ne_of_lt ht
    have habs : |t| = -t := abs_of_neg ht
    have hnonneg : (0 : ℝ) ≤ -t := le_of_lt (neg_pos.mpr ht)
    have hdiv : t / |t| = -1 := by rw [habs, div_neg, div_self ht0]
    rw [hdiv, habs, neg_one_mul, hn.neg_pow,
      ← Real.rpow_natCast ((-t) ^ ((n : ℝ))⁻¹) n, ← Real.rpow_mul hnonneg,
      inv_mul_cancel₀ hnR, Real.rpow_one, neg_neg]
  · subst ht
    simp [Real.zero_rpow (inv_ne_zero hnR), zero_pow hn0]
  · have habs : |t| = t := abs_of_pos ht
    have hdiv : t / |t| = 1 := by rw [habs, div_self (ne_of_gt ht)]
    rw [hdiv, habs, one_mul, ← Real.rpow_natCast (t ^ ((n : ℝ))⁻¹) n,
      ← Real.rpow_mul (le_of_lt ht), inv_mul_cancel₀ hnR, Real.rpow_one]

/-! ## Named elementary functions

Spelled out for the record: each standard function of the elementary calculus
belongs to the class in its own right, not merely as a constructor applied to
an elementary argument. -/

/-- The identity is elementary. -/
theorem isElementary_id : IsElementary fun x : ℝ => x := IsElementary.id

/-- The reciprocal is elementary. -/
theorem isElementary_inv : IsElementary fun x : ℝ => x⁻¹ := IsElementary.id.inv

/-- Every Mathlib real-power function with a fixed exponent is elementary.
At nonnegative inputs and for positive `n`, `r = (n : ℝ)⁻¹` gives the
principal `n`-th root; classical odd roots on all of `ℝ` are supplied
separately by `IsElementary.signedRpow` and verified by `signedRoot_pow`. -/
theorem isElementary_rpow (r : ℝ) : IsElementary fun x : ℝ => x ^ r :=
  IsElementary.id.rpow r

/-- `Real.exp` is elementary. -/
theorem isElementary_exp : IsElementary Real.exp := IsElementary.id.exp

/-- `Real.log` is elementary. -/
theorem isElementary_log : IsElementary Real.log := IsElementary.id.log

/-- `Real.sin` is elementary. -/
theorem isElementary_sin : IsElementary Real.sin := IsElementary.id.sin

/-- `Real.cos` is elementary. -/
theorem isElementary_cos : IsElementary Real.cos := IsElementary.id.cos

/-- `Real.tan` is elementary. -/
theorem isElementary_tan : IsElementary Real.tan := IsElementary.id.tan

/-- `Real.arcsin` is elementary. -/
theorem isElementary_arcsin : IsElementary Real.arcsin := IsElementary.id.arcsin

/-- `Real.arccos` is elementary. -/
theorem isElementary_arccos : IsElementary Real.arccos := IsElementary.id.arccos

/-- `Real.arctan` is elementary. -/
theorem isElementary_arctan : IsElementary Real.arctan := IsElementary.id.arctan

/-- `Real.sinh` is elementary. -/
theorem isElementary_sinh : IsElementary Real.sinh := IsElementary.id.sinh

/-- `Real.cosh` is elementary. -/
theorem isElementary_cosh : IsElementary Real.cosh := IsElementary.id.cosh

/-- `Real.tanh` is elementary. -/
theorem isElementary_tanh : IsElementary Real.tanh := IsElementary.id.tanh

/-- `Real.arsinh` is elementary. -/
theorem isElementary_arsinh : IsElementary Real.arsinh := IsElementary.id.arsinh

/-- `Real.sqrt` is elementary. -/
theorem isElementary_sqrt : IsElementary Real.sqrt := IsElementary.id.sqrt

/-- The absolute value is elementary. -/
theorem isElementary_abs : IsElementary fun x : ℝ => |x| := IsElementary.id.abs

/-- A representative closed-form expression, to exercise the definition. -/
example : IsElementary fun x : ℝ =>
    Real.exp (Real.sin (x ^ 2 + 1)) / (1 + x ^ 2)
      + Real.log |x| * Real.arctan (Real.sqrt (1 - x ^ 2)) := by
  have h1 : IsElementary fun x : ℝ => x ^ 2 + 1 :=
    (IsElementary.id.npow 2).add (IsElementary.const 1)
  have h2 : IsElementary fun x : ℝ => 1 + x ^ 2 :=
    (IsElementary.const 1).add (IsElementary.id.npow 2)
  have h3 : IsElementary fun x : ℝ => 1 - x ^ 2 :=
    (IsElementary.const 1).sub (IsElementary.id.npow 2)
  exact (h1.sin.exp.div h2).add (IsElementary.id.abs.log.mul h3.sqrt.arctan)

/-! ## The analytic locus -/

/-- The set of points at which `f` is real analytic. -/
def analyticLocus (f : ℝ → ℝ) : Set ℝ := {x : ℝ | AnalyticAt ℝ f x}

/-- Membership in `analyticLocus f` is definitionally real analyticity of `f`
at the given point. -/
@[simp]
theorem mem_analyticLocus {f : ℝ → ℝ} {x : ℝ} :
    x ∈ analyticLocus f ↔ AnalyticAt ℝ f x := Iff.rfl

/-- Real analyticity at a point is an open condition, so the analytic locus is
an open set. -/
theorem isOpen_analyticLocus (f : ℝ → ℝ) : IsOpen (analyticLocus f) :=
  isOpen_analyticAt ℝ f

/-- If `f` has dense analytic locus and `g` is analytic at every value outside
a finite set `B`, then `g ∘ f` has dense analytic locus.

This single lemma covers every unary generator: `B = ∅` for `Real.exp`,
`Real.sin`, `Real.cos` and `Real.arctan`; `B = {0}` for the reciprocal, the
logarithm and a real power; `B = {-1, 1}` for `Real.arcsin`. -/
theorem dense_analyticLocus_comp (f g : ℝ → ℝ) (B : Finset ℝ)
    (hf : Dense (analyticLocus f)) (hg : ∀ y : ℝ, y ∉ B → AnalyticAt ℝ g y) :
    Dense (analyticLocus fun x => g (f x)) := by
  rw [dense_iff_inter_open]
  intro U hU hUne
  obtain ⟨x₀, hx₀U, hx₀f⟩ := (dense_iff_inter_open.mp hf) U hU hUne
  have hx₀a : AnalyticAt ℝ f x₀ := hx₀f
  by_cases hc : ∃ c ∈ B, ∀ᶠ t in 𝓝 x₀, f t = c
  · -- `f` is constant near `x₀`, hence `g ∘ f` is constant near `x₀`.
    obtain ⟨c, -, hc⟩ := hc
    refine ⟨x₀, hx₀U, ?_⟩
    show AnalyticAt ℝ (fun x => g (f x)) x₀
    have heq : (fun _ : ℝ => g c) =ᶠ[𝓝 x₀] fun x => g (f x) := by
      filter_upwards [hc] with t ht
      rw [ht]
    exact (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => g c) x₀).congr heq
  · -- Otherwise `f` avoids `B` on a punctured neighbourhood of `x₀`.
    simp only [not_exists, not_and] at hc
    have hne : ∀ c ∈ B, ∀ᶠ t in 𝓝[≠] x₀, f t ≠ c := by
      intro c hcB
      rcases hx₀a.eventually_eq_or_eventually_ne
          (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => c) x₀) with h | h
      · exact absurd h (hc c hcB)
      · exact h
    have hall : ∀ᶠ t in 𝓝[≠] x₀, ∀ c ∈ B, f t ≠ c :=
      (Filter.eventually_all_finset B).2 hne
    have hmem : U ∩ analyticLocus f ∈ 𝓝 x₀ :=
      (hU.inter (isOpen_analyticLocus f)).mem_nhds ⟨hx₀U, hx₀f⟩
    have hUloc : ∀ᶠ t in 𝓝[≠] x₀, t ∈ U ∩ analyticLocus f :=
      eventually_nhdsWithin_of_eventually_nhds (Filter.eventually_iff.2 hmem)
    obtain ⟨t, ht₁, ht₂⟩ := (hall.and hUloc).exists
    refine ⟨t, ht₂.1, ?_⟩
    show AnalyticAt ℝ (fun x => g (f x)) t
    have hgt : AnalyticAt ℝ g (f t) := hg _ fun hB => ht₁ _ hB rfl
    have hft : AnalyticAt ℝ f t := ht₂.2
    simpa [Function.comp_def] using hgt.comp hft

/-- **Elementary functions are analytic on a dense open set.**

The analytic locus of an elementary function is dense; it is open by
`Fabius.isOpen_analyticLocus`.  Density cannot be improved to "everywhere":
`fun x => x⁻¹` is elementary and is not analytic at `0`. -/
theorem IsElementary.dense_analyticLocus {f : ℝ → ℝ} (hf : IsElementary f) :
    Dense (analyticLocus f) := by
  induction hf with
  | const c =>
      refine dense_univ.mono ?_
      intro x _
      exact (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => c) x)
  | id =>
      refine dense_univ.mono ?_
      intro x _
      exact analyticAt_id
  | add _ _ ih₁ ih₂ =>
      refine (ih₁.inter_of_isOpen_left ih₂ (isOpen_analyticLocus _)).mono ?_
      rintro x ⟨hx₁, hx₂⟩
      exact AnalyticAt.fun_add hx₁ hx₂
  | mul _ _ ih₁ ih₂ =>
      refine (ih₁.inter_of_isOpen_left ih₂ (isOpen_analyticLocus _)).mono ?_
      rintro x ⟨hx₁, hx₂⟩
      exact AnalyticAt.fun_mul hx₁ hx₂
  | neg _ ih =>
      refine ih.mono ?_
      intro x hx
      exact AnalyticAt.fun_neg hx
  | inv _ ih =>
      exact dense_analyticLocus_comp _ (fun t : ℝ => t⁻¹) {0} ih fun y hy =>
        analyticAt_inv (by simpa using hy)
  | rpow r _ ih =>
      exact dense_analyticLocus_comp _ (fun t : ℝ => t ^ r) {0} ih fun y hy =>
        analyticAt_rpow_const (by simpa using hy) r
  | exp _ ih =>
      exact dense_analyticLocus_comp _ Real.exp ∅ ih fun _ _ => analyticAt_rexp
  | log _ ih =>
      exact dense_analyticLocus_comp _ Real.log {0} ih fun y hy =>
        analyticAt_log_of_ne_zero (by simpa using hy)
  | sin _ ih =>
      exact dense_analyticLocus_comp _ Real.sin ∅ ih fun _ _ => Real.analyticAt_sin
  | cos _ ih =>
      exact dense_analyticLocus_comp _ Real.cos ∅ ih fun _ _ => Real.analyticAt_cos
  | arcsin _ ih =>
      refine dense_analyticLocus_comp _ Real.arcsin {-1, 1} ih fun y hy => ?_
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
      exact analyticAt_arcsin hy.1 hy.2
  | arctan _ ih =>
      exact dense_analyticLocus_comp _ Real.arctan ∅ ih fun y _ => analyticAt_arctan y

/-- The set where a function fails to be real analytic is closed. -/
theorem isClosed_compl_analyticLocus (f : ℝ → ℝ) : IsClosed (analyticLocus f)ᶜ :=
  (isOpen_analyticLocus f).isClosed_compl

/-- The set where an elementary function fails to be real analytic has empty
interior.  Together with `Fabius.isClosed_compl_analyticLocus` this says the
exceptional set is nowhere dense. -/
theorem IsElementary.interior_compl_analyticLocus {f : ℝ → ℝ} (hf : IsElementary f) :
    interior (analyticLocus f)ᶜ = ∅ := by
  rw [interior_compl, hf.dense_analyticLocus.closure_eq, compl_univ]

/-- The nonanalytic locus of an elementary function is nowhere dense. -/
theorem IsElementary.isNowhereDense_compl_analyticLocus
    {f : ℝ → ℝ} (hf : IsElementary f) :
    IsNowhereDense (analyticLocus f)ᶜ :=
  (isClosed_compl_analyticLocus f).isNowhereDense_iff.mpr
    hf.interior_compl_analyticLocus

/-- An elementary function is real analytic at *some* point of every nonempty
open set. -/
theorem IsElementary.exists_analyticAt_of_isOpen {f : ℝ → ℝ} (hf : IsElementary f)
    {U : Set ℝ} (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ x ∈ U, AnalyticAt ℝ f x := by
  obtain ⟨x, hxU, hxf⟩ := (dense_iff_inter_open.mp hf.dense_analyticLocus) U hU hUne
  exact ⟨x, hxU, hxf⟩

/-- An elementary function cannot agree on a set with nonempty interior with
a function that is nonanalytic at every point of that interior. -/
theorem IsElementary.not_eqOn_of_interior_nonempty
    {f g : ℝ → ℝ} (hg : IsElementary g) {S : Set ℝ}
    (hSne : (interior S).Nonempty)
    (hf : ∀ x ∈ interior S, ¬ AnalyticAt ℝ f x) :
    ¬ EqOn g f S := by
  intro heq
  obtain ⟨x, hxS, hxg⟩ :=
    hg.exists_analyticAt_of_isOpen isOpen_interior hSne
  exact hf x hxS (hxg.congr <| by
    filter_upwards [isOpen_interior.mem_nhds hxS] with t ht
    exact heq (interior_subset ht))

end Fabius
