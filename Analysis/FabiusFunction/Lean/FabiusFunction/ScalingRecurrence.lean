import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Differentiating multiplicative scaling recurrences

Several logarithmic transforms attached to the Fabius function satisfy an
exact *scaling recurrence* on the positive half line: a weighted value at a
dilated point differs from the value at the point itself by an elementary
kernel,

`c * f (q * t) = g t + f t`,  for every `t > 0`.

Differentiating such an identity produces the same shape one order up, with
the weight multiplied by the dilation factor:

`(q * c) * f' (q * s) = g' s + f' s`.

Iterating that step is how the corpus turns a single dilation equation into a
recurrence for every derivative of a logarithmic transform, and from there
into `O(log n / n ^ j)` cumulant bounds.

This module isolates the two differentiation steps that were previously
written out once per derivative order.  Both are stated for an arbitrary
dilation factor `q > 0` rather than for `q = 2`: the proofs never use
dyadicity, and the `k`-fold generalizations of the Fabius recurrence scale by
`k` rather than by `2`.  `two_mul`-flavoured specializations are supplied for
the dyadic case that the rest of the corpus consumes.

## Main results

* `hasDerivAt_of_scalingRecurrence` — differentiate `c * f (q * t) = g t + f t`
  in the dilated variable.
* `hasDerivAt_of_scalingRecurrence_two_mul` — its dyadic specialization.
* `hasDerivAt_of_parameterScalingRecurrence` — differentiate a dilation
  identity `f (q * t) θ = g t θ + f t θ` in an inert parameter `θ`, for
  functions valued in an arbitrary real normed space.  There the dilation
  acts on a *parameter* rather than on the differentiation variable, so no
  weight appears.
* `hasDerivAt_of_parameterScalingRecurrence_two_mul` — its dyadic
  specialization.

## Interface notes

The outgoing weight is supplied by the caller as a separate argument `d`
together with a proof `d = q * c`, rather than being left as the compound
term `q * c` in the conclusion.  This keeps the conclusion syntactically
equal to the recurrence the caller wants to state — `4 * f' (2 * s) = …`
rather than `2 * 2 * f' (2 * s) = …` — so that consumers are term-mode
applications with no arithmetic normalization step.

Callers should pin `f`, `g`, `f'` and `g'` by name.  The conclusion mentions
`f' (q * s)`, in which `q * s` is not a bound variable, so leaving `f'` to be
inferred is a flex-rigid unification problem that can be solved by the
constant function.  Every consumer in this corpus passes the four functions
explicitly for that reason.

## Placement

This module depends on `Mathlib` only; nothing in it mentions the Fabius
function.  It is imported by the negative-Laplace derivative layer, from
which the vertical modules inherit it transitively.
-/

set_option autoImplicit false

open Filter Set Topology

namespace Fabius

/-- **Differentiating a weighted scaling recurrence.**

If `f` and `g` are differentiable at every positive point with derivatives
`f'` and `g'`, and the weighted dilation identity

`c * f (q * t) = g t + f t`

holds for every `t > 0`, then the same identity holds one derivative up with
the weight multiplied by the dilation factor `q`.

The outgoing weight is taken as an argument `d` with `hd : d = q * c` so that
the conclusion is stated in the caller's preferred normal form. -/
theorem hasDerivAt_of_scalingRecurrence
    {f g f' g' : ℝ → ℝ} {c d q : ℝ} (hq : 0 < q) (hd : d = q * c)
    (hf : ∀ ⦃t : ℝ⦄, 0 < t → HasDerivAt f (f' t) t)
    (hg : ∀ ⦃t : ℝ⦄, 0 < t → HasDerivAt g (g' t) t)
    (hrec : ∀ ⦃t : ℝ⦄, 0 < t → c * f (q * t) = g t + f t)
    {s : ℝ} (hs : 0 < s) :
    d * f' (q * s) = g' s + f' s := by
  subst hd
  have hqs : 0 < q * s := mul_pos hq hs
  have hl := ((hf hqs).comp s ((hasDerivAt_id s).const_mul q)).const_mul c
  have hr := (hg hs).add (hf hs)
  have heq : (fun t : ℝ => c * f (q * t)) =ᶠ[nhds s] fun t : ℝ => g t + f t := by
    filter_upwards [Ioi_mem_nhds hs] with t ht using hrec ht
  have hu := hl.unique (hr.congr_of_eventuallyEq heq)
  calc q * c * f' (q * s) = c * (f' (q * s) * (q * 1)) := by ring
    _ = g' s + f' s := hu

/-- The dyadic case `q = 2` of `hasDerivAt_of_scalingRecurrence`: the weight
of a dilation recurrence doubles with every differentiation. -/
theorem hasDerivAt_of_scalingRecurrence_two_mul
    {f g f' g' : ℝ → ℝ} {c d : ℝ} (hd : d = 2 * c)
    (hf : ∀ ⦃t : ℝ⦄, 0 < t → HasDerivAt f (f' t) t)
    (hg : ∀ ⦃t : ℝ⦄, 0 < t → HasDerivAt g (g' t) t)
    (hrec : ∀ ⦃t : ℝ⦄, 0 < t → c * f (2 * t) = g t + f t)
    {s : ℝ} (hs : 0 < s) :
    d * f' (2 * s) = g' s + f' s :=
  hasDerivAt_of_scalingRecurrence (f := f) (g := g) (f' := f') (g' := g')
    (by norm_num) hd hf hg hrec hs

/-- **Differentiating a scaling recurrence in an inert parameter.**

Here the dilation `t ↦ q * t` acts on the first argument while the
differentiation is in the second.  Because the two variables are independent,
no weight is produced: the identity

`f (q * t) θ = g t θ + f t θ`,  for every `t > 0` and every `θ`,

differentiates to

`f' (q * s) θ = g' s θ + f' s θ`.

The values are taken in an arbitrary real normed space, which covers the
complex-valued vertical logarithmic derivatives. -/
theorem hasDerivAt_of_parameterScalingRecurrence
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g f' g' : ℝ → ℝ → E} {q : ℝ} (hq : 0 < q)
    (hf : ∀ ⦃t : ℝ⦄, 0 < t → ∀ θ : ℝ, HasDerivAt (f t) (f' t θ) θ)
    (hg : ∀ ⦃t : ℝ⦄, 0 < t → ∀ θ : ℝ, HasDerivAt (g t) (g' t θ) θ)
    (hrec : ∀ ⦃t : ℝ⦄, 0 < t → ∀ θ : ℝ, f (q * t) θ = g t θ + f t θ)
    {s : ℝ} (hs : 0 < s) (θ : ℝ) :
    f' (q * s) θ = g' s θ + f' s θ := by
  have hl := hf (mul_pos hq hs) θ
  have hr := (hg hs θ).add (hf hs θ)
  have heq : f (q * s) =ᶠ[nhds θ] fun u : ℝ => g s u + f s u :=
    Eventually.of_forall fun u => hrec hs u
  exact hl.unique (hr.congr_of_eventuallyEq heq)

/-- The dyadic case `q = 2` of `hasDerivAt_of_parameterScalingRecurrence`. -/
theorem hasDerivAt_of_parameterScalingRecurrence_two_mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g f' g' : ℝ → ℝ → E}
    (hf : ∀ ⦃t : ℝ⦄, 0 < t → ∀ θ : ℝ, HasDerivAt (f t) (f' t θ) θ)
    (hg : ∀ ⦃t : ℝ⦄, 0 < t → ∀ θ : ℝ, HasDerivAt (g t) (g' t θ) θ)
    (hrec : ∀ ⦃t : ℝ⦄, 0 < t → ∀ θ : ℝ, f (2 * t) θ = g t θ + f t θ)
    {s : ℝ} (hs : 0 < s) (θ : ℝ) :
    f' (2 * s) θ = g' s θ + f' s θ :=
  hasDerivAt_of_parameterScalingRecurrence (f := f) (g := g) (f' := f') (g' := g')
    (by norm_num) hf hg hrec hs θ

end Fabius
