import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Continuous branches of polynomial equations with analytic coefficients

This file is independent of the Fabius function.  It proves that a *continuous
branch* of a polynomial equation whose coefficients are real analytic and
whose leading coefficient does not vanish is real analytic on a dense subset
of the region:

`Fabius.analyticDenseOn_of_algebraic`.

This is what upgrades `Fabius.IsElementary` from "closed under `n`-th roots"
to "closed under arbitrary algebraic functions", and hence brings the
non-elementarity theorem in line with Liouville's differential-field notion of
an elementary function rather than only with the description in terms of
radicals.

## The obstruction, and the induction that removes it

Density cannot be improved to "analytic everywhere": `y = |·|` is a continuous
branch of `y ^ 2 - x ^ 2 = 0` and is not analytic at the origin.  The implicit
function theorem applies only where `∂P/∂y ≠ 0`, and the classical way to
control the locus where it vanishes is through the discriminant.  `Mathlib`
has no usable discriminant theory — `Polynomial.discr` has no bridge to
`Separable`, and there is no continuity of roots in the coefficients — so we
use a **degree induction** instead, which needs neither.

Write `g` for `∂P/∂y` evaluated along the branch, and split the region `U`:

* `V = {x ∈ U | g x ≠ 0}` is open, and on it the analytic implicit function
  theorem gives analyticity of the branch outright;
* `W = U \ closure V` is open, and on it `g ≡ 0`, so the branch satisfies the
  *derivative* equation, of degree one less, whose leading coefficient
  `(n + 1) * a (n + 1)` is still nowhere zero — the inductive hypothesis
  applies;
* `V` together with a dense subset of `W` is dense in `U`, because an open set
  disjoint from `V` is disjoint from `closure V` and therefore contained
  in `W`.

The set `W` absorbs exactly the degenerate locus that a discriminant argument
would have to control, and the induction terminates because the degree drops.

## The implicit function theorem used

`Mathlib`'s `ContDiffAt.implicitFunction` is stated for every smoothness
exponent in `ℕ ∪ {∞, ω}`, so instantiating at `ω` gives an *analytic* implicit
function theorem.  Its one nontrivial hypothesis is invertibility of the
partial derivative as a continuous linear map; in one variable that is
discharged by `HasDerivAt.hasFDerivAt_equiv` together with uniqueness of the
Fréchet derivative.  See `Fabius.analyticAt_implicitFunction`.
-/

set_option autoImplicit false

open Filter Set
open scoped Topology ContDiff

namespace Fabius

/-! ## An analytic implicit function theorem in two real variables -/

/-- **Analytic implicit function theorem** in two real variables.

If `f` is real analytic at `(x₀, y₀)` and its partial derivative in the second
variable there is a nonzero real `c`, then the equation `f p = f (x₀, y₀)` is
locally solved by a real analytic function `φ` with `φ x₀ = y₀`.

`Mathlib` has the analytic *inverse* function theorem but states its implicit
function theorem only at `ContDiffAt`; instantiating the smoothness exponent
at `ω` and converting with `ContDiffAt.analyticAt` supplies the analytic
version. -/
theorem analyticAt_implicitFunction {f : ℝ × ℝ → ℝ} {x₀ y₀ c : ℝ}
    (hf : AnalyticAt ℝ f (x₀, y₀))
    (hc : HasDerivAt (fun z : ℝ => f (x₀, z)) c y₀) (hc0 : c ≠ 0) :
    ∃ φ : ℝ → ℝ, AnalyticAt ℝ φ x₀ ∧ φ x₀ = y₀ ∧
      ∀ᶠ p in 𝓝 (x₀, y₀), f p = f (x₀, y₀) ↔ φ p.1 = p.2 := by
  have cdf : ContDiffAt ℝ ω f (x₀, y₀) := hf.contDiffAt
  have pn : (ω : ℕ∞ω) ≠ 0 := by simp
  have hd : HasFDerivAt f (fderiv ℝ f (x₀, y₀)) (x₀, y₀) := hf.differentiableAt.hasFDerivAt
  have hpart : HasFDerivAt (fun z : ℝ => f (x₀, z))
      (fderiv ℝ f (x₀, y₀) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ) y₀ := by
    simpa [Function.comp_def] using hd.comp y₀ (hasFDerivAt_prodMk_right x₀ y₀)
  have hinv : (fderiv ℝ f (x₀, y₀) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible :=
    ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 c hc0),
      (hc.hasFDerivAt_equiv hc0).unique hpart⟩
  exact ⟨cdf.implicitFunction pn hinv,
    (cdf.contDiffAt_implicitFunction pn hinv).analyticAt,
    cdf.implicitFunction_apply_self pn hinv,
    cdf.eventually_apply_eq_iff_implicitFunction pn hinv⟩

/-- A continuous branch through a point where the partial derivative does not
vanish is real analytic there: it must coincide near the point with the
analytic implicit function. -/
theorem analyticAt_of_continuous_branch {f : ℝ × ℝ → ℝ} {y : ℝ → ℝ} {x₀ c : ℝ}
    (hf : AnalyticAt ℝ f (x₀, y x₀))
    (hc : HasDerivAt (fun z : ℝ => f (x₀, z)) c (y x₀)) (hc0 : c ≠ 0)
    (hy : ContinuousAt y x₀)
    (hzero : ∀ᶠ x in 𝓝 x₀, f (x, y x) = f (x₀, y x₀)) :
    AnalyticAt ℝ y x₀ := by
  obtain ⟨φ, hφ, -, hiff⟩ := analyticAt_implicitFunction hf hc hc0
  refine hφ.congr ?_
  have hmap : Tendsto (fun x : ℝ => (x, y x)) (𝓝 x₀) (𝓝 (x₀, y x₀)) :=
    continuousAt_id.prodMk hy
  filter_upwards [hmap.eventually hiff, hzero] with x hx hx0
  exact hx.mp hx0

/-! ## Density of the analytic locus of a branch -/

/-- `y` is real analytic at some point of every nonempty open subset of `s`.
This is "the analytic locus of `y` is dense in `s`", phrased so that it
composes with the splitting lemma below. -/
def AnalyticDenseOn (y : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ V : Set ℝ, IsOpen V → V.Nonempty → V ⊆ s → ∃ x ∈ V, AnalyticAt ℝ y x

/-- Splitting an open set by an open piece on which analyticity is already
known.  An open set disjoint from `V` is disjoint from `closure V`, so it is
contained in `s \ closure V`. -/
theorem analyticDenseOn_of_split {y : ℝ → ℝ} {s V : Set ℝ}
    (hVan : ∀ x ∈ V, AnalyticAt ℝ y x) (hW : AnalyticDenseOn y (s \ closure V)) :
    AnalyticDenseOn y s := by
  intro B hB hBne hBs
  rcases Set.eq_empty_or_nonempty (B ∩ V) with hBV | ⟨x, hxB, hxV⟩
  · have hdisj : Disjoint B (closure V) :=
      (Set.disjoint_iff_inter_eq_empty.2 hBV).closure_right hB
    refine hW B hB hBne ?_
    intro z hz
    exact ⟨hBs hz, fun hzc => Set.disjoint_left.mp hdisj hz hzc⟩
  · exact ⟨x, hxB, hVan x hxV⟩

/-! ## The polynomial and its formal `y`-derivative -/

/-- `fun p => ∑ i < n + 1, a i p.1 * p.2 ^ i`, the two-variable polynomial
whose branches are studied here. -/
noncomputable def branchPoly (a : ℕ → ℝ → ℝ) (n : ℕ) (p : ℝ × ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), a i p.1 * p.2 ^ i

/-- `branchPoly` is real analytic wherever all its coefficients are. -/
theorem analyticAt_branchPoly {a : ℕ → ℝ → ℝ} (n : ℕ) {x₀ y₀ : ℝ}
    (ha : ∀ i, AnalyticAt ℝ (a i) x₀) :
    AnalyticAt ℝ (branchPoly a n) (x₀, y₀) := by
  have hfst : AnalyticAt ℝ (fun p : ℝ × ℝ => p.1) (x₀, y₀) := analyticAt_fst
  have hsnd : AnalyticAt ℝ (fun p : ℝ × ℝ => p.2) (x₀, y₀) := analyticAt_snd
  refine Finset.analyticAt_sum _ fun i _ => ?_
  have h1 : AnalyticAt ℝ (fun p : ℝ × ℝ => a i p.1) (x₀, y₀) := by
    simpa [Function.comp_def] using (ha i).comp hfst
  exact h1.fun_mul (hsnd.fun_pow i)

/-- The derivative of `z ↦ branchPoly a (n + 1) (x, z)`: the formal `∂/∂y` of
the polynomial, reindexed so that it is again of the shape `branchPoly`, of
degree one lower. -/
theorem hasDerivAt_branchPoly_snd (a : ℕ → ℝ → ℝ) (n : ℕ) (x z : ℝ) :
    HasDerivAt (fun w : ℝ => branchPoly a (n + 1) (x, w))
      (branchPoly (fun i x => ((i : ℝ) + 1) * a (i + 1) x) n (x, z)) z := by
  simp only [branchPoly]
  have h : HasDerivAt (fun w : ℝ => ∑ i ∈ Finset.range (n + 1 + 1), a i x * w ^ i)
      (∑ i ∈ Finset.range (n + 1 + 1), a i x * ((i : ℝ) * z ^ (i - 1))) z :=
    HasDerivAt.fun_sum fun i _ => (hasDerivAt_pow i z).const_mul (a i x)
  have hsum : (∑ i ∈ Finset.range (n + 1 + 1), a i x * ((i : ℝ) * z ^ (i - 1)))
      = ∑ i ∈ Finset.range (n + 1), ((i : ℝ) + 1) * a (i + 1) x * z ^ i := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.cast_add, Nat.cast_one,
      Nat.add_sub_cancel]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum] at h
  exact h

/-! ## The main theorem -/

/-- **A continuous branch of a polynomial equation with analytic coefficients
is analytic on a dense subset.**

`U` is open, the coefficients `a 0, …, a n` are real analytic on `U`, the
leading coefficient `a n` vanishes nowhere on `U`, `y` is continuous on `U`,
and `∑ i ≤ n, a i x * y x ^ i = 0` throughout `U`.  Then `y` is real analytic
at some point of every nonempty open subset of `U`.

Density is the correct conclusion: `y = |·|` is a continuous branch of
`y ^ 2 - x ^ 2 = 0` on `ℝ` and is not analytic at `0`. -/
theorem analyticDenseOn_of_algebraic :
    ∀ (n : ℕ) (a : ℕ → ℝ → ℝ) (y : ℝ → ℝ) (U : Set ℝ), IsOpen U →
      (∀ i, ∀ x ∈ U, AnalyticAt ℝ (a i) x) →
      (∀ x ∈ U, a n x ≠ 0) →
      ContinuousOn y U →
      (∀ x ∈ U, branchPoly a n (x, y x) = 0) →
      AnalyticDenseOn y U := by
  intro n
  induction n with
  | zero =>
      intro a y U _ _ hlead _ heq B hB hBne hBU
      obtain ⟨x, hxB⟩ := hBne
      refine absurd ?_ (hlead x (hBU hxB))
      simpa [branchPoly] using heq x (hBU hxB)
  | succ n ih =>
      intro a y U hU ha hlead hy heq
      set b : ℕ → ℝ → ℝ := fun i x => ((i : ℝ) + 1) * a (i + 1) x with hb
      set g : ℝ → ℝ := fun x => branchPoly b n (x, y x) with hgdef
      have hacont : ∀ i, ContinuousOn (a i) U := fun i x hx =>
        ((ha i x hx).continuousAt).continuousWithinAt
      have hgcont : ContinuousOn g U := by
        refine continuousOn_finset_sum _ fun i _ => ?_
        exact (continuousOn_const.mul (hacont (i + 1))).mul (hy.pow i)
      -- The good set: where the partial derivative along the branch is nonzero.
      have hVopen : IsOpen (U ∩ g ⁻¹' {0}ᶜ) :=
        hgcont.isOpen_inter_preimage hU isOpen_compl_singleton
      have hVan : ∀ x ∈ U ∩ g ⁻¹' {0}ᶜ, AnalyticAt ℝ y x := by
        rintro x ⟨hxU, hxg⟩
        refine analyticAt_of_continuous_branch
          (analyticAt_branchPoly (n + 1) fun i => ha i x hxU)
          (hasDerivAt_branchPoly_snd a n x (y x)) hxg
          (hy.continuousAt (hU.mem_nhds hxU)) ?_
        filter_upwards [hU.mem_nhds hxU] with x' hx'
        rw [heq x' hx', heq x hxU]
      -- The degenerate set: there the branch solves the derivative equation.
      have hWopen : IsOpen (U \ closure (U ∩ g ⁻¹' {0}ᶜ)) := hU.sdiff isClosed_closure
      have hWsub : U \ closure (U ∩ g ⁻¹' {0}ᶜ) ⊆ U := fun x hx => hx.1
      have hWg : ∀ x ∈ U \ closure (U ∩ g ⁻¹' {0}ᶜ), g x = 0 := by
        intro x hx
        by_contra h
        exact hx.2 (subset_closure ⟨hx.1, h⟩)
      have hWih : AnalyticDenseOn y (U \ closure (U ∩ g ⁻¹' {0}ᶜ)) := by
        refine ih b y _ hWopen (fun i x hx => ?_) (fun x hx => ?_) (hy.mono hWsub)
          (fun x hx => hWg x hx)
        · exact AnalyticAt.fun_mul analyticAt_const (ha (i + 1) x (hWsub hx))
        · have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
          exact mul_ne_zero h1 (hlead x (hWsub hx))
      exact analyticDenseOn_of_split hVan hWih

/-- The version used downstream: if the region is a dense open set, the
analytic locus of the branch is dense in `ℝ`. -/
theorem dense_setOf_analyticAt_of_algebraic (n : ℕ) (a : ℕ → ℝ → ℝ) (y : ℝ → ℝ)
    {U : Set ℝ} (hU : IsOpen U) (hUd : Dense U)
    (ha : ∀ i, ∀ x ∈ U, AnalyticAt ℝ (a i) x)
    (hlead : ∀ x ∈ U, a n x ≠ 0) (hy : ContinuousOn y U)
    (heq : ∀ x ∈ U, branchPoly a n (x, y x) = 0) :
    Dense {x : ℝ | AnalyticAt ℝ y x} := by
  rw [dense_iff_inter_open]
  intro B hB hBne
  obtain ⟨z, hzB, hzU⟩ := (dense_iff_inter_open.mp hUd) B hB hBne
  obtain ⟨x, hxB, hxa⟩ :=
    analyticDenseOn_of_algebraic n a y U hU ha hlead hy heq (B ∩ U) (hB.inter hU)
      ⟨z, hzB, hzU⟩ fun _ hw => hw.2
  exact ⟨x, hxB.1, hxa⟩

end Fabius
