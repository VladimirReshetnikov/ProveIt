import IPRADerivations.Analysis.Trigonometry.Sinc.GaussianNamedSineSincFactorization

/-!
# Congruence of sinc for independently certified names

Equal arguments can use different disk bounds, factorial cutoffs and
observation clocks. Their sinc samples agree at a computed dyadic rate.
The proof compares the two finite values directly near zero and cancels a
bounded reciprocal at twice the requested precision elsewhere.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNamedSincCongruence

open_ipra
open GaussianArctangentCayleyValues (imaginaryPoint right_endpoint unit_bound)
open GaussianNamedSincSamples (argument argumentClock clock argument_clock_later
  value sineValue sineBudget sampleSize sine_sample_error norm_cases)
open GaussianNamedSinc (nameF data rawF raw_at raw_regular modulus sample_distance_near sample_distance_away name_regular subst_data)
open GaussianNamedSineTaylor (imaginaryF imaginary_at imaginary_input rawData)
open GaussianNamedSineFromExponential (sineF sineData sine_regular sine_proper)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (qone reciprocal bound_congr)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalLowerBounds (lower)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone dyadic_weaken)
open GaussianApproximateInverseDistance (multiply_distance)
open GaussianNameEquivalence (crossEquivalent cross_at diagonal_at cross_to_diagonal)
open GaussianNamedDiagonalRate (diagonalRate cross_of_diagonal_rate)
open GaussianNameRingLaws (normalized_to_sample)
open GaussianRadiusExponentialName (input)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem imaginary_cross_at (f g : PR 2) (x y p q : PTm n) (h : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (imaginaryF f) p x) (ap2 (imaginaryF g) q y)
      (unit p+unit q) (unit p*unit q) := by
  have b : Γ ⊢[PRAAx] bounded (imaginaryPoint : PTm n) one one :=
    bound_congr (right_endpoint one (le_refl one)) (.eqRefl _) (.eqRefl _) (unit_bound one one (le_refl one))
  exact distance_congr (imaginary_at f p x).eqSymm (imaginary_at g q y).eqSymm (one_mul _) (.eqRefl _)
    (multiply_distance imaginaryPoint _ _ one _ _ (positive_product _ _ (unit_positive p) (unit_positive q))
      b (cross_at f g x y p q h))

theorem imaginary_cross (f g : PR 2) (x y : PTm n) (h : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (imaginaryF f) (imaginaryF g) x y := by
  refine .allI (.allI ?_)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let a := Syn.shift (Syn.shift x)
  let b := Syn.shift (Syn.shift y)
  have h' : Δ ⊢[PRAAx] crossEquivalent f g a b := by
    simpa only [Fm.shift, Syn.shift, GaussianNameEquivalence.subst_crossEquivalent, Δ, a, b] using h.shift.shift
  exact imaginary_cross_at f g a b (var 1) (var 0) h'

private theorem cross_at_later (f g : PR 2) (x y p r s : PTm n) (h : Γ ⊢[PRAAx] crossEquivalent f g x y)
    (hr : Γ ⊢[PRAAx] le p r) (hs : Γ ⊢[PRAAx] le p s) :
    Γ ⊢[PRAAx] distanceBounded (ap2 f r x) (ap2 g s y) two (unit p) := by
  have order := add_le_add₂ (le_mul_mono (le_refl (unit r)) (unit_monotone hs))
    (le_mul_mono (le_refl (unit s)) (unit_monotone hr))
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive r) (unit_positive s))
    (unit_positive p) (le_congr (by ipra_ring) (by ipra_ring) order) (cross_at f g x y r s h)

def sineCost (f g : PR 2) (R S x y : PTm n) : PTm n := sineBudget f R x+two+sineBudget g S y

private theorem sine_value_error (f g : PR 2) (R S x y p : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hg : Γ ⊢[PRAAx] input g S y) (h : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] distanceBounded (sineValue f R x p) (sineValue g S y p) (sineCost f g R S x y) (unit (clock p)) := by
  let F := sineF (imaginaryF f)
  let G := sineF (imaginaryF g)
  let a := sineData (imaginaryF f) R x
  let b := sineData (imaginaryF g) S y
  let t := clock p
  have hp := unit_positive (Γ := Γ) t
  have e := sine_proper (imaginaryF f) (imaginaryF g) R S x y
    (imaginary_input f R x hf) (imaginary_input g S y hg) (imaginary_cross f g x y h)
  have mid := diagonal_at F G a b t (cross_to_diagonal _ _ _ _ e)
  exact distance_triangle_same _ _ _ _ _ _ hp
    (distance_triangle_same _ _ _ _ _ _ hp (distance_symmetric _ _ _ _ hp (sine_sample_error f R x p hf)) mid)
    (sine_sample_error g S y p hg)

def rawCost (f g : PR 2) (R S x y : PTm n) : PTm n :=
  sineCost f g R S x y+sampleSize g S y*two+num 4

private theorem near_error (f g : PR 2) (R S x y p : PTm n)
    (hgap : Γ ⊢[PRAAx] distanceBounded (argument f R x p) (argument g S y p) two (unit (clock p)))
    (hnear : Γ ⊢[PRAAx] bounded (argument f R x p) one (unit (succ p))) :
    Γ ⊢[PRAAx] distanceBounded (value f R x p) (value g S y p) (rawCost f g R S x y) (unit (succ p)) := by
  have hU := unit_positive (Γ := Γ) (succ p)
  have cost : Γ ⊢[PRAAx] le (two+two) (rawCost f g R S x y) := by
    unfold rawCost
    ipra_le 𝔞 (sineCost f g R S x y)+2*𝔞 (sampleSize g S y)
  exact distance_radius_mono _ _ _ _ _ _ hU hU (le_mul_mono cost (le_refl _))
    (sample_distance_near f g R S x y p p hgap hnear)

private theorem away_error (f g : PR 2) (R S x y p : PTm n) (hg : Γ ⊢[PRAAx] input g S y)
    (hgap : Γ ⊢[PRAAx] distanceBounded (argument f R x p) (argument g S y p) two (unit (clock p)))
    (hSin : Γ ⊢[PRAAx] distanceBounded (sineValue f R x p) (sineValue g S y p) (sineCost f g R S x y) (unit (clock p)))
    (hfar : Γ ⊢[PRAAx] lower (argument f R x p) one (unit (succ p))) :
    Γ ⊢[PRAAx] distanceBounded (value f R x p) (value g S y p) (rawCost f g R S x y) (unit (succ p)) := by
  have hU := unit_positive (Γ := Γ) (succ p)
  have cost : Γ ⊢[PRAAx] le (sineCost f g R S x y+sampleSize g S y*two) (rawCost f g R S x y) :=
    le_add_right _ _
  exact distance_radius_mono _ _ _ _ _ _ hU hU (le_mul_mono cost (le_refl _))
    (sample_distance_away f g R S x y p p _ hg hgap hSin hfar)

theorem raw_error (f g : PR 2) (R S x y p : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hg : Γ ⊢[PRAAx] input g S y) (h : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] distanceBounded (value f R x p) (value g S y p) (rawCost f g R S x y) (unit p) := by
  have gap := cross_at_later f g x y (clock p) (argumentClock R p) (argumentClock S p) h
    (argument_clock_later R p) (argument_clock_later S p)
  have sinGap := sine_value_error f g R S x y p hf hg h
  apply dyadic_weaken _ _ _ p (succ p) (le_succ_self p)
  exact .orE (norm_cases (argument f R x p) one (unit (succ p)))
    (near_error f g R S x y p gap.wk Prf.hyp0)
    (away_error f g R S x y p hg.wk gap.wk sinGap.wk Prf.hyp0)

def budget (f g : PR 2) (R S x y : PTm n) : PTm n :=
  (modulus f R x+one)+rawCost f g R S x y+(modulus g S y+one)

ipra_subst budget [rawCost, sineCost]

theorem diagonal_error (f g : PR 2) (R S x y p : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hg : Γ ⊢[PRAAx] input g S y) (h : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data f R x)) (ap2 (nameF g) p (data g S y))
      (budget f g R S x y) (unit p) := by
  have hU := unit_positive (Γ := Γ) p
  have first := distance_congr (.eqRefl _) (raw_at f R x p) (.eqRefl _) (.eqRefl _)
    (normalized_to_sample (rawF f) (modulus f R x) (rawData R x) p (raw_regular f R x hf))
  have last := distance_congr (.eqRefl _) (raw_at g S y p) (.eqRefl _) (.eqRefl _)
    (normalized_to_sample (rawF g) (modulus g S y) (rawData S y) p (raw_regular g S y hg))
  exact distance_triangle_same _ _ _ _ _ _ hU
    (distance_triangle_same _ _ _ _ _ _ hU first (raw_error f g R S x y p hf hg h))
    (distance_symmetric _ _ _ _ hU last)

theorem sinc_proper (f g : PR 2) (R S x y : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hg : Γ ⊢[PRAAx] input g S y) (h : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data f R x) (data g S y) := by
  apply cross_of_diagonal_rate _ _ _ _ (budget f g R S x y) (name_regular f R x hf) (name_regular g S y hg)
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let sh (t : PTm n) := Syn.shift t
  have hf' : Δ ⊢[PRAAx] input f (sh R) (sh x) := by
    simpa only [Fm.shift, Syn.shift, GaussianRadiusExponentialName.subst_input, Δ, sh] using hf.shift
  have hg' : Δ ⊢[PRAAx] input g (sh S) (sh y) := by
    simpa only [Fm.shift, Syn.shift, GaussianRadiusExponentialName.subst_input, Δ, sh] using hg.shift
  have hh' : Δ ⊢[PRAAx] crossEquivalent f g (sh x) (sh y) := by
    simpa only [Fm.shift, Syn.shift, GaussianNameEquivalence.subst_crossEquivalent, Δ, sh] using h.shift
  simpa only [diagonalRate, Syn.shift, subst_data, subst_budget, Δ, sh] using
    diagonal_error f g (sh R) (sh S) (sh x) (sh y) (var 0) hf' hg' hh'

theorem actual_named_sinc_proper_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((input f (var 3) (var 1) ⋏ input g (var 2) (var 0)) ⟶ crossEquivalent f g (var 1) (var 0) ⟶
      crossEquivalent (nameF f) (nameF g) (data f (var 3) (var 1)) (data g (var 2) (var 0))) :=
  closeUniv 4 (.impI (.impI (sinc_proper f g _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianNamedSincCongruence
