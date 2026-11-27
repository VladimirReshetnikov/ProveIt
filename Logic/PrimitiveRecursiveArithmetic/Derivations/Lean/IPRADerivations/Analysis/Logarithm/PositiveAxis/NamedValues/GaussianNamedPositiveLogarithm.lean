import IPRADerivations.Analysis.Names.Approximation.GaussianPositiveCompactInputDecoding
import IPRADerivations.Analysis.Exponential.PositiveAxis.NamedValues.GaussianRealNameExponentialInjectivity

/-!
# The original positive-rational logarithm on a compact real name

Every sample decodes an actual sufficiently late real observation and
uses the original positive-rational logarithm at that point. A uniform
clock absorbs the compact logarithmic Lipschitz constant. The frozen
comparison retains the independent error of the original input sample.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedPositiveLogarithm

open_ipra
open GaussianRationalHorner (canonical canonical_congr positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactLogarithmBounds (domain radius)
open GaussianPositiveRationalLogarithm (logF fraction)
open GaussianNamedInverseRate (rateNumerator rateDenominator rate_at denominator_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent cross_at cross_refl)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def admissible (f : PR 2) (x E T : PTm n) : Fm PTm n := .all
  (canonical (ap2 f (var 0) (Syn.shift x)) ⋏
    GaussianPositiveCompactInputDecoding.source (ap2 f (var 0) (Syn.shift x)) (Syn.shift E) (Syn.shift T))
def source (f : PR 2) (x E T : PTm n) : Fm PTm n := pointCN f x ⋏ (le one E ⋏ admissible f x E T)
def clock (p E : PTm n) : PTm n := GaussianFastValueCut.exponent E (succ p)
def numerator (f : PR 2) (k x : PTm n) : PTm n := GaussianUnitIntervalInputDecoding.numerator (ap2 f k x)
def denominator (f : PR 2) (k x : PTm n) : PTm n := GaussianUnitIntervalInputDecoding.denominator (ap2 f k x)
def rationalData (f : PR 2) (k x : PTm n) : PTm n :=
  GaussianPositiveRationalLogarithm.data (numerator f k x) (denominator f k x)
def observation (f : PR 2) (p x E : PTm n) : PTm n := ap2 logF (succ p) (rationalData f (clock p E) x)
def data (x E : PTm n) : PTm n := pairT x E
def nameF (f : PR 2) : PR 2 := PTm.toPR (observation f (var 0) (fstT (var 1)) (sndT (var 1)))

ipra_subst source [admissible, GaussianPositiveCompactInputDecoding.source, Foundations.BoundedFormulas.subst_up_shift', one]
ipra_subst rationalData [numerator, denominator]
ipra_subst observation [clock]
ipra_subst data

theorem sample_at (f : PR 2) (p x E : PTm n) :
    Γ ⊢[PRAAx] ap2 (nameF f) p (data x E) ≐ observation f p x E := by
  simpa only [nameF, data, subst_observation, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using
    (toPR_pair_eq (Γ := Γ) (observation f (var 0) (var 1) (var 2)) p x E)

theorem admissible_at (f : PR 2) (k x E T : PTm n) (h : Γ ⊢[PRAAx] source f x E T) :
    Γ ⊢[PRAAx] canonical (ap2 f k x) ⋏ GaussianPositiveCompactInputDecoding.source (ap2 f k x) E T := by
  simpa [admissible,GaussianPositiveCompactInputDecoding.source] using h.andE₂.andE₂.allE k

theorem decoded_domain (f : PR 2) (k x E T : PTm n) (h : Γ ⊢[PRAAx] source f x E T) :
    Γ ⊢[PRAAx] domain (numerator f k x) (denominator f k x) E T :=
  GaussianPositiveCompactInputDecoding.decoded_source _ _ _ (admissible_at f k x E T h).andE₂

theorem decoded_value (f : PR 2) (k x E T : PTm n) (h : Γ ⊢[PRAAx] source f x E T) :
    Γ ⊢[PRAAx] fraction (numerator f k x) (denominator f k x) ≐ ap2 f k x :=
  GaussianPositiveCompactInputDecoding.fraction_exact _ _ _
    (admissible_at f k x E T h).andE₂ (admissible_at f k x E T h).andE₁

theorem sample_real (f : PR 2) (p x E : PTm n) :
    Γ ⊢[PRAAx] RationalGaussianEmbedding.axis (ap2 (nameF f) p (data x E)) :=
  RationalGaussianEmbedding.axis_congr (sample_at f p x E).eqSymm
    (GaussianPositiveRationalLogarithm.sample_axis (succ p) (numerator f (clock p E) x) (denominator f (clock p E) x))

theorem real_samples (f : PR 2) (x E : PTm n) :
    Γ ⊢[PRAAx] GaussianRealNameExponentialInjectivity.axisSamples (nameF f) (data x E) := by
  refine .allI ?_
  simpa only [GaussianRealNameExponentialInjectivity.axisSamples,subst_data,Syn.shift] using
    sample_real f (var 0) (Syn.shift x) (Syn.shift E)

theorem sample_bound (f : PR 2) (p x E T : PTm n) (h : Γ ⊢[PRAAx] source f x E T) :
    Γ ⊢[PRAAx] bounded (ap2 (nameF f) p (data x E)) (radius E T) one :=
  GaussianRationalReciprocal.bound_congr (sample_at f p x E).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianCompactLogarithmBounds.sample_bound (succ p) _ _ E T h.andE₂.andE₁
      (decoded_domain f (clock p E) x E T h))

private theorem decoded_log_rate (f g : PR 2) (r s x y E T U A D : PTm n)
    (hf : Γ ⊢[PRAAx] source f x E T) (hg : Γ ⊢[PRAAx] source g y E U)
    (hd : Γ ⊢[PRAAx] le one D) (hr : Γ ⊢[PRAAx] distanceBounded (ap2 f r x) (ap2 g s y) A D) :
    Γ ⊢[PRAAx] GaussianNamedInverseRate.independentRate logF logF (rationalData f r x) (rationalData g s y) (E*A) D := by
  have hx := decoded_domain f r x E T hf
  have hy := decoded_domain g s y E U hg
  exact GaussianCompactLogarithmBounds.original_log_rate _ _ _ _ E A D hx.andE₁ hy.andE₁ hd hx.andE₂.andE₁ hy.andE₂.andE₁
    (distance_congr (decoded_value f r x E T hf).eqSymm (decoded_value g s y E U hg).eqSymm (.eqRefl _) (.eqRefl _) hr)

private theorem double_unit (p : PTm n) : Γ ⊢[PRAAx] unit (succ p) ≐ two*unit p :=
  (pw_succ two p).eqTrans (mul_comm _ _)

private theorem clock_budget (p E : PTm n) : Γ ⊢[PRAAx] le (two*E*unit p) (unit (clock p E)) :=
  le_congr ((congrMul (.eqRefl E) (double_unit p)).eqTrans (by ipra_ring)) (.eqRefl _)
    (GaussianFastValueCut.query_budget E (succ p))

theorem observations_of_query_bound (f g : PR 2) (p q x y E T U A D : PTm n)
    (hf : Γ ⊢[PRAAx] source f x E T) (hg : Γ ⊢[PRAAx] source g y E U)
    (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] distanceBounded (ap2 f (clock p E) x) (ap2 g (clock q E) y)
      (rateNumerator A D (clock p E) (clock q E)) (rateDenominator D (clock p E) (clock q E))) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data x E)) (ap2 (nameF g) q (data y E))
      (rateNumerator (E*A) D p q) (rateDenominator D p q) := by
  let r := clock p E
  let s := clock q E
  let B := rateNumerator A D r s
  let C := rateDenominator D r s
  have hC : Γ ⊢[PRAAx] le one C := denominator_positive D r s hD
  have raw := rate_at logF logF (rationalData f r x) (rationalData g s y) (E*B) C (succ p) (succ q)
    (decoded_log_rate f g r s x y E T U B C hf hg hC h)
  have up := double_unit (Γ := Γ) p
  have uq := double_unit (Γ := Γ) q
  have eN : Γ ⊢[PRAAx] rateNumerator (E*B) C (succ p) (succ q) ≐
      (E*B)*(two*unit p)*(two*unit q)+C*(two*unit p+two*unit q) :=
    congrAdd (congrMul (congrMul (.eqRefl _) up) uq) (congrMul (.eqRefl _) (congrAdd up uq))
  have eD : Γ ⊢[PRAAx] rateDenominator C (succ p) (succ q) ≐ C*(two*unit p)*(two*unit q) :=
    congrMul (congrMul (.eqRefl _) up) uq
  apply distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ hC (positive_product _ _ RationalAlgebra.two_positive (unit_positive p)))
      (positive_product _ _ RationalAlgebra.two_positive (unit_positive q))) (denominator_positive D p q hD) ?_
    (distance_congr (sample_at f p x E).eqSymm (sample_at g q y E).eqSymm eN eD raw)
  dsimp only [B,C,rateNumerator,rateDenominator]
  ipra_le (2*(𝔞 D)^2*𝔞(unit p)*𝔞(unit q)*𝔞(unit s)*𝔞(unit q))*sl (clock_budget p E)+
    (2*(𝔞 D)^2*𝔞(unit p)*𝔞(unit q)*𝔞(unit r)*𝔞(unit p))*sl (clock_budget q E)

theorem original_observations (f g : PR 2) (p q x y E T : PTm n)
    (hf : Γ ⊢[PRAAx] source f x E T) (hg : Γ ⊢[PRAAx] source g y E T)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data x E)) (ap2 (nameF g) q (data y E))
      (unit p+unit q) (unit p*unit q) := by
  have raw := cross_at f g x y (clock p E) (clock q E) he
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold rateNumerator; ipra_ring) (by unfold rateDenominator; ipra_ring)
    (observations_of_query_bound f g p q x y E T T zero one hf hg (le_refl one)
      (distance_congr (.eqRefl _) (.eqRefl _) (by unfold rateNumerator; ipra_ring) (by unfold rateDenominator; ipra_ring) raw))

theorem proper (f g : PR 2) (x y E T : PTm n)
    (hf : Γ ⊢[PRAAx] source f x E T) (hg : Γ ⊢[PRAAx] source g y E T)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data x E) (data y E) := by
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source f (sh x) (sh E) (sh T) := by
    simpa only [Fm.shift,Syn.shift,subst_source,sh] using hf.shift.shift
  have gs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source g (sh y) (sh E) (sh T) := by
    simpa only [Fm.shift,Syn.shift,subst_source,sh] using hg.shift.shift
  have es : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] crossEquivalent f g (sh x) (sh y) := by
    simpa [Fm.shift,Syn.shift,sh] using he.shift.shift
  refine .allI (.allI ?_)
  simpa only [crossEquivalent,subst_data,Syn.shift,sh] using
    original_observations f g (var 1) (var 0) (sh x) (sh y) (sh E) (sh T) hs gs es

theorem name_regular (f : PR 2) (x E T : PTm n) (h : Γ ⊢[PRAAx] source f x E T) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data x E) := by
  simpa only [pointCN,GaussianEuclideanPointDistance.unit,GaussianCoefficientNameBounds.unit,crossEquivalent] using
    proper f f x x E T h h (cross_refl f x h.andE₁)

theorem exponential_input (f : PR 2) (x E T : PTm n) (h : Γ ⊢[PRAAx] source f x E T) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input (nameF f) (radius E T) (data x E) := by
  refine .andI (name_regular f x E T h) (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] source f (Syn.shift x) (Syn.shift E) (Syn.shift T) := by
    simpa only [Fm.shift,Syn.shift,subst_source] using h.shift
  simpa only [GaussianRadiusExponentialName.boundedSamples,subst_data,GaussianCompactLogarithmBounds.subst_radius,Syn.shift] using
    sample_bound f (var 0) (Syn.shift x) (Syn.shift E) (Syn.shift T) hs

/-- The second logarithm is the original name at one frozen input query. -/
theorem original_frozen_observations (f : PR 2) (p q k x E T : PTm n) (h : Γ ⊢[PRAAx] source f x E T) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data x E)) (ap2 logF q (rationalData f k x))
      (rateNumerator E (unit k) p q) (rateDenominator (unit k) p q) := by
  let r := clock p E
  let A := unit r+unit k
  let D := unit r*unit k
  have hd := positive_product _ _ (unit_positive (Γ := Γ) r) (unit_positive k)
  have raw := GaussianNamedInverseRate.rate_at logF logF _ _ (E*A) D (succ p) q
    (decoded_log_rate f f r k x x E T T A D h h hd (cross_at f f x x r k (cross_refl f x h.andE₁)))
  have up := double_unit (Γ := Γ) p
  have eN : Γ ⊢[PRAAx] rateNumerator (E*A) D (succ p) q ≐
      (E*A)*(two*unit p)*unit q+D*(two*unit p+unit q) :=
    congrAdd (congrMul (congrMul (.eqRefl _) up) (.eqRefl _)) (congrMul (.eqRefl _) (congrAdd up (.eqRefl _)))
  have eD : Γ ⊢[PRAAx] rateDenominator D (succ p) q ≐ D*(two*unit p)*unit q :=
    congrMul (congrMul (.eqRefl _) up) (.eqRefl _)
  have actual := distance_congr (sample_at f p x E).eqSymm (.eqRefl _) eN eD raw
  exact distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ hd (positive_product _ _ (le_succ_self one) (unit_positive p))) (unit_positive q))
    (GaussianNamedInverseRate.denominator_positive (unit k) p q (unit_positive k)) (by
      dsimp only [A,D]
      unfold rateNumerator rateDenominator
      ipra_le (𝔞(unit k)*𝔞(unit k)*𝔞(unit p)*𝔞(unit q)*𝔞(unit q))*sl (clock_budget p E)) actual

theorem original_frozen_rate (f : PR 2) (k x E T : PTm n) (hs : Γ ⊢[PRAAx] source f x E T) :
    Γ ⊢[PRAAx] GaussianNamedInverseRate.independentRate (nameF f) logF (data x E) (rationalData f k x) E (unit k) := by
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have ss : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source f (sh x) (sh E) (sh T) := by
    simpa only [Fm.shift,Syn.shift,subst_source,sh] using hs.shift.shift
  refine .allI (.allI ?_)
  simpa only [GaussianNamedInverseRate.independentRate,subst_data,subst_rationalData,
    GaussianCoefficientNameBounds.subst_unit,Syn.shift,sh] using
    original_frozen_observations f (var 1) (var 0) (sh k) (sh x) (sh E) (sh T) ss

theorem actual_named_positive_logarithm_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source f (var 0) (var 1) (var 2) ⟶
        GaussianRadiusExponentialName.input (nameF f) (radius (var 1) (var 2)) (data (var 0) (var 1))) :=
  closeUniv 3 (.impI (exponential_input f _ _ _ Prf.hyp0))

theorem actual_named_positive_logarithm_frozen_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (source f (var 3) (var 4) (var 5) ⟶
        distanceBounded (ap2 (nameF f) (var 0) (data (var 3) (var 4))) (ap2 logF (var 1) (rationalData f (var 2) (var 3)))
          (rateNumerator (var 4) (unit (var 2)) (var 0) (var 1)) (rateDenominator (unit (var 2)) (var 0) (var 1))) :=
  closeUniv 6 (.impI (original_frozen_observations f _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedPositiveLogarithm
