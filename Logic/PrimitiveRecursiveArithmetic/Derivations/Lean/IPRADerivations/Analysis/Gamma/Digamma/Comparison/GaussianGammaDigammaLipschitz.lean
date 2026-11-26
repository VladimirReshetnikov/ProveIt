import IPRADerivations.Analysis.Gamma.Digamma.Comparison.GaussianGammaDigammaSeriesLipschitz
import IPRADerivations.Analysis.Names.Rates.Order.GaussianNamedRealOrderTransport

/-!
# The original positive rational digamma name has a quantitative upper slope

At two independent precisions the upper difference of the literal native
observations is at most (y−x)(1/x+1/x²) plus their two dyadic allowances.
The same proof gives the sharper common coefficient 2 for x≥1, and
K(K+1) for x≥1/K. The reciprocal-series cutoff is chosen internally
and its auxiliary error is removed by a finite rational comparison.
-/

set_option autoImplicit false
set_option maxHeartbeats 1700000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaLipschitz

open_ipra
open GaussianStirlingGammaLogarithm (source)
open GaussianGammaDigammaSeriesLipschitz (numerator denominator finite_name_upper)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedInverseRate (rate_at rateNumerator rateDenominator denominator_positive)
open GaussianNamedRealOrderTransport (upperSlack precision remove_upper_slack)
open GaussianStirlingGammaFractionalIncrementObservations (scalar_upper)
open GaussianRationalHorner (positive_product)
open GaussianRationalDistanceOrder (distance_symmetric)
open RationalValueBounds (upper upper_mono upper_triangle)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "DF" => GaussianGammaDigammaNative.nameF
local notation "dd" => GaussianGammaDigammaNative.data
local notation "SF" => GaussianGammaDigammaSeries.nameF
local notation "sd" => GaussianGammaDigammaSeries.data

private theorem left_rate (p t a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] upper (fstT (ap2 DF p (dd a b))) (fstT (ap2 SF t (sd a b (succ (unit t)))))
      ((a+one)*unit p+unit t) (unit p*unit t) := by
  let L := succ (unit t)
  have hL : Γ ⊢[PRAAx] le one L := le_trans (unit_positive t) (le_succ_self (unit t))
  have d := denominator_positive L p t hL
  have e := rate_at DF SF (dd a b) (sd a b L) a L p t (GaussianGammaDigammaSeries.original_rate a b L hs hL)
  exact upper_mono _ _ _ _ _ _ d (scalar_upper _ _ _ _ d e)
    (by dsimp only [rateNumerator,rateDenominator,L]; ipra_le 𝔞(a)*𝔞(unit p)^2*𝔞(unit t)*sl (le_succ_self (unit t)))

private theorem right_rate (q t a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] upper (fstT (ap2 SF t (sd a b (succ (unit t))))) (fstT (ap2 DF q (dd a b)))
      ((a+one)*unit q+unit t) (unit q*unit t) := by
  let L := succ (unit t)
  have hL : Γ ⊢[PRAAx] le one L := le_trans (unit_positive t) (le_succ_self (unit t))
  have d := denominator_positive L q t hL
  have e := rate_at DF SF (dd a b) (sd a b L) a L q t (GaussianGammaDigammaSeries.original_rate a b L hs hL)
  exact upper_mono _ _ _ _ _ _ d (scalar_upper _ _ _ _ d (distance_symmetric _ _ _ _ d e))
    (by dsimp only [rateNumerator,rateDenominator,L]; ipra_le 𝔞(a)*𝔞(unit q)^2*𝔞(unit t)*sl (le_succ_self (unit t)))

private theorem original_upper_slack (p q t a c b : PTm n)
    (ha : Γ ⊢[PRAAx] source a b) (hc : Γ ⊢[PRAAx] source c b) (hac : Γ ⊢[PRAAx] le a c) :
    Γ ⊢[PRAAx] upperSlack (fstT (ap2 DF p (dd c b))) (fstT (ap2 DF q (dd a b)))
      (rateNumerator (numerator a c b) (denominator a) p q) (rateDenominator (denominator a) p q)
      (a+c+num 8) t := by
  have hu := unit_positive (Γ := Γ) t
  have hD : Γ ⊢[PRAAx] le one (denominator a) := positive_product _ _ ha.andE₁ ha.andE₁
  have joined := upper_triangle _ _ _ _ _ _ _
    (upper_triangle _ _ _ _ _ _ _ (left_rate p t c b hc) (finite_name_upper t a c b (unit t) ha.andE₁ hac))
    (right_rate q t a b ha)
  exact upper_mono _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ (positive_product _ _ (unit_positive p) hu)
      (positive_product _ _ hD hu)) (positive_product _ _ (unit_positive q) hu))
    joined (by dsimp only [rateNumerator,rateDenominator,upperSlack]; ipra_le 0)

theorem original_upper_at (p q a c b : PTm n)
    (ha : Γ ⊢[PRAAx] source a b) (hc : Γ ⊢[PRAAx] source c b) (hac : Γ ⊢[PRAAx] le a c) :
    Γ ⊢[PRAAx] upper (fstT (ap2 DF p (dd c b))) (fstT (ap2 DF q (dd a b)))
      (rateNumerator (numerator a c b) (denominator a) p q) (rateDenominator (denominator a) p q) :=
  remove_upper_slack _ _ _ _ (a+c+num 8) (original_upper_slack p q _ a c b ha hc hac)

theorem upper_with_radius (p q a c b R D : PTm n)
    (ha : Γ ⊢[PRAAx] source a b) (hc : Γ ⊢[PRAAx] source c b) (hac : Γ ⊢[PRAAx] le a c)
    (h : Γ ⊢[PRAAx] le (numerator a c b*D) (R*denominator a)) :
    Γ ⊢[PRAAx] upper (fstT (ap2 DF p (dd c b))) (fstT (ap2 DF q (dd a b)))
      (rateNumerator R D p q) (rateDenominator D p q) :=
  upper_mono _ _ _ _ _ _ (denominator_positive _ _ _ (positive_product _ _ ha.andE₁ ha.andE₁))
    (original_upper_at p q a c b ha hc hac)
    (by dsimp only [rateNumerator,rateDenominator,denominator] at *; ipra_le (𝔞(unit p)*𝔞(unit q))^2*sl h)

theorem unit_upper_at (p q a c b : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hba : Γ ⊢[PRAAx] le b a) (hac : Γ ⊢[PRAAx] le a c) :
    Γ ⊢[PRAAx] upper (fstT (ap2 DF p (dd c b))) (fstT (ap2 DF q (dd a b)))
      (rateNumerator (two*monus c a) b p q) (rateDenominator b p q) := by
  have ha := le_trans hb hba
  exact upper_with_radius p q a c b _ _ (.andI ha hb) (.andI (le_trans ha hac) hb) hac
    (by dsimp only [numerator,denominator]; ipra_le 𝔞(monus c a)*(2*𝔞(a)+𝔞(b))*sl hba)

theorem compact_upper_at (p q a c b K : PTm n)
    (ha : Γ ⊢[PRAAx] source a b) (hc : Γ ⊢[PRAAx] source c b)
    (hac : Γ ⊢[PRAAx] le a c) (h : Γ ⊢[PRAAx] le b (K*a)) :
    Γ ⊢[PRAAx] upper (fstT (ap2 DF p (dd c b))) (fstT (ap2 DF q (dd a b)))
      (rateNumerator ((K*(K+one))*monus c a) b p q) (rateDenominator b p q) :=
  upper_with_radius p q a c b _ _ ha hc hac
    (by dsimp only [numerator,denominator]; ipra_le 𝔞(monus c a)*((𝔞(K)+1)*𝔞(a)+𝔞(b))*sl h)

theorem actual_original_digamma_upper_slope_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 2) ⋏ (le (var 2) (var 0) ⋏ le (var 0) (var 1))) ⟶
      upper (fstT (ap2 DF (var 3) (dd (var 1) (var 2)))) (fstT (ap2 DF (var 4) (dd (var 0) (var 2))))
        (rateNumerator (two*monus (var 1) (var 0)) (var 2) (var 3) (var 4)) (rateDenominator (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (unit_upper_at _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaLipschitz
