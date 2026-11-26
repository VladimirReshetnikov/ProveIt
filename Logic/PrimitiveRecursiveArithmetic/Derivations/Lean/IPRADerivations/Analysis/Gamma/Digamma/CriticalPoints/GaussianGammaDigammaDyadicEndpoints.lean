import IPRADerivations.Analysis.Gamma.Digamma.CriticalPoints.GaussianGammaDigammaCriticalSigns
import IPRADerivations.Analysis.Gamma.Digamma.CriticalPoints.GaussianGammaDigammaDyadicMesh
import IPRADerivations.Analysis.Gamma.Digamma.CriticalPoints.GaussianGammaDigammaGridSign
import IPRADerivations.Analysis.Gamma.Digamma.Series.GaussianGammaDigammaRescaling

/-!
# Signs of the original digamma observations at the dyadic endpoints

The quarter margins persist at the explicit observation clock p+6,
after expressing one and two using the actual grid denominator.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaDyadicEndpoints

open_ipra
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)
open GaussianGammaDigammaCriticalSigns (quarter negativeQuarter one_upper two_lower)
open GaussianGammaDigammaDyadicCrossing (sample)
open GaussianGammaDigammaDyadicMesh (clock grid grid_positive grid_threshold)
open GaussianGammaDigammaGridSign (negative_from_upper nonnegative_from_upper)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm)
open GaussianNamedPositiveExponentialOrder (real_order_at)
open GaussianPositiveRealArithmetic (sign)
open GaussianRationalHorner (scalar_congr)
open GaussianRationalMetric (qnegative qnegative_canonical)
open GaussianRationalSyntheticDivision (qzero_add)
open GaussianStirlingGammaLogarithm (source)
open RationalArithmetic (represents)
open RationalValueBounds (upper_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "DF" => GaussianGammaDigammaNative.nameF
local notation "dd" => GaussianGammaDigammaNative.data

private theorem quarter_represents :
    Γ ⊢[PRAAx] represents (fstT (quarter : PTm n)) (ZT.ofNat one) (num 4) :=
  GaussianGammaDigammaHarmonicCells.point_fraction_represents one (num 4) (by ipra_le 3)

private theorem negative_quarter_represents :
    Γ ⊢[PRAAx] represents (fstT (negativeQuarter : PTm n)) (-ZT.ofNat one) (num 4) := by
  let x : PTm n := quarter
  have q := RationalRepresentations.represents_negative (fstT x) (ZT.ofNat one) (num 4)
    (quarter_represents (Γ := Γ))
  have e := (congrFst (qzero_add (Γ := Γ) (qnegative x) (qnegative_canonical x))).eqTrans
    (fst_pair (RationalArithmetic.negative (fstT x)) (RationalArithmetic.negative (sndT x)))
  exact scalar_congr e.eqSymm (.eqRefl _) (.eqRefl _) q

private theorem data_congr (a b c d : PTm n) (ha : Γ ⊢[PRAAx] a ≐ c) (hb : Γ ⊢[PRAAx] b ≐ d) :
    Γ ⊢[PRAAx] dd a b ≐ dd c d := by
  simpa only [GaussianGammaDigammaNative.subst_data, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one] using
    Prf.eqCongr (dd (var 0) (var 1) : PTm 2) (σ := ![a,b]) (σ' := ![c,d])
      (fun j => by fin_cases j; exacts [ha,hb])

private theorem endpoint_rescaling (a N i : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (ha : Γ ⊢[PRAAx] le one a) (e : Γ ⊢[PRAAx] N*a ≐ N+i) :
    Γ ⊢[PRAAx] crossEquivalent DF DF (dd (N+i) N) (dd a one) := by
  have base : Γ ⊢[PRAAx] source a one := .andI ha (le_refl one)
  exact cross_data_congr DF DF (dd (N*a) (N*one)) (dd (N+i) N) (dd a one) (dd a one)
    (data_congr _ _ _ _ e (by ipra_ring)) (.eqRefl _)
    (GaussianGammaDigammaRescaling.original_rescaling a one N base hN)

theorem left_sign (p : PTm n) :
    Γ ⊢[PRAAx] neg (sign (sample (clock p) (grid p) zero)) := by
  let N := grid p
  let t := clock p
  let c : PTm n := negativeQuarter
  let x := dd (N+zero) N
  have hx := endpoint_rescaling (Γ := Γ) one N zero (grid_positive p) (le_refl one) (by ipra_ring)
  have ord := GaussianNamedRealOrderTransport.transport DF DF constantF constantF x (dd one one) c c
    hx (cross_refl _ _ (constant_regular c)) (one_upper (Γ := Γ)).andE₁
  have h := real_order_at DF constantF x c t t ord
  exact negative_from_upper (sample t N zero) (fstT c) N (grid_threshold p)
    negative_quarter_represents (upper_congr (.eqRefl _) (congrFst (constant_at t c)) (.eqRefl _) (.eqRefl _) h)

theorem right_sign (p : PTm n) :
    Γ ⊢[PRAAx] sign (sample (clock p) (grid p) (grid p)) := by
  let N := grid p
  let t := clock p
  let c : PTm n := quarter
  let x := dd (N+N) N
  have hx := endpoint_rescaling (Γ := Γ) two N N (grid_positive p) (by ipra_le 1) (by ipra_ring)
  have ord := GaussianNamedRealOrderTransport.transport constantF constantF DF DF c c (dd two one) x
    (cross_refl _ _ (constant_regular c)) (cross_symm _ _ _ _ hx) (two_lower (Γ := Γ)).andE₁
  have h := real_order_at constantF DF c x t t ord
  exact nonnegative_from_upper (sample t N N) (fstT c) N (grid_threshold p)
    quarter_represents (upper_congr (congrFst (constant_at t c)) (.eqRefl _) (.eqRefl _) (.eqRefl _) h)

theorem endpoint_signs (p : PTm n) :
    Γ ⊢[PRAAx] neg (sign (sample (clock p) (grid p) zero)) ⋏
      sign (sample (clock p) (grid p) (grid p)) :=
  .andI (left_sign p) (right_sign p)

theorem actual_original_digamma_grid_endpoints_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (neg (sign (sample (clock (var 0)) (grid (var 0)) zero)) ⋏
      sign (sample (clock (var 0)) (grid (var 0)) (grid (var 0)))) :=
  closeUniv 1 (endpoint_signs (var 0))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaDyadicEndpoints
