import IPRADerivations.Analysis.Barnes.Names.GaussianBarnesCanonicalNamed
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateTransport
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateComposition

/-!
# Late rational readback and disk independence of the named Barnes value

The original named sampler has a unit independent rate to the
original rational evaluator at each sufficiently late input
observation. A common late observation and rational disk independence
identify the named evaluators at two distinct certified disk radii.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedFrozen

open_ipra
open GaussianBarnesCanonicalNamed (nameF modulus clock sample_at)
open GaussianBarnesCanonicalNamedDemand (source data frozenData clock_demand late_rate native_source)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at denominator_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalL1 (rawGaussian rawDen)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "V" => GaussianBarnesCanonicalValue.nameF

private theorem frozen_budget (p q s a : PTm n)
    (h : Γ ⊢[PRAAx] le (two*unit p*unit s) (unit a*(two*unit p+unit s))) :
    Γ ⊢[PRAAx] le (rateNumerator one (unit a) (succ p) q*rateDenominator (unit s) p q)
      (rateNumerator one (unit s) p q*rateDenominator (unit a) (succ p) q) := by
  let P := unit p
  let Q := unit q
  let S := unit s
  let W := unit a
  have cleared : Γ ⊢[PRAAx]
      le ((one*(two*P)*Q+W*(two*P+Q))*(S*P*Q)) ((one*P*Q+S*(P+Q))*(W*(two*P)*Q)) := by
    change Γ ⊢[PRAAx] le (two*P*S) (W*(two*P+S)) at h
    ipra_le 𝔞(P)*𝔞(Q)^2*sl h
  have double : Γ ⊢[PRAAx] unit (succ p) ≐ two*P := (pw_succ two p).eqTrans (mul_comm _ _)
  exact le_congr
    (congrMul (congrAdd (congrMul (congrMul (.eqRefl _) double) (.eqRefl _))
      (congrMul (.eqRefl _) (congrAdd double (.eqRefl _)))) (.eqRefl _)).eqSymm
    (congrMul (.eqRefl _) (congrMul (congrMul (.eqRefl _) double) (.eqRefl _))).eqSymm cleared

private theorem read_with (f : PR 2) (p q s a k x R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hk : Γ ⊢[PRAAx] le (clock s R) k)
    (hp : Γ ⊢[PRAAx] le a (succ p)) (hs : Γ ⊢[PRAAx] le a (succ s))
    (hb : Γ ⊢[PRAAx] le (two*unit p*unit s) (unit a*(two*unit p+unit s))) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data x R)) (ap2 V q (frozenData f k x R))
      (rateNumerator one (unit s) p q) (rateDenominator (unit s) p q) := by
  let r := clock p R
  have rate := late_rate modulus f f a r k x x R hf hf (cross_refl _ _ hf.andE₁)
    (clock_demand modulus p R a hp) (le_trans (clock_demand modulus s R a hs) hk)
  have near := distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ (unit_positive a))
    (denominator_positive _ _ _ (unit_positive s)) (frozen_budget p q s a hb)
    (rate_at _ _ _ _ _ _ (succ p) q rate)
  exact distance_congr (sample_at f p x R).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) near

theorem frozen_observations (f : PR 2) (p q s k x R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hk : Γ ⊢[PRAAx] le (clock s R) k) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data x R)) (ap2 V q (frozenData f k x R))
      (rateNumerator one (unit s) p q) (rateDenominator (unit s) p q) := by
  refine .orE (le_total p s) ?_ ?_
  · have lp : le p s :: Γ ⊢[PRAAx] le (succ p) (succ s) :=
      le_congr (succ_eq_add_one _).eqSymm (succ_eq_add_one _).eqSymm (add_le_add_right one Prf.hyp0)
    have double : le p s :: Γ ⊢[PRAAx] unit (succ p) ≐ two*unit p := (pw_succ two p).eqTrans (mul_comm _ _)
    have hb : le p s :: Γ ⊢[PRAAx] le (two*unit p*unit s) ((two*unit p)*(two*unit p+unit s)) :=
      le_of_eq_add (d := two*unit p*(two*unit p)) (by ipra_ring)
    exact read_with f p q s (succ p) k x R hf.wk hk.wk (le_refl _) lp
      (le_congr (.eqRefl _) (congrMul double.eqSymm (.eqRefl _)) hb)
  · have hb : le s p :: Γ ⊢[PRAAx] le (two*unit p*unit s) (unit s*(two*unit p+unit s)) :=
      le_of_eq_add (d := unit s*unit s) (by ipra_ring)
    exact read_with f p q s s k x R hf.wk hk.wk (le_trans Prf.hyp0 (le_succ_self p)) (le_succ_self s) hb

theorem frozen_rate (f : PR 2) (s k x R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hk : Γ ⊢[PRAAx] le (clock s R) k) :
    Γ ⊢[PRAAx] independentRate (nameF f) V (data x R) (frozenData f k x R) one (unit s) := by
  refine .allI (.allI ?_)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  have h : Δ ⊢[PRAAx] source f (sh x) (sh R) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hf.shift.shift
  have later : Δ ⊢[PRAAx] le (clock (sh s) (sh R)) (sh k) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hk.shift.shift
  simpa only [independentRate,GaussianBarnesCanonicalNamedDemand.subst_data,GaussianBarnesCanonicalNamedDemand.subst_frozenData,
    GaussianCoefficientNameBounds.subst_unit,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift,sh,Δ] using
      frozen_observations f (var 1) (var 0) (sh s) (sh k) (sh x) (sh R) h later

private theorem radius_observations (f : PR 2) (p x R S : PTm n)
    (hr : Γ ⊢[PRAAx] source f x R) (hs : Γ ⊢[PRAAx] source f x S) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data x R)) (ap2 (nameF f) p (data x S)) (num 4) (unit p) := by
  let k := clock p R+clock p S
  let q := ap2 f k x
  let a := data x R
  let b := data x S
  let A := frozenData f k x R
  let B := frozenData f k x S
  let U := unit p
  have hl := frozen_rate f p k x R hr (le_add_right (clock p R) (clock p S))
  have hq := frozen_rate f p k x S hs (le_add_left (clock p S) (clock p R))
  have eq : Γ ⊢[PRAAx] crossEquivalent V V A B :=
    GaussianBarnesCanonicalProperness.independent_radii (rawGaussian q) R S (rawDen q)
      (native_source f k x R hr) (native_source f k x S hs)
  have reg := GaussianBarnesCanonicalNamed.name_regular f x R hr
  have hu := unit_positive (Γ := Γ) p
  have first := GaussianNamedRateTransport.transport (nameF f) V (nameF f) V a A a B one U hu hl
    (cross_refl _ _ reg) (cross_symm _ _ _ _ eq)
  have join := GaussianNamedRateComposition.same_denominator (nameF f) V (nameF f) a B b one U one hu first
    (GaussianNamedRateComposition.symmetric (nameF f) V b B one U hu hq)
  have approx := GaussianNamedInverseRate.diagonal_rate (nameF f) (nameF f) a b (one+one) U p hu join
  exact distance_radius_mono _ _ _ _ (num 4) U (positive_product _ _ hu hu) hu
    (le_of_eq_add (d := zero) (by dsimp only [U]; ipra_ring)) approx

theorem independent_radii (f : PR 2) (x R S : PTm n)
    (hr : Γ ⊢[PRAAx] source f x R) (hs : Γ ⊢[PRAAx] source f x S) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF f) (data x R) (data x S) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 4)
    (GaussianBarnesCanonicalNamed.name_regular f x R hr) (GaussianBarnesCanonicalNamed.name_regular f x S hs)
  refine .allI ?_
  let sh (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have r : Δ ⊢[PRAAx] source f (sh x) (sh R) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hr.shift
  have s : Δ ⊢[PRAAx] source f (sh x) (sh S) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hs.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,GaussianBarnesCanonicalNamedDemand.subst_data,
    PTm.subst_num,Syn.shift,sh,Δ] using radius_observations f (var 0) (sh x) (sh R) (sh S) r s

theorem source_widen (f : PR 2) (x R S : PTm n)
    (hr : Γ ⊢[PRAAx] source f x R) (hRS : Γ ⊢[PRAAx] le R S) :
    Γ ⊢[PRAAx] source f x S := by
  refine .andI hr.andE₁ (.allI ?_)
  let sh (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have r : Δ ⊢[PRAAx] source f (sh x) (sh R) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hr.shift
  have order : Δ ⊢[PRAAx] le (sh R) (sh S) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hRS.shift
  have b := GaussianRootApproximationWitness.point_at f (sh R) (sh x) (var 0) r.andE₂
  simpa only [GaussianRootApproximationWitness.pointBounds,Syn.shift,sh,Δ,one,ConciseIPRA.PTm.subst_zero,
    ConciseIPRA.PTm.subst_succ] using
      GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one)
        (mul_le_mul_right one order) b

theorem proper (f g : PR 2) (x y R S : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hg : Γ ⊢[PRAAx] source g y S)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data x R) (data y S) := by
  let T := R+S
  have fr := source_widen f x R T hf (le_add_right R S)
  have gr := source_widen g y S T hg (le_add_left S R)
  exact cross_trans (nameF f) (nameF f) (nameF g) (data x R) (data x T) (data y S)
    (independent_radii f x R T hf fr)
    (cross_trans (nameF f) (nameF g) (nameF g) (data x T) (data y T) (data y S)
      (GaussianBarnesCanonicalNamed.proper f g x y T fr gr he) (independent_radii g y T S gr hg))

theorem actual_Barnes_named_late_rational_rate_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source f (var 0) (var 1) ⟶ le (clock (var 2) (var 1)) (var 3) ⟶
        independentRate (nameF f) V (data (var 0) (var 1)) (frozenData f (var 3) (var 0) (var 1))
          one (unit (var 2))) :=
  closeUniv 4 (.impI (.impI (frozen_rate f _ _ _ _ Prf.hyp0.wk Prf.hyp0)))

theorem actual_Barnes_named_independent_disk_proper_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source f (var 0) (var 2) ⟶ source g (var 1) (var 3) ⟶ crossEquivalent f g (var 0) (var 1) ⟶
        crossEquivalent (nameF f) (nameF g) (data (var 0) (var 2)) (data (var 1) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (proper f g _ _ _ _ Prf.hyp0.wk.wk Prf.hyp0.wk Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedFrozen
