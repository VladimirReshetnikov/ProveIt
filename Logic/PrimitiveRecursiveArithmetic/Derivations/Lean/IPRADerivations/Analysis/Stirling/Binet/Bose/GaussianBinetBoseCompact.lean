import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.Arctangent.GaussianBinetArctangentTimeRate
import IPRADerivations.Analysis.Stirling.Binet.Bose.GaussianBinetBoseReciprocalTimeRate
import IPRADerivations.Analysis.Euler.PowerScaling.GaussianEulerNamedPowerScalingPowerFrozen

/-!
# The original second-Binet compact quadrature away from zero

The positive initial time (A/E) bounds both original reciprocal
samplers by (E) throughout the panel. Together with a time horizon,
this gives a common modulus for the original arctangent and Bose
reciprocal product.
-/

set_option autoImplicit false
set_option maxHeartbeats 640000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBoseCompact

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetArctangentQuadrature (fixedData subst_fixedData)
open GaussianBinetLaplaceStrip (tagNumerator)
open GaussianCompactRiemannName (evaluatorName nameData sampledModulus inside localBody)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedInverseRate (independentRate)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "F" => GaussianBinetBoseIntegrandBound.nameF
local notation "fd" => GaussianBinetBoseIntegrandBound.data
local notation "Atan" => GaussianBinetArctangentQuadrature.nameF
local notation "atanData" => GaussianBinetArctangentQuadrature.data
local notation "Inv" => GaussianBinetBoseDenominator.reciprocalF
local notation "invData" => GaussianBinetBoseDenominator.reciprocalData
local notation "AtanGain" => GaussianBinetArctangentTimeRate.gain
local notation "InvGain" => GaussianBinetBoseReciprocalTimeRate.gain

def gain (D E T : PTm n) : PTm n := E*AtanGain D T+(T*D)*InvGain E T

def source (X D sign T A C E : PTm n) : Fm PTm n :=
  GaussianRightHalfPlaneLogarithm.source X D sign ⋏ (le one A ⋏ (le one E ⋏ le (A+C) (E*T)))

def evaluatorTerm (p t x : PTm n) : PTm n :=
  ap2 F p (fd (fstT x) (fstT (sndT x)) (fstT (sndT (sndT x))) (sndT (sndT (sndT x))) (tagNumerator t) (sndT t))
def evaluatorF : PR 3 := PTm.toPR (evaluatorTerm (var 0) (var 1) (var 2))
abbrev nameF : PR 2 := GaussianCompactRiemannName.nameF evaluatorF
def data (X Y D sign T A C E : PTm n) : PTm n :=
  GaussianCompactRiemannName.data (E+A) C E (gain D E T) T (fixedData X Y D sign)

@[simp] theorem subst_gain {m : ℕ} (σ : Fin n → PTm m) (D E T : PTm n) :
    Syn.subst σ (gain D E T) = gain (Syn.subst σ D) (Syn.subst σ E) (Syn.subst σ T) := by simp [gain]
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (X D sign T A C E : PTm n) :
    (source X D sign T A C E).subst σ = source (Syn.subst σ X) (Syn.subst σ D) (Syn.subst σ sign)
      (Syn.subst σ T) (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ E) := by
  simp [source,GaussianRightHalfPlaneLogarithm.source,GaussianRightHalfPlaneArgument.source]
@[simp] theorem subst_evaluatorTerm {m : ℕ} (σ : Fin n → PTm m) (p t x : PTm n) :
    Syn.subst σ (evaluatorTerm p t x) = evaluatorTerm (Syn.subst σ p) (Syn.subst σ t) (Syn.subst σ x) := by simp [evaluatorTerm]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (X Y D sign T A C E : PTm n) :
    Syn.subst σ (data X Y D sign T A C E) =
      data (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ D) (Syn.subst σ sign)
        (Syn.subst σ T) (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ E) := by simp [data]

theorem evaluator_at (p t X Y D sign : PTm n) :
    Γ ⊢[PRAAx] ap3 evaluatorF p t (fixedData X Y D sign) ≐ ap2 F p (fd X Y D sign (tagNumerator t) (sndT t)) := by
  let x := fixedData X Y D sign
  have read : Γ ⊢[PRAAx] ap3 evaluatorF p t x ≐ evaluatorTerm p t x := by
    simpa only [evaluatorF,ap3,subst_evaluatorTerm,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (evaluatorTerm (var 0) (var 1) (var 2) : PTm 3) ![p,t,x]
  have x₁ : Γ ⊢[PRAAx] sndT x ≐ pairT Y (pairT D sign) := snd_pair _ _
  have x₂ := (congrSnd x₁).eqTrans (snd_pair Y (pairT D sign))
  have decode := Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
    (ap2 F (var 0) (fd (var 1) (var 2) (var 3) (var 4) (tagNumerator (var 5)) (sndT (var 5))) : PTm 6)
    (σ := ![p,fstT x,fstT (sndT x),fstT (sndT (sndT x)),sndT (sndT (sndT x)),t])
    (σ' := ![p,X,Y,D,sign,t]) (fun j => by
      fin_cases j
      · exact .eqRefl _
      · exact fst_pair _ _
      · exact (congrFst x₁).eqTrans (fst_pair _ _)
      · exact (congrFst x₂).eqTrans (fst_pair _ _)
      · exact (congrSnd x₂).eqTrans (snd_pair _ _)
      · exact .eqRefl _)
  exact read.eqTrans (by simpa [evaluatorTerm] using decode)

theorem tag_lower (A C E t : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hE : Γ ⊢[PRAAx] le one E)
    (ht : Γ ⊢[PRAAx] inside (E+A) C E t) :
    Γ ⊢[PRAAx] le one (tagNumerator t) ⋏ le (sndT t) (E*tagNumerator t) := by
  let a := fstT t
  let b := sndT t
  let n := tagNumerator t
  have left : Γ ⊢[PRAAx] le b a :=
    RationalValueBounds.positive_cancel hE (le_trans
      (le_of_eq_add (d := A*b) (by ipra_ring : Γ ⊢[PRAAx] (E+A)*b ≐ E*b+A*b)) ht.andE₂.andE₂.andE₁)
  have line : Γ ⊢[PRAAx] le ((E+A)*b) (E*(b+n)) := le_congr (.eqRefl _) (congrMul (.eqRefl E) (eq_add_of_le left)) ht.andE₂.andE₂.andE₁
  have lower : Γ ⊢[PRAAx] le b (E*n) := by ipra_le sl line+𝔞(b)*sl hA
  exact .andI (GaussianDominantScalarOrder.factor_positive_left n E
    (le_congr (.eqRefl _) (mul_comm E n) (le_trans ht.andE₂.andE₁ lower))) lower

theorem tag_upper (A C E T t : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hT : Γ ⊢[PRAAx] le (A+C) (E*T)) (ht : Γ ⊢[PRAAx] inside (E+A) C E t) :
    Γ ⊢[PRAAx] le (tagNumerator t) (T*sndT t) :=
  (GaussianBinetLaplaceStrip.tag_inside t A C E T hE hT ht).andE₂

theorem arctangent_bound (p X Y D sign a b T : PTm n) (hz : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source X D sign)
    (hb : Γ ⊢[PRAAx] le one b) (hi : Γ ⊢[PRAAx] le a (T*b)) :
    Γ ⊢[PRAAx] bounded (ap2 Atan p (atanData X Y D sign a b)) (T*D) one := by
  have hX := hz.andE₁.andE₁
  apply GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (positive_product _ _ hb hX) (le_refl one) ?_
    (GaussianBinetArctangentQuadratureBound.name_bound p X Y D sign a b hz hb)
  ipra_le 𝔞(D)*sl hi+𝔞(T*D*b)*sl hX

theorem arctangent_samples (X Y D sign a b T : PTm n) (hz : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source X D sign)
    (hb : Γ ⊢[PRAAx] le one b) (hi : Γ ⊢[PRAAx] le a (T*b)) :
    Γ ⊢[PRAAx] GaussianNamedMultiplyRate.sampleBound Atan (atanData X Y D sign a b) (T*D) := by
  refine .allI ?_
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have zs : Δ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source (s X) (s D) (s sign) :=
    by simpa [Δ,s,Fm.shift,Syn.shift,GaussianRightHalfPlaneLogarithm.source,GaussianRightHalfPlaneArgument.source] using hz.shift
  have bs : Δ ⊢[PRAAx] le one (s b) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hb.shift
  have us : Δ ⊢[PRAAx] le (s a) (s T*s b) := by simpa [Δ,s,Fm.shift,Syn.shift] using hi.shift
  simpa only [GaussianNamedMultiplyRate.sampleBound,Syn.shift,s,GaussianBinetArctangentQuadrature.subst_data,PTm.subst_mul] using
    arctangent_bound (var 0) (s X) (s Y) (s D) (s sign) (s a) (s b) (s T) zs bs us

theorem time_rate (X Y D sign a b c d E T H Q : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source X D sign)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d)
    (lo : Γ ⊢[PRAAx] le b (E*a)) (lo' : Γ ⊢[PRAAx] le d (E*c))
    (hi : Γ ⊢[PRAAx] le a (T*b)) (hi' : Γ ⊢[PRAAx] le c (T*d))
    (hQ : Γ ⊢[PRAAx] le one Q) (h : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) H Q) :
    Γ ⊢[PRAAx] independentRate F F (fd X Y D sign a b) (fd X Y D sign c d) (gain D E T*H) Q := by
  have p := GaussianBinetArctangentTimeRate.independent_rate X Y D sign a b c d T H Q hz hb hd hi' hQ h
  have q := GaussianBinetBoseReciprocalTimeRate.inverse_rate a b c d E T H Q ha hb hc hd lo lo' hi hi' hQ h
  have proof := GaussianEulerNamedPowerScalingPowerFrozen.multiply_same_denominator Atan Inv Atan Inv
    (atanData X Y D sign a b) (invData a b) (atanData X Y D sign c d) (invData c d)
    (AtanGain D T*H) (InvGain E T*H) Q E (T*D) hQ
    (GaussianBinetArctangentQuadrature.regular X Y D sign a b hz hb) (GaussianBinetBoseDenominator.reciprocal_regular a b ha hb)
    (GaussianBinetArctangentQuadrature.regular X Y D sign c d hz hd) (GaussianBinetBoseDenominator.reciprocal_regular c d hc hd)
    (GaussianBinetBoseReciprocalTimeRate.inverse_samples_bound a b E ha hb lo) (arctangent_samples X Y D sign c d T hz hd hi') p q
  exact GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _
    (by unfold gain; ipra_ring) (.eqRefl _) proof

theorem local_rate (X Y D sign T A C E t u H Q : PTm n)
    (h : Γ ⊢[PRAAx] source X D sign T A C E)
    (hQ : Γ ⊢[PRAAx] le one Q)
    (ht : Γ ⊢[PRAAx] inside (E+A) C E t) (hu : Γ ⊢[PRAAx] inside (E+A) C E u)
    (near : Γ ⊢[PRAAx] distanceBounded (GaussianCompactRiemannName.value t) (GaussianCompactRiemannName.value u) H Q) :
    Γ ⊢[PRAAx] independentRate (evaluatorName evaluatorF) (evaluatorName evaluatorF)
      (nameData t (fixedData X Y D sign)) (nameData u (fixedData X Y D sign)) (gain D E T*H) Q := by
  let a := tagNumerator t
  let b := sndT t
  let c := tagNumerator u
  let d := sndT u
  have tl := tag_lower A C E t h.andE₂.andE₁ h.andE₂.andE₂.andE₁ ht
  have ul := tag_lower A C E u h.andE₂.andE₁ h.andE₂.andE₂.andE₁ hu
  have decoded := GaussianBinetLaplaceStrip.tag_source t u A C E T H Q h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂ hQ ht hu near
  have rate := time_rate X Y D sign a b c d E T H Q h.andE₁ tl.andE₁ decoded.andE₁ ul.andE₁ decoded.andE₂.andE₁
    tl.andE₂ ul.andE₂ decoded.andE₂.andE₂.andE₂.andE₁ decoded.andE₂.andE₂.andE₂.andE₂.andE₁ hQ
    decoded.andE₂.andE₂.andE₂.andE₂.andE₂
  let s (v : PTm n) := Syn.shift (Syn.shift v)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have shifted : Δ ⊢[PRAAx] independentRate F F (fd (s X) (s Y) (s D) (s sign) (tagNumerator (s t)) (sndT (s t)))
      (fd (s X) (s Y) (s D) (s sign) (tagNumerator (s u)) (sndT (s u))) (gain (s D) (s E) (s T)*s H) (s Q) :=
    by simpa [Δ,s,Fm.shift,Syn.shift,a,b,c,d] using rate.shift.shift
  refine .allI (.allI ?_)
  have left := (GaussianCompactRiemannName.evaluator_at (Γ := Δ) evaluatorF (var 1) (s t) (fixedData (s X) (s Y) (s D) (s sign))).eqTrans
    (evaluator_at (var 1) (s t) (s X) (s Y) (s D) (s sign))
  have right := (GaussianCompactRiemannName.evaluator_at (Γ := Δ) evaluatorF (var 0) (s u) (fixedData (s X) (s Y) (s D) (s sign))).eqTrans
    (evaluator_at (var 0) (s u) (s X) (s Y) (s D) (s sign))
  simpa only [independentRate,Δ,s,Syn.shift,GaussianCompactRiemannName.subst_nameData,subst_fixedData,subst_gain,PTm.subst_mul] using
    GaussianRationalDistanceOrder.distance_congr left.eqSymm right.eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianNamedInverseRate.rate_at _ _ _ _ _ _ (var 1) (var 0) shifted)

theorem sampled_modulus (X Y D sign T A C E : PTm n) (h : Γ ⊢[PRAAx] source X D sign T A C E) :
    Γ ⊢[PRAAx] sampledModulus evaluatorF (E+A) C E (gain D E T) (fixedData X Y D sign) := by
  let s (v : PTm n) := Syn.shift (Syn.shift (Syn.shift (Syn.shift v)))
  let Δ := (((Γ.map Fm.shift).map Fm.shift).map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] source (s X) (s D) (s sign) (s T) (s A) (s C) (s E) :=
    by simpa only [Δ,s,Fm.shift,Syn.shift,subst_source] using h.shift.shift.shift.shift
  refine .allI (.allI (.allI (.allI (.impI (.impI (.impI (.impI ?_)))))))
  simpa only [localBody,Δ,s,Syn.shift,subst_gain,subst_fixedData,PTm.subst_add] using
    local_rate (s X) (s Y) (s D) (s sign) (s T) (s A) (s C) (s E) (var 3) (var 2) (var 1) (var 0)
      hs.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

theorem compact_input (X Y D sign T A C E : PTm n) (h : Γ ⊢[PRAAx] source X D sign T A C E) :
    Γ ⊢[PRAAx] GaussianCompactRiemannName.input evaluatorF (E+A) C E (gain D E T) T (fixedData X Y D sign) :=
  .andI (le_trans h.andE₂.andE₂.andE₁ (le_add_right E A)) (.andI h.andE₂.andE₂.andE₁
    (.andI (le_trans (le_add_left C A) h.andE₂.andE₂.andE₂) (sampled_modulus X Y D sign T A C E h)))

theorem regular (X Y D sign T A C E : PTm n) (h : Γ ⊢[PRAAx] source X D sign T A C E) :
    Γ ⊢[PRAAx] pointCN nameF (data X Y D sign T A C E) :=
  GaussianCompactRiemannName.name_regular _ _ _ _ _ _ _ (compact_input X Y D sign T A C E h)

theorem actual_second_Binet_positive_compact_quadrature_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      pointCN nameF (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))) :=
  closeUniv 8 (.impI (regular _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetBoseCompact
