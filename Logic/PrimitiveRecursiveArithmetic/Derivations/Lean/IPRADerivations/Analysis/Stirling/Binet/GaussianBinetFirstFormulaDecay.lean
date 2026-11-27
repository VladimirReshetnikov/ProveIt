import IPRADerivations.Analysis.Stirling.Binet.StirlingBounds.Vertical.GaussianBinetStirlingVerticalBound
import IPRADerivations.Analysis.Stirling.Binet.Laplace.Exhaustion.GaussianBinetLaplaceImproperBound
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRecurrencePinning

/-!
# The actual first-formula discrepancy vanishes along right translations

The Stirling and improper Laplace bounds give a uniform decay
envelope for their normalized difference. Both evaluations at an
internal shift are the original names on the translated chart.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBinetFirstFormulaDecay

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianCompactRiemannName
  (sampleData field0 field1 field2 field3 field4 field0_at field1_at field2_at field3_at field4_at)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianLogGammaEulerHead (shifted_source)
open GaussianLogGammaEulerResidualRadius (radius source_of_right_half_plane)
open GaussianNamedInverseRate (diagonal_rate)
open GaussianNamedRecurrencePinning (regularFamily decayEnvelope decayAt)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (positive_product qzero)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bounded_difference)
open GaussianReconstructionRoots (distance_zero_iff norm_from_distance)
open GaussianRightHalfPlaneLogarithm (source)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "S" => GaussianBinetStirlingRemainder.nameF
local notation "sd" => GaussianBinetStirlingRemainder.data
local notation "J" => GaussianBinetLaplaceImproperName.nameF
local notation "jd" => GaussianBinetLaplaceImproperName.data

def laplaceData (A B D sign : PTm n) : PTm n := jd A B D sign (radius A B)
def nameF : PR 2 := GaussianNamedDifference.nameF S J
def data (A B D sign x : PTm n) : PTm n := GaussianNamedDifference.data (sd A B D sign x) (laplaceData A B D sign)

ipra_subst laplaceData
ipra_subst data

theorem laplace_regular (A B D sign : PTm n) (h : Γ ⊢[PRAAx] source A D sign) :
    Γ ⊢[PRAAx] pointCN J (laplaceData A B D sign) :=
  GaussianBinetLaplaceImproperName.regular A B D sign (radius A B) (source_of_right_half_plane A B D sign h)

theorem regular (A B D sign x : PTm n) (h : Γ ⊢[PRAAx] source A D sign) :
    Γ ⊢[PRAAx] pointCN nameF (data A B D sign x) :=
  GaussianNamedDifference.name_regular _ _ _ _ (GaussianBinetStirlingRemainder.regular A B D sign x h)
    (laplace_regular A B D sign h)

private theorem observation_bound (p A B D sign x : PTm n) (h : Γ ⊢[PRAAx] source A D sign) :
    Γ ⊢[PRAAx] bounded (ap2 nameF p (data A B D sign x))
      ((two*D+num 18*B)*unit p+num 9*(num 12*A)) ((num 12*A)*unit p) := by
  let U := unit p
  let E := num 12*A
  let Q := E*U
  let a := sd A B D sign x
  let b := laplaceData A B D sign
  let u := ap2 S p a
  let v := ap2 J p b
  have hu := unit_positive (Γ := Γ) p
  have he : Γ ⊢[PRAAx] le one E := positive_product (num 12) A (by ipra_le 11) h.andE₁.andE₁
  have hQ := positive_product E U he hu
  have stir := diagonal_rate S constantF a qzero (D+num 18*B) E p he
    (GaussianBinetStirlingVerticalBound.remainder_rate A B D sign x h)
  have left := distance_congr (.eqRefl _) (constant_at p qzero) (.eqRefl _) (.eqRefl _) stir
  have r : Γ ⊢[PRAAx] bounded u ((D+num 18*B)*U+two*E) Q :=
    (distance_zero_iff _ _ _ hQ).iffMp left
  have lap := GaussianBinetLaplaceImproperBound.improper_bound p A B D sign (radius A B)
    (source_of_right_half_plane A B D sign h)
  have hV := unit_positive (Γ := Γ) (succ p)
  have right : Γ ⊢[PRAAx] bounded v (D*U+E) Q := by
    apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ (positive_product _ _ he (le_refl one)) hV) hQ ?_ lap
    dsimp only [GaussianBinetLaplaceStripTail.tailNumerator,GaussianBinetLaplaceStripTail.tailDenominator,E,Q,U]
    have clock : Γ ⊢[PRAAx] unit (succ p) ≐ unit p*two := pw_succ two p
    have grow : Γ ⊢[PRAAx] le (unit p) (unit (succ p)) :=
      le_congr (.eqRefl _) clock.eqSymm (by ipra_le 𝔞(unit p))
    ipra_le 144*𝔞(A)^2*sl grow
  have both := bounded_difference _ _ _ _ _ _ hQ hQ r right
  have mid : Γ ⊢[PRAAx] bounded (GaussianRationalMetric.qsub u v) ((two*D+num 18*B)*U+num 3*E) Q :=
    bounded_radius_mono _ _ _ _ _ (positive_product Q Q hQ hQ) hQ
      (by dsimp only [Q]; ipra_le 0) both
  have close := GaussianNamedDifference.sample_error S J a b p (GaussianBinetStirlingRemainder.regular A B D sign x h)
    (laplace_regular A B D sign h)
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ hu hQ) hQ
    (by dsimp only [Q,E,U]; ipra_le 0)
    (norm_from_distance _ _ _ _ _ _ hu hQ close mid)

def parameters (A B D sign x : PTm n) : PTm n := sampleData A B D sign x zero
def family : PTm 2 :=
  data (field0 (var 1)+var 0*field2 (var 1)) (field1 (var 1)) (field2 (var 1)) (field3 (var 1)) (field4 (var 1))

theorem family_at (A B D sign x j : PTm n) : Γ ⊢[PRAAx]
    inst2 family j (parameters A B D sign x) ≐ data (A+j*D) B D sign x := by
  let a := parameters A B D sign x
  have e0 := field0_at (Γ := Γ) A B D sign x zero
  have e1 := field1_at (Γ := Γ) A B D sign x zero
  have e2 := field2_at (Γ := Γ) A B D sign x zero
  have e3 := field3_at (Γ := Γ) A B D sign x zero
  have e4 := field4_at (Γ := Γ) A B D sign x zero
  have raw := Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
    (data (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
    (σ := ![field0 a+j*field2 a,field1 a,field2 a,field3 a,field4 a]) (σ' := ![A+j*D,B,D,sign,x])
    (fun i => by fin_cases i; exact congrAdd e0 (congrMul (.eqRefl j) e2); exact e1; exact e2; exact e3; exact e4)
  simpa only [inst2,family,subst_data,PTm.subst_add,PTm.subst_mul,Syn.subst_var,
    GaussianCompactRiemannName.subst_field0,GaussianCompactRiemannName.subst_field1,GaussianCompactRiemannName.subst_field2,
    GaussianCompactRiemannName.subst_field3,GaussianCompactRiemannName.subst_field4,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,a] using raw

theorem family_regular (A B D sign x : PTm n) (h : Γ ⊢[PRAAx] source A D sign) :
    Γ ⊢[PRAAx] regularFamily nameF family (parameters A B D sign x) := by
  refine .allI ?_
  let s (a : PTm n) := Syn.shift a
  let Δ := Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (s A) (s D) (s sign) := by simpa [Δ,s,Fm.shift,Syn.shift,source,GaussianRightHalfPlaneArgument.source] using h.shift
  have proof := regular (s A+var 0*s D) (s B) (s D) (s sign) (s x) (shifted_source (var 0) _ _ _ hs)
  have read := family_at (Γ := Δ) (s A) (s B) (s D) (s sign) (s x) (var 0)
  have back : Δ ⊢[PRAAx] pointCN nameF (inst2 family (var 0) (parameters (s A) (s B) (s D) (s sign) (s x))) := by
    simpa only [GaussianEuclideanDistanceName.subst_pointCN,Syn.inst_zero,Syn.subst_var,Matrix.cons_val_zero] using
      Prf.eqSubst (pointCN nameF (var 0) : Fm PTm 1) ![data (s A+var 0*s D) (s B) (s D) (s sign) (s x)]
        ![inst2 family (var 0) (parameters (s A) (s B) (s D) (s sign) (s x))]
        (fun i => by fin_cases i; exact read.eqSymm) (by simpa only [GaussianEuclideanDistanceName.subst_pointCN,Syn.subst_var,Matrix.cons_val_zero] using proof)
  simpa only [regularFamily,parameters,s,Δ,Syn.shift,GaussianCompactRiemannName.subst_sampleData,ConciseIPRA.PTm.subst_zero] using back

theorem decay_observation (p A B D sign x j : PTm n)
    (h : Γ ⊢[PRAAx] source A D sign) (hj : Γ ⊢[PRAAx] le one j) :
    Γ ⊢[PRAAx] bounded (ap2 nameF p (inst2 family j (parameters A B D sign x)))
      ((two*D+num 18*B)*unit p+num 9*j) (j*unit p) := by
  let a := A+j*D
  let t := num 12*a
  let U := unit p
  let b := two*D+num 18*B
  have hs := shifted_source j A D sign h
  have hU := unit_positive (Γ := Γ) p
  have hT : Γ ⊢[PRAAx] le one t := positive_product (num 12) a (by ipra_le 11) hs.andE₁.andE₁
  have hjt : Γ ⊢[PRAAx] le j t := by
    dsimp only [t,a]
    ipra_le 12*𝔞(A)+11*𝔞(j)+12*𝔞(j)*sl h.andE₂
  have jt : Γ ⊢[PRAAx] le j (num 12*a) := hjt
  have out := bounded_radius_mono _ _ _ (b*U+num 9*j) (j*U) (positive_product t U hT hU)
    (positive_product j U hj hU)
    (by
      dsimp only [b,U,t]
      ipra_le 𝔞(two*D+num 18*B)*𝔞(unit p)^2*sl jt)
    (observation_bound p a B D sign x hs)
  exact GaussianRationalReciprocal.bound_congr (congrAp2 nameF (.eqRefl p) (family_at A B D sign x j)).eqSymm
    (.eqRefl _) (.eqRefl _) out

theorem decay_envelope (A B D sign x : PTm n) (h : Γ ⊢[PRAAx] source A D sign) :
    Γ ⊢[PRAAx] decayEnvelope nameF family (parameters A B D sign x) (two*D+num 18*B) (num 9) := by
  refine .allI (.impI (.allI ?_))
  let s (a : PTm n) := Syn.shift a
  let ss (a : PTm n) := Syn.shift (Syn.shift a)
  let Δ := Γ.map Fm.shift
  let j : PTm (n+1) := var 0
  let E := (le one j :: Δ).map Fm.shift
  have hs : Δ ⊢[PRAAx] source (s A) (s D) (s sign) :=
    by simpa [Δ,s,Fm.shift,Syn.shift,source,GaussianRightHalfPlaneArgument.source] using h.shift
  have hweak : (le one j :: Δ) ⊢[PRAAx] source (s A) (s D) (s sign) := hs.wk
  have ht : E ⊢[PRAAx] source (ss A) (ss D) (ss sign) :=
    by simpa [E,s,ss,Fm.shift,Syn.shift,source,GaussianRightHalfPlaneArgument.source,one] using hweak.shift
  have hj : E ⊢[PRAAx] le one (Syn.shift j) :=
    by simpa [E,Fm.shift,Syn.shift,one] using (Prf.hyp0 (Γ := Δ) (φ := le one j)).shift
  simpa only [decayEnvelope,decayAt,GaussianNamedFiniteEqualityChain.sample,parameters,E,Δ,s,ss,j,Syn.shift,
    GaussianCompactRiemannName.subst_sampleData,PTm.subst_add,PTm.subst_mul,PTm.subst_num,
    ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,two,one] using
      decay_observation (var 0) (ss A) (ss B) (ss D) (ss sign) (ss x) (Syn.shift j) ht hj

end LeanProofs.IPRA.Analysis.GaussianBinetFirstFormulaDecay
