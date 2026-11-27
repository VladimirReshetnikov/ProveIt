import IPRADerivations.Analysis.Integration.Moments.Even.GaussianEvenMomentSymmetricGrid
import IPRADerivations.Analysis.Gamma.HalfInteger.GaussianGammaHalfSqrtValues

/-!
# Literal whole-line even Gaussian moments on cofinal reflected panels

The program returns the sum of the actual positive and reflected
quadratures, on the original quadratic improper panels and mesh. The
same physical endpoints tend to zero and infinity. The compact
width-scaled comparison with the original half-line evaluator and its
omitted-tail bound identify this literal whole-line observation with
twice the checked factorial and square-root value.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEvenMomentWholeLine

open_ipra
open GaussianGammaHalfIntegerDomain (argument radius)
open GaussianEvenMomentSymmetricGrid (symmetricGrid)
open GaussianGammaIntegralCutoffs (etaDen height top)
open GaussianEulerQuadraticUpperEndpoint (preimage)
open GaussianEulerQuadraticCutoffGeometry (width)
open GaussianCompactRiemannName (precision mesh dyadic_monotone)
open GaussianNameArithmetic (addF addData add_fast sum_distance)
open GaussianRationalHorner (qadd positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans cross_to_diagonal point_at)
open GaussianEuclideanDistanceName (pointCN)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def clock (p : PTm n) : PTm n := succ (succ (succ p))
def lowerDenominator (p N c d : PTm n) : PTm n := etaDen (GaussianEvenMomentIntegral.cutoff p N c d) two (radius N)
def upperEndpoint (p N c d : PTm n) : PTm n := preimage (GaussianEvenMomentIntegral.cutoff p N c d) two (radius N) d
def span (p N c d : PTm n) : PTm n := width (GaussianEvenMomentIntegral.cutoff p N c d) two (radius N) d
def count (p N c d : PTm n) : PTm n := mesh (succ p)
  (GaussianEulerQuadraticKernelCompactName.lipschitz (radius N) (lowerDenominator p N c d) (upperEndpoint p N c d) c d)
  (upperEndpoint p N c d)
def query (p N c d : PTm n) : PTm n := precision (succ p) (upperEndpoint p N c d)
def finiteSample (p N c d : PTm n) : PTm n := symmetricGrid (query p N c d) (count p N c d)
  one (span p N c d) (lowerDenominator p N c d) N c d
def sample (p N c d : PTm n) : PTm n := finiteSample (clock p) N c d
def data (N c d : PTm n) : PTm n := GaussianEvenMomentSymmetricGrid.momentData N c d
private def body : PTm 2 := sample (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1)))
def nameF : PR 2 := PTm.toPR body

abbrev halfF : PR 2 := GaussianEvenMomentIntegral.nameF
abbrev doubledF : PR 2 := addF halfF halfF
def doubledData (N c d : PTm n) : PTm n := addData (GaussianEvenMomentIntegral.data N c d) (GaussianEvenMomentIntegral.data N c d)
abbrev valueF : PR 2 := addF GaussianGammaHalfSqrtValues.momentF GaussianGammaHalfSqrtValues.momentF
def valueData (N c d x : PTm n) : PTm n :=
  addData (GaussianGammaHalfSqrtValues.momentData N c d x) (GaussianGammaHalfSqrtValues.momentData N c d x)

ipra_subst data
ipra_subst doubledData
ipra_subst sample [finiteSample, clock, query, count, span, lowerDenominator, upperEndpoint, GaussianEulerQuadraticCutoffGeometry.width, GaussianEulerQuadraticUpperEndpoint.preimage, etaDen, height, top, GaussianGammaIntegralCutoffs.tailCoefficient]

theorem sample_at (p N c d : PTm n) : Γ ⊢[PRAAx] ap2 nameF p (data N c d) ≐ sample p N c d := by
  let x := data N c d
  have e : Γ ⊢[PRAAx] ap2 nameF p x ≐ sample p (fstT x) (fstT (sndT x)) (sndT (sndT x)) := by
    simpa only [nameF,body,ap2,subst_sample,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
      using toPR_eq (Γ := Γ) body ![p,x]
  have r : Γ ⊢[PRAAx] sndT x ≐ pairT c d := snd_pair N (pairT c d)
  let K : PTm 4 := sample (var 0) (var 1) (var 2) (var 3)
  let left : Fin 4 → PTm n := ![p,fstT x,fstT (sndT x),sndT (sndT x)]
  let right : Fin 4 → PTm n := ![p,N,c,d]
  have bodyAt (σ : Fin 4 → PTm n) : Syn.subst σ K = sample (σ 0) (σ 1) (σ 2) (σ 3) := by
    simp only [K,subst_sample,Syn.subst_var]
  have h : Γ ⊢[PRAAx] Syn.subst left K ≐ Syn.subst right K :=
    Prf.eqCongr K (σ := left) (σ' := right) (fun i => by
      fin_cases i
      · exact .eqRefl p
      · exact fst_pair N (pairT c d)
      · exact (congrFst r).eqTrans (fst_pair c d)
      · exact (congrSnd r).eqTrans (snd_pair c d))
  rw [bodyAt left,bodyAt right] at h
  exact e.eqTrans h

theorem endpoints_cofinal (p N c d : PTm n) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    le (unit p) (lowerDenominator p N c d) ⋏ le p (upperEndpoint p N c d) :=
  GaussianEulerQuadraticImproperSchedule.endpoints_cofinal p (GaussianEvenMomentIntegral.cutoff p N c d) two (radius N) d
    (GaussianEulerQuadraticImproperSchedule.index_later p two _ c d) (zero_lt_succ one) hd

theorem finite_sample_error (p N c d : PTm n) (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    distanceBounded (finiteSample p N c d)
      (qadd (ap2 halfF p (GaussianEvenMomentIntegral.data N c d)) (ap2 halfF p (GaussianEvenMomentIntegral.data N c d)))
      two (unit p) := by
  let j := GaussianEvenMomentIntegral.cutoff p N c d
  let E := lowerDenominator p N c d
  let T := upperEndpoint p N c d
  let W := span p N c d
  let M := count p N c d
  let q := query p N c d
  let U := unit q
  let V := unit p
  let A := ap2 halfF p (GaussianEvenMomentIntegral.data N c d)
  let B := GaussianCompactRiemannName.quadrature (GaussianEvenMomentSymmetricGrid.evaluatorF false) q M one W E
    (GaussianEvenMomentSymmetricGrid.momentData N c d)
  have eq : Γ ⊢[PRAAx] one+W ≐ E*T := GaussianEulerQuadraticCutoffGeometry.exact_right_endpoint j two (radius N) d hd
  have hE : Γ ⊢[PRAAx] le one E := GaussianGammaIntegralCutoffs.eta_den_positive j two (radius N)
  have hM : Γ ⊢[PRAAx] le one M := GaussianCompactRiemannName.mesh_positive _ _ _
  have source : Γ ⊢[PRAAx] GaussianEvenMomentSymmetricGrid.source one W E T c d :=
    .andI (.andI hE (.andI (le_refl _) (le_congr eq.eqSymm (.eqRefl _) (le_refl _)))) (.andI hc hd)
  have comparison := GaussianEvenMomentSymmetricGrid.original_grid_distance q q M one W E T N c d source hM
  have hU : Γ ⊢[PRAAx] le one U := unit_positive q
  have hV : Γ ⊢[PRAAx] le one V := unit_positive p
  have scale : Γ ⊢[PRAAx] le (unit (succ p+num 6)*T) U :=
    GaussianCompactRiemannName.precision_lower (succ p) T
  have wider : Γ ⊢[PRAAx] le (unit (succ p)) (unit (succ p+num 6)) :=
    dyadic_monotone (succ p) (succ p+num 6) (le_add_right _ _)
  have succUnit : Γ ⊢[PRAAx] unit (succ p) ≐ two*V :=
    (pw_succ two p).eqTrans (mul_comm V two)
  have queryRate : Γ ⊢[PRAAx] le (two*V*T) U :=
    le_trans (mul_le_mul_right T (le_congr succUnit (.eqRefl _) wider)) scale
  have hW : Γ ⊢[PRAAx] le W (E*T) :=
    le_trans (le_add_left W one) (le_congr eq.eqSymm (.eqRefl _) (le_refl _))
  have budget : Γ ⊢[PRAAx] le ((W*(U+U))*V) (one*(E*(U*U))) := by
    ipra_le 2*𝔞 V*𝔞 U*sl hW+𝔞 E*𝔞 U*sl queryRate
  have single : Γ ⊢[PRAAx] distanceBounded A B one V :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hE (positive_product _ _ hU hU)) hV budget
      (distance_congr (GaussianEvenMomentIntegral.actual_quadrature p N c d).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) comparison)
  have doubled := sum_distance A B A B one one V hV single single
  exact distance_congr (GaussianEvenMomentSymmetricGrid.symmetric_grid_at q M one W E N c d).eqSymm (.eqRefl _)
    (by ipra_ring) (.eqRefl _) (distance_symmetric _ _ _ _ hV doubled)

private theorem unit_clock (p : PTm n) : Γ ⊢[PRAAx] unit (clock p) ≐ num 8*unit p := by
  unfold clock unit
  exact (pw_succ two (succ (succ p))).eqTrans
    ((congrMul (pw_succ two (succ p)) (.eqRefl _)).eqTrans
      ((congrMul (congrMul (pw_succ two p) (.eqRefl _)) (.eqRefl _)).eqTrans (by ipra_ring)))

theorem whole_at (p q N c d : PTm n) (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data N c d)) (ap2 doubledF q (doubledData N c d))
      (unit p+unit q) (unit p*unit q) := by
  let s := clock p
  let U := unit s
  let P := unit p
  let Q := unit q
  let H := GaussianEvenMomentIntegral.data N c d
  let A := sample p N c d
  let B := qadd (ap2 halfF s H) (ap2 halfF s H)
  let C := ap2 doubledF s (doubledData N c d)
  let D := ap2 doubledF q (doubledData N c d)
  have hU : Γ ⊢[PRAAx] le one U := unit_positive s
  have hP : Γ ⊢[PRAAx] le one P := unit_positive p
  have hQ : Γ ⊢[PRAAx] le one Q := unit_positive q
  have hUQ := positive_product (Γ := Γ) _ _ hU hQ
  have reg : Γ ⊢[PRAAx] pointCN halfF H := GaussianEvenMomentIntegral.name_regular N c d hc hd
  have full : Γ ⊢[PRAAx] pointCN doubledF (doubledData N c d) := add_fast _ _ _ _ reg reg
  have first : Γ ⊢[PRAAx] distanceBounded A B two U := finite_sample_error s N c d hc hd
  have middle : Γ ⊢[PRAAx] distanceBounded B C (num 3) U :=
    distance_congr (.eqRefl _) (.eqRefl _) (by unfold GaussianNameRingLaws.three; ipra_ring) (.eqRefl _)
      (distance_symmetric _ _ _ _ hU (GaussianNameRingLaws.add_sample_error halfF halfF H H s reg reg))
  have initial : Γ ⊢[PRAAx] distanceBounded A C (num 5) U :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (distance_triangle_same A B C two (num 3) U hU first middle)
  have corrected : Γ ⊢[PRAAx] distanceBounded A C (num 5*Q) (U*Q) :=
    distance_radius_mono _ _ _ _ _ _ hU hUQ (by ipra_le 0) initial
  have distance : Γ ⊢[PRAAx] distanceBounded C D (U+Q) (U*Q) :=
    point_at doubledF (doubledData N c d) s q full
  have total := distance_triangle_same A C D (num 5*Q) (U+Q) (U*Q) hUQ corrected distance
  have final : Γ ⊢[PRAAx] distanceBounded A D (P+Q) (P*Q) :=
    distance_radius_mono _ _ _ _ _ _ hUQ (positive_product _ _ hP hQ)
      (by ipra_le 2*(𝔞 P)*(𝔞 Q)^2 with (𝔞 Q)^2*natEq (unit_clock (Γ := Γ) p)) total
  exact distance_congr (sample_at p N c d).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) final

theorem original_literal_whole (N c d : PTm n) (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    crossEquivalent nameF doubledF (data N c d) (doubledData N c d) := by
  refine .allI (.allI ?_)
  have hc' : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift c)) := by
    simpa [Fm.shift,Syn.shift,one] using hc.shift.shift
  have hd' : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift d)) := by
    simpa [Fm.shift,Syn.shift,one] using hd.shift.shift
  simpa only [crossEquivalent,Syn.shift,subst_data,subst_doubledData] using
    whole_at (var 1) (var 0) (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift c)) (Syn.shift (Syn.shift d)) hc' hd'

theorem original_even_whole_value (N c d x : PTm n) (hc : Γ ⊢[PRAAx] le one c)
    (hd : Γ ⊢[PRAAx] le one d) : Γ ⊢[PRAAx]
    crossEquivalent nameF valueF (data N c d) (valueData N c d x) := by
  let H := GaussianEvenMomentIntegral.data N c d
  let F := GaussianGammaHalfSqrtValues.momentF
  let Y := GaussianGammaHalfSqrtValues.momentData N c d x
  have hH := GaussianEvenMomentIntegral.name_regular N c d hc hd
  have h := GaussianGammaHalfSqrtValues.original_even_moment N c d x hc hd
  have yy : Γ ⊢[PRAAx] pointCN F Y :=
    cross_trans F halfF F Y H Y (cross_symm _ _ _ _ h) h
  have replacement := GaussianNameArithmetic.add_equivalent halfF F halfF F H Y H Y
    hH yy hH yy (cross_to_diagonal _ _ _ _ h) (cross_to_diagonal _ _ _ _ h)
  exact cross_trans _ _ _ _ _ _ (original_literal_whole N c d hc hd) replacement

theorem actual_even_Gaussian_whole_endpoints_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (le one (var 3) ⟶ le (unit (var 0)) (lowerDenominator (var 0) (var 1) (var 2) (var 3)) ⋏
        le (var 0) (upperEndpoint (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (endpoints_cofinal _ _ _ _ Prf.hyp0))

theorem actual_original_whole_line_Gaussian_even_sqrt_Pi_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (le one (var 1) ⟶ le one (var 2) ⟶ crossEquivalent nameF valueF
        (data (var 0) (var 1) (var 2)) (valueData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (original_even_whole_value _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEvenMomentWholeLine
