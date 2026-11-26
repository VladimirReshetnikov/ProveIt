import IPRADerivations.Analysis.Euler.PositiveAxis.UnitSubstitution.Panels.GaussianEulerUnitSubstitutionPanelComparison
import IPRADerivations.Analysis.Gamma.Integrals.GaussianEulerUnitSubstitutionGamma

/-!
# Cofinal ordinary quadrature for the unit-interval Gamma integral

Each observation is an original regular compact unit-kernel quadrature
on a computed rational panel. Its physical endpoints come from finite
rounding of the original two decay observations. The comparison pays
for an independently later time cutoff and for the independently
requested original Gamma observation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionOrdinaryImproper

open_ipra
open GaussianEulerUnitSubstitutionCompactName (stage stage_budget)
open GaussianGammaCompactQuadratureBoundary (width)
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianNameEquivalence (crossEquivalent cross_at cross_trans cross_symm)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

abbrev source (z R B A : PTm n) : Fm PTm n := GaussianEulerUnitSubstitutionGamma.source z R B A
abbrev data (z R B A : PTm n) : PTm n := GaussianEulerImproperName.data z R B A
def resolution (p : PTm n) : PTm n := stage (stage p)
def laterSample (p j z R B A : PTm n) : PTm n :=
  GaussianEulerUnitSubstitutionPanelComparison.sample (resolution p) z R B one (width j A R) (etaDen j A R) (top j A R)
def sample (p z R B A : PTm n) : PTm n := laterSample p (resolution p) z R B A
def reader (p x : PTm n) : PTm n := sample p (fstT x) (fstT (sndT x)) (fstT (sndT (sndT x))) (sndT (sndT (sndT x)))
def nameF : PR 2 := PTm.toPR (reader (var 0) (var 1))

ipra_subst resolution
ipra_subst laterSample [width, etaDen, top, GaussianGammaIntegralCutoffs.height, GaussianGammaIntegralCutoffs.tailCoefficient]
ipra_subst sample
ipra_subst reader

theorem name_at (p z R B A : PTm n) : Γ ⊢[PRAAx] ap2 nameF p (data z R B A) ≐ sample p z R B A := by
  let x := data z R B A
  have program : Γ ⊢[PRAAx] ap2 nameF p x ≐ reader p x := by
    simpa [nameF,ap2] using toPR_eq (Γ := Γ) (reader (var 0) (var 1) : PTm 2) ![p,x]
  have fields := Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
    (sample (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
    (σ := ![p,fstT x,fstT (sndT x),fstT (sndT (sndT x)),sndT (sndT (sndT x))])
    (σ' := ![p,z,R,B,A]) (fun i => by
      fin_cases i
      exact .eqRefl _
      exact GaussianEulerVaryingCutoffName.data_z _ _ _ _
      exact GaussianEulerVaryingCutoffName.data_R _ _ _ _
      exact GaussianEulerVaryingCutoffName.data_B _ _ _ _
      exact GaussianEulerVaryingCutoffName.data_A _ _ _ _)
  exact program.eqTrans (by simpa only [reader,subst_sample,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons] using fields)

theorem resolution_budget (p : PTm n) : Γ ⊢[PRAAx] le (num 15*unit p) (unit (resolution p)) := by
  have inner := mul_le_mul_right (num 6) (stage_budget (Γ := Γ) p)
  have outer : Γ ⊢[PRAAx] le (num 36*unit p) (unit (resolution p)) :=
    le_trans (le_congr (by ipra_ring) (mul_comm _ _) inner) (stage_budget (stage p))
  exact le_trans (le_of_eq_add (d := num 21*unit p) (by ipra_ring)) outer

/-- The time cutoff j can be chosen independently at any later index. -/
theorem original_later_Euler_observations (p q j z R B A : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A) (hj : Γ ⊢[PRAAx] le (resolution p) j) : Γ ⊢[PRAAx]
    distanceBounded (laterSample p j z R B A) (ap2 GaussianEulerImproperName.nameF q (data z R B A))
      (unit p+unit q) (unit p*unit q) := by
  let s := resolution p
  let U := unit s
  let V := unit (stage j)
  let J := unit j
  let Q := unit q
  have hU := unit_positive (Γ := Γ) s
  have hV := unit_positive (Γ := Γ) (stage j)
  have hJ := unit_positive (Γ := Γ) j
  have hQ := unit_positive (Γ := Γ) q
  have d := positive_product _ _ hU hQ
  have original := GaussianEulerIntegralGammaIdentification.improper_source z R B A h
  have hs := GaussianEulerUnitSubstitutionImproperName.cutoff_source j z R B A original
  have adjusted := GaussianEulerUnitSubstitutionPanelComparison.original_observations s (stage j) z R B one
    (width j A R) (etaDen j A R) (top j A R) hs
  have same := (GaussianEulerImproperName.original_observation (Γ := Γ) j z R B A).eqSymm
  have before := distance_congr (.eqRefl _) same (.eqRefl _) (.eqRefl _) adjusted
  have grow : Γ ⊢[PRAAx] le U V :=
    GaussianExponentialReference.unit_monotone (le_trans hj (le_add_right j (num 4)))
  have first := distance_radius_mono _ _ _ _ (num 14*Q) (U*Q) (positive_product _ _ hU hV) d
    (by ipra_le (𝔞 U*𝔞 Q)*sl grow) before
  have growth : Γ ⊢[PRAAx] le U J := GaussianExponentialReference.unit_monotone hj
  have tail := GaussianEulerImproperName.observations j q z R B A original
  have second := distance_radius_mono _ _ _ _ (U+Q) (U*Q) (positive_product _ _ hJ hQ) d
    (by ipra_le (𝔞 Q^2)*sl growth) tail
  exact distance_radius_mono _ _ _ _ _ _ d (positive_product _ _ (unit_positive p) hQ)
    (by ipra_le (𝔞 Q^2)*sl (resolution_budget p)) (distance_triangle_same _ _ _ _ _ _ d first second)

theorem original_Euler_observations (p q z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data z R B A)) (ap2 GaussianEulerImproperName.nameF q (data z R B A))
      (unit p+unit q) (unit p*unit q) :=
  distance_congr (name_at p z R B A).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (original_later_Euler_observations p q (resolution p) z R B A h (le_refl _))

theorem original_Euler_cross (z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    crossEquivalent nameF GaussianEulerImproperName.nameF (data z R B A) (data z R B A) := by
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh A) :=
    by simpa [Fm.shift,source,GaussianEulerUnitSubstitutionGamma.source,Syn.shift,sh] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [crossEquivalent,GaussianEulerImproperName.subst_data,Syn.shift,sh] using
    original_Euler_observations (var 1) (var 0) (sh z) (sh R) (sh B) (sh A) hs

theorem name_regular (z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx] pointCN nameF (data z R B A) := by
  have near := original_Euler_cross z R B A h
  exact cross_trans _ _ _ _ _ _ near (cross_symm _ _ _ _ near)

theorem original_Gamma_cross (z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    crossEquivalent nameF gammaF (data z R B A) (gammaData z R B A) :=
  cross_trans _ _ _ _ _ _ (original_Euler_cross z R B A h)
    (GaussianEulerIntegralGammaIdentification.original_Euler_integral_is_Gamma z R B A h)

theorem actual_ordinary_cofinal_unit_quadrature_is_Gamma_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ crossEquivalent nameF gammaF
      (data (var 0) (var 1) (var 2) (var 3)) (gammaData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (original_Gamma_cross _ _ _ _ Prf.hyp0))

theorem actual_ordinary_cofinal_unit_Gamma_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 2) (var 3) (var 4) (var 5) ⟶ distanceBounded
      (ap2 nameF (var 0) (data (var 2) (var 3) (var 4) (var 5)))
      (ap2 gammaF (var 1) (gammaData (var 2) (var 3) (var 4) (var 5)))
      (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 6 (.impI (cross_at _ _ _ _ _ _ (original_Gamma_cross _ _ _ _ Prf.hyp0)))

theorem actual_ordinary_unit_quadrature_later_Euler_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((source (var 3) (var 4) (var 5) (var 6) ⋏ le (resolution (var 0)) (var 2)) ⟶
      distanceBounded (laterSample (var 0) (var 2) (var 3) (var 4) (var 5) (var 6))
        (ap2 GaussianEulerImproperName.nameF (var 1) (data (var 3) (var 4) (var 5) (var 6)))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 7 (.impI (original_later_Euler_observations _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionOrdinaryImproper
