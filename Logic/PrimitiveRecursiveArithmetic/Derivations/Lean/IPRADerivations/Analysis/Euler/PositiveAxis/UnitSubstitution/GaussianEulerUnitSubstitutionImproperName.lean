import IPRADerivations.Analysis.Euler.PositiveAxis.UnitSubstitution.GaussianEulerUnitSubstitutionCompactName
import IPRADerivations.Analysis.Euler.GaussianEulerImproperName

/-!
# The actual cofinal original unit-substitution density

The compact density program is evaluated on the unchanged original
eta/top cutoffs. Every observation remains a sum of the original power
at the exact exp(-t) chart times actual adjacent decay differences.
Original compact equivalence and the original improper name's proved
regularity yield independent observations and a regular PR2 name.
No arbitrary rational unit-grid integration identity is asserted here.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionImproperName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerUnitSubstitutionCompactName (stage)
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianGammaCompactQuadratureBoundary (width exact_right_endpoint)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianNameEquivalence (crossEquivalent)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

abbrev source (z R B A : PTm n) : Fm PTm n := GaussianEulerImproperName.source z R B A
abbrev data (z R B A : PTm n) : PTm n := GaussianEulerImproperName.data z R B A
def compactData (j z R B A : PTm n) : PTm n :=
  GaussianEulerUnitSubstitutionCompactName.data z R B one (width j A R) (etaDen j A R) (top j A R)
def sample (p z R B A : PTm n) : PTm n :=
  ap2 GaussianEulerUnitSubstitutionCompactName.nameF (stage (stage p)) (compactData (stage p) z R B A)
def reader (p d : PTm n) : PTm n := sample p (fstT d) (fstT (sndT d))
  (fstT (sndT (sndT d))) (sndT (sndT (sndT d)))
def nameF : PR 2 := PTm.toPR (reader (var 0) (var 1))

@[simp] theorem subst_compactData {m : ℕ} (σ : Fin n → PTm m) (j z R B A : PTm n) :
    Syn.subst σ (compactData j z R B A) = compactData (Syn.subst σ j) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ A) := by
  simp [compactData,etaDen,top,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient]
@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (p z R B A : PTm n) :
    Syn.subst σ (sample p z R B A) = sample (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ A) := by simp [sample]
@[simp] theorem subst_reader {m : ℕ} (σ : Fin n → PTm m) (p d : PTm n) :
    Syn.subst σ (reader p d) = reader (Syn.subst σ p) (Syn.subst σ d) := by simp [reader]

theorem name_at (p z R B A : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF p (data z R B A) ≐ sample p z R B A := by
  have program : Γ ⊢[PRAAx] ap2 nameF p (data z R B A) ≐ reader p (data z R B A) := by
    simpa [nameF,ap2] using toPR_eq (Γ := Γ) (reader (var 0) (var 1) : PTm 2) ![p,data z R B A]
  apply program.eqTrans
  simpa only [reader,subst_sample,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (sample (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
      (σ := ![p,fstT (data z R B A),fstT (sndT (data z R B A)),fstT (sndT (sndT (data z R B A))),sndT (sndT (sndT (data z R B A)))])
      (σ' := ![p,z,R,B,A]) (fun i : Fin 5 => by
        fin_cases i
        · exact .eqRefl _
        · exact GaussianEulerVaryingCutoffName.data_z _ _ _ _
        · exact GaussianEulerVaryingCutoffName.data_R _ _ _ _
        · exact GaussianEulerVaryingCutoffName.data_B _ _ _ _
        · exact GaussianEulerVaryingCutoffName.data_A _ _ _ _)

theorem cutoff_source (j z R B A : PTm n) (hs : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    GaussianEulerUnitSubstitutionCompactName.source z R B one (width j A R) (etaDen j A R) (top j A R) := by
  have hE := GaussianGammaIntegralCutoffs.eta_den_positive (Γ := Γ) j A R
  have oldInput := GaussianGammaEulerCompactQuadrature.original_input z R B j A hs.andE₁
  have full : Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.intervalSource z R B one (width j A R) (etaDen j A R) (top j A R) :=
    .andI oldInput.andE₁ (.andI (le_refl one)
      (le_congr (.eqRefl _) (exact_right_endpoint j A R) (le_refl _)))
  have t2 : Γ ⊢[PRAAx] le two (top j A R) :=
    le_congr (one_mul two) (mul_comm _ _) (mul_le_mul_right two (GaussianGammaIntegralCutoffs.height_positive j A R))
  have product : Γ ⊢[PRAAx] le two (etaDen j A R*top j A R) := le_trans t2
    (le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (top j A R) hE))
  have endpoint := natEq (exact_right_endpoint (Γ := Γ) j A R)
  have positiveWidth : Γ ⊢[PRAAx] le one (width j A R) := by
    ipra_le sl product with endpoint
  exact .andI full positiveWidth

theorem actual_sampler (p z R B A : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF p (data z R B A) ≐ GaussianEulerUnitSubstitutionDensity.density
      (GaussianEulerUnitSubstitutionCompactName.rowQuery (stage (stage p)) R (width (stage p) A R) (etaDen (stage p) A R) (top (stage p) A R))
      (GaussianEulerUnitSubstitutionCompactName.count (stage (stage p)) R (width (stage p) A R) (etaDen (stage p) A R) (top (stage p) A R))
      z B one (width (stage p) A R) (etaDen (stage p) A R) :=
  (name_at p z R B A).eqTrans (GaussianEulerUnitSubstitutionCompactName.name_at (stage (stage p)) z R B one
    (width (stage p) A R) (etaDen (stage p) A R) (top (stage p) A R))

theorem original_observations (p q z R B A : PTm n) (hs : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data z R B A)) (ap2 GaussianEulerImproperName.nameF q (data z R B A))
      (unit p+unit q) (unit p*unit q) := by
  let j := stage p
  let r := stage j
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have hj := unit_positive (Γ := Γ) j
  have hr := unit_positive (Γ := Γ) r
  have densityNear := GaussianEulerUnitSubstitutionCompactName.original_observations r r z R B one
    (width j A R) (etaDen j A R) (top j A R) (cutoff_source j z R B A hs)
  have old : Γ ⊢[PRAAx] ap2 GaussianEulerCompactAdditivity.nameF r
      (GaussianEulerCompactAdditivity.data z R B one (width j A R) (etaDen j A R) (top j A R)) ≐
        ap2 GaussianEulerImproperName.nameF j (data z R B A) :=
    (GaussianEulerImproperName.original_observation j z R B A).eqSymm
  have first := distance_congr (.eqRefl _) old (.eqRefl _) (.eqRefl _) densityNear
  have grow : Γ ⊢[PRAAx] le (unit j) (unit r) :=
    GaussianExponentialReference.unit_monotone (le_add_right j (LeanProofs.IPRA.PTm.num 4))
  have coarse := distance_radius_mono _ _ _ _ (two*unit q) (unit j*unit q)
    (positive_product _ _ hr hr) (positive_product _ _ hj hq)
    (by ipra_le (2*𝔞(unit q)*𝔞(unit r))*sl grow) first
  have tail := GaussianEulerImproperName.observations j q z R B A hs
  have joined := distance_triangle_same _ _ _ _ _ _ (positive_product _ _ hj hq) coarse tail
  have budget : Γ ⊢[PRAAx] le (LeanProofs.IPRA.PTm.num 3*unit p) (unit j) :=
    le_trans (le_of_eq_add (d := LeanProofs.IPRA.PTm.num 3*unit p) (by ipra_ring))
      (GaussianEulerUnitSubstitutionCompactName.stage_budget p)
  apply distance_congr (name_at p z R B A).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hj hq) (positive_product _ _ hp hq)
    (by ipra_le (𝔞(unit q)*𝔞(unit q))*sl budget) joined

theorem original_improper_cross (z R B A : PTm n) (hs : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    crossEquivalent nameF GaussianEulerImproperName.nameF (data z R B A) (data z R B A) := by
  have ss : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R))
      (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift A)) := by simpa [Fm.shift,Syn.shift] using hs.shift.shift
  refine .allI (.allI ?_)
  simpa only [crossEquivalent,GaussianEulerImproperName.subst_data,GaussianEuclideanPointDistance.unit,
    GaussianCoefficientNameBounds.unit,Syn.shift] using original_observations (var 1) (var 0) (Syn.shift (Syn.shift z))
      (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift A)) ss

theorem name_regular (z R B A : PTm n) (hs : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    pointCN nameF (data z R B A) := by
  have e := original_improper_cross z R B A hs
  exact GaussianNameEquivalence.cross_trans _ _ _ _ _ _ e (GaussianNameEquivalence.cross_symm _ _ _ _ e)

theorem actual_original_cofinal_unit_density_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ crossEquivalent nameF GaussianEulerImproperName.nameF
      (data (var 0) (var 1) (var 2) (var 3)) (data (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (original_improper_cross _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionImproperName
