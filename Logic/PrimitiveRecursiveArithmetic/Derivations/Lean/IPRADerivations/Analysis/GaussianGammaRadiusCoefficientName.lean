import IPRADerivations.Analysis.GaussianGammaHigherCoefficientName
import IPRADerivations.Analysis.GaussianNameConjugation

/-!
# Original coefficient names at an admissible common radius

Radius and coefficient degree are packed numerical data of one actual
PR2 program. Under R>=1 and e<=2R+1, its raw observations are unchanged
original cofinal polynomial coefficients at radius R. The proved modulus
retimes that original program into a genuine fast name. At R=e+1 it
has exactly the same samples as the previously constructed coefficient
name. Equality between different numerical radii remains separate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaRadiusCoefficientName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaFixedCoefficientVariation (modulus)
open GaussianGammaFiniteCoefficientStability (cofinalObservation)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalHorner (canonical)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianCoefficientNameBounds (unit)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def admissible (R e : PTm n) : Fm PTm n := le one R ⋏ le e (succ (two*R))
def rawValue (p R e : PTm n) : PTm n := cofinalObservation p R e
def rawData (R e : PTm n) : PTm n := pairT R e
def rawF : PR 2 := PTm.toPR (rawValue (var 0) (fstT (var 1)) (sndT (var 1)))
def nameF : PR 2 := GaussianFastValueCut.nameF rawF
def data (R e : PTm n) : PTm n := GaussianFastValueCut.nameData (modulus R e) (rawData R e)
def clock (p R e : PTm n) : PTm n := GaussianFastValueCut.exponent (modulus R e) p
def sample (p R e : PTm n) : PTm n := ap2 nameF p (data R e)
@[simp] theorem subst_admissible {m : ℕ} (σ : Fin n → PTm m) (R e : PTm n) :
    (admissible R e).subst σ = admissible (Syn.subst σ R) (Syn.subst σ e) := by simp [admissible]
@[simp] theorem subst_rawValue {m : ℕ} (σ : Fin n → PTm m) (p R e : PTm n) :
    Syn.subst σ (rawValue p R e) = rawValue (Syn.subst σ p) (Syn.subst σ R) (Syn.subst σ e) := by simp [rawValue]
@[simp] theorem subst_rawData {m : ℕ} (σ : Fin n → PTm m) (R e : PTm n) :
    Syn.subst σ (rawData R e) = rawData (Syn.subst σ R) (Syn.subst σ e) := by simp [rawData]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (R e : PTm n) :
    Syn.subst σ (data R e) = data (Syn.subst σ R) (Syn.subst σ e) := by simp [data]
@[simp] theorem subst_clock {m : ℕ} (σ : Fin n → PTm m) (p R e : PTm n) :
    Syn.subst σ (clock p R e) = clock (Syn.subst σ p) (Syn.subst σ R) (Syn.subst σ e) := by simp [clock]
@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (p R e : PTm n) :
    Syn.subst σ (sample p R e) = sample (Syn.subst σ p) (Syn.subst σ R) (Syn.subst σ e) := by simp [sample]

theorem raw_congr {p R e p' R' e' : PTm n} (hp : Γ ⊢[PRAAx] p ≐ p') (hR : Γ ⊢[PRAAx] R ≐ R')
    (he : Γ ⊢[PRAAx] e ≐ e') : Γ ⊢[PRAAx] rawValue p R e ≐ rawValue p' R' e' := by
  simpa only [subst_rawValue,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (rawValue (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![p,R,e]) (σ' := ![p',R',e']) (fun i => by fin_cases i; exact hp; exact hR; exact he)
theorem raw_at (p R e : PTm n) : Γ ⊢[PRAAx] ap2 rawF p (rawData R e) ≐ rawValue p R e := by
  have actual : Γ ⊢[PRAAx] ap2 rawF p (rawData R e) ≐ rawValue p (fstT (rawData R e)) (sndT (rawData R e)) := by
    simpa only [rawF,ap2,subst_rawValue,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
      toPR_eq (Γ := Γ) (rawValue (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 2) ![p,rawData R e]
  exact actual.eqTrans (raw_congr (.eqRefl _) (fst_pair _ _) (snd_pair _ _))

theorem raw_regularity (p q R e : PTm n) (h : Γ ⊢[PRAAx] admissible R e) : Γ ⊢[PRAAx]
    distanceBounded (rawValue p R e) (rawValue q R e) (modulus R e*(unit p+unit q)) (unit p*unit q) := by
  have pc := le_trans (le_add_right p e) (GaussianGammaCofinalCoefficientName.coefficient_precision_cofinal (Γ := Γ) (p+e) R)
  have qc := le_trans (le_add_right q e) (GaussianGammaCofinalCoefficientName.coefficient_precision_cofinal (Γ := Γ) (q+e) R)
  exact distance_congr (GaussianGammaFiniteCoefficientStability.cofinal_observation_fixed p R e h.andE₂).eqSymm
    (GaussianGammaFiniteCoefficientStability.cofinal_observation_fixed q R e h.andE₂).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianGammaHigherCoefficientName.later_distance p q _ _ R e pc qc h.andE₁ h.andE₂)

theorem raw_regular (R e : PTm n) (h : Γ ⊢[PRAAx] admissible R e) : Γ ⊢[PRAAx]
    GaussianFastValueCut.regular rawF (modulus R e) (rawData R e) := by
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] admissible (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift e)) := by
    simpa [Fm.shift,Syn.shift] using h.shift.shift
  refine .allI (.allI ?_)
  have actual := distance_congr (raw_at (var 1) _ _).eqSymm (raw_at (var 0) _ _).eqSymm (.eqRefl _) (.eqRefl _)
    (raw_regularity (var 1) (var 0) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift e)) hs)
  simpa only [GaussianFastValueCut.regular,Syn.shift,subst_rawData,GaussianGammaFixedCoefficientVariation.subst_modulus,unit] using actual
theorem name_regular (R e : PTm n) (h : Γ ⊢[PRAAx] admissible R e) : Γ ⊢[PRAAx] pointCN nameF (data R e) :=
  GaussianFastValueCut.name_fast rawF (modulus R e) (rawData R e) (raw_regular R e h)

theorem raw_canonical (p R e : PTm n) : Γ ⊢[PRAAx] canonical (rawValue p R e) :=
  GaussianRationalPolynomialExponentialCoefficients.exponent_canonical _ _ _
    (GaussianRationalPolynomialProduct.product_canonical _ _ _ _) (GaussianRationalPolynomialProduct.product_length _ _ _ _)
theorem sample_at (p R e : PTm n) : Γ ⊢[PRAAx] sample p R e ≐ cofinalObservation (clock p R e) R e :=
  (GaussianFastValueCut.name_at rawF (modulus R e) (rawData R e) p).eqTrans
    ((GaussianNameArithmetic.recode_congr (raw_at (clock p R e) R e)).eqTrans
      (GaussianNamedSmallPerturbationTransport.recode_fixed _ (raw_canonical _ _ _)))

theorem canonical_samples (p e : PTm n) : Γ ⊢[PRAAx] sample p (succ e) e ≐ GaussianGammaHigherCoefficientName.sample p e :=
  (sample_at p (succ e) e).eqTrans (GaussianGammaHigherCoefficientName.sample_at p e).eqSymm
theorem canonical_identity (e : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent nameF GaussianGammaHigherCoefficientName.nameF (data (succ e) e) (GaussianGammaHigherCoefficientName.data e) := by
  have admissible : Γ ⊢[PRAAx] admissible (succ e) e := .andI (zero_lt_succ e)
    (le_of_eq_add (d := e+succ two) (by ipra_ring))
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (name_regular _ _ admissible) (GaussianGammaHigherCoefficientName.name_regular e)
  refine .allI ?_
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,subst_data,PTm.subst_succ,
    GaussianGammaHigherCoefficientName.subst_data,sample,GaussianGammaHigherCoefficientName.sample] using canonical_samples (var 0) (Syn.shift e)

theorem original_common_radius_Gamma_coefficient_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (admissible (var 0) (var 1) ⟶ pointCN nameF (data (var 0) (var 1))) :=
  closeUniv 2 (.impI (name_regular _ _ Prf.hyp0))
theorem original_common_radius_Gamma_coefficient_sample_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (sample (var 0) (var 1) (var 2) ≐ cofinalObservation (clock (var 0) (var 1) (var 2)) (var 1) (var 2)) :=
  closeUniv 3 (sample_at _ _ _)
theorem original_canonical_radius_Gamma_coefficient_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (crossEquivalent nameF GaussianGammaHigherCoefficientName.nameF (data (succ (var 0)) (var 0)) (GaussianGammaHigherCoefficientName.data (var 0))) :=
  closeUniv 1 (canonical_identity _)

end LeanProofs.IPRA.Analysis.GaussianGammaRadiusCoefficientName
