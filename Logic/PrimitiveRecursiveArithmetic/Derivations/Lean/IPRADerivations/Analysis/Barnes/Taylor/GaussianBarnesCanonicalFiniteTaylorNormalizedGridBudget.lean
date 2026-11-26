import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalFiniteTaylorGridBudget
import IPRADerivations.Analysis.Polynomials.GaussianPolynomialForwardDifferenceNormalization

/-!
# Normalize the finite Barnes Taylor grid error

A fractional lower margin H/(2B) for the Gaussian step permits
normalization without losing a power of the displacement. The full
degree-(e+1) remainder becomes a first-order term in H/B.
The original Taylor clock and the additional readback clock stay distinct.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorNormalizedGridBudget

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.Analysis.Products (fact)
open GaussianBarnesCanonicalFiniteTaylorGridBudget (analyticGain clockGain)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianPolynomialForwardDifferenceGrid (samples)
open GaussianPolynomialForwardDifferenceGridError (rowBound)
open GaussianPolynomialForwardDifferenceNormalization (normalized)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalNaturalScale (natScale)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rowNumerator (q s z R B H M K : PTm n) : PTm n :=
  GaussianBarnesCanonicalFiniteTaylorGridBudget.numerator q z R B H M*unit s+
  GaussianBarnesCanonicalFiniteTaylorGridBudget.denominator q B M*K

def rowDenominator (q s B M : PTm n) : PTm n :=
  GaussianBarnesCanonicalFiniteTaylorGridBudget.denominator q B M*unit s

def amplification (B M : PTm n) : PTm n := pw (num 4*B) (previous M)

def analyticCoefficient (z R B M : PTm n) : PTm n :=
  pw (num 4) (previous M)*analyticGain z R B M

def numerator (q s z R B H M K : PTm n) : PTm n :=
  analyticCoefficient z R B M*H*unit q*unit s+
    amplification B M*clockGain z R B*B*unit s+
    amplification B M*K*B*unit q

def denominator (q s B : PTm n) : PTm n := B*unit q*unit s

def rowNumeratorWithGains (q s B H M K A C : PTm n) : PTm n :=
  (A*pw H (succ (previous M))*unit q+C*pw B (succ (previous M)))*unit s+GaussianBarnesCanonicalFiniteTaylorGridBudget.denominator q B M*K

def normalizedNumeratorWithGains (q s B H M K A C : PTm n) : PTm n :=
  (pw (num 4) (previous M)*A)*H*unit q*unit s+
    amplification B M*C*B*unit s+amplification B M*K*B*unit q

@[simp] theorem subst_rowNumeratorWithGains {l : ℕ} (σ : Fin n → PTm l) (q s B H M K A C : PTm n) :
    Syn.subst σ (rowNumeratorWithGains q s B H M K A C) =
      rowNumeratorWithGains (Syn.subst σ q) (Syn.subst σ s) (Syn.subst σ B) (Syn.subst σ H)
        (Syn.subst σ M) (Syn.subst σ K) (Syn.subst σ A) (Syn.subst σ C) := by
  simp [rowNumeratorWithGains,rowDenominator,zero]

@[simp] theorem subst_normalizedNumeratorWithGains {l : ℕ} (σ : Fin n → PTm l) (q s B H M K A C : PTm n) :
    Syn.subst σ (normalizedNumeratorWithGains q s B H M K A C) =
      normalizedNumeratorWithGains (Syn.subst σ q) (Syn.subst σ s) (Syn.subst σ B) (Syn.subst σ H)
        (Syn.subst σ M) (Syn.subst σ K) (Syn.subst σ A) (Syn.subst σ C) := by
  simp [normalizedNumeratorWithGains,amplification]

@[simp] theorem subst_rowNumerator {l : ℕ} (σ : Fin n → PTm l) (q s z R B H M K : PTm n) :
    Syn.subst σ (rowNumerator q s z R B H M K) = rowNumerator (Syn.subst σ q) (Syn.subst σ s)
      (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ H) (Syn.subst σ M) (Syn.subst σ K) := by
  simp [rowNumerator]

@[simp] theorem subst_rowDenominator {l : ℕ} (σ : Fin n → PTm l) (q s B M : PTm n) :
    Syn.subst σ (rowDenominator q s B M) = rowDenominator (Syn.subst σ q) (Syn.subst σ s) (Syn.subst σ B) (Syn.subst σ M) := by
  simp [rowDenominator]

@[simp] theorem subst_amplification {l : ℕ} (σ : Fin n → PTm l) (B M : PTm n) :
    Syn.subst σ (amplification B M) = amplification (Syn.subst σ B) (Syn.subst σ M) := by simp [amplification]

@[simp] theorem subst_analyticCoefficient {l : ℕ} (σ : Fin n → PTm l) (z R B M : PTm n) :
    Syn.subst σ (analyticCoefficient z R B M) = analyticCoefficient (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ M) := by simp [analyticCoefficient]

@[simp] theorem subst_numerator {l : ℕ} (σ : Fin n → PTm l) (q s z R B H M K : PTm n) :
    Syn.subst σ (numerator q s z R B H M K) = numerator (Syn.subst σ q) (Syn.subst σ s)
      (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ H) (Syn.subst σ M) (Syn.subst σ K) := by simp [numerator]

@[simp] theorem subst_denominator {l : ℕ} (σ : Fin n → PTm l) (q s B : PTm n) :
    Syn.subst σ (denominator q s B) = denominator (Syn.subst σ q) (Syn.subst σ s) (Syn.subst σ B) := by simp [denominator]

theorem row_denominator_positive (q s B M : PTm n) (hb : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] le one (rowDenominator q s B M) :=
  positive_product _ _ (GaussianBarnesCanonicalFiniteTaylorGridBudget.denominator_positive q B M hb) (unit_positive s)

theorem denominator_positive (q s B : PTm n) (hb : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] le one (denominator q s B) :=
  positive_product _ _ (positive_product _ _ hb (unit_positive q)) (unit_positive s)

private theorem amplification_eq (B M : PTm n) : Γ ⊢[PRAAx]
    pw (two*B) (previous M)*pw two (previous M) ≐ amplification B M :=
  (AnalyticNumberTheory.LocalFactor.pw_mul_base (two*B) two (previous M)).eqSymm.eqTrans
    (congrAp2 powF (.eqRefl _) (by ipra_ring))

theorem radius_comparison_with_gains (q s B H M K A C : PTm n) (hH : Γ ⊢[PRAAx] le one H) :
    Γ ⊢[PRAAx] le
      ((pw (two*B) (previous M)*(pw two (previous M)*rowNumeratorWithGains q s B H M K A C))*denominator q s B)
      (normalizedNumeratorWithGains q s B H M K A C*(pw H (previous M)*rowDenominator q s B M)) := by
  let e := previous M
  let u := unit q
  let v := unit s
  let bh := pw H e
  let bb := pw B e
  let g := pw (num 4 : PTm n) e
  let T := amplification B M
  have hh : Γ ⊢[PRAAx] le one bh := GaussianFactorBudget.power_positive H e hH
  have hhpow := natEq (pw_succ (Γ := Γ) H e)
  have hbpow := natEq (pw_succ (Γ := Γ) B e)
  have hsplit : Γ ⊢[PRAAx] T ≐ g*bb := AnalyticNumberTheory.LocalFactor.pw_mul_base (num 4) B e
  have hs := natEq hsplit
  let W := rowNumeratorWithGains q s B H M K A C
  let D := denominator q s B
  have rearrange : Γ ⊢[PRAAx] (pw (two*B) e*(pw two e*W))*D ≐ T*W*D :=
    (show Γ ⊢[PRAAx] (pw (two*B) e*(pw two e*W))*D ≐ (pw (two*B) e*pw two e)*W*D by ipra_ring).eqTrans
      (congrMul (congrMul (amplification_eq B M) (.eqRefl W)) (.eqRefl D))
  refine le_congr rearrange.eqSymm (.eqRefl _) ?_
  change Γ ⊢[PRAAx] le
    (T*((A*pw H (succ e)*u+C*pw B (succ e))*v+(pw B (succ e)*u)*K)*(B*u*v))
    ((g*A*H*u*v+T*C*B*v+T*K*B*u)*(bh*((pw B (succ e)*u)*v)))
  let 𝔞 := fun x : PTm n => Groth.ι (IPRA.Q.mk Γ x)
  ipra_le (𝔞 T*𝔞 bb*𝔞 B*𝔞 B*𝔞 u*𝔞 v*(𝔞 C*𝔞 v+𝔞 K*𝔞 u))*sl hh using
    dsimp only [𝔞]
    rw [hhpow,hbpow,hs]
    dsimp only [bh,bb]
    ring

theorem radius_comparison (q s z R B H M K : PTm n) (hH : Γ ⊢[PRAAx] le one H) :
    Γ ⊢[PRAAx] le
      ((pw (two*B) (previous M)*(pw two (previous M)*rowNumerator q s z R B H M K))*denominator q s B)
      (numerator q s z R B H M K*(pw H (previous M)*rowDenominator q s B M)) :=
  radius_comparison_with_gains q s B H M K (analyticGain z R B M) (clockGain z R B) hH

theorem coefficient_error_with_gains (q s B H M K A G V C x h : PTm n)
    (hb : Γ ⊢[PRAAx] le one B) (hH : Γ ⊢[PRAAx] le one H)
    (hC : Γ ⊢[PRAAx] length C ≐ succ (previous M))
    (hh : Γ ⊢[PRAAx] GaussianRationalLowerBounds.lower h H (two*B))
    (hr : Γ ⊢[PRAAx] rowBound V (samples C (succ (previous M)) x h) (succ (previous M))
      (rowNumeratorWithGains q s B H M K A G) (rowDenominator q s B M)) :
    Γ ⊢[PRAAx] distanceBounded (normalized V (previous M) h) (natScale (fact (previous M)) (entry C zero))
      (normalizedNumeratorWithGains q s B H M K A G) (denominator q s B) := by
  have hd : Γ ⊢[PRAAx] le one (two*B) := positive_product _ _ (le_succ_self one) hb
  have hrden := row_denominator_positive q s B M hb
  have hnorm := GaussianPolynomialForwardDifferenceNormalization.fractional_coefficient_error V C (previous M) x h H (two*B)
    (rowNumeratorWithGains q s B H M K A G) (rowDenominator q s B M) hC hH hd hh hrden hr
  have old := positive_product _ _ (GaussianFactorBudget.power_positive H (previous M) hH) hrden
  exact distance_radius_mono _ _ _ _ _ _ old (denominator_positive q s B hb) (radius_comparison_with_gains q s B H M K A G hH) hnorm

theorem coefficient_error (q s z R B H M K V C x h : PTm n)
    (hb : Γ ⊢[PRAAx] le one B) (hH : Γ ⊢[PRAAx] le one H)
    (hC : Γ ⊢[PRAAx] length C ≐ succ (previous M))
    (hh : Γ ⊢[PRAAx] GaussianRationalLowerBounds.lower h H (two*B))
    (hr : Γ ⊢[PRAAx] rowBound V (samples C (succ (previous M)) x h) (succ (previous M))
      (rowNumerator q s z R B H M K) (rowDenominator q s B M)) :
    Γ ⊢[PRAAx] distanceBounded (normalized V (previous M) h) (natScale (fact (previous M)) (entry C zero))
      (numerator q s z R B H M K) (denominator q s B) :=
  coefficient_error_with_gains q s B H M K (analyticGain z R B M) (clockGain z R B) V C x h hb hH hC hh hr

theorem actual_Barnes_finite_normalized_Taylor_grid_radius_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (let q := var 0
     let s := var 1
     let z := var 2
     let R := var 3
     let B := var 4
     let H := var 5
     let M := var 6
     let K := var 7
     le one H ⟶ le
       ((pw (two*B) (previous M)*(pw two (previous M)*rowNumerator q s z R B H M K))*denominator q s B)
       (numerator q s z R B H M K*(pw H (previous M)*rowDenominator q s B M))) :=
  closeUniv 8 (.impI (radius_comparison _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorNormalizedGridBudget
