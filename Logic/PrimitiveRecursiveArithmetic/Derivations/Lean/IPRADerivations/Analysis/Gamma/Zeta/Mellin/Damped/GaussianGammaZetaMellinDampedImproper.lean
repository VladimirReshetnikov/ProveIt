import IPRADerivations.Analysis.Gamma.Integrals.GaussianEulerPositiveScalingGamma
import IPRADerivations.Analysis.Names.FiniteOperations.Sums.GaussianNamedFiniteSumFamilyCongruence
import IPRADerivations.Analysis.Names.FiniteOperations.Sums.GaussianNamedFiniteSumFamilyMultiply

/-!
# Finite sums of the original damped Euler improper integrals

Apply positive scaling to each of the internally many rows at scale `j+1`.
The finite named sum keeps the original improper row samplers and identifies
their sum with the corresponding finite sum of Dirichlet factors times Gamma.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinDampedImproper

open_ipra
open GaussianEulerPositiveScalingConstant (inverseF inverseData)
open GaussianEulerPositiveScalingGamma (productData)
open GaussianEulerIntegralGammaIdentification (source)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)
open GaussianGammaCompactCutoffSplit (point_data_congr)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNamedFiniteProductFamily (regularRows)
open GaussianNamedFiniteProductFamilyCongruence (equalRows)
open GaussianNamedFiniteSumFamilyCongruence (family_sum_cross)
open GaussianNameEquivalence (crossEquivalent cross_trans)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "Damped" => GaussianEulerPositiveScalingImproper.nameF
local notation "Product" => GaussianEulerPositiveScalingGamma.productF

def parameters (z R B A : PTm n) : PTm n := pairT (pairT z R) (pairT B A)

def dampedBody : PTm 2 :=
  let x := var 1
  GaussianEulerPositiveScalingImproper.data (fstT (fstT x)) (sndT (fstT x))
    (fstT (sndT x)) (sndT (sndT x)) (succ (var 0)) one

def productBody : PTm 2 :=
  let x := var 1
  productData (fstT (fstT x)) (sndT (fstT x))
    (fstT (sndT x)) (sndT (sndT x)) (succ (var 0)) one

def dirichletBody : PTm 2 :=
  let x := var 1
  inverseData (fstT (fstT x)) (fstT (sndT x)) (succ (var 0)) one

def data (N z R B A : PTm n) : PTm n := GaussianNamedFiniteSumFamily.data N (parameters z R B A)
def nameF : PR 2 := GaussianNamedFiniteSumFamily.nameF Damped dampedBody
def productSumF : PR 2 := GaussianNamedFiniteSumFamily.nameF Product productBody
def dirichletF : PR 2 := GaussianNamedFiniteSumFamily.nameF inverseF dirichletBody

ipra_subst parameters

ipra_subst data

private theorem five_at (t : PTm 5) (i z R B A : PTm n) :
    Γ ⊢[PRAAx] Syn.subst ![i, fstT (fstT (parameters z R B A)), sndT (fstT (parameters z R B A)),
      fstT (sndT (parameters z R B A)), sndT (sndT (parameters z R B A))] t ≐
      Syn.subst ![i,z,R,B,A] t := by
  -- Apply the projection identities directly to the data code.
  have left := fst_pair (Γ := Γ) (pairT z R) (pairT B A)
  have right := snd_pair (Γ := Γ) (pairT z R) (pairT B A)
  refine Prf.eqCongr t (fun j => ?_)
  fin_cases j
  · exact .eqRefl i
  · exact (congrFst left).eqTrans (fst_pair z R)
  · exact (congrSnd left).eqTrans (snd_pair z R)
  · exact (congrFst right).eqTrans (fst_pair B A)
  · exact (congrSnd right).eqTrans (snd_pair B A)

theorem damped_at (i z R B A : PTm n) :
    Γ ⊢[PRAAx] inst2 dampedBody i (parameters z R B A) ≐
      GaussianEulerPositiveScalingImproper.data z R B A (succ i) one := by
  simpa only [dampedBody,inst2,GaussianEulerPositiveScalingImproper.subst_data,
    subst_fstT,subst_sndT,PTm.subst_succ,ConciseIPRA.PTm.subst_zero,one,Syn.subst_var,Matrix.cons_val] using
    five_at (GaussianEulerPositiveScalingImproper.data (var 1) (var 2) (var 3) (var 4) (succ (var 0)) one)
      i z R B A

theorem product_at (i z R B A : PTm n) :
    Γ ⊢[PRAAx] inst2 productBody i (parameters z R B A) ≐ productData z R B A (succ i) one := by
  simpa only [productBody,inst2,GaussianEulerPositiveScalingGamma.subst_productData,
    subst_fstT,subst_sndT,PTm.subst_succ,ConciseIPRA.PTm.subst_zero,one,Syn.subst_var,Matrix.cons_val] using
    five_at (productData (var 1) (var 2) (var 3) (var 4) (succ (var 0)) one) i z R B A

theorem dirichlet_at (i z R B A : PTm n) :
    Γ ⊢[PRAAx] inst2 dirichletBody i (parameters z R B A) ≐ inverseData z B (succ i) one := by
  simpa only [dirichletBody,inst2,GaussianEulerPositiveScalingConstant.subst_inverseData,
    subst_fstT,subst_sndT,PTm.subst_succ,ConciseIPRA.PTm.subst_zero,one,Syn.subst_var,Matrix.cons_val] using
    five_at (inverseData (var 1) (var 3) (succ (var 0)) one) i z R B A

theorem row_source (i z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) :
    Γ ⊢[PRAAx] GaussianEulerPositiveScalingGamma.source z R B A (succ i) one :=
  .andI h (.andI (zero_lt_succ i) (le_refl one))

theorem rows_cross (N z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) :
    Γ ⊢[PRAAx] equalRows Damped Product dampedBody productBody N (parameters z R B A) (parameters z R B A) := by
  refine .allI (.impI ?_)
  let sh (x : PTm n) := Syn.shift x
  let Δ := lt (var 0) (sh N) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh A) := by
    simpa only [Fm.shift,GaussianEulerIntegralGammaIdentification.subst_source,Syn.shift,sh,Δ] using h.shift.wk
  have e := GaussianEulerPositiveScalingGamma.original_scaling_is_Gamma
    (sh z) (sh R) (sh B) (sh A) (succ (var 0)) one (row_source (var 0) _ _ _ _ hs)
  simpa only [Syn.shift,sh,Δ,subst_parameters] using
    cross_data_congr Damped Product _ _ _ _
      (damped_at (var 0) (sh z) (sh R) (sh B) (sh A)).eqSymm
      (product_at (var 0) (sh z) (sh R) (sh B) (sh A)).eqSymm e

theorem finite_scaling (N z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) :
    Γ ⊢[PRAAx] crossEquivalent nameF productSumF (data N z R B A) (data N z R B A) :=
  family_sum_cross Damped Product dampedBody productBody N _ _ (rows_cross N z R B A h)

/-- The common original Gamma datum, decoded from the same fixed parameters. -/
def gammaBody : PTm 1 :=
  let x := var 0
  gammaData (fstT (fstT x)) (sndT (fstT x)) (fstT (sndT x)) (sndT (sndT x))

@[simp] private theorem subst_gammaData {m : ℕ} (σ : Fin n → PTm m) (z R B A : PTm n) :
    Syn.subst σ (gammaData z R B A) =
      gammaData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) := by
  simp [gammaData,GaussianGammaReciprocalInverse.gammaHeight]

theorem gamma_at (z R B A : PTm n) :
    Γ ⊢[PRAAx] inst1 gammaBody (parameters z R B A) ≐ gammaData z R B A := by
  simpa only [gammaBody,inst1,subst_gammaData,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val] using
    five_at (gammaData (var 1) (var 2) (var 3) (var 4)) (ConciseIPRA.PTm.zero : PTm n) z R B A

theorem damped_regular (N z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) :
    Γ ⊢[PRAAx] pointCN nameF (data N z R B A) := by
  apply GaussianNamedFiniteSumFamily.regular Damped dampedBody
  refine .allI (.impI ?_)
  let sh (x : PTm n) := Syn.shift x
  let Δ := lt (var 0) (sh N) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh A) := by
    simpa only [Fm.shift,GaussianEulerIntegralGammaIdentification.subst_source,Syn.shift,sh,Δ] using h.shift.wk
  let j : PTm (n+1) := var 0
  have hi := GaussianEulerPositiveScalingGamma.improper_source (sh z) (sh R) (sh B) (sh A) (succ j) one
    (row_source j _ _ _ _ hs)
  simpa only [Syn.shift,sh,Δ,j,subst_parameters] using
    point_data_congr Damped _ _ (damped_at j (sh z) (sh R) (sh B) (sh A)).eqSymm
      (GaussianEulerPositiveScalingImproper.name_regular _ _ _ _ _ _ hi)

theorem dirichlet_rows_regular (N z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) :
    Γ ⊢[PRAAx] regularRows inverseF dirichletBody N (parameters z R B A) := by
  refine .allI (.impI ?_)
  let sh (x : PTm n) := Syn.shift x
  let Δ := lt (var 0) (sh N) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh A) := by
    simpa only [Fm.shift,GaussianEulerIntegralGammaIdentification.subst_source,Syn.shift,sh,Δ] using h.shift.wk
  let j : PTm (n+1) := var 0
  have hc := GaussianEulerPositiveScalingGamma.constant_source (sh z) (sh R) (sh B) (sh A) (succ j) one
    (row_source j _ _ _ _ hs)
  simpa only [Syn.shift,sh,Δ,j,subst_parameters] using
    point_data_congr inverseF _ _ (dirichlet_at j (sh z) (sh R) (sh B) (sh A)).eqSymm
      (GaussianEulerPositiveScalingConstant.inverse_regular _ _ _ _ hc)

theorem dirichlet_regular (N z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) :
    Γ ⊢[PRAAx] pointCN dirichletF (data N z R B A) :=
  GaussianNamedFiniteSumFamily.regular inverseF dirichletBody N _
    (dirichlet_rows_regular N z R B A h)

def gammaProductF : PR 2 := multiplyF dirichletF gammaF
def gammaProductData (N z R B A : PTm n) : PTm n :=
  multiplyData dirichletF gammaF (data N z R B A) (gammaData z R B A)

ipra_subst gammaProductData

theorem product_factored (N z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) :
    Γ ⊢[PRAAx] crossEquivalent productSumF gammaProductF (data N z R B A) (gammaProductData N z R B A) := by
  let x := parameters z R B A
  let y := data N z R B A
  have hg := GaussianEulerIntegralGammaIdentification.original_gamma_regular z R B A h
  have e := gamma_at (Γ := Γ) z R B A
  have hInst : Γ ⊢[PRAAx] pointCN gammaF (inst1 gammaBody x) :=
    point_data_congr gammaF _ _ e.eqSymm hg
  have hproduct := GaussianNamedFiniteSumFamilyMultiply.family_multiply_cross inverseF gammaF dirichletBody
    gammaBody N x (dirichlet_rows_regular N z R B A h) hInst
  have congr : Γ ⊢[PRAAx] multiplyData dirichletF gammaF y (inst1 gammaBody x) ≐
      gammaProductData N z R B A := by
    simpa only [gammaProductData,GaussianNameArithmetic.subst_multiplyData,Syn.subst_var,Matrix.cons_val]
      using Prf.eqCongr (multiplyData dirichletF gammaF (var 0) (var 1) : PTm 2) (σ := ![y,inst1 gammaBody x])
        (σ' := ![y,gammaData z R B A]) (fun j => by fin_cases j; exact .eqRefl y; exact e)
  have eqBody : GaussianNamedFiniteSumFamilyMultiply.mixedBody inverseF gammaF dirichletBody gammaBody =
      productBody := by
    simp only [GaussianNamedFiniteSumFamilyMultiply.mixedBody,dirichletBody,productBody,productData,inst1,gammaBody,
      subst_gammaData,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val]
  rw [eqBody] at hproduct
  exact cross_data_congr productSumF gammaProductF y y _ _ (.eqRefl _) congr hproduct

/-- Exact identity for the original improper sum at every internal count, including zero. -/
theorem finite_gamma_dirichlet (N z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) :
    Γ ⊢[PRAAx] crossEquivalent nameF gammaProductF (data N z R B A) (gammaProductData N z R B A) :=
  cross_trans nameF productSumF gammaProductF _ _ _ (finite_scaling N z R B A h)
    (product_factored N z R B A h)

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinDampedImproper
