import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.GaussianGaussMultiplicationFixedProducts
import IPRADerivations.Analysis.Names.FiniteOperations.Products.Bounds.GaussianNamedFiniteProductApartness
import IPRADerivations.Analysis.Names.FiniteOperations.Products.Families.GaussianNamedFiniteProductFamily

/-!
# Apartness of the original finite Gauss denominators

Each actual reciprocal observation is bounded below by the inverse of
the anchor cap of its underlying positive-radius name. Summing these
caps through the original reference rows, and multiplying the resulting
lower bounds, gives a reciprocal clock for the actual normalized fold.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGaussEulerFiniteApartness

open_ipra
open ComplexLogarithmRemainder (oneCode normSq_one)
open GaussianCoefficientNameBounds (unit)
open GaussianGammaEulerInverseConvergence (subst_directData)
open GaussianGammaEulerReciprocalInverse (eulerF eulerData eulerHeight original_euler_inverse)
open GaussianGammaFiniteApproximantName (qF qData)
open GaussianGammaGaussReferenceProduct (argument)
open GaussianGaussMultiplicationFixedProducts (referenceF referenceData reference_regular)
open GaussianNameBounds (U U_positive sample_bound)
open GaussianNameReciprocal (apart input lower anchor nameF nameData)
open GaussianNamedFiniteProductApartness (rowLower rowLowerAt weaken_margin)
open GaussianNamedFiniteProductFamily (radius family_radius_at)
open GaussianRationalHorner (ofGaussian_represents)
open GaussianRationalLowerBounds (lower_from_representation)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (qone reciprocal_canonical)
open GaussianRootSchedule (binaryLength binary_length_correct)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "ER" => GaussianGammaGaussReferenceEulerProduct.rowF
local notation "rowData" => GaussianGammaGaussReferenceEulerProduct.rowData
local notation "rowRadius" => GaussianGammaGaussReferenceEulerProduct.rowRadius
local notation "threshold" => GaussianGammaGaussReferenceEulerProduct.threshold

private theorem unit_lower : Γ ⊢[PRAAx] lower (qone : PTm n) one :=
  lower_from_representation _ oneCode one one one (le_refl _) (le_refl _) (ofGaussian_represents _ _ (le_refl _))
    (le_congr (by ipra_ring) (congrMul (.eqRefl _) normSq_one).eqSymm (le_refl _))

theorem inverse_name_lower (f : PR 2) (p h x : PTm n) (hi : Γ ⊢[PRAAx] input f h x) :
    Γ ⊢[PRAAx] lower (ap2 (nameF f) p (nameData h x)) (U f x) := by
  let t := GaussianFastValueCut.exponent (GaussianNameReciprocal.modulus h) p
  let y := GaussianNameReciprocal.tail f h x t
  let v := GaussianNameReciprocal.raw f h x t
  have read : Γ ⊢[PRAAx] ap2 (nameF f) p (nameData h x) ≐ v :=
    (GaussianNameReciprocal.name_at f h x p).eqTrans
      (GaussianExponentialReference.recode_fixed v (reciprocal_canonical y))
  have hy := sample_bound f x (t+anchor h) hi.andE₁
  have prod := (qmul_commutative v y).eqTrans (GaussianNameReciprocal.tail_inverse_identity f h x t hi.andE₁ hi.andE₂)
  have prodLower := GaussianRationalLowerBounds.lower_congr prod.eqSymm (.eqRefl _) (.eqRefl _) unit_lower
  have invLower := GaussianBoundedInverseApartness.factor_lower v y one one (U f x) (le_refl one)
    (U_positive f x) prodLower hy
  exact GaussianRationalLowerBounds.lower_congr read.eqSymm (.eqRefl _) (one_mul _) invLower

def inverseApartClock (f : PR 2) (x : PTm n) : PTm n := binaryLength (U f x)

theorem inverse_name_apart (f : PR 2) (h x : PTm n) (hi : Γ ⊢[PRAAx] input f h x) :
    Γ ⊢[PRAAx] apart (nameF f) (inverseApartClock f x) (nameData h x) :=
  weaken_margin _ (U f x) _ (U_positive f x) (binary_length_correct (U f x)).andE₁
    (inverse_name_lower f (anchor (inverseApartClock f x)) h x hi)

theorem euler_apart (z R B a d N : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianGammaEulerReciprocalInverse.source z R B a d N) :
    Γ ⊢[PRAAx] apart eulerF (inverseApartClock qF (qData z B N)) (eulerData z R B d N) :=
  inverse_name_apart qF (eulerHeight z R B d N) (qData z B N) (original_euler_inverse z R B a d N hs).andE₁

def referenceQBody : PTm 2 := qData (argument (var 0)) (fstT (var 1)) (sndT (var 1))
def referenceDenominator (m N : PTm n) : PTm n := one+radius qF referenceQBody m (rowData m N)
def referenceApartClock (m N : PTm n) : PTm n :=
  GaussianNamedFiniteProductApartness.apartClock m (referenceDenominator m N)

ipra_subst referenceDenominator [one]

private theorem reference_q_at (r m N : PTm n) : Γ ⊢[PRAAx]
    inst2 referenceQBody r (rowData m N) ≐ qData (argument r) m N := by
  have e := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (qData (argument (var 0)) (var 1) (var 2) : PTm 3)
    (σ := ![r, fstT (pairT m N), sndT (pairT m N)]) (σ' := ![r,m,N]) (fun i => by
      fin_cases i
      · exact .eqRefl _
      · exact fst_pair _ _
      · exact snd_pair _ _)
  simpa only [referenceQBody,inst2,GaussianGammaGaussReferenceEulerProduct.rowData,subst_directData,
    GaussianGammaGaussReferenceProduct.subst_argument,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using e

private theorem reference_row_lower_at (s p r m N : PTm n) (hr : Γ ⊢[PRAAx] lt r m)
    (hn : Γ ⊢[PRAAx] le (threshold s m) N) :
    Γ ⊢[PRAAx] lower (ap3 ER p r (rowData m N)) (referenceDenominator m N) := by
  let z := argument r
  let x := qData z m N
  let y := inst2 referenceQBody r (rowData m N)
  have hrow := GaussianGammaGaussReferenceProduct.row_source r m hr
  have guard := GaussianGaussEulerCutoffUniform.cutoff_source s z one m one m N hrow hn
  have hi := (original_euler_inverse z one m one m N (.andI hrow guard.andE₂.andE₁)).andE₁
  have b := inverse_name_lower qF (succ p) (eulerHeight z one m m N) x hi
  have e : Γ ⊢[PRAAx] U qF x ≐ U qF y := by
    simpa only [GaussianNameBounds.subst_U,Syn.subst_var,Matrix.cons_val_zero] using
      Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (U qF (var 0) : PTm 1)
        (σ := ![x]) (σ' := ![y]) (fun i => by fin_cases i; exact (reference_q_at r m N).eqSymm)
  have cap := family_radius_at qF referenceQBody m (rowData m N) r hr
  have hD : Γ ⊢[PRAAx] le (U qF x) (referenceDenominator m N) := le_trans
    (le_congr e.eqSymm (.eqRefl _) cap) (le_add_left _ _)
  exact GaussianNameReciprocal.lower_congr (GaussianGammaGaussReferenceEulerProduct.row_at p r m N).eqSymm
    (.eqRefl _) (weaken_margin _ (U qF x) _ (U_positive qF x) hD b)

theorem reference_rows_lower (s m N : PTm n) (hn : Γ ⊢[PRAAx] le (threshold s m) N) :
    Γ ⊢[PRAAx] rowLower ER m (referenceDenominator m N) (rowData m N) := by
  refine .allI (.allI (.impI ?_))
  let sh (w : PTm n) := Syn.shift (Syn.shift w)
  let Δ := lt (var 0) (sh m) :: (Γ.map Fm.shift).map Fm.shift
  have hn' : Δ ⊢[PRAAx] le (threshold (sh s) (sh m)) (sh N) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hn.shift.shift.wk
  simpa [rowLower,rowLowerAt,Δ,sh,Syn.shift] using reference_row_lower_at (sh s) (var 1) (var 0) (sh m) (sh N)
    (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (sh m)) hn'

theorem reference_input (s m N : PTm n) (hn : Γ ⊢[PRAAx] le (threshold s m) N) :
    Γ ⊢[PRAAx] input referenceF (referenceApartClock m N) (referenceData m N) :=
  .andI (reference_regular s m N hn)
    (GaussianNamedFiniteProductApartness.name_apart ER m (rowRadius m) one (referenceDenominator m N)
      (rowData m N) (le_add_right _ _) (reference_rows_lower s m N hn))

theorem actual_fixed_Gauss_reference_product_apart_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (threshold (var 0) (var 1)) (var 2) ⟶
      input referenceF (referenceApartClock (var 1) (var 2)) (referenceData (var 1) (var 2))) :=
  closeUniv 3 (.impI (reference_input _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGaussEulerFiniteApartness
