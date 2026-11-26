import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.FixedCoefficients.GaussianBarnesCanonicalFixedTaylorDerivativeName
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalTaylorDerivativeZero

/-!
# Degree zero of each original finite Barnes Taylor name

The constant coefficient of the stored polynomial is the kept power
product at every prefactor clock. The fixed central exponential and
the zero factorial therefore give the literal finite product at the
same cutoff.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFixedTaylorDerivativeZero

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalBaseProductShift (powerBody powerProduct)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyData multiplyF)
open GaussianNameConjugation (equal_samples_cross)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianRationalHorner (qmul)
open GaussianRationalNaturalScale (natScale_as_product natScale_congr natScale_one_canonical naturalPoint)
open LeanProofs.IPRA.Analysis.Products (fact)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "C" => constantF
local notation "K" => GaussianBarnesCanonicalFixedTaylorCoefficientName.nameF
local notation "kd" => GaussianBarnesCanonicalFixedTaylorCoefficientName.data
local notation "H" => GaussianBarnesCanonicalFixedTaylorDerivativeName.coefficientF
local notation "hd" => GaussianBarnesCanonicalFixedTaylorDerivativeName.coefficientData
local notation "F" => GaussianBarnesCanonicalFixedTaylorDerivativeName.nameF
local notation "fd" => GaussianBarnesCanonicalFixedTaylorDerivativeName.data
local notation "S" => GaussianBarnesCanonicalFiniteCentralExponential.finiteNameF
local notation "sd" => GaussianBarnesCanonicalFiniteCentralExponential.finiteData
local notation "V" => GaussianBarnesCanonicalValue.prefixF
local notation "vd" => GaussianBarnesCanonicalProduct.literalData

theorem coefficient_sample (p z R B r M : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] ap2 K p (kd z R B r M zero) ≐ powerProduct z B (initial R) := by
  let k := GaussianBarnesCanonicalTaylorProductCoefficientName.clock p z R B M zero
  let q := GaussianBarnesCanonicalExponentTaylorRetainedCoefficient.precision k R
  exact (GaussianBarnesCanonicalFixedTaylorCoefficientName.sample_at p z R B r M zero).eqTrans
    (GaussianBarnesCanonicalTaylorDerivativeZero.coefficient_at_zero q z R B r M hB)

theorem coefficient_cross (z R B r M : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] crossEquivalent K C (kd z R B r M zero) (powerProduct z B (initial R)) := by
  apply equal_samples_cross K C _ _
    (GaussianBarnesCanonicalFixedTaylorCoefficientName.regular z R B r M zero hz (zero_le _)) (constant_regular _)
  refine .allI ?_
  let sh (x : PTm n) := Syn.shift x
  let p : PTm (n+1) := var 0
  have hB : Γ.map Fm.shift ⊢[PRAAx] le one (sh B) :=
    by simpa [sh,Fm.shift,Syn.shift] using hz.andE₁.shift
  simpa only [sh,p,Syn.shift,GaussianBarnesCanonicalFixedTaylorCoefficientName.subst_data,
    GaussianBarnesCanonicalBaseProductShift.subst_powerProduct,GaussianBarnesCanonicalLogSchedule.subst_initial,
    ConciseIPRA.PTm.subst_zero] using
    (coefficient_sample p (sh z) (sh R) (sh B) (sh r) (sh M) hB).eqTrans
      (constant_at p (powerProduct (sh z) (sh B) (initial (sh R)))).eqSymm

theorem value_cross (z R B r M : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] crossEquivalent F V (fd z R B r M zero) (vd z R B (initial R+r)) := by
  let h := powerProduct z B (initial R)
  let a : PTm n := naturalPoint (fact zero)
  let s := sd z R B r
  have hr := constant_regular (Γ := Γ) h
  have ar := constant_regular (Γ := Γ) a
  have sr := GaussianBarnesCanonicalFiniteCentralExponential.finite_regular z R B r hz
  have kr := GaussianBarnesCanonicalFixedTaylorCoefficientName.regular z R B r M zero hz (zero_le _)
  have fr := GaussianBarnesCanonicalFixedTaylorDerivativeName.coefficient_regular z R B r M zero hz (zero_le _)
  have hc := GaussianRationalFiniteProduct.product_canonical (Γ := Γ) powerBody (initial R)
    (GaussianBarnesCanonicalPolynomialShift.data z B)
  have unit : Γ ⊢[PRAAx] qmul a h ≐ h :=
    (natScale_as_product (fact zero) h).eqSymm.eqTrans
      ((natScale_congr (LeanProofs.IPRA.Analysis.ExponentialSeries.fact_zero' (Γ := Γ)) (.eqRefl h)).eqTrans
        (natScale_one_canonical h hc))
  have factor : Γ ⊢[PRAAx] crossEquivalent H C (hd z R B r M zero) h :=
    cross_trans _ _ _ _ _ _ (multiply_cross C C K C a a (kd z R B r M zero) h ar ar kr hr
      (cross_refl C a ar) (coefficient_cross z R B r M hz))
      (GaussianGammaDigammaTwoShiftNamedSize.constant_product a h h unit)
  have product : Γ ⊢[PRAAx] crossEquivalent F (multiplyF S C) (fd z R B r M zero) (multiplyData S C s h) :=
    multiply_cross S S H C s s (hd z R B r M zero) h sr sr fr hr (cross_refl S s sr) factor
  exact cross_trans _ _ _ _ _ _ product
    (cross_trans _ _ _ _ _ _ (GaussianNameRingLaws.multiply_commutative S C s h sr hr)
      (cross_symm _ _ _ _ (GaussianBarnesCanonicalFiniteCentralExponential.literal_factorization z R B r hz)))

theorem actual_Barnes_fixed_zero_factorial_Taylor_literal_product_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (let z := var 0
       let R := var 1
       let B := var 2
       let r := var 3
       let M := var 4
       source z R B ⟶ crossEquivalent F V (fd z R B r M zero) (vd z R B (initial R+r))) :=
  closeUniv 5 (.impI (value_cross _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFixedTaylorDerivativeZero
