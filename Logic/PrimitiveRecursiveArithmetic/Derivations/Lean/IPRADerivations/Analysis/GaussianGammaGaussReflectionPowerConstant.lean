import IPRADerivations.Analysis.GaussianGammaGaussReflectionCancellation
import IPRADerivations.Analysis.GaussianNamedFiniteProductFamily

/-!
# Literal powers of two for the squared Gauss normalization

The actual finite family of constant two has code `2^N` at every
observation. Multiplying this code by the literal `1/(N+1)) gives
the exact reciprocal of the M1 sine normalization.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaGaussReflectionPowerConstant

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale oneCode mul)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaFactorialValues (natural_congr natural_one)
open GaussianGammaGaussReflectionCancellation (inverseRatio)
open GaussianNamedFiniteProduct (sample sample_zero sample_succ)
open GaussianNamedFiniteProductFamily (rowF row_at regularRows productData family_product_regular)
open GaussianNameConjugation (pointwiseEqual equal_samples_cross)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalHorner (qmul qmul_canonical qmul_represents represents_congr canonical_unique
  ofGaussian ofGaussian_represents ofGaussian_canonical)
open GaussianRationalNaturalScale (naturalPoint natural_point_represents natural_product_value)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRootAlgebra (equal equal_of_values equal_trans re_scale im_scale re_mul im_mul re_one im_one)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "FProd" => GaussianNamedFiniteProductName.nameF

def twoBody : PTm 2 := naturalPoint two
def familyF : PR 3 := rowF constantF twoBody
def twoPowerF : PR 2 := FProd familyF
def twoPowerData (N x : PTm n) : PTm n := productData constantF twoBody N x
def reciprocalModulus (N : PTm n) : PTm n := ofGaussian oneCode (succ N)

private theorem row_value (p i x : PTm n) :
    Γ ⊢[PRAAx] ap3 familyF p i x ≐ naturalPoint two := by
  have e : inst2 twoBody i x = naturalPoint two := by simp [twoBody,inst2,two,one]
  exact (row_at constantF twoBody p i x).eqTrans (by rw [e]; exact constant_at p _)

theorem two_rows (N x : PTm n) : Γ ⊢[PRAAx] regularRows constantF twoBody N x :=
  .allI (.impI (constant_regular _))

private theorem natural_times_two (k : PTm n) :
    Γ ⊢[PRAAx] qmul (naturalPoint k) (naturalPoint two) ≐ naturalPoint (k*two) := by
  have e : Γ ⊢[PRAAx] equal (mul (scale k oneCode) (scale two oneCode)) (scale (k*two) oneCode) := by
    refine equal_trans (natural_product_value k (scale two oneCode)) ?_
    apply equal_of_values <;> simp only [re_scale,im_scale] <;> ipra_simps <;> ring
  exact canonical_unique _ _ _ one (qmul_canonical _ _) (ofGaussian_canonical _ _ (le_refl one)) (le_refl one)
    (represents_congr (.eqRefl _) e (one_mul one) (qmul_represents _ _ _ _ _ _ (le_refl one) (le_refl one)
      (natural_point_represents k) (natural_point_represents two))) (natural_point_represents _)

private def powerLaw (p N x : PTm n) : Fm PTm n :=
  sample familyF p N x ≐ naturalPoint (unit N)
@[simp] private theorem subst_powerLaw {l : ℕ} (σ : Fin n → PTm l) (p N x : PTm n) :
    (powerLaw p N x).subst σ = powerLaw (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ x) := by simp [powerLaw]

theorem product_at (p N x : PTm n) :
    Γ ⊢[PRAAx] sample familyF p N x ≐ naturalPoint (unit N) := by
  have all : Γ ⊢[PRAAx] .all (powerLaw (Syn.shift p) (var 0) (Syn.shift x)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_powerLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (sample_zero familyF p x).eqTrans
        (((natural_congr (pw_zero two)).eqTrans natural_one).eqSymm)
    · simp only [subst_powerLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      let P := Syn.shift p
      let X := Syn.shift x
      let i : PTm (n+1) := var 0
      let Δ := powerLaw P i X :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] powerLaw P i X := Prf.hyp0
      exact (sample_succ familyF P i X).eqTrans ((qmul_congr ih (row_value P i X)).eqTrans
        ((natural_times_two (unit i)).eqTrans (natural_congr (pw_succ two i).eqSymm)))
  change Γ ⊢[PRAAx] powerLaw p N x
  simpa only [subst_powerLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

theorem name_at (p N x : PTm n) :
    Γ ⊢[PRAAx] ap2 twoPowerF p (twoPowerData N x) ≐ naturalPoint (unit N) :=
  (GaussianNamedFiniteProductName.name_at familyF p N (GaussianNamedFiniteProductFamily.radius constantF twoBody N x)
    one x).eqTrans (product_at _ _ _)

theorem two_power_cross (N x : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent twoPowerF constantF (twoPowerData N x) (naturalPoint (unit N)) := by
  apply equal_samples_cross _ _ _ _ (family_product_regular constantF twoBody N x (two_rows N x)) (constant_regular _)
  refine .allI ?_
  simpa [pointwiseEqual,twoPowerF,familyF,twoPowerData,productData,Syn.shift,one] using
    (name_at (Γ := Γ.map Fm.shift) (var 0) (Syn.shift N) (Syn.shift x)).eqTrans (constant_at _ _).eqSymm

theorem power_times_reciprocal (N : PTm n) :
    Γ ⊢[PRAAx] qmul (naturalPoint (unit N)) (reciprocalModulus N) ≐ inverseRatio N := by
  let m := succ N
  let v := unit N
  have hm := zero_lt_succ (Γ := Γ) N
  have e : Γ ⊢[PRAAx] equal (mul (scale v oneCode) oneCode) (scale v oneCode) := by
    apply equal_of_values <;> simp only [re_mul,im_mul,re_one,im_one] <;> ring
  exact canonical_unique _ _ _ m (qmul_canonical _ _) (ofGaussian_canonical _ _ hm) hm
    (represents_congr (.eqRefl _) e (one_mul _) (qmul_represents _ _ _ _ _ _ (le_refl one) hm
      (natural_point_represents v) (ofGaussian_represents _ _ hm))) (ofGaussian_represents _ _ hm)

end LeanProofs.IPRA.Analysis.GaussianGammaGaussReflectionPowerConstant
