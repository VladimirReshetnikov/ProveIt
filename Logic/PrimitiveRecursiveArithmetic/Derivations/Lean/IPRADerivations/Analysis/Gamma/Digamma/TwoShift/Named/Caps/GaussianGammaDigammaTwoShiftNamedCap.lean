import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.Named.Caps.GaussianGammaDigammaTwoShiftNamedSize
import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.Named.Charts.GaussianGammaDigammaTwoShiftNamedFreeze
import IPRADerivations.Analysis.Names.Rates.Reciprocals.GaussianNamedPositiveReciprocalFrozen
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedUniformRateClosure

/-!
# The original real named cap for the normalized Gamma ratio

The exact cap is the original product of the quadratic shift size
4 A(A+1) and the positive reciprocal of the base. Its independent
comparison with the exact rational cap uses a bound independent of the
late chart and retains the original two observation allowances.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftNamedCap

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaDigammaTwoShiftRationalWindow (coefficient)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (cross_refl cross_symm)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedPositiveLateLogSource (retimedF retimedData)
open GaussianNamedRightHalfPlane (radius threshold)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (scalar_congr positive_product)
open GaussianStirlingRationalTelescopers (fraction_same)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "S" => GaussianNamedGammaPositiveLower.source
local notation "U" => GaussianNameBounds.U
local notation "QF" => GaussianGammaDigammaTwoShiftNamedSize.nameF
local notation "QD" => GaussianGammaDigammaTwoShiftNamedSize.data
local notation "QB" => GaussianGammaDigammaTwoShiftNamedSize.budget

def inverseF (f : PR 2) : PR 2 := GaussianNamedPositiveReciprocal.nameF (retimedF f)
def inverseData (x M : PTm n) : PTm n := GaussianNamedPositiveReciprocal.data (retimedData x M) (two*M)
def nameF (f j : PR 2) : PR 2 := multiplyF (QF j) (inverseF f)
def data (f j : PR 2) (x w M : PTm n) : PTm n :=
  multiplyData (QF j) (inverseF f) (QD j w) (inverseData x M)
def budget (f j : PR 2) (x w M : PTm n) : PTm n :=
  GaussianNamedUniformRateClosure.productBudget (QB j w) ((two*M)*(two*M))
    (U (inverseF f) (inverseData x M)) (U (QF j) (QD j w))

@[simp] theorem subst_inverseData {m : ℕ} (σ : Fin n → PTm m) (x M : PTm n) :
    Syn.subst σ (inverseData x M) = inverseData (Syn.subst σ x) (Syn.subst σ M) := by simp [inverseData,two]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (f j : PR 2) (x w M : PTm n) :
    Syn.subst σ (data f j x w M) = data f j (Syn.subst σ x) (Syn.subst σ w) (Syn.subst σ M) := by simp [data]

@[simp] theorem subst_budget {m : ℕ} (σ : Fin n → PTm m) (f j : PR 2) (x w M : PTm n) :
    Syn.subst σ (budget f j x w M) = budget f j (Syn.subst σ x) (Syn.subst σ w) (Syn.subst σ M) := by
  simp [budget,GaussianNamedUniformRateClosure.productBudget,two]

theorem inverse_regular (f : PR 2) (x M : PTm n) (h : Γ ⊢[PRAAx] S f x M) :
    Γ ⊢[PRAAx] pointCN (inverseF f) (inverseData x M) :=
  GaussianNamedPositiveReciprocal.name_regular _ _ _ _ (GaussianGammaDigammaTwoShiftNamedFreeze.baseLog_input f x M h)

theorem name_regular (f j : PR 2) (x w M : PTm n) (hf : Γ ⊢[PRAAx] S f x M)
    (hj : Γ ⊢[PRAAx] pointCN j w) : Γ ⊢[PRAAx] pointCN (nameF f j) (data f j x w M) :=
  multiply_fast _ _ _ _ (GaussianGammaDigammaTwoShiftNamedSize.name_regular j w hj) (inverse_regular f x M hf)

private theorem inverse_fraction_congr (a b c d : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d)
    (eq : Γ ⊢[PRAAx] fraction a b ≐ fraction c d) : Γ ⊢[PRAAx] fraction b a ≐ fraction d c := by
  have right : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (fraction a b)) (ZT.ofNat c) d :=
    scalar_congr (congrFst eq).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianGammaDigammaHarmonicCells.point_fraction_represents c d hd)
  have p := RationalMultiplicativeConvexity.natural_representation_cross (fstT (fraction a b)) a b c d
    (GaussianGammaDigammaHarmonicCells.point_fraction_represents a b hb) right
  exact fraction_same b a d c ha hc ((mul_comm b c).eqTrans (p.eqSymm.eqTrans (mul_comm a d)))

theorem inverse_frozen_rate (f : PR 2) (s r x M a b : PTm n)
    (hf : Γ ⊢[PRAAx] S f x M) (ha : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source a b)
    (hr : Γ ⊢[PRAAx] le s r) (he : Γ ⊢[PRAAx] ap2 f (r+threshold M) x ≐ fraction a b) :
    Γ ⊢[PRAAx] independentRate (inverseF f) constantF (inverseData x M) (fraction b a)
      ((two*M)*(two*M)) (unit s) := by
  let F := retimedF f
  let X := retimedData x M
  let E := two*M
  let A := GaussianNamedPositiveLogarithm.numerator F r X
  let B := GaussianNamedPositiveLogarithm.denominator F r X
  let q := fraction B A
  have hs := GaussianGammaDigammaTwoShiftNamedFreeze.baseLog_input f x M hf
  have dom := (GaussianNamedPositiveLogarithm.decoded_domain F r X E (radius f x) hs).andE₁
  have decoded := (GaussianNamedPositiveLogarithm.decoded_value F r X E (radius f x) hs).eqTrans
    ((GaussianNamedPositiveLateLogSource.sample_at f r x M).eqTrans he)
  have eq := inverse_fraction_congr A B a b dom.andE₁ dom.andE₂ ha.andE₁ ha.andE₂ decoded
  have hr' := unit_positive (Γ := Γ) r
  have raw := GaussianNamedPositiveReciprocalFrozen.original_rate F r X E (radius f x) hs
  have changeChart := GaussianNamedRateTransport.transport (inverseF f) constantF (inverseF f) constantF
    (inverseData x M) q (inverseData x M) (fraction b a) (E*E) (unit r) hr' raw
    (cross_refl _ _ (inverse_regular f x M hf))
    (GaussianSignedNameExponentialOrder.constant_equal_cross (fraction b a) q eq.eqSymm)
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ (E*E) (unit s) hr' (unit_positive s)
    (by ipra_le 𝔞(E*E)*sl (GaussianExponentialReference.unit_monotone hr)) changeChart

theorem frozen_rate (f j : PR 2) (s r x w M a b L : PTm n)
    (hf : Γ ⊢[PRAAx] S f x M) (hj : Γ ⊢[PRAAx] pointCN j w)
    (ha : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source a b)
    (hr : Γ ⊢[PRAAx] le s r) (he : Γ ⊢[PRAAx] ap2 f (r+threshold M) x ≐ fraction a b)
    (hL : Γ ⊢[PRAAx] le L (radius j w*b))
    (hJ : Γ ⊢[PRAAx] independentRate j constantF w (fraction L b) one (unit s)) :
    Γ ⊢[PRAAx] independentRate (nameF f j) constantF (data f j x w M) (fraction (coefficient b L) (a*b))
      (budget f j x w M) (unit s) := by
  let u := fraction (coefficient b L) (b*b)
  let v := fraction b a
  let R := fraction (coefficient b L) (a*b)
  let D := unit s
  let X := QD j w
  let Y := inverseData x M
  have hD := unit_positive (Γ := Γ) s
  have hX := GaussianGammaDigammaTwoShiftNamedSize.name_regular j w hj
  have hY := inverse_regular f x M hf
  have hA := GaussianGammaDigammaTwoShiftNamedSize.frozen_rate j w L b D hj ha.andE₂ hD hL hJ
  have hB := inverse_frozen_rate f s r x M a b hf ha hr he
  have raw : Γ ⊢[PRAAx] independentRate (nameF f j) (multiplyF constantF constantF)
      (data f j x w M) (multiplyData constantF constantF u v) (budget f j x w M) D :=
    GaussianNamedUniformRateClosure.same_denominator_product (QF j) (inverseF f) constantF constantF X Y u v
      (QB j w) ((two*M)*(two*M)) D _ _ hD hX hY (constant_regular _) (constant_regular _)
      (GaussianNameBounds.all_samples_bounded _ _ hY) (GaussianNameBounds.all_samples_bounded _ _ hX) hA hB
  have hb := ha.andE₂
  have hb₂ := positive_product _ _ hb hb
  have hbA := positive_product _ _ ha.andE₁ hb
  have prodEq := GaussianStirlingOddCoefficients.fraction_product (coefficient b L) (b*b) b a hb₂ ha.andE₁
  have eq : Γ ⊢[PRAAx] GaussianRationalHorner.qmul u v ≐ R :=
    prodEq.eqTrans (fraction_same _ _ _ _ (positive_product _ _ hb₂ ha.andE₁) hbA (by ipra_ring))
  exact GaussianNamedRateTransport.transport (nameF f j) (multiplyF constantF constantF) (nameF f j) constantF
    (data f j x w M) (multiplyData constantF constantF u v) (data f j x w M) R (budget f j x w M) D hD raw
    (cross_refl _ _ (name_regular f j x w M hf hj))
    (cross_symm _ _ _ _ (GaussianGammaDigammaTwoShiftNamedSize.constant_product u v R eq))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftNamedCap
