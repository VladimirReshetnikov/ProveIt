import IPRADerivations.Analysis.Trigonometry.GaussianSineProductTailLower
import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGammaReflectionProduct

/-!
# The R3 lower bound for z times the literal sine product

The finite pole guard extends to all larger indices by the original disk
bound. Pairing the integer factors and using the uniform inverse-square
suffix bound yields δ^(2L+1)/(2^(4R²)(L!)²) whenever L ≥ 2R. The same
lower comparison holds literally at the original product name's late
rational queries.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianSineProductReflectionLower

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaEulerReflectionHead (sineProduct body)
open GaussianGammaEulerHeadLower (poleAt poleGuard pole_at translated)
open GaussianSineProductHeadLower (head_lower argument_lower denominator_positive)
open GaussianRationalHorner (qmul qmul_canonical ofGaussian positive_product)
open GaussianRationalLowerBounds (lower lower_congr product_lower)
open GaussianRationalFiniteProduct (product_split product_index_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameArithmetic (multiply_at multiplyModulus recode_congr)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianSineProductName (cutoff sample_at)
open GaussianGammaReflectionProduct (productLinearF productLinearData)
open GaussianCoordinateRadius (native_coordinates native_squared)
open ComplexLogarithmRemainder (normSq re)
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_tri zabs_neg)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "gneg" => ComplexLogarithmRemainder.neg
local notation "H" => GaussianSineProductHeadLower.input
local notation "S" => GaussianSineProductName.nameF
local notation "D" => GaussianSineProductName.data

def guardCutoff (R : PTm n) : PTm n := succ (two*R)
def numerator (a L : PTm n) : PTm n := a*GaussianSineProductHeadLower.numerator a L
def denominator (d R L : PTm n) : PTm n :=
  d*(GaussianSineProductHeadLower.denominator d L*unit (two*(two*(R*R))))

def source (z R B a d L : PTm n) : Fm PTm n :=
  ((le one R ⋏ le one B) ⋏ (le one a ⋏ le a d)) ⋏
    (ComplexLogarithmRemainder.bounded z (R*B) ⋏ (le (two*R) L ⋏ H z B a d (guardCutoff R)))

theorem automatic_pole_at (z R B a d j : PTm n)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (ha : Γ ⊢[PRAAx] le a d) (hj : Γ ⊢[PRAAx] le (succ R) j) :
    Γ ⊢[PRAAx] poleAt z B a d j := by
  let t := translated z B j
  have abs : Γ ⊢[PRAAx] le (zabs (re z)) (R*B) := by
    have native : Γ ⊢[PRAAx] le ((one*one)*normSq z) ((R*R)*(B*B)) :=
      le_congr (by ipra_ring) (by ipra_ring) hz
    exact le_congr (one_mul _) (.eqRefl _) (native_coordinates z R one B native).andE₁
  have eq : ZT.toZ Γ (ZT.ofNat (B*j)) = ZT.toZ Γ (re t)+ZT.toZ Γ (-re z) := by
    simp only [t,translated,GaussianRootAlgebra.re_add,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one,
      ZT.toZ_neg,ZT.toZ_ofNat]
    ipra_simps
    ring
  have tri : Γ ⊢[PRAAx] le (B*j) (zabs (re t)+zabs (re z)) :=
    le_congr (GaussianL1.abs_ofNat (B*j)) (congrAdd (.eqRefl _) (zabs_neg _)) (zabs_tri eq)
  have start : Γ ⊢[PRAAx] le (B+R*B) (B*j) :=
    le_congr (by ipra_ring) (mul_comm _ _) (mul_le_mul_right B hj)
  have real : Γ ⊢[PRAAx] le B (zabs (re t)) := by
    exact le_of_add_le_add_right (c := R*B)
      (le_trans (le_trans start tri) (add_le_add₂ (le_refl _) abs))
  have bound : Γ ⊢[PRAAx] le (B*B) (normSq t) :=
    le_trans (le_mul_mono real real)
      (le_congr (.eqRefl _) (native_squared t).eqSymm (le_add_right _ _))
  exact le_congr (by ipra_ring) (.eqRefl _)
    (le_mul_mono (le_mul_mono ha ha) bound)

theorem extend_guard (z R B a d L : PTm n)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (ha : Γ ⊢[PRAAx] le a d) (h : Γ ⊢[PRAAx] poleGuard z B a d (guardCutoff R)) :
    Γ ⊢[PRAAx] poleGuard z B a d L := by
  refine .allI (.impI ?_)
  let Δ := le (var 0) (Syn.shift L) :: Γ.map Fm.shift
  let z' := Syn.shift z
  let R' := Syn.shift R
  let B' := Syn.shift B
  let a' := Syn.shift a
  let d' := Syn.shift d
  have hh : Δ ⊢[PRAAx] poleGuard z' B' a' d' (guardCutoff R') := by
    simpa [Δ,z',R',B',a',d',guardCutoff,Fm.shift,Syn.shift] using h.shift.wk
  have hd : Δ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z' (R'*B') := by
    simpa [Δ,z',R',B',Fm.shift,Syn.shift] using hz.shift.wk
  have adj : Δ ⊢[PRAAx] le a' d' := by simpa [Δ,a',d',Fm.shift,Syn.shift] using ha.shift.wk
  have later : Δ ⊢[PRAAx] le (succ R') (guardCutoff R') := by
    apply le_of_eq_add (d := R')
    unfold guardCutoff
    ipra_ring
  refine .orE (le_total (var 0) (guardCutoff R')) (pole_at _ _ _ _ _ _ hh.wk Prf.hyp0) ?_
  exact automatic_pole_at z' R' B' a' d' (var 0) hd.wk adj.wk (le_trans later.wk Prf.hyp0)

theorem numerator_positive (a L : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] le one (numerator a L) :=
  positive_product _ _ ha (GaussianFactorBudget.power_positive _ _ (positive_product _ _ ha ha))

theorem denominator_positive (d R L : PTm n) (hd : Γ ⊢[PRAAx] le one d) :
    Γ ⊢[PRAAx] le one (denominator d R L) :=
  positive_product _ _ hd (positive_product _ _ (GaussianSineProductHeadLower.denominator_positive _ _ hd)
    (unit_positive _))

theorem finite_lower (z R B a d L N : PTm n) (hs : Γ ⊢[PRAAx] source z R B a d L)
    (hN : Γ ⊢[PRAAx] le L N) :
    Γ ⊢[PRAAx] lower (qmul (ofGaussian z B) (sineProduct z B N)) (numerator a L) (denominator d R L) := by
  let r := monus N L
  let t := GaussianInverseSquareProductTail.product body L r (pairT z B)
  have hB := hs.andE₁.andE₁.andE₂
  have ad := hs.andE₁.andE₂.andE₂
  have hd := le_trans hs.andE₁.andE₂.andE₁ ad
  have hz := hs.andE₂.andE₁
  have hL := hs.andE₂.andE₂.andE₁
  have guard := hs.andE₂.andE₂.andE₂
  have pos := extend_guard z R B a d L hz ad guard.andE₁
  have neg := extend_guard (gneg z) R B a d L (ComplexLogarithmRemainder.bounded_neg hz) ad guard.andE₂
  have head := head_lower z B a d L hB hd (.andI pos neg)
  have tail := GaussianSineProductTailLower.tail_lower z R B L r hB hz hL
  have hD := GaussianSineProductHeadLower.denominator_positive d L hd
  have hU := unit_positive (Γ := Γ) (two*(two*(R*R)))
  have split : Γ ⊢[PRAAx] sineProduct z B N ≐ qmul (sineProduct z B L) t :=
    (product_index_congr body (eq_add_of_le hN) (.eqRefl _)).eqTrans (product_split body L r (pairT z B))
  have s := lower_congr split.eqSymm (by ipra_ring) (.eqRefl _) (product_lower _ _ _ _ _ _ hD hU head tail)
  have harg := argument_lower z B a d hB hd (pole_at z B a d L zero pos (zero_le _))
  exact product_lower _ _ _ _ _ _ hd (positive_product _ _ hD hU) harg s

theorem cutoff_ge_unit (R p : PTm n) (hR : Γ ⊢[PRAAx] le one R) :
    Γ ⊢[PRAAx] le (unit p) (cutoff R p) := by
  have hpow := GaussianFactorBudget.power_positive (one+R*R) (GaussianSineProductName.initial R)
    (le_add_right one (R*R) : Γ ⊢[PRAAx] le one (one+R*R))
  have htwo : Γ ⊢[PRAAx] le one two := zero_lt_succ _
  have hb : Γ ⊢[PRAAx] le one (GaussianSineProductName.bound R) := positive_product _ _ htwo hpow
  have hr : Γ ⊢[PRAAx] le one (GaussianSineProductName.rate R) :=
    positive_product _ _ hb (positive_product _ _ htwo (positive_product _ _ hR hR))
  have c : Γ ⊢[PRAAx] le (unit p) (GaussianSineProductName.rate R*unit p) :=
    le_congr (one_mul _ ) (.eqRefl _) (mul_le_mul_right (unit p) hr)
  exact le_trans c (le_add_left _ _)

theorem named_product_lower (z R B a d L p : PTm n) (hs : Γ ⊢[PRAAx] source z R B a d L)
    (hp : Γ ⊢[PRAAx] le L (unit p)) :
    Γ ⊢[PRAAx] lower (ap2 productLinearF p (productLinearData z R B)) (numerator a L) (denominator d R L) := by
  let c := ofGaussian z B
  let y := D z R B
  let k := GaussianFastValueCut.exponent (multiplyModulus constantF S c y) p
  have hk : Γ ⊢[PRAAx] le p k := le_add_right _ _
  have hN := le_trans (le_trans hp (GaussianBalancedRadiusArithmetic.unit_monotone p k hk))
    (cutoff_ge_unit R k hs.andE₁.andE₁.andE₁)
  have e : Γ ⊢[PRAAx] ap2 productLinearF p (productLinearData z R B) ≐
      qmul c (sineProduct z B (cutoff R k)) :=
    (multiply_at constantF S c y p).eqTrans
      ((recode_congr (qmul_congr (constant_at k c) (sample_at z R B k))).eqTrans
        (GaussianExponentialReference.recode_fixed _ (qmul_canonical _ _)))
  exact lower_congr e.eqSymm (.eqRefl _) (.eqRefl _) (finite_lower z R B a d L (cutoff R k) hs hN)

theorem actual_sine_product_R3_lower_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶ le (var 5) (unit (var 6)) ⟶
      lower (ap2 productLinearF (var 6) (productLinearData (var 0) (var 1) (var 2)))
        (numerator (var 3) (var 5)) (denominator (var 4) (var 1) (var 5))) :=
  closeUniv 7 (.impI (.impI (named_product_lower _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianSineProductReflectionLower
