import IPRADerivations.Analysis.Gamma.GaussianGammaExponentStep
import IPRADerivations.Analysis.Gamma.EulerProducts.CanonicalProducts.GaussianGammaCanonicalExponentBound
import IPRADerivations.Analysis.Gamma.EulerProducts.CanonicalProducts.GaussianGammaCanonicalTailExponential
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianRationalRoundedPower
import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianRationalFiniteRoots
import IPRADerivations.Analysis.Exponential.GaussianPositiveExponentialMajorant
import IPRADerivations.Analysis.Exponential.GaussianScalarExponentialProductTail

/-!
# Literal finite Weierstrass factors

The finite program evaluates the exponential of the individual argument
`-z/(B(k+1))` by the original rational Taylor kernel. Its finite fold
uses the literal factors in C5, at a common numerical Taylor cutoff.
The exact Euler harmonic increment identifies the exponent of the folded
prefix at the next index, independently of the Taylor truncation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaWeierstrassFactors

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (ofGaussian qadd qmul qzero canonical)
open GaussianRationalMetric (bounded distanceBounded qsub qnegative qnegative_canonical)
open GaussianRationalSyntheticDivision (qone qadd_congr qmul_congr qsub_congr qzero_add)
open GaussianRationalPowerAlgebra (qmul_commutative qmul_shuffle)
open GaussianRationalPolynomialExponential (scalarSum)
open GaussianRationalFiniteProduct (qprod product_zero product_succ)
open GaussianReciprocalHorner (qmul_one_right qmul_associative qadd_zero_right)
open GaussianRationalReciprocal (bound_congr bounded_negative bounded_product)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianGammaCanonicalExponent (harmonicPoint)
open GaussianScalarExponentialProductTail (rectangleCutoff actual_scalar_product_dyadic)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def localArgument (i z B : PTm n) : PTm n := qnegative (ofGaussian z (B*succ i))

def harmonicArgument (z B i : PTm n) : PTm n := qmul (qsub qzero (harmonicPoint i)) (ofGaussian z B)

def factor (i z B K : PTm n) : PTm n :=
  qmul (GaussianGammaEulerHead.factor i z B) (scalarSum (localArgument i z B) K)

def data (z B K : PTm n) : PTm n := pairT z (pairT B K)

def factorBody : PTm 2 := factor (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1)))

def literalPrefix (z B K j : PTm n) : PTm n := qmul (ofGaussian z B) (qprod factorBody j (data z B K))

def foldedPrefix (z B K j : PTm n) : PTm n :=
  qmul (GaussianGammaEulerHead.head z B j) (scalarSum (harmonicArgument z B j) K)

@[simp] theorem subst_localArgument {m : ℕ} (σ : Fin n → PTm m) (i z B : PTm n) :
    Syn.subst σ (localArgument i z B) = localArgument (Syn.subst σ i) (Syn.subst σ z) (Syn.subst σ B) := by
  simp [localArgument]

@[simp] theorem subst_harmonicArgument {m : ℕ} (σ : Fin n → PTm m) (z B i : PTm n) :
    Syn.subst σ (harmonicArgument z B i) = harmonicArgument (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ i) := by
  simp [harmonicArgument]

@[simp] theorem subst_factor {m : ℕ} (σ : Fin n → PTm m) (i z B K : PTm n) :
    Syn.subst σ (factor i z B K) = factor (Syn.subst σ i) (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ K) := by
  simp [factor]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z B K : PTm n) :
    Syn.subst σ (data z B K) = data (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ K) := by simp [data]

@[simp] theorem subst_literalPrefix {m : ℕ} (σ : Fin n → PTm m) (z B K j : PTm n) :
    Syn.subst σ (literalPrefix z B K j) = literalPrefix (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ K) (Syn.subst σ j) := by
  simp [literalPrefix]

@[simp] theorem subst_foldedPrefix {m : ℕ} (σ : Fin n → PTm m) (z B K j : PTm n) :
    Syn.subst σ (foldedPrefix z B K j) = foldedPrefix (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ K) (Syn.subst σ j) := by
  simp [foldedPrefix]

theorem factor_at (i z B K : PTm n) :
    Γ ⊢[PRAAx] inst2 factorBody i (data z B K) ≐ factor i z B K := by
  have tail := snd_pair (Γ := Γ) z (pairT B K)
  simpa [factorBody,inst2] using Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
    (factor (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![i, fstT (data z B K), fstT (sndT (data z B K)), sndT (sndT (data z B K))])
    (σ' := ![i,z,B,K])
    (fun j => by
      fin_cases j
      · exact .eqRefl _
      · exact fst_pair _ _
      · exact (congrFst tail).eqTrans (fst_pair _ _)
      · exact (congrSnd tail).eqTrans (snd_pair _ _))

theorem literal_zero (z B K : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] literalPrefix z B K zero ≐ ofGaussian z B :=
  (qmul_congr (.eqRefl _) (product_zero factorBody (data z B K))).eqTrans
    (qmul_one_right _ (GaussianRationalHorner.ofGaussian_canonical _ _ hB))

theorem literal_step (z B K j : PTm n) :
    Γ ⊢[PRAAx] literalPrefix z B K (succ j) ≐ qmul (literalPrefix z B K j) (factor j z B K) :=
  (qmul_congr (.eqRefl _) ((product_succ factorBody j (data z B K)).eqTrans
    (qmul_congr (.eqRefl _) (factor_at j z B K)))).eqTrans (qmul_associative _ _ _).eqSymm

theorem harmonic_argument_step (z B j : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qadd (harmonicArgument z B j) (localArgument j z B) ≐ harmonicArgument z B (succ j) := by
  let v := ofGaussian z (B*succ j)
  let next := harmonicArgument z B (succ j)
  have h := GaussianGammaExponentStep.harmonic_product_step qzero z B j hB
  have e : Γ ⊢[PRAAx] qsub qzero v ≐ localArgument j z B :=
    qzero_add _ (qnegative_canonical v)
  exact (qadd_congr h e.eqSymm).eqTrans ((GaussianRationalSumAlgebra.qadd_associative next v _).eqTrans
    ((qadd_congr (.eqRefl _) (GaussianNameRingLaws.additive_inverse_value v)).eqTrans
      (qadd_zero_right next (GaussianRationalHorner.qmul_canonical _ _))))

theorem local_argument_bound (i z R B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] bounded (localArgument i z B) R one := by
  let E := B*succ i
  have hi : Γ ⊢[PRAAx] le one (succ i) := zero_lt_succ i
  have hE := GaussianRationalHorner.positive_product _ _ hB hi
  have es : Γ ⊢[PRAAx] le (R*B) (R*E) :=
    le_congr (by ipra_ring) (by dsimp only [E]; ipra_ring) (mul_le_mul_right (R*B) hi)
  exact bounded_negative _ _ _ (le_refl _)
    (GaussianGammaEulerHead.fraction_disk z R E hE (ComplexLogarithmRemainder.bounded_mono hz es))

theorem factor_bound (i z R B K : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] bounded (factor i z B K) ((one+R)*pw (num 3) R) one :=
  bound_congr (.eqRefl _) (.eqRefl _) (one_mul one) (bounded_product _ _ _ _ _ _
    (le_refl _) (le_refl _) (GaussianGammaEulerHead.factor_bound i z R B hB hz)
    (GaussianPositiveExponentialMajorant.disk_bound _ _ _ (local_argument_bound i z R B hB hz)))

theorem harmonic_argument_bound (z R B j : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] bounded (harmonicArgument z B j) (j*R) one := by
  let h := harmonicPoint j
  have neg := bounded_negative (Γ := Γ) h j one (le_refl _) (GaussianGammaCanonicalExponentBound.harmonic_point_bound j)
  have d : Γ ⊢[PRAAx] qsub qzero h ≐ qnegative h := qzero_add _ (qnegative_canonical h)
  exact bound_congr (qmul_congr d.eqSymm (.eqRefl _)) (.eqRefl _) (one_mul one)
    (bounded_product _ _ _ _ _ _ (le_refl _) (le_refl _) neg (GaussianGammaEulerHead.fraction_disk z R B hB hz))

theorem harmonic_argument_zero (z B : PTm n) : Γ ⊢[PRAAx] harmonicArgument z B zero ≐ qzero := by
  let h := harmonicPoint (zero : PTm n)
  have positive := GaussianRationalL1.raw_den_positive (Γ := Γ) h
  have hn := GaussianRationalMetric.bounded_zero_norm h _ _ one positive (le_refl _)
    (GaussianRationalL1.raw_represents h) (GaussianGammaCanonicalExponentBound.harmonic_point_bound zero)
  have eq := GaussianRationalFiniteRoots.canonical_zero_of_norm_zero h
    (RationalGaussianEmbedding.embed_canonical _) hn
  have inverseZero : Γ ⊢[PRAAx] qsub qzero h ≐ qzero :=
    (qsub_congr (.eqRefl _) eq).eqTrans (GaussianCoefficientNormOrder.qsub_self _)
  exact (qmul_congr inverseZero (.eqRefl _)).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_left _)

theorem folded_zero (z B K : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] foldedPrefix z B K zero ≐ ofGaussian z B :=
  (qmul_congr (GaussianGammaEulerHead.head_zero z B hB)
    ((GaussianRationalFiniteSum.sum_index_congr _ (.eqRefl _) (harmonic_argument_zero z B)).eqTrans
      (GaussianGammaCanonicalTailExponential.scalar_zero_point K))).eqTrans
    (qmul_one_right _ (GaussianRationalHorner.ofGaussian_canonical _ _ hB))

theorem scaled_distance (t u v A M D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (ht : Γ ⊢[PRAAx] bounded t M one) (hd : Γ ⊢[PRAAx] distanceBounded u v A D) :
    Γ ⊢[PRAAx] distanceBounded (qmul t u) (qmul t v) (M*A) D :=
  bound_congr (GaussianRationalRoundedPower.multiplication_difference t u v).eqSymm (.eqRefl _) (one_mul D)
    (bounded_product _ _ _ _ _ _ (le_refl _) hD ht hd)

def width (R N : PTm n) : PTm n := one+R+N*R

def amplitude (R : PTm n) : PTm n := (one+R)*pw (num 3) R

def errorBudget (R j : PTm n) : PTm n := R*j*pw (amplitude R) j

@[simp] theorem subst_width {m : ℕ} (σ : Fin n → PTm m) (R N : PTm n) :
    Syn.subst σ (width R N) = width (Syn.subst σ R) (Syn.subst σ N) := by simp [width]

@[simp] theorem subst_errorBudget {m : ℕ} (σ : Fin n → PTm m) (R j : PTm n) :
    Syn.subst σ (errorBudget R j) = errorBudget (Syn.subst σ R) (Syn.subst σ j) := by simp [errorBudget,amplitude]

theorem folded_step_distance (z R B N j p : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) (hj : Γ ⊢[PRAAx] le j N) :
    Γ ⊢[PRAAx] distanceBounded
      (qmul (foldedPrefix z B (rectangleCutoff (width R N) p) j) (factor j z B (rectangleCutoff (width R N) p)))
      (foldedPrefix z B (rectangleCutoff (width R N) p) (succ j))
      (R*pw (one+R) (succ j)) (unit p) := by
  let C := width R N
  let K := rectangleCutoff C p
  let u := harmonicArgument z B j
  let v := localArgument j z B
  let H := GaussianGammaEulerHead.head z B (succ j)
  let L := GaussianGammaEulerHead.factor j z B
  let steps := qmul (scalarSum u K) (scalarSum v K)
  have hc : Γ ⊢[PRAAx] le one C := by
    dsimp [C,width]
    exact le_trans (le_add_right _ _) (le_add_right _ _)
  have hr : Γ ⊢[PRAAx] le R C := by
    dsimp [C,width]
    exact le_trans (le_congr (.eqRefl _) (add_comm _ _) (le_add_right R one)) (le_add_right _ _)
  have hu' : Γ ⊢[PRAAx] le (j*R) C := le_trans (mul_le_mul_right R hj) (by
    dsimp [C,width]
    exact le_congr (.eqRefl _) (add_comm _ _) (le_add_right _ _))
  have hu := GaussianCoefficientNameBounds.bounded_radius_mono u (j*R) one C one
    (le_refl _) (le_refl _) (le_congr (by ipra_ring) (by ipra_ring) hu') (harmonic_argument_bound z R B j hB hz)
  have hv := GaussianCoefficientNameBounds.bounded_radius_mono v R one C one
    (le_refl _) (le_refl _) (le_congr (by ipra_ring) (by ipra_ring) hr) (local_argument_bound j z R B hB hz)
  have small := actual_scalar_product_dyadic u v C p hc hu hv
  have small' := scaled_distance H steps _ one (R*pw (one+R) (succ j)) (unit p) (unit_positive _)
    (GaussianGammaEulerHead.prefix_bound z R B (succ j) hB hz) small
  have left : Γ ⊢[PRAAx] qmul (foldedPrefix z B K j) (factor j z B K) ≐ qmul H steps :=
    (qmul_shuffle (GaussianGammaEulerHead.head z B j) (scalarSum u K) L (scalarSum v K)).eqTrans
      (qmul_congr (GaussianGammaEulerHead.head_succ z B j).eqSymm (.eqRefl _))
  have right : Γ ⊢[PRAAx] qmul H (scalarSum (qadd u v) K) ≐ foldedPrefix z B K (succ j) :=
    qmul_congr (.eqRefl _) (GaussianRationalFiniteSum.sum_index_congr _ (.eqRefl _) (harmonic_argument_step z B j hB))
  exact distance_congr left.eqSymm right (by ipra_ring) (.eqRefl _) small'

theorem budget_step (R j : PTm n) : Γ ⊢[PRAAx]
    le (amplitude R*errorBudget R j+R*pw (one+R) (succ j)) (errorBudget R (succ j)) := by
  have h : Γ ⊢[PRAAx] le (one+R) (amplitude R) := by
    have h0 := LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl (Γ := Γ) (one+R))
      (GaussianFactorBudget.power_positive (num 3) R (zero_lt_succ two))
    exact le_congr (by ipra_ring) (.eqRefl _) h0
  have shift := LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl R) (pw_le_pw (succ j) h)
  have added := add_le_add_right (amplitude R*errorBudget R j) shift
  apply le_congr (add_comm _ _) ?_ added
  have ep := natEq (pw_succ (Γ := Γ) (amplitude R) j)
  apply deriveNat
  unfold errorBudget
  ipra_simps
  rw [ep]
  ring

def prefixComparison (z R B N p j : PTm n) : Fm PTm n :=
  le j N ⟶ distanceBounded (literalPrefix z B (rectangleCutoff (width R N) p) j)
    (foldedPrefix z B (rectangleCutoff (width R N) p) j) (errorBudget R j) (unit p)

@[simp] theorem subst_prefixComparison {m : ℕ} (σ : Fin n → PTm m) (z R B N p j : PTm n) :
    (prefixComparison z R B N p j).subst σ = prefixComparison (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ p) (Syn.subst σ j) := by
  simp [prefixComparison,rectangleCutoff,GaussianScalarExponentialProductTail.reserve,GaussianScalarExponentialProductTail.growthExponent,unit]

theorem prefix_comparison_zero (z R B N p : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] prefixComparison z R B N p zero := by
  apply Prf.impI
  exact distance_congr (literal_zero z B _ hB.wk).eqSymm (folded_zero z B _ hB.wk).eqSymm
    (by unfold errorBudget; ipra_ring) (.eqRefl _) (GaussianRationalPowerDifference.distance_refl_zero _ _ (unit_positive _))

theorem prefix_comparison_step (z R B N p j : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (ih : Γ ⊢[PRAAx] prefixComparison z R B N p j) : Γ ⊢[PRAAx] prefixComparison z R B N p (succ j) := by
  let K := rectangleCutoff (width R N) p
  let x := literalPrefix z B K j
  let y := foldedPrefix z B K j
  let t := factor j z B K
  apply Prf.impI
  have hj : (le (succ j) N) :: Γ ⊢[PRAAx] le j N := le_trans (le_succ_self _) Prf.hyp0
  have dx := scaled_distance t x y (errorBudget R j) (amplitude R) (unit p) (unit_positive _)
    (factor_bound j z R B K hB.wk hz.wk) (.impE ih.wk hj)
  have part : (le (succ j) N) :: Γ ⊢[PRAAx] distanceBounded (literalPrefix z B K (succ j))
      (qmul y t) (amplitude R*errorBudget R j) (unit p) :=
    distance_congr ((qmul_commutative t x).eqTrans (literal_step z B K j).eqSymm) (qmul_commutative t y)
      (.eqRefl _) (.eqRefl _) dx
  have last := folded_step_distance z R B N j p hB.wk hz.wk hj
  have all := distance_triangle_same _ _ _ _ _ _ (unit_positive p) part last
  exact distance_radius_mono _ _ _ _ _ _ (unit_positive p) (unit_positive p)
    (mul_le_mul_right (unit p) (budget_step R j)) all

theorem prefix_comparison (z R B N p j : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) (hj : Γ ⊢[PRAAx] le j N) :
    Γ ⊢[PRAAx] distanceBounded (literalPrefix z B (rectangleCutoff (width R N) p) j)
      (foldedPrefix z B (rectangleCutoff (width R N) p) j) (errorBudget R j) (unit p) := by
  have hB' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have hz' : Γ.map Fm.shift ⊢[PRAAx] ComplexLogarithmRemainder.bounded (Syn.shift z) (Syn.shift R*Syn.shift B) := by
    simpa [Fm.shift,Syn.shift] using hz.shift
  have all : Γ ⊢[PRAAx] .all (prefixComparison (Syn.shift z) (Syn.shift R) (Syn.shift B)
      (Syn.shift N) (Syn.shift p) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,le_QF _ _⟩ ?_ ?_
    · simp only [subst_prefixComparison,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact prefix_comparison_zero z R B N p hB
    · simp only [subst_prefixComparison,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact prefix_comparison_step _ _ _ _ _ _ hB'.wk hz'.wk Prf.hyp0
  have rule : Γ ⊢[PRAAx] prefixComparison z R B N p j := by
    simpa only [subst_prefixComparison,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE rule hj

theorem original_literal_weierstrass_finite_comparison_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 2) ⟶ ComplexLogarithmRemainder.bounded (var 0) (var 1*var 2) ⟶
      prefixComparison (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (prefix_comparison _ _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem original_literal_factor_prefix_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (literalPrefix (var 0) (var 1) (var 2) (succ (var 3)) ≐
      qmul (literalPrefix (var 0) (var 1) (var 2) (var 3)) (factor (var 3) (var 0) (var 1) (var 2))) :=
  closeUniv 4 (literal_step _ _ _ _)

theorem original_literal_harmonic_argument_step_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ qadd (harmonicArgument (var 0) (var 1) (var 2)) (localArgument (var 2) (var 0) (var 1))
      ≐ harmonicArgument (var 0) (var 1) (succ (var 2))) :=
  closeUniv 3 (.impI (harmonic_argument_step _ _ _ Prf.hyp0))

theorem original_literal_weierstrass_factor_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 3) ⟶ ComplexLogarithmRemainder.bounded (var 1) (var 2*var 3) ⟶
      bounded (factor (var 0) (var 1) (var 3) (var 4)) ((one+var 2)*pw (num 3) (var 2)) one) :=
  closeUniv 5 (.impI (.impI (factor_bound _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaWeierstrassFactors
