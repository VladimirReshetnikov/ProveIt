import IPRADerivations.Analysis.Barnes.FunctionalEquations.Glaisher.GaussianBarnesGlaisherFinite
import IPRADerivations.Analysis.Barnes.FunctionalEquations.IntegerValues.BarnesInteger
import IPRADerivations.Analysis.Beta.Endpoints.Upper.GaussianBetaUpperPowerCancellation
import IPRADerivations.Analysis.Euler.HarmonicLogarithms.GaussianHarmonicLogarithmPower

/-!
# The finite weighted logarithm is the logarithm of the actual hyperfactorial

A finite bound relates the original named weighted prefix to the original
harmonic logarithm of the encoded integer product. The induction is on
actual rational observations, with an explicit dyadic allowance.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesGlaisherHyperfactorial

open_ipra
open BarnesInteger (hyp hyp_zero hyp_succ hyp_pos)
open GaussianBarnesGlaisherFinite (sumData regular_rows sum_regular weightedF weighted_regular weightedData)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_regular constant_at)
open GaussianNameArithmetic (sum_distance)
open GaussianNameRingLaws
  (equivalent_of_envelope add_sample_error product_right_error)
open GaussianNameEquivalence (crossEquivalent)
open GaussianPositiveRationalLogarithm (baseF)
open GaussianRationalHorner (qadd qmul qzero canonical positive_product)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono distance_triangle_same)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalNaturalScale (natScale naturalPoint natScale_as_product)
open GaussianRationalSyntheticDivision (qsub_congr qmul_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "H" => GaussianHarmonicLogarithmName.sample
local notation "S" => GaussianBarnesGlaisherFinite.sumF

theorem hyp_positive (N : PTm n) : Γ ⊢[PRAAx] le one (hyp N) :=
  Order.zero_lt_of_eq_succ (hyp_pos N)

private theorem harmonic_congr {p a b c d : PTm n} (ha : Γ ⊢[PRAAx] a ≐ c)
    (hb : Γ ⊢[PRAAx] b ≐ d) : Γ ⊢[PRAAx] H p a b ≐ H p c d := by
  ipra_congr (H (var 0) (var 1) (var 2) : PTm 3) with [(.eqRefl p),ha,hb]

theorem harmonic_integer_readback (p a : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] H p a one ≐ ap2 baseF (GaussianHarmonicLogarithmName.clock p) a := by
  let s := GaussianHarmonicLogarithmName.clock p
  let Q := GammaEulerConstantName.mesh s
  have e := GaussianPositiveRationalLogarithmProperness.original_finite_difference a one Q ha (le_refl one)
  have aRead := GaussianGammaFiniteApproximantName.log_sample_at (Γ := Γ) s a
  have oneRead := GaussianGammaFiniteApproximantName.log_sample_at (Γ := Γ) s one
  have hc : Γ ⊢[PRAAx] canonical (ap2 baseF s a) :=
    GaussianRationalHorner.canonical_congr aRead (RationalGaussianEmbedding.embed_canonical _)
  have d := (qsub_congr aRead oneRead).eqTrans e
  have z := (qsub_congr (.eqRefl (ap2 baseF s a)) (GaussianBetaUpperPowerCancellation.integer_log_at_one s)).eqTrans
    (GaussianRationalReconstruction.qsub_zero_right _ hc)
  exact (GaussianHarmonicLogarithmName.sample_at p a one).eqTrans (d.eqSymm.eqTrans z)

theorem harmonic_integer_error (p a : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] distanceBounded (H p a one) (ap2 baseF p a) two (unit p) := by
  let s := GaussianHarmonicLogarithmName.clock p
  have hs : Γ ⊢[PRAAx] le (unit p) (unit s) :=
    GaussianExponentialReference.unit_monotone (le_add_right p (num 9))
  have e := GaussianNameEquivalence.point_at baseF a s p (GaussianGammaFiniteApproximantName.log_regular a ha)
  have r : Γ ⊢[PRAAx] le ((unit s+unit p)*unit p) (two*(unit s*unit p)) := by
    ipra_le 𝔞(unit p)*sl hs
  exact distance_congr (harmonic_integer_readback p a ha).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive s) (unit_positive p)) (unit_positive p) r e)

theorem weighted_row_error (p j : PTm n) (hj : Γ ⊢[PRAAx] le one j) :
    Γ ⊢[PRAAx] distanceBounded (H p (pw j j) one) (ap2 weightedF p (weightedData (naturalPoint j) j))
      (num 6*j) (unit p) := by
  let a := naturalPoint j
  let b := ap2 baseF p j
  let g := H p j one
  have hU := unit_positive (Γ := Γ) p
  have first := GaussianHarmonicLogarithmPower.finite_sample_error p j one j (.andI hj (le_refl one))
  have powerOne := harmonic_congr (Γ := Γ) (p := p) (Prf.eqRefl (pw j j))
    (GaussianPolynomialPerturbation.one_power j)
  have shift := distance_congr powerOne (natScale_as_product j g) (.eqRefl _) (.eqRefl _) first
  have hG := GaussianHarmonicLogarithmName.name_regular j one (.andI hj (le_refl one))
  have scaled := product_right_error a g b two (unit p)
    (GaussianNameBounds.U GaussianHarmonicLogarithmName.nameF (GaussianHarmonicLogarithmName.data j one)) j
    hU (harmonic_integer_error p j hj)
    (GaussianNameBounds.sample_bound _ _ _ hG) (GaussianNamedNaturalScale.natural_point_bound j)
  let L := GaussianNameArithmetic.multiplyModulus constantF baseF a j
  let s := GaussianFastValueCut.exponent L p
  let v := ap2 baseF s j
  have lag : Γ ⊢[PRAAx] le (unit p) (unit s) :=
    GaussianExponentialReference.unit_monotone (le_add_right p (GaussianFastValueCut.normalizer L))
  have hp := GaussianGammaFiniteApproximantName.log_regular j hj
  have clockErr : Γ ⊢[PRAAx] distanceBounded b v two (unit p) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hU (unit_positive s)) hU
      (by ipra_le 𝔞(unit p)*sl lag) (GaussianNameEquivalence.point_at baseF j p s hp)
  have endErr := product_right_error a b v two (unit p) (GaussianNameBounds.U baseF j) j hU clockErr
    (GaussianNameBounds.sample_bound _ _ _ hp) (GaussianNamedNaturalScale.natural_point_bound j)
  have eq := (GaussianNameArithmetic.multiply_at (Γ := Γ) constantF baseF a j p).eqTrans
    ((GaussianNameArithmetic.recode_congr (qmul_congr (constant_at s a) (.eqRefl v))).eqTrans
      (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qmul_canonical _ _)))
  exact distance_congr (.eqRefl _) eq.eqSymm (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hU (distance_triangle_same _ _ _ _ _ _ hU shift scaled) endErr)

def estimate (p N : PTm n) : Fm PTm n :=
  distanceBounded (ap2 S p (sumData N)) (H p (hyp N) one) (num 20*N*N) (unit p)

@[simp] theorem subst_estimate {m : ℕ} (σ : Fin n → PTm m) (p N : PTm n) :
    (estimate p N).subst σ = estimate (Syn.subst σ p) (Syn.subst σ N) := by
  simp [estimate,GaussianBarnesGlaisherFinite.sumData]

private theorem estimate_zero (p : PTm n) : Γ ⊢[PRAAx] estimate p zero := by
  let f := GaussianBarnesGlaisherFinite.weightedF
  let t := GaussianBarnesGlaisherFinite.body
  let k := GaussianFastValueCut.exponent zero p
  have near := GaussianNamedFiniteSumFamily.sample_at (Γ := Γ) f t p zero zero
  have val := GaussianRationalFiniteSum.sum_zero (Γ := Γ) (GaussianNamedFiniteSumFamily.body f t) (pairT k zero)
  have left := near.eqTrans val
  have right := (harmonic_congr (Γ := Γ) (p := p) hyp_zero (.eqRefl one)).eqTrans
    ((harmonic_integer_readback p one (le_refl one)).eqTrans (GaussianBetaUpperPowerCancellation.integer_log_at_one _))
  exact distance_congr left.eqSymm right.eqSymm (by ipra_ring) (.eqRefl _)
    (GaussianRationalPowerDifference.distance_refl_zero qzero (unit p) (unit_positive p))

private theorem estimate_succ (p N : PTm n) (ih : Γ ⊢[PRAAx] estimate p N) :
    Γ ⊢[PRAAx] estimate p (succ N) := by
  let j := succ N
  let f := weightedF
  let r := weightedData (naturalPoint j) j
  let u := ap2 S p (sumData N)
  let v := ap2 f p r
  let x := H p (hyp N) one
  let y := H p (pw j j) one
  have hU := unit_positive (Γ := Γ) p
  have hj : Γ ⊢[PRAAx] le one j := zero_lt_succ _
  have append := GaussianNamedFiniteSumFamilySplit.append_sample (Γ := Γ) f GaussianBarnesGlaisherFinite.body p N zero
    (regular_rows j zero)
  rw [GaussianBarnesGlaisherFinite.body_at] at append
  have toSum := distance_triangle_same _ _ _ _ _ _ hU append
    (add_sample_error S f (sumData N) r p (sum_regular N) (weighted_regular _ _ hj))
  have cmp := sum_distance u x v y (num 20*N*N) (num 6*j) (unit p) hU ih
    (distance_symmetric _ _ _ _ hU (weighted_row_error p j hj))
  have target := GaussianHarmonicLogarithmProduct.finite_samples p (hyp N) one (pw j j) one
    (.andI (.andI (hyp_positive N) (le_refl one))
      (.andI (GaussianPolynomialPerturbation.power_positive j j hj) (le_refl one)))
  have toProduct := distance_congr (harmonic_congr (hyp_succ (Γ := Γ) N).eqSymm (one_mul one)) (.eqRefl _)
    (.eqRefl _) (.eqRefl _) target
  have total := distance_triangle_same _ _ _ _ _ _ hU (distance_triangle_same _ _ _ _ _ _ hU toSum cmp)
    (distance_symmetric _ _ _ _ hU toProduct)
  refine distance_radius_mono _ _ _ _ _ _ hU hU ?_ total
  apply le_of_eq_add (d := (num 34*N+two)*unit p)
  unfold GaussianNameRingLaws.three j
  ipra_ring

theorem finite_estimate (p N : PTm n) : Γ ⊢[PRAAx] estimate p N := by
  have all : Γ ⊢[PRAAx] .all (estimate (Syn.shift p) (var 0)) := by
    refine PRA.qfInd _ (by simp [estimate,distanceBounded,GaussianRationalMetric.bounded,RationalArgmin.rationalLE,le_QF]) ?_ ?_
    · simpa only [subst_estimate,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using estimate_zero (Γ := Γ) p
    · simp only [subst_estimate,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact estimate_succ (Syn.shift p) (var 0) Prf.hyp0
  simpa only [subst_estimate,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

theorem prefix_hyperfactorial_logarithm (N : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent S baseF (sumData N) (hyp N) := by
  apply equivalent_of_envelope S baseF (sumData N) (hyp N) (num 20*N*N+two)
    (sum_regular N) (GaussianGammaFiniteApproximantName.log_regular _ (hyp_positive N))
  refine .allI ?_
  let sh (v : PTm n) := Syn.shift v
  simpa [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,sh,GaussianBarnesGlaisherFinite.sumData] using
    distance_triangle_same _ _ _ _ _ _ (unit_positive (var 0))
      (finite_estimate (Γ := Γ.map Fm.shift) (var 0) (sh N))
      (harmonic_integer_error (var 0) (hyp (sh N)) (hyp_positive (sh N)))

theorem actual_weighted_logarithm_is_hyperfactorial_logarithm_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 (crossEquivalent S baseF (sumData (var 0)) (hyp (var 0))) :=
  closeUniv 1 (prefix_hyperfactorial_logarithm _)

end LeanProofs.IPRA.Analysis.GaussianBarnesGlaisherHyperfactorial
