import IPRADerivations.Analysis.Stirling.Binet.Kernel.BaselNormalization.GaussianBinetBaselName
import IPRADerivations.Analysis.Stirling.Binet.Kernel.GaussianBinetKernelCofinal
import IPRADerivations.Analysis.Integration.CompactGrids.Splits.GaussianCompactZeroWidth
import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianRationalCoefficientScaling

/-!
# Exact value of the cofinal Binet kernel at zero

At a common π clock the zero row has a shared factor `1/(2π²)`
times a literal reciprocal square. The finite Basel comparison cancels
this factor quantitatively and identifies the cofinal endpoint `1/12`.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianBinetKernelZero

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBinetBaselBinding (literalSum subst_literalSum)
open GaussianBinetBaselName (minimumCutoff finite_vs_named_pi)
open GaussianBinetKernelPi (sample_fraction sample_margins denominator_positive)
open GaussianBinetKernelRows (inputData rowF rowBody rowData row_at row_sample nativeNum nativeDen weight value value_fraction)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (exponent)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNameRingLaws (equivalent_of_envelope)
open GaussianNamedFiniteSumFamily (finite)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same distance_radius_mono_den)
open GaussianRationalHorner (qzero qmul qadd positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalSyntheticDivision (qmul_congr qadd_congr qmul_zero_right)
open GaussianStirlingConstant (piNumerator piDenominator)
open GaussianStirlingOddCoefficients (fraction_embed fraction_equal fraction_product)
open RationalGaussianEmbedding (embed embedF embed_at embed_add)
open RationalReciprocalPowerTail (reciprocalPower tail tail_succ tail_zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "P" => GaussianBinetKernelPi.sample
local notation "cofinalF" => GaussianBinetKernelCofinal.nameF
local notation "finiteF" => GaussianBinetKernelTail.finiteF
local notation "finiteData" => GaussianBinetKernelTail.finiteData

def factor (p : PTm n) : PTm n := fraction (piDenominator p*piDenominator p) (two*(piNumerator p*piNumerator p))
def sixthFactor (p : PTm n) : PTm n := fraction (piDenominator p*piDenominator p) (num 12*(piNumerator p*piNumerator p))
def endpoint : PTm n := fraction one (num 12)

private theorem pi_num_positive (p : PTm n) : Γ ⊢[PRAAx] le one (piNumerator p) :=
  le_trans (positive_product _ _ (le_succ_self one) (denominator_positive p)) (sample_margins p).andE₁

private theorem embed_congr {x y : PTm n} (e : Γ ⊢[PRAAx] x ≐ y) : Γ ⊢[PRAAx] embed x ≐ embed y :=
  (embed_at x).eqSymm.eqTrans ((congrAp1 embedF e).eqTrans (embed_at y))

private theorem factor_positive_denom (p : PTm n) : Γ ⊢[PRAAx] le one (two*(piNumerator p*piNumerator p)) := by
  have h := pi_num_positive (Γ := Γ) p
  exact positive_product _ _ (le_succ_self one) (positive_product _ _ h h)

private theorem sixth_positive_denom (p : PTm n) : Γ ⊢[PRAAx] le one (num 12*(piNumerator p*piNumerator p)) := by
  have h := pi_num_positive (Γ := Γ) p
  exact positive_product _ _ (by ipra_le 11) (positive_product _ _ h h)

theorem zero_value (p i B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hi : Γ ⊢[PRAAx] le one i) : Γ ⊢[PRAAx]
    value p i zero B ≐ qmul (factor p) (fraction one (i*i)) := by
  let u := piNumerator p
  let v := piDenominator p
  have hu := pi_num_positive (Γ := Γ) p
  have hii := positive_product _ _ hi hi
  have hvv := positive_product _ _ hu hu
  have hw : Γ ⊢[PRAAx] le one (weight i) := positive_product _ _ (by ipra_le 3) hii
  have hA : Γ ⊢[PRAAx] le one (nativeNum zero B i u v) :=
    le_congr (.eqRefl _) (by unfold nativeNum; ipra_ring)
      (positive_product _ _ (positive_product _ _ hw hvv) (positive_product _ _ hB hB))
  have hc := factor_positive_denom (Γ := Γ) p
  have hd := positive_product _ _ hc hii
  have seq := fraction_product (v*v) (two*(u*u)) one (i*i) hc hii
  refine (value_fraction p i zero B hB hi).eqTrans ((fraction_equal _ _ _ _ hA hd ?_).eqTrans seq.eqSymm)
  unfold nativeNum nativeDen weight
  ipra_ring

private theorem literal_succ (i : PTm n) : Γ ⊢[PRAAx]
    literalSum (succ i) ≐ qadd (literalSum i) (fraction one (succ i*succ i)) := by
  let k := succ i
  have hk : Γ ⊢[PRAAx] le one k := zero_lt_succ _
  have sq : Γ ⊢[PRAAx] pw k two ≐ k*k := (pw_succ k one).eqTrans (congrMul (pw_one k) (.eqRefl _))
  have e : Γ ⊢[PRAAx] reciprocalPower two (succ (zero+i)) ≐ GaussianEuclideanDistanceName.fraction one (k*k) :=
    (RationalReciprocalPowerTail.reciprocal_congr (.eqRefl _) (congrSucc (zero_add i))).eqTrans
      (RationalNonnegativePowers.fraction_congr (.eqRefl _) sq)
  exact (embed_congr (tail_succ two zero i)).eqTrans ((embed_add _ _).eqTrans
    (qadd_congr (.eqRefl _) ((embed_congr e).eqTrans (fraction_embed one (k*k) (positive_product _ _ hk hk)))))

private def rowIdentity (p B c : PTm n) : Fm PTm n := .all
  (ap2 rowF (Syn.shift p) (rowData (var 0) zero (Syn.shift B)) ≐ qmul (Syn.shift c) (fraction one (succ (var 0)*succ (var 0))))

@[simp] private theorem subst_rowIdentity {l : ℕ} (σ : Fin n → PTm l) (p B c : PTm n) :
    (rowIdentity p B c).subst σ = rowIdentity (Syn.subst σ p) (Syn.subst σ B) (Syn.subst σ c) := by
  simp [rowIdentity, Syn.subst_shift, Syn.shift_subst, one]

private theorem row_identity (p i B c : PTm n) (h : Γ ⊢[PRAAx] rowIdentity p B c) : Γ ⊢[PRAAx]
    ap2 rowF p (rowData i zero B) ≐ qmul c (fraction one (succ i*succ i)) := by
  simpa [rowIdentity,one] using h.allE i

private def sumLaw (p N B c : PTm n) : Fm PTm n :=
  finite rowF rowBody p N (inputData zero B) ≐ qmul c (literalSum N)

@[simp] private theorem subst_sumLaw {l : ℕ} (σ : Fin n → PTm l) (p N B c : PTm n) :
    (sumLaw p N B c).subst σ = sumLaw (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ B) (Syn.subst σ c) := by
  simp [sumLaw,finite]

private theorem sum_law_zero (p B c : PTm n) : Γ ⊢[PRAAx] sumLaw p zero B c := by
  have y := (embed_congr (tail_zero (Γ := Γ) two zero)).eqTrans
    ((fraction_embed zero one (le_refl one)).eqTrans (GaussianCompactZeroWidth.zero_fraction one (le_refl one)))
  exact (GaussianRationalFiniteSum.sum_zero _ _).eqTrans
    (((qmul_congr (.eqRefl c) y).eqTrans (qmul_zero_right c)).eqSymm)

private theorem sum_law_step (p i B c : PTm n) (h : Γ ⊢[PRAAx] rowIdentity p B c)
    (ih : Γ ⊢[PRAAx] sumLaw p i B c) : Γ ⊢[PRAAx] sumLaw p (succ i) B c := by
  let k := succ i
  have row := (congrAp2 rowF (.eqRefl p) (row_at (Γ := Γ) i zero B)).eqTrans (row_identity p i B c h)
  have sum := GaussianNamedFiniteSumFamilySplit.finite_append (Γ := Γ) rowF rowBody p i (inputData zero B)
  exact sum.eqTrans ((qadd_congr ih row).eqTrans
    ((GaussianRationalCoefficientScaling.qmul_add c (literalSum i) (fraction one (k*k))).eqSymm.eqTrans
      (qmul_congr (.eqRefl _) (literal_succ i).eqSymm)))

private theorem sum_law (p N B c : PTm n) (h : Γ ⊢[PRAAx] rowIdentity p B c) : Γ ⊢[PRAAx] sumLaw p N B c := by
  let s (x : PTm n) := Syn.shift x
  have all : Γ ⊢[PRAAx] .all (sumLaw (s p) (var 0) (s B) (s c)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [subst_sumLaw,s,Syn.subst_var,Syn.subst_inst_shift,Syn.inst_zero] using sum_law_zero p B c
    · have hs : Γ.map Fm.shift ⊢[PRAAx] rowIdentity (s p) (s B) (s c) := by
        simpa only [Fm.shift,Syn.shift,s,subst_rowIdentity] using h.shift
      simp only [subst_sumLaw,s,subst_repl_shift]
      exact sum_law_step (s p) (var 0) (s B) (s c) hs.wk Prf.hyp0
  simpa only [subst_sumLaw,s,Syn.subst_var,Syn.subst_inst_shift,Syn.inst_zero] using all.allE N

theorem finite_zero (p N B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    finite rowF rowBody p N (inputData zero B) ≐ qmul (factor p) (literalSum N) := by
  apply sum_law p N B (factor p)
  refine .allI ?_
  let s (x : PTm n) := Syn.shift x
  have hs : Γ.map Fm.shift ⊢[PRAAx] le one (s B) := by simpa [Fm.shift,Syn.shift,s] using hB.shift
  have shiftFactor : Syn.shift (factor p) = factor (s p) := by
    simp [factor,s,Syn.shift,piNumerator,piDenominator,GaussianGammaHalfPiName.clearing,GaussianGammaHalfPiName.meshAt,
      GaussianGammaHalfPiName.meshIndex,GaussianGammaHalfPiName.orderAt,GaussianGammaHalfPiName.orderIndex,WallisFinite.Dm,
      Products.fact,one,two]
  rw [shiftFactor]
  exact (row_sample (s p) (var 0) zero (s B)).eqTrans (zero_value (s p) (succ (var 0)) (s B) hs (zero_lt_succ _))

private theorem factor_six (p : PTm n) : Γ ⊢[PRAAx] qmul (sixthFactor p) (fraction (num 6) one) ≐ factor p := by
  let u := piNumerator p
  let v := piDenominator p
  let D := num 12*(u*u)
  have hD := sixth_positive_denom (Γ := Γ) p
  exact (fraction_product (v*v) D (num 6) one hD (le_refl one)).eqTrans
    (fraction_equal _ _ _ _ (positive_product _ _ hD (le_refl one)) (factor_positive_denom p)
      (by dsimp only [D]; ipra_ring))

private theorem factor_pi_square (p : PTm n) : Γ ⊢[PRAAx] qmul (sixthFactor p) (qmul (P p) (P p)) ≐ endpoint := by
  let u := piNumerator p
  let v := piDenominator p
  let D := num 12*(u*u)
  have hd := sixth_positive_denom (Γ := Γ) p
  have hv := denominator_positive (Γ := Γ) p
  have hvv := positive_product _ _ hv hv
  have pi := (qmul_congr (sample_fraction (Γ := Γ) p) (sample_fraction p)).eqTrans (fraction_product u v u v hv hv)
  exact (qmul_congr (.eqRefl _) pi).eqTrans ((fraction_product (v*v) D (u*u) (v*v) hd hvv).eqTrans
    (fraction_equal _ _ _ _ (positive_product _ _ hd hvv) (by ipra_le 11) (by dsimp only [D]; ipra_ring)))

private theorem sixth_bound (p : PTm n) : Γ ⊢[PRAAx] bounded (sixthFactor p) one one := by
  let u := piNumerator p
  let v := piDenominator p
  have h : Γ ⊢[PRAAx] le v (two*v) := le_congr (.eqRefl _) (by ipra_ring) (le_add_right v v)
  have hu := le_trans h (sample_margins (Γ := Γ) p).andE₁
  have huv := le_mul_mono hu hu
  have hu12 : Γ ⊢[PRAAx] le (u*u) (one*(num 12*(u*u))) := by
    ipra_le 11*Groth.ι (Q.mk Γ u)^2
  exact GaussianEulerExponentCompactBounds.fraction_bound _ _ one (sixth_positive_denom p) (le_trans huv hu12)

theorem late_zero_distance (p M B : PTm n) (hM : Γ ⊢[PRAAx] le (minimumCutoff p) M)
    (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    distanceBounded (finite rowF rowBody p M (inputData zero B)) endpoint (num 10) (unit p) := by
  let c := sixthFactor p
  let x := literalSum M
  have base := finite_vs_named_pi p M hM
  have scaled := GaussianApproximateInverseDistance.multiply_distance c _ _ one (num 10) (unit p)
    (unit_positive p) (sixth_bound p) base
  have exactSum : Γ ⊢[PRAAx] qmul c (qmul (fraction (num 6) one) x) ≐ finite rowF rowBody p M (inputData zero B) :=
    (GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans
      ((qmul_congr (factor_six p) (.eqRefl _)).eqTrans (finite_zero p M B hB).eqSymm)
  exact distance_congr exactSum (factor_pi_square p) (one_mul _) (.eqRefl _) scaled

theorem observations (p B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    distanceBounded (ap2 cofinalF p (inputData zero B)) endpoint (num 11) (unit p) := by
  let N := GaussianBinetKernelCofinal.cutoff p
  let U := unit p
  let k := exponent N (succ p)
  let r := minimumCutoff k
  have hu := unit_positive (Γ := Γ) p
  have hN : Γ ⊢[PRAAx] le one N := hu
  have hd := positive_product _ _ GaussianBinetKernelTailMajorant.eight_positive hN
  have a := distance_symmetric _ _ _ _ hd (GaussianBinetKernelTail.finite_gap k N r zero B hN hB)
  have a' := distance_radius_mono _ _ _ _ one U hd hu
    (le_of_eq_add (d := num 7*U) (by dsimp only [N,U,GaussianBinetKernelCofinal.cutoff]; ipra_ring)) a
  have b := late_zero_distance k (N+r) B (le_add_left r N) hB
  have later : Γ ⊢[PRAAx] le p k := le_trans (le_succ_self p) (le_add_right (succ p) _)
  have b' := distance_radius_mono_den hu (GaussianExponentialReference.unit_monotone later) b
  have e := (GaussianBinetKernelCofinal.sample_at (Γ := Γ) p zero B).eqTrans
    (GaussianNamedFiniteSumFamily.sample_at rowF rowBody (succ p) N (inputData zero B))
  exact distance_congr e.eqSymm (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hu a' b')

theorem endpoint_equivalent (B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    crossEquivalent cofinalF constantF (inputData zero B) endpoint := by
  refine equivalent_of_envelope _ _ _ _ (num 11) (GaussianBinetKernelCofinal.regular zero B hB)
    (constant_regular endpoint) (.allI ?_)
  let b := Syn.shift B
  let p : PTm (n+1) := var 0
  have h : Γ.map Fm.shift ⊢[PRAAx] le one b := by simpa [Fm.shift,Syn.shift,b] using hB.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,GaussianBinetKernelRows.subst_inputData,
    Syn.shift,b,p,endpoint,GaussianPositiveRationalLogarithm.subst_fraction,PTm.subst_num,
    one,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ] using
    distance_congr (.eqRefl _) (constant_at p endpoint).eqSymm (.eqRefl _) (.eqRefl _) (observations p b h)

theorem actual_Binet_kernel_endpoint_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (var 0) ⟶ crossEquivalent cofinalF constantF (inputData zero (var 0)) endpoint) :=
  closeUniv 1 (.impI (endpoint_equivalent _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetKernelZero
