import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.Rational.Rates.GaussianGammaDigammaTwoShiftFiniteRate
import IPRADerivations.Analysis.Names.Order.GaussianNamedRealOrderEnvelope
import IPRADerivations.Analysis.LinearAlgebra.Determinants.GaussianDeterminantSignTransport

/-!
# Cofinal transfer to the original two-shift log quotient

Finite bounds with radius K/a and vanishing observation error give
exact independent-clock order between the named constants −K/a and K/a.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftCofinalRate

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaDigammaHarmonicCells (point_fraction_represents)
open GaussianGammaDigammaTwoShiftBinding
  (coefficient powerLogF powerLogData denominatorLogF denominatorLogData quotientLogF quotientLogData
    power_log_regular denominator_log_regular quotient_log_regular)
open GaussianGammaDigammaTwoShiftFiniteRate (raw)
open GaussianGammaDigammaTwoShiftSecants (logSample upper_negative negative_mul)
open GaussianHarmonicLogarithmName (sample)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNamedRealOrderEnvelope (envelope order_from_envelope)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same reversed_difference)
open GaussianRationalHorner (qadd qmul qzero positive_product scalar_congr ofGaussian_canonical)
open GaussianRationalMetric (qsub qnegative distanceBounded)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr qadd_sub_cancel qmul_zero_left)
open GaussianStirlingGammaLogarithm (source logGammaF logGammaData log_gamma_regular)
open GaussianStirlingGammaFractionalIncrementObservations (scalar_upper)
open RationalRepresentedUpper (left right to_signed from_signed)
open RationalValueBounds (upper upper_congr upper_mono upper_triangle upper_of_order)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "harmonicData" => GaussianHarmonicLogarithmName.data
local notation "H" => GaussianHarmonicLogarithmName.nameF

def rawSample (p a b c d : PTm n) : PTm n :=
  qsub (qsub (logSample p c b) (logSample p d b)) (qmul (coefficient b c d) (sample p a b))

def sampleCost (a b c d : PTm n) : PTm n :=
  GaussianNameArithmetic.multiplyModulus constantF H (coefficient b c d) (harmonicData a b)+num 10

ipra_subst rawSample [logSample, sample]

ipra_subst sampleCost

theorem raw_data_congr (p a b c d c' d' : PTm n) (ec : Γ ⊢[PRAAx] c ≐ c') (ed : Γ ⊢[PRAAx] d ≐ d') :
    Γ ⊢[PRAAx] rawSample p a b c d ≐ rawSample p a b c' d' := by
  have e := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (rawSample (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
    (σ := ![p,a,b,c,d]) (σ' := ![p,a,b,c',d']) (fun i => by
      fin_cases i <;> first | exact ec | exact ed | exact .eqRefl _)
  simpa only [subst_rawSample,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using e

private theorem coefficient_exact (b d r : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] GaussianGammaDigammaTwoShiftBinding.coefficient b (d+r) d ≐ fraction r b := by
  have ad := GaussianEulerPositivePowerChartCorrectedImage.fraction_sum d b r b hb hb
  have same := GaussianStirlingRationalTelescopers.fraction_same (d*b+r*b) (b*b) (d+r) b
    (GaussianRationalHorner.positive_product _ _ hb hb) hb (by ipra_ring)
  exact (qsub_congr (ad.eqTrans same).eqSymm (.eqRefl _)).eqTrans
    (qadd_sub_cancel _ _ (ofGaussian_canonical _ _ hb))

theorem raw_positive_coefficient (p a u b r : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] rawSample p a b (u+b+r) (u+b) ≐ raw p a u b r :=
  qsub_congr (.eqRefl _) (qmul_congr (coefficient_exact b (u+b) r hb) (.eqRefl _))

private theorem reversed_raw (p a b c d : PTm n) : Γ ⊢[PRAAx] qnegative (rawSample p a b c d) ≐ rawSample p a b d c := by
  let g := logSample p c b
  let h := logSample p d b
  let l := sample p a b
  let x := qsub g h
  let w := GaussianGammaDigammaTwoShiftBinding.coefficient b c d
  let v := GaussianGammaDigammaTwoShiftBinding.coefficient b d c
  let y := qmul w l
  have eX : Γ ⊢[PRAAx] qnegative x ≐ qsub h g := reversed_difference g h
  have eV : Γ ⊢[PRAAx] qnegative w ≐ v := reversed_difference (fraction c b) (fraction d b)
  have eY : Γ ⊢[PRAAx] qnegative y ≐ qmul v l :=
    (GaussianRationalMatrixFiniteSums.negative_as_minusOne (Γ := Γ) y).eqTrans
      ((qmul_congr (.eqRefl _) (qmul_commutative w l)).eqTrans
        ((GaussianRationalMatrixFiniteSums.negative_as_minusOne (qmul l w)).eqSymm.eqTrans
          ((negative_mul l w).eqTrans ((qmul_congr (.eqRefl _) eV).eqTrans (qmul_commutative _ _)))))
  have invol := GaussianDeterminantSignTransport.negative_involution (Γ := Γ) y (GaussianRationalHorner.qmul_canonical _ _)
  have swap : Γ ⊢[PRAAx] qsub (qnegative x) (qnegative y) ≐ qsub y x :=
    (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) invol).eqTrans (GaussianReciprocalHorner.qadd_commutative _ _)
  exact (reversed_difference x y).eqTrans (swap.eqSymm.eqTrans (qsub_congr eX eY))

private theorem same_raw (p a b c : PTm n) : Γ ⊢[PRAAx] rawSample p a b c c ≐ qzero := by
  have e := GaussianCoefficientNormOrder.qsub_self (Γ := Γ) (logSample p c b)
  have w := GaussianCoefficientNormOrder.qsub_self (Γ := Γ) (fraction c b)
  exact (qsub_congr e ((qmul_congr w (.eqRefl _)).eqTrans (qmul_zero_left _))).eqTrans
    (GaussianCoefficientNormOrder.qsub_self qzero)

/-- The scalar part lies between the two signed bounds with radius `A/D`. -/
abbrev symmetricUpper (q A D : PTm n) : Fm PTm n :=
  (upper (fstT qzero) (fstT q) A D) ⋏ upper (fstT q) (fstT qzero) A D

/-- Combine the two ordered window estimates and their respective error allowances. -/
theorem raw_bounds_from_ordered (p a b c d A T F G : PTm n) (hT : Γ ⊢[PRAAx] le one T)
    (forward : Γ ⊢[PRAAx] lt d c ⟶ symmetricUpper (rawSample p a b c d) (A+F*T) (T*unit p))
    (backward : Γ ⊢[PRAAx] lt c d ⟶ symmetricUpper (rawSample p a b d c) (A+G*T) (T*unit p)) :
    Γ ⊢[PRAAx] symmetricUpper (rawSample p a b c d) (A+(F+G)*T) (T*unit p) := by
  let K := A+(F+G)*T
  let D := T*unit p
  let r := rawSample p a b c d
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hT (unit_positive p)
  have fw : Γ ⊢[PRAAx] le (A+F*T) K := le_of_eq_add (d := G*T) (by unfold K; ipra_ring)
  have bw : Γ ⊢[PRAAx] le (A+G*T) K := le_of_eq_add (d := F*T) (by unfold K; ipra_ring)
  have widen {Δ : List (Fm PTm n)} {B : PTm n} (hD : Δ ⊢[PRAAx] le one D)
      (hB : Δ ⊢[PRAAx] le B K) (h : Δ ⊢[PRAAx] symmetricUpper r B D) :
      Δ ⊢[PRAAx] symmetricUpper r K D := by
    have bound := mul_le_mul_right D hB
    exact .andI (upper_mono _ _ _ _ _ _ hD h.andE₁ bound) (upper_mono _ _ _ _ _ _ hD h.andE₂ bound)
  have flip {Δ : List (Fm PTm n)} (h : Δ ⊢[PRAAx] symmetricUpper (rawSample p a b d c) (A+G*T) D) :
      Δ ⊢[PRAAx] symmetricUpper r (A+G*T) D := by
    have e := reversed_raw (Γ := Δ) p a b d c
    have nz : Δ ⊢[PRAAx] qnegative qzero ≐ qzero :=
      (GaussianRationalMatrixFiniteSums.negative_as_minusOne _).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_right _)
    exact .andI
      (upper_congr (congrFst nz) (congrFst e) (.eqRefl _) (.eqRefl _) (upper_negative _ _ _ _ h.andE₂))
      (upper_congr (congrFst e) (congrFst nz) (.eqRefl _) (.eqRefl _) (upper_negative _ _ _ _ h.andE₁))
  have coincident {Δ : List (Fm PTm n)} (e : Δ ⊢[PRAAx] c ≐ d) :
      Δ ⊢[PRAAx] symmetricUpper r K D := by
    have same := (raw_data_congr p a b c d d d e (.eqRefl _)).eqTrans (same_raw p a b d)
    have o := upper_of_order (Γ := Δ) (fstT (qzero : PTm n)) (fstT qzero) K D (le_refl _)
    exact .andI (upper_congr (.eqRefl _) (congrFst same.eqSymm) (.eqRefl _) (.eqRefl _) o)
      (upper_congr (congrFst same.eqSymm) (.eqRefl _) (.eqRefl _) (.eqRefl _) o)
  refine .orE (le_total c d) ?_ ?_
  · exact .orE (lt_or_eq_of_le Prf.hyp0)
      (widen hD.wk.wk bw.wk.wk (flip (Prf.impE backward.wk.wk Prf.hyp0)))
      (coincident Prf.hyp0)
  · exact .orE (lt_or_eq_of_le Prf.hyp0)
      (widen hD.wk.wk fw.wk.wk (Prf.impE forward.wk.wk Prf.hyp0))
      (coincident Prf.hyp0.eqSymm)

theorem quotient_sample_error (p a b c d : PTm n) (ha : Γ ⊢[PRAAx] source a b)
    (hc : Γ ⊢[PRAAx] source c b) (hD : Γ ⊢[PRAAx] source d b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 quotientLogF p (quotientLogData a b c d)) (rawSample p a b c d)
      (sampleCost a b c d) (unit p) := by
  let x := logGammaData c b
  let y := logGammaData d b
  let z := powerLogData a b c d
  let w := coefficient b c d
  let u := unit p
  have hU := unit_positive (Γ := Γ) p
  have hx := log_gamma_regular c b hc
  have hy := log_gamma_regular d b hD
  have hz := power_log_regular a b c d ha
  have hden := denominator_log_regular a b c d ha hD
  have pr := distance_congr (.eqRefl _) (qmul_congr (constant_at p w) (.eqRefl _)) (.eqRefl _) (.eqRefl _)
    (GaussianNameRingLaws.multiply_sample_error constantF H w (harmonicData a b) p (constant_regular w)
      (GaussianHarmonicLogarithmName.name_regular a b ha))
  have addErr := GaussianNameRingLaws.add_sample_error logGammaF powerLogF y z p hy hz
  have dy := GaussianRationalPowerDifference.distance_refl_zero (Γ := Γ) (ap2 logGammaF p y) u hU
  have href := GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ hU dy pr
  have hsum := distance_triangle_same _ _ _ _ _ u hU addErr href
  have dx := GaussianRationalPowerDifference.distance_refl_zero (Γ := Γ) (ap2 logGammaF p x) u hU
  have together := GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hU dx hsum
  have named := GaussianNamedDifference.sample_error logGammaF denominatorLogF x (denominatorLogData a b c d) p hx hden
  have arr := GaussianRationalInverseQuadraticAlgebra.subtract_sum (Γ := Γ) (logSample p c b) (logSample p d b)
    (qmul w (sample p a b))
  exact distance_congr (.eqRefl _) arr.eqSymm (by unfold sampleCost GaussianNameRingLaws.three; ipra_ring)
    (.eqRefl _) (distance_triangle_same _ _ _ _ _ _ hU named together)

def finiteRateWithDenominator (a b c d K D B : PTm n) : Fm PTm n := .all
  ((upper (fstT qzero) (fstT (rawSample (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift d)))
      (Syn.shift K*unit (var 0)+Syn.shift B*Syn.shift D) (Syn.shift D*unit (var 0))) ⋏
   (upper (fstT (rawSample (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift d))) (fstT qzero)
      (Syn.shift K*unit (var 0)+Syn.shift B*Syn.shift D) (Syn.shift D*unit (var 0))))

ipra_subst finiteRateWithDenominator [Syn.subst_shift, Syn.shift_subst]

private theorem finite_at (p a b c d K D B : PTm n) (h : Γ ⊢[PRAAx] finiteRateWithDenominator a b c d K D B) :
    Γ ⊢[PRAAx] (upper (fstT qzero) (fstT (rawSample p a b c d)) (K*unit p+B*D) (D*unit p) ⋏
      upper (fstT (rawSample p a b c d)) (fstT qzero) (K*unit p+B*D) (D*unit p)) := by
  simpa [finiteRateWithDenominator,Syn.subst_inst_shift,Syn.inst_zero] using h.allE p

private theorem zero_rep : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (qzero : PTm n)) (ZT.ofNat zero) one :=
  scalar_congr (RationalGaussianRealPart.real_zero (Γ := Γ)).eqSymm (.eqRefl _) (.eqRefl _)
    (RationalGaussianEmbedding.scalar_zero_represents one)

private theorem point_rep (z : PTm n) : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT z)
    (ComplexLogarithmRemainder.re (GaussianRationalL1.rawGaussian z)) (GaussianRationalL1.rawDen z) :=
  (GaussianRationalL1.raw_represents (Γ := Γ) z).andE₁

private theorem move_radius_right (z K a B p : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (h : Γ ⊢[PRAAx] upper (fstT z) (fstT qzero) (K*unit p+B*a) (a*unit p)) :
    Γ ⊢[PRAAx] upper (fstT z) (fstT (fraction K a)) B (unit p) := by
  let Z := ComplexLogarithmRemainder.re (GaussianRationalL1.rawGaussian z)
  let E := GaussianRationalL1.rawDen z
  let U := unit p
  let M := K*U+B*a
  let R := a*U
  have h' := to_signed _ _ Z (ZT.ofNat zero) E one M R (point_rep z) zero_rep h
  apply from_signed _ _ Z (ZT.ofNat K) E a B U (GaussianRationalL1.raw_den_positive z) ha
    (point_rep z) (point_fraction_represents K a ha)
  apply zle_of_toZ (PolynomialBisection.slack (left Z one R) (right (ZT.ofNat zero) E one M R))
  have eq := zle_toZ h'
  simp only [left,right,PolynomialBisection.slack,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat] at eq ⊢
  dsimp only [M,R] at eq ⊢
  simp only [Q.mk_mul,Q.mk_add,Q.mk_one,Q.mk_zero,map_mul,map_add,map_one,map_zero] at eq ⊢
  linear_combination eq

private theorem move_radius_left (z K a B p : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (h : Γ ⊢[PRAAx] upper (fstT qzero) (fstT z) (K*unit p+B*a) (a*unit p)) :
    Γ ⊢[PRAAx] upper (fstT (qnegative (fraction K a))) (fstT z) B (unit p) := by
  let Z := ComplexLogarithmRemainder.re (GaussianRationalL1.rawGaussian z)
  let E := GaussianRationalL1.rawDen z
  let U := unit p
  let M := K*U+B*a
  let R := a*U
  have h' := to_signed _ _ (ZT.ofNat zero) Z one E M R zero_rep (point_rep z) h
  have negRep : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (qnegative (fraction K a))) (-ZT.ofNat K) a :=
    scalar_congr (fst_pair _ _).eqSymm (.eqRefl _) (.eqRefl _)
      (RationalRepresentations.represents_negative _ _ _ (point_fraction_represents K a ha))
  apply from_signed _ _ (-ZT.ofNat K) Z a E B U ha (GaussianRationalL1.raw_den_positive z) negRep (point_rep z)
  apply zle_of_toZ (PolynomialBisection.slack (left (ZT.ofNat zero) E R) (right Z one E M R))
  have eq := zle_toZ h'
  simp only [left,right,PolynomialBisection.slack,ZT.toZ_neg,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat] at eq ⊢
  dsimp only [M,R] at eq ⊢
  simp only [Q.mk_mul,Q.mk_add,Q.mk_one,Q.mk_zero,map_mul,map_add,map_one,map_zero] at eq ⊢
  linear_combination eq

def logRateWithDenominator (a b c d K T : PTm n) : Fm PTm n :=
  realOrder constantF quotientLogF (qnegative (fraction K T)) (quotientLogData a b c d) ⋏
  realOrder quotientLogF constantF (quotientLogData a b c d) (fraction K T)

private theorem diagonal (p a b c d K T B : PTm n) (ha : Γ ⊢[PRAAx] source a b)
    (hc : Γ ⊢[PRAAx] source c b) (hd : Γ ⊢[PRAAx] source d b) (hT : Γ ⊢[PRAAx] le one T)
    (h : Γ ⊢[PRAAx] finiteRateWithDenominator a b c d K T B) :
    Γ ⊢[PRAAx]
      (upper (fstT (ap2 constantF p (qnegative (fraction K T))))
        (fstT (ap2 quotientLogF p (quotientLogData a b c d))) (B+sampleCost a b c d) (unit p) ⋏
       upper (fstT (ap2 quotientLogF p (quotientLogData a b c d)))
        (fstT (ap2 constantF p (fraction K T))) (B+sampleCost a b c d) (unit p)) := by
  let q := ap2 quotientLogF p (quotientLogData a b c d)
  let r := rawSample p a b c d
  let C := sampleCost a b c d
  let L := qnegative (fraction K T)
  let R := fraction K T
  let U := unit p
  have hp := unit_positive (Γ := Γ) p
  have e := quotient_sample_error p a b c d ha hc hd
  have base := finite_at p a b c d K T B h
  have lo := move_radius_left r K T B p hT base.andE₁
  have hi := move_radius_right r K T B p hT base.andE₂
  have eF := scalar_upper q r C U hp e
  have eR := scalar_upper r q C U hp (distance_symmetric _ _ _ _ hp e)
  refine .andI ?_ ?_
  · apply upper_congr (congrFst (constant_at p L).eqSymm) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    exact upper_mono _ _ _ _ _ _ (positive_product _ _ hp hp) (upper_triangle _ _ _ _ _ _ _ lo eR)
      (le_of_eq_add (d := zero) (by ipra_ring))
  · apply upper_congr (.eqRefl _) (congrFst (constant_at p R).eqSymm) (.eqRefl _) (.eqRefl _)
    exact upper_mono _ _ _ _ _ _ (positive_product _ _ hp hp) (upper_triangle _ _ _ _ _ _ _ eF hi)
      (le_of_eq_add (d := zero) (by ipra_ring))

/-- The limiting radius may have a denominator independent of the Gamma input. -/
theorem cofinal_rate_with_denominator (a b c d K T B : PTm n) (ha : Γ ⊢[PRAAx] source a b)
    (hc : Γ ⊢[PRAAx] source c b) (hd : Γ ⊢[PRAAx] source d b) (hT : Γ ⊢[PRAAx] le one T)
    (h : Γ ⊢[PRAAx] finiteRateWithDenominator a b c d K T B) : Γ ⊢[PRAAx] logRateWithDenominator a b c d K T := by
  let q := quotientLogData a b c d
  let L := qnegative (fraction K T)
  let R := fraction K T
  let E := B+sampleCost a b c d
  have ha' : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift a) (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using ha.shift
  have hc' : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift c) (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using hc.shift
  have hd' : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift d) (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using hd.shift
  have hT' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift T) := by simpa [Fm.shift,Syn.shift,one] using hT.shift
  have h' : Γ.map Fm.shift ⊢[PRAAx] finiteRateWithDenominator (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift d) (Syn.shift K) (Syn.shift T) (Syn.shift B) := by
    simpa only [Fm.shift,subst_finiteRateWithDenominator,Syn.shift] using h.shift
  have row := diagonal (var 0) _ _ _ _ _ _ _ ha' hc' hd' hT' h'
  have low : Γ ⊢[PRAAx] envelope constantF quotientLogF L q E := .allI (by simpa [envelope,L,q,E,Syn.shift] using row.andE₁)
  have cap : Γ ⊢[PRAAx] envelope quotientLogF constantF q R E := .allI (by simpa [envelope,R,q,E,Syn.shift] using row.andE₂)
  have hq := quotient_log_regular a b c d ha hc hd
  exact .andI (order_from_envelope _ _ _ _ _ (constant_regular L) hq low)
    (order_from_envelope _ _ _ _ _ hq (constant_regular R) cap)

def finiteRate (a b c d K B : PTm n) : Fm PTm n :=
  finiteRateWithDenominator a b c d K a B

ipra_subst finiteRate [finiteRateWithDenominator, Syn.subst_shift, Syn.shift_subst]

def logRate (a b c d K : PTm n) : Fm PTm n :=
  logRateWithDenominator a b c d K a

theorem cofinal_rate (a b c d K B : PTm n) (ha : Γ ⊢[PRAAx] source a b)
    (hc : Γ ⊢[PRAAx] source c b) (hD : Γ ⊢[PRAAx] source d b)
    (h : Γ ⊢[PRAAx] finiteRate a b c d K B) : Γ ⊢[PRAAx] logRate a b c d K :=
  cofinal_rate_with_denominator a b c d K a B ha hc hD ha.andE₁ h

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftCofinalRate
