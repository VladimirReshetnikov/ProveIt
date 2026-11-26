import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaTwoShiftFiniteRate
import IPRADerivations.Analysis.Names.GaussianNamedRealOrderEnvelope

/-!
# Cofinal transfer to the original two-shift log quotient

Finite bounds with radius K/a and vanishing observation error give
exact independent-clock order between the named constants −K/a and K/a.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftCofinalRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaDigammaHarmonicCells (point_fraction_represents)
open GaussianGammaDigammaTwoShiftBinding
  (coefficient powerLogF powerLogData denominatorLogF denominatorLogData quotientLogF quotientLogData
    power_log_regular denominator_log_regular quotient_log_regular)
open GaussianGammaDigammaTwoShiftSecants (logSample upper_negative)
open GaussianHarmonicLogarithmName (sample)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNamedRealOrderEnvelope (envelope order_from_envelope)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qadd qmul qzero positive_product scalar_congr)
open GaussianRationalMetric (qsub qnegative distanceBounded)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr)
open GaussianStirlingGammaLogarithm (source logGammaF logGammaData log_gamma_regular)
open GaussianStirlingGammaFractionalIncrementObservations (scalar_upper)
open RationalRepresentedUpper (left right to_signed from_signed)
open RationalValueBounds (upper upper_congr upper_mono upper_triangle)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "hd" => GaussianHarmonicLogarithmName.data
local notation "H" => GaussianHarmonicLogarithmName.nameF

def rawSample (p a b c d : PTm n) : PTm n :=
  qsub (qsub (logSample p c b) (logSample p d b)) (qmul (coefficient b c d) (sample p a b))

def sampleCost (a b c d : PTm n) : PTm n :=
  GaussianNameArithmetic.multiplyModulus constantF H (coefficient b c d) (hd a b)+num 10

@[simp] theorem subst_rawSample {m : ℕ} (σ : Fin n → PTm m) (p a b c d : PTm n) :
    Syn.subst σ (rawSample p a b c d) = rawSample (Syn.subst σ p) (Syn.subst σ a)
      (Syn.subst σ b) (Syn.subst σ c) (Syn.subst σ d) := by
  simp [rawSample,logSample,sample]

@[simp] theorem subst_sampleCost {m : ℕ} (σ : Fin n → PTm m) (a b c d : PTm n) :
    Syn.subst σ (sampleCost a b c d) = sampleCost (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ c) (Syn.subst σ d) := by
  simp [sampleCost]

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
    (GaussianNameRingLaws.multiply_sample_error constantF H w (hd a b) p (constant_regular w)
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

def finiteRate (a b c d K B : PTm n) : Fm PTm n := .all
  ((upper (fstT qzero) (fstT (rawSample (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift d)))
    (Syn.shift K*unit (var 0)+Syn.shift B*Syn.shift a) (Syn.shift a*unit (var 0))) ⋏
   (upper (fstT (rawSample (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift d))) (fstT qzero)
    (Syn.shift K*unit (var 0)+Syn.shift B*Syn.shift a) (Syn.shift a*unit (var 0))))

@[simp] theorem subst_finiteRate {m : ℕ} (σ : Fin n → PTm m) (a b c d K B : PTm n) :
    (finiteRate a b c d K B).subst σ = finiteRate (Syn.subst σ a) (Syn.subst σ b)
      (Syn.subst σ c) (Syn.subst σ d) (Syn.subst σ K) (Syn.subst σ B) := by
  simp [finiteRate,Syn.subst_shift,Syn.shift_subst]

private theorem finite_at (p a b c d K B : PTm n) (h : Γ ⊢[PRAAx] finiteRate a b c d K B) :
    Γ ⊢[PRAAx] (upper (fstT qzero) (fstT (rawSample p a b c d)) (K*unit p+B*a) (a*unit p) ⋏
      upper (fstT (rawSample p a b c d)) (fstT qzero) (K*unit p+B*a) (a*unit p)) := by
  simpa [finiteRate,Syn.subst_inst_shift,Syn.inst_zero] using h.allE p

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

def logRate (a b c d K : PTm n) : Fm PTm n :=
  realOrder constantF quotientLogF (qnegative (fraction K a)) (quotientLogData a b c d) ⋏
  realOrder quotientLogF constantF (quotientLogData a b c d) (fraction K a)

private theorem diagonal (p a b c d K B : PTm n) (ha : Γ ⊢[PRAAx] source a b)
    (hc : Γ ⊢[PRAAx] source c b) (hD : Γ ⊢[PRAAx] source d b)
    (h : Γ ⊢[PRAAx] finiteRate a b c d K B) :
    Γ ⊢[PRAAx]
      (upper (fstT (ap2 constantF p (qnegative (fraction K a))))
        (fstT (ap2 quotientLogF p (quotientLogData a b c d))) (B+sampleCost a b c d) (unit p) ⋏
       upper (fstT (ap2 quotientLogF p (quotientLogData a b c d)))
        (fstT (ap2 constantF p (fraction K a))) (B+sampleCost a b c d) (unit p)) := by
  let q := ap2 quotientLogF p (quotientLogData a b c d)
  let r := rawSample p a b c d
  let C := sampleCost a b c d
  let L := qnegative (fraction K a)
  let R := fraction K a
  let U := unit p
  have hp := unit_positive (Γ := Γ) p
  have e := quotient_sample_error p a b c d ha hc hD
  have base := finite_at p a b c d K B h
  have lo := move_radius_left r K a B p ha.andE₁ base.andE₁
  have hi := move_radius_right r K a B p ha.andE₁ base.andE₂
  have eF := scalar_upper q r C U hp e
  have eR := scalar_upper r q C U hp (distance_symmetric _ _ _ _ hp e)
  refine .andI ?_ ?_
  · apply upper_congr (congrFst (constant_at p L).eqSymm) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    exact upper_mono _ _ _ _ _ _ (positive_product _ _ hp hp) (upper_triangle _ _ _ _ _ _ _ lo eR)
      (le_of_eq_add (d := zero) (by ipra_ring))
  · apply upper_congr (.eqRefl _) (congrFst (constant_at p R).eqSymm) (.eqRefl _) (.eqRefl _)
    exact upper_mono _ _ _ _ _ _ (positive_product _ _ hp hp) (upper_triangle _ _ _ _ _ _ _ eF hi)
      (le_of_eq_add (d := zero) (by ipra_ring))

theorem cofinal_rate (a b c d K B : PTm n) (ha : Γ ⊢[PRAAx] source a b)
    (hc : Γ ⊢[PRAAx] source c b) (hD : Γ ⊢[PRAAx] source d b)
    (h : Γ ⊢[PRAAx] finiteRate a b c d K B) : Γ ⊢[PRAAx] logRate a b c d K := by
  let q := quotientLogData a b c d
  let L := qnegative (fraction K a)
  let R := fraction K a
  let E := B+sampleCost a b c d
  have ha' : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift a) (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using ha.shift
  have hc' : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift c) (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using hc.shift
  have hD' : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift d) (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using hD.shift
  have h' : Γ.map Fm.shift ⊢[PRAAx] finiteRate (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift d) (Syn.shift K) (Syn.shift B) := by
    simpa only [Fm.shift,subst_finiteRate,Syn.shift] using h.shift
  have row := diagonal (var 0) _ _ _ _ _ _ ha' hc' hD' h'
  have low : Γ ⊢[PRAAx] envelope constantF quotientLogF L q E := .allI (by simpa [envelope,L,q,E,Syn.shift] using row.andE₁)
  have cap : Γ ⊢[PRAAx] envelope quotientLogF constantF q R E := .allI (by simpa [envelope,R,q,E,Syn.shift] using row.andE₂)
  have hq := quotient_log_regular a b c d ha hc hD
  exact .andI (order_from_envelope _ _ _ _ _ (constant_regular L) hq low)
    (order_from_envelope _ _ _ _ _ hq (constant_regular R) cap)

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftCofinalRate
