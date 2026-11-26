import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaTwoShiftCofinalRate

/-!
# Cofinal two-shift bounds with an explicit rational denominator

The leading radius and the original Gamma input denominator are
independent. Move each exact scalar radius into the endpoints of
the interval, and remove the remaining dyadic observation slack by
named real order.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftExactCofinalRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaDigammaHarmonicCells (point_fraction_represents)
open GaussianGammaDigammaTwoShiftBinding (quotientLogF quotientLogData quotient_log_regular)
open GaussianGammaDigammaTwoShiftCofinalRate (rawSample quotient_sample_error sampleCost)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNamedRealOrderEnvelope (envelope order_from_envelope)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_symmetric)
open GaussianRationalHorner (qzero scalar_congr positive_product)
open GaussianRationalMetric (qnegative)
open GaussianStirlingGammaFractionalIncrementObservations (scalar_upper)
open GaussianStirlingGammaLogarithm (source)
open RationalRepresentedUpper (to_signed from_signed left right)
open RationalValueBounds (upper upper_congr upper_mono upper_triangle)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def finiteRate (a b c d K D B : PTm n) : Fm PTm n := .all
  ((upper (fstT qzero) (fstT (rawSample (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift d)))
      (Syn.shift K*unit (var 0)+Syn.shift B*Syn.shift D) (Syn.shift D*unit (var 0))) ⋏
   (upper (fstT (rawSample (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift d))) (fstT qzero)
      (Syn.shift K*unit (var 0)+Syn.shift B*Syn.shift D) (Syn.shift D*unit (var 0))))

@[simp] theorem subst_finiteRate {m : ℕ} (σ : Fin n → PTm m) (a b c d K D B : PTm n) :
    (finiteRate a b c d K D B).subst σ = finiteRate (Syn.subst σ a) (Syn.subst σ b)
      (Syn.subst σ c) (Syn.subst σ d) (Syn.subst σ K) (Syn.subst σ D) (Syn.subst σ B) := by
  simp [finiteRate,Syn.subst_shift,Syn.shift_subst]

private theorem finite_at (p a b c d K D B : PTm n) (h : Γ ⊢[PRAAx] finiteRate a b c d K D B) :
    Γ ⊢[PRAAx] (upper (fstT qzero) (fstT (rawSample p a b c d)) (K*unit p+B*D) (D*unit p) ⋏
      upper (fstT (rawSample p a b c d)) (fstT qzero) (K*unit p+B*D) (D*unit p)) := by
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

def logRate (a b c d K T : PTm n) : Fm PTm n :=
  realOrder constantF quotientLogF (qnegative (fraction K T)) (quotientLogData a b c d) ⋏
  realOrder quotientLogF constantF (quotientLogData a b c d) (fraction K T)

private theorem diagonal (p a b c d K T B : PTm n) (ha : Γ ⊢[PRAAx] source a b)
    (hc : Γ ⊢[PRAAx] source c b) (hd : Γ ⊢[PRAAx] source d b) (hT : Γ ⊢[PRAAx] le one T)
    (h : Γ ⊢[PRAAx] finiteRate a b c d K T B) :
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

theorem cofinal_rate (a b c d K T B : PTm n) (ha : Γ ⊢[PRAAx] source a b)
    (hc : Γ ⊢[PRAAx] source c b) (hd : Γ ⊢[PRAAx] source d b) (hT : Γ ⊢[PRAAx] le one T)
    (h : Γ ⊢[PRAAx] finiteRate a b c d K T B) : Γ ⊢[PRAAx] logRate a b c d K T := by
  let q := quotientLogData a b c d
  let L := qnegative (fraction K T)
  let R := fraction K T
  let E := B+sampleCost a b c d
  have ha' : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift a) (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using ha.shift
  have hc' : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift c) (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using hc.shift
  have hd' : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift d) (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using hd.shift
  have hT' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift T) := by simpa [Fm.shift,Syn.shift,one] using hT.shift
  have h' : Γ.map Fm.shift ⊢[PRAAx] finiteRate (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift d) (Syn.shift K) (Syn.shift T) (Syn.shift B) := by
    simpa only [Fm.shift,subst_finiteRate,Syn.shift] using h.shift
  have row := diagonal (var 0) _ _ _ _ _ _ _ ha' hc' hd' hT' h'
  have low : Γ ⊢[PRAAx] envelope constantF quotientLogF L q E := .allI (by simpa [envelope,L,q,E,Syn.shift] using row.andE₁)
  have cap : Γ ⊢[PRAAx] envelope quotientLogF constantF q R E := .allI (by simpa [envelope,R,q,E,Syn.shift] using row.andE₂)
  have hq := quotient_log_regular a b c d ha hc hd
  exact .andI (order_from_envelope _ _ _ _ _ (constant_regular L) hq low)
    (order_from_envelope _ _ _ _ _ hq (constant_regular R) cap)

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftExactCofinalRate
