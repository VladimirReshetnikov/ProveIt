import IPRADerivations.Analysis.Trigonometry.Hyperbolic.GaussianSineProductImaginaryLogDerivative

/-!
# Cofinal imaginary-axis sine product logarithmic derivative

The actual derivative rows 2x/(j²+x²) have a uniform reciprocal-square
tail for 0 ≤ x ≤ R. The original rational sums therefore give a regular
name with a computed cutoff on every such interval.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianSineProductImaginaryLogDerivativeTail

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder (normSq normSq_code)
open GaussianCoefficientNameBounds (bounded_radius_mono unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalHorner (ofGaussian_represents ofGaussian_canonical positive_product qzero qadd)
open GaussianRationalMetric (bounded bounded_iff distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSyntheticDivision (qadd_congr qadd_sub_cancel)
open GaussianReciprocalHorner (qadd_zero_right qadd_commutative)
open GaussianSineProductImaginaryLogDerivative
  (axisNumerator realNumerator rationalReal squareDenominator logarithmRow logarithmSum logarithm_sum_succ)
open GaussianReconstructionRoots (distance_triangle norm_from_distance)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

theorem real_norm (a : PTm n) : Γ ⊢[PRAAx] normSq (realNumerator a) ≐ a*a := by
  apply deriveNat
  rw [realNumerator, normSq_code, ZT.toZ_ofNat, ZT.toZ_ofNat]
  ipra_simps
  ring

theorem axis_norm (a : PTm n) : Γ ⊢[PRAAx] normSq (axisNumerator a) ≐ a*a := by
  apply deriveNat
  rw [axisNumerator, normSq_code, ZT.toZ_ofNat, ZT.toZ_ofNat]
  ipra_simps
  ring

theorem rational_real_bound (a d C D : PTm n)
    (hd : Γ ⊢[PRAAx] le one d) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] le (D*a) (C*d)) : Γ ⊢[PRAAx] bounded (rationalReal a d) C D := by
  have sq := le_mul_mono h h
  have left : Γ ⊢[PRAAx] (D*a)*(D*a) ≐ (D*D)*normSq (realNumerator a) :=
    (show Γ ⊢[PRAAx] (D*a)*(D*a) ≐ (D*D)*(a*a) from by ipra_ring).eqTrans
      (congrMul (.eqRefl _) (real_norm a).eqSymm)
  exact (bounded_iff _ _ _ _ _ hd hD (ofGaussian_represents _ _ hd)).iffMpr
    (le_congr left (by ipra_ring) sq)

theorem row_bound (A B R i : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] bounded (logarithmRow i A B) (two*R) (succ i*succ i) := by
  let j := succ i
  let E := squareDenominator i B+A*A
  have hj : Γ ⊢[PRAAx] le one j := zero_lt_succ _
  have hBj := positive_product _ _ hB hj
  have hE := le_trans (positive_product _ _ hBj hBj) (le_add_right (squareDenominator i B) (A*A))
  apply rational_real_bound (two*A*B) E (two*R) (j*j) hE (positive_product _ _ hj hj)
  dsimp only [E, squareDenominator, j]
  ipra_le 2*𝔞(B)*𝔞(succ i)^2*sl hA+2*𝔞(R)*𝔞(A)^2

private theorem row_canonical (A B i : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] GaussianRationalHorner.canonical (logarithmRow i A B) := by
  have hBj := positive_product _ _ hB (zero_lt_succ (Γ := Γ) i)
  exact ofGaussian_canonical _ _ (le_trans (positive_product _ _ hBj hBj) (le_add_right _ _))

private theorem sum_index_congr (A B : PTm n) {k l : PTm n} (h : Γ ⊢[PRAAx] k ≐ l) :
    Γ ⊢[PRAAx] logarithmSum A B k ≐ logarithmSum A B l := by
  simpa only [GaussianSineProductImaginaryLogDerivative.subst_logarithmSum, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] using
      Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (logarithmSum (var 0) (var 1) (var 2) : PTm 3)
        (σ := ![A,B,k]) (σ' := ![A,B,l]) (fun j => by fin_cases j; exact .eqRefl _; exact .eqRefl _; exact h)

def tail (A B R N r : PTm n) : Fm PTm n :=
  distanceBounded (logarithmSum A B (N+r)) (logarithmSum A B N) (two*R*r) (N*(N+r))

ipra_subst tail [two]

private theorem tail_den_positive (N r : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] le one (N*(N+r)) :=
  positive_product _ _ hN (le_trans hN (le_add_right _ _))

private theorem tail_zero (A B R N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] tail A B R N zero :=
  distance_congr (sum_index_congr A B (add_zero N)).eqSymm (.eqRefl _) (mul_zero _).eqSymm (.eqRefl _)
    (GaussianRationalPowerDifference.distance_refl_zero _ _ (tail_den_positive N zero hN))

private theorem tail_succ (A B R N r : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hA : Γ ⊢[PRAAx] le A (R*B)) (hN : Γ ⊢[PRAAx] le one N)
    (ih : Γ ⊢[PRAAx] tail A B R N r) : Γ ⊢[PRAAx] tail A B R N (succ r) := by
  let S := logarithmSum A B (N+r)
  let W := logarithmRow (N+r) A B
  let k := succ (N+r)
  let D := N*(N+r)
  let E := k*k
  let C := two*R
  have hD := tail_den_positive N r hN
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ (zero_lt_succ _) (zero_lt_succ _)
  have add : Γ ⊢[PRAAx] distanceBounded (qadd S W) S C E :=
    bound_congr (qadd_sub_cancel S W (row_canonical A B (N+r) hB)).eqSymm (.eqRefl _) (.eqRefl _)
      (row_bound A B R (N+r) hB hA)
  have combo := distance_triangle (qadd S W) S (logarithmSum A B N) C E (C*r) D hE hD add ih
  have estimate : Γ ⊢[PRAAx] distanceBounded (qadd S W) (logarithmSum A B N)
      (C*succ r) (N*(N+succ r)) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hE hD) (tail_den_positive N (succ r) hN)
      (le_of_eq_add (d := C*N*N*k) (by dsimp only [D,E,k]; ipra_ring)) combo
  have eq : Γ ⊢[PRAAx] N+succ r ≐ succ (N+r) := by ipra_ring
  exact distance_congr ((sum_index_congr A B eq).eqTrans (logarithm_sum_succ A B (N+r))).eqSymm
    (.eqRefl _) (.eqRefl _) (.eqRefl _) estimate

theorem sharp_tail (A B R N r : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hA : Γ ⊢[PRAAx] le A (R*B)) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] tail A B R N r := by
  let Δ := Γ.map Fm.shift
  let s (t : PTm n) := Syn.shift t
  have sb : Δ ⊢[PRAAx] le one (s B) := by simpa [Δ, s, Fm.shift, Syn.shift, one] using hB.shift
  have sa : Δ ⊢[PRAAx] le (s A) (s R*s B) := by simpa [Δ, s, Fm.shift, Syn.shift] using hA.shift
  have sn : Δ ⊢[PRAAx] le one (s N) := by simpa [Δ, s, Fm.shift, Syn.shift, one] using hN.shift
  have all : Γ ⊢[PRAAx] .all (tail (s A) (s B) (s R) (s N) (var 0)) := by
    refine PRA.qfInd _ (by unfold tail distanceBounded bounded RationalArgmin.rationalLE; exact le_QF _ _) ?_ ?_
    · simpa only [subst_tail, s, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using tail_zero A B R N hN
    · simpa only [subst_tail, s, Syn.subst_var, Syn.repl_zero, subst_repl_shift] using
        tail_succ (s A) (s B) (s R) (s N) (var 0) sb.wk sa.wk sn.wk Prf.hyp0
  simpa only [subst_tail, s, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using all.allE r

theorem finite_rate (A B R N M : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hA : Γ ⊢[PRAAx] le A (R*B)) (hN : Γ ⊢[PRAAx] le one N) (hM : Γ ⊢[PRAAx] le N M) :
    Γ ⊢[PRAAx] distanceBounded (logarithmSum A B M) (logarithmSum A B N) (two*R) N := by
  let r := monus M N
  have e := eq_add_of_le hM
  have coarse := distance_radius_mono _ _ _ _ (two*R) N (tail_den_positive N r hN) hN
    (le_of_eq_add (d := two*R*N*N) (by ipra_ring)) (sharp_tail A B R N r hB hA hN)
  exact distance_congr (sum_index_congr A B e.eqSymm) (.eqRefl _) (.eqRefl _) (.eqRefl _) coarse

private theorem sum_zero (A B : PTm n) : Γ ⊢[PRAAx] logarithmSum A B zero ≐ qzero :=
  GaussianRationalFiniteSum.sum_zero _ _

theorem uniform_bound (A B R N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] bounded (logarithmSum A B N) (two*(two*R)) one := by
  let C := two*R
  refine .orE (zero_or_succ N) ?_ ?_
  · have z := (sum_index_congr (Γ := (N ≐ zero) :: Γ) A B Prf.hyp0).eqTrans (sum_zero A B)
    exact bound_congr z.eqSymm (.eqRefl _) (.eqRefl _) (GaussianMonicResidualRadius.zero_bounded _ _ (le_refl one))
  · let Δ := (N ≐ succ (pred N)) :: Γ
    have hN : Δ ⊢[PRAAx] le one N := le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ _)
    have base : Δ ⊢[PRAAx] logarithmSum A B one ≐ logarithmRow zero A B :=
      (logarithm_sum_succ A B zero).eqTrans
        ((qadd_congr (sum_zero A B) (.eqRefl _)).eqTrans
          ((qadd_commutative _ _).eqTrans (qadd_zero_right _ (row_canonical A B zero hB.wk))))
    have first : Δ ⊢[PRAAx] bounded (logarithmSum A B one) C one :=
      bound_congr base.eqSymm (.eqRefl _) (by ipra_ring) (row_bound A B R zero hB.wk hA.wk)
    have near := finite_rate A B R one N hB.wk hA.wk (le_refl one) hN
    exact bound_congr (.eqRefl _) (by unfold C; ipra_ring) (by ipra_ring)
      (norm_from_distance _ _ _ _ _ _ (le_refl one) (le_refl one) near first)

def cutoff (R p : PTm n) : PTm n := one+(two*R)*unit p
def data (A B R : PTm n) : PTm n := pairT A (pairT B R)
def sampled (A B R p : PTm n) : PTm n := logarithmSum A B (cutoff R p)
def nameF : PR 2 := PTm.toPR
  (sampled (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0) : PTm 2)

ipra_subst sampled [cutoff, two, one]

ipra_subst data

theorem sample_at (A B R p : PTm n) : Γ ⊢[PRAAx] ap2 nameF p (data A B R) ≐ sampled A B R p := by
  let d := data A B R
  have body : Γ ⊢[PRAAx] ap2 nameF p d ≐ sampled (fstT d) (fstT (sndT d)) (sndT (sndT d)) p := by
    simpa only [ap2,nameF,subst_sampled,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,
      Matrix.cons_val_one] using toPR_eq (Γ := Γ)
      (sampled (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0) : PTm 2) ![p,d]
  have second := snd_pair (Γ := Γ) A (pairT B R)
  refine body.eqTrans ?_
  simpa only [subst_sampled,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (sampled (var 0) (var 1) (var 2) (var 3) : PTm 4)
      (σ := ![fstT d,fstT (sndT d),sndT (sndT d),p]) (σ' := ![A,B,R,p])
      (fun i => by
        fin_cases i
        · exact fst_pair _ _
        · exact (congrFst second).eqTrans (fst_pair _ _)
        · exact (congrSnd second).eqTrans (snd_pair _ _)
        · exact .eqRefl _)

theorem cofinal_error (A B R p N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hA : Γ ⊢[PRAAx] le A (R*B)) (hN : Γ ⊢[PRAAx] le (cutoff R p) N) :
    Γ ⊢[PRAAx] distanceBounded (logarithmSum A B N) (ap2 nameF p (data A B R)) one (unit p) := by
  have hc : Γ ⊢[PRAAx] le one (cutoff R p) := le_add_right _ _
  have cmp : Γ ⊢[PRAAx] le ((two*R)*unit p) (one*cutoff R p) :=
    le_congr (.eqRefl _) (one_mul _).eqSymm (le_add_left _ _)
  exact distance_congr (.eqRefl _) (sample_at A B R p).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ hc (unit_positive p) cmp
      (finite_rate A B R (cutoff R p) N hB hA hc hN))

private theorem ordered (A B R p q : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hA : Γ ⊢[PRAAx] le A (R*B)) (hq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF q (data A B R)) (ap2 nameF p (data A B R)) one (unit p) := by
  have hpq : Γ ⊢[PRAAx] le (cutoff R p) (cutoff R q) :=
    add_le_add₂ (le_refl one) (le_mul_mono (le_refl (two*R)) (GaussianBalancedRadiusArithmetic.unit_monotone p q hq))
  exact distance_congr (sample_at A B R q).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (cofinal_error A B R p (cutoff R q) hB hA hpq)

theorem sample_pair (A B R p q : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data A B R)) (ap2 nameF q (data A B R))
      (unit p+unit q) (unit p*unit q) := by
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have hD := positive_product _ _ hp hq
  refine .orE (le_total p q) ?_ ?_
  · exact distance_radius_mono _ _ _ _ _ _ hp.wk hD.wk
      (le_of_eq_add (d := unit p*unit p) (by ipra_ring))
      (distance_symmetric _ _ _ _ hp.wk (ordered A B R p q hB.wk hA.wk Prf.hyp0))
  · exact distance_radius_mono _ _ _ _ _ _ hq.wk hD.wk
      (le_of_eq_add (d := unit q*unit q) (by ipra_ring)) (ordered A B R q p hB.wk hA.wk Prf.hyp0)

theorem regular (A B R : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] pointCN nameF (data A B R) := by
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let s (t : PTm n) := Syn.shift (Syn.shift t)
  have hbs : Δ ⊢[PRAAx] le one (s B) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hB.shift.shift
  have has : Δ ⊢[PRAAx] le (s A) (s R*s B) := by simpa [Δ,s,Fm.shift,Syn.shift] using hA.shift.shift
  refine .allI (.allI ?_)
  simpa only [pointCN, Δ, Syn.shift, s, subst_data, GaussianEuclideanPointDistance.unit, unit] using
    sample_pair (s A) (s B) (s R) (var 1) (var 0) hbs has

theorem actual_imaginary_sine_logarithmic_derivative_sum_regular_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((le one (var 1) ⋏ le (var 0) (var 2*var 1)) ⟶ pointCN nameF (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (regular _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianSineProductImaginaryLogDerivativeTail
