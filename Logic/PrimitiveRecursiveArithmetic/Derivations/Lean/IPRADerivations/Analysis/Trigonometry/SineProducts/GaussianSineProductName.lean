import IPRADerivations.Analysis.FiniteOperations.FiniteProducts.GaussianInverseSquareProductTail

/-!
# Cofinal regular name of the literal sine product

Use the finite inverse-square tail bound to give the literal factors
1−(z/(Bk))² a primitive recursive cofinal clock. The same finite bounds
give an explicit uniform Cauchy rate for the unnormalized products.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianSineProductName

open_ipra
open GaussianGammaEulerReflectionHead (body sineProduct squareFactor square_factor_at)
open GaussianInverseSquareProductTail (sine_factor_bound sine_product_tail
  denominator_positive partial_product_bound)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalFiniteProduct (product_zero product_succ product_split product_index_congr
  product_canonical)
open GaussianRationalSyntheticDivision (qone qmul_congr)
open GaussianRationalReciprocal (qone_bounded bounded_sum bounded_product bounded_product_one bound_congr)
open GaussianRationalMetric (bounded distanceBounded qsub qsub_canonical)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_from_later_observations)
open GaussianRationalLinearProduct (add_sub_right)
open GaussianReciprocalHorner (qmul_one_right)
open GaussianEuclideanDistanceName (pointCN)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianBalancedRadiusArithmetic (unit_monotone)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def initial (R : PTm n) : PTm n := succ (two*(R*R))
def bound (R : PTm n) : PTm n := two*pw (one+R*R) (initial R)
def rate (R : PTm n) : PTm n := bound R*(two*(R*R))
def cutoff (R p : PTm n) : PTm n := initial R+rate R*unit p

ipra_subst cutoff [rate, bound, initial]

theorem initial_positive (R : PTm n) : Γ ⊢[PRAAx] le one (initial R) := zero_lt_succ _

theorem sine_product_succ (z B N : PTm n) :
    Γ ⊢[PRAAx] sineProduct z B (succ N) ≐ qmul (sineProduct z B N) (squareFactor N z B) :=
  (product_succ body N (pairT z B)).eqTrans (qmul_congr (.eqRefl _) (square_factor_at N z B))

theorem factor_norm (i z R B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] bounded (squareFactor i z B) (one+R*R) one := by
  let F := squareFactor i z B
  let j := succ i
  have hp : Γ ⊢[PRAAx] le one (j*j) := positive_product _ _ (zero_lt_succ _) (zero_lt_succ _)
  have compare : Γ ⊢[PRAAx] le ((R*R)*one) ((R*R)*(j*j)) :=
    mul_le_mul_left (R*R) hp
  have hf := distance_radius_mono F qone (R*R) (j*j) (R*R) one hp (le_refl _)
    compare (sine_factor_bound i z R B hB hz)
  have sum := bounded_sum qone (qsub F qone) one one (R*R) one (le_refl _) (le_refl _) qone_bounded hf
  exact bound_congr (add_sub_right qone F (qsub_canonical _ _)) (by ipra_ring) (by ipra_ring) sum

private def prefixBound (z R B N : PTm n) : Fm PTm n := bounded (sineProduct z B N) (pw (one+R*R) N) one

@[simp] private theorem subst_prefixBound {l : ℕ} (σ : Fin n → PTm l) (z R B N : PTm n) :
    (prefixBound z R B N).subst σ = prefixBound (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [prefixBound,sineProduct]

private theorem prefix_zero (z R B : PTm n) : Γ ⊢[PRAAx] prefixBound z R B zero :=
  bound_congr (product_zero body (pairT z B)).eqSymm (pw_zero (one+R*R)).eqSymm (.eqRefl _) qone_bounded

private theorem prefix_succ (z R B N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (h : Γ ⊢[PRAAx] prefixBound z R B N) : Γ ⊢[PRAAx] prefixBound z R B (succ N) :=
  bound_congr (sine_product_succ z B N).eqSymm (pw_succ _ _).eqSymm (.eqRefl _)
    (bounded_product_one h (factor_norm N z R B hB hz))

theorem prefix_norm (z R B N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) : Γ ⊢[PRAAx] prefixBound z R B N := by
  have hb : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have hd : Γ.map Fm.shift ⊢[PRAAx] ComplexLogarithmRemainder.bounded (Syn.shift z) (Syn.shift R*Syn.shift B) := by
    simpa [Fm.shift,Syn.shift] using hz.shift
  have all : Γ ⊢[PRAAx] .all (prefixBound (Syn.shift z) (Syn.shift R) (Syn.shift B) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simpa only [subst_prefixBound,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using prefix_zero z R B
    · simpa only [subst_prefixBound,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        prefix_succ (Syn.shift z) (Syn.shift R) (Syn.shift B) (var 0) hb.wk hd.wk Prf.hyp0
  simpa only [subst_prefixBound,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

theorem uniform_norm (z R B N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (hN : Γ ⊢[PRAAx] le (initial R) N) :
    Γ ⊢[PRAAx] bounded (sineProduct z B N) (bound R) one := by
  let K := initial R
  let r := monus N K
  have kh : Γ ⊢[PRAAx] le (two*(R*R)) K := le_succ_self _
  have hp := sine_product_tail z R B K r hB hz (initial_positive R) kh
  have boundedTail := partial_product_bound body (pairT z B) (R*R) K r (initial_positive R) kh hp
  have eq : Γ ⊢[PRAAx] sineProduct z B N ≐ qmul (sineProduct z B K)
      (GaussianInverseSquareProductTail.product body K r (pairT z B)) :=
    (product_index_congr body (eq_add_of_le hN) (.eqRefl _)).eqTrans (product_split body K r (pairT z B))
  exact bound_congr eq.eqSymm (by unfold bound K; ipra_ring) (.eqRefl _)
    (bounded_product_one (prefix_norm z R B K hB hz) boundedTail)

theorem finite_rate (z R B K M : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (hK : Γ ⊢[PRAAx] le (initial R) K) (hM : Γ ⊢[PRAAx] le K M) :
    Γ ⊢[PRAAx] distanceBounded (sineProduct z B M) (sineProduct z B K) (rate R) K := by
  let r := monus M K
  let S := sineProduct z B K
  let T := GaussianInverseSquareProductTail.product body K r (pairT z B)
  have kp := le_trans (initial_positive R) hK
  have hk := le_trans (le_succ_self (two*(R*R))) hK
  have e : Γ ⊢[PRAAx] sineProduct z B M ≐ qmul S T :=
    (product_index_congr body (eq_add_of_le hM) (.eqRefl _)).eqTrans (product_split body K r (pairT z B))
  have ht := sine_product_tail z R B K r hB hz kp hk
  have den := denominator_positive K r kp
  have old := bounded_product S (qsub T qone) (bound R) one (two*(R*R)*r) (K*(K+r))
    (le_refl one) den (uniform_norm z R B K hB hz hK) ht
  have small : Γ ⊢[PRAAx] distanceBounded (sineProduct z B M) S (rate R*r) (K*(K+r)) :=
    distance_congr e.eqSymm (qmul_one_right S (product_canonical _ _ _)) (by unfold rate; ipra_ring) (one_mul _)
      (bound_congr (GaussianRationalRoundedPower.multiplication_difference S T qone).eqSymm (.eqRefl _) (.eqRefl _) old)
  exact distance_radius_mono _ _ _ _ _ _ den kp
    (le_of_eq_add (d := rate R*K*K) (by ipra_ring)) small

def data (z R B : PTm n) : PTm n := pairT z (pairT R B)
def sampled (z R B p : PTm n) : PTm n := sineProduct z B (cutoff R p)
def nameF : PR 2 := PTm.toPR
  (sampled (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0) : PTm 2)

ipra_subst sampled [sineProduct]

theorem sample_at (z R B p : PTm n) : Γ ⊢[PRAAx] ap2 nameF p (data z R B) ≐ sampled z R B p := by
  simpa [nameF, data, pairVector, pairVectorField] using
    (toPR_pairVector_eq (Γ := Γ) (k := 2) (sampled (var 1) (var 2) (var 3) (var 0)) p ![z, R, B])

theorem cofinal_error (z R B p M : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) (hM : Γ ⊢[PRAAx] le (cutoff R p) M) :
    Γ ⊢[PRAAx] distanceBounded (sineProduct z B M) (ap2 nameF p (data z R B)) one (unit p) := by
  have hc : Γ ⊢[PRAAx] le (initial R) (cutoff R p) := le_add_right _ _
  have c : Γ ⊢[PRAAx] le (rate R*unit p) (one*cutoff R p) :=
    le_congr (.eqRefl _) (one_mul _).eqSymm (le_add_left _ _)
  exact distance_congr (.eqRefl _) (sample_at z R B p).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ (le_trans (initial_positive R) hc) (unit_positive p) c
      (finite_rate z R B (cutoff R p) M hB hz hc hM))

theorem ordered_samples (z R B p q : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) (h : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF q (data z R B)) (ap2 nameF p (data z R B)) one (unit p) := by
  have hm : Γ ⊢[PRAAx] le (cutoff R p) (cutoff R q) := add_le_add₂ (le_refl (initial R))
    (mul_le_mul_left (rate R) (unit_monotone p q h))
  exact distance_congr (sample_at z R B q).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (cofinal_error z R B p (cutoff R q) hB hz hm)

theorem sample_pair (z R B p q : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data z R B)) (ap2 nameF q (data z R B))
      (unit p+unit q) (unit p*unit q) :=
  distance_from_later_observations _ _ p q
    (ordered_samples z R B p q hB.wk hz.wk Prf.hyp0)
    (ordered_samples z R B q p hB.wk hz.wk Prf.hyp0)

theorem name_regular (z R B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] pointCN nameF (data z R B) := by
  refine .allI (.allI ?_)
  let t := fun x : PTm n => Syn.shift (Syn.shift x)
  have hb : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (t B) := by simpa [Fm.shift,Syn.shift,t] using hB.shift.shift
  have hd : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      ComplexLogarithmRemainder.bounded (t z) (t R*t B) := by simpa [Fm.shift,Syn.shift,t] using hz.shift.shift
  simpa only [pointCN,data,Syn.shift,t,subst_pairT,GaussianEuclideanPointDistance.unit,unit] using
    sample_pair (t z) (t R) (t B) (var 1) (var 0) hb hd

theorem actual_literal_sine_product_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ ComplexLogarithmRemainder.bounded (var 0) (var 1*var 2) ⟶
      pointCN nameF (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (name_regular _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_literal_sine_product_cofinal_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 2) ⟶ ComplexLogarithmRemainder.bounded (var 0) (var 1*var 2) ⟶
      le (cutoff (var 1) (var 3)) (var 4) ⟶
      distanceBounded (sineProduct (var 0) (var 2) (var 4)) (ap2 nameF (var 3) (data (var 0) (var 1) (var 2)))
        one (unit (var 3))) :=
  closeUniv 5 (.impI (.impI (.impI (cofinal_error _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianSineProductName
