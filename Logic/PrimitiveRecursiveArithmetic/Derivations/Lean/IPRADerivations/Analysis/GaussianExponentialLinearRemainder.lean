import IPRADerivations.Analysis.GaussianRationalExponentialTail
import IPRADerivations.Analysis.GaussianRationalPowerDifference
import IPRADerivations.Analysis.GaussianIntegerFractionPowers
import IPRADerivations.Analysis.GaussianRadiusExponentialName
import IPRADerivations.Analysis.GaussianGammaCanonicalExponent

/-!
# Quadratic error of the original finite exponential

For |h| ≤ A/B ≤ 1, the terms of degree at least two in the actual
factorial sum have norm at most A²/B². The proof uses its original
tail recurrence and the cleared reciprocal-factorial bound at radius
one. The estimate is uniform in the numerical cutoff.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianExponentialLinearRemainder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianRationalExponentialTail (tail tail_succ tail_zero scalarPrefix prefix_difference)
open GaussianRationalPolynomialExponential
  (scalarSum scalarBody scalar_sum_zero scalar_sum_succ inverseFactorial factorial_positive)
open GaussianRationalHorner (qadd qmul canonical positive_product)
open GaussianRationalReciprocal (power bounded_power bounded_product bound_congr)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalSyntheticDivision (qone qmul_congr qadd_congr)
open GaussianCoefficientNameBounds (bounded_radius_mono)
open GaussianPolynomialPerturbation (one_power)
open Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ subst_zero subst_succ)
open LeanProofs.IPRA.PTm (monus num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def count (k : PTm n) : PTm n := ExponentialTail.tsum two one k
def weight (k : PTm n) : PTm n := fact (two+k)

@[simp] theorem subst_count {m : ℕ} (σ : Fin n → PTm m) (k : PTm n) :
    Syn.subst σ (count k) = count (Syn.subst σ k) := by
  simp [count, ExponentialTail.tsum, one, two]
@[simp] theorem subst_weight {m : ℕ} (σ : Fin n → PTm m) (k : PTm n) :
    Syn.subst σ (weight k) = weight (Syn.subst σ k) := by simp [weight, fact, two]

theorem count_succ (k : PTm n) : Γ ⊢[PRAAx] count (succ k) ≐ (count k+one)*succ (two+k) :=
  (ExponentialTail.tsum_succ two one k).eqTrans
    (congrMul (congrAdd (.eqRefl _) (one_power _)) (.eqRefl _))
theorem weight_succ (k : PTm n) : Γ ⊢[PRAAx] weight (succ k) ≐ weight k*succ (two+k) :=
  (congrAp2 factF (add_succ two k) (.eqRefl zero)).eqTrans (fact_succ (two+k) zero)

private theorem factorial_one : Γ ⊢[PRAAx] fact (one : PTm n) ≐ one :=
  (fact_succ zero zero).eqTrans ((congrMul (fact_zero zero) (.eqRefl _)).eqTrans (one_mul _))

theorem factorial_reserve (k : PTm n) : Γ ⊢[PRAAx] le (count k+two) (weight k) := by
  have all : Γ ⊢[PRAAx] .all (le (count (var 0)+two) (weight (var 0))) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le, PTm.subst_add, subst_count, subst_weight, Syn.subst_var, Syn.inst_zero, two, subst_zero, subst_succ]
      have c : Γ ⊢[PRAAx] count (zero : PTm n) ≐ zero := ExponentialTail.tsum_zero two one
      have w : Γ ⊢[PRAAx] weight (zero : PTm n) ≐ two :=
        (congrAp2 factF (add_zero two) (.eqRefl zero)).eqTrans
          ((fact_succ one zero).eqTrans ((congrMul factorial_one (.eqRefl _)).eqTrans (one_mul _)))
      exact le_congr ((congrAdd c (.eqRefl _)).eqTrans (zero_add _)).eqSymm w.eqSymm (le_refl two)
    · simp only [subst_le, PTm.subst_add, subst_count, subst_weight, Syn.subst_var, Syn.repl_zero, two, subst_zero, subst_succ]
      let j : PTm (n+1) := var 0
      let Δ := le (count j+two) (weight j) :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] le (count j+two) (weight j) := Prf.hyp0
      have larger : Δ ⊢[PRAAx] le two (succ (two+j)) :=
        le_trans (le_add_right two j) (le_succ_self _)
      have c := natEq (count_succ (Γ := Δ) j)
      have w := natEq (weight_succ (Γ := Δ) j)
      ipra_le 𝔞(succ (two+j))*sl ih+sl larger using rw [c,w]; ring
  simpa only [subst_le, PTm.subst_add, subst_count, subst_weight, Syn.subst_var, Syn.inst_zero, two, subst_zero, subst_succ] using all.allE k

private theorem square_power (a : PTm n) : Γ ⊢[PRAAx] pw a two ≐ a*a :=
  (pw_succ a one).eqTrans (congrMul (pw_one a) (.eqRefl a))

theorem fractional_term_bound (q A B k : PTm n) (hb : Γ ⊢[PRAAx] le one B)
    (ha : Γ ⊢[PRAAx] le A B) (hq : Γ ⊢[PRAAx] bounded q A B) :
    Γ ⊢[PRAAx] bounded (qmul (inverseFactorial (two+k)) (power q (two+k))) (A*A) (B*B*weight k) := by
  have h1 : Γ ⊢[PRAAx] bounded q one one :=
    bounded_radius_mono _ _ _ _ _ hb (le_refl one) (le_congr (by ipra_ring) (by ipra_ring) ha) hq
  have small : Γ ⊢[PRAAx] bounded (power q k) one one :=
    bound_congr (.eqRefl _) (one_power _) (one_power _) (bounded_power _ _ _ _ (le_refl one) h1)
  have sq := bounded_power q A B two hb hq
  have B2 := positive_product _ _ hb hb
  have all : Γ ⊢[PRAAx] bounded (power q (two+k)) (A*A) (B*B) :=
    bound_congr (GaussianRationalPowerAlgebra.power_add q two k).eqSymm
      ((by ipra_ring : Γ ⊢[PRAAx] pw A two*one ≐ pw A two).eqTrans (square_power A))
      ((by ipra_ring : Γ ⊢[PRAAx] pw B two*one ≐ pw B two).eqTrans (square_power B))
      (bounded_product _ _ _ _ _ _ (GaussianPolynomialPerturbation.power_positive B two hb) (le_refl one) sq small)
  have inv : Γ ⊢[PRAAx] bounded (inverseFactorial (two+k)) one (weight k) :=
    GaussianCoefficientNormEntries.l1_to_euclidean _ _ _ (factorial_positive _)
      (RationalArgmin.rationalLE_congr (GaussianFiniteExponentialWeightedNorm.inverse_factorial_norm _).eqSymm
        (.eqRefl _) (RationalArgmin.reflexive _))
  exact bound_congr (.eqRefl _) (one_mul _) (mul_comm _ _)
    (bounded_product _ _ _ _ _ _ (factorial_positive _) B2 inv all)

def scaledLaw (q A B k : PTm n) : Fm PTm n :=
  bounded (tail q two k) (A*A*count k) (B*B*weight k)
@[simp] theorem subst_scaledLaw {m : ℕ} (σ : Fin n → PTm m) (q A B k : PTm n) :
    (scaledLaw q A B k).subst σ = scaledLaw (Syn.subst σ q) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ k) := by
  simp [scaledLaw, two]

private theorem scaled_step (q A B k : PTm n) (hb : Γ ⊢[PRAAx] le one B)
    (ha : Γ ⊢[PRAAx] le A B) (hq : Γ ⊢[PRAAx] bounded q A B) (old : Γ ⊢[PRAAx] scaledLaw q A B k) :
    Γ ⊢[PRAAx] scaledLaw q A B (succ k) := by
  let D := B*B*weight k
  let E := B*B*weight (succ k)
  have b := positive_product _ _ hb hb
  have d : Γ ⊢[PRAAx] le one D := positive_product _ _ b (factorial_positive _)
  have e : Γ ⊢[PRAAx] le one E := positive_product _ _ b (factorial_positive _)
  have joined := GaussianRationalPowerDifference.bounded_sum_same _ _ (A*A*count k) (A*A) D d old
    (fractional_term_bound q A B k hb ha hq)
  apply bound_congr (tail_succ q two k).eqSymm (.eqRefl _) (.eqRefl _)
  apply bounded_radius_mono _ _ _ _ _ d e _ joined
  have c := natEq (count_succ (Γ := Γ) k)
  have w := natEq (weight_succ (Γ := Γ) k)
  apply le_of_eq_add (d := zero)
  apply deriveNat
  dsimp only [D, E]
  ipra_simps
  rw [c,w]
  ring

theorem actual_quadratic_tail (q A B k : PTm n) (hb : Γ ⊢[PRAAx] le one B)
    (ha : Γ ⊢[PRAAx] le A B) (hq : Γ ⊢[PRAAx] bounded q A B) :
    Γ ⊢[PRAAx] bounded (tail q two k) (A*A) (B*B) := by
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift, Syn.shift] using hb.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift A) (Syn.shift B) := by simpa [Fm.shift, Syn.shift] using ha.shift
  have qs : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift q) (Syn.shift A) (Syn.shift B) :=
    by simpa [Fm.shift, Syn.shift] using hq.shift
  have all : Γ ⊢[PRAAx] .all (scaledLaw (Syn.shift q) (Syn.shift A) (Syn.shift B) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_scaledLaw, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      have d : Γ ⊢[PRAAx] le one (B*B*weight zero) :=
        positive_product _ _ (positive_product _ _ hb hb) (factorial_positive _)
      have c : Γ ⊢[PRAAx] A*A*count zero ≐ zero :=
        (congrMul (.eqRefl _) (ExponentialTail.tsum_zero two one)).eqTrans (by ipra_ring)
      exact bound_congr (tail_zero q two).eqSymm c.eqSymm (.eqRefl _)
        (GaussianMonicResidualRadius.zero_bounded zero _ d)
    · simp only [subst_scaledLaw, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      exact scaled_step _ _ _ _ bs.wk hs.wk qs.wk Prf.hyp0
  have raw : Γ ⊢[PRAAx] scaledLaw q A B k := by
    simpa only [subst_scaledLaw, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using all.allE k
  have b := positive_product _ _ hb hb
  have d : Γ ⊢[PRAAx] le one (B*B*weight k) := positive_product _ _ b (factorial_positive _)
  have c : Γ ⊢[PRAAx] le (count k) (weight k) := le_trans (le_add_right (count k) two) (factorial_reserve k)
  exact bounded_radius_mono _ _ _ _ _ d b
    (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (A*A*(B*B)) c)) raw

private theorem scalar_linear_prefix (q : PTm n) (hq : Γ ⊢[PRAAx] canonical q) :
    Γ ⊢[PRAAx] scalarPrefix q two ≐ qadd qone q := by
  have inv : Γ ⊢[PRAAx] inverseFactorial (one : PTm n) ≐ qone :=
    GaussianIntegerFractionPowers.fraction_congr (.eqRefl _) factorial_one
  exact (scalar_sum_succ q zero).eqTrans (qadd_congr (scalar_sum_zero q)
    ((qmul_congr inv (GaussianRationalPowerAlgebra.power_one q hq)).eqTrans
      (GaussianPolynomialDeterminantTerms.one_mul_canonical q hq)))

theorem original_finite_linear_remainder (q A B K : PTm n) (hb : Γ ⊢[PRAAx] le one B)
    (ha : Γ ⊢[PRAAx] le A B) (hq : Γ ⊢[PRAAx] bounded q A B)
    (can : Γ ⊢[PRAAx] canonical q) (hk : Γ ⊢[PRAAx] le one K) :
    Γ ⊢[PRAAx] distanceBounded (scalarSum q K) (qadd qone q) (A*A) (B*B) := by
  let k := monus K one
  have e : Γ ⊢[PRAAx] succ K ≐ two+k :=
    (congrSucc (eq_add_of_le hk)).eqTrans (by ipra_ring)
  have h := prefix_difference (Γ := Γ) q two k
  have out := GaussianRationalSyntheticDivision.qsub_congr
    (GaussianRationalFiniteSum.sum_index_congr scalarBody e (.eqRefl q)).eqSymm (scalar_linear_prefix q can)
  exact bound_congr (h.eqSymm.eqTrans out) (.eqRefl _) (.eqRefl _) (actual_quadratic_tail q A B k hb ha hq)

theorem original_finite_exponential_linear_remainder_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((le one (var 2) ⋏ le (var 1) (var 2)) ⟶ bounded (var 0) (var 1) (var 2) ⟶
      canonical (var 0) ⟶ le one (var 3) ⟶
        distanceBounded (scalarSum (var 0) (var 3)) (qadd qone (var 0)) (var 1*var 1) (var 2*var 2)) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (original_finite_linear_remainder _ _ _ _
    hyp2.wk.andE₁ hyp2.wk.andE₂ hyp2 Prf.hyp1 Prf.hyp0)))))

theorem original_constant_exponential_linear_remainder (q A B p : PTm n)
    (hb : Γ ⊢[PRAAx] le one B) (ha : Γ ⊢[PRAAx] le A B) (hq : Γ ⊢[PRAAx] bounded q A B)
    (hc : Γ ⊢[PRAAx] canonical q) : Γ ⊢[PRAAx]
    distanceBounded (GaussianRadiusExponentialName.sample constantF one p q) (qadd qone q) (A*A) (B*B) := by
  let K := GaussianRadiusExponentialName.index one p
  have b : Γ ⊢[PRAAx] le two (GaussianRationalExponentialTail.cutoff one (p+num 4)) := by
    unfold GaussianRationalExponentialTail.cutoff ExponentialTail.Nt
    ipra_le 𝔞 p+10
  have hK : Γ ⊢[PRAAx] le one K := (succ_monus_succ one K).eqSymm.eqTrans
    (le_congr (.eqRefl _) (GaussianRationalExponentialTail.last_successor one (p+num 4)).eqSymm b)
  have e : Γ ⊢[PRAAx] GaussianRadiusExponentialName.sample constantF one p q ≐ scalarSum q K :=
    (GaussianRadiusExponentialName.sample_at constantF one p q).eqTrans
      (GaussianRationalFiniteSum.sum_index_congr scalarBody (.eqRefl _)
        (constant_at (GaussianRadiusExponentialName.inputPrecision one p) q))
  exact GaussianRationalDistanceOrder.distance_congr e.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (original_finite_linear_remainder q A B K hb ha hq hc hK)

theorem original_constant_exponential_linear_remainder_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((le one (var 2) ⋏ le (var 1) (var 2)) ⟶ bounded (var 0) (var 1) (var 2) ⟶ canonical (var 0) ⟶
      distanceBounded (GaussianRadiusExponentialName.sample constantF one (var 3) (var 0))
        (qadd qone (var 0)) (var 1*var 1) (var 2*var 2)) :=
  closeUniv 4 (.impI (.impI (.impI (original_constant_exponential_linear_remainder _ _ _ _
    hyp2.andE₁ hyp2.andE₂ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianExponentialLinearRemainder
