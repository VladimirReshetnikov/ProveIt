import IPRADerivations.Analysis.Stirling.AllOrders.Covariance.GaussianStirlingAllOrderOuterCovariance

/-!
# Uniform rate for the sum of midpoint corrections

The first two terms use explicit bounds. Every later term is bounded
by the corresponding reciprocal power, whose finite tail has an
explicit antiderivative bound independent of the outer prefix length.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderMidpointPrefixRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalFiniteProduct (offset_at)
open GaussianRationalHorner (positive_product)
open GaussianRationalL1 (nonnegative_of_lower nonnegative_of_representation)
open GaussianRationalSyntheticBounds (add_monotone)
open GaussianStirlingAllOrderBernoulliEnvelope (cap cap_nonnegative)
open GaussianStirlingAllOrderFullGridCovariance (midpointCorrection)
open GaussianStirlingAllOrderKernel (multiply_zero_right)
open GaussianStirlingAllOrderMidpointCorrection (baseCap tailCap midpoint_base_bound midpoint_tail_bound)
open GaussianStirlingAllOrderOuterCovariance (midpointBody midpointPrefix midpoint_at midpoint_succ)
open GaussianStirlingAllOrderPanelPartsOuter (data)
open RationalAlgebra (add_congr add_commutative multiply_add multiply_associative multiply_congr)
open RationalArgmin (rationalLE rationalLE_congr transitive)
open RationalArithmetic (add multiply multiply_monotone multiply_guard)
open RationalFiniteSum (sum sum_zero term termwiseLE sum_monotone)
open RationalNonnegativePowers (fraction_congr)
open RationalReciprocalPowerTail (zero_fraction add_zero_right reciprocalPower potential tail reciprocal_congr sharp_tail)
open RationalSumLinearity (scaledBody scaled_term sum_homogeneous)
open RationalSumSegments (sum_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "z" => fraction zero one

def midpointBudget (m e : ℕ) (A B : PTm n) : PTm n :=
  add (add (baseCap m (num (e-1)) A B) (cap m)) (multiply (cap m) (potential (succ (num (e-1))) one))

@[simp] theorem subst_midpointBudget {l : ℕ} (σ : Fin n → PTm l) (m e : ℕ) (A B : PTm n) :
    Syn.subst σ (midpointBudget m e A B) = midpointBudget m e (Syn.subst σ A) (Syn.subst σ B) := by simp [midpointBudget]

private theorem degree_guard (e : ℕ) (he : 2≤e) : Γ ⊢[PRAAx] le two (succ (num (e-1) : PTm n)) := by
  have eq : succ (num (e-1) : PTm n) = num e := by
    change num ((e-1)+1) = num e
    congr 1
    omega
  rw [eq]
  exact Foundations.NumeralPrimes.num_le he

private theorem fraction_sign (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] GaussianPositiveRealArithmetic.sign (fraction one N) :=
  nonnegative_of_representation _ _ _ hN (fraction_represents one N hN)

private theorem weight_sign (m : ℕ) (S : PTm n) (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] GaussianPositiveRealArithmetic.sign (multiply (fraction one (S*num 4)) (cap m)) := by
  have hN : Γ ⊢[PRAAx] le one (S*num 4) := positive_product _ _ hS (by ipra_le 3)
  have zero_sign := nonnegative_of_representation (Γ := Γ) (z : PTm n) zero one (le_refl one)
    (fraction_represents _ _ (le_refl one))
  have h := multiply_monotone (fraction one (S*num 4)) _ _ (fraction_sign _ hN) (cap_nonnegative m)
  exact nonnegative_of_lower _ _ zero_sign (rationalLE_congr (multiply_zero_right _) (.eqRefl _) h)

private theorem initial_two (m e : ℕ) (A B S : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] rationalLE (midpointPrefix m e A B S two)
      (multiply (fraction one (S*num 4)) (add (baseCap m (num (e-1)) A B) (cap m))) := by
  let Q : PTm n := num (e-1)
  let c := fraction one (S*num 4)
  let x := midpointCorrection m Q A B S zero
  let y := midpointCorrection m Q A B S one
  have e₀ : Γ ⊢[PRAAx] midpointPrefix m e A B S zero ≐ z := by
    unfold midpointPrefix
    exact (RationalFiniteSum.sum_zero (midpointBody m e) (data A B S)).eqTrans zero_fraction.eqSymm
  have e₁ := (midpoint_succ m e A B S zero).eqTrans ((add_congr e₀ (.eqRefl x)).eqTrans
    ((add_commutative _ _).eqTrans (add_zero_right x (multiply_guard _ _))))
  have e₂ := (midpoint_succ m e A B S one).eqTrans (add_congr e₁ (.eqRefl y))
  have hx := (midpoint_base_bound m Q A B S zero hA hS).andE₂
  have hy := (midpoint_tail_bound m Q A B S one hA hS (le_refl one)).andE₂
  have unit : Γ ⊢[PRAAx] tailCap m Q one ≐ cap m :=
    (multiply_congr (.eqRefl _) (fraction_congr (.eqRefl _) (AnalyticNumberTheory.Order.pw_one_base _))).eqTrans
      (RationalSumConstants.multiply_one_right _ (GaussianStirlingAllOrderCenteredBernoulli.sample_canonical _ _ _
        (le_succ_self one)))
  exact rationalLE_congr e₂.eqSymm (multiply_add c _ _).eqSymm
    (add_monotone _ _ _ _ hx (rationalLE_congr (.eqRefl _) (multiply_congr (.eqRefl _) unit) hy))

private theorem shifted_tail (m e : ℕ) (he : 2≤e) (A B S L : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] rationalLE (sum (offB (midpointBody m e)) L (pairT two (data A B S)))
      (multiply (fraction one (S*num 4)) (multiply (cap m) (potential (succ (num (e-1))) one))) := by
  let c := fraction one (S*num 4)
  let g : PTm n := cap m
  let w := multiply c g
  let Q : PTm n := num (e-1)
  let D := succ Q
  let f := offB (midpointBody m e)
  let v := RationalReciprocalPowerTail.body
  let x := pairT two (data A B S)
  let y := RationalReciprocalPowerTail.data D one
  have h : Γ ⊢[PRAAx] termwiseLE f (scaledBody v) L x (pairT w y) := by
    refine .allI (.impI ?_)
    let sh (T : PTm n) := Syn.shift T
    let i : PTm (n+1) := var 0
    let Δ := lt i (sh L) :: Γ.map Fm.shift
    have ha : Δ ⊢[PRAAx] le one (sh A) := (by simpa [Fm.shift,Syn.shift,sh] using hA.shift :
      Γ.map Fm.shift ⊢[PRAAx] le one (sh A)).wk
    have hs : Δ ⊢[PRAAx] le one (sh S) := (by simpa [Fm.shift,Syn.shift,sh] using hS.shift :
      Γ.map Fm.shift ⊢[PRAAx] le one (sh S)).wk
    let Q' : PTm (n+1) := num (e-1)
    let c' := fraction one (sh S*num 4)
    let g' : PTm (n+1) := cap m
    let w' := multiply c' g'
    let j := two+i
    have hj : Δ ⊢[PRAAx] le one j := le_trans (le_succ_self one) (le_add_right _ _)
    have eq : Δ ⊢[PRAAx] succ (one+i) ≐ j := by unfold j; ipra_ring
    have lb := (offset_at (Γ := Δ) (midpointBody m e) two i (data (sh A) (sh B) (sh S))).eqTrans
      (midpoint_at m e (sh A) (sh B) (sh S) j)
    have rb := (scaled_term (Γ := Δ) v i w' (RationalReciprocalPowerTail.data (succ Q') one)).eqTrans
      ((multiply_congr (.eqRefl _) ((RationalReciprocalPowerTail.term_at (succ Q') one i).eqTrans
        (reciprocal_congr (.eqRefl _) eq))).eqTrans (multiply_associative c' g' _))
    have rate := (midpoint_tail_bound m Q' (sh A) (sh B) (sh S) j ha hs hj).andE₂
    have sx : sh x = pairT two (data (sh A) (sh B) (sh S)) := by simp [x,sh,Syn.shift,two,data]
    have sy : sh (pairT w y) = pairT w' (RationalReciprocalPowerTail.data (succ Q') one) := by
      simp [w,y,c,g,D,Q,sh,Syn.shift,w',c',g',Q']
    change Δ ⊢[PRAAx] rationalLE (term f i (sh x)) (term (scaledBody v) i (sh (pairT w y)))
    rw [sx,sy]
    exact rationalLE_congr lb.eqSymm rb.eqSymm rate
  have oneS := sum_monotone f (scaledBody v) L x (pairT w y) h
  have eSum := sum_homogeneous (Γ := Γ) v L w y
  have afterSum := rationalLE_congr (.eqRefl _) eSum oneS
  have power := sharp_tail (Γ := Γ) D one L (degree_guard e he) (le_refl one)
  have pulled := multiply_monotone w _ _ (weight_sign m S hS) power
  exact transitive afterSum (rationalLE_congr (.eqRefl _) (multiply_associative c g _) pulled)

theorem uniform_midpoint_prefix (m e : ℕ) (he : 2≤e) (A B S L : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] rationalLE (midpointPrefix m e A B S (succ (succ L)))
      (multiply (fraction one (S*num 4)) (midpointBudget m e A B)) := by
  let f := midpointBody m e
  let x := data A B S
  let c := fraction one (S*num 4)
  have hlength : Γ ⊢[PRAAx] sum f (succ (succ L)) x ≐ sum f (two+L) x := sum_congr f (by ipra_ring) (.eqRefl _)
  have split := hlength.eqTrans (RationalSumSegments.split f two L x)
  have bound := add_monotone _ _ _ _ (initial_two m e A B S hA hS) (shifted_tail m e he A B S L hA hS)
  let xCap := add (baseCap m (num (e-1)) A B) (cap m)
  let yCap : PTm n := multiply (cap m) (potential (succ (num (e-1))) one)
  have combine : Γ ⊢[PRAAx] add (multiply c xCap) (multiply c yCap) ≐ multiply c (midpointBudget m e A B) :=
    (multiply_add c xCap yCap).eqSymm
  exact rationalLE_congr split.eqSymm combine bound

theorem actual_original_midpoint_prefix_uniform_rate_closed (m e : ℕ) (he : 2≤e) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (le one (var 0) ⟶ le one (var 2) ⟶
        rationalLE (midpointPrefix m e (var 0) (var 1) (var 2) (succ (succ (var 3))))
          (multiply (fraction one (var 2*num 4)) (midpointBudget m e (var 0) (var 1)))) :=
  closeUniv 4 (.impI (.impI (uniform_midpoint_prefix m e he _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderMidpointPrefixRate
