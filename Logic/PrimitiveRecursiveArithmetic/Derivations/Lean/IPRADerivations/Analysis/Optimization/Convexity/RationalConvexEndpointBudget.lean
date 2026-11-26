import IPRADerivations.Analysis.Optimization.Convexity.RationalConvexSecants

/-!
# The source local modulus from two precision-zero samples

The input is the original primitive-recursive rational sampler. The program
queries it at the two original endpoints and precision zero, takes the
ceiling of the larger absolute sample, and adds one. The endpoint bound
at any later precision follows from the original regularity inequality.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalConvexEndpointBudget

open_ipra
open RationalCubeMidpoint (fraction fraction_represents)
open RationalSupMetric (numeratorOf denominatorOf)
open RationalArgmin (rationalLE denominator_positive)
open RationalArithmetic (represents add maximum maximum_bounds)
open RationalValueBounds (upper crossLeft upper_order_right)
open RationalConvexSecants (nonnegative naturalNumerator nonnegative_representation)
open RationalConvexSecantWeights (leftPoint rightPoint modulus)
open GaussianRationalSyntheticBounds (natCode natCode_represents natCode_nonnegative natCode_add add_monotone)
open GaussianDescentClockArithmetic (ceiling ceiling_lower)
open LeanProofs.IPRA.Foundations.GapDecision (zabs)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def absolute (q : PTm n) : PTm n := fraction (zabs (numeratorOf q)) (denominatorOf q)
def observedBound (a b : PTm n) : PTm n := maximum (absolute a) (absolute b)
def coarseCeiling (a b : PTm n) : PTm n :=
  ceiling (naturalNumerator (observedBound a b)) (denominatorOf (observedBound a b))
def coarseBudget (a b : PTm n) : PTm n := succ (coarseCeiling a b)
def sample (A : PR 3) (q p x : PTm n) : PTm n := ap3 A q p x
def M (A : PR 3) (D P Q x : PTm n) : PTm n :=
  coarseBudget (sample A (leftPoint D P) zero x) (sample A (rightPoint D Q) zero x)
def localModulus (A : PR 3) (D P Q k x : PTm n) : PTm n := modulus D P (M A D P Q x) k

theorem absolute_nonnegative (q : PTm n) : Γ ⊢[PRAAx] nonnegative (absolute q) := by
  apply GaussianRationalMetric.comparison_of_cleared _ _ zero (zabs (numeratorOf q)) one (denominatorOf q)
    (le_refl _) (denominator_positive q) (natCode_represents zero) (fraction_represents _ _ (denominator_positive q))
  exact le_congr (mul_zero _).eqSymm (.eqRefl _) (zero_le _)

theorem below_absolute (q : PTm n) : Γ ⊢[PRAAx] rationalLE q (absolute q) := by
  let u := numeratorOf q
  let D := denominatorOf q
  apply RationalArithmetic.order_of_representations q (absolute q) u (ZT.ofNat (zabs u)) D D
    (RationalRepresentations.represents_self q) (fraction_represents _ _ (denominator_positive q))
    (denominator_positive q) (denominator_positive q)
  apply zle_of_toZ (two*D*monus u.neg u.pos)
  have balance : Γ ⊢[PRAAx] u.pos+monus u.neg u.pos ≐ u.neg+monus u.pos u.neg := by
    refine .orE (le_total u.pos u.neg) ?_ ?_
    · have h : (le u.pos u.neg :: Γ) ⊢[PRAAx] le u.pos u.neg := Prf.hyp0
      exact (eq_add_of_le h).eqSymm.eqTrans ((add_zero _).eqSymm.eqTrans (congrAdd (.eqRefl _) h.eqSymm))
    · have h : (le u.neg u.pos :: Γ) ⊢[PRAAx] le u.neg u.pos := Prf.hyp0
      exact (congrAdd (.eqRefl _) h).eqTrans ((add_zero _).eqTrans (eq_add_of_le h))
  have e := natEq balance
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [ZT.toZ,zabs,LeanProofs.IPRA.Probability.Variance.ad]
  ipra_simps
  linear_combination 𝔞 D*e

theorem observed_nonnegative (a b : PTm n) : Γ ⊢[PRAAx] nonnegative (observedBound a b) :=
  RationalArgmin.transitive (absolute_nonnegative a) (maximum_bounds (absolute a) (absolute b)).andE₁

theorem original_observation_bound (a b : PTm n) : Γ ⊢[PRAAx]
    rationalLE a (natCode (coarseCeiling a b)) ⋏ rationalLE b (natCode (coarseCeiling a b)) := by
  let C := observedBound a b
  let J := coarseCeiling a b
  have hc : Γ ⊢[PRAAx] rationalLE C (natCode J) := by
    apply GaussianRationalMetric.comparison_of_cleared _ _ _ _ (denominatorOf C) one
      (denominator_positive C) (le_refl _) (nonnegative_representation C (observed_nonnegative a b))
      (natCode_represents J)
    exact le_congr (one_mul _).eqSymm (mul_comm _ _) (ceiling_lower _ _ (denominator_positive C))
  have h := maximum_bounds (Γ := Γ) (absolute a) (absolute b)
  exact .andI (RationalArgmin.transitive (below_absolute a) (RationalArgmin.transitive h.andE₁ hc))
    (RationalArgmin.transitive (below_absolute b) (RationalArgmin.transitive h.andE₂ hc))

/-- One-sided metric bounds give the corresponding addition inequality on the original codes. -/
theorem order_of_upper (a b U V : PTm n) (hV : Γ ⊢[PRAAx] le one V)
    (h : Γ ⊢[PRAAx] upper a b U V) :
    Γ ⊢[PRAAx] rationalLE a (add b (fraction U V)) := by
  let A := denominatorOf a
  let B := denominatorOf b
  have hb := RationalRepresentations.represents_add (Γ := Γ) b (fraction U V) _ _ B V
    (RationalRepresentations.represents_self b) (fraction_represents U V hV)
  apply RationalArithmetic.order_of_representations _ _ _ _ A (B*V) (RationalRepresentations.represents_self a)
    hb (denominator_positive a) (RationalAlgebra.positive_product (denominator_positive b) hV)
  apply zle_of_toZ (monus (V*crossLeft b a+U*A*B) (V*crossLeft a b))
  have e := natEq (eq_add_of_le h)
  simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [ZT.toZ]
  unfold crossLeft at e ⊢
  dsimp only [A,B] at e ⊢
  ipra_simps
  linear_combination -e

theorem move_integer_unit (J V : PTm n) (hV : Γ ⊢[PRAAx] le one V) : Γ ⊢[PRAAx]
    add (natCode J) (fraction (V+one) V) ≐ add (natCode (succ J)) (fraction one V) := by
  have jl := RationalRepresentations.represents_add (Γ := Γ) (natCode J) (fraction (V+one) V) _ _ one V
    (natCode_represents J) (fraction_represents _ V hV)
  have jr := RationalRepresentations.represents_add (Γ := Γ) (natCode (succ J)) (fraction one V) _ _ one V
    (natCode_represents (succ J)) (fraction_represents _ V hV)
  have h := RationalAlgebra.positive_product (le_refl one) hV
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.add_guard _ _)
    (RationalArithmetic.add_guard _ _) jl jr h h
  ipra_lc

/-- The supplied upper regularity instance at (p,0) produces the original coarse bound plus (2^{-p}). -/
theorem endpoint_sample_bound (a b q s p : PTm n) (h₀ : Γ ⊢[PRAAx] rationalLE q (natCode (coarseCeiling a b)))
    (h : Γ ⊢[PRAAx] upper s q (pw two p+one) (pw two p)) :
    Γ ⊢[PRAAx] rationalLE s (add (natCode (coarseBudget a b)) (fraction one (pw two p))) := by
  have hp : Γ ⊢[PRAAx] le one (pw two p) := GaussianPolynomialPerturbation.power_positive two p (le_succ_self one)
  exact RationalArgmin.rationalLE_congr (.eqRefl _) (move_integer_unit (coarseCeiling a b) (pw two p) hp)
    (order_of_upper _ _ _ _ hp (upper_order_right _ _ _ _ _ h h₀))

theorem actual_two_endpoint_sample_bounds (A : PR 3) (D P Q p x : PTm n)
    (ha : Γ ⊢[PRAAx] upper (sample A (leftPoint D P) p x) (sample A (leftPoint D P) zero x) (pw two p+one) (pw two p))
    (hb : Γ ⊢[PRAAx] upper (sample A (rightPoint D Q) p x) (sample A (rightPoint D Q) zero x) (pw two p+one) (pw two p)) :
    Γ ⊢[PRAAx] rationalLE (sample A (leftPoint D P) p x) (add (natCode (M A D P Q x)) (fraction one (pw two p))) ⋏
      rationalLE (sample A (rightPoint D Q) p x) (add (natCode (M A D P Q x)) (fraction one (pw two p))) := by
  let a := sample A (leftPoint D P) zero x
  let b := sample A (rightPoint D Q) zero x
  have h := original_observation_bound (Γ := Γ) a b
  exact .andI (endpoint_sample_bound a b a _ p h.andE₁ ha) (endpoint_sample_bound a b b _ p h.andE₂ hb)

def output (A : PR 3) (D P Q k x : PTm n) : PTm n :=
  pairT (leftPoint D P) (pairT (rightPoint D Q) (pairT (M A D P Q x) (localModulus A D P Q k x)))

def outputF (A : PR 3) : PR 5 := PTm.toPR (output A (var 0) (var 1) (var 2) (var 3) (var 4))
def run (A : PR 3) (D P Q k x : PTm n) : PTm n := app (outputF A) ![D,P,Q,k,x]

@[simp] theorem subst_absolute {j : ℕ} (σ : Fin n → PTm j) (q : PTm n) :
    Syn.subst σ (absolute q) = absolute (Syn.subst σ q) := by
  unfold absolute
  rw [RationalCubeMidpoint.subst_fraction,LeanProofs.IPRA.Foundations.GapDecision.subst_zabs,
    RationalSupMetric.subst_numeratorOf,RationalSupMetric.subst_denominatorOf]

ipra_subst coarseBudget [coarseCeiling, observedBound, naturalNumerator, numeratorOf]

ipra_subst M [sample, RationalConvexSecantWeights.leftPoint, RationalConvexSecantWeights.rightPoint]

ipra_subst output [localModulus, RationalConvexSecantWeights.leftPoint, RationalConvexSecantWeights.rightPoint, RationalConvexSecantWeights.modulus, RationalConvexSecantWeights.budget, RationalConvexSecantWeights.margin, LeanProofs.IPRA.Foundations.FiniteObservations.MetricKernel.meet]

theorem program_at (A : PR 3) (D P Q k x : PTm n) : Γ ⊢[PRAAx] run A D P Q k x ≐ output A D P Q k x := by
  simpa only [run,outputF,subst_output,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using
    toPR_eq (Γ := Γ) (output A (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![D,P,Q,k,x]

theorem returned_budget (A : PR 3) (D P Q k x : PTm n) :
    Γ ⊢[PRAAx] fstT (sndT (sndT (run A D P Q k x))) ≐ M A D P Q x :=
  ((congrFst (congrSnd (congrSnd (program_at A D P Q k x)))).eqTrans
    ((congrFst (congrSnd (snd_pair _ _))).eqTrans (congrFst (snd_pair _ _)))).eqTrans (fst_pair _ _)

theorem returned_modulus (A : PR 3) (D P Q k x : PTm n) :
    Γ ⊢[PRAAx] sndT (sndT (sndT (run A D P Q k x))) ≐ localModulus A D P Q k x :=
  ((congrSnd (congrSnd (congrSnd (program_at A D P Q k x)))).eqTrans
    ((congrSnd (congrSnd (snd_pair _ _))).eqTrans (congrSnd (snd_pair _ _)))).eqTrans (snd_pair _ _)

theorem actual_coarse_endpoint_observation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (rationalLE (var 0) (natCode (coarseCeiling (var 0) (var 1))) ⋏
      rationalLE (var 1) (natCode (coarseCeiling (var 0) (var 1)))) :=
  closeUniv 2 (original_observation_bound _ _)

theorem actual_endpoint_sample_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (rationalLE (var 2) (natCode (coarseCeiling (var 0) (var 1))) ⟶
      upper (var 3) (var 2) (pw two (var 4)+one) (pw two (var 4)) ⟶
      rationalLE (var 3) (add (natCode (coarseBudget (var 0) (var 1))) (fraction one (pw two (var 4))))) :=
  closeUniv 5 (.impI (.impI (endpoint_sample_bound _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_endpoint_modulus_program_closed (A : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run A (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output A (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at A _ _ _ _ _)

theorem actual_returned_endpoint_modulus_closed (A : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sndT (sndT (sndT (run A (var 0) (var 1) (var 2) (var 3) (var 4)))) ≐
      localModulus A (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (returned_modulus A _ _ _ _ _)

end LeanProofs.IPRA.Analysis.RationalConvexEndpointBudget
