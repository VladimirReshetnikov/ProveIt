import IPRADerivations.Analysis.Optimization.Convexity.Moduli.RationalConvexScheduledModulus

/-!
# Ordinary named convexity from the original rational log-convexity rule

All rational arguments and numerical weights remain internal. A positive
total weight and two positive arguments force their exact barycenter to
be positive. The original scheduled rule then gives the exact weighted
comparison between any lower output interval and any two upper input
intervals. A zero first weight is handled by the same rule at swapped
arguments and swapped weights.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalPositiveNamedConvexity

open_ipra
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiRationalScaling (rationalLT)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open RationalArgmin (rationalLE rationalLE_congr denominator_positive left transitive)
open RationalSupMetric (denominatorOf)
open RationalConvexSecants (scale nonnegative naturalNumerator nonnegative_representation rescaled_representation
  multiply_natural_representation add_natural_representation)
open RationalMultiplicativeConvexity (weighted ordinary multiplicative_to_ordinary)
open RationalNamedLocalModulus (barycentric)
open RationalConvexArguments (positive_natural_representative)
open RationalConvexSourceRLC (rule instance_at positive_of_natural_representation schedule)
open RationalConvexScheduledModulus (positivePresentation presentation_at sourceSchedule cutoff_bounds cutoff_le_schedule witnesses_at)
open RationalNestedConvexModulus (upper_nonnegative lower_nonnegative witnessExponent)
open RationalNestedIntervals (read nesting)
open GaussianRationalSyntheticBounds (natCode natCode_congr natCode_nonnegative natCode_multiply add_monotone)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

def sourceInput (A B C r t : PTm n) : Fm PTm n :=
  rationalLT (natCode zero) A ⋏ (rationalLT (natCode zero) B ⋏
    (le one (r+t) ⋏ barycentric (r+t) r t A B C))

def weightedComparison (L U : PR 3) (A B C r t i j k x : PTm n) : Fm PTm n :=
  rationalLE (scale (r+t) (read L C i x)) (weighted r t (read U A j x) (read U B k x))

/-- Positivity of the weighted sum follows from the original two argument codes. -/
theorem weighted_positive (A B r t : PTm n)
    (ha : Γ ⊢[PRAAx] rationalLT (natCode zero) A)
    (hb : Γ ⊢[PRAAx] rationalLT (natCode zero) B)
    (hw : Γ ⊢[PRAAx] le one (r+t)) :
    Γ ⊢[PRAAx] rationalLT (natCode zero) (weighted r t A B) := by
  let a := denominatorOf A
  let b := denominatorOf B
  let D := a*b
  let U := naturalNumerator A*b
  let V := naturalNumerator B*a
  have aPos := positive_natural_representative A (naturalNumerator A) a (denominator_positive A)
    (nonnegative_representation A (le_of_lt ha)) ha
  have bPos := positive_natural_representative B (naturalNumerator B) b (denominator_positive B)
    (nonnegative_representation B (le_of_lt hb)) hb
  have up : Γ ⊢[PRAAx] le one U := RationalAlgebra.positive_product aPos (denominator_positive B)
  have vp : Γ ⊢[PRAAx] le one V := RationalAlgebra.positive_product bPos (denominator_positive A)
  have dp : Γ ⊢[PRAAx] le one D := RationalAlgebra.positive_product (denominator_positive A) (denominator_positive B)
  have hN : Γ ⊢[PRAAx] le one (r*U+t*V) := by
    ipra_le sl hw+𝔟 r*sl up+𝔟 t*sl vp
  have ru := rescaled_representation A b D (le_of_lt ha) (.eqRefl _)
  have rv := rescaled_representation B a D (le_of_lt hb) (mul_comm _ _)
  exact positive_of_natural_representation _ (r*U+t*V) D hN
    (add_natural_representation _ _ _ _ D dp
      (multiply_natural_representation r A U D ru) (multiply_natural_representation t B V D rv))

/-- No separate positivity premise for the barycenter is needed. -/
theorem barycenter_positive (A B C r t : PTm n) (h : Γ ⊢[PRAAx] sourceInput A B C r t) :
    Γ ⊢[PRAAx] rationalLT (natCode zero) C := by
  have positive := weighted_positive A B r t h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂.andE₁
  refine .orE (lt_or_le (left (natCode zero) C) (left C (natCode zero))) Prf.hyp0 ?_
  have negative := RationalArithmetic.multiply_monotone (natCode (r+t)) C (natCode zero)
    (natCode_nonnegative (r+t)) (Prf.hyp0 : (rationalLE C (natCode zero) :: Γ) ⊢[PRAAx] _)
  have zeroScale : (rationalLE C (natCode zero) :: Γ) ⊢[PRAAx] scale (r+t) (natCode zero) ≐ natCode zero :=
    (natCode_multiply _ _).eqTrans (natCode_congr (mul_zero _))
  have contradiction := rationalLE_congr h.andE₂.andE₂.andE₂.wk zeroScale negative
  exact le_lt_absurd _ contradiction positive.wk

theorem sourceInput_swap (A B C r t : PTm n) (h : Γ ⊢[PRAAx] sourceInput A B C r t) :
    Γ ⊢[PRAAx] sourceInput B A C t r := by
  have w : Γ ⊢[PRAAx] le one (t+r) := le_congr (.eqRefl _) (add_comm r t) h.andE₂.andE₂.andE₁
  have e : Γ ⊢[PRAAx] barycentric (t+r) t r B A C :=
    (RationalAlgebra.multiply_congr (natCode_congr (add_comm t r)) (.eqRefl C)).eqTrans
      (h.andE₂.andE₂.andE₂.eqTrans (RationalAlgebra.add_commutative _ _))
  exact .andI h.andE₂.andE₁ (.andI h.andE₁ (.andI w e))

theorem named_convexity_first_positive (L U : PR 3) (W : PR 2) (A B C r t i j k x : PTm n)
    (h : Γ ⊢[PRAAx] sourceInput A B C r t) (hr : Γ ⊢[PRAAx] le one r)
    (hp : Γ ⊢[PRAAx] positivePresentation L U W x)
    (hc : Γ ⊢[PRAAx] rule L U (sourceSchedule U W) x) :
    Γ ⊢[PRAAx] weightedComparison L U A B C r t i j k x := by
  let o := schedule (sourceSchedule U W) A B C r t x
  let p := o+i+j+k
  have hop : Γ ⊢[PRAAx] le o p := by dsimp only [p]; ipra_le 𝔟 i+𝔟 j+𝔟 k
  have hip : Γ ⊢[PRAAx] le i p := by dsimp only [p]; ipra_le 𝔟 o+𝔟 j+𝔟 k
  have hjp : Γ ⊢[PRAAx] le j p := by dsimp only [p]; ipra_le 𝔟 o+𝔟 i+𝔟 k
  have hkp : Γ ⊢[PRAAx] le k p := by dsimp only [p]; ipra_le 𝔟 o+𝔟 i+𝔟 j
  have a := presentation_at L U W A x hp h.andE₁
  have b := presentation_at L U W B x hp h.andE₂.andE₁
  have c := presentation_at L U W C x hp (barycenter_positive A B C r t h)
  have pts := Prf.andI a (.andI b c)
  have hl := cutoff_le_schedule (Γ := Γ) U W A B C r t x
  have bounds := cutoff_bounds (Γ := Γ) W A B C x
  have wit := witnesses_at L U W A B C x o pts hl
  have apos := upper_nonnegative L U W A p x a (le_trans (le_trans bounds.andE₁ hl) hop)
  have bpos := upper_nonnegative L U W B p x b (le_trans (le_trans bounds.andE₂.andE₁ hl) hop)
  have cpos := lower_nonnegative L U W C p x c (le_trans (le_trans bounds.andE₂.andE₂ hl) hop)
  have co := Prf.impE (instance_at L U (sourceSchedule U W) A B C r t x hc) h
  have mul := RationalIntervalPowerComparison.multiplicative_of_center_order L U A B C r t o p
    (witnessExponent W A x) (witnessExponent W B x) (witnessExponent W C x) x
    a.andE₁ b.andE₁ c.andE₁ wit.andE₂.andE₂.andE₂.andE₁
    wit.andE₂.andE₂.andE₂.andE₂.andE₁ wit.andE₂.andE₂.andE₂.andE₂.andE₂ hop co
  have convex := multiplicative_to_ordinary r t _ _ _ hr apos bpos cpos mul
  have output := RationalConvexIntervalBounds.scale_monotone (r+t) _ _ (nesting L U C i p x c.andE₁ hip).andE₁
  have inputs := add_monotone _ _ _ _
    (RationalConvexIntervalBounds.scale_monotone r _ _ (nesting L U A j p x a.andE₁ hjp).andE₂)
    (RationalConvexIntervalBounds.scale_monotone t _ _ (nesting L U B k p x b.andE₁ hkp).andE₂)
  exact transitive output (transitive convex inputs)

theorem original_named_convexity (L U : PR 3) (W : PR 2) (A B C r t i j k x : PTm n)
    (h : Γ ⊢[PRAAx] sourceInput A B C r t)
    (hp : Γ ⊢[PRAAx] positivePresentation L U W x)
    (hc : Γ ⊢[PRAAx] rule L U (sourceSchedule U W) x) :
    Γ ⊢[PRAAx] weightedComparison L U A B C r t i j k x := by
  refine .orE (zero_or_succ r) ?_ ?_
  · have ht : ((r ≐ zero) :: Γ) ⊢[PRAAx] le one t :=
      le_congr (.eqRefl _) ((congrAdd Prf.hyp0 (.eqRefl t)).eqTrans (zero_add t)) h.andE₂.andE₂.andE₁.wk
    have result := named_convexity_first_positive L U W B A C t r i k j x
      (sourceInput_swap A B C r t h.wk) ht hp.wk hc.wk
    exact rationalLE_congr (RationalAlgebra.multiply_congr (natCode_congr (add_comm t r)) (.eqRefl _))
      (RationalAlgebra.add_commutative _ _) result
  · have hr : ((r ≐ ConciseIPRA.PTm.succ (LeanProofs.IPRA.PTm.pred r)) :: Γ) ⊢[PRAAx] le one r :=
      le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ _)
    exact named_convexity_first_positive L U W A B C r t i j k x h.wk hr hp.wk hc.wk

theorem original_positive_barycenter_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sourceInput (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ rationalLT (natCode zero) (var 2)) :=
  closeUniv 5 (.impI (barycenter_positive _ _ _ _ _ Prf.hyp0))

theorem original_named_positive_convexity_closed (L U : PR 3) (W : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (sourceInput (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ positivePresentation L U W (var 8) ⟶
      rule L U (sourceSchedule U W) (var 8) ⟶
      weightedComparison L U (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)) :=
  closeUniv 9 (.impI (.impI (.impI (original_named_convexity L U W _ _ _ _ _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.RationalPositiveNamedConvexity
