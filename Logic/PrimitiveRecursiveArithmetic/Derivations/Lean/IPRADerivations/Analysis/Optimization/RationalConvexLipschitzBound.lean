import IPRADerivations.Analysis.Optimization.RationalConvexScheduledModulus
import IPRADerivations.Analysis.Optimization.RationalConvexCoarseIntervalBudget
import IPRADerivations.Analysis.Series.SignedTelescope

/-!
# The exact Lipschitz comparison for the source convex presentation

Work directly with the upper endpoints of the two input values and the
lower endpoint of the convex combination. The rational secant estimate
has no sampling error. Nesting transports it to the requested intervals.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalConvexLipschitzBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (monus)
open RationalArgmin (rationalLE denominator_positive)
open RationalSupMetric (numeratorOf denominatorOf)
open RationalConvexSecants (naturalNumerator nonnegative scale rescaled_representation
  multiply_natural_representation add_natural_representation compare_same_to_natural)
open RationalConvexSecantWeights (secant_with_error margin left_width right_width left_margin right_margin displacement)
open RationalConvexArguments (arguments enlargedDen endpointDen firstNumerator secondNumerator interiorNumerator original_geometry)
open RationalOriginalConvexModulus (sourceLeft sourceRight source_queries)
open RationalConvexSourceRLC (rule source_secants leftWeightFor rightWeightFor shiftWeightFor positive_fraction)
open RationalConvexScheduledModulus (positivePresentation presentation_at inInterval)
open RationalNestedConvexModulus (left_weight_positive right_weight_positive)
open RationalConvexEndpointBudget (M)
open RationalNestedIntervals (centerF)
open RationalConvexCoarseIntervalBudget (original_two_upper_endpoint_bounds)
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Probability.MedianWeighted (ad_mul)
open LeanProofs.IPRA.Foundations.GapDecision (zabs)
open RationalConvexArguments (first_numerator_positive endpoint_den_positive)
open RationalConvexSecantWeights (margin_positive)
open GaussianRationalSyntheticBounds (natCode_nonnegative)
open RationalArithmetic (recode)
open RationalArgmin (transitive)
open RationalMultiplicativeConvexity (ordinary weighted)
open GaussianRationalSyntheticBounds (natCode)
open RationalConvexFiniteModulus (integer_representation)
open RationalValueBounds (upper cross crossLeft cross_absolute)
open RationalNestedIntervals (read regular)
open RationalNestedConvexModulus (presented witnessIndex witnessExponent lower_nonnegative upper_nonnegative)
open RationalConvexScheduledModulus (threePoints cutoff cutoff_bounds cutoff_le_schedule witnesses_at sourceSchedule)
open RationalConvexSourceRLC (schedule)
open RationalIntervalPowerComparison (centerOrder multiplicative_of_center_order)
open RationalMultiplicativeConvexity (multiplicative_to_ordinary)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem exact_rational_secant (r t δ A B C M : PTm n)
    (hδ : Γ ⊢[PRAAx] le δ (r+t))
    (ha : Γ ⊢[PRAAx] nonnegative A) (hb : Γ ⊢[PRAAx] nonnegative B)
    (hc : Γ ⊢[PRAAx] nonnegative C) (hm : Γ ⊢[PRAAx] rationalLE B (natCode M))
    (h : Γ ⊢[PRAAx] ordinary r t A B C) : Γ ⊢[PRAAx] upper C A (M*t) δ := by
  let a := denominatorOf A
  let b := denominatorOf B
  let c := denominatorOf C
  let J := a*b*c
  let U := naturalNumerator A*(b*c)
  let V := naturalNumerator B*(a*c)
  let W := naturalNumerator C*(a*b)
  have hJ : Γ ⊢[PRAAx] le one J := RationalAlgebra.positive_product
    (RationalAlgebra.positive_product (denominator_positive A) (denominator_positive B))
    (denominator_positive C)
  have hU := rescaled_representation A (b*c) J ha (by dsimp only [J,a]; ipra_ring)
  have hV := rescaled_representation B (a*c) J hb (by dsimp only [J,b]; ipra_ring)
  have hW := rescaled_representation C (a*b) J hc (by dsimp only [J,c]; ipra_ring)
  have hB := compare_same_to_natural B (natCode M) V (M*J) J hJ hV (integer_representation M J) hm
  have hC := compare_same_to_natural (scale (r+t) C) (weighted r t A B) ((r+t)*W) (r*U+t*V) J hJ
    (multiply_natural_representation (r+t) C W J hW)
    (add_natural_representation _ _ _ _ J hJ (multiply_natural_representation r A U J hU)
      (multiply_natural_representation t B V J hV)) h
  have hz := le_congr (.eqRefl _) (by ipra_ring : Γ ⊢[PRAAx] r*U+t*V ≐ r*U+t*V+(r+t)*zero) hC
  have hd := secant_with_error (r+t) t r δ U W V (M*J) zero (add_comm _ _) hz hB hδ
  have hD : Γ ⊢[PRAAx] le (δ*W) (δ*U+M*t*J) := le_congr (.eqRefl _) (by ipra_ring) hd
  apply RationalCubeInfimumIntervals.upper_of_representations C A (ZT.ofNat W) (ZT.ofNat U) J J (M*t) δ
    hJ hJ hW hU
  apply zle_of_toZ (J*monus (δ*U+M*t*J) (δ*W))
  have e := natEq (eq_add_of_le hD)
  simp only [ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_ofNat]
  ipra_simps
  linear_combination -Groth.ι (IPRA.Q.mk Γ J)*e

theorem actual_exact_rational_secant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le (var 2) (var 0+var 1) ⟶
      (nonnegative (var 3) ⋏ (nonnegative (var 4) ⋏ (nonnegative (var 5) ⋏ rationalLE (var 4) (natCode (var 6))))) ⟶
      ordinary (var 0) (var 1) (var 3) (var 4) (var 5) ⟶ upper (var 5) (var 3) (var 6*var 1) (var 2)) :=
  closeUniv 7 (.impI (.impI (.impI (exact_rational_secant _ _ _ _ _ _ _
    hyp2 Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂.andE₁
    Prf.hyp1.andE₂.andE₂.andE₂ Prf.hyp0))))

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- Use the two exact input upper endpoints and the exact output lower endpoint. -/
theorem exact_named_secant (L U : PR 3) (W : PR 2) (A B C r t δ M i j x : PTm n)
    (h : Γ ⊢[PRAAx] threePoints L U W A B C x) (hr : Γ ⊢[PRAAx] le one r)
    (hδ : Γ ⊢[PRAAx] le δ (r+t))
    (hm : Γ ⊢[PRAAx] rationalLE (read U B (schedule (sourceSchedule U W) A B C r t x+i+j) x) (natCode M))
    (hc : Γ ⊢[PRAAx] centerOrder L U A B C r t (schedule (sourceSchedule U W) A B C r t x) x) :
    Γ ⊢[PRAAx] upper (read L C i x) (read U A j x) (M*t) δ := by
  let o := schedule (sourceSchedule U W) A B C r t x
  let p := o+i+j
  have hop : Γ ⊢[PRAAx] le o p := by dsimp only [p]; ipra_le 𝔟 i+𝔟 j
  have hip : Γ ⊢[PRAAx] le i p := by dsimp only [p]; ipra_le 𝔟 o+𝔟 j
  have hjp : Γ ⊢[PRAAx] le j p := by dsimp only [p]; ipra_le 𝔟 o+𝔟 i
  have hl := cutoff_le_schedule (Γ := Γ) U W A B C r t x
  have bounds := cutoff_bounds (Γ := Γ) W A B C x
  have wit := witnesses_at L U W A B C x o h hl
  have a := h.andE₁
  have b := h.andE₂.andE₁
  have c := h.andE₂.andE₂
  have apos := upper_nonnegative L U W A p x a (le_trans (le_trans bounds.andE₁ hl) hop)
  have bpos := upper_nonnegative L U W B p x b (le_trans (le_trans bounds.andE₂.andE₁ hl) hop)
  have cpos := lower_nonnegative L U W C p x c (le_trans (le_trans bounds.andE₂.andE₂ hl) hop)
  have mul := multiplicative_of_center_order L U A B C r t o p (witnessExponent W A x)
    (witnessExponent W B x) (witnessExponent W C x) x a.andE₁ b.andE₁ c.andE₁
    wit.andE₂.andE₂.andE₂.andE₁ wit.andE₂.andE₂.andE₂.andE₂.andE₁ wit.andE₂.andE₂.andE₂.andE₂.andE₂ hop hc
  have proof := exact_rational_secant r t δ (read U A p x) (read U B p x) (read L C p x) M hδ
    apos bpos cpos hm (multiplicative_to_ordinary _ _ _ _ _ hr apos bpos cpos mul)
  exact RationalValueBounds.upper_order_left _ _ _ _ _ (RationalNestedIntervals.nesting L U C i p x c.andE₁ hip).andE₁
    (RationalValueBounds.upper_order_right _ _ _ _ _ proof (RationalNestedIntervals.nesting L U A j p x a.andE₁ hjp).andE₂)

/-- The absolute argument difference has the common scale of the secants. -/
def distanceWord (a b u v : PTm n) : PTm n :=
  two*ad (interiorNumerator a b u v) (interiorNumerator a b v u)

def distanceBudget (L U : PR 3) (a b u v x : PTm n) : PTm n :=
  M (centerF L U) (endpointDen a b) (firstNumerator a b) (secondNumerator a b) x*distanceWord a b u v

def marginWord (a b u v : PTm n) : PTm n :=
  margin (endpointDen a b) (firstNumerator a b)*endpointDen u v

def crossBounds (L U : PR 3) (a b u v i j x : PTm n) : Fm PTm n :=
  upper (read L (recode u) i x) (read U (recode v) j x) (distanceBudget L U a b u v x) (marginWord a b u v) ⋏
    upper (read L (recode v) j x) (read U (recode u) i x) (distanceBudget L U a b u v x) (marginWord a b u v)

theorem ordered_distance_word (a b u v : PTm n)
    (h : Γ ⊢[PRAAx] le (interiorNumerator a b u v) (interiorNumerator a b v u)) :
    Γ ⊢[PRAAx] shiftWeightFor a b u v ≐ distanceWord a b u v := by
  unfold shiftWeightFor displacement distanceWord
  exact congrMul (.eqRefl _) ((add_zero _).eqSymm.eqTrans (by
    exact (congrAdd (.eqRefl _) h.eqSymm).eqTrans (add_comm _ _)))

theorem distance_word_on_original_codes (a b u v : PTm n)
    (hu : Γ ⊢[PRAAx] nonnegative u) (hv : Γ ⊢[PRAAx] nonnegative v) :
    Γ ⊢[PRAAx] distanceWord a b u v ≐ two*endpointDen a b*zabs (cross u v) := by
  let D := endpointDen a b
  let A := naturalNumerator u*denominatorOf v
  let B := naturalNumerator v*denominatorOf u
  have eu := natEq (eq_add_of_le (GaussianRationalL1.nonnegative_of_lower _ _ (natCode_nonnegative zero) hu))
  have ev := natEq (eq_add_of_le (GaussianRationalL1.nonnegative_of_lower _ _ (natCode_nonnegative zero) hv))
  have r : Γ ⊢[PRAAx] crossLeft u v+B ≐ A+crossLeft v u := by
    apply deriveNat
    dsimp only [A,B,crossLeft,naturalNumerator]
    ipra_simps
    linear_combination 𝔟 (denominatorOf v)*eu-𝔟 (denominatorOf u)*ev
  have c : Γ ⊢[PRAAx] zabs (cross u v) ≐ ad A B :=
    (cross_absolute u v).eqTrans (SignedTelescope.ad_eq_of_cross r)
  have ea : Γ ⊢[PRAAx] interiorNumerator a b u v ≐ D*A := by dsimp only [interiorNumerator,D,A]; ipra_ring
  have eb : Γ ⊢[PRAAx] interiorNumerator a b v u ≐ D*B := by dsimp only [interiorNumerator,D,B]; ipra_ring
  have e : Γ ⊢[PRAAx] ad (interiorNumerator a b u v) (interiorNumerator a b v u) ≐ D*zabs (cross u v) :=
    (congrAdd (congrMonus ea eb) (congrMonus eb ea)).eqTrans
      ((ad_mul D A B).eqTrans (congrMul (.eqRefl _) c.eqSymm))
  exact (congrMul (.eqRefl two) e).eqTrans (by dsimp only [D]; ipra_ring)

theorem original_margin_word_positive (a b u v : PTm n)
    (h : Γ ⊢[PRAAx] inInterval a b u v) : Γ ⊢[PRAAx] le one (marginWord a b u v) :=
  RationalAlgebra.positive_product
    (margin_positive _ _ (endpoint_den_positive a b) (first_numerator_positive a b h.andE₁))
    (endpoint_den_positive u v)

theorem actual_original_distance_word_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (nonnegative (var 2) ⟶ nonnegative (var 3) ⟶
      distanceWord (var 0) (var 1) (var 2) (var 3) ≐
        two*endpointDen (var 0) (var 1)*zabs (cross (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (distance_word_on_original_codes _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_original_margin_word_positive_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (inInterval (var 0) (var 1) (var 2) (var 3) ⟶ le one (marginWord (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (original_margin_word_positive _ _ _ _ Prf.hyp0))

theorem original_ordered_lipschitz (L U : PR 3) (W : PR 2) (a b u v i j x : PTm n)
    (h : Γ ⊢[PRAAx] arguments a b u v) (hp : Γ ⊢[PRAAx] positivePresentation L U W x)
    (hc : Γ ⊢[PRAAx] rule L U (sourceSchedule U W) x) :
    Γ ⊢[PRAAx] crossBounds L U a b u v i j x := by
  let D := enlargedDen a b u v
  let P := firstNumerator a b*endpointDen u v
  let Q := secondNumerator a b*endpointDen u v
  let X := interiorNumerator a b u v
  let Y := interiorNumerator a b v u
  let A := sourceLeft a
  let B := sourceRight b
  let C := recode u
  let E := recode v
  let t := shiftWeightFor a b u v
  let r := leftWeightFor a b u v
  let s := rightWeightFor a b u v
  let S := sourceSchedule U W
  let cap := M (centerF L U) (endpointDen a b) (firstNumerator a b) (secondNumerator a b) x
  have g := original_geometry a b u v h
  have eq := source_queries a b u v h
  have hD := g.andE₁
  have hP := g.andE₂.andE₁
  have hPX := g.andE₂.andE₂.andE₁
  have hXY := g.andE₂.andE₂.andE₂.andE₁
  have hYQ := g.andE₂.andE₂.andE₂.andE₂
  have hX := le_trans hP hPX
  have hY := le_trans hX hXY
  have hQ := le_trans hY hYQ
  have pa := presentation_at L U W A x hp (positive_fraction P (two*D) A hP
    (RationalAlgebra.positive_product (le_succ_self one) hD) eq.andE₁)
  have pb := presentation_at L U W B x hp (positive_fraction (Q+D) D B (le_trans hQ (le_add_right _ _)) hD eq.andE₂.andE₁)
  have pc := presentation_at L U W C x hp (positive_fraction X D C hX hD eq.andE₂.andE₂.andE₁)
  have pe := presentation_at L U W E x hp (positive_fraction Y D E hY hD eq.andE₂.andE₂.andE₂)
  have hna : Γ ⊢[PRAAx] nonnegative a := le_of_lt h.andE₁
  have hnb : Γ ⊢[PRAAx] nonnegative b := transitive hna (transitive h.andE₂.andE₁ (transitive h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂))
  have cap_at (p : PTm _) := original_two_upper_endpoint_bounds L U a b p x hna hnb pa.andE₁ pb.andE₁
  have li := (cap_at (schedule S E A C r t x+i+j)).andE₁
  have ri := (cap_at (schedule S C B E s t x+j+i)).andE₂
  have dl : Γ ⊢[PRAAx] le (margin D P) (r+t) :=
    le_congr (.eqRefl _) ((left_width P X Y hPX hXY).eqTrans (add_comm _ _))
      (left_margin D P Y (le_trans hPX hXY))
  have dr : Γ ⊢[PRAAx] le (margin D P) (s+t) :=
    le_congr (.eqRefl _) ((right_width D Q X Y hXY hYQ).eqTrans (add_comm _ _))
      (right_margin D P Q X (le_trans hXY hYQ))
  have rules := source_secants L U S a b u v x h hc
  have l := exact_named_secant L U W E A C r t (margin D P) cap i j x (.andI pe (.andI pa pc))
    (left_weight_positive P X hP hPX) dl li rules.andE₁
  have r' := exact_named_secant L U W C B E s t (margin D P) cap j i x (.andI pc (.andI pb pe))
    (right_weight_positive D Q Y hD hYQ) dr ri rules.andE₂
  have eb := congrMul (.eqRefl cap) (ordered_distance_word a b u v hXY)
  have em := RationalConvexClockRescale.margin_rescale (Γ := Γ) (endpointDen a b) (firstNumerator a b) (endpointDen u v)
  exact .andI (RationalValueBounds.upper_congr (.eqRefl _) (.eqRefl _) eb em l)
    (RationalValueBounds.upper_congr (.eqRefl _) (.eqRefl _) eb em r')

theorem original_lipschitz (L U : PR 3) (W : PR 2) (a b u v i j x : PTm n)
    (h : Γ ⊢[PRAAx] inInterval a b u v) (hp : Γ ⊢[PRAAx] positivePresentation L U W x)
    (hc : Γ ⊢[PRAAx] rule L U (sourceSchedule U W) x) :
    Γ ⊢[PRAAx] crossBounds L U a b u v i j x := by
  refine .orE (RationalArgmin.total u v) ?_ ?_
  · have ho := h.wk (ψ := rationalLE u v)
    exact original_ordered_lipschitz L U W a b u v i j x
      (.andI ho.andE₁ (.andI ho.andE₂.andE₁ (.andI Prf.hyp0 ho.andE₂.andE₂.andE₂.andE₂))) hp.wk hc.wk
  · have ho := h.wk (ψ := rationalLE v u)
    have bound := original_ordered_lipschitz L U W a b v u j i x
      (.andI ho.andE₁ (.andI ho.andE₂.andE₂.andE₁ (.andI Prf.hyp0 ho.andE₂.andE₂.andE₂.andE₁))) hp.wk hc.wk
    have eb : (rationalLE v u :: Γ) ⊢[PRAAx] distanceBudget L U a b v u x ≐ distanceBudget L U a b u v x :=
      congrMul (.eqRefl _) (congrMul (.eqRefl _) (add_comm _ _))
    have em : (rationalLE v u :: Γ) ⊢[PRAAx] marginWord a b v u ≐ marginWord a b u v :=
      congrMul (.eqRefl _) (mul_comm _ _)
    exact .andI (RationalValueBounds.upper_congr (.eqRefl _) (.eqRefl _) eb em bound.andE₂)
      (RationalValueBounds.upper_congr (.eqRefl _) (.eqRefl _) eb em bound.andE₁)

theorem original_rational_lipschitz_closed (L U : PR 3) (W : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (inInterval (var 0) (var 1) (var 2) (var 3) ⟶ positivePresentation L U W (var 6) ⟶
      rule L U (sourceSchedule U W) (var 6) ⟶ crossBounds L U (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (.impI (.impI (.impI (original_lipschitz L U W _ _ _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.RationalConvexLipschitzBound
