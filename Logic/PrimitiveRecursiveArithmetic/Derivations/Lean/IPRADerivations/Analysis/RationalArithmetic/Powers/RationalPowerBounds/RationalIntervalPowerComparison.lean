import IPRADerivations.Analysis.RationalArithmetic.Intervals.RationalNestedIntervals
import IPRADerivations.Analysis.Optimization.Convexity.Secants.RationalMultiplicativeConvexity
import IPRADerivations.Analysis.Inequalities.NonnegativeArithmetic.RationalNonnegativePowerOrder

/-!
# Cofinal midpoint order reflects the actual powered endpoints

The endpoint programs read the original interval arrays at k+2+offset.
Their powers and products are the actual nonnegative rational operations.
Original nesting and the three finite positivity witnesses give the needed
monotone enclosures. The stated comparison of these actual midpoints then
implies the exact fixed-precision multiplicative inequality, by a computed
rational gap query. Regularity of general transformed names is separate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalIntervalPowerComparison

open_ipra
open RationalArgmin (rationalLE transitive rationalLE_congr denominator_positive)
open RationalArithmetic (multiply)
open RationalConvexSecants (nonnegative nonnegative_representation naturalNumerator)
open RationalNestedIntervals (read regular positiveWitness)
open RationalSupMetric (denominatorOf)
open RationalValueBounds (upper crossLeft)
open RationalCubeGrid (scale)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiCenters (midpoint)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

def stage (offset k : PTm n) : PTm n := succ (succ k)+offset
def powerEndpoint (F : PR 3) (Z e offset k x : PTm n) : PTm n :=
  RationalMultiplicativeConvexity.power (read F Z (stage offset k) x) e
def productEndpoint (F : PR 3) (X Y a b offset k x : PTm n) : PTm n :=
  multiply (powerEndpoint F X a offset k x) (powerEndpoint F Y b offset k x)
def powerCenter (L U : PR 3) (Z e offset k x : PTm n) : PTm n :=
  midpoint (powerEndpoint L Z e offset k x) (powerEndpoint U Z e offset k x)
def productCenter (L U : PR 3) (X Y a b offset k x : PTm n) : PTm n :=
  midpoint (productEndpoint L X Y a b offset k x) (productEndpoint U X Y a b offset k x)
def centerOrder (L U : PR 3) (X Y Z a b offset x : PTm n) : Fm PTm n :=
  .all (upper
    (powerCenter L U (Syn.shift Z) (Syn.shift a+Syn.shift b) (Syn.shift offset) (var 0) (Syn.shift x))
    (productCenter L U (Syn.shift X) (Syn.shift Y) (Syn.shift a) (Syn.shift b)
      (Syn.shift offset) (var 0) (Syn.shift x)) one (scale (var 0)))

ipra_subst stage
@[simp] theorem subst_power {m : ℕ} (σ : Fin n → PTm m) (q e : PTm n) :
    Syn.subst σ (RationalMultiplicativeConvexity.power q e) =
      RationalMultiplicativeConvexity.power (Syn.subst σ q) (Syn.subst σ e) := by
  simp [RationalMultiplicativeConvexity.power,naturalNumerator,RationalSupMetric.denominatorOf,
    RationalSupMetric.numeratorOf]
ipra_subst powerEndpoint
ipra_subst productEndpoint
ipra_subst powerCenter
ipra_subst productCenter
ipra_subst centerOrder [scale, Syn.subst_shift, Syn.shift_subst]

theorem stage_cofinal (offset k : PTm n) : Γ ⊢[PRAAx] le k (stage offset k) := by
  unfold stage
  ipra_le 2+𝔟 offset

theorem stage_after_offset (offset k : PTm n) : Γ ⊢[PRAAx] le offset (stage offset k) := by
  unfold stage
  ipra_le 𝔟 k+2

theorem power_nonnegative (q e : PTm n) : Γ ⊢[PRAAx] nonnegative (RationalMultiplicativeConvexity.power q e) := by
  simpa [nonnegative,GaussianRationalSyntheticBounds.natCode,GaussianEuclideanDistanceName.fraction,
    RationalMultiplicativeConvexity.power] using
    RationalNonnegativePowers.power_nonnegative (Γ := Γ) (naturalNumerator q) (denominatorOf q) e
      (denominator_positive q)

theorem power_monotone (q r e : PTm n) (hq : Γ ⊢[PRAAx] nonnegative q)
    (hr : Γ ⊢[PRAAx] nonnegative r) (h : Γ ⊢[PRAAx] rationalLE q r) : Γ ⊢[PRAAx]
    rationalLE (RationalMultiplicativeConvexity.power q e) (RationalMultiplicativeConvexity.power r e) := by
  have raw := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (nonnegative_representation q hq) (nonnegative_representation r hr) h
  exact RationalNonnegativePowerOrder.power_order_preserve _ _ _ _ e
    (denominator_positive q) (denominator_positive r)
    (GaussianEuclideanDistanceName.fraction_order _ _ _ _ (denominator_positive q)
      (denominator_positive r) raw)

theorem product_monotone (A B C D : PTm n) (hB : Γ ⊢[PRAAx] nonnegative B)
    (hC : Γ ⊢[PRAAx] nonnegative C) (hAC : Γ ⊢[PRAAx] rationalLE A C)
    (hBD : Γ ⊢[PRAAx] rationalLE B D) : Γ ⊢[PRAAx] rationalLE (multiply A B) (multiply C D) := by
  have hb := GaussianRationalL1.nonnegative_of_lower _ _
    (GaussianRationalSyntheticBounds.natCode_nonnegative zero) hB
  have hc := GaussianRationalL1.nonnegative_of_lower _ _
    (GaussianRationalSyntheticBounds.natCode_nonnegative zero) hC
  have left := rationalLE_congr (RationalAlgebra.multiply_commutative _ _)
    (RationalAlgebra.multiply_commutative _ _) (RationalArithmetic.multiply_monotone B A C hb hAC)
  exact transitive left (RationalArithmetic.multiply_monotone C B D hc hBD)

theorem endpoints_nonnegative (L U : PR 3) (q offset p s x : PTm n)
    (h : Γ ⊢[PRAAx] regular L U q x) (hpos : Γ ⊢[PRAAx] positiveWitness L q offset s x)
    (hp : Γ ⊢[PRAAx] le offset p) : Γ ⊢[PRAAx]
    nonnegative (read L q p x) ⋏ nonnegative (read U q p x) := by
  have lower := transitive (RationalConvexFiniteModulus.eps_nonnegative s)
    (transitive hpos (RationalNestedIntervals.nesting L U q offset p x h hp).andE₁)
  exact .andI lower (transitive lower (RationalNestedIntervals.ordered L U q p x h))

theorem power_interval_ordered (L U : PR 3) (q e offset k s x : PTm n)
    (h : Γ ⊢[PRAAx] regular L U q x) (hpos : Γ ⊢[PRAAx] positiveWitness L q offset s x) :
    Γ ⊢[PRAAx] rationalLE (powerEndpoint L q e offset k x) (powerEndpoint U q e offset k x) := by
  have positive := endpoints_nonnegative L U q offset (stage offset k) s x h hpos (stage_after_offset _ _)
  exact power_monotone _ _ e positive.andE₁ positive.andE₂
    (RationalNestedIntervals.ordered L U q (stage offset k) x h)

theorem power_center_lower (L U : PR 3) (q e offset p k s x : PTm n)
    (h : Γ ⊢[PRAAx] regular L U q x) (hpos : Γ ⊢[PRAAx] positiveWitness L q offset s x)
    (hp : Γ ⊢[PRAAx] le offset p) (hk : Γ ⊢[PRAAx] le p (stage offset k)) : Γ ⊢[PRAAx]
    rationalLE (RationalMultiplicativeConvexity.power (read L q p x) e) (powerCenter L U q e offset k x) := by
  have positive := endpoints_nonnegative L U q offset p s x h hpos hp
  have later := endpoints_nonnegative L U q offset (stage offset k) s x h hpos (stage_after_offset _ _)
  exact transitive (power_monotone _ _ _ positive.andE₁ later.andE₁
      (RationalNestedIntervals.nesting L U q p (stage offset k) x h hk).andE₁)
    (RationalCubeInfimumName.midpoint_lower _ _ (power_interval_ordered L U q e offset k s x h hpos))

theorem product_interval_ordered (L U : PR 3) (X Y a b offset k sx sy x : PTm n)
    (hx : Γ ⊢[PRAAx] regular L U X x) (hy : Γ ⊢[PRAAx] regular L U Y x)
    (hpx : Γ ⊢[PRAAx] positiveWitness L X offset sx x)
    (hpy : Γ ⊢[PRAAx] positiveWitness L Y offset sy x) : Γ ⊢[PRAAx]
    rationalLE (productEndpoint L X Y a b offset k x) (productEndpoint U X Y a b offset k x) :=
  product_monotone _ _ _ _ (power_nonnegative _ _) (power_nonnegative _ _)
    (power_interval_ordered L U X a offset k sx x hx hpx)
    (power_interval_ordered L U Y b offset k sy x hy hpy)

theorem product_center_upper (L U : PR 3) (X Y a b offset p k sx sy x : PTm n)
    (hx : Γ ⊢[PRAAx] regular L U X x) (hy : Γ ⊢[PRAAx] regular L U Y x)
    (hpx : Γ ⊢[PRAAx] positiveWitness L X offset sx x)
    (hpy : Γ ⊢[PRAAx] positiveWitness L Y offset sy x)
    (hp : Γ ⊢[PRAAx] le offset p) (hk : Γ ⊢[PRAAx] le p (stage offset k)) : Γ ⊢[PRAAx]
    rationalLE (productCenter L U X Y a b offset k x)
      (multiply (RationalMultiplicativeConvexity.power (read U X p x) a)
        (RationalMultiplicativeConvexity.power (read U Y p x) b)) := by
  have xp := endpoints_nonnegative L U X offset p sx x hx hpx hp
  have yp := endpoints_nonnegative L U Y offset p sy x hy hpy hp
  have xk := endpoints_nonnegative L U X offset (stage offset k) sx x hx hpx (stage_after_offset _ _)
  have yk := endpoints_nonnegative L U Y offset (stage offset k) sy x hy hpy (stage_after_offset _ _)
  have xn := (RationalNestedIntervals.nesting L U X p (stage offset k) x hx hk).andE₂
  have yn := (RationalNestedIntervals.nesting L U Y p (stage offset k) x hy hk).andE₂
  exact transitive (RationalCubeInfimumName.midpoint_upper _ _
      (product_interval_ordered L U X Y a b offset k sx sy x hx hy hpx hpy))
    (product_monotone _ _ _ _ (power_nonnegative _ _) (power_nonnegative _ _)
      (power_monotone _ _ a xk.andE₂ xp.andE₂ xn) (power_monotone _ _ b yk.andE₂ yp.andE₂ yn))

theorem center_order_at (L U : PR 3) (X Y Z a b offset x k : PTm n)
    (h : Γ ⊢[PRAAx] centerOrder L U X Y Z a b offset x) : Γ ⊢[PRAAx]
    upper (powerCenter L U Z (a+b) offset k x) (productCenter L U X Y a b offset k x) one (scale k) := by
  simpa [centerOrder,scale] using h.allE k

theorem multiplicative_of_center_order (L U : PR 3) (X Y Z a b offset p sx sy sz x : PTm n)
    (hx : Γ ⊢[PRAAx] regular L U X x) (hy : Γ ⊢[PRAAx] regular L U Y x)
    (hz : Γ ⊢[PRAAx] regular L U Z x)
    (hpx : Γ ⊢[PRAAx] positiveWitness L X offset sx x)
    (hpy : Γ ⊢[PRAAx] positiveWitness L Y offset sy x)
    (hpz : Γ ⊢[PRAAx] positiveWitness L Z offset sz x)
    (hp : Γ ⊢[PRAAx] le offset p)
    (h : Γ ⊢[PRAAx] centerOrder L U X Y Z a b offset x) : Γ ⊢[PRAAx]
    RationalMultiplicativeConvexity.multiplicative a b (read U X p x) (read U Y p x) (read L Z p x) := by
  let A := RationalMultiplicativeConvexity.power (read L Z p x) (a+b)
  let B := multiply (RationalMultiplicativeConvexity.power (read U X p x) a)
    (RationalMultiplicativeConvexity.power (read U Y p x) b)
  let C := denominatorOf A*denominatorOf B
  let k := C+p
  have hk : Γ ⊢[PRAAx] le C k := by dsimp [k]; ipra_le 𝔟 p
  have hstage : Γ ⊢[PRAAx] le p (stage offset k) := by dsimp [stage,k]; ipra_le 𝔟 C+2+𝔟 offset
  have lower := power_center_lower L U Z (a+b) offset p k sz x hz hpz hp hstage
  have upper := product_center_upper L U X Y a b offset p k sx sy x hx hy hpx hpy hp hstage
  have error := RationalValueBounds.upper_order_left _ _ _ _ _ lower
    (RationalValueBounds.upper_order_right _ _ _ _ _ (center_order_at L U X Y Z a b offset x k h) upper)
  have small : Γ ⊢[PRAAx] lt C (scale k) :=
    lt_of_le_of_lt hk (LeanProofs.IPRA.AnalyticNumberTheory.Valuation.lt_pw (le_refl two) k)
  have raw : Γ ⊢[PRAAx] le (crossLeft A B*pw two k) (crossLeft B A*pw two k+C) :=
    le_congr (mul_comm _ _) (by dsimp [A,B,C,scale]; ipra_ring) error
  exact GapRemoval.gap_of small raw

theorem positive_witness_refine (L U : PR 3) (q p r s x : PTm n)
    (h : Γ ⊢[PRAAx] regular L U q x) (hp : Γ ⊢[PRAAx] positiveWitness L q p s x)
    (hpr : Γ ⊢[PRAAx] le p r) : Γ ⊢[PRAAx] positiveWitness L q r s x :=
  transitive hp (RationalNestedIntervals.nesting L U q p r x h hpr).andE₁

def input (L U : PR 3) (X Y Z offset p sx sy sz x : PTm n) : Fm PTm n :=
  regular L U X x ⋏ (regular L U Y x ⋏ (regular L U Z x ⋏
    (positiveWitness L X offset sx x ⋏ (positiveWitness L Y offset sy x ⋏
      (positiveWitness L Z offset sz x ⋏ le offset p)))))

ipra_subst input [positiveWitness, RationalConvexFiniteModulus.eps]

theorem endpoint_comparison (L U : PR 3) (X Y Z a b offset p sx sy sz x : PTm n)
    (h : Γ ⊢[PRAAx] input L U X Y Z offset p sx sy sz x)
    (ho : Γ ⊢[PRAAx] centerOrder L U X Y Z a b offset x) : Γ ⊢[PRAAx]
    RationalMultiplicativeConvexity.multiplicative a b (read U X p x) (read U Y p x) (read L Z p x) :=
  multiplicative_of_center_order L U X Y Z a b offset p sx sy sz x
    h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₁
    h.andE₂.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
    h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂ ho

/- The PR2 schedule and PR8 tuple return these exact original endpoint
readings and centers. No normalization/regularity contract is an input. -/
def stageF : PR 2 := PTm.toPR (stage (var 0) (var 1))
theorem stage_at (offset k : PTm n) : Γ ⊢[PRAAx] ap2 stageF offset k ≐ stage offset k := by
  simpa [stageF,ap2] using toPR_eq (Γ := Γ) (stage (var 0) (var 1) : PTm 2) ![offset,k]

def output (L U : PR 3) (X Y Z a b offset k x : PTm n) : PTm n :=
  pairT (powerEndpoint L Z (a+b) offset k x)
    (pairT (powerEndpoint U Z (a+b) offset k x)
      (pairT (productEndpoint L X Y a b offset k x)
        (pairT (productEndpoint U X Y a b offset k x)
          (pairT (powerCenter L U Z (a+b) offset k x)
            (pairT (productCenter L U X Y a b offset k x) (stage offset k))))))
def outputF (L U : PR 3) : PR 8 :=
  PTm.toPR (output L U (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
def run (L U : PR 3) (X Y Z a b offset k x : PTm n) : PTm n :=
  PTm.app (outputF L U) ![X,Y,Z,a,b,offset,k,x]

ipra_subst output
ipra_subst run

theorem program_at (L U : PR 3) (X Y Z a b offset k x : PTm n) :
    Γ ⊢[PRAAx] run L U X Y Z a b offset k x ≐ output L U X Y Z a b offset k x := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output L U (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) : PTm 8)
    ![X,Y,Z,a,b,offset,k,x]

theorem returned_power_lower (L U : PR 3) (X Y Z a b offset k x : PTm n) : Γ ⊢[PRAAx]
    fstT (run L U X Y Z a b offset k x) ≐ powerEndpoint L Z (a+b) offset k x :=
  (program_at L U X Y Z a b offset k x).fstE
theorem returned_power_upper (L U : PR 3) (X Y Z a b offset k x : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run L U X Y Z a b offset k x)) ≐ powerEndpoint U Z (a+b) offset k x := by
  have h := congrFst (congrSnd (program_at (Γ := Γ) L U X Y Z a b offset k x))
  simpa only [output] using h.eqTrans
    (snd_pair _ _).fstE
theorem returned_product_lower (L U : PR 3) (X Y Z a b offset k x : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run L U X Y Z a b offset k x))) ≐ productEndpoint L X Y a b offset k x := by
  have h := congrFst (congrSnd (congrSnd (program_at (Γ := Γ) L U X Y Z a b offset k x)))
  simpa only [output] using h.eqTrans ((congrFst (congrSnd (snd_pair _ _))).eqTrans
    (snd_pair _ _).fstE)
theorem returned_product_upper (L U : PR 3) (X Y Z a b offset k x : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (sndT (run L U X Y Z a b offset k x)))) ≐ productEndpoint U X Y a b offset k x := by
  have h := congrFst (congrSnd (congrSnd (congrSnd (program_at (Γ := Γ) L U X Y Z a b offset k x))))
  simpa only [output] using h.eqTrans ((congrFst (congrSnd (congrSnd (snd_pair _ _)))).eqTrans
    ((congrFst (congrSnd (snd_pair _ _))).eqTrans (snd_pair _ _).fstE))
theorem midpoint_congr {A B C D : PTm n} (hA : Γ ⊢[PRAAx] A ≐ C) (hB : Γ ⊢[PRAAx] B ≐ D) :
    Γ ⊢[PRAAx] midpoint A B ≐ midpoint C D := by
  ipra_congr (midpoint (var 0) (var 1) : PTm 2) with [hA, hB]
theorem returned_power_center (L U : PR 3) (X Y Z a b offset k x : PTm n) : Γ ⊢[PRAAx]
    midpoint (fstT (run L U X Y Z a b offset k x)) (fstT (sndT (run L U X Y Z a b offset k x))) ≐
      powerCenter L U Z (a+b) offset k x :=
  midpoint_congr (returned_power_lower L U X Y Z a b offset k x)
    (returned_power_upper L U X Y Z a b offset k x)
theorem returned_product_center (L U : PR 3) (X Y Z a b offset k x : PTm n) : Γ ⊢[PRAAx]
    midpoint (fstT (sndT (sndT (run L U X Y Z a b offset k x))))
      (fstT (sndT (sndT (sndT (run L U X Y Z a b offset k x))))) ≐
      productCenter L U X Y a b offset k x :=
  midpoint_congr (returned_product_lower L U X Y Z a b offset k x)
    (returned_product_upper L U X Y Z a b offset k x)

theorem actual_cofinal_schedule_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ap2 stageF (var 0) (var 1) ≐ stage (var 0) (var 1) ⋏
      (le (var 0) (stage (var 0) (var 1)) ⋏ le (var 1) (stage (var 0) (var 1)))) :=
  closeUniv 2 (.andI (stage_at _ _) (.andI (stage_after_offset _ _) (stage_cofinal _ _)))
theorem actual_nonnegative_power_monotone_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (nonnegative (var 0) ⟶ nonnegative (var 1) ⟶ rationalLE (var 0) (var 1) ⟶
      rationalLE (RationalMultiplicativeConvexity.power (var 0) (var 2))
        (RationalMultiplicativeConvexity.power (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (.impI (power_monotone _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem actual_positive_witness_refinement_closed (L U : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (regular L U (var 0) (var 4) ⟶ positiveWitness L (var 0) (var 1) (var 3) (var 4) ⟶
      le (var 1) (var 2) ⟶ positiveWitness L (var 0) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (positive_witness_refine L U _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem actual_endpoint_comparison_closed (L U : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    (input L U (var 0) (var 1) (var 2) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) ⟶
      centerOrder L U (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 10) ⟶
      RationalMultiplicativeConvexity.multiplicative (var 3) (var 4)
        (read U (var 0) (var 6) (var 10)) (read U (var 1) (var 6) (var 10))
        (read L (var 2) (var 6) (var 10))) :=
  closeUniv 11 (.impI (.impI (endpoint_comparison L U _ _ _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_endpoint_program_closed (L U : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (run L U (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ≐
      output L U (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) :=
  closeUniv 8 (program_at L U _ _ _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.RationalIntervalPowerComparison
