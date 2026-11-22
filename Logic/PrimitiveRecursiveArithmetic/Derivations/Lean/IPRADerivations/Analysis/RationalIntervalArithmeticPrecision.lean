import IPRADerivations.Analysis.RationalNestedIntervals
import IPRADerivations.Analysis.RationalMultiplicativeConvexity
import IPRADerivations.Analysis.GaussianRationalPowerDifference
import IPRADerivations.Analysis.RationalIntervalPowerComparison

/-!
# Computed precision for positive rational interval powers and products

Finite power perturbation is proved by ordinary QF induction. Actual
rational representatives then give quantitative bounds for the original
endpoint programs; no powered-interval width law is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalIntervalArithmeticPrecision

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred monus)
open RationalArithmetic (represents multiply)
open RationalArgmin (rationalLE denominator_positive)
open RationalConvexSecants (nonnegative naturalNumerator nonnegative_representation rescaled_representation)
open RationalSupMetric (denominatorOf)
open RationalValueBounds (upper)
open GaussianRationalSyntheticBounds (natCode natCode_represents)
open GaussianRationalPowerDifference (budget budget_zero budget_step)
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

def perturbation (u v R A B j : PTm n) : Fm PTm n :=
  le (B*pw u j) (B*pw v j+budget R A j)

@[simp] theorem subst_perturbation {m : ℕ} (σ : Fin n → PTm m) (u v R A B j : PTm n) :
    (perturbation u v R A B j).subst σ = perturbation (Syn.subst σ u) (Syn.subst σ v)
      (Syn.subst σ R) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ j) := by simp [perturbation]

theorem perturbation_zero (u v R A B : PTm n) : Γ ⊢[PRAAx] perturbation u v R A B zero :=
  le_congr ((congrMul (.eqRefl _) (pw_zero u)).eqTrans (by ipra_ring)).eqSymm
    ((congrAdd (congrMul (.eqRefl _) (pw_zero v)) (budget_zero R A)).eqTrans (by ipra_ring)).eqSymm
    (le_refl B)

theorem perturbation_step (u v R A B j : PTm n) (hu : Γ ⊢[PRAAx] le u R)
    (hv : Γ ⊢[PRAAx] le v R) (hd : Γ ⊢[PRAAx] le (B*u) (B*v+A))
    (hi : Γ ⊢[PRAAx] perturbation u v R A B j) : Γ ⊢[PRAAx] perturbation u v R A B (succ j) := by
  have first := mul_le_mul_right u hi
  have second := mul_le_mul_right (pw v j) hd
  have remain := add_le_add₂ (mul_le_mul_right (budget R A j) hu)
    (mul_le_mul_right A (pw_le_pw j hv))
  have first' : Γ ⊢[PRAAx] le (B*pw u j*u) (B*pw v j*u+budget R A j*u) :=
    le_congr (.eqRefl _) (by ipra_ring) first
  have second' : Γ ⊢[PRAAx] le (B*pw v j*u+budget R A j*u)
      (B*pw v j*v+pw v j*A+budget R A j*u) :=
    le_congr (by ipra_ring) (by ipra_ring) (add_le_add_right (budget R A j*u) second)
  have third' : Γ ⊢[PRAAx] le (B*pw v j*v+pw v j*A+budget R A j*u)
      (B*pw v j*v+(budget R A j*R+pw R j*A)) :=
    le_congr (by ipra_ring) (by ipra_ring) (add_le_add_right (B*pw v j*v) remain)
  have total : Γ ⊢[PRAAx] le (B*pw u j*u)
      (B*pw v j*v+(budget R A j*R+pw R j*A)) := by
    exact le_trans first' (le_trans second' third')
  exact le_congr ((congrMul (.eqRefl _) (pw_succ u j)).eqTrans (by ipra_ring)).eqSymm
    ((congrAdd (congrMul (.eqRefl _) (pw_succ v j)) (budget_step R A j).eqSymm).eqTrans (by ipra_ring)).eqSymm total

theorem natural_power_perturbation (u v R A B j : PTm n) (hu : Γ ⊢[PRAAx] le u R)
    (hv : Γ ⊢[PRAAx] le v R) (hd : Γ ⊢[PRAAx] le (B*u) (B*v+A)) : Γ ⊢[PRAAx]
    perturbation u v R A B j := by
  have us : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift u) (Syn.shift R) := by simpa [Fm.shift,Syn.shift] using hu.shift
  have vs : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift v) (Syn.shift R) := by simpa [Fm.shift,Syn.shift] using hv.shift
  have ds : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift B*Syn.shift u) (Syn.shift B*Syn.shift v+Syn.shift A) := by
    simpa [Fm.shift,Syn.shift] using hd.shift
  have all : Γ ⊢[PRAAx] .all (perturbation (Syn.shift u) (Syn.shift v) (Syn.shift R)
      (Syn.shift A) (Syn.shift B) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_perturbation,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact perturbation_zero u v R A B
    · simp only [subst_perturbation,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact perturbation_step _ _ _ _ _ _ us.wk vs.wk ds.wk Prf.hyp0
  simpa only [subst_perturbation,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j

theorem upper_to_natural_same (c d u v E P Q : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hQ : Γ ⊢[PRAAx] le one Q) (hc : Γ ⊢[PRAAx] represents c (ZT.ofNat u) E)
    (hd : Γ ⊢[PRAAx] represents d (ZT.ofNat v) E) (h : Γ ⊢[PRAAx] upper c d P Q) :
    Γ ⊢[PRAAx] le (Q*u) (Q*v+P*E) := by
  have added : Γ ⊢[PRAAx] represents (RationalArithmetic.add d (GaussianEuclideanDistanceName.fraction P Q))
      (ZT.ofNat (v*Q+P*E)) (E*Q) := by
    refine GaussianRationalHorner.scalar_congr (.eqRefl _) ?_ (.eqRefl _)
      (RationalRepresentations.represents_add _ _ _ _ _ _ hd (GaussianEuclideanDistanceName.fraction_represents P Q hQ))
    apply ZT.derive
    simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]
    ipra_simps
  have raw := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _ hc added
    (RationalConvexEndpointBudget.order_of_upper c d P Q hQ h)
  exact RationalValueBounds.positive_cancel hE (le_congr (by ipra_ring) (by ipra_ring) raw)

theorem upper_from_natural_same (c d u v E P Q : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hc : Γ ⊢[PRAAx] represents c (ZT.ofNat u) E) (hd : Γ ⊢[PRAAx] represents d (ZT.ofNat v) E)
    (h : Γ ⊢[PRAAx] le (Q*u) (Q*v+P*E)) : Γ ⊢[PRAAx] upper c d P Q := by
  apply RationalCubeInfimumIntervals.upper_of_representations _ _ _ _ E E P Q hE hE hc hd
  apply zle_of_toZ (E*monus (Q*v+P*E) (Q*u))
  have e := natEq (eq_add_of_le h)
  simp only [ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_ofNat]
  ipra_simps
  linear_combination -(𝔟 E)*e

def slope (M e : PTm n) : PTm n := e*pw M e
@[simp] theorem subst_slope {m : ℕ} (σ : Fin n → PTm m) (M e : PTm n) :
    Syn.subst σ (slope M e) = slope (Syn.subst σ M) (Syn.subst σ e) := by simp [slope]

theorem budget_common_denominator (M E e : PTm n) (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx]
    le (budget (M*E) E e) (slope M e*pw E e) := by
  refine .orE (zero_or_succ e) ?_ ?_
  · have h : ((e ≐ zero) :: Γ) ⊢[PRAAx] e ≐ zero := Prf.hyp0
    have z : ((e ≐ zero) :: Γ) ⊢[PRAAx] budget (M*E) E e ≐ zero :=
      (congrMul (congrMul h (.eqRefl _)) (.eqRefl E)).eqTrans (by ipra_ring)
    exact le_congr z.eqSymm (.eqRefl _) (zero_le _)
  · have h : ((e ≐ succ (pred e)) :: Γ) ⊢[PRAAx] e ≐ succ (pred e) := Prf.hyp0
    have pwE := natEq ((congrAp2 powF h (.eqRefl E)).eqTrans (pw_succ E (pred e)))
    have pwME := natEq (pw_mul_base (Γ := (e ≐ succ (pred e)) :: Γ) M E (pred e))
    have bigger : ((e ≐ succ (pred e)) :: Γ) ⊢[PRAAx] le (pw M (pred e)) (pw M e) := by
      exact le_congr (one_mul _) ((mul_comm _ _).eqTrans
        ((congrAp2 powF h (.eqRefl M)).eqTrans (pw_succ M (pred e))).eqSymm)
        (mul_le_mul_right (pw M (pred e)) hM.wk)
    have result := mul_le_mul_right (e*pw E e) bigger
    apply le_congr (b' := slope M e*pw E e) ?_ (by unfold slope; ipra_ring) result
    apply deriveNat
    unfold budget
    ipra_simps
    rw [pwE,pwME]
    ring

theorem power_width (q r M e P Q : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hQ : Γ ⊢[PRAAx] le one Q) (hq : Γ ⊢[PRAAx] nonnegative q) (hr : Γ ⊢[PRAAx] nonnegative r)
    (bq : Γ ⊢[PRAAx] rationalLE q (natCode M)) (br : Γ ⊢[PRAAx] rationalLE r (natCode M))
    (hd : Γ ⊢[PRAAx] upper q r P Q) : Γ ⊢[PRAAx]
    upper (RationalMultiplicativeConvexity.power q e) (RationalMultiplicativeConvexity.power r e)
      (slope M e*P) Q := by
  let E := denominatorOf q*denominatorOf r
  let u := naturalNumerator q*denominatorOf r
  let v := naturalNumerator r*denominatorOf q
  have hE : Γ ⊢[PRAAx] le one E := RationalAlgebra.positive_product (denominator_positive q) (denominator_positive r)
  have rq := rescaled_representation q (denominatorOf r) E hq (.eqRefl _)
  have rr := rescaled_representation r (denominatorOf q) E hr (by dsimp [E]; ipra_ring)
  have uq : Γ ⊢[PRAAx] le u (M*E) := by
    exact le_congr (one_mul _) (.eqRefl _)
      (GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _ rq (natCode_represents M) bq)
  have vr : Γ ⊢[PRAAx] le v (M*E) := by
    exact le_congr (one_mul _) (.eqRefl _)
      (GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _ rr (natCode_represents M) br)
  have original := upper_to_natural_same q r u v E P Q hE hQ rq rr hd
  have finite := natural_power_perturbation u v (M*E) (P*E) Q e uq vr
    original
  have budgetP : Γ ⊢[PRAAx] le (budget (M*E) (P*E) e) (slope M e*P*pw E e) :=
    le_congr (by unfold budget; ipra_ring) (by ipra_ring)
      (mul_le_mul_right P (budget_common_denominator M E e hM))
  exact upper_from_natural_same _ _ _ _ (pw E e) _ Q
    (RationalNonnegativePowers.denominator_positive E e hE)
    (RationalMultiplicativeConvexity.power_representation q u E e hq hE rq)
    (RationalMultiplicativeConvexity.power_representation r v E e hr hE rr)
    (le_trans finite (le_congr (add_comm _ _) (add_comm _ _) (add_le_add_right (Q*pw v e) budgetP)))

theorem power_bound (q M e : PTm n) (hq : Γ ⊢[PRAAx] nonnegative q)
    (hb : Γ ⊢[PRAAx] rationalLE q (natCode M)) : Γ ⊢[PRAAx]
    rationalLE (RationalMultiplicativeConvexity.power q e) (natCode (pw M e)) := by
  let D := denominatorOf q
  let u := naturalNumerator q
  have rep := nonnegative_representation q hq
  have raw : Γ ⊢[PRAAx] le u (M*D) :=
    le_congr (one_mul _) (.eqRefl _) (GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _ rep (natCode_represents M) hb)
  exact GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _
    (RationalNonnegativePowers.denominator_positive D e (denominator_positive q)) (le_refl one)
    (RationalMultiplicativeConvexity.power_representation q u D e hq (denominator_positive q) rep)
    (natCode_represents (pw M e))
    (le_congr (one_mul _).eqSymm (pw_mul_base M D e) (pw_le_pw e raw))

theorem product_width (q r s t M N P S Q : PTm n) (hQ : Γ ⊢[PRAAx] le one Q)
    (hq : Γ ⊢[PRAAx] nonnegative q) (hr : Γ ⊢[PRAAx] nonnegative r)
    (hs : Γ ⊢[PRAAx] nonnegative s) (ht : Γ ⊢[PRAAx] nonnegative t)
    (bq : Γ ⊢[PRAAx] rationalLE q (natCode M)) (bt : Γ ⊢[PRAAx] rationalLE t (natCode N))
    (hqr : Γ ⊢[PRAAx] upper q r P Q) (hst : Γ ⊢[PRAAx] upper s t S Q) : Γ ⊢[PRAAx]
    upper (multiply q s) (multiply r t) (P*N+S*M) Q := by
  let dq := denominatorOf q
  let dr := denominatorOf r
  let ds := denominatorOf s
  let dt := denominatorOf t
  let E := dq*dr*ds*dt
  let u := naturalNumerator q*(dr*ds*dt)
  let v := naturalNumerator r*(dq*ds*dt)
  let w := naturalNumerator s*(dq*dr*dt)
  let z := naturalNumerator t*(dq*dr*ds)
  have hE : Γ ⊢[PRAAx] le one E := RationalAlgebra.positive_product
    (RationalAlgebra.positive_product (RationalAlgebra.positive_product (denominator_positive q)
      (denominator_positive r)) (denominator_positive s)) (denominator_positive t)
  have rq := rescaled_representation q (dr*ds*dt) E hq (by dsimp [E,dq]; ipra_ring)
  have rr := rescaled_representation r (dq*ds*dt) E hr (by dsimp [E,dr]; ipra_ring)
  have rs := rescaled_representation s (dq*dr*dt) E hs (by dsimp [E,ds]; ipra_ring)
  have rt := rescaled_representation t (dq*dr*ds) E ht (by dsimp [E,dt]; ipra_ring)
  have hu : Γ ⊢[PRAAx] le u (M*E) :=
    le_congr (one_mul _) (.eqRefl _) (GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _ rq (natCode_represents M) bq)
  have hz : Γ ⊢[PRAAx] le z (N*E) :=
    le_congr (one_mul _) (.eqRefl _) (GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _ rt (natCode_represents N) bt)
  have hd1 := upper_to_natural_same q r u v E P Q hE hQ rq rr hqr
  have hd2 := upper_to_natural_same s t w z E S Q hE hQ rs rt hst
  have first : Γ ⊢[PRAAx] le (Q*(u*w)) (Q*(u*z)+S*E*u) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right u hd2)
  have second : Γ ⊢[PRAAx] le (Q*(u*z)+S*E*u) (Q*(v*z)+P*E*z+S*E*u) :=
    le_congr (by ipra_ring) (by ipra_ring) (add_le_add_right (S*E*u) (mul_le_mul_right z hd1))
  have errors := add_le_add₂ (mul_le_mul_right (P*E) hz) (mul_le_mul_right (S*E) hu)
  have third : Γ ⊢[PRAAx] le (Q*(v*z)+P*E*z+S*E*u) (Q*(v*z)+(P*N+S*M)*(E*E)) :=
    le_congr (by ipra_ring) (by ipra_ring) (add_le_add_right (Q*(v*z)) errors)
  have qprod : Γ ⊢[PRAAx] represents (multiply q s) (ZT.ofNat (u*w)) (E*E) := by
    refine GaussianRationalHorner.scalar_congr (.eqRefl _) ?_ (.eqRefl _)
      (RationalRepresentations.represents_multiply _ _ _ _ _ _ rq rs)
    apply ZT.derive
    dsimp [u,w]
    simp only [ZT.toZ_mul,ZT.toZ_ofNat]
    ipra_simps
  have rprod : Γ ⊢[PRAAx] represents (multiply r t) (ZT.ofNat (v*z)) (E*E) := by
    refine GaussianRationalHorner.scalar_congr (.eqRefl _) ?_ (.eqRefl _)
      (RationalRepresentations.represents_multiply _ _ _ _ _ _ rr rt)
    apply ZT.derive
    dsimp [v,z]
    simp only [ZT.toZ_mul,ZT.toZ_ofNat]
    ipra_simps
  exact upper_from_natural_same _ _ _ _ (E*E) _ Q (RationalAlgebra.positive_product hE hE)
    qprod rprod (le_trans first (le_trans second third))

theorem product_power_width (q r s t M a b Q : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hQ : Γ ⊢[PRAAx] le one Q)
    (hq : Γ ⊢[PRAAx] nonnegative q) (hr : Γ ⊢[PRAAx] nonnegative r)
    (hs : Γ ⊢[PRAAx] nonnegative s) (ht : Γ ⊢[PRAAx] nonnegative t)
    (bq : Γ ⊢[PRAAx] rationalLE q (natCode M)) (br : Γ ⊢[PRAAx] rationalLE r (natCode M))
    (bs : Γ ⊢[PRAAx] rationalLE s (natCode M)) (bt : Γ ⊢[PRAAx] rationalLE t (natCode M))
    (hqr : Γ ⊢[PRAAx] upper q r one Q) (hst : Γ ⊢[PRAAx] upper s t one Q) : Γ ⊢[PRAAx]
    upper (multiply (RationalMultiplicativeConvexity.power q a) (RationalMultiplicativeConvexity.power s b))
      (multiply (RationalMultiplicativeConvexity.power r a) (RationalMultiplicativeConvexity.power t b))
      (slope M (a+b)) Q := by
  have first := power_width q r M a one Q hM hQ hq hr bq br hqr
  have second := power_width s t M b one Q hM hQ hs ht bs bt hst
  have result := product_width _ _ _ _ (pw M a) (pw M b) (slope M a*one) (slope M b*one) Q hQ
    (RationalIntervalPowerComparison.power_nonnegative _ _) (RationalIntervalPowerComparison.power_nonnegative _ _)
    (RationalIntervalPowerComparison.power_nonnegative _ _) (RationalIntervalPowerComparison.power_nonnegative _ _)
    (power_bound q M a hq bq) (power_bound t M b ht bt) first second
  have e : Γ ⊢[PRAAx] slope M a*one*pw M b+slope M b*one*pw M a ≐ slope M (a+b) := by
    have hp := natEq (pw_add (Γ := Γ) M a b)
    apply deriveNat
    unfold slope
    ipra_simps
    rw [hp]
    ring
  exact RationalValueBounds.upper_congr (.eqRefl _) (.eqRefl _) e (.eqRefl _) result

def M (U : PR 3) (X Y x : PTm n) : PTm n :=
  succ (RationalConvexEndpointBudget.coarseCeiling (RationalNestedIntervals.read U X zero x)
    (RationalNestedIntervals.read U Y zero x))
def offset (U : PR 3) (X Y e p x : PTm n) : PTm n := p+slope (M U X Y x) e

@[simp] theorem subst_M {m : ℕ} (σ : Fin n → PTm m) (U : PR 3) (X Y x : PTm n) :
    Syn.subst σ (M U X Y x) = M U (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ x) := by
  simp [M,RationalConvexEndpointBudget.coarseCeiling,RationalConvexEndpointBudget.observedBound,
    RationalConvexEndpointBudget.absolute,naturalNumerator,RationalSupMetric.numeratorOf]
@[simp] theorem subst_offset {m : ℕ} (σ : Fin n → PTm m) (U : PR 3) (X Y e p x : PTm n) :
    Syn.subst σ (offset U X Y e p x) = offset U (Syn.subst σ X) (Syn.subst σ Y)
      (Syn.subst σ e) (Syn.subst σ p) (Syn.subst σ x) := by simp [offset]

theorem M_positive (U : PR 3) (X Y x : PTm n) : Γ ⊢[PRAAx] le one (M U X Y x) := zero_lt_succ _
theorem offset_after_cutoff (U : PR 3) (X Y e p x : PTm n) : Γ ⊢[PRAAx] le p (offset U X Y e p x) := by
  unfold offset
  ipra_le 𝔟 (slope (M U X Y x) e)
theorem offset_covers_slope (U : PR 3) (X Y e p x : PTm n) : Γ ⊢[PRAAx]
    le (slope (M U X Y x) e) (offset U X Y e p x) := by unfold offset; ipra_le 𝔟 p

theorem initial_bounds (U : PR 3) (X Y x : PTm n) : Γ ⊢[PRAAx]
    rationalLE (RationalNestedIntervals.read U X zero x) (natCode (M U X Y x)) ⋏
      rationalLE (RationalNestedIntervals.read U Y zero x) (natCode (M U X Y x)) := by
  have h := RationalConvexEndpointBudget.original_observation_bound (Γ := Γ)
    (RationalNestedIntervals.read U X zero x) (RationalNestedIntervals.read U Y zero x)
  have hm : Γ ⊢[PRAAx] rationalLE
      (natCode (RationalConvexEndpointBudget.coarseCeiling (RationalNestedIntervals.read U X zero x)
        (RationalNestedIntervals.read U Y zero x))) (natCode (M U X Y x)) :=
    GaussianRationalSyntheticBounds.natCode_order _ _ (le_succ_self _)
  exact .andI (RationalArgmin.transitive h.andE₁ hm) (RationalArgmin.transitive h.andE₂ hm)

theorem endpoint_bounds (L U : PR 3) (q p B x : PTm n)
    (h : Γ ⊢[PRAAx] RationalNestedIntervals.regular L U q x)
    (h0 : Γ ⊢[PRAAx] rationalLE (RationalNestedIntervals.read U q zero x) (natCode B)) : Γ ⊢[PRAAx]
    rationalLE (RationalNestedIntervals.read L q p x) (natCode B) ⋏
      rationalLE (RationalNestedIntervals.read U q p x) (natCode B) := by
  have hu := RationalArgmin.transitive
    (RationalNestedIntervals.nesting L U q zero p x h (zero_le _)).andE₂ h0
  exact .andI (RationalArgmin.transitive (RationalNestedIntervals.ordered L U q p x h) hu) hu

theorem shifted_budget (K o k : PTm n) (ho : Γ ⊢[PRAAx] le K o) : Γ ⊢[PRAAx]
    le (K*RationalCubeGrid.scale k) (RationalCubeGrid.scale (RationalIntervalPowerComparison.stage o k)) := by
  have hsmall : Γ ⊢[PRAAx] le K (pw two (two+o)) := le_trans ho
    (le_trans (by ipra_le 2) (le_of_lt (LeanProofs.IPRA.AnalyticNumberTheory.Valuation.lt_pw (le_refl two) (two+o))))
  have e : Γ ⊢[PRAAx] pw two (two+o)*pw two k ≐
      RationalCubeGrid.scale (RationalIntervalPowerComparison.stage o k) :=
    (mul_comm _ _).eqTrans ((pw_add two k (two+o)).eqSymm.eqTrans
      (congrAp2 powF (by unfold RationalIntervalPowerComparison.stage; ipra_ring) (.eqRefl two)))
  exact le_congr (.eqRefl _) e (mul_le_mul_right (pw two k) hsmall)

theorem stage_monotone (o k l : PTm n) (h : Γ ⊢[PRAAx] le k l) : Γ ⊢[PRAAx]
    le (RationalIntervalPowerComparison.stage o k) (RationalIntervalPowerComparison.stage o l) :=
  le_congr (by unfold RationalIntervalPowerComparison.stage; ipra_ring)
    (by unfold RationalIntervalPowerComparison.stage; ipra_ring) (add_le_add_right (two+o) h)

theorem power_endpoint_width (L U : PR 3) (q e p s k x : PTm n)
    (h : Γ ⊢[PRAAx] RationalNestedIntervals.regular L U q x)
    (hp : Γ ⊢[PRAAx] RationalNestedIntervals.positiveWitness L q p s x) : Γ ⊢[PRAAx]
    upper (RationalIntervalPowerComparison.powerEndpoint U q e (offset U q q e p x) k x)
      (RationalIntervalPowerComparison.powerEndpoint L q e (offset U q q e p x) k x)
      one (RationalCubeGrid.scale k) := by
  let o := offset U q q e p x
  let r := RationalIntervalPowerComparison.stage o k
  have hpr : Γ ⊢[PRAAx] le p r := le_trans (offset_after_cutoff U q q e p x)
    (RationalIntervalPowerComparison.stage_after_offset o k)
  have nn := RationalIntervalPowerComparison.endpoints_nonnegative L U q p r s x h hp hpr
  have bb := endpoint_bounds L U q r (M U q q x) x h (initial_bounds U q q x).andE₁
  have old := (RationalNestedIntervals.step_at L U q r x h).andE₂.andE₂.andE₂
  have powered := power_width _ _ (M U q q x) e one (RationalCubeGrid.scale r)
    (M_positive U q q x) (RationalCubeGrid.scale_positive r) nn.andE₂ nn.andE₁ bb.andE₂ bb.andE₁ old
  exact RationalValueBounds.upper_mono _ _ _ _ _ _ (RationalCubeGrid.scale_positive r) powered
    (le_congr (by ipra_ring) (one_mul _).eqSymm
      (shifted_budget _ o k (offset_covers_slope U q q e p x)))

theorem product_endpoint_width (L U : PR 3) (X Y a b p sx sy k x : PTm n)
    (hx : Γ ⊢[PRAAx] RationalNestedIntervals.regular L U X x)
    (hy : Γ ⊢[PRAAx] RationalNestedIntervals.regular L U Y x)
    (hpx : Γ ⊢[PRAAx] RationalNestedIntervals.positiveWitness L X p sx x)
    (hpy : Γ ⊢[PRAAx] RationalNestedIntervals.positiveWitness L Y p sy x) : Γ ⊢[PRAAx]
    upper (RationalIntervalPowerComparison.productEndpoint U X Y a b (offset U X Y (a+b) p x) k x)
      (RationalIntervalPowerComparison.productEndpoint L X Y a b (offset U X Y (a+b) p x) k x)
      one (RationalCubeGrid.scale k) := by
  let o := offset U X Y (a+b) p x
  let r := RationalIntervalPowerComparison.stage o k
  have hpr : Γ ⊢[PRAAx] le p r := le_trans (offset_after_cutoff U X Y (a+b) p x)
    (RationalIntervalPowerComparison.stage_after_offset o k)
  have xn := RationalIntervalPowerComparison.endpoints_nonnegative L U X p r sx x hx hpx hpr
  have yn := RationalIntervalPowerComparison.endpoints_nonnegative L U Y p r sy x hy hpy hpr
  have xb := endpoint_bounds L U X r (M U X Y x) x hx (initial_bounds U X Y x).andE₁
  have yb := endpoint_bounds L U Y r (M U X Y x) x hy (initial_bounds U X Y x).andE₂
  have xd := (RationalNestedIntervals.step_at L U X r x hx).andE₂.andE₂.andE₂
  have yd := (RationalNestedIntervals.step_at L U Y r x hy).andE₂.andE₂.andE₂
  have result := product_power_width _ _ _ _ (M U X Y x) a b (RationalCubeGrid.scale r)
    (M_positive U X Y x) (RationalCubeGrid.scale_positive r) xn.andE₂ xn.andE₁ yn.andE₂ yn.andE₁
    xb.andE₂ xb.andE₁ yb.andE₂ yb.andE₁ xd yd
  exact RationalValueBounds.upper_mono _ _ _ _ _ _ (RationalCubeGrid.scale_positive r) result
    (le_congr (.eqRefl _) (one_mul _).eqSymm
      (shifted_budget _ o k (offset_covers_slope U X Y (a+b) p x)))

theorem power_endpoint_nested (L U : PR 3) (q e p s k l x : PTm n)
    (h : Γ ⊢[PRAAx] RationalNestedIntervals.regular L U q x)
    (hp : Γ ⊢[PRAAx] RationalNestedIntervals.positiveWitness L q p s x)
    (hkl : Γ ⊢[PRAAx] le k l) : Γ ⊢[PRAAx]
    rationalLE (RationalIntervalPowerComparison.powerEndpoint L q e (offset U q q e p x) k x)
      (RationalIntervalPowerComparison.powerEndpoint L q e (offset U q q e p x) l x) ⋏
    rationalLE (RationalIntervalPowerComparison.powerEndpoint U q e (offset U q q e p x) l x)
      (RationalIntervalPowerComparison.powerEndpoint U q e (offset U q q e p x) k x) := by
  let o := offset U q q e p x
  let r := RationalIntervalPowerComparison.stage o k
  let t := RationalIntervalPowerComparison.stage o l
  have hr := le_trans (offset_after_cutoff (Γ := Γ) U q q e p x) (RationalIntervalPowerComparison.stage_after_offset o k)
  have ht := le_trans (offset_after_cutoff (Γ := Γ) U q q e p x) (RationalIntervalPowerComparison.stage_after_offset o l)
  have rn := RationalIntervalPowerComparison.endpoints_nonnegative L U q p r s x h hp hr
  have tn := RationalIntervalPowerComparison.endpoints_nonnegative L U q p t s x h hp ht
  have nested := RationalNestedIntervals.nesting L U q r t x h (stage_monotone o k l hkl)
  exact .andI (RationalIntervalPowerComparison.power_monotone _ _ e rn.andE₁ tn.andE₁ nested.andE₁)
    (RationalIntervalPowerComparison.power_monotone _ _ e tn.andE₂ rn.andE₂ nested.andE₂)

theorem product_endpoint_nested (L U : PR 3) (X Y a b p sx sy k l x : PTm n)
    (hx : Γ ⊢[PRAAx] RationalNestedIntervals.regular L U X x)
    (hy : Γ ⊢[PRAAx] RationalNestedIntervals.regular L U Y x)
    (hpx : Γ ⊢[PRAAx] RationalNestedIntervals.positiveWitness L X p sx x)
    (hpy : Γ ⊢[PRAAx] RationalNestedIntervals.positiveWitness L Y p sy x)
    (hkl : Γ ⊢[PRAAx] le k l) : Γ ⊢[PRAAx]
    rationalLE (RationalIntervalPowerComparison.productEndpoint L X Y a b (offset U X Y (a+b) p x) k x)
      (RationalIntervalPowerComparison.productEndpoint L X Y a b (offset U X Y (a+b) p x) l x) ⋏
    rationalLE (RationalIntervalPowerComparison.productEndpoint U X Y a b (offset U X Y (a+b) p x) l x)
      (RationalIntervalPowerComparison.productEndpoint U X Y a b (offset U X Y (a+b) p x) k x) := by
  let o := offset U X Y (a+b) p x
  let r := RationalIntervalPowerComparison.stage o k
  let t := RationalIntervalPowerComparison.stage o l
  have hr := le_trans (offset_after_cutoff (Γ := Γ) U X Y (a+b) p x) (RationalIntervalPowerComparison.stage_after_offset o k)
  have ht := le_trans (offset_after_cutoff (Γ := Γ) U X Y (a+b) p x) (RationalIntervalPowerComparison.stage_after_offset o l)
  have xr := RationalIntervalPowerComparison.endpoints_nonnegative L U X p r sx x hx hpx hr
  have xt := RationalIntervalPowerComparison.endpoints_nonnegative L U X p t sx x hx hpx ht
  have yr := RationalIntervalPowerComparison.endpoints_nonnegative L U Y p r sy x hy hpy hr
  have yt := RationalIntervalPowerComparison.endpoints_nonnegative L U Y p t sy x hy hpy ht
  have xn := RationalNestedIntervals.nesting L U X r t x hx (stage_monotone o k l hkl)
  have yn := RationalNestedIntervals.nesting L U Y r t x hy (stage_monotone o k l hkl)
  exact .andI (RationalIntervalPowerComparison.product_monotone _ _ _ _
      (RationalIntervalPowerComparison.power_nonnegative _ _) (RationalIntervalPowerComparison.power_nonnegative _ _)
      (RationalIntervalPowerComparison.power_monotone _ _ a xr.andE₁ xt.andE₁ xn.andE₁)
      (RationalIntervalPowerComparison.power_monotone _ _ b yr.andE₁ yt.andE₁ yn.andE₁))
    (RationalIntervalPowerComparison.product_monotone _ _ _ _
      (RationalIntervalPowerComparison.power_nonnegative _ _) (RationalIntervalPowerComparison.power_nonnegative _ _)
      (RationalIntervalPowerComparison.power_monotone _ _ a xt.andE₂ xr.andE₂ xn.andE₂)
      (RationalIntervalPowerComparison.power_monotone _ _ b yt.andE₂ yr.andE₂ yn.andE₂))

def output (U : PR 3) (X Y e p x : PTm n) : PTm n :=
  pairT (M U X Y x) (offset U X Y e p x)
def outputF (U : PR 3) : PR 5 := PTm.toPR (output U (var 0) (var 1) (var 2) (var 3) (var 4))
def run (U : PR 3) (X Y e p x : PTm n) : PTm n := PTm.app (outputF U) ![X,Y,e,p,x]
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (U : PR 3) (X Y e p x : PTm n) :
    Syn.subst σ (output U X Y e p x) =
      output U (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ e) (Syn.subst σ p) (Syn.subst σ x) := by
  simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (U : PR 3) (X Y e p x : PTm n) :
    Syn.subst σ (run U X Y e p x) =
      run U (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ e) (Syn.subst σ p) (Syn.subst σ x) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
theorem program_at (U : PR 3) (X Y e p x : PTm n) : Γ ⊢[PRAAx] run U X Y e p x ≐ output U X Y e p x := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output U (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![X,Y,e,p,x]
theorem returned_bound (U : PR 3) (X Y e p x : PTm n) : Γ ⊢[PRAAx] fstT (run U X Y e p x) ≐ M U X Y x :=
  (congrFst (program_at U X Y e p x)).eqTrans (fst_pair _ _)
theorem returned_offset (U : PR 3) (X Y e p x : PTm n) : Γ ⊢[PRAAx] sndT (run U X Y e p x) ≐ offset U X Y e p x :=
  (congrSnd (program_at U X Y e p x)).eqTrans (snd_pair _ _)
theorem returned_precision_bound (U : PR 3) (X Y e p x : PTm n) : Γ ⊢[PRAAx]
    le one (fstT (run U X Y e p x)) ⋏
      (le p (sndT (run U X Y e p x)) ⋏ le (slope (fstT (run U X Y e p x)) e) (sndT (run U X Y e p x))) := by
  have slopeEq : Γ ⊢[PRAAx] slope (fstT (run U X Y e p x)) e ≐ slope (M U X Y x) e :=
    congrMul (.eqRefl _) (congrAp2 powF (.eqRefl _) (returned_bound U X Y e p x))
  exact .andI (le_congr (.eqRefl _) (returned_bound U X Y e p x).eqSymm (M_positive U X Y x))
    (.andI (le_congr (.eqRefl _) (returned_offset U X Y e p x).eqSymm (offset_after_cutoff U X Y e p x))
      (le_congr slopeEq.eqSymm (returned_offset U X Y e p x).eqSymm (offset_covers_slope U X Y e p x)))

theorem actual_native_power_perturbation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (var 0) (var 2) ⟶ le (var 1) (var 2) ⟶ le (var 4*var 0) (var 4*var 1+var 3) ⟶
      perturbation (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (natural_power_perturbation _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem actual_power_interval_width_closed (L U : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (RationalNestedIntervals.regular L U (var 0) (var 5) ⟶
      RationalNestedIntervals.positiveWitness L (var 0) (var 2) (var 3) (var 5) ⟶
      upper (RationalIntervalPowerComparison.powerEndpoint U (var 0) (var 1)
          (offset U (var 0) (var 0) (var 1) (var 2) (var 5)) (var 4) (var 5))
        (RationalIntervalPowerComparison.powerEndpoint L (var 0) (var 1)
          (offset U (var 0) (var 0) (var 1) (var 2) (var 5)) (var 4) (var 5)) one (RationalCubeGrid.scale (var 4))) :=
  closeUniv 6 (.impI (.impI (power_endpoint_width L U _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_product_interval_width_closed (L U : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (RationalNestedIntervals.regular L U (var 0) (var 8) ⟶ RationalNestedIntervals.regular L U (var 1) (var 8) ⟶
      RationalNestedIntervals.positiveWitness L (var 0) (var 4) (var 5) (var 8) ⟶
      RationalNestedIntervals.positiveWitness L (var 1) (var 4) (var 6) (var 8) ⟶
      upper (RationalIntervalPowerComparison.productEndpoint U (var 0) (var 1) (var 2) (var 3)
          (offset U (var 0) (var 1) (var 2+var 3) (var 4) (var 8)) (var 7) (var 8))
        (RationalIntervalPowerComparison.productEndpoint L (var 0) (var 1) (var 2) (var 3)
          (offset U (var 0) (var 1) (var 2+var 3) (var 4) (var 8)) (var 7) (var 8)) one (RationalCubeGrid.scale (var 7))) :=
  closeUniv 9 (.impI (.impI (.impI (.impI (product_endpoint_width L U _ _ _ _ _ _ _ _ _
    Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem actual_power_interval_nesting_closed (L U : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (RationalNestedIntervals.regular L U (var 0) (var 6) ⟶
      RationalNestedIntervals.positiveWitness L (var 0) (var 2) (var 3) (var 6) ⟶ le (var 4) (var 5) ⟶
      (rationalLE (RationalIntervalPowerComparison.powerEndpoint L (var 0) (var 1)
          (offset U (var 0) (var 0) (var 1) (var 2) (var 6)) (var 4) (var 6))
        (RationalIntervalPowerComparison.powerEndpoint L (var 0) (var 1)
          (offset U (var 0) (var 0) (var 1) (var 2) (var 6)) (var 5) (var 6)) ⋏
      rationalLE (RationalIntervalPowerComparison.powerEndpoint U (var 0) (var 1)
          (offset U (var 0) (var 0) (var 1) (var 2) (var 6)) (var 5) (var 6))
        (RationalIntervalPowerComparison.powerEndpoint U (var 0) (var 1)
          (offset U (var 0) (var 0) (var 1) (var 2) (var 6)) (var 4) (var 6)))) :=
  closeUniv 7 (.impI (.impI (.impI (power_endpoint_nested L U _ _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem actual_product_interval_nesting_closed (L U : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (RationalNestedIntervals.regular L U (var 0) (var 9) ⟶ RationalNestedIntervals.regular L U (var 1) (var 9) ⟶
      RationalNestedIntervals.positiveWitness L (var 0) (var 4) (var 5) (var 9) ⟶
      RationalNestedIntervals.positiveWitness L (var 1) (var 4) (var 6) (var 9) ⟶ le (var 7) (var 8) ⟶
      (rationalLE (RationalIntervalPowerComparison.productEndpoint L (var 0) (var 1) (var 2) (var 3)
          (offset U (var 0) (var 1) (var 2+var 3) (var 4) (var 9)) (var 7) (var 9))
        (RationalIntervalPowerComparison.productEndpoint L (var 0) (var 1) (var 2) (var 3)
          (offset U (var 0) (var 1) (var 2+var 3) (var 4) (var 9)) (var 8) (var 9)) ⋏
      rationalLE (RationalIntervalPowerComparison.productEndpoint U (var 0) (var 1) (var 2) (var 3)
          (offset U (var 0) (var 1) (var 2+var 3) (var 4) (var 9)) (var 8) (var 9))
        (RationalIntervalPowerComparison.productEndpoint U (var 0) (var 1) (var 2) (var 3)
          (offset U (var 0) (var 1) (var 2+var 3) (var 4) (var 9)) (var 7) (var 9)))) :=
  closeUniv 10 (.impI (.impI (.impI (.impI (.impI (product_endpoint_nested L U _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))
theorem actual_precision_program_closed (U : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run U (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output U (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at U _ _ _ _ _)
theorem actual_returned_precision_closed (U : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (fstT (run U (var 0) (var 1) (var 2) (var 3) (var 4))) ⋏
      (le (var 3) (sndT (run U (var 0) (var 1) (var 2) (var 3) (var 4))) ⋏
        le (slope (fstT (run U (var 0) (var 1) (var 2) (var 3) (var 4))) (var 2))
          (sndT (run U (var 0) (var 1) (var 2) (var 3) (var 4))))) :=
  closeUniv 5 (returned_precision_bound U _ _ _ _ _)

end LeanProofs.IPRA.Analysis.RationalIntervalArithmeticPrecision
