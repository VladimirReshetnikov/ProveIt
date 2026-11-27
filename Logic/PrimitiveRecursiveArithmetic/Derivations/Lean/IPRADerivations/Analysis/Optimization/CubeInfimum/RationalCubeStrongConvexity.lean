import IPRADerivations.Analysis.RationalArithmetic.Grids.RationalCubeMidpoint
import IPRADerivations.Analysis.RationalArithmetic.Grids.RationalCubeCoherentMinimizer
import IPRADerivations.Foundations.StrongConvexity
import IPRADerivations.Analysis.RationalArithmetic.Distances.Scalar.RationalPointDistanceVariation

/-!
# The original finite midpoint-drop estimate on actual cube points

The source hypothesis is the same-query finite strong-convexity inequality,
cleared through the actual independent sample denominators and the actual
rational sup distance. The near-minimum and lower laws derive the penalty
bound; no quantitative uniqueness law is supplied as a premise.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalCubeStrongConvexity

open_ipra
open RationalSupMetric (numeratorOf denominatorOf)
open RationalCubeMinimum (sample coherence continuity presentedCube)
open RationalCubeGrid (scale)
open RationalCubeCoherentMinimizer (near nearAt)
open RationalPointDistanceVariation (pointNumerator pointDenominator)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def common (a b c : PTm n) : PTm n := denominatorOf a*denominatorOf b*denominatorOf c
def midNum (a b c : PTm n) : ZT n := numeratorOf a*ZT.ofNat (denominatorOf b*denominatorOf c)
def leftNum (a b c : PTm n) : ZT n := numeratorOf b*ZT.ofNat (denominatorOf a*denominatorOf c)
def rightNum (a b c : PTm n) : ZT n := numeratorOf c*ZT.ofNat (denominatorOf a*denominatorOf b)
def dropLeft (a b c N B L M t : PTm n) : ZT n :=
  ZT.ofNat (num 8*M*B*B*scale t)*midNum a b c+ZT.ofNat (L*N*N*common a b c*scale t)
def dropRight (a b c _N B _L M t : PTm n) : ZT n :=
  ZT.ofNat (num 4*M*B*B*scale t)*(leftNum a b c+rightNum a b c)+ZT.ofNat (num 16*M*B*B*common a b c)
def dropRelation (a b c N B L M t : PTm n) : Fm PTm n := zle (dropLeft a b c N B L M t) (dropRight a b c N B L M t)
def dropAt (A : PR 3) (L M d x y z t : PTm n) : Fm PTm n := dropRelation
  (sample A (RationalCubeMidpoint.point d y z) t x) (sample A y t x) (sample A z t x)
  (pointNumerator y z d) (pointDenominator y z d) L M t
def midpointDrop (A : PR 3) (L M d x : PTm n) : Fm PTm n := .all (.all (.all
  (presentedCube (var 2) (Syn.shift (Syn.shift (Syn.shift d))) ⟶ presentedCube (var 1) (Syn.shift (Syn.shift (Syn.shift d))) ⟶
    dropAt A (Syn.shift (Syn.shift (Syn.shift L))) (Syn.shift (Syn.shift (Syn.shift M)))
      (Syn.shift (Syn.shift (Syn.shift d))) (Syn.shift (Syn.shift (Syn.shift x))) (var 2) (var 1) (var 0))))

ipra_subst common
ipra_subst midNum
ipra_subst leftNum
ipra_subst rightNum
ipra_subst dropLeft
ipra_subst dropRight
ipra_subst dropRelation
ipra_subst dropAt
ipra_subst midpointDrop [Syn.subst_shift, Syn.shift_subst]

theorem midpoint_drop_at (A : PR 3) (L M d x y z t : PTm n) (h : Γ ⊢[PRAAx] midpointDrop A L M d x)
    (hy : Γ ⊢[PRAAx] presentedCube y d) (hz : Γ ⊢[PRAAx] presentedCube z d) : Γ ⊢[PRAAx] dropAt A L M d x y z t := by
  have law : Γ ⊢[PRAAx] presentedCube y d ⟶ presentedCube z d ⟶ dropAt A L M d x y z t := by
    simpa [midpointDrop,Syn.subst_shift,Syn.shift_subst,Syn.shift,Syn.subst_subst,Function.comp_def] using ((h.allE y).allE z).allE t
  exact .impE (.impE law hy) hz

/-- Genuine finite penalty extraction, retaining all four independent raw
sample denominators and cancelling only their proved positive product. -/
theorem finite_penalty (v a b c N B L M e t : PTm n)
    (h0 : Γ ⊢[PRAAx] RationalValueBounds.upper v a two (scale t))
    (h1 : Γ ⊢[PRAAx] RationalValueBounds.upper b v (scale t+two*scale e) (scale e*scale t))
    (h2 : Γ ⊢[PRAAx] RationalValueBounds.upper c v (scale t+two*scale e) (scale e*scale t))
    (h3 : Γ ⊢[PRAAx] dropRelation a b c N B L M t) : Γ ⊢[PRAAx]
    le (L*N*N*scale e*scale t) (num 8*M*B*B*scale t+num 48*M*B*B*scale e) := by
  let Q := denominatorOf v*denominatorOf a*denominatorOf b*denominatorOf c
  let E := scale e
  let S := scale t
  let Fv := numeratorOf v*ZT.ofNat (denominatorOf a*denominatorOf b*denominatorOf c)
  let Fm := numeratorOf a*ZT.ofNat (denominatorOf v*denominatorOf b*denominatorOf c)
  let Fl := numeratorOf b*ZT.ofNat (denominatorOf v*denominatorOf a*denominatorOf c)
  let Fr := numeratorOf c*ZT.ofNat (denominatorOf v*denominatorOf a*denominatorOf b)
  let lower := ZT.ofNat (S*E)*Fv
  let middle := ZT.ofNat (S*E)*Fm+ZT.ofNat (two*E*Q)
  let left := ZT.ofNat (S*E)*Fl+ZT.ofNat (num 4*E*Q)
  let right := ZT.ofNat (S*E)*Fr+ZT.ofNat (num 4*E*Q)
  let weight := num 8*M*B*B
  let penalty := L*N*N*Q*S*E
  let eta := Q*(S+num 6*E)
  have low : Γ ⊢[PRAAx] zle lower middle := by
    apply zle_of_toZ (E*denominatorOf b*denominatorOf c*
      monus (S*RationalValueBounds.crossLeft a v+two*denominatorOf v*denominatorOf a) (S*RationalValueBounds.crossLeft v a))
    have eq := natEq (eq_add_of_le h0)
    dsimp [lower,middle,Fv,Fm,Q,S,E]
    simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat]
    simp only [ZT.toZ]
    unfold RationalValueBounds.crossLeft at eq ⊢
    ipra_simps
    linear_combination -𝔞(scale e)*𝔞(denominatorOf b)*𝔞(denominatorOf c)*eq
  have leftBound : Γ ⊢[PRAAx] zle left (lower+ZT.ofNat eta) := by
    apply zle_of_toZ (denominatorOf a*denominatorOf c*
      monus ((E*S)*RationalValueBounds.crossLeft v b+(S+two*E)*denominatorOf b*denominatorOf v)
        ((E*S)*RationalValueBounds.crossLeft b v))
    have eq := natEq (eq_add_of_le h1)
    dsimp [left,lower,Fl,Fv,eta,Q,S,E]
    simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat]
    simp only [ZT.toZ]
    unfold RationalValueBounds.crossLeft at eq ⊢
    ipra_simps
    linear_combination -𝔞(denominatorOf a)*𝔞(denominatorOf c)*eq
  have rightBound : Γ ⊢[PRAAx] zle right (lower+ZT.ofNat eta) := by
    apply zle_of_toZ (denominatorOf a*denominatorOf b*
      monus ((E*S)*RationalValueBounds.crossLeft v c+(S+two*E)*denominatorOf c*denominatorOf v)
        ((E*S)*RationalValueBounds.crossLeft c v))
    have eq := natEq (eq_add_of_le h2)
    dsimp [right,lower,Fr,Fv,eta,Q,S,E]
    simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat]
    simp only [ZT.toZ]
    unfold RationalValueBounds.crossLeft at eq ⊢
    ipra_simps
    linear_combination -𝔞(denominatorOf a)*𝔞(denominatorOf b)*eq
  have convex : Γ ⊢[PRAAx] zle (ZT.ofNat (two*weight)*middle+ZT.ofNat (two*penalty)) (ZT.ofNat weight*(left+right)) := by
    let gap := monus ((dropRight a b c N B L M t).pos+(dropLeft a b c N B L M t).neg)
      ((dropLeft a b c N B L M t).pos+(dropRight a b c N B L M t).neg)
    have eq := zle_toZ h3
    change ZT.toZ Γ (dropLeft a b c N B L M t)+𝔞(gap) = ZT.toZ Γ (dropRight a b c N B L M t) at eq
    apply zle_of_toZ (two*denominatorOf v*E*gap)
    dsimp [middle,left,right,Fm,Fl,Fr,weight,penalty,Q,S,E]
    dsimp [dropLeft,dropRight,midNum,leftNum,rightNum,common] at eq
    simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat] at eq ⊢
    simp only [ZT.toZ] at eq ⊢
    ipra_simps
    linear_combination (2*𝔞(denominatorOf v)*𝔞(scale e))*eq
  have actual := Foundations.StrongConvexity.penalty_bound lower middle left right weight penalty eta low leftBound rightBound convex
  have hQ : Γ ⊢[PRAAx] le one Q :=
    RationalAlgebra.positive_product (RationalAlgebra.positive_product (RationalAlgebra.positive_product
      (RationalArgmin.denominator_positive v) (RationalArgmin.denominator_positive a))
      (RationalArgmin.denominator_positive b)) (RationalArgmin.denominator_positive c)
  apply RationalValueBounds.positive_cancel hQ
  exact le_congr (by dsimp [penalty]; ipra_ring) (by dsimp [weight,eta,E,S]; ipra_ring) actual


theorem near_same (A : PR 3) (mu : PR 2) (d x y e t : PTm n) (h : Γ ⊢[PRAAx] near A mu d x y e) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (sample A y t x) (RationalCubeInfimumName.value A mu d t x)
      (scale t+two*scale e) (scale e*scale t) :=
  RationalValueBounds.upper_cancel _ _ _ _ (scale t) (RationalCubeGrid.scale_positive t)
    (RationalValueBounds.upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (RationalCubeCoherentMinimizer.near_at A mu d x y e t t h))

theorem lower_same (A : PR 3) (mu : PR 2) (d x y t : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) (hy : Γ ⊢[PRAAx] presentedCube y d) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (RationalCubeInfimumName.value A mu d t x) (sample A y t x) two (scale t) :=
  RationalValueBounds.upper_cancel _ _ _ _ (scale t) (RationalCubeGrid.scale_positive t)
    (RationalValueBounds.upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (RationalCubeInfimumName.value_lower_bound A mu d t x y t hc ht hy))

/-- The real source predicates derive the squared strong-convexity gap
bound at one explicitly computed sampling precision. -/
theorem source_squared (A : PR 3) (mu : PR 2) (L M d x y z e : PTm n)
    (hc : Γ ⊢[PRAAx] coherence A d x) (ht : Γ ⊢[PRAAx] continuity A mu d x)
    (hd : Γ ⊢[PRAAx] midpointDrop A L M d x) (hy : Γ ⊢[PRAAx] presentedCube y d) (hz : Γ ⊢[PRAAx] presentedCube z d)
    (hn : Γ ⊢[PRAAx] near A mu d x y e) (hm : Γ ⊢[PRAAx] near A mu d x z e) : Γ ⊢[PRAAx]
    le (L*scale e*pointNumerator y z d*pointNumerator y z d) (num 8*M*pointDenominator y z d*pointDenominator y z d) := by
  let N := pointNumerator y z d
  let B := pointDenominator y z d
  let C := num 48*M*B*B*scale e
  have penalty := finite_penalty (RationalCubeInfimumName.value A mu d C x)
    (sample A (RationalCubeMidpoint.point d y z) C x) (sample A y C x) (sample A z C x) N B L M e C
    (lower_same A mu d x _ C hc ht (RationalCubeMidpoint.point_presented d y z hy hz))
    (near_same A mu d x y e C hn) (near_same A mu d x z e C hm) (midpoint_drop_at A L M d x y z C hd hy hz)
  have finite : Γ ⊢[PRAAx] le ((L*scale e*N*N)*scale C) ((num 8*M*B*B)*scale C+C) :=
    le_congr (by ipra_ring) (.eqRefl _) penalty
  exact GapRemoval.gap finite

def linearIndex (k c : PTm n) : PTm n := two*k+c
ipra_subst linearIndex [two, one]

theorem scale_linear (k c : PTm n) : Γ ⊢[PRAAx] scale (linearIndex k c) ≐ (scale k*scale k)*scale c :=
  (congrAp2 powF (show Γ ⊢[PRAAx] linearIndex k c ≐ (k+k)+c by unfold linearIndex; ipra_ring) (.eqRefl two)).eqTrans
    ((pw_add two (k+k) c).eqTrans (congrMul (pw_add two k k) (.eqRefl _)))

/-- Original lambda and cutoff guards turn the derived square bound into
exact rational point distance, including zero distance and dimension zero. -/
theorem linear_radius (A : PR 3) (mu : PR 2) (L M d x c k y z : PTm n)
    (hc : Γ ⊢[PRAAx] coherence A d x) (ht : Γ ⊢[PRAAx] continuity A mu d x)
    (hd : Γ ⊢[PRAAx] midpointDrop A L M d x) (hM : Γ ⊢[PRAAx] le one M)
    (hBudget : Γ ⊢[PRAAx] le (num 8*M) (L*scale c))
    (hy : Γ ⊢[PRAAx] presentedCube y d) (hz : Γ ⊢[PRAAx] presentedCube z d)
    (hn : Γ ⊢[PRAAx] near A mu d x y (linearIndex k c)) (hm : Γ ⊢[PRAAx] near A mu d x z (linearIndex k c)) : Γ ⊢[PRAAx]
    RationalHausdorff.pointRadius y z d one (scale k) := by
  let N := pointNumerator y z d
  let B := pointDenominator y z d
  have squared := source_squared A mu L M d x y z (linearIndex k c) hc ht hd hy hz hn hm
  have schedule := mul_le_mul_right ((scale k*scale k)*(N*N)) hBudget
  have first : Γ ⊢[PRAAx] le ((num 8*M)*((scale k*N)*(scale k*N))) (L*scale (linearIndex k c)*N*N) := by
    apply le_congr (by ipra_ring) _ schedule
    apply deriveNat
    ipra_simps
    rw [natEq (scale_linear (Γ := Γ) k c)]
    ipra_simps
    ring
  have final : Γ ⊢[PRAAx] le ((num 8*M)*((scale k*N)*(scale k*N))) ((num 8*M)*(B*B)) :=
    le_trans first (le_congr (.eqRefl _) (by ipra_ring) squared)
  have hp : Γ ⊢[PRAAx] le one (num 8*M) := RationalAlgebra.positive_product
    (le_of_eq_add (d := num 7) (by ipra_ring)) hM
  have radius := nat_sqrt_mono (RationalValueBounds.positive_cancel hp final)
  exact RationalPointDistanceVariation.point_radius_of_bound _ _ _ _ _
    (le_congr (.eqRefl _) (one_mul _).eqSymm radius)


def linearUniqueness (A : PR 3) (mu : PR 2) (d x c : PTm n) : Fm PTm n := .all (.all (.all
  (presentedCube (var 1) (Syn.shift (Syn.shift (Syn.shift d))) ⟶ presentedCube (var 0) (Syn.shift (Syn.shift (Syn.shift d))) ⟶
    near A mu (Syn.shift (Syn.shift (Syn.shift d))) (Syn.shift (Syn.shift (Syn.shift x))) (var 1)
      (linearIndex (var 2) (Syn.shift (Syn.shift (Syn.shift c)))) ⟶
    near A mu (Syn.shift (Syn.shift (Syn.shift d))) (Syn.shift (Syn.shift (Syn.shift x))) (var 0)
      (linearIndex (var 2) (Syn.shift (Syn.shift (Syn.shift c)))) ⟶
    RationalHausdorff.pointRadius (var 1) (var 0) (Syn.shift (Syn.shift (Syn.shift d))) one (scale (var 2)))))
ipra_subst linearUniqueness [Syn.subst_shift, Syn.shift_subst]

theorem source_linear_uniqueness (A : PR 3) (mu : PR 2) (L M d x c : PTm n)
    (hc : Γ ⊢[PRAAx] coherence A d x) (ht : Γ ⊢[PRAAx] continuity A mu d x)
    (hd : Γ ⊢[PRAAx] midpointDrop A L M d x) (hM : Γ ⊢[PRAAx] le one M)
    (hBudget : Γ ⊢[PRAAx] le (num 8*M) (L*scale c)) : Γ ⊢[PRAAx] linearUniqueness A mu d x c := by
  refine .allI (.allI (.allI (.impI (.impI (.impI (.impI ?_))))))
  let D := Syn.shift (Syn.shift (Syn.shift d))
  let X := Syn.shift (Syn.shift (Syn.shift x))
  let C := Syn.shift (Syn.shift (Syn.shift c))
  let LL := Syn.shift (Syn.shift (Syn.shift L))
  let MM := Syn.shift (Syn.shift (Syn.shift M))
  let Δ := near A mu D X (var 0) (linearIndex (var 2) C) :: near A mu D X (var 1) (linearIndex (var 2) C) ::
    presentedCube (var 0) D :: presentedCube (var 1) D :: ((Γ.map Fm.shift).map Fm.shift).map Fm.shift
  have co : Δ ⊢[PRAAx] coherence A D X := by
    simpa only [Δ,D,X,Fm.shift,RationalCubeMinimum.subst_coherence,Syn.shift] using hc.shift.shift.shift.wk.wk.wk.wk
  have ct : Δ ⊢[PRAAx] continuity A mu D X := by
    simpa only [Δ,D,X,Fm.shift,RationalCubeMinimum.subst_continuity,Syn.shift] using ht.shift.shift.shift.wk.wk.wk.wk
  have md : Δ ⊢[PRAAx] midpointDrop A LL MM D X := by
    simpa only [Δ,D,X,LL,MM,Fm.shift,subst_midpointDrop,Syn.shift] using hd.shift.shift.shift.wk.wk.wk.wk
  have mp : Δ ⊢[PRAAx] le one MM := by
    simpa only [Δ,MM,Fm.shift,subst_le,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hM.shift.shift.shift.wk.wk.wk.wk
  have bd : Δ ⊢[PRAAx] le (num 8*MM) (LL*scale C) := by
    simpa [Δ,MM,LL,C,Fm.shift,Syn.shift] using hBudget.shift.shift.shift.wk.wk.wk.wk
  simpa only [Δ,D,X,C,LL,MM] using linear_radius A mu LL MM D X C (var 2) (var 1) (var 0) co ct md mp bd
    (.hyp (by simp [Δ])) (.hyp (by simp [Δ])) (.hyp (by simp [Δ])) (.hyp (by simp [Δ]))

def cutoff (M : PTm n) : PTm n := num 8*M
ipra_subst cutoff
theorem cutoff_budget (L M : PTm n) (hL : Γ ⊢[PRAAx] le one L) : Γ ⊢[PRAAx] le (num 8*M) (L*scale (cutoff M)) := by
  have p : Γ ⊢[PRAAx] le (cutoff M) (scale (cutoff M)) := le_of_lt (AnalyticNumberTheory.Valuation.lt_pw (le_refl two) (cutoff M))
  have m : Γ ⊢[PRAAx] le (scale (cutoff M)) (L*scale (cutoff M)) :=
    le_congr (one_mul _) (.eqRefl _) (AnalyticNumberTheory.PhiLower.le_mul_mono hL (le_refl _))
  exact le_trans p m

theorem computed_linear_uniqueness (A : PR 3) (mu : PR 2) (L M d x : PTm n)
    (hc : Γ ⊢[PRAAx] coherence A d x) (ht : Γ ⊢[PRAAx] continuity A mu d x)
    (hd : Γ ⊢[PRAAx] midpointDrop A L M d x) (hL : Γ ⊢[PRAAx] le one L) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] linearUniqueness A mu d x (cutoff M) := source_linear_uniqueness A mu L M d x (cutoff M) hc ht hd hM (cutoff_budget L M hL)

def cutoffF : PR 1 := PTm.toPR (cutoff (var 0))
def runCutoff (M : PTm n) : PTm n := ap1 cutoffF M
def linearF : PR 2 := PTm.toPR (linearIndex (var 0) (var 1))
def runLinear (k c : PTm n) : PTm n := ap2 linearF k c

theorem cutoff_program_at (M : PTm n) : Γ ⊢[PRAAx] runCutoff M ≐ cutoff M := by
  simpa [ap1,runCutoff,cutoffF] using toPR_eq (Γ := Γ) (cutoff (var 0) : PTm 1) ![M]
theorem linear_program_at (k c : PTm n) : Γ ⊢[PRAAx] runLinear k c ≐ linearIndex k c := by
  simpa [ap2,runLinear,linearF] using toPR_eq (Γ := Γ) (linearIndex (var 0) (var 1) : PTm 2) ![k,c]

theorem actual_same_query_finite_penalty_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (RationalValueBounds.upper (var 0) (var 1) two (scale (var 9)) ⟶
      RationalValueBounds.upper (var 2) (var 0) (scale (var 9)+two*scale (var 8)) (scale (var 8)*scale (var 9)) ⟶
      RationalValueBounds.upper (var 3) (var 0) (scale (var 9)+two*scale (var 8)) (scale (var 8)*scale (var 9)) ⟶
      dropRelation (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 9) ⟶
      le (var 6*var 4*var 4*scale (var 8)*scale (var 9))
        (num 8*var 7*var 5*var 5*scale (var 9)+num 48*var 7*var 5*var 5*scale (var 8))) :=
  closeUniv 10 (.impI (.impI (.impI (.impI (finite_penalty (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)))))))
theorem actual_source_midpoint_squared_bound_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (coherence A (var 2) (var 3) ⟶ continuity A mu (var 2) (var 3) ⟶ midpointDrop A (var 0) (var 1) (var 2) (var 3) ⟶
      presentedCube (var 4) (var 2) ⟶ presentedCube (var 5) (var 2) ⟶
      near A mu (var 2) (var 3) (var 4) (var 6) ⟶ near A mu (var 2) (var 3) (var 5) (var 6) ⟶
      le (var 0*scale (var 6)*pointNumerator (var 4) (var 5) (var 2)*pointNumerator (var 4) (var 5) (var 2))
        (num 8*var 1*pointDenominator (var 4) (var 5) (var 2)*pointDenominator (var 4) (var 5) (var 2))) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI (.impI (.impI (source_squared A mu (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp))))))))))
theorem actual_source_linear_uniqueness_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (coherence A (var 2) (var 3) ⟶ continuity A mu (var 2) (var 3) ⟶ midpointDrop A (var 0) (var 1) (var 2) (var 3) ⟶
      le one (var 1) ⟶ le (num 8*var 1) (var 0*scale (var 4)) ⟶ linearUniqueness A mu (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (.impI (source_linear_uniqueness A mu (var 0) (var 1) (var 2) (var 3) (var 4)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp))))))))
theorem actual_computed_positive_lambda_cutoff_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⟶ le (num 8*var 1) (var 0*scale (cutoff (var 1)))) := closeUniv 2 (.impI (cutoff_budget (var 0) (var 1) Prf.hyp0))
theorem actual_source_computed_linear_uniqueness_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (coherence A (var 2) (var 3) ⟶ continuity A mu (var 2) (var 3) ⟶ midpointDrop A (var 0) (var 1) (var 2) (var 3) ⟶
      le one (var 0) ⟶ le one (var 1) ⟶ linearUniqueness A mu (var 2) (var 3) (cutoff (var 1))) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (.impI (computed_linear_uniqueness A mu (var 0) (var 1) (var 2) (var 3)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp))))))))
theorem actual_source_cutoff_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (runCutoff (var 0) ≐ num 8*var 0) := closeUniv 1 (cutoff_program_at (var 0))
theorem actual_source_linear_schedule_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (runLinear (var 0) (var 1) ≐ two*var 0+var 1) := closeUniv 2 (linear_program_at (var 0) (var 1))

end LeanProofs.IPRA.Analysis.RationalCubeStrongConvexity
