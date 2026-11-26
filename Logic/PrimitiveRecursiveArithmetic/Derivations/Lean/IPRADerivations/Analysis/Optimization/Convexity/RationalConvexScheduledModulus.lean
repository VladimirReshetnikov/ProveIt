import IPRADerivations.Analysis.Optimization.Convexity.RationalConvexSourceRLC
import IPRADerivations.Analysis.RationalArithmetic.Powers.RationalCofinalPowerOrder
import IPRADerivations.Analysis.Names.RationalIntervalArithmeticNames

/-!
# The local modulus for the fixed source log-convex presentation

The precision schedule for a power comparison is compiled from the
original endpoint names and positivity witnesses. The two comparisons
may use different offsets. The proof moves both to their common sum,
preserving the original upper/lower widths and the source order, then
uses the two-endpoint modulus on the original rational arguments.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalConvexScheduledModulus

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiRationalScaling (rationalLT)
open RationalNestedConvexModulus (presented witnessIndex witnessExponent)
open RationalNestedIntervals (positiveWitness center centerF)
open RationalConvexSourceRLC (schedule rule leftOffset rightOffset leftWeightFor rightWeightFor shiftWeightFor
  source_secants positive_fraction)
open RationalConvexArguments (arguments enlargedDen firstNumerator secondNumerator endpointDen interiorNumerator
  original_geometry clock)
open RationalOriginalConvexModulus (sourceLeft sourceRight source_queries sourceInputs sourcePowerComparisons original_named_modulus)
open RationalIntervalPowerComparison (centerOrder positive_witness_refine)
open RationalIntervalArithmeticPrecision (offset offset_after_cutoff)
open RationalCofinalPowerOrder (widthsAt widths witnessInput transport)
open RationalConvexSecants (nonnegative)
open GaussianRationalSyntheticBounds (natCode)
open RationalArithmetic (recode)
open RationalValueBounds (radius)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

def cutoff (W : PR 2) (A B C x : PTm n) : PTm n := witnessIndex W A x+witnessIndex W B x+witnessIndex W C x

def suggestedOffset (U : PR 3) (W : PR 2) (A B C j l x : PTm n) : PTm n :=
  offset U C C (j+l) (cutoff W A B C x) x + offset U A B (j+l) (cutoff W A B C x) x

def sourceSchedule (U : PR 3) (W : PR 2) : PR 6 :=
  PTm.toPR (suggestedOffset U W (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))

def positivePresentation (L U : PR 3) (W : PR 2) (x : PTm n) : Fm PTm n :=
  .all (rationalLT (natCode zero) (var 0) ⟶ presented L U W (var 0) (Syn.shift x))

def threePoints (L U : PR 3) (W : PR 2) (A B C x : PTm n) : Fm PTm n :=
  presented L U W A x ⋏ (presented L U W B x ⋏ presented L U W C x)

@[simp] theorem subst_presented {m : ℕ} (σ : Fin n → PTm m) (L U : PR 3) (W : PR 2) (q x : PTm n) :
    (presented L U W q x).subst σ =
      presented L U W (Syn.subst σ q) (Syn.subst σ x) := by
  simp [presented,witnessIndex,witnessExponent,RationalNestedIntervals.positiveWitness,RationalConvexFiniteModulus.eps]
@[simp] theorem subst_threePoints {m : ℕ} (σ : Fin n → PTm m) (L U : PR 3) (W : PR 2) (A B C x : PTm n) :
    (threePoints L U W A B C x).subst σ =
      threePoints L U W (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ C) (Syn.subst σ x) := by simp [threePoints]
@[simp] theorem subst_suggestedOffset {m : ℕ} (σ : Fin n → PTm m) (U : PR 3) (W : PR 2) (A B C j l x : PTm n) :
    Syn.subst σ (suggestedOffset U W A B C j l x) =
      suggestedOffset U W (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ C) (Syn.subst σ j) (Syn.subst σ l) (Syn.subst σ x) := by
  simp [suggestedOffset,cutoff,witnessIndex]

theorem schedule_at (U : PR 3) (W : PR 2) (A B C j l x : PTm n) :
    Γ ⊢[PRAAx] schedule (sourceSchedule U W) A B C j l x ≐ suggestedOffset U W A B C j l x := by
  simpa [schedule,sourceSchedule] using toPR_eq (Γ := Γ)
    (suggestedOffset U W (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![A,B,C,j,l,x]

theorem presentation_at (L U : PR 3) (W : PR 2) (q x : PTm n)
    (h : Γ ⊢[PRAAx] positivePresentation L U W x) (hp : Γ ⊢[PRAAx] rationalLT (natCode zero) q) :
    Γ ⊢[PRAAx] presented L U W q x := by
  have a : Γ ⊢[PRAAx] rationalLT (natCode zero) q ⟶ presented L U W q x := by
    simpa [positivePresentation] using h.allE q
  exact .impE a hp

theorem cutoff_bounds (W : PR 2) (A B C x : PTm n) :
    Γ ⊢[PRAAx] le (witnessIndex W A x) (cutoff W A B C x) ⋏
      (le (witnessIndex W B x) (cutoff W A B C x) ⋏ le (witnessIndex W C x) (cutoff W A B C x)) := by
  let p := witnessIndex W A x
  let q := witnessIndex W B x
  let r := witnessIndex W C x
  have ha : Γ ⊢[PRAAx] le p (p+q+r) := by ipra_le 𝔟 q+𝔟 r
  have hb : Γ ⊢[PRAAx] le q (p+q+r) := by ipra_le 𝔟 p+𝔟 r
  have hc : Γ ⊢[PRAAx] le r (p+q+r) := by ipra_le 𝔟 p+𝔟 q
  exact .andI ha (.andI hb hc)

theorem cutoff_le_schedule (U : PR 3) (W : PR 2) (A B C j l x : PTm n) :
    Γ ⊢[PRAAx] le (cutoff W A B C x) (schedule (sourceSchedule U W) A B C j l x) := by
  have h := offset_after_cutoff (Γ := Γ) U C C (j+l) (cutoff W A B C x) x
  exact le_congr (.eqRefl _) (schedule_at U W A B C j l x).eqSymm (le_trans h (le_add_right _ _))

theorem witnesses_at (L U : PR 3) (W : PR 2) (A B C x o : PTm n)
    (h : Γ ⊢[PRAAx] threePoints L U W A B C x) (ho : Γ ⊢[PRAAx] le (cutoff W A B C x) o) :
    Γ ⊢[PRAAx] witnessInput L U A B C o (witnessExponent W A x) (witnessExponent W B x) (witnessExponent W C x) x := by
  have e := cutoff_bounds (Γ := Γ) W A B C x
  have ha := h.andE₁
  have hb := h.andE₂.andE₁
  have hc := h.andE₂.andE₂
  have pa := positive_witness_refine L U A (witnessIndex W A x) o (witnessExponent W A x) x
    ha.andE₁ ha.andE₂ (le_trans e.andE₁ ho)
  have pb := positive_witness_refine L U B (witnessIndex W B x) o (witnessExponent W B x) x
    hb.andE₁ hb.andE₂ (le_trans e.andE₂.andE₁ ho)
  have pc := positive_witness_refine L U C (witnessIndex W C x) o (witnessExponent W C x) x
    hc.andE₁ hc.andE₂ (le_trans e.andE₂.andE₂ ho)
  exact .andI ha.andE₁ (.andI hb.andE₁ (.andI hc.andE₁ (.andI pa (.andI pb pc))))

theorem adequate_at (L U : PR 3) (W : PR 2) (A B C j l o k x : PTm n)
    (h : Γ ⊢[PRAAx] threePoints L U W A B C x)
    (ho : Γ ⊢[PRAAx] le (suggestedOffset U W A B C j l x) o) :
    Γ ⊢[PRAAx] widthsAt L U A B C j l o k x := by
  let p := cutoff W A B C x
  let f := offset U C C (j+l) p x
  let g := offset U A B (j+l) p x
  have hh := witnesses_at L U W A B C x p h (le_refl p)
  have hf : Γ ⊢[PRAAx] le f (f+g) := le_add_right _ _
  have hg : Γ ⊢[PRAAx] le g (f+g) := by ipra_le 𝔟 f
  exact .andI (RationalIntervalArithmeticNames.power_width L U C (j+l) p (witnessExponent W C x) o k x
    hh.andE₂.andE₂.andE₁ hh.andE₂.andE₂.andE₂.andE₂.andE₂ (le_trans hf ho))
    (RationalIntervalArithmeticNames.product_width L U A B j l p (witnessExponent W A x) (witnessExponent W B x) o k x
      hh.andE₁ hh.andE₂.andE₁ hh.andE₂.andE₂.andE₂.andE₁ hh.andE₂.andE₂.andE₂.andE₂.andE₁ (le_trans hg ho))

theorem adequate (L U : PR 3) (W : PR 2) (A B C j l o x : PTm n)
    (h : Γ ⊢[PRAAx] threePoints L U W A B C x)
    (ho : Γ ⊢[PRAAx] le (schedule (sourceSchedule U W) A B C j l x) o) :
    Γ ⊢[PRAAx] widths L U A B C j l o x := by
  have hh : Γ.map Fm.shift ⊢[PRAAx] threePoints L U W (Syn.shift A) (Syn.shift B) (Syn.shift C) (Syn.shift x) := by
    simpa only [Fm.shift,subst_threePoints,Syn.shift] using h.shift
  have h₀ := le_congr (schedule_at U W A B C j l x) (.eqRefl _) ho
  have he : Γ.map Fm.shift ⊢[PRAAx] le
      (suggestedOffset U W (Syn.shift A) (Syn.shift B) (Syn.shift C) (Syn.shift j) (Syn.shift l) (Syn.shift x)) (Syn.shift o) := by
    simpa only [Fm.shift,Syn.shift,subst_le,subst_suggestedOffset] using h₀.shift
  exact .allI (adequate_at L U W (Syn.shift A) (Syn.shift B) (Syn.shift C) (Syn.shift j) (Syn.shift l)
    (Syn.shift o) (var 0) (Syn.shift x) hh he)

theorem retain_source_order (L U : PR 3) (W : PR 2) (A B C j l o x : PTm n)
    (h : Γ ⊢[PRAAx] threePoints L U W A B C x)
    (ho : Γ ⊢[PRAAx] le (schedule (sourceSchedule U W) A B C j l x) o)
    (hc : Γ ⊢[PRAAx] centerOrder L U A B C j l (schedule (sourceSchedule U W) A B C j l x) x) :
    Γ ⊢[PRAAx] centerOrder L U A B C j l o x :=
  transport L U A B C j l _ o (witnessExponent W A x) (witnessExponent W B x) (witnessExponent W C x)
    x (witnesses_at L U W A B C x _ h (cutoff_le_schedule U W A B C j l x)) ho hc (adequate L U W A B C j l o x h ho)

theorem actual_original_scheduled_modulus (L U : PR 3) (W : PR 2) (a b u v k t x : PTm n)
    (h : Γ ⊢[PRAAx] arguments a b u v) (hp : Γ ⊢[PRAAx] positivePresentation L U W x)
    (hc : Γ ⊢[PRAAx] rule L U (sourceSchedule U W) x)
    (hd : Γ ⊢[PRAAx] radius u v one (pw two (clock (centerF L U) a b k x))) :
    Γ ⊢[PRAAx] radius (center L U (recode u) (succ (succ t)) x) (center L U (recode v) (succ (succ t)) x)
      (pw two k+pw two t) (pw two k*pw two t) := by
  let S := sourceSchedule U W
  let p := leftOffset S a b u v x
  let q := rightOffset S a b u v x
  let o := p+q
  let j := leftWeightFor a b u v
  let l := rightWeightFor a b u v
  let m := shiftWeightFor a b u v
  let A := sourceLeft a
  let B := sourceRight b
  let C := recode u
  let E := recode v
  let D := enlargedDen a b u v
  let P := firstNumerator a b*endpointDen u v
  let Q := secondNumerator a b*endpointDen u v
  let X := interiorNumerator a b u v
  let Y := interiorNumerator a b v u
  have g := original_geometry a b u v h
  have eq := source_queries a b u v h
  have hd' := g.andE₁
  have hP := g.andE₂.andE₁
  have hX := le_trans hP g.andE₂.andE₂.andE₁
  have hY := le_trans hX g.andE₂.andE₂.andE₂.andE₁
  have hQ := le_trans hY g.andE₂.andE₂.andE₂.andE₂
  have pa := presentation_at L U W A x hp (positive_fraction P (two*D) A hP
    (RationalAlgebra.positive_product (le_succ_self one) hd') eq.andE₁)
  have pb := presentation_at L U W B x hp (positive_fraction (Q+D) D B (le_trans hQ (le_add_right _ _)) hd' eq.andE₂.andE₁)
  have pc := presentation_at L U W C x hp (positive_fraction X D C hX hd' eq.andE₂.andE₂.andE₁)
  have pe := presentation_at L U W E x hp (positive_fraction Y D E hY hd' eq.andE₂.andE₂.andE₂)
  have lp : Γ ⊢[PRAAx] le p o := le_add_right _ _
  have rq : Γ ⊢[PRAAx] le q o := by dsimp only [o]; ipra_le 𝔟 p
  have lp' := le_trans (cutoff_le_schedule U W E A C j m x) lp
  have rq' := le_trans (cutoff_le_schedule U W C B E l m x) rq
  have ep := cutoff_bounds (Γ := Γ) W E A C x
  have eq' := cutoff_bounds (Γ := Γ) W C B E x
  have hpts : Γ ⊢[PRAAx] sourceInputs L U W a b u v o x := .andI (.andI pa (le_trans ep.andE₂.andE₁ lp'))
    (.andI (.andI pb (le_trans eq'.andE₂.andE₁ rq'))
      (.andI (.andI pc (le_trans ep.andE₂.andE₂ lp')) (.andI pe (le_trans ep.andE₁ lp'))))
  have sec := source_secants L U S a b u v x h hc
  have both : Γ ⊢[PRAAx] sourcePowerComparisons L U a b u v o x := .andI
    (retain_source_order L U W E A C j m o x (.andI pe (.andI pa pc)) lp sec.andE₁)
    (retain_source_order L U W C B E l m o x (.andI pc (.andI pb pe)) rq sec.andE₂)
  exact original_named_modulus L U W a b u v k t o x h hpts both hd

theorem original_scheduled_named_modulus_closed (L U : PR 3) (W : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (arguments (var 0) (var 1) (var 2) (var 3) ⟶
      positivePresentation L U W (var 6) ⟶ rule L U (sourceSchedule U W) (var 6) ⟶
      radius (var 2) (var 3) one (pw two (clock (centerF L U) (var 0) (var 1) (var 4) (var 6))) ⟶
      radius (center L U (recode (var 2)) (succ (succ (var 5))) (var 6))
        (center L U (recode (var 3)) (succ (succ (var 5))) (var 6))
        (pw two (var 4)+pw two (var 5)) (pw two (var 4)*pw two (var 5))) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (actual_original_scheduled_modulus L U W _ _ _ _ _ _ _
    (.hyp (by simp)) hyp2 Prf.hyp1 Prf.hyp0)))))

def inInterval (a b u v : PTm n) : Fm PTm n :=
  rationalLT (natCode zero) a ⋏ (RationalArgmin.rationalLE a u ⋏ (RationalArgmin.rationalLE a v ⋏
    (RationalArgmin.rationalLE u b ⋏ RationalArgmin.rationalLE v b)))

theorem actual_scheduled_modulus_on_interval (L U : PR 3) (W : PR 2) (a b u v k t x : PTm n)
    (h : Γ ⊢[PRAAx] inInterval a b u v) (hp : Γ ⊢[PRAAx] positivePresentation L U W x)
    (hc : Γ ⊢[PRAAx] rule L U (sourceSchedule U W) x)
    (hd : Γ ⊢[PRAAx] radius u v one (pw two (clock (centerF L U) a b k x))) :
    Γ ⊢[PRAAx] radius (center L U (recode u) (succ (succ t)) x) (center L U (recode v) (succ (succ t)) x)
      (pw two k+pw two t) (pw two k*pw two t) := by
  refine .orE (RationalArgmin.total u v) ?_ ?_
  · have h' := h.wk (ψ := RationalArgmin.rationalLE u v)
    exact actual_original_scheduled_modulus L U W a b u v k t x
      (.andI h'.andE₁ (.andI h'.andE₂.andE₁ (.andI Prf.hyp0 h'.andE₂.andE₂.andE₂.andE₂))) hp.wk hc.wk hd.wk
  · have h' := h.wk (ψ := RationalArgmin.rationalLE v u)
    have r := actual_original_scheduled_modulus L U W a b v u k t x
      (.andI h'.andE₁ (.andI h'.andE₂.andE₂.andE₁ (.andI Prf.hyp0 h'.andE₂.andE₂.andE₂.andE₁))) hp.wk hc.wk
        (RationalValueBounds.radius_symmetric _ _ _ _ hd.wk)
    exact RationalValueBounds.radius_symmetric _ _ _ _ r

theorem original_scheduled_modulus_on_interval_closed (L U : PR 3) (W : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (inInterval (var 0) (var 1) (var 2) (var 3) ⟶
      positivePresentation L U W (var 6) ⟶ rule L U (sourceSchedule U W) (var 6) ⟶
      radius (var 2) (var 3) one (pw two (clock (centerF L U) (var 0) (var 1) (var 4) (var 6))) ⟶
      radius (center L U (recode (var 2)) (succ (succ (var 5))) (var 6))
        (center L U (recode (var 3)) (succ (succ (var 5))) (var 6))
        (pw two (var 4)+pw two (var 5)) (pw two (var 4)*pw two (var 5))) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (actual_scheduled_modulus_on_interval L U W _ _ _ _ _ _ _
    (.hyp (by simp)) hyp2 Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.RationalConvexScheduledModulus
