import IPRADerivations.Analysis.Optimization.Aggregates.AggregateApproximateImage
import IPRADerivations.Analysis.Names.Aggregation.AggregateDistanceName

/-!
# The prescribed action of an approximate map on point names

Finite-demand Section 3 defines fhat(U)(k)=f(U(k+c),k+c). This actual fixed
PR program is regular and respects equivalent point names. Original support
membership transports forward to the SAME actual approximate image lists,
using a real finite selected source neighbor. No preimage is selected from
an arbitrary named image point, and no completed-function law is supplied.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.AggregateApproximatePointMap

open_ipra
open AggregateEquality (sample unit unit_positive nonempty nonempty_at regular)
open AggregateOptimization (evaluate pointRegular pointRegular_at supportZero errorNumerator errorDenominator)
open AggregateApproximateImage (mapContract map_at data clock)
open RationalHausdorff (pointRadius)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def mapped (U : PR 2) (f : PR 3) (k c x : PTm n) : PTm n := evaluate f (sample U (k+c) x) (k+c) x
def body (U : PR 2) (f : PR 3) : PTm 2 := mapped U f (var 0) (fstT (var 1)) (sndT (var 1))
def pointF (U : PR 2) (f : PR 3) : PR 2 := PTm.toPR (body U f)
ipra_subst mapped

theorem point_at (U : PR 2) (f : PR 3) (k c x : PTm n) : Γ ⊢[PRAAx]
    sample (pointF U f) k (data c x) ≐ mapped U f k c x := by
  have reified : Γ ⊢[PRAAx] sample (pointF U f) k (data c x) ≐ mapped U f k (fstT (data c x)) (sndT (data c x)) := by
    let b := body U f
    change Γ ⊢[PRAAx] PTm.app (PTm.toPR b) ![k,data c x] ≐ mapped U f k (fstT (data c x)) (sndT (data c x))
    simpa [b,body] using toPR_eq (Γ := Γ) b ![k,data c x]
  exact reified.eqTrans (congrAp3 f (congrAp2 U (congrAdd (.eqRefl _) (fst_pair _ _)) (snd_pair _ _))
    (congrAdd (.eqRefl _) (fst_pair _ _)) (snd_pair _ _))

theorem point_regular_pair (U : PR 2) (f : PR 3) (d e A B c x s t : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c))
    (hU : Γ ⊢[PRAAx] pointRegular U d x) (hmap : Γ ⊢[PRAAx] mapContract f d e A B x) : Γ ⊢[PRAAx]
    pointRadius (mapped U f s c x) (mapped U f t c x) e (unit s+unit t) (unit s*unit t) := by
  have source := pointRegular_at U (s+c) (t+c) d x hU
  have actual := map_at f d e A B x (sample U (s+c) x) (sample U (t+c) x) (s+c) (t+c)
    (unit (s+c)+unit (t+c)) (unit (s+c)*unit (t+c)) hmap source
  exact AggregateChain.point_mono _ _ _ _ _ _ _
    (AggregateApproximateImage.denominator_positive B (unit (s+c)*unit (t+c)) (s+c) (t+c) hB
      (AggregateApproximateImage.positive_product _ _ (unit_positive _) (unit_positive _))) actual
    (AggregateApproximateImage.regular_budget A B c s t hc)

theorem point_regular (U : PR 2) (f : PR 3) (d e A B c x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c))
    (hU : Γ ⊢[PRAAx] pointRegular U d x) (hmap : Γ ⊢[PRAAx] mapContract f d e A B x) :
    Γ ⊢[PRAAx] pointRegular (pointF U f) e (data c x) := by
  refine .allI (.allI ?_)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let D := Syn.shift (Syn.shift d)
  let E := Syn.shift (Syn.shift e)
  let a := Syn.shift (Syn.shift A)
  let b := Syn.shift (Syn.shift B)
  let c' := Syn.shift (Syn.shift c)
  let y := Syn.shift (Syn.shift x)
  have b' : Δ ⊢[PRAAx] le one b := by simpa [Δ,b,Fm.shift,Syn.shift,one] using hB.shift.shift
  have clock : Δ ⊢[PRAAx] le (a+b) (b*unit c') := by simpa [Δ,a,b,c',Fm.shift,Syn.shift] using hc.shift.shift
  have reg : Δ ⊢[PRAAx] pointRegular U D y := by simpa [Δ,D,y,Fm.shift,Syn.shift] using hU.shift.shift
  have law : Δ ⊢[PRAAx] mapContract f D E a b y := by simpa [Δ,D,E,a,b,y,Fm.shift,Syn.shift] using hmap.shift.shift
  simpa [Δ,D,E,a,b,c',y,Syn.shift] using AggregateChain.point_congr (point_at U f (var 1) c' y).eqSymm
    (point_at U f (var 0) c' y).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (point_regular_pair U f D E a b c' y (var 1) (var 0) b' clock reg law)

theorem point_equivalent_pair (U V : PR 2) (f : PR 3) (d e A B c x k : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c))
    (hUV : Γ ⊢[PRAAx] AggregateDistanceName.pointEquivalent U V d x)
    (hmap : Γ ⊢[PRAAx] mapContract f d e A B x) : Γ ⊢[PRAAx]
    pointRadius (mapped U f k c x) (mapped V f k c x) e two (unit k) := by
  have source := AggregateDistanceName.point_equivalent_at U V (k+c) d x hUV
  have actual := map_at f d e A B x (sample U (k+c) x) (sample V (k+c) x) (k+c) (k+c) two (unit (k+c)) hmap source
  exact AggregateChain.point_mono _ _ _ _ _ _ _
    (AggregateApproximateImage.denominator_positive B (unit (k+c)) (k+c) (k+c) hB (unit_positive _)) actual
    (AggregateApproximateImage.equivalent_budget A B c k hc)

theorem point_equivalent (U V : PR 2) (f : PR 3) (d e A B c x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c))
    (hUV : Γ ⊢[PRAAx] AggregateDistanceName.pointEquivalent U V d x)
    (hmap : Γ ⊢[PRAAx] mapContract f d e A B x) :
    Γ ⊢[PRAAx] AggregateDistanceName.pointEquivalent (pointF U f) (pointF V f) e (data c x) := by
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let D := Syn.shift d
  let E := Syn.shift e
  let a := Syn.shift A
  let b := Syn.shift B
  let c' := Syn.shift c
  let y := Syn.shift x
  have b' : Δ ⊢[PRAAx] le one b := by simpa [Δ,b,Fm.shift,Syn.shift,one] using hB.shift
  have clock : Δ ⊢[PRAAx] le (a+b) (b*unit c') := by simpa [Δ,a,b,c',Fm.shift,Syn.shift] using hc.shift
  have eqv : Δ ⊢[PRAAx] AggregateDistanceName.pointEquivalent U V D y := by simpa [Δ,D,y,Fm.shift,Syn.shift] using hUV.shift
  have law : Δ ⊢[PRAAx] mapContract f D E a b y := by simpa [Δ,D,E,a,b,y,Fm.shift,Syn.shift] using hmap.shift
  simpa [Δ,D,E,a,b,c',y,Syn.shift,two,one] using AggregateChain.point_congr (point_at U f (var 0) c' y).eqSymm
    (point_at V f (var 0) c' y).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (point_equivalent_pair U V f D E a b c' y (var 0) b' clock eqv law)

theorem support_budget (A B c k : PTm n) (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c)) : Γ ⊢[PRAAx] le
    (errorNumerator A B (unit (succ k+c)+unit (succ k+c)) (unit (succ k+c)*unit (succ k+c)) (succ k+c) (succ k+c)*unit k)
    (one*errorDenominator B (unit (succ k+c)*unit (succ k+c)) (succ k+c) (succ k+c)) := by
  have add := natEq (AggregateChain.unit_add (Γ := Γ) (succ k) c)
  have step := natEq (AggregateChain.unit_succ (Γ := Γ) k)
  refine le_congr ?_ ?_ (mul_le_mul_right (two*unit (succ k+c)*unit (succ k+c)*unit (succ k+c)*unit k) hc)
  all_goals
    apply deriveNat
    simp only [errorNumerator,errorDenominator]
    ipra_simps
    rw [add,step]
    ring

theorem mapped_point_hit (U S : PR 2) (f : PR 3) (d e A B c x k : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c))
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hU : Γ ⊢[PRAAx] pointRegular U d x) (hs : Γ ⊢[PRAAx] supportZero U S d x)
    (hmap : Γ ⊢[PRAAx] mapContract f d e A B x) : Γ ⊢[PRAAx]
    RationalPointDistance.pointHit (sample (pointF U f) (succ k) (data c x))
      (sample (AggregateApproximateImage.nameF S f) (succ k) (data c x)) e one (unit k) := by
  let p := succ k+c
  let T := sample S p x
  let q := sample U p x
  let j := RationalPointDistance.selected q T d
  have hj : Γ ⊢[PRAAx] lt j (length T) := RationalPointDistance.selected_spec q T d (nonempty_at S p x hS)
  have original : Γ ⊢[PRAAx] pointRadius q (entry T j) d (unit p+unit p) (unit p*unit p) :=
    AggregateOptimization.support_nearby U S p p d x hS hR hU hs
  have mappedPair := map_at f d e A B x q (entry T j) p p (unit p+unit p) (unit p*unit p) hmap original
  have pointCode : Γ ⊢[PRAAx] sample (pointF U f) (succ k) (data c x) ≐ evaluate f q p x := point_at U f (succ k) c x
  have listCode : Γ ⊢[PRAAx] entry (sample (AggregateApproximateImage.nameF S f) (succ k) (data c x)) j ≐
      evaluate f (entry T j) p x :=
    (entry_congr (AggregateApproximateImage.name_at S f (succ k) c x) (.eqRefl _)).eqTrans
      (AggregateApproximateImage.name_lookup S f (succ k) c x j hj)
  have output : Γ ⊢[PRAAx] pointRadius (sample (pointF U f) (succ k) (data c x))
      (entry (sample (AggregateApproximateImage.nameF S f) (succ k) (data c x)) j) e
      (errorNumerator A B (unit p+unit p) (unit p*unit p) p p) (errorDenominator B (unit p*unit p) p p) :=
    AggregateChain.point_congr pointCode.eqSymm listCode.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) mappedPair
  have relaxed : Γ ⊢[PRAAx] pointRadius (sample (pointF U f) (succ k) (data c x))
      (entry (sample (AggregateApproximateImage.nameF S f) (succ k) (data c x)) j) e one (unit k) :=
    AggregateChain.point_mono _ _ _ _ _ _ _
      (AggregateApproximateImage.denominator_positive B (unit p*unit p) p p hB
        (AggregateApproximateImage.positive_product _ _ (unit_positive _) (unit_positive _))) output (support_budget A B c k hc)
  have range : Γ ⊢[PRAAx] lt j (length (sample (AggregateApproximateImage.nameF S f) (succ k) (data c x))) :=
    lt_congr (.eqRefl _) ((congrFst (AggregateApproximateImage.name_at S f (succ k) c x)).eqTrans
      (AggregateApproximateImage.name_length S f (succ k) c x)).eqSymm hj
  refine .exI j ?_
  simpa [RationalPointDistance.pointHit] using Prf.andI range relaxed

theorem support_bound (U S : PR 2) (f : PR 3) (d e A B c x k : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c))
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hU : Γ ⊢[PRAAx] pointRegular U d x) (hs : Γ ⊢[PRAAx] supportZero U S d x)
    (hmap : Γ ⊢[PRAAx] mapContract f d e A B x) : Γ ⊢[PRAAx] le
    (unit k*RationalPointDistance.numerator (sample (pointF U f) (succ k) (data c x))
      (sample (AggregateApproximateImage.nameF S f) (succ k) (data c x)) e)
    (RationalPointDistance.denominator (sample (pointF U f) (succ k) (data c x))
      (sample (AggregateApproximateImage.nameF S f) (succ k) (data c x)) e) :=
  le_congr (.eqRefl _) (one_mul _) (RationalPointDistance.bound_of_point_hit _ _ _ _ _
    (mapped_point_hit U S f d e A B c x k hB hc hS hR hU hs hmap))

theorem support_preserved (U S : PR 2) (f : PR 3) (d e A B c x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c))
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hU : Γ ⊢[PRAAx] pointRegular U d x) (hs : Γ ⊢[PRAAx] supportZero U S d x)
    (hmap : Γ ⊢[PRAAx] mapContract f d e A B x) : Γ ⊢[PRAAx]
    supportZero (pointF U f) (AggregateApproximateImage.nameF S f) e (data c x) := by
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let D := Syn.shift d
  let E := Syn.shift e
  let a := Syn.shift A
  let b := Syn.shift B
  let c' := Syn.shift c
  let y := Syn.shift x
  have b' : Δ ⊢[PRAAx] le one b := by simpa [Δ,b,Fm.shift,Syn.shift,one] using hB.shift
  have clock : Δ ⊢[PRAAx] le (a+b) (b*unit c') := by simpa [Δ,a,b,c',Fm.shift,Syn.shift] using hc.shift
  have ne : Δ ⊢[PRAAx] nonempty S y := by simpa [Δ,y,Fm.shift,Syn.shift] using hS.shift
  have reg : Δ ⊢[PRAAx] regular S D y := by simpa [Δ,D,y,Fm.shift,Syn.shift] using hR.shift
  have point : Δ ⊢[PRAAx] pointRegular U D y := by simpa [Δ,D,y,Fm.shift,Syn.shift] using hU.shift
  have supp : Δ ⊢[PRAAx] supportZero U S D y := by simpa [Δ,D,y,Fm.shift,Syn.shift] using hs.shift
  have law : Δ ⊢[PRAAx] mapContract f D E a b y := by simpa [Δ,D,E,a,b,y,Fm.shift,Syn.shift] using hmap.shift
  simpa [Δ,D,E,a,b,c',y,Syn.shift] using support_bound U S f D E a b c' y (var 0) b' clock ne reg point supp law

/-- All output-name and membership properties are conclusions of original contracts. -/
theorem computed_certificate (U S : PR 2) (f : PR 3) (d e A B x : PTm n)
    (h : Γ ⊢[PRAAx] AggregateApproximateImage.input S f d e A B x)
    (hU : Γ ⊢[PRAAx] pointRegular U d x) (hs : Γ ⊢[PRAAx] supportZero U S d x) : Γ ⊢[PRAAx]
    pointRegular (pointF U f) e (data (clock A B) x) ⋏
      (supportZero (pointF U f) (AggregateApproximateImage.nameF S f) e (data (clock A B) x) ⋏
        (nonempty (AggregateApproximateImage.nameF S f) (data (clock A B) x) ⋏
          regular (AggregateApproximateImage.nameF S f) e (data (clock A B) x))) := by
  have b : Γ ⊢[PRAAx] le one B := .andE₁ h
  have ne : Γ ⊢[PRAAx] nonempty S x := .andE₁ (.andE₂ h)
  have reg : Γ ⊢[PRAAx] regular S d x := .andE₁ (.andE₂ (.andE₂ h))
  have law : Γ ⊢[PRAAx] mapContract f d e A B x := .andE₂ (.andE₂ (.andE₂ h))
  have budget := AggregateApproximateImage.clock_budget A B b
  exact .andI (point_regular U f d e A B _ x b budget hU law)
    (.andI (support_preserved U S f d e A B _ x b budget ne reg hU hs law)
      (AggregateApproximateImage.input_certificate S f d e A B x h))

def computed (U : PR 2) (f : PR 3) (k A B x : PTm n) : PTm n := mapped U f k (clock A B) x
def computedF (U : PR 2) (f : PR 3) : PR 4 := PTm.toPR (computed U f (var 0) (var 1) (var 2) (var 3))
ipra_subst computed

theorem computed_at (U : PR 2) (f : PR 3) (k A B x : PTm n) : Γ ⊢[PRAAx]
    PTm.app (computedF U f) ![k,A,B,x] ≐ computed U f k A B x := by
  simpa only [computedF,subst_computed,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
    toPR_eq (Γ := Γ) (computed U f (var 0) (var 1) (var 2) (var 3) : PTm 4) ![k,A,B,x]

theorem actual_approximate_point_program_closed (U : PR 2) (f : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (sample (pointF U f) (var 0) (data (var 1) (var 2)) ≐
      evaluate f (sample U (var 0+var 1) (var 2)) (var 0+var 1) (var 2)) := closeUniv 3 (point_at U f _ _ _)

theorem actual_approximate_point_regular_closed (U : PR 2) (f : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 3) ⟶ pointRegular U (var 0) (var 4) ⟶ mapContract f (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      pointRegular (pointF U f) (var 1) (data (clock (var 2) (var 3)) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (point_regular U f _ _ _ _ _ _ Prf.hyp1.wk
    (AggregateApproximateImage.clock_budget _ _ Prf.hyp1.wk) Prf.hyp1 Prf.hyp0))))

theorem actual_approximate_point_equivalent_closed (U V : PR 2) (f : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 3) ⟶ AggregateDistanceName.pointEquivalent U V (var 0) (var 4) ⟶
      mapContract f (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
        AggregateDistanceName.pointEquivalent (pointF U f) (pointF V f) (var 1) (data (clock (var 2) (var 3)) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (point_equivalent U V f _ _ _ _ _ _ Prf.hyp1.wk
    (AggregateApproximateImage.clock_budget _ _ Prf.hyp1.wk) Prf.hyp1 Prf.hyp0))))

theorem actual_approximate_image_support_closed (U S : PR 2) (f : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (AggregateApproximateImage.input S f (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      pointRegular U (var 0) (var 4) ⟶ supportZero U S (var 0) (var 4) ⟶
        (pointRegular (pointF U f) (var 1) (data (clock (var 2) (var 3)) (var 4)) ⋏
          (supportZero (pointF U f) (AggregateApproximateImage.nameF S f) (var 1) (data (clock (var 2) (var 3)) (var 4)) ⋏
            (nonempty (AggregateApproximateImage.nameF S f) (data (clock (var 2) (var 3)) (var 4)) ⋏
              regular (AggregateApproximateImage.nameF S f) (var 1) (data (clock (var 2) (var 3)) (var 4)))))) :=
  closeUniv 5 (.impI (.impI (.impI (computed_certificate U S f _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem actual_computed_approximate_point_closed (U : PR 2) (f : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (PTm.app (computedF U f) ![var 0,var 1,var 2,var 3] ≐
      evaluate f (sample U (var 0+clock (var 1) (var 2)) (var 3)) (var 0+clock (var 1) (var 2)) (var 3)) :=
  closeUniv 4 (computed_at U f _ _ _ _)

end LeanProofs.IPRA.Analysis.AggregateApproximatePointMap
