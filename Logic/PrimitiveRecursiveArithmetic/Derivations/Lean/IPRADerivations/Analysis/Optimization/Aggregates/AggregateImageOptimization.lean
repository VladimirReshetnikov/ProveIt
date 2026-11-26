import IPRADerivations.Analysis.Optimization.Aggregates.AggregateApproximatePointMap

/-!
# Actual optimization on a produced approximate image

Finite-demand Section 3 composes the actual image and optimization producers.
The image clock and original persistent data are kept separate. The scalar
objective drops only that clock from its numerical data; its original map
contract is transported, not assumed anew. Actual source-index scans recover
the exact finite image minimizer, including the original least tie rule.
Original supported point names give both represented optimization bounds by
forward image support. No image preimage, exact optimizer or cross-k coherence
is selected.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.AggregateImageOptimization

open_ipra
open AggregateEquality (sample unit nonempty regular)
open AggregateOptimization (evaluate pointRegular supportZero)
open AggregateApproximateImage (data clock nameF)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The SAME objective and original data, with only the image-clock field removed. -/
def liftObjective (g : PR 3) : PR 3 := PTm.toPR (evaluate g (var 0) (var 1) (sndT (var 2)))

theorem lifted_at (g : PR 3) (q p c x : PTm n) : Γ ⊢[PRAAx]
    evaluate (liftObjective g) q p (data c x) ≐ evaluate g q p x := by
  have code : Γ ⊢[PRAAx] evaluate (liftObjective g) q p (data c x) ≐ evaluate g q p (sndT (data c x)) := by
    let b : PTm 3 := evaluate g (var 0) (var 1) (sndT (var 2))
    change Γ ⊢[PRAAx] PTm.app (PTm.toPR b) ![q,p,data c x] ≐ evaluate g q p (sndT (data c x))
    simpa only [b,AggregateOptimization.subst_evaluate,subst_sndT,Syn.subst_var,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) b ![q,p,data c x]
  exact code.eqTrans (congrAp3 g (.eqRefl q) (.eqRefl p) (snd_pair _ _))

theorem lifted_contract (g : PR 3) (e C D c x : PTm n)
    (h : Γ ⊢[PRAAx] AggregateOptimization.mapContract g e C D x) : Γ ⊢[PRAAx]
    AggregateOptimization.mapContract (liftObjective g) e C D (data c x) := by
  refine .allI (.impI ?_)
  let Δ := (RationalHausdorff.pointRadius (AggregateOptimization.argument 0 (var 0))
    (AggregateOptimization.argument 1 (var 0)) (Syn.shift e) (AggregateOptimization.argument 4 (var 0))
    (AggregateOptimization.argument 5 (var 0))) :: Γ.map Fm.shift
  have h' : Δ ⊢[PRAAx] AggregateOptimization.mapContract g (Syn.shift e) (Syn.shift C) (Syn.shift D) (Syn.shift x) := by
    simpa [Δ,Fm.shift,Syn.shift] using h.shift.wk
  have actual := AggregateOptimization.mapContract_at g (Syn.shift e) (Syn.shift C) (Syn.shift D) (Syn.shift x)
    (AggregateOptimization.argument 0 (var 0)) (AggregateOptimization.argument 1 (var 0))
    (AggregateOptimization.argument 2 (var 0)) (AggregateOptimization.argument 3 (var 0))
    (AggregateOptimization.argument 4 (var 0)) (AggregateOptimization.argument 5 (var 0)) h' Prf.hyp0
  simpa [Δ,Syn.shift] using RationalValueBounds.radius_congr
    (lifted_at g _ _ (Syn.shift c) (Syn.shift x)).eqSymm
    (lifted_at g _ _ (Syn.shift c) (Syn.shift x)).eqSymm (.eqRefl _) (.eqRefl _) actual

/-- Bounded individual code equality is enough for the actual least argmin
scans to agree, even with ties and independently denominated raw values. -/
def valuesAgree (v w : PR 2) (K x y : PTm n) : Fm PTm n := .all
  (le (var 0) (Syn.shift K) ⟶ RationalArgmin.value v (var 0) (Syn.shift x) ≐ RationalArgmin.value w (var 0) (Syn.shift y))
ipra_subst valuesAgree [Syn.subst_shift, Syn.shift_subst]

theorem agree_at (v w : PR 2) (K x y i : PTm n) (h : Γ ⊢[PRAAx] valuesAgree v w K x y)
    (hi : Γ ⊢[PRAAx] le i K) : Γ ⊢[PRAAx] RationalArgmin.value v i x ≐ RationalArgmin.value w i y := by
  have a : Γ ⊢[PRAAx] le i K ⟶ RationalArgmin.value v i x ≐ RationalArgmin.value w i y := by
    simpa [valuesAgree] using h.allE i
  exact .impE a hi

theorem selected_transport (v w : PR 2) (K x y : PTm n) (h : Γ ⊢[PRAAx] valuesAgree v w K x y) :
    Γ ⊢[PRAAx] RationalArgmin.selected v K x ≐ RationalArgmin.selected w K y := by
  let i := RationalArgmin.selected v K x
  let j := RationalArgmin.selected w K y
  have hi := RationalArgmin.selected_spec (Γ := Γ) v K x
  have hj := RationalArgmin.selected_spec (Γ := Γ) w K y
  have ei := agree_at v w K x y i h hi
  have ej := agree_at v w K x y j h hj
  have vij := RationalArgmin.selected_minimal v K j x hj
  have wji := RationalArgmin.selected_minimal w K i y hi
  have vji := RationalArgmin.rationalLE_congr ej.eqSymm ei.eqSymm wji
  have wij := RationalArgmin.rationalLE_congr ei ej vij
  exact le_antisymm
    (RationalArgmin.selected_least v K j x (RationalArgmin.antisymm vji vij))
    (RationalArgmin.selected_least w K i y (RationalArgmin.antisymm wij wji))

def pullbackData (s c x : PTm n) : PTm n := pairT s (pairT c x)
def pullbackValue (S : PR 2) (f g : PR 3) (i s c x : PTm n) : PTm n :=
  evaluate g (evaluate f (entry (sample S (s+c) x) i) (s+c) x) s x
def pullbackBody (S : PR 2) (f g : PR 3) : PTm 2 :=
  pullbackValue S f g (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1)))
def pullbackF (S : PR 2) (f g : PR 3) : PR 2 := PTm.toPR (pullbackBody S f g)
def pullbackIndex (S : PR 2) (f g : PR 3) (s c x : PTm n) : PTm n :=
  RationalArgmin.selected (pullbackF S f g) (pred (length (sample S (s+c) x))) (pullbackData s c x)

ipra_subst pullbackData
ipra_subst pullbackValue
ipra_subst pullbackIndex

theorem pullback_at (S : PR 2) (f g : PR 3) (i s c x : PTm n) : Γ ⊢[PRAAx]
    RationalArgmin.value (pullbackF S f g) i (pullbackData s c x) ≐ pullbackValue S f g i s c x := by
  have raw : Γ ⊢[PRAAx] RationalArgmin.value (pullbackF S f g) i (pullbackData s c x) ≐
      pullbackValue S f g i (fstT (pullbackData s c x)) (fstT (sndT (pullbackData s c x))) (sndT (sndT (pullbackData s c x))) := by
    simpa [RationalArgmin.value,ap2,pullbackF,pullbackBody] using
      toPR_eq (Γ := Γ) (pullbackBody S f g) ![i,pullbackData s c x]
  have ss := fst_pair (Γ := Γ) s (pairT c x)
  have cc : Γ ⊢[PRAAx] fstT (sndT (pullbackData s c x)) ≐ c := (snd_pair s (pairT c x)).fstE
  have xx : Γ ⊢[PRAAx] sndT (sndT (pullbackData s c x)) ≐ x := (snd_pair s (pairT c x)).sndE
  exact raw.eqTrans (congrAp3 g
    (congrAp3 f (entry_congr (congrAp2 S (congrAdd ss cc) xx) (.eqRefl i)) (congrAdd ss cc) xx) ss xx)

theorem image_length (S : PR 2) (f : PR 3) (s c x : PTm n) : Γ ⊢[PRAAx]
    length (sample (nameF S f) s (data c x)) ≐ length (sample S (s+c) x) :=
  (congrFst (AggregateApproximateImage.name_at S f s c x)).eqTrans (AggregateApproximateImage.name_length S f s c x)

theorem image_stage_value (S : PR 2) (f g : PR 3) (s c x i : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (length (sample S (s+c) x))) : Γ ⊢[PRAAx]
    RationalArgmin.value (AggregateOptimization.stageValues (nameF S f) (liftObjective g)) i (pairT s (data c x)) ≐
      pullbackValue S f g i s c x := by
  have actual := AggregateOptimization.stageValues_at (Γ := Γ) (nameF S f) (liftObjective g) s i (data c x)
  have point : Γ ⊢[PRAAx] entry (sample (nameF S f) s (data c x)) i ≐ evaluate f (entry (sample S (s+c) x) i) (s+c) x :=
    (entry_congr (AggregateApproximateImage.name_at S f s c x) (.eqRefl i)).eqTrans
      (AggregateApproximateImage.name_lookup S f s c x i hi)
  exact actual.eqTrans ((lifted_at g _ s c x).eqTrans (congrAp3 g point (.eqRefl _) (.eqRefl _)))

theorem image_minimum_index (S : PR 2) (f g : PR 3) (s c x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) : Γ ⊢[PRAAx]
    AggregateOptimization.minimumIndex (nameF S f) (liftObjective g) s (data c x) ≐ pullbackIndex S f g s c x := by
  let K := pred (length (sample S (s+c) x))
  have agree : Γ ⊢[PRAAx] valuesAgree (AggregateOptimization.stageValues (nameF S f) (liftObjective g))
      (pullbackF S f g) K (pairT s (data c x)) (pullbackData s c x) := by
    refine .allI (.impI ?_)
    let Δ := le (var 0) (Syn.shift K) :: Γ.map Fm.shift
    have len : Δ ⊢[PRAAx] length (sample S (Syn.shift s+Syn.shift c) (Syn.shift x)) ≐
        succ (pred (length (sample S (Syn.shift s+Syn.shift c) (Syn.shift x)))) :=
      AnalyticNumberTheory.Primes.eq_succ_pred ((eq_add_of_le
        (AggregateEquality.nonempty_at S (Syn.shift s+Syn.shift c) (Syn.shift x)
          (by simpa [Δ,Fm.shift,Syn.shift] using hS.shift.wk))).eqTrans (by ipra_ring))
    have hk : Δ ⊢[PRAAx] le (var 0) (pred (length (sample S (Syn.shift s+Syn.shift c) (Syn.shift x)))) := by
      simpa only [Δ,K,Syn.shift,PTm.subst_pred,Foundations.SequenceComposition.subst_length,AggregateEquality.subst_sample,PTm.subst_add] using (Prf.hyp0 : Δ ⊢[PRAAx] le (var 0) (Syn.shift K))
    have hi : Δ ⊢[PRAAx] lt (var 0) (length (sample S (Syn.shift s+Syn.shift c) (Syn.shift x))) :=
      le_congr (.eqRefl _) len.eqSymm
        ((succ_monus_succ (var 0) (pred (length (sample S (Syn.shift s+Syn.shift c) (Syn.shift x))))).eqTrans hk)
    simpa [Δ,K,Syn.shift] using (image_stage_value S f g (Syn.shift s) (Syn.shift c) (Syn.shift x) (var 0) hi).eqTrans
      (pullback_at S f g (var 0) (Syn.shift s) (Syn.shift c) (Syn.shift x)).eqSymm
  have horizon := congrPred (image_length (Γ := Γ) S f s c x)
  exact (congrAp2 (RationalArgmin.selectedF (AggregateOptimization.stageValues (nameF S f) (liftObjective g))) horizon (.eqRefl _)).eqTrans
    (selected_transport _ _ K _ _ agree)

theorem image_minimum_value (S : PR 2) (f g : PR 3) (s c x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) : Γ ⊢[PRAAx]
    AggregateOptimization.minimumValue (nameF S f) (liftObjective g) s (data c x) ≐
      pullbackValue S f g (pullbackIndex S f g s c x) s c x := by
  let i := AggregateOptimization.minimumIndex (nameF S f) (liftObjective g) s (data c x)
  have hi : Γ ⊢[PRAAx] lt i (length (sample S (s+c) x)) :=
    lt_congr (.eqRefl _) (image_length S f s c x)
      (AggregateOptimization.minimum_index_range (nameF S f) (liftObjective g) s (data c x)
        (AggregateApproximateImage.name_nonempty S f c x hS))
  have a := (AggregateOptimization.stageValues_at (Γ := Γ) (nameF S f) (liftObjective g) s i (data c x)).eqSymm.eqTrans
    (image_stage_value S f g s c x i hi)
  exact a.eqTrans (congrAp3 g (congrAp3 f
    (entry_congr (.eqRefl _) (image_minimum_index S f g s c x hS)) (.eqRefl _) (.eqRefl _)) (.eqRefl _) (.eqRefl _))

def input (S : PR 2) (f g : PR 3) (d e A B C D x : PTm n) : Fm PTm n :=
  AggregateApproximateImage.input S f d e A B x ⋏
    (le one D ⋏ AggregateOptimization.mapContract g e C D x)
ipra_subst input

theorem image_optimization (S : PR 2) (f g : PR 3) (d e A B C D x : PTm n)
    (h : Γ ⊢[PRAAx] input S f g d e A B C D x) : Γ ⊢[PRAAx]
    AggregateOptimization.optimizationResult (nameF S f) (liftObjective g)
      (AggregateOptimization.coarseWitnessShift C D) (AggregateOptimization.coarseValueShift C D) e (data (clock A B) x) := by
  have image := AggregateApproximateImage.input_certificate S f d e A B x (.andE₁ h)
  exact AggregateOptimization.aggregate_optimization_coarse (nameF S f) (liftObjective g) e C D _
    (.andE₁ (.andE₂ h)) (.andE₁ image) (.andE₂ image)
    (lifted_contract g e C D _ x (.andE₂ (.andE₂ h)))

/-- Every original represented support point supplies a genuine competitor
for the actual image optimization. Both bounds use the original scalar map. -/
theorem mapped_named_bounds (U S : PR 2) (f g : PR 3) (d e A B C D x : PTm n)
    (h : Γ ⊢[PRAAx] input S f g d e A B C D x)
    (hU : Γ ⊢[PRAAx] pointRegular U d x) (hs : Γ ⊢[PRAAx] supportZero U S d x) : Γ ⊢[PRAAx]
    AggregateOptimization.namedLower (AggregateApproximatePointMap.pointF U f) (nameF S f) (liftObjective g)
      (AggregateOptimization.coarseValueShift C D) (data (clock A B) x) ⋏
    AggregateOptimization.namedUpper (AggregateApproximatePointMap.pointF U f) (nameF S f) (liftObjective g)
      (AggregateOptimization.coarseValueShift C D) (data (clock A B) x) := by
  have image := AggregateApproximateImage.input_certificate S f d e A B x (.andE₁ h)
  have point := AggregateApproximatePointMap.computed_certificate U S f d e A B x (.andE₁ h) hU hs
  have Dp : Γ ⊢[PRAAx] le one D := .andE₁ (.andE₂ h)
  have budget := AggregateOptimization.coarse_shift_bound (C+D) D Dp
  have objective := lifted_contract g e C D (clock A B) x (.andE₂ (.andE₂ h))
  exact .andI (AggregateOptimization.named_lower _ _ _ _ e C D _ Dp budget (.andE₁ image) (.andE₂ image)
      objective (.andE₁ point) (.andE₁ (.andE₂ point)))
    (AggregateOptimization.named_upper _ _ _ _ e C D _ Dp budget (.andE₁ image) (.andE₂ image)
      objective (.andE₁ point) (.andE₁ (.andE₂ point)))

def value (S : PR 2) (f g : PR 3) (k A B C D x : PTm n) : PTm n :=
  AggregateOptimization.valueName (nameF S f) (liftObjective g) k (AggregateOptimization.coarseValueShift C D) (data (clock A B) x)
def pointObservation (U : PR 2) (f g : PR 3) (t A B C D x : PTm n) : PTm n :=
  evaluate g (evaluate f (sample U (t+AggregateOptimization.coarseValueShift C D+clock A B) x)
    (t+AggregateOptimization.coarseValueShift C D+clock A B) x) (t+AggregateOptimization.coarseValueShift C D) x

ipra_subst value [AggregateOptimization.coarseValueShift]
ipra_subst pointObservation [AggregateOptimization.coarseValueShift]

theorem value_at_source_scan (S : PR 2) (f g : PR 3) (k A B C D x : PTm n)
    (hS : Γ ⊢[PRAAx] nonempty S x) : Γ ⊢[PRAAx]
    value S f g k A B C D x ≐ pullbackValue S f g
      (pullbackIndex S f g (k+AggregateOptimization.coarseValueShift C D) (clock A B) x)
      (k+AggregateOptimization.coarseValueShift C D) (clock A B) x :=
  image_minimum_value S f g _ _ x hS

theorem point_observation_at (U : PR 2) (f g : PR 3) (t A B C D x : PTm n) : Γ ⊢[PRAAx]
    AggregateOptimization.pointValue (AggregateApproximatePointMap.pointF U f) (liftObjective g) t
      (AggregateOptimization.coarseValueShift C D) (data (clock A B) x) ≐ pointObservation U f g t A B C D x :=
  (lifted_at g _ _ _ x).eqTrans (congrAp3 g (AggregateApproximatePointMap.point_at U f _ _ x) (.eqRefl _) (.eqRefl _))

theorem value_regular (S : PR 2) (f g : PR 3) (d e A B C D x k l : PTm n)
    (h : Γ ⊢[PRAAx] input S f g d e A B C D x) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (value S f g k A B C D x) (value S f g l A B C D x)
      (unit k+unit l) (unit k*unit l) := by
  have image := AggregateApproximateImage.input_certificate S f d e A B x (.andE₁ h)
  have Dp : Γ ⊢[PRAAx] le one D := .andE₁ (.andE₂ h)
  exact AggregateOptimization.value_name_regular (nameF S f) (liftObjective g) k l _ e C D _ Dp
    (AggregateOptimization.coarse_shift_bound (C+D) D Dp) (.andE₁ image) (.andE₂ image)
    (lifted_contract g e C D _ x (.andE₂ (.andE₂ h)))

/-- Literal finite name inequality for the two actual programs at arbitrary
independent observation indices; the auxiliary optimization slack is gone. -/
theorem mapped_point_lower (U S : PR 2) (f g : PR 3) (d e A B C D x k t : PTm n)
    (h : Γ ⊢[PRAAx] input S f g d e A B C D x)
    (hU : Γ ⊢[PRAAx] pointRegular U d x) (hs : Γ ⊢[PRAAx] supportZero U S d x) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (value S f g k A B C D x) (pointObservation U f g t A B C D x)
      (unit k+unit t) (unit k*unit t) := by
  have image := AggregateApproximateImage.input_certificate S f d e A B x (.andE₁ h)
  have point := AggregateApproximatePointMap.computed_certificate U S f d e A B x (.andE₁ h) hU hs
  have Dp : Γ ⊢[PRAAx] le one D := .andE₁ (.andE₂ h)
  have result := AggregateOptimization.support_lower_exact (AggregateApproximatePointMap.pointF U f) (nameF S f)
    (liftObjective g) t k (AggregateOptimization.coarseValueShift C D) e C D _ Dp
    (AggregateOptimization.coarse_shift_bound (C+D) D Dp) (.andE₁ image) (.andE₂ image)
    (lifted_contract g e C D _ x (.andE₂ (.andE₂ h))) (.andE₁ point) (.andE₁ (.andE₂ point))
  exact RationalValueBounds.upper_congr (.eqRefl _) (point_observation_at U f g t A B C D x) (add_comm _ _) (mul_comm _ _) result

def output (U S : PR 2) (f g : PR 3) (k t A B C D x : PTm n) : PTm n :=
  pairT (value S f g k A B C D x) (pairT (pointObservation U f g t A B C D x)
    (pullbackIndex S f g (k+AggregateOptimization.coarseValueShift C D) (clock A B) x))
def outputF (U S : PR 2) (f g : PR 3) : PR 7 :=
  PTm.toPR (output U S f g (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
def run (U S : PR 2) (f g : PR 3) (k t A B C D x : PTm n) : PTm n :=
  PTm.app (outputF U S f g) ![k,t,A,B,C,D,x]
ipra_subst output [AggregateOptimization.coarseValueShift]
ipra_subst run

theorem run_at (U S : PR 2) (f g : PR 3) (k t A B C D x : PTm n) : Γ ⊢[PRAAx]
    run U S f g k t A B C D x ≐ output U S f g k t A B C D x := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output U S f g (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7) ![k,t,A,B,C,D,x]

theorem returned_value (U S : PR 2) (f g : PR 3) (k t A B C D x : PTm n) : Γ ⊢[PRAAx]
    fstT (run U S f g k t A B C D x) ≐ value S f g k A B C D x :=
  (run_at U S f g k t A B C D x).fstE
theorem returned_point_value (U S : PR 2) (f g : PR 3) (k t A B C D x : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run U S f g k t A B C D x)) ≐ pointObservation U f g t A B C D x :=
  (run_at U S f g k t A B C D x).sndE.fstE
theorem returned_index (U S : PR 2) (f g : PR 3) (k t A B C D x : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run U S f g k t A B C D x)) ≐ pullbackIndex S f g (k+AggregateOptimization.coarseValueShift C D) (clock A B) x :=
  (run_at U S f g k t A B C D x).sndE.sndE

theorem returned_lower (U S : PR 2) (f g : PR 3) (d e A B C D x k t : PTm n)
    (h : Γ ⊢[PRAAx] input S f g d e A B C D x)
    (hU : Γ ⊢[PRAAx] pointRegular U d x) (hs : Γ ⊢[PRAAx] supportZero U S d x) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (fstT (run U S f g k t A B C D x)) (fstT (sndT (run U S f g k t A B C D x)))
      (unit k+unit t) (unit k*unit t) :=
  RationalValueBounds.upper_congr (returned_value U S f g k t A B C D x).eqSymm
    (returned_point_value U S f g k t A B C D x).eqSymm (.eqRefl _) (.eqRefl _)
    (mapped_point_lower U S f g d e A B C D x k t h hU hs)

theorem actual_image_minimizer_source_index_closed (S : PR 2) (f g : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (nonempty S (var 2) ⟶ AggregateOptimization.minimumIndex (nameF S f) (liftObjective g) (var 0) (data (var 1) (var 2)) ≐
      pullbackIndex S f g (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (image_minimum_index S f g _ _ _ Prf.hyp0))

theorem actual_image_value_source_scan_closed (S : PR 2) (f g : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (nonempty S (var 5) ⟶ value S f g (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐
      pullbackValue S f g (pullbackIndex S f g (var 0+AggregateOptimization.coarseValueShift (var 3) (var 4))
        (clock (var 1) (var 2)) (var 5)) (var 0+AggregateOptimization.coarseValueShift (var 3) (var 4))
          (clock (var 1) (var 2)) (var 5)) :=
  closeUniv 6 (.impI (value_at_source_scan S f g _ _ _ _ _ _ Prf.hyp0))

theorem actual_image_optimization_closed (S : PR 2) (f g : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input S f g (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      AggregateOptimization.optimizationResult (nameF S f) (liftObjective g)
        (AggregateOptimization.coarseWitnessShift (var 4) (var 5)) (AggregateOptimization.coarseValueShift (var 4) (var 5))
          (var 1) (data (clock (var 2) (var 3)) (var 6))) :=
  closeUniv 7 (.impI (image_optimization S f g _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_mapped_point_observation_closed (U : PR 2) (f g : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (AggregateOptimization.pointValue (AggregateApproximatePointMap.pointF U f) (liftObjective g) (var 0)
      (AggregateOptimization.coarseValueShift (var 3) (var 4)) (data (clock (var 1) (var 2)) (var 5)) ≐
        pointObservation U f g (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (point_observation_at U f g _ _ _ _ _ _)

theorem actual_mapped_point_named_bounds_closed (U S : PR 2) (f g : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input S f g (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      pointRegular U (var 0) (var 6) ⟶ supportZero U S (var 0) (var 6) ⟶
        (AggregateOptimization.namedLower (AggregateApproximatePointMap.pointF U f) (nameF S f) (liftObjective g)
          (AggregateOptimization.coarseValueShift (var 4) (var 5)) (data (clock (var 2) (var 3)) (var 6)) ⋏
        AggregateOptimization.namedUpper (AggregateApproximatePointMap.pointF U f) (nameF S f) (liftObjective g)
          (AggregateOptimization.coarseValueShift (var 4) (var 5)) (data (clock (var 2) (var 3)) (var 6)))) :=
  closeUniv 7 (.impI (.impI (.impI (mapped_named_bounds U S f g _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem actual_image_value_regular_closed (S : PR 2) (f g : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (input S f g (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      RationalValueBounds.radius (value S f g (var 7) (var 2) (var 3) (var 4) (var 5) (var 6))
        (value S f g (var 8) (var 2) (var 3) (var 4) (var 5) (var 6))
          (unit (var 7)+unit (var 8)) (unit (var 7)*unit (var 8))) :=
  closeUniv 9 (.impI (value_regular S f g _ _ _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_image_optimization_program_closed (U S : PR 2) (f g : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (run U S f g (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ≐
      output U S f g (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (run_at U S f g _ _ _ _ _ _ _)

theorem actual_returned_image_lower_bound_closed (U S : PR 2) (f g : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (input S f g (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      pointRegular U (var 0) (var 6) ⟶ supportZero U S (var 0) (var 6) ⟶
        RationalValueBounds.upper (fstT (run U S f g (var 7) (var 8) (var 2) (var 3) (var 4) (var 5) (var 6)))
          (fstT (sndT (run U S f g (var 7) (var 8) (var 2) (var 3) (var 4) (var 5) (var 6))))
            (unit (var 7)+unit (var 8)) (unit (var 7)*unit (var 8))) :=
  closeUniv 9 (.impI (.impI (.impI (returned_lower U S f g _ _ _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.AggregateImageOptimization
