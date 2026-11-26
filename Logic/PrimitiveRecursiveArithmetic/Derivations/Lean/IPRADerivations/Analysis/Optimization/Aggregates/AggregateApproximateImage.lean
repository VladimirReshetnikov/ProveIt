import IPRADerivations.Analysis.Optimization.Aggregates.AggregateOptimization
import IPRADerivations.Analysis.Polynomials.RootFinding.Adequacy.GaussianRootSchedule

/-!
# Actual finite images under an approximate rational map

Finite-demand Section 3, equation (L), followed by the displayed image-name
constructor. The fixed PR map returns rational vectors. Its only mathematical
input is the original approximate Lipschitz contract at numerical point,
precision and radius arguments. Actual mapped lists retain source positions;
all output covers and name regularity are derived. Arithmetic uses the total
first-e coordinate decoder, without an assertion of stored output lengths.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.AggregateApproximateImage

open_ipra
open AggregateEquality (sample unit unit_positive nonempty nonempty_at regular regular_at equivalent equivalent_at)
open AggregateOptimization (evaluate errorNumerator errorDenominator argument)
open RationalHausdorff (pointRadius originalHit originalCover originalClose source originalCover_at originalHit_intro)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def mapInstance (f : PR 3) (d e A B x q r p t C D : PTm n) : Fm PTm n :=
  pointRadius q r d C D ⟶ pointRadius (evaluate f q p x) (evaluate f r t x) e
    (errorNumerator A B C D p t) (errorDenominator B D p t)
ipra_subst mapInstance

def mapContract (f : PR 3) (d e A B x : PTm n) : Fm PTm n :=
  .all (mapInstance f (Syn.shift d) (Syn.shift e) (Syn.shift A) (Syn.shift B) (Syn.shift x)
    (argument 0 (var 0)) (argument 1 (var 0)) (argument 2 (var 0))
    (argument 3 (var 0)) (argument 4 (var 0)) (argument 5 (var 0)))
ipra_subst mapContract [Fm.subst_all, subst_mapInstance, Syn.subst_shift, Syn.shift_subst,
    AggregateOptimization.subst_argument, Syn.subst_var, Syn.up_zero, Syn.up_succ]

theorem map_at (f : PR 3) (d e A B x q r p t C D : PTm n)
    (h : Γ ⊢[PRAAx] mapContract f d e A B x) (hqr : Γ ⊢[PRAAx] pointRadius q r d C D) :
    Γ ⊢[PRAAx] pointRadius (evaluate f q p x) (evaluate f r t x) e
      (errorNumerator A B C D p t) (errorDenominator B D p t) := by
  let z := Foundations.BoundedSyntax.pack ![q,r,p,t,C,D]
  have raw : Γ ⊢[PRAAx] mapInstance f d e A B x (argument 0 z) (argument 1 z)
      (argument 2 z) (argument 3 z) (argument 4 z) (argument 5 z) := by
    simpa only [mapContract,subst_mapInstance,Syn.subst_inst_shift,AggregateOptimization.subst_argument,
      Syn.subst_var,Syn.inst_zero] using h.allE z
  have eqs (i : Fin 6) : Γ ⊢[PRAAx] argument i z ≐ (![q,r,p,t,C,D] : Fin 6 → PTm n) i :=
    Foundations.BoundedSyntax.projections_pack _ i
  have current := Prf.eqSubst (mapInstance f (var 6) (var 7) (var 8) (var 9) (var 10)
      (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : Fm PTm 11)
    ![argument 0 z,argument 1 z,argument 2 z,argument 3 z,argument 4 z,argument 5 z,d,e,A,B,x]
    ![q,r,p,t,C,D,d,e,A,B,x] (fun i => by
      fin_cases i
      · exact eqs 0
      · exact eqs 1
      · exact eqs 2
      · exact eqs 3
      · exact eqs 4
      · exact eqs 5
      all_goals exact .eqRefl _) (by simpa [subst_mapInstance] using raw)
  have rule : Γ ⊢[PRAAx] mapInstance f d e A B x q r p t C D := by simpa [subst_mapInstance] using current
  exact .impE rule hqr

def imageBody (f : PR 3) : PTm 2 := evaluate f (entry (fstT (var 1)) (var 0))
  (fstT (sndT (var 1))) (sndT (sndT (var 1)))
def image (f : PR 3) (T p x : PTm n) : PTm n := sequence (imageBody f) (length T) (pairT T (pairT p x))
ipra_subst image

theorem image_length (f : PR 3) (T p x : PTm n) : Γ ⊢[PRAAx] length (image f T p x) ≐ length T := sequence_length _ _ _
theorem image_body_at (f : PR 3) (T p x i : PTm n) : Γ ⊢[PRAAx]
    inst2 (imageBody f) i (pairT T (pairT p x)) ≐ evaluate f (entry T i) p x := by
  simp only [imageBody,inst2,AggregateOptimization.subst_evaluate,Foundations.MasterCertificate.subst_entry,
    subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact congrAp3 f (entry_congr (fst_pair _ _) (.eqRefl _))
    (snd_pair _ _).fstE (snd_pair _ _).sndE
theorem image_lookup (f : PR 3) (T p x i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length T)) : Γ ⊢[PRAAx]
    entry (image f T p x) i ≐ evaluate f (entry T i) p x :=
  (sequence_decode (imageBody f) hi).eqTrans (image_body_at f T p x i)

/-- The actual source hit supplies the same bounded target position in the image. -/
theorem image_hit (f : PR 3) (S T d e A B x p t C D i : PTm n)
    (hmap : Γ ⊢[PRAAx] mapContract f d e A B x) (hi : Γ ⊢[PRAAx] lt i (length S))
    (h : Γ ⊢[PRAAx] originalHit .left .right S T d C D i) : Γ ⊢[PRAAx]
    originalHit .left .right (image f S p x) (image f T t x) e
      (errorNumerator A B C D p t) (errorDenominator B D p t) i := by
  refine .exE h ?_
  let E : Fm PTm (n+1) := lt (var 0) (length (Syn.shift T)) ⋏
    pointRadius (entry (Syn.shift S) (Syn.shift i)) (entry (Syn.shift T) (var 0)) (Syn.shift d) (Syn.shift C) (Syn.shift D)
  let Δ := E :: Γ.map Fm.shift
  have law : Δ ⊢[PRAAx] mapContract f (Syn.shift d) (Syn.shift e) (Syn.shift A) (Syn.shift B) (Syn.shift x) := by
    simpa [Δ,Fm.shift,Syn.shift] using hmap.shift.wk
  have ib : Δ ⊢[PRAAx] lt (Syn.shift i) (length (Syn.shift S)) := by simpa [Δ,Fm.shift,Syn.shift] using hi.shift.wk
  have found : Δ ⊢[PRAAx] E := Prf.hyp0
  have jb : Δ ⊢[PRAAx] lt (var 0) (length (Syn.shift T)) := .andE₁ found
  have radius := map_at f (Syn.shift d) (Syn.shift e) (Syn.shift A) (Syn.shift B) (Syn.shift x)
    (entry (Syn.shift S) (Syn.shift i)) (entry (Syn.shift T) (var 0)) (Syn.shift p) (Syn.shift t)
    (Syn.shift C) (Syn.shift D) law (.andE₂ found)
  have actual : Δ ⊢[PRAAx] pointRadius
      (entry (image f (Syn.shift S) (Syn.shift p) (Syn.shift x)) (Syn.shift i))
      (entry (image f (Syn.shift T) (Syn.shift t) (Syn.shift x)) (var 0)) (Syn.shift e)
      (errorNumerator (Syn.shift A) (Syn.shift B) (Syn.shift C) (Syn.shift D) (Syn.shift p) (Syn.shift t))
      (errorDenominator (Syn.shift B) (Syn.shift D) (Syn.shift p) (Syn.shift t)) :=
    AggregateChain.point_congr (image_lookup f _ _ _ _ ib).eqSymm (image_lookup f _ _ _ _ jb).eqSymm
      (.eqRefl _) (.eqRefl _) (.eqRefl _) radius
  have result := originalHit_intro .left .right (image f (Syn.shift S) (Syn.shift p) (Syn.shift x))
    (image f (Syn.shift T) (Syn.shift t) (Syn.shift x)) (Syn.shift e) _ _ (Syn.shift i) (var 0)
    (lt_congr (.eqRefl _) (image_length f _ _ _).eqSymm jb) actual
  simpa [Δ,E,Fm.shift,Syn.shift,source] using result

theorem image_cover (f : PR 3) (S T d e A B x p t C D : PTm n)
    (hmap : Γ ⊢[PRAAx] mapContract f d e A B x) (h : Γ ⊢[PRAAx] originalCover .left .right S T d C D) : Γ ⊢[PRAAx]
    originalCover .left .right (image f S p x) (image f T t x) e
      (errorNumerator A B C D p t) (errorDenominator B D p t) := by
  refine .allI (.impI ?_)
  let E := lt (var 0) (length (image f (Syn.shift S) (Syn.shift p) (Syn.shift x)))
  let Δ := E :: Γ.map Fm.shift
  have index : Δ ⊢[PRAAx] lt (var 0) (length (Syn.shift S)) :=
    lt_congr (.eqRefl _) (image_length f _ _ _) Prf.hyp0
  have law : Δ ⊢[PRAAx] mapContract f (Syn.shift d) (Syn.shift e) (Syn.shift A) (Syn.shift B) (Syn.shift x) := by
    simpa [Δ,E,Fm.shift,Syn.shift,source] using hmap.shift.wk
  have cover : Δ ⊢[PRAAx] originalCover .left .right (Syn.shift S) (Syn.shift T) (Syn.shift d) (Syn.shift C) (Syn.shift D) := by
    simpa [Δ,E,Fm.shift,Syn.shift,source] using h.shift.wk
  have hit : Δ ⊢[PRAAx] originalHit .left .right (Syn.shift S) (Syn.shift T) (Syn.shift d) (Syn.shift C) (Syn.shift D) (var 0) :=
    originalCover_at .left .right _ _ _ _ _ _ cover index
  simpa [Δ,E,Syn.shift,source] using image_hit f (Syn.shift S) (Syn.shift T) (Syn.shift d) (Syn.shift e)
    (Syn.shift A) (Syn.shift B) (Syn.shift x) (Syn.shift p) (Syn.shift t) (Syn.shift C) (Syn.shift D) (var 0) law index hit

theorem reverse_cover_formula (S T d A B : PTm n) :
    originalCover .right .left S T d A B = originalCover .left .right T S d A B := rfl

theorem image_close (f : PR 3) (S T d e A B x p t C D : PTm n)
    (hmap : Γ ⊢[PRAAx] mapContract f d e A B x) (h : Γ ⊢[PRAAx] originalClose S T d C D) : Γ ⊢[PRAAx]
    originalClose (image f S p x) (image f T t x) e
      (errorNumerator A B C D p t) (errorDenominator B D p t) := by
  have forward : Γ ⊢[PRAAx] originalCover .left .right S T d C D := .andE₁ h
  have backward : Γ ⊢[PRAAx] originalCover .left .right T S d C D := .andE₂ h
  have first := image_cover f S T d e A B x p t C D hmap forward
  have second := image_cover f T S d e A B x t p C D hmap backward
  have changed : Γ ⊢[PRAAx] originalCover .left .right (image f T t x) (image f S p x) e
      (errorNumerator A B C D p t) (errorDenominator B D p t) :=
    RationalHausdorffTriangle.originalCover_radius_congr _ _ _
      (by unfold errorNumerator; ipra_ring) (by unfold errorDenominator; ipra_ring) second
  exact .andI first (Eq.mpr (congrArg (fun F => Γ ⊢[PRAAx] F)
    (reverse_cover_formula (image f S p x) (image f T t x) e _ _)) changed)

def imageF (f : PR 3) : PR 3 := PTm.toPR (image f (var 0) (var 1) (var 2))
theorem image_at (f : PR 3) (T p x : PTm n) : Γ ⊢[PRAAx] ap3 (imageF f) T p x ≐ image f T p x := by
  simpa only [imageF,ap3,subst_image,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons] using toPR_eq (Γ := Γ) (image f (var 0) (var 1) (var 2) : PTm 3) ![T,p,x]
theorem image_congr (f : PR 3) {T T' p p' x x' : PTm n} (hT : Γ ⊢[PRAAx] T ≐ T')
    (hp : Γ ⊢[PRAAx] p ≐ p') (hx : Γ ⊢[PRAAx] x ≐ x') : Γ ⊢[PRAAx] image f T p x ≐ image f T' p' x' :=
  (image_at f _ _ _).eqSymm.eqTrans ((congrAp3 (imageF f) hT hp hx).eqTrans (image_at f _ _ _))

def data (c x : PTm n) : PTm n := pairT c x
def name (S : PR 2) (f : PR 3) (k c x : PTm n) : PTm n := image f (sample S (k+c) x) (k+c) x
def nameBody (S : PR 2) (f : PR 3) : PTm 2 := name S f (var 0) (fstT (var 1)) (sndT (var 1))
def nameF (S : PR 2) (f : PR 3) : PR 2 := PTm.toPR (nameBody S f)
ipra_subst data
ipra_subst name

theorem name_at (S : PR 2) (f : PR 3) (k c x : PTm n) : Γ ⊢[PRAAx]
    sample (nameF S f) k (data c x) ≐ name S f k c x := by
  have reified : Γ ⊢[PRAAx] sample (nameF S f) k (data c x) ≐
      name S f k (fstT (data c x)) (sndT (data c x)) := by
    let body := nameBody S f
    change Γ ⊢[PRAAx] PTm.app (PTm.toPR body) ![k,data c x] ≐ name S f k (fstT (data c x)) (sndT (data c x))
    simpa [body,nameBody] using toPR_eq (Γ := Γ) body ![k,data c x]
  exact reified.eqTrans (image_congr f (congrAp2 S (congrAdd (.eqRefl _) (fst_pair _ _)) (snd_pair _ _))
    (congrAdd (.eqRefl _) (fst_pair _ _)) (snd_pair _ _))

theorem name_length (S : PR 2) (f : PR 3) (k c x : PTm n) : Γ ⊢[PRAAx]
    length (name S f k c x) ≐ length (sample S (k+c) x) := image_length _ _ _ _
theorem name_lookup (S : PR 2) (f : PR 3) (k c x i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length (sample S (k+c) x))) :
    Γ ⊢[PRAAx] entry (name S f k c x) i ≐ evaluate f (entry (sample S (k+c) x) i) (k+c) x := image_lookup _ _ _ _ _ hi

alias positive_product := Common.one_le_mul
theorem denominator_positive (B D p t : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] le one (errorDenominator B D p t) :=
  positive_product _ _ (positive_product _ _ (positive_product _ _ hB hD) (unit_positive p)) (unit_positive t)

theorem close_mono (S T e A B C D : PTm n) (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T))
    (hB : Γ ⊢[PRAAx] le one B) (hBudget : Γ ⊢[PRAAx] le (A*D) (C*B))
    (h : Γ ⊢[PRAAx] originalClose S T e A B) : Γ ⊢[PRAAx] originalClose S T e C D :=
  RationalHausdorff.original_close_of_bound S T e C D hS hT
    (AggregateChain.fraction_mono hB (RationalHausdorff.bound_of_original_close S T e A B h) hBudget)

theorem close_lists {S S' T T' : PTm n} (e A B : PTm n) (hS : Γ ⊢[PRAAx] S ≐ S')
    (hT : Γ ⊢[PRAAx] T ≐ T') (h : Γ ⊢[PRAAx] originalClose S T e A B) : Γ ⊢[PRAAx] originalClose S' T' e A B := by
  have old : Γ ⊢[PRAAx] (originalClose (var 0) (var 1) (var 2) (var 3) (var 4) : Fm PTm 5).subst ![S,T,e,A,B] := by simpa using h
  have result := Prf.eqSubst (originalClose (var 0) (var 1) (var 2) (var 3) (var 4) : Fm PTm 5)
    ![S,T,e,A,B] ![S',T',e,A,B] (fun i => by fin_cases i; exact hS; exact hT; exact .eqRefl _; exact .eqRefl _; exact .eqRefl _) old
  simpa using result

theorem regular_budget (A B c s t : PTm n) (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c)) : Γ ⊢[PRAAx] le
    (errorNumerator A B (unit (s+c)+unit (t+c)) (unit (s+c)*unit (t+c)) (s+c) (t+c)*(unit s*unit t))
    ((unit s+unit t)*errorDenominator B (unit (s+c)*unit (t+c)) (s+c) (t+c)) := by
  let F := unit c*unit c*unit c*(unit s+unit t)*(unit s*unit t)*(unit s*unit t)
  have es := natEq (AggregateChain.unit_add (Γ := Γ) s c)
  have et := natEq (AggregateChain.unit_add (Γ := Γ) t c)
  refine le_congr ?_ ?_ (mul_le_mul_right F hc)
  all_goals
    apply deriveNat
    simp only [F,errorNumerator,errorDenominator]
    ipra_simps
    rw [es,et]
    ring

theorem equivalent_budget (A B c k : PTm n) (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c)) : Γ ⊢[PRAAx] le
    (errorNumerator A B two (unit (k+c)) (k+c) (k+c)*unit k)
    (two*errorDenominator B (unit (k+c)) (k+c) (k+c)) := by
  have e := natEq (AggregateChain.unit_add (Γ := Γ) k c)
  refine le_congr ?_ ?_ (mul_le_mul_right (two*unit (k+c)*unit (k+c)*unit k) hc)
  all_goals
    apply deriveNat
    simp only [errorNumerator,errorDenominator]
    ipra_simps
    rw [e]
    ring

theorem name_nonempty (S : PR 2) (f : PR 3) (c x : PTm n) (hS : Γ ⊢[PRAAx] nonempty S x) :
    Γ ⊢[PRAAx] nonempty (nameF S f) (data c x) := by
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  have ne : Δ ⊢[PRAAx] nonempty S (Syn.shift x) := by simpa [Δ,Fm.shift,Syn.shift] using hS.shift
  have len : Δ ⊢[PRAAx] length (sample (nameF S f) (var 0) (data (Syn.shift c) (Syn.shift x))) ≐
      length (sample S (var 0+Syn.shift c) (Syn.shift x)) :=
    (congrFst (name_at S f (var 0) (Syn.shift c) (Syn.shift x))).eqTrans (name_length S f _ _ _)
  simpa [Δ,Syn.shift,one] using le_congr (.eqRefl _) len.eqSymm (nonempty_at S _ _ ne)

theorem name_regular_pair (S : PR 2) (f : PR 3) (d e A B c x s t : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c))
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hmap : Γ ⊢[PRAAx] mapContract f d e A B x) : Γ ⊢[PRAAx]
    originalClose (name S f s c x) (name S f t c x) e (unit s+unit t) (unit s*unit t) := by
  have original := image_close f (sample S (s+c) x) (sample S (t+c) x) d e A B x (s+c) (t+c)
    (unit (s+c)+unit (t+c)) (unit (s+c)*unit (t+c)) hmap (regular_at S (s+c) (t+c) d x hR)
  have posS : Γ ⊢[PRAAx] le one (length (name S f s c x)) :=
    le_congr (.eqRefl _) (name_length S f s c x).eqSymm (nonempty_at S (s+c) x hS)
  have posT : Γ ⊢[PRAAx] le one (length (name S f t c x)) :=
    le_congr (.eqRefl _) (name_length S f t c x).eqSymm (nonempty_at S (t+c) x hS)
  exact close_mono _ _ _ _ _ _ _ posS posT
    (denominator_positive B (unit (s+c)*unit (t+c)) (s+c) (t+c) hB (positive_product _ _ (unit_positive _) (unit_positive _)))
    (regular_budget A B c s t hc) original

theorem name_regular (S : PR 2) (f : PR 3) (d e A B c x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c))
    (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hmap : Γ ⊢[PRAAx] mapContract f d e A B x) : Γ ⊢[PRAAx] regular (nameF S f) e (data c x) := by
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
  have ne : Δ ⊢[PRAAx] nonempty S y := by simpa [Δ,y,Fm.shift,Syn.shift] using hS.shift.shift
  have reg : Δ ⊢[PRAAx] regular S D y := by simpa [Δ,D,y,Fm.shift,Syn.shift] using hR.shift.shift
  have law : Δ ⊢[PRAAx] mapContract f D E a b y := by simpa [Δ,D,E,a,b,y,Fm.shift,Syn.shift] using hmap.shift.shift
  simpa [Δ,D,E,a,b,c',y,Syn.shift] using close_lists E _ _ (name_at S f (var 1) c' y).eqSymm
    (name_at S f (var 0) c' y).eqSymm (name_regular_pair S f D E a b c' y (var 1) (var 0) b' clock ne reg law)

theorem name_equivalent_pair (S T : PR 2) (f : PR 3) (d e A B c x k : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c))
    (hS : Γ ⊢[PRAAx] nonempty S x) (hT : Γ ⊢[PRAAx] nonempty T x)
    (heq : Γ ⊢[PRAAx] equivalent S T d x) (hmap : Γ ⊢[PRAAx] mapContract f d e A B x) : Γ ⊢[PRAAx]
    originalClose (name S f k c x) (name T f k c x) e two (unit k) := by
  have original := image_close f (sample S (k+c) x) (sample T (k+c) x) d e A B x (k+c) (k+c)
    two (unit (k+c)) hmap (equivalent_at S T (k+c) d x heq)
  have posS : Γ ⊢[PRAAx] le one (length (name S f k c x)) :=
    le_congr (.eqRefl _) (name_length S f k c x).eqSymm (nonempty_at S (k+c) x hS)
  have posT : Γ ⊢[PRAAx] le one (length (name T f k c x)) :=
    le_congr (.eqRefl _) (name_length T f k c x).eqSymm (nonempty_at T (k+c) x hT)
  exact close_mono _ _ _ _ _ _ _ posS posT (denominator_positive B (unit (k+c)) (k+c) (k+c) hB (unit_positive _))
    (equivalent_budget A B c k hc) original

theorem name_equivalent (S T : PR 2) (f : PR 3) (d e A B c x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hc : Γ ⊢[PRAAx] le (A+B) (B*unit c))
    (hS : Γ ⊢[PRAAx] nonempty S x) (hT : Γ ⊢[PRAAx] nonempty T x)
    (heq : Γ ⊢[PRAAx] equivalent S T d x) (hmap : Γ ⊢[PRAAx] mapContract f d e A B x) :
    Γ ⊢[PRAAx] equivalent (nameF S f) (nameF T f) e (data c x) := by
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
  have neS : Δ ⊢[PRAAx] nonempty S y := by simpa [Δ,y,Fm.shift,Syn.shift] using hS.shift
  have neT : Δ ⊢[PRAAx] nonempty T y := by simpa [Δ,y,Fm.shift,Syn.shift] using hT.shift
  have eqv : Δ ⊢[PRAAx] equivalent S T D y := by simpa [Δ,D,y,Fm.shift,Syn.shift] using heq.shift
  have law : Δ ⊢[PRAAx] mapContract f D E a b y := by simpa [Δ,D,E,a,b,y,Fm.shift,Syn.shift] using hmap.shift
  simpa [Δ,D,E,a,b,c',y,Syn.shift,two,one] using close_lists E _ _ (name_at S f (var 0) c' y).eqSymm
    (name_at T f (var 0) c' y).eqSymm (name_equivalent_pair S T f D E a b c' y (var 0) b' clock neS neT eqv law)

def clock (A B : PTm n) : PTm n := GaussianRootSchedule.binaryLength (A+B)
ipra_subst clock

theorem clock_budget (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] le (A+B) (B*unit (clock A B)) := by
  have power : Γ ⊢[PRAAx] le (A+B) (unit (clock A B)) := by
    simpa [unit,clock] using (Prf.andE₁ (GaussianRootSchedule.binary_length_correct (Γ := Γ) (A+B)))
  exact le_trans power (le_congr (one_mul _) (.eqRefl _) (le_mul_mono hB (le_refl _)))

theorem computed_name (S : PR 2) (f : PR 3) (d e A B x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hS : Γ ⊢[PRAAx] nonempty S x) (hR : Γ ⊢[PRAAx] regular S d x)
    (hmap : Γ ⊢[PRAAx] mapContract f d e A B x) : Γ ⊢[PRAAx]
    nonempty (nameF S f) (data (clock A B) x) ⋏ regular (nameF S f) e (data (clock A B) x) :=
  .andI (name_nonempty S f _ x hS) (name_regular S f d e A B _ x hB (clock_budget A B hB) hS hR hmap)

def input (S : PR 2) (f : PR 3) (d e A B x : PTm n) : Fm PTm n :=
  le one B ⋏ (nonempty S x ⋏ (regular S d x ⋏ mapContract f d e A B x))
ipra_subst input

theorem input_certificate (S : PR 2) (f : PR 3) (d e A B x : PTm n) (h : Γ ⊢[PRAAx] input S f d e A B x) : Γ ⊢[PRAAx]
    nonempty (nameF S f) (data (clock A B) x) ⋏ regular (nameF S f) e (data (clock A B) x) :=
  computed_name S f d e A B x (.andE₁ h) (.andE₁ (.andE₂ h)) (.andE₁ (.andE₂ (.andE₂ h))) (.andE₂ (.andE₂ (.andE₂ h)))

theorem computed_equivalent (S T : PR 2) (f : PR 3) (d e A B x : PTm n)
    (hS : Γ ⊢[PRAAx] input S f d e A B x) (hT : Γ ⊢[PRAAx] input T f d e A B x)
    (heq : Γ ⊢[PRAAx] equivalent S T d x) : Γ ⊢[PRAAx]
    equivalent (nameF S f) (nameF T f) e (data (clock A B) x) :=
  name_equivalent S T f d e A B (clock A B) x (.andE₁ hS) (clock_budget A B (.andE₁ hS))
    (.andE₁ (.andE₂ hS)) (.andE₁ (.andE₂ hT)) heq (.andE₂ (.andE₂ (.andE₂ hS)))

def computed (S : PR 2) (f : PR 3) (k A B x : PTm n) : PTm n := name S f k (clock A B) x
def computedF (S : PR 2) (f : PR 3) : PR 4 := PTm.toPR (computed S f (var 0) (var 1) (var 2) (var 3))
ipra_subst computed

theorem computed_at (S : PR 2) (f : PR 3) (k A B x : PTm n) : Γ ⊢[PRAAx]
    PTm.app (computedF S f) ![k,A,B,x] ≐ computed S f k A B x := by
  simpa only [computedF,subst_computed,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
    toPR_eq (Γ := Γ) (computed S f (var 0) (var 1) (var 2) (var 3) : PTm 4) ![k,A,B,x]

theorem computed_lookup (S : PR 2) (f : PR 3) (k A B x i : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (length (sample S (k+clock A B) x))) : Γ ⊢[PRAAx]
    entry (PTm.app (computedF S f) ![k,A,B,x]) i ≐ evaluate f (entry (sample S (k+clock A B) x) i) (k+clock A B) x :=
  (entry_congr (computed_at S f k A B x) (.eqRefl _)).eqTrans (name_lookup S f k (clock A B) x i hi)

theorem actual_approximate_image_finite_close_closed (f : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    (mapContract f (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      originalClose (var 0) (var 1) (var 2) (var 9) (var 10) ⟶
        originalClose (image f (var 0) (var 7) (var 6)) (image f (var 1) (var 8) (var 6)) (var 3)
          (errorNumerator (var 4) (var 5) (var 9) (var 10) (var 7) (var 8))
          (errorDenominator (var 5) (var 10) (var 7) (var 8))) :=
  closeUniv 11 (.impI (.impI (image_close f _ _ _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_approximate_image_name_closed (S : PR 2) (f : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input S f (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      (nonempty (nameF S f) (data (clock (var 2) (var 3)) (var 4)) ⋏
        regular (nameF S f) (var 1) (data (clock (var 2) (var 3)) (var 4)))) :=
  closeUniv 5 (.impI (input_certificate S f _ _ _ _ _ Prf.hyp0))

theorem actual_approximate_image_extensional_closed (S T : PR 2) (f : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input S f (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ input T f (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      equivalent S T (var 0) (var 4) ⟶
        equivalent (nameF S f) (nameF T f) (var 1) (data (clock (var 2) (var 3)) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (computed_equivalent S T f _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem actual_approximate_image_length_closed (f : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (image f (var 0) (var 1) (var 2)) ≐ length (var 0)) := closeUniv 3 (image_length f _ _ _)

theorem actual_approximate_image_lookup_closed (f : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (length (var 0)) ⟶ entry (image f (var 0) (var 1) (var 2)) (var 3) ≐
      evaluate f (entry (var 0) (var 3)) (var 1) (var 2)) := closeUniv 4 (.impI (image_lookup f _ _ _ _ Prf.hyp0))

theorem actual_approximate_image_clock_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ le (var 0+var 1) (var 1*unit (clock (var 0) (var 1)))) :=
  closeUniv 2 (.impI (clock_budget _ _ Prf.hyp0))

theorem actual_approximate_image_program_closed (S : PR 2) (f : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (PTm.app (computedF S f) ![var 0,var 1,var 2,var 3] ≐
      image f (sample S (var 0+clock (var 1) (var 2)) (var 3)) (var 0+clock (var 1) (var 2)) (var 3)) :=
  closeUniv 4 (computed_at S f _ _ _ _)

theorem actual_returned_approximate_image_entry_closed (S : PR 2) (f : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (var 4) (length (sample S (var 0+clock (var 1) (var 2)) (var 3))) ⟶
      entry (PTm.app (computedF S f) ![var 0,var 1,var 2,var 3]) (var 4) ≐
        evaluate f (entry (sample S (var 0+clock (var 1) (var 2)) (var 3)) (var 4))
          (var 0+clock (var 1) (var 2)) (var 3)) :=
  closeUniv 5 (.impI (computed_lookup S f _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.AggregateApproximateImage
