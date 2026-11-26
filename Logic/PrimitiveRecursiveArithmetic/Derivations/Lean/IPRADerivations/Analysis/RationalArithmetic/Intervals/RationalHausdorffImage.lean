import IPRADerivations.Analysis.RationalArithmetic.Intervals.RationalHausdorff
import IPRADerivations.Foundations.FiniteHausdorffOperations
import IPRADerivations.Foundations.BoundedSyntax

/-!
# Finite Lipschitz images on original rational coordinates

Finite-demand Section 3, `lem:aggregate-calculus`, clause 4. The fixed PR map
has an original rational point and persistent numerical data as inputs.
Input/output dimensions and the nonnegative rational multiplier A/B are
runtime parameters. The only map law concerns cross pairs of entries of the
two actual supplied lists. It compares their true rational distances using
each pair's independently computed positive normalization scale. A reverse
law follows from the proved metric symmetry.

Original finite cover witnesses transport to the actual mapped lists, with
positive source-scale cancellation. Their own independently denominated
Hausdorff codes then satisfy the exact rational image inequality. No global
Lipschitz law, supplied image cover, or common-denominator premise is used.
Coordinates use the literal total entry decoder in the first d/e positions;
no zero-padding or stored-length property of an arbitrary map is asserted.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192

namespace LeanProofs.IPRA.Analysis.RationalHausdorffImage

open_ipra
open LeanProofs.IPRA.Analysis.RationalSupMetric (metricF)
open LeanProofs.IPRA.Analysis.RationalHausdorff
open LeanProofs.IPRA.Foundations.FiniteHausdorff (distance subst_distance)
open LeanProofs.IPRA.Foundations.FiniteHausdorffOperations (mapList map_length map_lookup subst_mapList)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Actual fixed PR map applied at every actual supplied list position. -/
def image (f : PR 2) (S x : PTm n) : PTm n := mapList f S x

@[simp] theorem subst_image {l : ℕ} (σ : Fin n → PTm l) (f : PR 2) (S x : PTm n) :
    Syn.subst σ (image f S x) = image f (Syn.subst σ S) (Syn.subst σ x) := subst_mapList _ _ _ _

theorem image_length (f : PR 2) (S x : PTm n) : Γ ⊢[PRAAx] length (image f S x) ≐ length S := map_length _ _ _
theorem image_lookup (f : PR 2) (S x i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length S)) :
    Γ ⊢[PRAAx] entry (image f S x) i ≐ ap2 f (entry S i) x := map_lookup _ _ _ _ hi

theorem image_source_length (s : Side) (f : PR 2) (S T x : PTm n) :
    Γ ⊢[PRAAx] length (source s (image f S x) (image f T x)) ≐ length (source s S T) := by
  cases s <;> exact image_length f _ x

/-- Actual integer numerator of a pair distance in the pair's own true scale. -/
def pairMetric (s t : Side) (S T d i j : PTm n) : PTm n :=
  distance metricF (entry (grid s S T d) i) (entry (grid t S T d) j) (parameter S T d)

ipra_subst pairMetric

theorem pairMetric_symmetric (s t : Side) (S T d i j : PTm n) :
    Γ ⊢[PRAAx] pairMetric s t S T d i j ≐ pairMetric t s S T d j i :=
  RationalSupMetric.metric_symmetry _ _ _

/-- The source Lipschitz law at one finite pair. Ds and Dt are the actual
independent source/image scales, rather than supplied denominator data. -/
def localPair (s t : Side) (f : PR 2) (S T d e A B x i j : PTm n) : Fm PTm n :=
  le ((B*denominator S T d)*pairMetric s t (image f S x) (image f T x) e i j)
    ((A*denominator (image f S x) (image f T x) e)*pairMetric s t S T d i j)

def localLaw (s t : Side) (f : PR 2) (S T d e A B x : PTm n) : Fm PTm n :=
  .all (lt (var 0) (length (source s (Syn.shift S) (Syn.shift T))) ⟶
    .all (lt (var 0) (length (source t (Syn.shift (Syn.shift S)) (Syn.shift (Syn.shift T)))) ⟶
      localPair s t f (Syn.shift (Syn.shift S)) (Syn.shift (Syn.shift T))
        (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift e)) (Syn.shift (Syn.shift A))
        (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift x)) (var 1) (var 0)))

def finiteLaw (f : PR 2) (S T d e A B x : PTm n) : Fm PTm n := localLaw .left .right f S T d e A B x

ipra_subst localPair
ipra_subst localLaw [Fm.subst_all, Fm.subst_imp, subst_lt, subst_length, subst_source, subst_localPair,
    Syn.subst_var, Syn.up_zero, Syn.up_one, Syn.up_succ, Syn.subst_shift, Syn.shift_subst, Syn.shift_var,
    Fin.succ_zero_eq_one]
@[simp] theorem subst_finiteLaw {l : ℕ} (σ : Fin n → PTm l) (f : PR 2) (S T d e A B x : PTm n) :
    (finiteLaw f S T d e A B x).subst σ = finiteLaw f (Syn.subst σ S) (Syn.subst σ T)
      (Syn.subst σ d) (Syn.subst σ e) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ x) := subst_localLaw _ _ _ _ _ _ _ _ _ _ _

theorem localLaw_at (s t : Side) (f : PR 2) (S T d e A B x i j : PTm n)
    (h : Γ ⊢[PRAAx] localLaw s t f S T d e A B x)
    (hi : Γ ⊢[PRAAx] lt i (length (source s S T))) (hj : Γ ⊢[PRAAx] lt j (length (source t S T))) :
    Γ ⊢[PRAAx] localPair s t f S T d e A B x i j := by
  have first : Γ ⊢[PRAAx] lt i (length (source s S T)) ⟶
      .all (lt (var 0) (length (source t (Syn.shift S) (Syn.shift T))) ⟶
        localPair s t f (Syn.shift S) (Syn.shift T) (Syn.shift d) (Syn.shift e)
          (Syn.shift A) (Syn.shift B) (Syn.shift x) (Syn.shift i) (var 0)) := by
    simpa only [localLaw, Fm.subst_all, Fm.subst_imp, subst_lt, subst_length, subst_source, subst_localPair,
      Syn.subst_var, Syn.inst_zero, Syn.up_zero, Syn.up_one, Syn.up_succ, Syn.subst_inst_shift,
      LeanProofs.IPRA.AnalyticNumberTheory.Fermat.subst_up_shift'] using Prf.allE i h
  have second : Γ ⊢[PRAAx] lt j (length (source t S T)) ⟶ localPair s t f S T d e A B x i j := by
    simpa only [Fm.subst_imp, subst_lt, subst_length, subst_source, subst_localPair,
      Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using Prf.allE j (Prf.impE first hi)
  exact .impE second hj

/-- The reverse finite law is derived from symmetry, not another hypothesis. -/
theorem reverse_law (f : PR 2) (S T d e A B x : PTm n) (h : Γ ⊢[PRAAx] finiteLaw f S T d e A B x) :
    Γ ⊢[PRAAx] localLaw .right .left f S T d e A B x := by
  refine .allI (.impI (.allI (.impI ?_)))
  let Δ := lt (var 0) (length (Syn.shift (Syn.shift S))) ::
    lt (var 1) (length (Syn.shift (Syn.shift T))) :: (Γ.map Fm.shift).map Fm.shift
  have forward : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] finiteLaw f (Syn.shift (Syn.shift S)) (Syn.shift (Syn.shift T))
      (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift e)) (Syn.shift (Syn.shift A))
      (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift, subst_finiteLaw, Syn.shift] using h.shift.shift
  have raw := localLaw_at .left .right f _ _ _ _ _ _ _ (var 0) (var 1) forward.wk.wk
    (Prf.hyp0 : Δ ⊢[PRAAx] _) (Prf.hyp1 : Δ ⊢[PRAAx] _)
  have out : Δ ⊢[PRAAx] localPair .right .left f (Syn.shift (Syn.shift S)) (Syn.shift (Syn.shift T))
      (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift e)) (Syn.shift (Syn.shift A))
      (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift x)) (var 1) (var 0) :=
    le_congr (congrMul (.eqRefl _) (pairMetric_symmetric .left .right _ _ _ _ _))
      (congrMul (.eqRefl _) (pairMetric_symmetric .left .right _ _ _ _ _)) raw
  simpa only [Δ, List.map_cons, Fm.shift, subst_lt, subst_length, subst_source, source,
    Syn.shift, Syn.subst_var, Fin.succ_zero_eq_one] using out

private alias positive_cancel := Common.mul_cancel_le

/-- The pair inequality transports an arbitrary original radius at the same
actual finite pair. Only the computed positive source scale is cancelled. -/
theorem image_pair_radius (s t : Side) (f : PR 2) (S T d e A B x i j C D : PTm n)
    (hf : Γ ⊢[PRAAx] localLaw s t f S T d e A B x)
    (hi : Γ ⊢[PRAAx] lt i (length (source s S T))) (hj : Γ ⊢[PRAAx] lt j (length (source t S T)))
    (h : Γ ⊢[PRAAx] pointRadius (entry (source s S T) i) (entry (source t S T) j) d C D) :
    Γ ⊢[PRAAx] pointRadius (entry (source s (image f S x) (image f T x)) i)
      (entry (source t (image f S x) (image f T x)) j) e (A*C) (B*D) := by
  have sourceBound := point_radius_to_metric s t S T d i j C D hi hj h
  have pairBound := localLaw_at s t f S T d e A B x i j hf hi hj
  have first : Γ ⊢[PRAAx] le
      (denominator S T d*((B*D)*pairMetric s t (image f S x) (image f T x) e i j))
      ((A*denominator (image f S x) (image f T x) e)*(D*pairMetric s t S T d i j)) :=
    le_congr (by ipra_ring) (by ipra_ring) (le_mul_mono (le_refl D) pairBound)
  have second : Γ ⊢[PRAAx] le
      ((A*denominator (image f S x) (image f T x) e)*(D*pairMetric s t S T d i j))
      (denominator S T d*((A*C)*denominator (image f S x) (image f T x) e)) :=
    le_congr (.eqRefl _) (by ipra_ring)
      (le_mul_mono (le_refl (A*denominator (image f S x) (image f T x) e)) sourceBound)
  have bound := positive_cancel (RationalSupMetric.commonDenominator_one_le (pool S T) d) (le_trans first second)
  exact metric_to_point_radius s t (image f S x) (image f T x) e i j (A*C) (B*D)
    (lt_congr (.eqRefl _) (image_source_length s f S T x).eqSymm hi)
    (lt_congr (.eqRefl _) (image_source_length t f S T x).eqSymm hj) bound


/-- An actual source-cover witness is reused as an actual image-cover witness;
its existential scope is local and no infinite selector is introduced. -/
theorem image_hit (s t : Side) (f : PR 2) (S T d e A B x C D i : PTm n)
    (hf : Γ ⊢[PRAAx] localLaw s t f S T d e A B x)
    (hi : Γ ⊢[PRAAx] lt i (length (source s S T)))
    (h : Γ ⊢[PRAAx] originalHit s t S T d C D i) :
    Γ ⊢[PRAAx] originalHit s t (image f S x) (image f T x) e (A*C) (B*D) i := by
  refine .exE h ?_
  let E : Fm PTm (n+1) := lt (var 0) (length (source t (Syn.shift S) (Syn.shift T))) ⋏
    pointRadius (entry (source s (Syn.shift S) (Syn.shift T)) (Syn.shift i))
      (entry (source t (Syn.shift S) (Syn.shift T)) (var 0)) (Syn.shift d) (Syn.shift C) (Syn.shift D)
  have law : Γ.map Fm.shift ⊢[PRAAx] localLaw s t f (Syn.shift S) (Syn.shift T) (Syn.shift d)
      (Syn.shift e) (Syn.shift A) (Syn.shift B) (Syn.shift x) := by
    simpa only [Fm.shift, subst_localLaw, Syn.shift] using hf.shift
  have ibound : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift i) (length (source s (Syn.shift S) (Syn.shift T))) := by
    simpa only [Fm.shift, subst_lt, subst_length, subst_source, Syn.shift] using hi.shift
  have jb : E :: Γ.map Fm.shift ⊢[PRAAx] lt (var 0) (length (source t (Syn.shift S) (Syn.shift T))) := Prf.andE₁ Prf.hyp0
  have radius := image_pair_radius s t f (Syn.shift S) (Syn.shift T) (Syn.shift d) (Syn.shift e)
    (Syn.shift A) (Syn.shift B) (Syn.shift x) (Syn.shift i) (var 0) (Syn.shift C) (Syn.shift D)
    law.wk ibound.wk jb (Prf.andE₂ Prf.hyp0)
  have out := originalHit_intro s t (image f (Syn.shift S) (Syn.shift x)) (image f (Syn.shift T) (Syn.shift x))
    (Syn.shift e) (Syn.shift A*Syn.shift C) (Syn.shift B*Syn.shift D) (Syn.shift i) (var 0)
    (lt_congr (.eqRefl _) (image_source_length t f _ _ _).eqSymm jb) radius
  simpa only [E, Fm.shift, subst_originalHit, subst_image, PTm.subst_mul, Syn.shift] using out

/-- Original-coordinate directed cover transport at the exact scaled radius. -/
theorem image_cover (s t : Side) (f : PR 2) (S T d e A B x C D : PTm n)
    (hf : Γ ⊢[PRAAx] localLaw s t f S T d e A B x)
    (h : Γ ⊢[PRAAx] originalCover s t S T d C D) :
    Γ ⊢[PRAAx] originalCover s t (image f S x) (image f T x) e (A*C) (B*D) := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (source s (Syn.shift (image f S x)) (Syn.shift (image f T x)))) :: Γ.map Fm.shift
  have ibound : Δ ⊢[PRAAx] lt (var 0) (length (source s (Syn.shift S) (Syn.shift T))) := by
    have lengthEq : Δ ⊢[PRAAx] length (source s (Syn.shift (image f S x)) (Syn.shift (image f T x))) ≐
        length (source s (Syn.shift S) (Syn.shift T)) := by
      simpa only [Syn.shift, subst_image] using image_source_length (Γ := Δ) s f (Syn.shift S) (Syn.shift T) (Syn.shift x)
    exact lt_congr (.eqRefl _) lengthEq Prf.hyp0
  have law : Γ.map Fm.shift ⊢[PRAAx] localLaw s t f (Syn.shift S) (Syn.shift T) (Syn.shift d)
      (Syn.shift e) (Syn.shift A) (Syn.shift B) (Syn.shift x) := by
    simpa only [Fm.shift, subst_localLaw, Syn.shift] using hf.shift
  have cover : Γ.map Fm.shift ⊢[PRAAx] originalCover s t (Syn.shift S) (Syn.shift T) (Syn.shift d) (Syn.shift C) (Syn.shift D) := by
    simpa only [Fm.shift, subst_originalCover, Syn.shift] using h.shift
  have result := image_hit s t f (Syn.shift S) (Syn.shift T) (Syn.shift d) (Syn.shift e)
    (Syn.shift A) (Syn.shift B) (Syn.shift x) (Syn.shift C) (Syn.shift D) (var 0)
    law.wk ibound (originalCover_at s t _ _ _ _ _ _ cover.wk ibound)
  simpa only [Δ, Syn.shift, subst_image, PTm.subst_mul] using result

/-- Two-sided cover transport needs one original cross-pair law; the reverse
oriented law is proved from symmetry. -/
theorem image_close (f : PR 2) (S T d e A B x C D : PTm n)
    (hf : Γ ⊢[PRAAx] finiteLaw f S T d e A B x)
    (h : Γ ⊢[PRAAx] originalClose S T d C D) :
    Γ ⊢[PRAAx] originalClose (image f S x) (image f T x) e (A*C) (B*D) :=
  .andI (image_cover .left .right f S T d e A B x C D hf (Prf.andE₁ h))
    (image_cover .right .left f S T d e A B x C D (reverse_law f S T d e A B x hf) (Prf.andE₂ h))

/-- The input's actual rational Hausdorff code supplies its original cover. -/
theorem image_own_cover (f : PR 2) (S T d e A B x : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T))
    (hf : Γ ⊢[PRAAx] finiteLaw f S T d e A B x) :
    Γ ⊢[PRAAx] originalClose (image f S x) (image f T x) e
      (A*numerator S T d) (B*denominator S T d) :=
  image_close f S T d e A B x (numerator S T d) (denominator S T d) hf
    (original_close_of_bound S T d _ _ hS hT (le_congr (mul_comm _ _) (.eqRefl _) (le_refl _)))

/-- Exact rational output-H bound, retaining both independently computed
scales. For B>0 this is H(f[S],f[T])≤(A/B)H(S,T). -/
theorem rational_image (f : PR 2) (S T d e A B x : PTm n)
    (_hB : Γ ⊢[PRAAx] le one B)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T))
    (hf : Γ ⊢[PRAAx] finiteLaw f S T d e A B x) :
    Γ ⊢[PRAAx] le ((B*denominator S T d)*numerator (image f S x) (image f T x) e)
      ((A*numerator S T d)*denominator (image f S x) (image f T x) e) :=
  bound_of_original_close _ _ _ _ _ (image_own_cover f S T d e A B x hS hT hf)

/-- The actual original-coordinate Hausdorff radius checker accepts the
computed image bound. No output checker or cover premise is assumed. -/
theorem image_checker (f : PR 2) (S T d e A B x : PTm n)
    (_hB : Γ ⊢[PRAAx] le one B)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T))
    (hf : Γ ⊢[PRAAx] finiteLaw f S T d e A B x) :
    Γ ⊢[PRAAx] apply5 checkerF (image f S x) (image f T x) e
      (A*numerator S T d) (B*denominator S T d) ≐ one :=
  checker_complete _ _ _ _ _ (image_own_cover f S T d e A B x hS hT hf)

/-- The bound can be read directly through the actual rational output codes. -/
theorem image_code_bound (f : PR 2) (S T d e A B x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T))
    (hf : Γ ⊢[PRAAx] finiteLaw f S T d e A B x) :
    Γ ⊢[PRAAx] le ((B*sndT (ap3 codeF S T d))*fstT (ap3 codeF (image f S x) (image f T x) e))
      ((A*fstT (ap3 codeF S T d))*sndT (ap3 codeF (image f S x) (image f T x) e)) :=
  le_congr (congrMul (congrMul (.eqRefl _) (code_denominator S T d).eqSymm)
      (code_numerator _ _ _).eqSymm)
    (congrMul (congrMul (.eqRefl _) (code_numerator S T d).eqSymm)
      (code_denominator _ _ _).eqSymm) (rational_image f S T d e A B x hB hS hT hf)


/-! ## Fixed bounded-syntax checker for the genuine finite source law -/

open LeanProofs.IPRA.Foundations.BoundedSyntax

def pairSyntax (s t : Side) (f : PR 2) (S T d e A B x i j : PTm n) : BFm n :=
  .le ((B*denominator S T d)*pairMetric s t (image f S x) (image f T x) e i j)
    ((A*denominator (image f S x) (image f T x) e)*pairMetric s t S T d i j)

def finiteSyntax (f : PR 2) (S T d e A B x : PTm n) : BFm n :=
  .all (length S) (.all (length (Syn.shift T))
    (pairSyntax .left .right f (Syn.shift (Syn.shift S)) (Syn.shift (Syn.shift T))
      (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift e)) (Syn.shift (Syn.shift A))
      (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift x)) (var 1) (var 0)))

theorem pair_formula (s t : Side) (f : PR 2) (S T d e A B x i j : PTm n) :
    formula (pairSyntax s t f S T d e A B x i j) = localPair s t f S T d e A B x i j := rfl

theorem finite_formula (f : PR 2) (S T d e A B x : PTm n) :
    formula (finiteSyntax f S T d e A B x) = finiteLaw f S T d e A B x := by
  simp only [finiteSyntax, formula, finiteLaw, localLaw, pair_formula, source, Syn.shift, subst_length]

def apply7 (v : PR 7) (S T d e A B x : PTm n) : PTm n := PTm.app v ![S,T,d,e,A,B,x]
def finiteCheckerF (f : PR 2) : PR 7 := bitF (finiteSyntax f (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
def checkFinite (f : PR 2) (S T d e A B x : PTm n) : PTm n := apply7 (finiteCheckerF f) S T d e A B x

@[simp] theorem subst_apply7 {l : ℕ} (σ : Fin n → PTm l) (v : PR 7) (S T d e A B x : PTm n) :
    Syn.subst σ (apply7 v S T d e A B x) = apply7 v (Syn.subst σ S) (Syn.subst σ T) (Syn.subst σ d)
      (Syn.subst σ e) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ x) := by
  show PTm.app _ _ = PTm.app _ _
  congr 1
  funext i
  fin_cases i <;> rfl
@[simp] theorem subst_checkFinite {l : ℕ} (σ : Fin n → PTm l) (f : PR 2) (S T d e A B x : PTm n) :
    Syn.subst σ (checkFinite f S T d e A B x) = checkFinite f (Syn.subst σ S) (Syn.subst σ T) (Syn.subst σ d)
      (Syn.subst σ e) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ x) := subst_apply7 _ _ _ _ _ _ _ _ _

theorem finite_checker_program (f : PR 2) (S T d e A B x : PTm n) :
    Γ ⊢[PRAAx] checkFinite f S T d e A B x ≐
      bit (finiteSyntax f (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) ![S,T,d,e,A,B,x] :=
  program_correct _ _

theorem finite_checker_reflection (f : PR 2) (S T d e A B x : PTm n) :
    Γ ⊢[PRAAx] Fm.iff (checkFinite f S T d e A B x ≐ one) (finiteLaw f S T d e A B x) := by
  have e5 : (5 : Fin 7) = (4 : Fin 6).succ := rfl
  have e6 : (6 : Fin 7) = (5 : Fin 6).succ := rfl
  have e5' : (5 : Fin 6) = (4 : Fin 5).succ := rfl
  have raw := bounded_reflection (Γ := Γ)
    (finiteSyntax f (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) ![S,T,d,e,A,B,x]
  rw [finite_formula] at raw
  have reflected : Γ ⊢[PRAAx] Fm.iff
      (bit (finiteSyntax f (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) ![S,T,d,e,A,B,x] ≐ one)
      (finiteLaw f S T d e A B x) := by
    simpa only [subst_finiteLaw, Syn.subst_var, e5, e6, e5', Matrix.cons_val_succ, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons] using raw
  have p := finite_checker_program (Γ := Γ) f S T d e A B x
  exact .iffI (.impI (reflected.wk.iffMp (p.wk.eqSymm.eqTrans Prf.hyp0)))
    (.impI (p.wk.eqTrans (reflected.wk.iffMpr Prf.hyp0)))

theorem finite_checker_boolean (f : PR 2) (S T d e A B x : PTm n) :
    Γ ⊢[PRAAx] (checkFinite f S T d e A B x ≐ zero) ⋎ (checkFinite f S T d e A B x ≐ one) := by
  have p := finite_checker_program (Γ := Γ) f S T d e A B x
  exact .orE (bit_cases (finiteSyntax f (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) ![S,T,d,e,A,B,x])
    (.orI₁ (p.wk.eqTrans Prf.hyp0)) (.orI₂ (p.wk.eqTrans Prf.hyp0))

/-! ## Actual output programs and all-parameter endpoints -/

def imageF (f : PR 2) : PR 2 := PTm.toPR (image f (var 0) (var 1))
def boundCheckerTerm (f : PR 2) (S T d e A B x : PTm n) : PTm n :=
  apply5 checkerF (image f S x) (image f T x) e (A*numerator S T d) (B*denominator S T d)
def boundCheckerF (f : PR 2) : PR 7 := PTm.toPR
  (boundCheckerTerm f (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
def checkBound (f : PR 2) (S T d e A B x : PTm n) : PTm n := apply7 (boundCheckerF f) S T d e A B x

ipra_subst boundCheckerTerm

theorem image_at (f : PR 2) (S x : PTm n) : Γ ⊢[PRAAx] ap2 (imageF f) S x ≐ image f S x := by
  have h := toPR_eq (Γ := Γ) (image f (var 0) (var 1) : PTm 2) ![S,x]
  simpa only [imageF, ap2, subst_image, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one] using h

theorem bound_checker_at (f : PR 2) (S T d e A B x : PTm n) :
    Γ ⊢[PRAAx] checkBound f S T d e A B x ≐ boundCheckerTerm f S T d e A B x := by
  have e5 : (5 : Fin 7) = (4 : Fin 6).succ := rfl
  have e6 : (6 : Fin 7) = (5 : Fin 6).succ := rfl
  have e5' : (5 : Fin 6) = (4 : Fin 5).succ := rfl
  have h := toPR_eq (Γ := Γ)
    (boundCheckerTerm f (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7) ![S,T,d,e,A,B,x]
  simpa only [checkBound, apply7, boundCheckerF, subst_boundCheckerTerm, Syn.subst_var,
    e5, e6, e5', Matrix.cons_val_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] using h

/-- Acceptance of the actual finite source-pair checker proves both acceptance
of the actual output radius checker and the exact rational H inequality. -/
theorem checked_image (f : PR 2) (S T d e A B x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T))
    (hcheck : Γ ⊢[PRAAx] checkFinite f S T d e A B x ≐ one) :
    Γ ⊢[PRAAx] (checkBound f S T d e A B x ≐ one) ⋏
      le ((B*sndT (ap3 codeF S T d))*fstT (ap3 codeF (image f S x) (image f T x) e))
        ((A*fstT (ap3 codeF S T d))*sndT (ap3 codeF (image f S x) (image f T x) e)) := by
  have law := (finite_checker_reflection f S T d e A B x).iffMp hcheck
  exact .andI ((bound_checker_at f S T d e A B x).eqTrans (image_checker f S T d e A B x hB hS hT law))
    (image_code_bound f S T d e A B x hB hS hT law)

theorem original_image_cover_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      (finiteLaw f (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
        originalClose (var 0) (var 1) (var 2) (var 7) (var 8) ⟶
          originalClose (image f (var 0) (var 6)) (image f (var 1) (var 6)) (var 3)
            (var 4*var 7) (var 5*var 8)) :=
  closeUniv 9 (.impI (.impI (image_close f (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)
    (var 7) (var 8) Prf.hyp1 Prf.hyp0)))

theorem rational_image_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (le one (var 5) ⟶ le one (length (var 0)) ⟶ le one (length (var 1)) ⟶
        finiteLaw f (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
          le ((var 5*denominator (var 0) (var 1) (var 2))*
            numerator (image f (var 0) (var 6)) (image f (var 1) (var 6)) (var 3))
            ((var 4*numerator (var 0) (var 1) (var 2))*
              denominator (image f (var 0) (var 6)) (image f (var 1) (var 6)) (var 3))) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (rational_image f (var 0) (var 1) (var 2) (var 3)
    (var 4) (var 5) (var 6) Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

theorem checked_image_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (le one (var 5) ⟶ le one (length (var 0)) ⟶ le one (length (var 1)) ⟶
        checkFinite f (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ≐ one ⟶
          ((checkBound f (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ≐ one) ⋏
            le ((var 5*sndT (ap3 codeF (var 0) (var 1) (var 2)))*
              fstT (ap3 codeF (image f (var 0) (var 6)) (image f (var 1) (var 6)) (var 3)))
              ((var 4*fstT (ap3 codeF (var 0) (var 1) (var 2)))*
                sndT (ap3 codeF (image f (var 0) (var 6)) (image f (var 1) (var 6)) (var 3))))) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (checked_image f (var 0) (var 1) (var 2) (var 3)
    (var 4) (var 5) (var 6) Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

theorem finite_checker_reflection_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (Fm.iff (checkFinite f (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ≐ one)
        (finiteLaw f (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))) :=
  closeUniv 7 (finite_checker_reflection f _ _ _ _ _ _ _)

theorem image_program_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((ap2 (imageF f) (var 0) (var 1) ≐ image f (var 0) (var 1)) ⋏
        (lt (var 2) (length (var 0)) ⟶ entry (image f (var 0) (var 1)) (var 2) ≐ ap2 f (entry (var 0) (var 2)) (var 1))) :=
  closeUniv 3 (.andI (image_at f _ _) (.impI (image_lookup f _ _ _ Prf.hyp0)))

theorem bound_checker_program_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (checkBound f (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ≐
        boundCheckerTerm f (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (bound_checker_at f _ _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.RationalHausdorffImage
