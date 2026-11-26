import IPRADerivations.Foundations.SquareRootNames
import IPRADerivations.Foundations.BoundedEnumeration
import IPRADerivations.Foundations.FilteredEnumerationCode
import IPRADerivations.Foundations.CodedViableChain
import IPRADerivations.Analysis.Polynomials.RootFinding.Descent.GaussianDescentClockArithmetic
import IPRADerivations.Analysis.RationalArithmetic.Representations.RationalRepresentations
import IPRADerivations.Analysis.Geometry.Distances.GaussianEuclideanDistanceName
import IPRADerivations.Probability.Variance
import IPRADerivations.Core.CongruenceTactic
import IPRADerivations.Core.SubstCommand
import IPRADerivations.Core.Header

/-!
# Actual finite rational square-root candidates

Source: `ipra_evidence_framework/report.tex`, worked example at lines 68--73.
The source mesh and cutoff are retained: K=2^n and
M=ceil((u+v)K/v)+1. The chosen numerator is the predecessor of the actual
least crossing of `SquareRootNames`. No correctness of that candidate is
assumed. Local residuals are the exact cleared inequalities
|v*j^2-u*K^2| <= (2u+3v)K. The original rational input has v>=1.

Proof-step correction to source line 71: at perfect squares, the predecessor
of the least ceiling crossing gives a NONSTRICT upper bracket. The valid
bracket v*c^2<=u*K^2<=v*(c+1)^2 suffices for the unchanged local residual.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.SquareRootRelationalCandidates

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Analysis.RationalIntegerNormalization (positive_form)
open LeanProofs.IPRA.Analysis.GaussianDescentClockArithmetic (ceiling ceiling_lower)
open LeanProofs.IPRA.Foundations.MasterCertificate (sequence entry stack)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def unit (k : PTm n) : PTm n := pw two k
def three : PTm n := two+one
def cutoff (u v k : PTm n) : PTm n := succ (ceiling ((u+v)*unit k) v)
def candidate (u v k : PTm n) : PTm n := pred (SquareRootNames.jn u v k)
def target (u k : PTm n) : PTm n := u*(unit k*unit k)
def budget (u v k : PTm n) : PTm n := (two*u+three*v)*unit k
def localCondition (u v k j : PTm n) : Fm PTm n :=
  le (v*j*j) (target u k+budget u v k) ⋏ le (target u k) (v*j*j+budget u v k)
def defect (u v k j : PTm n) : PTm n :=
  monus (v*j*j) (target u k+budget u v k)+monus (target u k) (v*j*j+budget u v k)
def compatible (j l : PTm n) : Fm PTm n :=
  le (two*j) (l+(three+three)) ⋏ le l (two*j+(three+three))
def point (j k : PTm n) : PTm n := Analysis.RationalIntegerNormalization.normalize (ZT.ofNat j) (unit k)
def inputValue (u v : PTm n) : PTm n := Analysis.RationalIntegerNormalization.normalize (ZT.ofNat u) v
def errorValue (u v k : PTm n) : PTm n :=
  Analysis.RationalIntegerNormalization.normalize (ZT.ofNat (two*u+three*v)) (v*unit k)
def rationalResidual (u v k j : PTm n) : Fm PTm n :=
  Analysis.RationalArgmin.rationalLE (Analysis.RationalArithmetic.multiply (point j k) (point j k))
    (Analysis.RationalArithmetic.add (inputValue u v) (errorValue u v k)) ⋏
  Analysis.RationalArgmin.rationalLE (inputValue u v)
    (Analysis.RationalArithmetic.add (Analysis.RationalArithmetic.multiply (point j k) (point j k)) (errorValue u v k))

ipra_subst unit
@[simp] theorem subst_three {m : ℕ} (σ : Fin n → PTm m) :
    Syn.subst σ (three : PTm n) = (three : PTm m) := by simp [three]
ipra_subst cutoff
ipra_subst candidate [SquareRootNames.jn]
ipra_subst target
ipra_subst budget
ipra_subst localCondition
ipra_subst defect
ipra_subst compatible
ipra_subst point
ipra_subst inputValue
ipra_subst errorValue
ipra_subst rationalResidual

theorem unit_positive (k : PTm n) : Γ ⊢[PRAAx] le one (unit k) :=
  le_trans (zero_lt_succ k) (Analysis.RationalClosure.succ_le_two_pow k)
theorem unit_succ (k : PTm n) : Γ ⊢[PRAAx] unit (succ k) ≐ two*unit k :=
  (pw_succ two k).eqTrans (mul_comm _ _)

theorem predecessor_le (j : PTm n) : Γ ⊢[PRAAx] le (pred j) j := by
  refine .orE (zero_or_succ j) ?_ ?_
  · exact le_congr ((congrPred Prf.hyp0).eqTrans pred_zero).eqSymm Prf.hyp0.eqSymm (le_refl zero)
  · exact le_congr (.eqRefl _) Prf.hyp0.eqSymm (le_succ_self _)
theorem le_predecessor_succ (j : PTm n) : Γ ⊢[PRAAx] le j (succ (pred j)) := by
  refine .orE (zero_or_succ j) ?_ ?_
  · exact le_congr Prf.hyp0.eqSymm (.eqRefl _) (zero_le _)
  · exact le_congr Prf.hyp0.eqSymm (.eqRefl _) (le_refl _)

theorem candidate_lower (u v k : PTm n) (_hv : Γ ⊢[PRAAx] le one v) : Γ ⊢[PRAAx]
    le (v*candidate u v k*candidate u v k) (target u k) := by
  refine .orE (zero_or_succ (SquareRootNames.jn u v k)) ?_ ?_
  · have e : ((SquareRootNames.jn u v k ≐ zero) :: Γ) ⊢[PRAAx] candidate u v k ≐ zero :=
      (congrPred Prf.hyp0).eqTrans pred_zero
    have eq : ((SquareRootNames.jn u v k ≐ zero) :: Γ) ⊢[PRAAx]
        v*candidate u v k*candidate u v k ≐ zero :=
      (congrMul (congrMul (.eqRefl v) e) e).eqTrans (by ipra_ring)
    exact le_congr eq.eqSymm (.eqRefl _) (zero_le _)
  · have ht : ((SquareRootNames.jn u v k ≐ succ (pred (SquareRootNames.jn u v k))) :: Γ) ⊢[PRAAx]
        lt (candidate u v k) (SquareRootNames.jn u v k) :=
      le_congr (.eqRefl _) Prf.hyp0.eqSymm (le_refl _)
    exact le_congr (by ipra_ring) (.eqRefl _) (le_of_lt (SquareRootNames.sqrt_below ht))

theorem candidate_upper (u v k : PTm n) (hv : Γ ⊢[PRAAx] le one v) : Γ ⊢[PRAAx]
    le (target u k) (v*succ (candidate u v k)*succ (candidate u v k)) := by
  have cross : Γ ⊢[PRAAx] le (target u k) (v*SquareRootNames.jn u v k*SquareRootNames.jn u v k) :=
    le_congr (.eqRefl _) (by ipra_ring) (SquareRootNames.sqrt_cross (u := u) (positive_form hv) k)
  have order : Γ ⊢[PRAAx] le (SquareRootNames.jn u v k) (succ (candidate u v k)) := le_predecessor_succ _
  have bigger : Γ ⊢[PRAAx] le (v*SquareRootNames.jn u v k*SquareRootNames.jn u v k)
      (v*succ (candidate u v k)*succ (candidate u v k)) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right v (le_mul_mono order order))
  exact le_trans cross bigger

/-- sqrt(a)<=a+1 is proved only by a native square comparison. -/
theorem candidate_linear_bound (u v k : PTm n) (hv : Γ ⊢[PRAAx] le one v) : Γ ⊢[PRAAx]
    le (v*candidate u v k) ((u+v)*unit k) := by
  apply nat_sqrt_mono
  have lower := candidate_lower (Γ := Γ) u v k hv
  have scaled := mul_le_mul_right v lower
  have larger : Γ ⊢[PRAAx] le (u*v*(unit k*unit k)) (((u+v)*unit k)*((u+v)*unit k)) :=
    le_of_eq_add (d := (u*u+u*v+v*v)*(unit k*unit k)) (by ipra_ring)
  exact le_trans (le_congr (by ipra_ring) (by unfold target; ipra_ring) scaled) larger

theorem candidate_in_grid (u v k : PTm n) (hv : Γ ⊢[PRAAx] le one v) : Γ ⊢[PRAAx]
    le (candidate u v k) (cutoff u v k) := by
  have cleared := le_trans (candidate_linear_bound u v k hv) (ceiling_lower ((u+v)*unit k) v hv)
  have small : Γ ⊢[PRAAx] le (candidate u v k) (ceiling ((u+v)*unit k) v) :=
    mul_le_cancel (le_congr (congrMul (positive_form hv) (.eqRefl _))
      (congrMul (positive_form hv) (.eqRefl _)) cleared)
  exact le_trans small (le_succ_self _)

theorem candidate_residual (u v k : PTm n) (hv : Γ ⊢[PRAAx] le one v) : Γ ⊢[PRAAx]
    localCondition u v k (candidate u v k) := by
  refine .andI (le_trans (candidate_lower u v k hv) (le_add_right _ _)) ?_
  have cross := candidate_upper (Γ := Γ) u v k hv
  have linear := candidate_linear_bound (Γ := Γ) u v k hv
  have vk : Γ ⊢[PRAAx] le v (v*unit k) :=
    le_congr (one_mul v) (mul_comm (unit k) v) (mul_le_mul_right v (unit_positive k))
  unfold budget three
  ipra_le sl cross + 2*sl linear + sl vk

theorem defect_of_local (u v k j : PTm n) (h : Γ ⊢[PRAAx] localCondition u v k j) : Γ ⊢[PRAAx]
    defect u v k j ≐ zero :=
  (congrAdd (Prf.andE₁ h) (Prf.andE₂ h)).eqTrans (add_zero zero)
theorem local_of_defect (u v k j : PTm n) (h : Γ ⊢[PRAAx] defect u v k j ≐ zero) : Γ ⊢[PRAAx]
    localCondition u v k j := .andI (add_eq_zero_left h) (add_eq_zero_left ((add_comm _ _).eqTrans h))

theorem candidate_compatible (u v k : PTm n) (hv : Γ ⊢[PRAAx] le one v) : Γ ⊢[PRAAx]
    compatible (candidate u v k) (candidate u v (succ k)) := by
  have upper := SquareRootNames.sqrt_upper (Γ := Γ) (u := u) (positive_form hv) k
  have lower := SquareRootNames.sqrt_lower (Γ := Γ) (u := u) (positive_form hv) k
  have p0 := predecessor_le (Γ := Γ) (SquareRootNames.jn u v k)
  have p1 := predecessor_le (Γ := Γ) (SquareRootNames.jn u v (succ k))
  have s0 := le_predecessor_succ (Γ := Γ) (SquareRootNames.jn u v k)
  have s1 := le_predecessor_succ (Γ := Γ) (SquareRootNames.jn u v (succ k))
  refine .andI ?_ ?_
  · unfold candidate three
    ipra_le sl lower+2*sl p0+sl s1+4
  · unfold candidate three
    ipra_le sl upper+sl p1+2*sl s0+4

theorem positive_product (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] le one (A*B) := le_congr (one_mul one) (.eqRefl _) (le_mul_mono hA hB)
theorem point_represents (j k : PTm n) : Γ ⊢[PRAAx]
    Analysis.RationalArithmetic.represents (point j k) (ZT.ofNat j) (unit k) :=
  Analysis.RationalIntegerNormalization.normalize_preserves_value _ _ (unit_positive k)
theorem input_represents (u v : PTm n) (hv : Γ ⊢[PRAAx] le one v) : Γ ⊢[PRAAx]
    Analysis.RationalArithmetic.represents (inputValue u v) (ZT.ofNat u) v :=
  Analysis.RationalIntegerNormalization.normalize_preserves_value _ _ hv
theorem error_represents (u v k : PTm n) (hv : Γ ⊢[PRAAx] le one v) : Γ ⊢[PRAAx]
    Analysis.RationalArithmetic.represents (errorValue u v k) (ZT.ofNat (two*u+three*v)) (v*unit k) :=
  Analysis.RationalIntegerNormalization.normalize_preserves_value _ _ (positive_product _ _ hv (unit_positive k))

/-- This is the actual normalized scalar rational residual, using only
the original u/v and the dyadic mesh code, with all denominators proved. -/
theorem rational_residual (u v k j : PTm n) (hv : Γ ⊢[PRAAx] le one v)
    (h : Γ ⊢[PRAAx] localCondition u v k j) : Γ ⊢[PRAAx] rationalResidual u v k j := by
  have hK := unit_positive (Γ := Γ) k
  have hVK := positive_product _ _ hv hK
  have hKK := positive_product _ _ hK hK
  have square := Analysis.RationalRepresentations.represents_multiply _ _ _ _ _ _
    (point_represents (Γ := Γ) j k) (point_represents j k)
  have input := input_represents (Γ := Γ) u v hv
  have error := error_represents (Γ := Γ) u v k hv
  have sum1 := Analysis.RationalRepresentations.represents_add _ _ _ _ _ _ input error
  have sum2 := Analysis.RationalRepresentations.represents_add _ _ _ _ _ _ square error
  refine .andI ?_ ?_
  · apply Analysis.RationalArithmetic.order_of_representations _ _ _ _ _ _ square sum1 hKK
      (positive_product _ _ hv hVK)
    apply zle_of_toZ ((v*unit k)*monus (target u k+budget u v k) (v*j*j))
    have e := natEq (eq_add_of_le (Prf.andE₁ h))
    simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat]
    unfold target budget at *
    ipra_simps
    linear_combination -(𝔞 v*𝔞 (unit k))*e
  · apply Analysis.RationalArithmetic.order_of_representations _ _ _ _ _ _ input sum2 hv
      (positive_product _ _ hKK hVK)
    apply zle_of_toZ ((v*unit k)*monus (v*j*j+budget u v k) (target u k))
    have e := natEq (eq_add_of_le (Prf.andE₂ h))
    simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat]
    unfold target budget at *
    ipra_simps
    linear_combination -(𝔞 v*𝔞 (unit k))*e

theorem actual_candidate_rational_residual (u v k : PTm n) (hv : Γ ⊢[PRAAx] le one v) : Γ ⊢[PRAAx]
    rationalResidual u v k (candidate u v k) := rational_residual u v k _ hv (candidate_residual u v k hv)

/-- The stored list records grid numerators. Its rational decoder is `point`;
thus its size bound depends on the finite grid, not on an output-code oracle. -/
def data (u v k : PTm n) : PTm n := pairT u (pairT v k)
def defectBody : PTm 2 := defect (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def retainedBody : PTm 2 := BoundedEnumeration.vb defectBody
def count (u v k : PTm n) : PTm n := FilteredEnumerationCode.count retainedBody (succ (cutoff u v k)) (data u v k)
def candidateList (u v k : PTm n) : PTm n :=
  FilteredEnumerationCode.list retainedBody (succ (cutoff u v k)) (data u v k)
def listBound (u v k : PTm n) : PTm n :=
  FilteredEnumerationCode.codeBound retainedBody (succ (cutoff u v k)) (data u v k)
def position (u v k j : PTm n) : PTm n := FilteredEnumeration.rank retainedBody j (data u v k)
def observed (u v k r : PTm n) : PTm n := point (entry (candidateList u v k) r) k

ipra_subst data
ipra_subst count
ipra_subst candidateList
ipra_subst listBound
ipra_subst position [FilteredEnumeration.rank]
ipra_subst observed

theorem point_congr {j j' k k' : PTm n} (hj : Γ ⊢[PRAAx] j ≐ j') (hk : Γ ⊢[PRAAx] k ≐ k') : Γ ⊢[PRAAx]
    point j k ≐ point j' k' := by
  ipra_congr (point (var 0) (var 1) : PTm 2) with [hj, hk]

theorem defect_body_at (u v k j : PTm n) : Γ ⊢[PRAAx]
    inst2 defectBody j (data u v k) ≐ defect u v k j := by
  have eu : Γ ⊢[PRAAx] fstT (data u v k) ≐ u := fst_pair u (pairT v k)
  have ev : Γ ⊢[PRAAx] fstT (sndT (data u v k)) ≐ v :=
    (congrFst (snd_pair u (pairT v k))).eqTrans (fst_pair v k)
  have ek : Γ ⊢[PRAAx] sndT (sndT (data u v k)) ≐ k :=
    (congrSnd (snd_pair u (pairT v k))).eqTrans (snd_pair v k)
  simpa only [defectBody,inst2,subst_defect,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
    (Prf.eqCongr (defect (var 0) (var 1) (var 2) (var 3) : PTm 4)
      (σ := ![fstT (data u v k),fstT (sndT (data u v k)),sndT (sndT (data u v k)),j])
      (σ' := ![u,v,k,j]) (fun i => by fin_cases i; exact eu; exact ev; exact ek; exact .eqRefl j))

theorem list_length (u v k : PTm n) : Γ ⊢[PRAAx] length (candidateList u v k) ≐ count u v k :=
  FilteredEnumerationCode.list_length _ _ _
theorem count_bound (u v k : PTm n) : Γ ⊢[PRAAx] le (count u v k) (succ (cutoff u v k)) :=
  FilteredEnumerationCode.count_le _ _ _
theorem list_size_bound (u v k : PTm n) : Γ ⊢[PRAAx] lt (candidateList u v k) (listBound u v k) :=
  FilteredEnumerationCode.size_bound _ _ _
theorem entry_in_grid (u v k r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count u v k)) : Γ ⊢[PRAAx]
    le (entry (candidateList u v k) r) (cutoff u v k) :=
  (succ_monus_succ _ _).eqSymm.eqTrans (FilteredEnumerationCode.entry_bound retainedBody _ _ r hr)
theorem entry_residual (u v k r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count u v k)) : Γ ⊢[PRAAx]
    localCondition u v k (entry (candidateList u v k) r) := by
  have valid := BoundedEnumeration.valid_of_kept (FilteredEnumerationCode.entry_valid retainedBody _ _ r hr)
  exact local_of_defect _ _ _ _ ((defect_body_at _ _ _ _).eqSymm.eqTrans valid)
theorem entry_rational_residual (u v k r : PTm n) (hv : Γ ⊢[PRAAx] le one v)
    (hr : Γ ⊢[PRAAx] lt r (count u v k)) : Γ ⊢[PRAAx]
    rationalResidual u v k (entry (candidateList u v k) r) :=
  rational_residual _ _ _ _ hv (entry_residual _ _ _ _ hr)
theorem list_increasing (u v k r s : PTm n) (hrs : Γ ⊢[PRAAx] lt r s)
    (hs : Γ ⊢[PRAAx] lt s (count u v k)) : Γ ⊢[PRAAx]
    lt (entry (candidateList u v k) r) (entry (candidateList u v k) s) :=
  FilteredEnumerationCode.increasing _ _ _ _ _ hrs hs

/-- Completeness uses the original grid/residual tests, not a supplied property
of the returned list. -/
theorem grid_candidate_listed (u v k j : PTm n) (hGrid : Γ ⊢[PRAAx] le j (cutoff u v k))
    (hLocal : Γ ⊢[PRAAx] localCondition u v k j) : Γ ⊢[PRAAx]
    lt (position u v k j) (count u v k) ⋏ entry (candidateList u v k) (position u v k j) ≐ j := by
  apply FilteredEnumerationCode.listed retainedBody _ _ j
    ((succ_monus_succ _ _).eqTrans hGrid)
  exact BoundedEnumeration.kept_of_valid ((defect_body_at _ _ _ _).eqTrans (defect_of_local _ _ _ _ hLocal))
theorem actual_candidate_listed (u v k : PTm n) (hv : Γ ⊢[PRAAx] le one v) : Γ ⊢[PRAAx]
    lt (position u v k (candidate u v k)) (count u v k) ⋏
      entry (candidateList u v k) (position u v k (candidate u v k)) ≐ candidate u v k :=
  grid_candidate_listed _ _ _ _ (candidate_in_grid _ _ _ hv) (candidate_residual _ _ _ hv)
theorem list_nonempty (u v k : PTm n) (hv : Γ ⊢[PRAAx] le one v) : Γ ⊢[PRAAx] le one (count u v k) :=
  le_trans (zero_lt_succ _) (Prf.andE₁ (actual_candidate_listed _ _ _ hv))
theorem actual_observation (u v k : PTm n) (hv : Γ ⊢[PRAAx] le one v) : Γ ⊢[PRAAx]
    observed u v k (position u v k (candidate u v k)) ≐ point (candidate u v k) k :=
  point_congr (Prf.andE₂ (actual_candidate_listed _ _ _ hv)) (.eqRefl k)

/-- Exact source compatibility between adjacent mesh fractions. -/
theorem rational_compatible (j l k : PTm n) (h : Γ ⊢[PRAAx] compatible j l) : Γ ⊢[PRAAx]
    Analysis.RationalValueBounds.radius (point j k) (point l (succ k)) three (unit k) := by
  have K := unit_positive (Γ := Γ) k
  have K1 := unit_positive (Γ := Γ) (succ k)
  have actual := unit_succ (Γ := Γ) k
  apply Analysis.RationalValueBounds.radius_of_upper
  · apply Analysis.GaussianEuclideanDistanceName.upper_of_representations _ _ j (unit k) l (unit (succ k))
      three (unit k) K K1 (point_represents _ _) (point_represents _ _)
    have cross : Γ ⊢[PRAAx] le (unit k*(two*unit k)*j)
        (unit k*l*unit k+three*unit k*(two*unit k)) :=
      le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (unit k*unit k) (Prf.andE₁ h))
    exact le_congr (congrMul (congrMul (.eqRefl _) actual.eqSymm) (.eqRefl _))
      (congrAdd (.eqRefl _) (congrMul (.eqRefl _) actual.eqSymm)) cross
  · apply Analysis.GaussianEuclideanDistanceName.upper_of_representations _ _ l (unit (succ k)) j (unit k)
      three (unit k) K1 K (point_represents _ _) (point_represents _ _)
    have cross : Γ ⊢[PRAAx] le (unit k*unit k*l)
        (unit k*j*(two*unit k)+three*(two*unit k)*unit k) :=
      le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (unit k*unit k) (Prf.andE₂ h))
    exact le_congr (.eqRefl _)
      (congrAdd (congrMul (.eqRefl _) actual.eqSymm) (congrMul (congrMul (.eqRefl _) actual.eqSymm) (.eqRefl _))) cross

theorem actual_candidate_transition (u v k : PTm n) (hv : Γ ⊢[PRAAx] le one v) : Γ ⊢[PRAAx]
    Analysis.RationalValueBounds.radius (point (candidate u v k) k)
      (point (candidate u v (succ k)) (succ k)) three (unit k) :=
  rational_compatible _ _ _ (candidate_compatible _ _ _ hv)

def outputF : PR 3 := PTm.toPR (candidateList (var 0) (var 1) (var 2))
def run (u v k : PTm n) : PTm n := ap3 outputF u v k
def candidateF : PR 3 := PTm.toPR (candidate (var 0) (var 1) (var 2))
def countF : PR 3 := PTm.toPR (count (var 0) (var 1) (var 2))
def boundF : PR 3 := PTm.toPR (listBound (var 0) (var 1) (var 2))
def observationF : PR 4 := PTm.toPR (observed (var 0) (var 1) (var 2) (var 3))
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (u v k : PTm n) :
    Syn.subst σ (run u v k) = run (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ k) := by
  simp only [run,ap3,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
theorem output_at (u v k : PTm n) : Γ ⊢[PRAAx] run u v k ≐ candidateList u v k := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (candidateList (var 0) (var 1) (var 2) : PTm 3) ![u,v,k]
theorem candidate_at (u v k : PTm n) : Γ ⊢[PRAAx] ap3 candidateF u v k ≐ candidate u v k := by
  simpa [candidateF,ap3] using toPR_eq (Γ := Γ) (candidate (var 0) (var 1) (var 2) : PTm 3) ![u,v,k]
theorem count_at (u v k : PTm n) : Γ ⊢[PRAAx] ap3 countF u v k ≐ count u v k := by
  simpa [countF,ap3] using toPR_eq (Γ := Γ) (count (var 0) (var 1) (var 2) : PTm 3) ![u,v,k]
theorem bound_at (u v k : PTm n) : Γ ⊢[PRAAx] ap3 boundF u v k ≐ listBound u v k := by
  simpa [boundF,ap3] using toPR_eq (Γ := Γ) (listBound (var 0) (var 1) (var 2) : PTm 3) ![u,v,k]
theorem observation_at (u v k r : PTm n) : Γ ⊢[PRAAx] app observationF ![u,v,k,r] ≐ observed u v k r := by
  simpa [observationF] using toPR_eq (Γ := Γ) (observed (var 0) (var 1) (var 2) (var 3) : PTm 4) ![u,v,k,r]

theorem returned_length (u v k : PTm n) : Γ ⊢[PRAAx] length (run u v k) ≐ count u v k :=
  (congrFst (output_at _ _ _)).eqTrans (list_length _ _ _)
theorem returned_size (u v k : PTm n) : Γ ⊢[PRAAx] lt (run u v k) (listBound u v k) :=
  lt_congr (output_at _ _ _).eqSymm (.eqRefl _) (list_size_bound _ _ _)
theorem returned_grid (u v k r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count u v k)) : Γ ⊢[PRAAx]
    le (entry (run u v k) r) (cutoff u v k) :=
  le_congr (entry_congr (output_at _ _ _ ) (.eqRefl _)).eqSymm (.eqRefl _) (entry_in_grid _ _ _ _ hr)
theorem returned_rational_residual (u v k r : PTm n) (hv : Γ ⊢[PRAAx] le one v)
    (hr : Γ ⊢[PRAAx] lt r (count u v k)) : Γ ⊢[PRAAx] rationalResidual u v k (entry (run u v k) r) := by
  have original := BoundedEnumeration.valid_of_kept
    (FilteredEnumerationCode.entry_valid retainedBody (succ (cutoff u v k)) (data u v k) r hr)
  have decoded : Γ ⊢[PRAAx] inst2 defectBody (entry (run u v k) r) (data u v k) ≐
      inst2 defectBody (entry (candidateList u v k) r) (data u v k) :=
    congrInst2 defectBody (entry_congr (output_at u v k) (.eqRefl r)) (.eqRefl (data u v k))
  have actual : Γ ⊢[PRAAx] defect u v k (entry (run u v k) r) ≐ zero :=
    (defect_body_at _ _ _ _).eqSymm.eqTrans (decoded.eqTrans original)
  exact rational_residual _ _ _ _ hv (local_of_defect _ _ _ _ actual)

theorem source_brackets_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶
      (le ((var 1)*candidate (var 0) (var 1) (var 2)*candidate (var 0) (var 1) (var 2)) (target (var 0) (var 2)) ⋏
        le (target (var 0) (var 2)) ((var 1)*succ (candidate (var 0) (var 1) (var 2))*succ (candidate (var 0) (var 1) (var 2))))) :=
  closeUniv 3 (.impI (.andI (candidate_lower _ _ _ Prf.hyp0) (candidate_upper _ _ _ Prf.hyp0)))
theorem source_nonempty_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ (le one (count (var 0) (var 1) (var 2)) ⋏
      lt (position (var 0) (var 1) (var 2) (candidate (var 0) (var 1) (var 2))) (count (var 0) (var 1) (var 2)) ⋏
      entry (run (var 0) (var 1) (var 2)) (position (var 0) (var 1) (var 2) (candidate (var 0) (var 1) (var 2))) ≐
        candidate (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.andI (list_nonempty _ _ _ Prf.hyp0)
    (.andI (Prf.andE₁ (actual_candidate_listed _ _ _ Prf.hyp0))
      ((entry_congr (output_at _ _ _) (.eqRefl _)).eqTrans (Prf.andE₂ (actual_candidate_listed _ _ _ Prf.hyp0))))))
theorem source_list_sound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ lt (var 3) (count (var 0) (var 1) (var 2)) ⟶
      (le (entry (run (var 0) (var 1) (var 2)) (var 3)) (cutoff (var 0) (var 1) (var 2)) ⋏
        rationalResidual (var 0) (var 1) (var 2) (entry (run (var 0) (var 1) (var 2)) (var 3)))) :=
  closeUniv 4 (.impI (.impI (.andI (returned_grid _ _ _ _ Prf.hyp0)
    (returned_rational_residual _ _ _ _ Prf.hyp1 Prf.hyp0))))
theorem source_list_complete_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 3) (cutoff (var 0) (var 1) (var 2)) ⟶ localCondition (var 0) (var 1) (var 2) (var 3) ⟶
      (lt (position (var 0) (var 1) (var 2) (var 3)) (count (var 0) (var 1) (var 2)) ⋏
        entry (run (var 0) (var 1) (var 2)) (position (var 0) (var 1) (var 2) (var 3)) ≐ var 3)) :=
  closeUniv 4 (.impI (.impI (.andI (Prf.andE₁ (grid_candidate_listed _ _ _ _ Prf.hyp1 Prf.hyp0))
    ((entry_congr (output_at _ _ _) (.eqRefl _)).eqTrans
      (Prf.andE₂ (grid_candidate_listed _ _ _ _ Prf.hyp1 Prf.hyp0))))))
theorem source_compatibility_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ Analysis.RationalValueBounds.radius
      (point (candidate (var 0) (var 1) (var 2)) (var 2))
      (point (candidate (var 0) (var 1) (succ (var 2))) (succ (var 2))) three (unit (var 2))) :=
  closeUniv 3 (.impI (actual_candidate_transition _ _ _ Prf.hyp0))
theorem actual_list_size_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (run (var 0) (var 1) (var 2)) ≐ count (var 0) (var 1) (var 2) ⋏
      (le (count (var 0) (var 1) (var 2)) (succ (cutoff (var 0) (var 1) (var 2))) ⋏
        lt (run (var 0) (var 1) (var 2)) (listBound (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.andI (returned_length _ _ _) (.andI (count_bound _ _ _) (returned_size _ _ _)))
theorem actual_candidate_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 candidateF (var 0) (var 1) (var 2) ≐ candidate (var 0) (var 1) (var 2) ⋏
      ap3 countF (var 0) (var 1) (var 2) ≐ count (var 0) (var 1) (var 2) ⋏
      ap3 boundF (var 0) (var 1) (var 2) ≐ listBound (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.andI (candidate_at _ _ _) (.andI (count_at _ _ _) (bound_at _ _ _)))
theorem actual_observation_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (app observationF ![var 0,var 1,var 2,var 3] ≐ observed (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (observation_at _ _ _ _)

end LeanProofs.IPRA.Foundations.SquareRootRelationalCandidates
