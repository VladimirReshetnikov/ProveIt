import IPRADerivations.Analysis.Polynomials.RootFinding.DominantTerms.GaussianOffDominantWeights
import IPRADerivations.Analysis.Polynomials.Horner.GaussianHornerCommonDenominator
import IPRADerivations.Analysis.RationalArithmetic.Norms.GaussianRationalNormClearing
import IPRADerivations.Analysis.RationalArithmetic.Covers.GaussianRationalCover

/-!
# The exact geometric bound for two actual Gaussian-rational sums

Individual lower and upper geometric comparisons are transported through
one computed positive denominator. The actual integer folds satisfy the
Euclidean relative triangle estimate, and actual Horner evaluation at one
identifies the rational sums. The resulting scalar bound is exactly
9*normSq(otherSum) <= 4*normSq(reference).

The pointwise comparisons are local helper inputs. The source producer
derives them from its computed dominant plateau and displacement bound.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGeometricSumBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalCover (Side original numerators)
open LeanProofs.IPRA.Analysis.GaussianRationalNormalization (commonD queryNumerator)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (represents evaluate qadd)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (qone)
open LeanProofs.IPRA.Analysis.GaussianRelativeNormTriangle (gaussianSum termBounds)
open LeanProofs.IPRA.Analysis.GaussianRationalNormClearing (weightedNorm three nine)
open LeanProofs.IPRA.Analysis.GaussianDominantSyntax (four)
open LeanProofs.IPRA.Analysis.GaussianBalancedRadiusSyntax (unit)
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (normSq scale add)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def count : Side → PTm n → PTm n → PTm n
  | .source, _, k => GaussianOffDominantWeights.lowerCount k
  | .target, N, k => GaussianOffDominantWeights.upperCount N k
def distance : Side → PTm n → PTm n → PTm n
  | .source, k, i => GaussianOffDominantWeights.lowerDistance k i
  | .target, _, i => GaussianOffDominantWeights.upperDistance i
def weight : Side → PTm n → PTm n → PTm n → PTm n
  | .source, N, k, i => GaussianOffDominantWeights.lowerWeight N k i
  | .target, N, _, i => GaussianOffDominantWeights.upperWeight N i
def g : Side → PR 2
  | .source => GaussianOffDominantWeights.gLower
  | .target => GaussianOffDominantWeights.gUpper
def payloadField (s : Side) (x : PTm n) : PTm n :=
  original s (fstT (sndT (sndT x))) (sndT (sndT (sndT x)))
def scaledBody (s : Side) : PTm 2 := scale (GaussianOffDominantWeights.C (fstT (var 1)))
  (entry (payloadField s (var 1)) (var 0))
def f (s : Side) : PR 2 := PTm.toPR (scaledBody s)
def payload (S T ref : PTm n) : PTm n := pairT (numerators .source S T ref) (numerators .target S T ref)
def data (N k S T ref : PTm n) : PTm n := GaussianOffDominantWeights.data N k (payload S T ref)
def sumNumerator (s : Side) (N k S T ref : PTm n) : PTm n := gaussianSum (f s) (count s N k) (data N k S T ref)
def otherSum (S T : PTm n) : PTm n := qadd (evaluate S qone) (evaluate T qone)

@[simp] theorem subst_count {m : ℕ} (σ : Fin n → PTm m) (s : Side) (N k : PTm n) :
    Syn.subst σ (count s N k) = count s (Syn.subst σ N) (Syn.subst σ k) := by cases s <;> simp [count]
@[simp] theorem subst_distance {m : ℕ} (σ : Fin n → PTm m) (s : Side) (k i : PTm n) :
    Syn.subst σ (distance s k i) = distance s (Syn.subst σ k) (Syn.subst σ i) := by cases s <;> simp [distance]
@[simp] theorem subst_weight {m : ℕ} (σ : Fin n → PTm m) (s : Side) (N k i : PTm n) :
    Syn.subst σ (weight s N k i) = weight s (Syn.subst σ N) (Syn.subst σ k) (Syn.subst σ i) := by cases s <;> simp [weight]
@[simp] theorem subst_payloadField {m : ℕ} (σ : Fin n → PTm m) (s : Side) (x : PTm n) :
    Syn.subst σ (payloadField s x) = payloadField s (Syn.subst σ x) := by simp [payloadField]
@[simp] theorem subst_payload {m : ℕ} (σ : Fin n → PTm m) (S T ref : PTm n) :
    Syn.subst σ (payload S T ref) = payload (Syn.subst σ S) (Syn.subst σ T) (Syn.subst σ ref) := by simp [payload]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (N k S T ref : PTm n) :
    Syn.subst σ (data N k S T ref) = data (Syn.subst σ N) (Syn.subst σ k)
      (Syn.subst σ S) (Syn.subst σ T) (Syn.subst σ ref) := by simp [data]
@[simp] theorem subst_sumNumerator {m : ℕ} (σ : Fin n → PTm m) (s : Side) (N k S T ref : PTm n) :
    Syn.subst σ (sumNumerator s N k S T ref) = sumNumerator s (Syn.subst σ N) (Syn.subst σ k)
      (Syn.subst σ S) (Syn.subst σ T) (Syn.subst σ ref) := by simp [sumNumerator]
@[simp] theorem subst_otherSum {m : ℕ} (σ : Fin n → PTm m) (S T : PTm n) :
    Syn.subst σ (otherSum S T) = otherSum (Syn.subst σ S) (Syn.subst σ T) := by simp [otherSum]

theorem scaled_program (s : Side) (N k GL GU i : PTm n) : Γ ⊢[PRAAx]
    ap2 (f s) i (GaussianOffDominantWeights.data N k (pairT GL GU)) ≐
      scale (GaussianOffDominantWeights.C N) (entry (original s GL GU) i) := by
  let x := GaussianOffDominantWeights.data N k (pairT GL GU)
  have tail : Γ ⊢[PRAAx] sndT x ≐ pairT k (pairT GL GU) := snd_pair _ _
  have pay := (congrSnd tail).eqTrans (snd_pair _ _)
  have field : Γ ⊢[PRAAx] payloadField s x ≐ original s GL GU := by
    cases s
    · exact (congrFst pay).eqTrans (fst_pair _ _)
    · exact (congrSnd pay).eqTrans (snd_pair _ _)
  have fields := Prf.eqCongr (Ax := PRAAx) (Γ := Γ)
    (scale (var 0) (entry (var 1) (var 2)) : PTm 3)
    (σ := ![GaussianOffDominantWeights.C (fstT x),payloadField s x,i])
    (σ' := ![GaussianOffDominantWeights.C N,original s GL GU,i])
    (fun j => by fin_cases j; exact congrAp2 powF (fst_pair _ _) (.eqRefl four); exact field; exact .eqRefl _)
  have program := toPR_eq (Γ := Γ) (scaledBody s) ![i,x]
  exact program.eqTrans (by simpa only [scaledBody,ComplexLogarithmRemainder.subst_scale,
    Foundations.MasterCertificate.subst_entry,subst_payloadField,GaussianOffDominantWeights.subst_C,
    subst_fstT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons] using fields)

theorem weight_program (s : Side) (N k p i : PTm n) : Γ ⊢[PRAAx]
    ap2 (g s) i (GaussianOffDominantWeights.data N k p) ≐ weight s N k i := by
  cases s
  · exact GaussianOffDominantWeights.lower_program N k p i
  · exact GaussianOffDominantWeights.upper_program N k p i

def entryBounds (s : Side) (N k S T ref : PTm n) : Fm PTm n := .all
  (lt (var 0) (count s (Syn.shift N) (Syn.shift k)) ⟶
    RationalArgmin.rationalLE
      (weightedNorm (unit (four*distance s (Syn.shift k) (var 0))) (entry (original s (Syn.shift S) (Syn.shift T)) (var 0)))
      (GaussianRationalMetric.qnormSq (Syn.shift ref)))

@[simp] theorem subst_entryBounds {m : ℕ} (σ : Fin n → PTm m) (s : Side) (N k S T ref : PTm n) :
    (entryBounds s N k S T ref).subst σ = entryBounds s (Syn.subst σ N) (Syn.subst σ k)
      (Syn.subst σ S) (Syn.subst σ T) (Syn.subst σ ref) := by simp [entryBounds,Syn.subst_shift,Syn.shift_subst]

theorem entry_bound_at (s : Side) (N k S T ref i : PTm n)
    (h : Γ ⊢[PRAAx] entryBounds s N k S T ref) (hi : Γ ⊢[PRAAx] lt i (count s N k)) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (weightedNorm (unit (four*distance s k i)) (entry (original s S T) i))
      (GaussianRationalMetric.qnormSq ref) := by
  have rule : Γ ⊢[PRAAx] lt i (count s N k) ⟶
      RationalArgmin.rationalLE (weightedNorm (unit (four*distance s k i)) (entry (original s S T) i))
        (GaussianRationalMetric.qnormSq ref) := by simpa [entryBounds] using h.allE i
  exact .impE rule hi

theorem point_bound (s : Side) (N k S T ref i : PTm n)
    (hkN : Γ ⊢[PRAAx] le k N) (hLen : Γ ⊢[PRAAx] length (original s S T) ≐ count s N k)
    (hi : Γ ⊢[PRAAx] lt i (count s N k))
    (hValue : Γ ⊢[PRAAx] RationalArgmin.rationalLE
      (weightedNorm (unit (four*distance s k i)) (entry (original s S T) i)) (GaussianRationalMetric.qnormSq ref)) : Γ ⊢[PRAAx]
    le (normSq (ap2 (f s) i (data N k S T ref)))
      (ap2 (g s) i (data N k S T ref)*ap2 (g s) i (data N k S T ref)*normSq (queryNumerator S T ref)) := by
  have hD := GaussianRationalNormalization.commonD_positive (Γ := Γ) S T ref
  have hEntry := GaussianRationalCover.entry_represents s S T ref i (lt_congr (.eqRefl _) hLen.eqSymm hi)
  have cleared := GaussianRationalNormClearing.weighted_clear _ _ _ _ _ _ hD hEntry
    (GaussianRationalNormalization.query_clearing S T ref) hValue
  have hd : Γ ⊢[PRAAx] le (distance s k i) N := by
    cases s
    · exact GaussianOffDominantWeights.lower_distance_bound N k i hkN
    · exact GaussianOffDominantWeights.upper_distance_bound N k i hi
  have scaled := GaussianOffDominantWeights.squared_reweight N (distance s k i) _ _ hd cleared
  have value := scaled_program (Γ := Γ) s N k (numerators .source S T ref) (numerators .target S T ref) i
  have w := weight_program (Γ := Γ) s N k (payload S T ref) i
  cases s <;> exact le_congr (ComplexLogarithmRemainder.congr_normSq value).eqSymm
    (congrMul (congrMul w.eqSymm w.eqSymm) (.eqRefl _)) scaled

theorem derived_term_bounds (s : Side) (N k S T ref : PTm n)
    (hkN : Γ ⊢[PRAAx] le k N) (hLen : Γ ⊢[PRAAx] length (original s S T) ≐ count s N k)
    (hBounds : Γ ⊢[PRAAx] entryBounds s N k S T ref) : Γ ⊢[PRAAx]
    termBounds (f s) (g s) (count s N k) (normSq (queryNumerator S T ref)) (data N k S T ref) := by
  refine .allI (.impI ?_)
  have hn : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift k) (Syn.shift N) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using hkN.shift
  have hl : Γ.map Fm.shift ⊢[PRAAx] length (original s (Syn.shift S) (Syn.shift T)) ≐ count s (Syn.shift N) (Syn.shift k) := by
    simpa only [Fm.shift,Fm.subst_eq,Foundations.SequenceComposition.subst_length,
      GaussianRationalCover.subst_original,subst_count,Syn.shift] using hLen.shift
  have hb : Γ.map Fm.shift ⊢[PRAAx] entryBounds s (Syn.shift N) (Syn.shift k) (Syn.shift S) (Syn.shift T) (Syn.shift ref) := by
    simpa only [Fm.shift,subst_entryBounds,Syn.shift] using hBounds.shift
  simpa only [Syn.shift,subst_count,subst_data,ComplexLogarithmRemainder.subst_normSq,
    GaussianRationalNormalization.subst_queryNumerator] using
    point_bound s (Syn.shift N) (Syn.shift k) (Syn.shift S) (Syn.shift T) (Syn.shift ref) (var 0)
      hn.wk hl.wk Prf.hyp0 (entry_bound_at s _ _ _ _ _ _ hb.wk Prf.hyp0)

theorem finite_side_bound (s : Side) (N k S T ref : PTm n)
    (hk : Γ ⊢[PRAAx] le one k) (hkN : Γ ⊢[PRAAx] le k N)
    (hLen : Γ ⊢[PRAAx] length (original s S T) ≐ count s N k)
    (hBounds : Γ ⊢[PRAAx] entryBounds s N k S T ref) : Γ ⊢[PRAAx]
    le (nine*normSq (sumNumerator s N k S T ref))
      (GaussianOffDominantWeights.C N*GaussianOffDominantWeights.C N*normSq (queryNumerator S T ref)) := by
  have budget : Γ ⊢[PRAAx] le (three*GaussianRelativeNormTriangle.weightSum (g s) (count s N k) (data N k S T ref))
      (GaussianOffDominantWeights.C N) := by
    cases s
    · exact GaussianOffDominantWeights.lower_budget N k (payload S T ref) hk hkN
    · exact GaussianOffDominantWeights.upper_budget N k (payload S T ref)
  exact GaussianRelativeNormTriangle.finite_sum_budget (f s) (g s) _ _ _ three _
    (derived_term_bounds s N k S T ref hkN hLen hBounds) budget

theorem scaled_entry_represents (s : Side) (N k S T ref i : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (length (original s S T))) : Γ ⊢[PRAAx]
    represents (entry (original s S T) i) (ap2 (f s) i (data N k S T ref))
      (GaussianOffDominantWeights.C N*commonD S T ref) :=
  GaussianRationalHorner.represents_congr (.eqRefl _)
    (GaussianRootAlgebra.equal_of_code
      (scaled_program s N k (numerators .source S T ref) (numerators .target S T ref) i).eqSymm)
    (mul_comm _ _) (GaussianRationalHorner.represents_rescale _ _ _ (GaussianOffDominantWeights.C N)
      (GaussianRationalCover.entry_represents s S T ref i hi))

theorem scaled_entry_representations (s : Side) (N k S T ref : PTm n) : Γ ⊢[PRAAx]
    GaussianHornerCommonDenominator.entryRepresentations (f s) (original s S T)
      (GaussianOffDominantWeights.C N*commonD S T ref) (length (original s S T)) (data N k S T ref) := by
  refine .allI (.impI ?_)
  simpa only [Syn.shift,GaussianRationalCover.subst_original,GaussianOffDominantWeights.subst_C,
    Foundations.SequenceComposition.subst_length,GaussianRationalNormalization.subst_commonD,PTm.subst_mul,subst_data] using
    scaled_entry_represents s (Syn.shift N) (Syn.shift k) (Syn.shift S) (Syn.shift T) (Syn.shift ref) (var 0) Prf.hyp0

theorem sum_part_represents (s : Side) (N k S T ref : PTm n)
    (hLen : Γ ⊢[PRAAx] length (original s S T) ≐ count s N k) : Γ ⊢[PRAAx]
    represents (evaluate (original s S T) qone) (sumNumerator s N k S T ref)
      (GaussianOffDominantWeights.C N*commonD S T ref) := by
  have hD := GaussianRationalHorner.positive_product _ _ (GaussianOffDominantWeights.C_positive (Γ := Γ) N)
    (GaussianRationalNormalization.commonD_positive (Γ := Γ) S T ref)
  have raw := GaussianHornerCommonDenominator.evaluate_represents (f s) (original s S T)
    (GaussianOffDominantWeights.C N*commonD S T ref) (data N k S T ref) hD
    (scaled_entry_representations s N k S T ref)
  exact GaussianRationalHorner.represents_congr (.eqRefl _)
    (GaussianRootAlgebra.equal_of_code (congrAp2 (GaussianRelativeNormTriangle.gaussianSumF (f s)) hLen (.eqRefl _)))
    (.eqRefl _) raw

/-- The value of the actual rational sum is proved at its computed
common scaled denominator, rather than supplied as an output law. -/
theorem other_sum_represents (N k S T ref : PTm n)
    (hSL : Γ ⊢[PRAAx] length S ≐ count .source N k) (hTL : Γ ⊢[PRAAx] length T ≐ count .target N k) : Γ ⊢[PRAAx]
    represents (otherSum S T) (add (sumNumerator .source N k S T ref) (sumNumerator .target N k S T ref))
      (GaussianOffDominantWeights.C N*commonD S T ref) :=
  GaussianRationalHorner.qadd_represents _ _ _ _ _
    (GaussianRationalHorner.positive_product _ _ (GaussianOffDominantWeights.C_positive N)
      (GaussianRationalNormalization.commonD_positive S T ref))
    (sum_part_represents .source N k S T ref hSL) (sum_part_represents .target N k S T ref hTL)

/-- Exact 2/3 relative norm bound for the two original rational lists.
Only their individual geometric comparisons are local mathematical inputs. -/
theorem geometric_sum_bound (N k S T ref : PTm n)
    (hk : Γ ⊢[PRAAx] le one k) (hkN : Γ ⊢[PRAAx] le k N)
    (hSL : Γ ⊢[PRAAx] length S ≐ count .source N k) (hTL : Γ ⊢[PRAAx] length T ≐ count .target N k)
    (hLower : Γ ⊢[PRAAx] entryBounds .source N k S T ref)
    (hUpper : Γ ⊢[PRAAx] entryBounds .target N k S T ref) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (weightedNorm nine (otherSum S T)) (weightedNorm four ref) :=
  GaussianRationalNormClearing.scaled_bound _ _ _ _ _ _
    (GaussianOffDominantWeights.C_positive N) (GaussianRationalNormalization.commonD_positive S T ref)
    (other_sum_represents N k S T ref hSL hTL) (GaussianRationalNormalization.query_clearing S T ref)
    (GaussianRationalNormClearing.two_sum_bound _ _ _ _
      (finite_side_bound .source N k S T ref hk hkN hSL hLower)
      (finite_side_bound .target N k S T ref hk hkN hTL hUpper))

theorem actual_geometric_sum_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ le (var 1) (var 0) ⟶
      length (var 2) ≐ count .source (var 0) (var 1) ⟶ length (var 3) ≐ count .target (var 0) (var 1) ⟶
      entryBounds .source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      entryBounds .target (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      RationalArgmin.rationalLE (weightedNorm nine (otherSum (var 2) (var 3))) (weightedNorm four (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (.impI (.impI
    (geometric_sum_bound _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk
      Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))))

end LeanProofs.IPRA.Analysis.GaussianGeometricSumBound
