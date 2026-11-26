import IPRADerivations.Analysis.Polynomials.RootFinding.DominantTerms.GaussianOffDominantSum
import IPRADerivations.Analysis.Polynomials.RootFinding.DominantTerms.GaussianDominantPairAlgebra
import IPRADerivations.Foundations.FiniteFiberGrouping
import IPRADerivations.Analysis.Polynomials.RootFinding.DominantTerms.GaussianTranslatedDominantPlateau
import IPRADerivations.Analysis.Polynomials.RootFinding.Descent.GaussianTranslatedNonconstant

/-!
# Finite lower cuts for the sum of individual off-dominant magnitudes

All original geometric weights and cleared numerators are retained.
Independent nonnegative scalar lower approximants are placed on the
positive real axis. Their actual Gaussian fold is identified with the
actual natural sum; hence the bound concerns the sum of individual
Euclidean lengths rather than the norm of the original vector sum.
-/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

namespace LeanProofs.IPRA.Analysis.GaussianOffDominantMagnitudeSum

open_ipra
open GaussianRootAlgebra (equal equal_of_code equal_refl equal_trans add_equal normSq_equal)
open ComplexLogarithmRemainder (normSq add zeroCode)
open GaussianDominantPairAlgebra (radiusNumerator)
open GaussianRationalCover (Side original)
open GaussianRelativeNormTriangle (gaussianSum gaussianSumF)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def naturalSum (f : PTm 2) (N x : PTm n) : PTm n := ap2 (sumF f) N x
def positiveBody (f : PTm 2) : PTm 2 := radiusNumerator f
def positiveF (f : PTm 2) : PR 2 := PTm.toPR (positiveBody f)
def positiveSum (f : PTm 2) (N x : PTm n) : PTm n := gaussianSum (positiveF f) N x
ipra_subst naturalSum
ipra_subst positiveSum

theorem natural_point_congr {A B : PTm n} (h : Γ ⊢[PRAAx] A ≐ B) : Γ ⊢[PRAAx] radiusNumerator A ≐ radiusNumerator B := by
  ipra_congr (radiusNumerator (var 0) : PTm 1) with [h]
theorem natural_point_add (A B : PTm n) : Γ ⊢[PRAAx]
    equal (add (radiusNumerator A) (radiusNumerator B)) (radiusNumerator (A+B)) := by
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,GaussianDominantPairAlgebra.radiusNumerator,
      ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat] <;> ipra_simps <;> ring

theorem positive_program (f : PTm 2) (i x : PTm n) : Γ ⊢[PRAAx]
    ap2 (positiveF f) i x ≐ radiusNumerator (inst2 f i x) := by
  simpa only [positiveF,positiveBody,GaussianDominantPairAlgebra.subst_radiusNumerator,inst2,ap2] using
    toPR_eq (Γ := Γ) (positiveBody f) ![i,x]

theorem positive_sum_value (f : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx]
    equal (positiveSum f N x) (radiusNumerator (naturalSum f N x)) := by
  have all : Γ ⊢[PRAAx] .all
      (equal (positiveSum f (var 0) (Syn.shift x)) (radiusNumerator (naturalSum f (var 0) (Syn.shift x)))) := by
    ipra_qfind (⟨trivial,trivial⟩) [GaussianRootAlgebra.subst_equal, subst_positiveSum, subst_naturalSum,
        GaussianDominantPairAlgebra.subst_radiusNumerator]
    · exact equal_trans (equal_of_code (GaussianRelativeNormTriangle.gaussian_sum_zero _ _))
        (equal_of_code (natural_point_congr (LeanProofs.IPRA.sum_zero f x)).eqSymm)
    · let Δ := equal (positiveSum f (var 0) (Syn.shift x)) (radiusNumerator (naturalSum f (var 0) (Syn.shift x))) :: Γ.map Fm.shift
      have step := equal_trans (equal_of_code (GaussianRelativeNormTriangle.gaussian_sum_succ (Γ := Δ)
          (positiveF f) (var 0) (Syn.shift x)))
        (add_equal Prf.hyp0 (equal_of_code (positive_program f (var 0) (Syn.shift x))))
      exact equal_trans step (equal_trans (natural_point_add _ _)
        (equal_of_code (natural_point_congr (LeanProofs.IPRA.sum_succ' f (var 0) (Syn.shift x))).eqSymm))
  simpa only [GaussianRootAlgebra.subst_equal,subst_positiveSum,subst_naturalSum,
    GaussianDominantPairAlgebra.subst_radiusNumerator,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

theorem positive_sum_norm (f : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx]
    normSq (positiveSum f N x) ≐ naturalSum f N x*naturalSum f N x :=
  (normSq_equal (positive_sum_value f N x)).eqTrans (GaussianDominantPairAlgebra.radius_numerator_norm _)

def candidateData (N k A B : PTm n) : PTm n := GaussianOffDominantWeights.data N k (pairT A B)
def candidateBody (s : Side) : PTm 2 := entry (GaussianGeometricSumBound.payloadField s (var 1)) (var 0)
def candidateSum (s : Side) (N k A B : PTm n) : PTm n :=
  positiveSum (candidateBody s) (GaussianGeometricSumBound.count s N k) (candidateData N k A B)
def candidateTotal (N k A B : PTm n) : PTm n :=
  naturalSum (candidateBody .source) (GaussianGeometricSumBound.count .source N k) (candidateData N k A B)+
    naturalSum (candidateBody .target) (GaussianGeometricSumBound.count .target N k) (candidateData N k A B)
def lowerCandidates (s : Side) (N k S T ref H A B : PTm n) : Fm PTm n := .all
  (lt (var 0) (GaussianGeometricSumBound.count s (Syn.shift N) (Syn.shift k)) ⟶
    le (entry (original s (Syn.shift A) (Syn.shift B)) (var 0)*entry (original s (Syn.shift A) (Syn.shift B)) (var 0))
      (Syn.shift H*Syn.shift H*normSq (ap2 (GaussianGeometricSumBound.f s) (var 0)
        (GaussianGeometricSumBound.data (Syn.shift N) (Syn.shift k) (Syn.shift S) (Syn.shift T) (Syn.shift ref)))))
ipra_subst candidateData
ipra_subst candidateSum
ipra_subst candidateTotal
ipra_subst lowerCandidates [Syn.subst_shift, Syn.shift_subst]

theorem candidate_body_at (s : Side) (N k A B i : PTm n) : Γ ⊢[PRAAx]
    inst2 (candidateBody s) i (candidateData N k A B) ≐ entry (original s A B) i := by
  let x := candidateData N k A B
  have tail : Γ ⊢[PRAAx] sndT x ≐ pairT k (pairT A B) := snd_pair _ _
  have pay := tail.sndE
  have field : Γ ⊢[PRAAx] GaussianGeometricSumBound.payloadField s x ≐ original s A B := by
    cases s
    · exact pay.fstE
    · exact pay.sndE
  simpa only [candidateBody,inst2,Foundations.MasterCertificate.subst_entry,
    GaussianGeometricSumBound.subst_payloadField,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    entry_congr field (.eqRefl i)
theorem candidate_program (s : Side) (N k A B i : PTm n) : Γ ⊢[PRAAx]
    ap2 (positiveF (candidateBody s)) i (candidateData N k A B) ≐ radiusNumerator (entry (original s A B) i) :=
  (positive_program _ _ _).eqTrans (natural_point_congr (candidate_body_at s N k A B i))
theorem lower_candidate_at (s : Side) (N k S T ref H A B i : PTm n)
    (h : Γ ⊢[PRAAx] lowerCandidates s N k S T ref H A B)
    (hi : Γ ⊢[PRAAx] lt i (GaussianGeometricSumBound.count s N k)) : Γ ⊢[PRAAx]
    le (entry (original s A B) i*entry (original s A B) i)
      (H*H*normSq (ap2 (GaussianGeometricSumBound.f s) i (GaussianGeometricSumBound.data N k S T ref))) := by
  have rule : Γ ⊢[PRAAx] lt i (GaussianGeometricSumBound.count s N k) ⟶
      le (entry (original s A B) i*entry (original s A B) i)
        (H*H*normSq (ap2 (GaussianGeometricSumBound.f s) i (GaussianGeometricSumBound.data N k S T ref))) := by
    simpa [lowerCandidates] using h.allE i
  exact .impE rule hi

theorem candidate_point_bound (s : Side) (N k S T ref H A B i : PTm n)
    (hkN : Γ ⊢[PRAAx] le k N)
    (hLen : Γ ⊢[PRAAx] length (original s S T) ≐ GaussianGeometricSumBound.count s N k)
    (hi : Γ ⊢[PRAAx] lt i (GaussianGeometricSumBound.count s N k))
    (hGeometric : Γ ⊢[PRAAx] GaussianGeometricSumBound.entryBounds s N k S T ref)
    (hApprox : Γ ⊢[PRAAx] lowerCandidates s N k S T ref H A B) : Γ ⊢[PRAAx]
    le (normSq (ap2 (positiveF (candidateBody s)) i (candidateData N k A B)))
      (ap2 (GaussianGeometricSumBound.g s) i (candidateData N k A B)*
        ap2 (GaussianGeometricSumBound.g s) i (candidateData N k A B)*
          (H*H*normSq (GaussianRationalNormalization.queryNumerator S T ref))) := by
  have originalBound := GaussianGeometricSumBound.point_bound s N k S T ref i hkN hLen hi
    (GaussianGeometricSumBound.entry_bound_at s _ _ _ _ _ _ hGeometric hi)
  have small := lower_candidate_at s N k S T ref H A B i hApprox hi
  have scaled : Γ ⊢[PRAAx] le
      (H*H*normSq (ap2 (GaussianGeometricSumBound.f s) i (GaussianGeometricSumBound.data N k S T ref)))
      (ap2 (GaussianGeometricSumBound.g s) i (GaussianGeometricSumBound.data N k S T ref)*
        ap2 (GaussianGeometricSumBound.g s) i (GaussianGeometricSumBound.data N k S T ref)*
          (H*H*normSq (GaussianRationalNormalization.queryNumerator S T ref))) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (H*H) originalBound)
  have weight : Γ ⊢[PRAAx] ap2 (GaussianGeometricSumBound.g s) i (GaussianGeometricSumBound.data N k S T ref) ≐
      ap2 (GaussianGeometricSumBound.g s) i (candidateData N k A B) :=
    (GaussianGeometricSumBound.weight_program s N k (GaussianGeometricSumBound.payload S T ref) i).eqTrans
      (GaussianGeometricSumBound.weight_program s N k (pairT A B) i).eqSymm
  have value := (ComplexLogarithmRemainder.congr_normSq (candidate_program (Γ := Γ) s N k A B i)).eqTrans
    (GaussianDominantPairAlgebra.radius_numerator_norm _)
  exact le_congr value.eqSymm (congrMul (congrMul weight weight) (.eqRefl _)) (le_trans small scaled)

theorem candidate_term_bounds (s : Side) (N k S T ref H A B : PTm n)
    (hkN : Γ ⊢[PRAAx] le k N)
    (hLen : Γ ⊢[PRAAx] length (original s S T) ≐ GaussianGeometricSumBound.count s N k)
    (hGeometric : Γ ⊢[PRAAx] GaussianGeometricSumBound.entryBounds s N k S T ref)
    (hApprox : Γ ⊢[PRAAx] lowerCandidates s N k S T ref H A B) : Γ ⊢[PRAAx]
    GaussianRelativeNormTriangle.termBounds (positiveF (candidateBody s)) (GaussianGeometricSumBound.g s)
      (GaussianGeometricSumBound.count s N k) (H*H*normSq (GaussianRationalNormalization.queryNumerator S T ref)) (candidateData N k A B) := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift (GaussianGeometricSumBound.count s N k)) :: Γ.map Fm.shift
  have kn : Δ ⊢[PRAAx] le (Syn.shift k) (Syn.shift N) := by simpa [Δ,Fm.shift,Syn.shift] using hkN.shift.wk
  have len : Δ ⊢[PRAAx] length (original s (Syn.shift S) (Syn.shift T)) ≐ GaussianGeometricSumBound.count s (Syn.shift N) (Syn.shift k) := by
    simpa [Δ,Fm.shift,Syn.shift] using hLen.shift.wk
  have geo : Δ ⊢[PRAAx] GaussianGeometricSumBound.entryBounds s (Syn.shift N) (Syn.shift k) (Syn.shift S) (Syn.shift T) (Syn.shift ref) := by
    simpa [Δ,Fm.shift,Syn.shift] using hGeometric.shift.wk
  have approx : Δ ⊢[PRAAx] lowerCandidates s (Syn.shift N) (Syn.shift k) (Syn.shift S) (Syn.shift T) (Syn.shift ref)
      (Syn.shift H) (Syn.shift A) (Syn.shift B) := by simpa [Δ,Fm.shift,Syn.shift] using hApprox.shift.wk
  have actual := candidate_point_bound (Γ := Δ) s (Syn.shift N) (Syn.shift k) (Syn.shift S) (Syn.shift T) (Syn.shift ref)
    (Syn.shift H) (Syn.shift A) (Syn.shift B) (var 0) kn len (by simpa [Δ,Syn.shift] using Prf.hyp0) geo approx
  simpa only [Δ,Syn.shift,GaussianGeometricSumBound.subst_count,PTm.subst_mul,ComplexLogarithmRemainder.subst_normSq,
    GaussianRationalNormalization.subst_queryNumerator,subst_candidateData] using actual

theorem candidate_side_bound (s : Side) (N k S T ref H A B : PTm n)
    (hk : Γ ⊢[PRAAx] le one k) (hkN : Γ ⊢[PRAAx] le k N)
    (hLen : Γ ⊢[PRAAx] length (original s S T) ≐ GaussianGeometricSumBound.count s N k)
    (hGeometric : Γ ⊢[PRAAx] GaussianGeometricSumBound.entryBounds s N k S T ref)
    (hApprox : Γ ⊢[PRAAx] lowerCandidates s N k S T ref H A B) : Γ ⊢[PRAAx]
    le (GaussianRationalNormClearing.nine*normSq (candidateSum s N k A B))
      (GaussianOffDominantWeights.C N*GaussianOffDominantWeights.C N*
        (H*H*normSq (GaussianRationalNormalization.queryNumerator S T ref))) := by
  have budget : Γ ⊢[PRAAx] le
      (GaussianRationalNormClearing.three*GaussianRelativeNormTriangle.weightSum (GaussianGeometricSumBound.g s)
        (GaussianGeometricSumBound.count s N k) (candidateData N k A B)) (GaussianOffDominantWeights.C N) := by
    cases s
    · exact GaussianOffDominantWeights.lower_budget N k (pairT A B) hk hkN
    · exact GaussianOffDominantWeights.upper_budget N k (pairT A B)
  exact GaussianRelativeNormTriangle.finite_sum_budget (positiveF (candidateBody s)) (GaussianGeometricSumBound.g s)
    _ _ _ GaussianRationalNormClearing.three _ (candidate_term_bounds s N k S T ref H A B hkN hLen hGeometric hApprox) budget

theorem candidate_combined_norm (N k A B : PTm n) : Γ ⊢[PRAAx]
    normSq (add (candidateSum .source N k A B) (candidateSum .target N k A B)) ≐
      candidateTotal N k A B*candidateTotal N k A B := by
  have value : Γ ⊢[PRAAx] equal
      (add (candidateSum .source N k A B) (candidateSum .target N k A B)) (radiusNumerator (candidateTotal N k A B)) :=
    equal_trans (add_equal
      (positive_sum_value (candidateBody .source) (GaussianGeometricSumBound.count .source N k) (candidateData N k A B))
      (positive_sum_value (candidateBody .target) (GaussianGeometricSumBound.count .target N k) (candidateData N k A B)))
      (natural_point_add _ _)
  exact (normSq_equal value).eqTrans (GaussianDominantPairAlgebra.radius_numerator_norm _)

/-- Every independent nonnegative rational lower tuple satisfies the exact
2/3 bound. The final actual square-root sampler supplies such tuples. -/
theorem lower_list_bound (N k S T ref H A B : PTm n)
    (hk : Γ ⊢[PRAAx] le one k) (hkN : Γ ⊢[PRAAx] le k N)
    (hSL : Γ ⊢[PRAAx] length S ≐ GaussianGeometricSumBound.count .source N k)
    (hTL : Γ ⊢[PRAAx] length T ≐ GaussianGeometricSumBound.count .target N k)
    (hLower : Γ ⊢[PRAAx] GaussianGeometricSumBound.entryBounds .source N k S T ref)
    (hUpper : Γ ⊢[PRAAx] GaussianGeometricSumBound.entryBounds .target N k S T ref)
    (hA : Γ ⊢[PRAAx] lowerCandidates .source N k S T ref H A B)
    (hB : Γ ⊢[PRAAx] lowerCandidates .target N k S T ref H A B) : Γ ⊢[PRAAx]
    le (GaussianRationalNormClearing.nine*(candidateTotal N k A B*candidateTotal N k A B))
      (GaussianDominantSyntax.four*GaussianOffDominantWeights.C N*GaussianOffDominantWeights.C N*H*H*
        normSq (GaussianRationalNormalization.queryNumerator S T ref)) := by
  have actual := GaussianRationalNormClearing.two_sum_bound _ _ (GaussianOffDominantWeights.C N)
    (H*H*normSq (GaussianRationalNormalization.queryNumerator S T ref))
    (candidate_side_bound .source N k S T ref H A B hk hkN hSL hLower hA)
    (candidate_side_bound .target N k S T ref H A B hk hkN hTL hUpper hB)
  exact le_congr (congrMul (.eqRefl _) (candidate_combined_norm _ _ _ _)) (by ipra_ring) actual

def rootTerm (s : Side) (N k S T ref H i : PTm n) : PTm n :=
  isqrt (normSq (ap2 (GaussianGeometricSumBound.f s) i (GaussianGeometricSumBound.data N k S T ref))*H*H)
def rootData (N k S T ref H : PTm n) : PTm n := pairT (GaussianGeometricSumBound.data N k S T ref) H
def rootBody (s : Side) : PTm 2 := isqrt (normSq (ap2 (GaussianGeometricSumBound.f s) (var 0) (fstT (var 1)))*sndT (var 1)*sndT (var 1))
def rootList (s : Side) (N k S T ref H : PTm n) : PTm n :=
  sequence (rootBody s) (GaussianGeometricSumBound.count s N k) (rootData N k S T ref H)
def rootTotal (N k S T ref H : PTm n) : PTm n := candidateTotal N k (rootList .source N k S T ref H) (rootList .target N k S T ref H)
ipra_subst rootTerm
ipra_subst rootData
ipra_subst rootList
ipra_subst rootTotal

theorem root_lower (s : Side) (N k S T ref H i : PTm n) : Γ ⊢[PRAAx]
    le (rootTerm s N k S T ref H i*rootTerm s N k S T ref H i)
      (H*H*normSq (ap2 (GaussianGeometricSumBound.f s) i (GaussianGeometricSumBound.data N k S T ref))) :=
  le_congr (.eqRefl _) (by ipra_ring) (isqrt_le _)
theorem root_upper (s : Side) (N k S T ref H i : PTm n) : Γ ⊢[PRAAx]
    lt (H*H*normSq (ap2 (GaussianGeometricSumBound.f s) i (GaussianGeometricSumBound.data N k S T ref)))
      (succ (rootTerm s N k S T ref H i)*succ (rootTerm s N k S T ref H i)) :=
  lt_congr (by ipra_ring) (congrMul (succ_eq_add_one _).eqSymm (succ_eq_add_one _).eqSymm) (lt_isqrt_succ_sq _)
theorem root_body_at (s : Side) (N k S T ref H i : PTm n) : Γ ⊢[PRAAx]
    inst2 (rootBody s) i (rootData N k S T ref H) ≐ rootTerm s N k S T ref H i := by
  simp only [rootBody,inst2,subst_ap2,ComplexLogarithmRemainder.subst_normSq,PTm.subst_mul,isqrt,subst_ap1,
    subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact congrAp1 isqrtF (congrMul (congrMul (ComplexLogarithmRemainder.congr_normSq
    (congrAp2 (GaussianGeometricSumBound.f s) (.eqRefl _) (fst_pair _ _))) (snd_pair _ _)) (snd_pair _ _))
theorem root_list_length (s : Side) (N k S T ref H : PTm n) : Γ ⊢[PRAAx]
    length (rootList s N k S T ref H) ≐ GaussianGeometricSumBound.count s N k := sequence_length _ _ _
theorem root_list_lookup (s : Side) (N k S T ref H i : PTm n) (hi : Γ ⊢[PRAAx] lt i (GaussianGeometricSumBound.count s N k)) : Γ ⊢[PRAAx]
    entry (rootList s N k S T ref H) i ≐ rootTerm s N k S T ref H i :=
  (sequence_decode (rootBody s) (x := rootData N k S T ref H) hi).eqTrans (root_body_at s N k S T ref H i)

theorem sampler_lower_candidates (s : Side) (N k S T ref H : PTm n) : Γ ⊢[PRAAx]
    lowerCandidates s N k S T ref H (rootList .source N k S T ref H) (rootList .target N k S T ref H) := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift (GaussianGeometricSumBound.count s N k)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (GaussianGeometricSumBound.count s (Syn.shift N) (Syn.shift k)) := by simpa [Δ,Syn.shift] using Prf.hyp0
  have value : Δ ⊢[PRAAx] entry (original s (rootList .source (Syn.shift N) (Syn.shift k) (Syn.shift S) (Syn.shift T) (Syn.shift ref) (Syn.shift H))
      (rootList .target (Syn.shift N) (Syn.shift k) (Syn.shift S) (Syn.shift T) (Syn.shift ref) (Syn.shift H))) (var 0) ≐
      rootTerm s (Syn.shift N) (Syn.shift k) (Syn.shift S) (Syn.shift T) (Syn.shift ref) (Syn.shift H) (var 0) := by
    cases s <;> exact root_list_lookup _ _ _ _ _ _ _ _ hi
  have actual := le_congr (congrMul value value).eqSymm (.eqRefl _)
    (root_lower s (Syn.shift N) (Syn.shift k) (Syn.shift S) (Syn.shift T) (Syn.shift ref) (Syn.shift H) (var 0))
  simpa only [Δ,Syn.shift,GaussianGeometricSumBound.subst_count,GaussianRationalCover.subst_original,
    Foundations.MasterCertificate.subst_entry,PTm.subst_mul,ComplexLogarithmRemainder.subst_normSq,
    GaussianGeometricSumBound.subst_data,subst_rootList] using actual

theorem sampled_magnitude_bound (N k S T ref H : PTm n)
    (hk : Γ ⊢[PRAAx] le one k) (hkN : Γ ⊢[PRAAx] le k N)
    (hSL : Γ ⊢[PRAAx] length S ≐ GaussianGeometricSumBound.count .source N k)
    (hTL : Γ ⊢[PRAAx] length T ≐ GaussianGeometricSumBound.count .target N k)
    (hLower : Γ ⊢[PRAAx] GaussianGeometricSumBound.entryBounds .source N k S T ref)
    (hUpper : Γ ⊢[PRAAx] GaussianGeometricSumBound.entryBounds .target N k S T ref) : Γ ⊢[PRAAx]
    le (GaussianRationalNormClearing.nine*(rootTotal N k S T ref H*rootTotal N k S T ref H))
      (GaussianDominantSyntax.four*GaussianOffDominantWeights.C N*GaussianOffDominantWeights.C N*H*H*
        normSq (GaussianRationalNormalization.queryNumerator S T ref)) :=
  lower_list_bound N k S T ref H _ _ hk hkN hSL hTL hLower hUpper
    (sampler_lower_candidates .source _ _ _ _ _ _) (sampler_lower_candidates .target _ _ _ _ _ _)

def totalBound (N k S T ref H A B : PTm n) : Fm PTm n :=
  le (GaussianRationalNormClearing.nine*(candidateTotal N k A B*candidateTotal N k A B))
    (GaussianDominantSyntax.four*GaussianOffDominantWeights.C N*GaussianOffDominantWeights.C N*H*H*
      normSq (GaussianRationalNormalization.queryNumerator S T ref))
def magnitudeCut (N k S T ref : PTm n) : Fm PTm n := .all (.all (.all
  (lowerCandidates .source (Syn.shift (Syn.shift (Syn.shift N))) (Syn.shift (Syn.shift (Syn.shift k)))
      (Syn.shift (Syn.shift (Syn.shift S))) (Syn.shift (Syn.shift (Syn.shift T))) (Syn.shift (Syn.shift (Syn.shift ref)))
      (var 2) (var 1) (var 0) ⟶
    lowerCandidates .target (Syn.shift (Syn.shift (Syn.shift N))) (Syn.shift (Syn.shift (Syn.shift k)))
      (Syn.shift (Syn.shift (Syn.shift S))) (Syn.shift (Syn.shift (Syn.shift T))) (Syn.shift (Syn.shift (Syn.shift ref)))
      (var 2) (var 1) (var 0) ⟶
    totalBound (Syn.shift (Syn.shift (Syn.shift N))) (Syn.shift (Syn.shift (Syn.shift k)))
      (Syn.shift (Syn.shift (Syn.shift S))) (Syn.shift (Syn.shift (Syn.shift T))) (Syn.shift (Syn.shift (Syn.shift ref)))
      (var 2) (var 1) (var 0))))
ipra_subst totalBound
@[simp] theorem subst_magnitudeCut {l : ℕ} (σ : Fin n → PTm l) (N k S T ref : PTm n) :
    (magnitudeCut N k S T ref).subst σ = magnitudeCut (Syn.subst σ N) (Syn.subst σ k)
      (Syn.subst σ S) (Syn.subst σ T) (Syn.subst σ ref) := by
  have atTwo : Syn.up (Syn.up (Syn.up σ)) (2 : Fin (n+1+1+1)) = var 2 := by rfl
  simp [magnitudeCut,Syn.subst_shift,Syn.shift_subst,atTwo]

theorem geometric_magnitude_cut (N k S T ref : PTm n)
    (hk : Γ ⊢[PRAAx] le one k) (hkN : Γ ⊢[PRAAx] le k N)
    (hSL : Γ ⊢[PRAAx] length S ≐ GaussianGeometricSumBound.count .source N k)
    (hTL : Γ ⊢[PRAAx] length T ≐ GaussianGeometricSumBound.count .target N k)
    (hLower : Γ ⊢[PRAAx] GaussianGeometricSumBound.entryBounds .source N k S T ref)
    (hUpper : Γ ⊢[PRAAx] GaussianGeometricSumBound.entryBounds .target N k S T ref) : Γ ⊢[PRAAx]
    magnitudeCut N k S T ref := by
  refine .allI (.allI (.allI (.impI (.impI ?_))))
  let N' := Syn.shift (Syn.shift (Syn.shift N))
  let k' := Syn.shift (Syn.shift (Syn.shift k))
  let S' := Syn.shift (Syn.shift (Syn.shift S))
  let T' := Syn.shift (Syn.shift (Syn.shift T))
  let r' := Syn.shift (Syn.shift (Syn.shift ref))
  let Δ := lowerCandidates .target N' k' S' T' r' (var 2) (var 1) (var 0) ::
    lowerCandidates .source N' k' S' T' r' (var 2) (var 1) (var 0) ::
      ((Γ.map Fm.shift).map Fm.shift).map Fm.shift
  have kk : Δ ⊢[PRAAx] le one k' := by simpa [Δ,k',Fm.shift,Syn.shift,one] using hk.shift.shift.shift.wk.wk
  have kn : Δ ⊢[PRAAx] le k' N' := by simpa [Δ,k',N',Fm.shift,Syn.shift] using hkN.shift.shift.shift.wk.wk
  have sl : Δ ⊢[PRAAx] length S' ≐ GaussianGeometricSumBound.count .source N' k' := by
    simpa [Δ,k',N',S',Fm.shift,Syn.shift] using hSL.shift.shift.shift.wk.wk
  have tl : Δ ⊢[PRAAx] length T' ≐ GaussianGeometricSumBound.count .target N' k' := by
    simpa [Δ,k',N',T',Fm.shift,Syn.shift] using hTL.shift.shift.shift.wk.wk
  have lo : Δ ⊢[PRAAx] GaussianGeometricSumBound.entryBounds .source N' k' S' T' r' := by
    simpa [Δ,k',N',S',T',r',Fm.shift,Syn.shift] using hLower.shift.shift.shift.wk.wk
  have up : Δ ⊢[PRAAx] GaussianGeometricSumBound.entryBounds .target N' k' S' T' r' := by
    simpa [Δ,k',N',S',T',r',Fm.shift,Syn.shift] using hUpper.shift.shift.shift.wk.wk
  exact lower_list_bound N' k' S' T' r' (var 2) (var 1) (var 0) kk kn sl tl lo up Prf.hyp1 Prf.hyp0

/-- The actual selected positive real radius; no displacement is supplied. -/
def radialPoint (C N : PTm n) : PTm n := GaussianDominantPairAlgebra.radiusPoint
  (GaussianOffDominantTerms.radiusNumerator C N) (GaussianOffDominantTerms.radiusDenominator C N)
def radialLower (C N : PTm n) : PTm n := GaussianOffDominantSum.lower C N (radialPoint C N)
def radialUpper (C N : PTm n) : PTm n := GaussianOffDominantSum.upper C N (radialPoint C N)
def sourceCut (C N : PTm n) : Fm PTm n := magnitudeCut N (GaussianDominantPlateau.winner C N)
  (radialLower C N) (radialUpper C N) (GaussianOffDominantTerms.selectedReference C N)
def sourceRoot (s : Side) (C N H : PTm n) : PTm n := rootList s N (GaussianDominantPlateau.winner C N)
  (radialLower C N) (radialUpper C N) (GaussianOffDominantTerms.selectedReference C N) H
def sourceTotal (C N H : PTm n) : PTm n := rootTotal N (GaussianDominantPlateau.winner C N)
  (radialLower C N) (radialUpper C N) (GaussianOffDominantTerms.selectedReference C N) H
ipra_subst radialPoint
ipra_subst radialLower
ipra_subst radialUpper
ipra_subst sourceCut
ipra_subst sourceRoot
ipra_subst sourceTotal

theorem radial_within (C N : PTm n) : Γ ⊢[PRAAx] GaussianOffDominantTerms.withinRadius C N (radialPoint C N) :=
  GaussianDominantPairAlgebra.radius_bounded _ _ (GaussianOffDominantTerms.radius_denominator_positive C N)

theorem radial_term_reference (C N A B i : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    GaussianOffDominantTerms.term C N (GaussianDominantPairAlgebra.radiusPoint A B) i ≐
      GaussianOffDominantTerms.reference C N A B i := by
  have hd := GaussianRationalHorner.positive_product _ _
    (GaussianRationalL1.raw_den_positive (GaussianBalancedRadiusSyntax.coefficient C N i))
    (GaussianPolynomialPerturbation.power_positive B i hB)
  exact GaussianRationalHorner.canonical_unique _ _ _ _
    (GaussianOffDominantTerms.term_canonical _ _ _ _) (GaussianOffDominantTerms.reference_canonical _ _ _ _ _ hB) hd
    (GaussianDominantPairAlgebra.radial_represents _ _ _ _ hB)
    (GaussianRationalHorner.ofGaussian_represents _ _ hd)

theorem radial_term_norm (C N i : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalMetric.qnormSq (GaussianOffDominantTerms.term C N (radialPoint C N) i) ≐
      RationalArithmetic.multiply (GaussianRationalMetric.qnormSq (GaussianBalancedRadiusSyntax.coefficient C N i))
        (RationalNonnegativePowers.power (GaussianOffDominantTerms.radiusNumerator C N)
          (GaussianOffDominantTerms.radiusDenominator C N) (two*i)) :=
  (GaussianRationalProductWitness.qnormSq_congr (radial_term_reference C N _ _ i (GaussianOffDominantTerms.radius_denominator_positive C N))).eqTrans
    (GaussianOffDominantTerms.reference_norm_general _ _ _ _ _ (GaussianOffDominantTerms.radius_denominator_positive C N))

/-- Exact source sum-of-individual-magnitudes lower cut. Only original
coefficient input is a premise; all independent lower tuples are bound. -/
theorem source_magnitude_cut (C N : PTm n) (hInput : Γ ⊢[PRAAx] GaussianBalancedRadiusSyntax.input C N) : Γ ⊢[PRAAx] sourceCut C N := by
  have hk := GaussianDominantPlateau.winner_bounds C N hInput
  exact geometric_magnitude_cut N (GaussianDominantPlateau.winner C N) (radialLower C N) (radialUpper C N)
    (GaussianOffDominantTerms.selectedReference C N) (.andE₁ hk) (.andE₂ hk)
    (GaussianOffDominantTerms.lower_length _ _ _ _) (GaussianOffDominantTerms.upper_length _ _ _ _)
    (GaussianOffDominantSum.lower_bounds C N (radialPoint C N) hInput (radial_within C N))
    (GaussianOffDominantSum.upper_bounds C N (radialPoint C N) hInput (radial_within C N))

theorem source_sample_bound (C N H : PTm n) (hInput : Γ ⊢[PRAAx] GaussianBalancedRadiusSyntax.input C N) : Γ ⊢[PRAAx]
    le (GaussianRationalNormClearing.nine*(sourceTotal C N H*sourceTotal C N H))
      (GaussianDominantSyntax.four*GaussianOffDominantWeights.C N*GaussianOffDominantWeights.C N*H*H*
        normSq (GaussianRationalNormalization.queryNumerator (radialLower C N) (radialUpper C N) (GaussianOffDominantTerms.selectedReference C N))) := by
  have hk := GaussianDominantPlateau.winner_bounds C N hInput
  exact sampled_magnitude_bound N (GaussianDominantPlateau.winner C N) (radialLower C N) (radialUpper C N)
    (GaussianOffDominantTerms.selectedReference C N) H (.andE₁ hk) (.andE₂ hk)
    (GaussianOffDominantTerms.lower_length _ _ _ _) (GaussianOffDominantTerms.upper_length _ _ _ _)
    (GaussianOffDominantSum.lower_bounds C N (radialPoint C N) hInput (radial_within C N))
    (GaussianOffDominantSum.upper_bounds C N (radialPoint C N) hInput (radial_within C N))

def sampleDen (N S T ref H : PTm n) : PTm n :=
  (GaussianOffDominantWeights.C N*H)*GaussianRationalNormalization.commonD S T ref
def samplePoint (N k S T ref H : PTm n) : PTm n := GaussianDominantPairAlgebra.radiusPoint
  (rootTotal N k S T ref H) (sampleDen N S T ref H)
def lowerPoint (s : Side) (N k S T ref H i : PTm n) : PTm n := GaussianDominantPairAlgebra.radiusPoint
  (rootTerm s N k S T ref H i) (sampleDen N S T ref H)
def upperPoint (s : Side) (N k S T ref H i : PTm n) : PTm n := GaussianDominantPairAlgebra.radiusPoint
  (succ (rootTerm s N k S T ref H i)) (sampleDen N S T ref H)
ipra_subst sampleDen
ipra_subst samplePoint
ipra_subst lowerPoint
ipra_subst upperPoint

theorem sample_den_positive (N S T ref H : PTm n) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    le one (sampleDen N S T ref H) :=
  GaussianRationalHorner.positive_product _ _
    (GaussianRationalHorner.positive_product _ _ (GaussianOffDominantWeights.C_positive N) hH)
    (GaussianRationalNormalization.commonD_positive S T ref)

theorem normalized_sample_bound (N k S T ref H : PTm n)
    (hk : Γ ⊢[PRAAx] le one k) (hkN : Γ ⊢[PRAAx] le k N)
    (hSL : Γ ⊢[PRAAx] length S ≐ GaussianGeometricSumBound.count .source N k)
    (hTL : Γ ⊢[PRAAx] length T ≐ GaussianGeometricSumBound.count .target N k)
    (hLower : Γ ⊢[PRAAx] GaussianGeometricSumBound.entryBounds .source N k S T ref)
    (hUpper : Γ ⊢[PRAAx] GaussianGeometricSumBound.entryBounds .target N k S T ref)
    (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (GaussianRationalNormClearing.weightedNorm GaussianRationalNormClearing.nine (samplePoint N k S T ref H))
      (GaussianRationalNormClearing.weightedNorm GaussianDominantSyntax.four ref) := by
  have hD := GaussianRationalNormalization.commonD_positive (Γ := Γ) S T ref
  have hCH := GaussianRationalHorner.positive_product _ _ (GaussianOffDominantWeights.C_positive (Γ := Γ) N) hH
  apply GaussianRationalNormClearing.scaled_bound _ _ _ _ (GaussianOffDominantWeights.C N*H)
    (GaussianRationalNormalization.commonD S T ref) hCH hD
    (GaussianDominantPairAlgebra.radius_represents _ _ (sample_den_positive N S T ref H hH))
    (GaussianRationalNormalization.query_clearing S T ref)
  exact le_congr (congrMul (.eqRefl _) (GaussianDominantPairAlgebra.radius_numerator_norm _)).eqSymm
    (by ipra_ring) (sampled_magnitude_bound N k S T ref H hk hkN hSL hTL hLower hUpper)

theorem lower_point_bound (s : Side) (N k S T ref H i : PTm n)
    (hH : Γ ⊢[PRAAx] le one H) (hi : Γ ⊢[PRAAx] lt i (length (original s S T))) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (GaussianRationalMetric.qnormSq (lowerPoint s N k S T ref H i))
      (GaussianRationalMetric.qnormSq (entry (original s S T) i)) := by
  let CD := GaussianOffDominantWeights.C N*GaussianRationalNormalization.commonD S T ref
  have hCD := GaussianRationalHorner.positive_product _ _ (GaussianOffDominantWeights.C_positive (Γ := Γ) N)
    (GaussianRationalNormalization.commonD_positive (Γ := Γ) S T ref)
  have hE := sample_den_positive (Γ := Γ) N S T ref H hH
  have bound := root_lower (Γ := Γ) s N k S T ref H i
  have point := GaussianRationalMetric.qnormSq_represents (Γ := Γ)
    (GaussianDominantPairAlgebra.radiusPoint (rootTerm s N k S T ref H i) (sampleDen N S T ref H))
    (radiusNumerator (rootTerm s N k S T ref H i)) (sampleDen N S T ref H) hE
    (GaussianDominantPairAlgebra.radius_represents _ _ hE)
  have target := GaussianRationalMetric.qnormSq_represents (Γ := Γ) _ _ _ hCD
    (GaussianGeometricSumBound.scaled_entry_represents s N k S T ref i hi)
  apply GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _
    (GaussianRationalHorner.positive_product _ _ hE hE)
    (GaussianRationalHorner.positive_product _ _ hCD hCD) point target
  exact le_congr ((congrMul (GaussianDominantPairAlgebra.radius_numerator_norm _).eqSymm (.eqRefl _)).eqTrans
      (by simp only [CD] <;> ipra_ring))
    (by simp only [sampleDen,CD]; ipra_ring) (mul_le_mul_right (CD*CD) bound)

theorem upper_point_bound (s : Side) (N k S T ref H i : PTm n)
    (hH : Γ ⊢[PRAAx] le one H) (hi : Γ ⊢[PRAAx] lt i (length (original s S T))) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (GaussianRationalMetric.qnormSq (entry (original s S T) i))
      (GaussianRationalMetric.qnormSq (upperPoint s N k S T ref H i)) := by
  let CD := GaussianOffDominantWeights.C N*GaussianRationalNormalization.commonD S T ref
  have hCD := GaussianRationalHorner.positive_product _ _ (GaussianOffDominantWeights.C_positive (Γ := Γ) N)
    (GaussianRationalNormalization.commonD_positive (Γ := Γ) S T ref)
  have hE := sample_den_positive (Γ := Γ) N S T ref H hH
  have bound := le_of_lt (root_upper (Γ := Γ) s N k S T ref H i)
  have point := GaussianRationalMetric.qnormSq_represents (Γ := Γ)
    (GaussianDominantPairAlgebra.radiusPoint (succ (rootTerm s N k S T ref H i)) (sampleDen N S T ref H))
    (radiusNumerator (succ (rootTerm s N k S T ref H i))) (sampleDen N S T ref H) hE
    (GaussianDominantPairAlgebra.radius_represents _ _ hE)
  have target := GaussianRationalMetric.qnormSq_represents (Γ := Γ) _ _ _ hCD
    (GaussianGeometricSumBound.scaled_entry_represents s N k S T ref i hi)
  apply GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _
    (GaussianRationalHorner.positive_product _ _ hCD hCD)
    (GaussianRationalHorner.positive_product _ _ hE hE) target point
  exact le_congr (by simp only [sampleDen,CD]; ipra_ring)
    (congrMul (GaussianDominantPairAlgebra.radius_numerator_norm _).eqSymm (.eqRefl _)) (mul_le_mul_right (CD*CD) bound)

def upperBody (s : Side) : PTm 2 := succ (candidateBody s)
def candidateCount (N k : PTm n) : PTm n :=
  GaussianGeometricSumBound.count .source N k+GaussianGeometricSumBound.count .target N k
def upperTotal (N k S T ref H : PTm n) : PTm n :=
  naturalSum (upperBody .source) (GaussianGeometricSumBound.count .source N k)
    (candidateData N k (rootList .source N k S T ref H) (rootList .target N k S T ref H))+
  naturalSum (upperBody .target) (GaussianGeometricSumBound.count .target N k)
    (candidateData N k (rootList .source N k S T ref H) (rootList .target N k S T ref H))
def lowerValue (N k S T ref H : PTm n) : PTm n :=
  GaussianEuclideanDistanceName.fraction (rootTotal N k S T ref H) (sampleDen N S T ref H)
def upperValue (N k S T ref H : PTm n) : PTm n :=
  GaussianEuclideanDistanceName.fraction (upperTotal N k S T ref H) (sampleDen N S T ref H)
def precision (N k m : PTm n) : PTm n := succ (candidateCount N k)*GaussianEuclideanPointDistance.unit m
ipra_subst candidateCount
ipra_subst upperTotal
ipra_subst lowerValue
ipra_subst upperValue
ipra_subst precision

theorem natural_sum_successors (f : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx]
    naturalSum (succ f) N x ≐ naturalSum f N x+N := by
  have bodies : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift N) ⟶
      inst2 (succ f) (var 0) (Syn.shift x) ≐ inst2 (LeanProofs.IPRA.addBody f one) (var 0) (Syn.shift x)) := by
    refine .allI (.impI ?_)
    simpa only [inst2,LeanProofs.IPRA.addBody,PTm.subst_succ,PTm.subst_add,one,PTm.subst_zero] using succ_eq_add_one _
  exact (LeanProofs.IPRA.sum_congr_bounded _ _ x x N bodies).eqTrans
    ((LeanProofs.IPRA.sum_add f one N x).eqTrans
      (congrAdd (.eqRefl _) (LeanProofs.IPRA.Foundations.FiniteFiberGrouping.sum_units N x)))

theorem upper_total_value (N k S T ref H : PTm n) : Γ ⊢[PRAAx]
    upperTotal N k S T ref H ≐ rootTotal N k S T ref H+candidateCount N k := by
  exact (congrAdd (natural_sum_successors (candidateBody .source) _ _)
    (natural_sum_successors (candidateBody .target) _ _)).eqTrans (by unfold rootTotal candidateTotal candidateCount; ipra_ring)

theorem fraction_gap (A B E : PTm n) (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx]
    RationalArithmetic.add (GaussianEuclideanDistanceName.fraction (A+B) E)
      (RationalArithmetic.negative (GaussianEuclideanDistanceName.fraction A E)) ≐ GaussianEuclideanDistanceName.fraction B E := by
  have value := GaussianRationalHorner.scalar_add_same _ _ _ _ _ hE
    (GaussianEuclideanDistanceName.fraction_represents (Γ := Γ) (A+B) E hE)
    (RationalRepresentations.represents_negative _ _ _ (GaussianEuclideanDistanceName.fraction_represents (Γ := Γ) A E hE))
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.add_guard _ _)
    (RationalNormalForm.normalize_well_formed _ _ hE) value (GaussianEuclideanDistanceName.fraction_represents _ _ hE) hE hE
  ipra_lc

theorem total_bracket_width (N k S T ref H : PTm n) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    RationalArithmetic.add (upperValue N k S T ref H) (RationalArithmetic.negative (lowerValue N k S T ref H)) ≐
      GaussianEuclideanDistanceName.fraction (candidateCount N k) (sampleDen N S T ref H) := by
  have e : Γ ⊢[PRAAx] RationalArithmetic.add (upperValue N k S T ref H)
      (RationalArithmetic.negative (lowerValue N k S T ref H)) ≐
      RationalArithmetic.add (GaussianEuclideanDistanceName.fraction (rootTotal N k S T ref H+candidateCount N k) (sampleDen N S T ref H))
        (RationalArithmetic.negative (lowerValue N k S T ref H)) := RationalAlgebra.add_congr
    (RationalNonnegativePowers.fraction_congr (upper_total_value N k S T ref H) (.eqRefl _)) (.eqRefl _)
  exact e.eqTrans (fraction_gap _ _ _ (sample_den_positive N S T ref H hH))

theorem precision_positive (N k m : PTm n) : Γ ⊢[PRAAx] le one (precision N k m) :=
  GaussianRationalHorner.positive_product _ _ (zero_lt_succ _) (GaussianEuclideanPointDistance.unit_positive m)

theorem sample_den_ge (N S T ref H : PTm n) : Γ ⊢[PRAAx] le H (sampleDen N S T ref H) := by
  have c := mul_le_mul_right H (GaussianOffDominantWeights.C_positive (Γ := Γ) N)
  have d := mul_le_mul_right (GaussianOffDominantWeights.C N*H)
    (GaussianRationalNormalization.commonD_positive (Γ := Γ) S T ref)
  have first : Γ ⊢[PRAAx] le H (GaussianOffDominantWeights.C N*H) := le_congr (one_mul H) (.eqRefl _) c
  have second : Γ ⊢[PRAAx] le (GaussianOffDominantWeights.C N*H) (sampleDen N S T ref H) :=
    le_congr (one_mul _) (mul_comm _ _) d
  exact le_trans first second

theorem cofinal_width (N k S T ref m : PTm n) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE
      (RationalArithmetic.add (upperValue N k S T ref (precision N k m))
        (RationalArithmetic.negative (lowerValue N k S T ref (precision N k m))))
      (GaussianEuclideanDistanceName.fraction one (GaussianEuclideanPointDistance.unit m)) := by
  apply RationalArgmin.rationalLE_congr (total_bracket_width N k S T ref _ (precision_positive N k m)).eqSymm (.eqRefl _)
  apply GaussianEuclideanDistanceName.fraction_order _ _ _ _ (sample_den_positive _ _ _ _ _ (precision_positive N k m))
    (GaussianEuclideanPointDistance.unit_positive m)
  exact le_trans (le_congr (mul_comm _ _) (.eqRefl _) (mul_le_mul_right (GaussianEuclideanPointDistance.unit m) (le_succ_self (candidateCount N k))))
    (le_congr (.eqRefl _) (one_mul _).eqSymm (sample_den_ge N S T ref (precision N k m)))

def sourceDen (C N H : PTm n) : PTm n := sampleDen N (radialLower C N) (radialUpper C N)
  (GaussianOffDominantTerms.selectedReference C N) H
def sourcePoint (C N H : PTm n) : PTm n := samplePoint N (GaussianDominantPlateau.winner C N)
  (radialLower C N) (radialUpper C N) (GaussianOffDominantTerms.selectedReference C N) H
def sourceLower (C N H : PTm n) : PTm n := lowerValue N (GaussianDominantPlateau.winner C N)
  (radialLower C N) (radialUpper C N) (GaussianOffDominantTerms.selectedReference C N) H
def sourceUpper (C N H : PTm n) : PTm n := upperValue N (GaussianDominantPlateau.winner C N)
  (radialLower C N) (radialUpper C N) (GaussianOffDominantTerms.selectedReference C N) H
def sourcePrecision (C N m : PTm n) : PTm n := precision N (GaussianDominantPlateau.winner C N) m
ipra_subst sourceDen
ipra_subst sourcePoint
ipra_subst sourceLower
ipra_subst sourceUpper
ipra_subst sourcePrecision

theorem source_normalized_bound (C N H : PTm n) (hInput : Γ ⊢[PRAAx] GaussianBalancedRadiusSyntax.input C N)
    (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (GaussianRationalNormClearing.weightedNorm GaussianRationalNormClearing.nine (sourcePoint C N H))
      (RationalArithmetic.multiply (GaussianEuclideanDistanceName.fraction GaussianDominantSyntax.four one) (GaussianOffDominantSum.selectedScore C N)) := by
  have hk := GaussianDominantPlateau.winner_bounds C N hInput
  have bound := normalized_sample_bound N (GaussianDominantPlateau.winner C N) (radialLower C N) (radialUpper C N)
    (GaussianOffDominantTerms.selectedReference C N) H (.andE₁ hk) (.andE₂ hk)
    (GaussianOffDominantTerms.lower_length _ _ _ _) (GaussianOffDominantTerms.upper_length _ _ _ _)
    (GaussianOffDominantSum.lower_bounds C N (radialPoint C N) hInput (radial_within C N))
    (GaussianOffDominantSum.upper_bounds C N (radialPoint C N) hInput (radial_within C N)) hH
  exact RationalArgmin.rationalLE_congr (.eqRefl _)
    (RationalAlgebra.multiply_congr (.eqRefl _) (GaussianOffDominantTerms.selected_reference_norm C N)) bound

theorem source_cofinal_width (C N m : PTm n) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE
      (RationalArithmetic.add (sourceUpper C N (sourcePrecision C N m))
        (RationalArithmetic.negative (sourceLower C N (sourcePrecision C N m))))
      (GaussianEuclideanDistanceName.fraction one (GaussianEuclideanPointDistance.unit m)) :=
  cofinal_width N (GaussianDominantPlateau.winner C N) (radialLower C N) (radialUpper C N)
    (GaussianOffDominantTerms.selectedReference C N) m

theorem original_monic_magnitude_cut (C N z : PTm n)
    (hInput : Γ ⊢[PRAAx] GaussianTranslatedBalancedRadius.inputContract C N)
    (hPositive : Γ ⊢[PRAAx] le one (GaussianTranslatedBalancedRadius.residual C z)) : Γ ⊢[PRAAx]
    sourceCut (GaussianRationalTranslation.translated C N z) N :=
  source_magnitude_cut _ _ (GaussianTranslatedDominantPlateau.positive_input C N z hInput hPositive)

theorem original_nonmonic_magnitude_cut (C N z : PTm n)
    (hInput : Γ ⊢[PRAAx] GaussianBalancedRadius.inputContract C N)
    (hPositive : Γ ⊢[PRAAx] le one (GaussianTranslatedBalancedRadius.residual C z)) : Γ ⊢[PRAAx]
    sourceCut (GaussianRationalTranslation.translated C N z) N :=
  source_magnitude_cut _ _ (GaussianBalancedRadius.positive_input _ _
    (GaussianTranslatedNonconstant.translated_radius_input C N z hInput)
    (le_congr (.eqRefl _) (GaussianTranslatedBalancedRadius.residual_identity C N z).eqSymm hPositive))

/-- Actual PR3 source sampler: lower/upper numerator lists, their scalar
sum brackets, normalized positive-axis total, common denominator, reference. -/
def output (C N m : PTm n) : PTm n := pairT (sourceRoot .source C N (sourcePrecision C N m))
  (pairT (sourceRoot .target C N (sourcePrecision C N m))
    (pairT (sourceLower C N (sourcePrecision C N m))
      (pairT (sourceUpper C N (sourcePrecision C N m))
        (pairT (sourcePoint C N (sourcePrecision C N m))
          (pairT (sourceDen C N (sourcePrecision C N m)) (GaussianOffDominantTerms.selectedReference C N))))))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (C N m : PTm n) : PTm n := ap3 outputF C N m
ipra_subst output
ipra_subst run

theorem program_at (C N m : PTm n) : Γ ⊢[PRAAx] run C N m ≐ output C N m := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![C,N,m]
theorem returned_lower_roots (C N m : PTm n) : Γ ⊢[PRAAx]
    fstT (run C N m) ≐ sourceRoot .source C N (sourcePrecision C N m) :=
  (program_at C N m).fstE
theorem returned_upper_roots (C N m : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run C N m)) ≐ sourceRoot .target C N (sourcePrecision C N m) :=
  (congrFst (congrSnd (program_at C N m))).eqTrans (snd_pair _ _).fstE
theorem returned_lower (C N m : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run C N m))) ≐ sourceLower C N (sourcePrecision C N m) :=
  (congrFst (congrSnd (congrSnd (program_at C N m)))).eqTrans
    ((congrFst (congrSnd (snd_pair _ _))).eqTrans (snd_pair _ _).fstE)
theorem returned_upper (C N m : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (sndT (run C N m)))) ≐ sourceUpper C N (sourcePrecision C N m) := by
  exact (congrFst (congrSnd (congrSnd (congrSnd (program_at C N m))))).eqTrans
    ((congrFst (congrSnd (congrSnd (snd_pair _ _)))).eqTrans
      ((congrFst (congrSnd (snd_pair _ _))).eqTrans (snd_pair _ _).fstE))
theorem returned_point (C N m : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (sndT (sndT (run C N m))))) ≐ sourcePoint C N (sourcePrecision C N m) := by
  have t1 := (program_at (Γ := Γ) C N m).sndE
  have t2 := t1.sndE
  have t3 := t2.sndE
  have t4 := t3.sndE
  exact t4.fstE

theorem returned_denominator (C N m : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (sndT (sndT (sndT (run C N m)))))) ≐ sourceDen C N (sourcePrecision C N m) := by
  have t1 := (program_at (Γ := Γ) C N m).sndE
  have t2 := t1.sndE
  have t3 := t2.sndE
  have t4 := t3.sndE
  have t5 := t4.sndE
  exact t5.fstE
theorem returned_reference (C N m : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (sndT (sndT (sndT (run C N m)))))) ≐ GaussianOffDominantTerms.selectedReference C N := by
  have t1 := (program_at (Γ := Γ) C N m).sndE
  have t2 := t1.sndE
  have t3 := t2.sndE
  have t4 := t3.sndE
  have t5 := t4.sndE
  exact t5.sndE

theorem returned_bound (C N m : PTm n) (hInput : Γ ⊢[PRAAx] GaussianBalancedRadiusSyntax.input C N) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE
      (GaussianRationalNormClearing.weightedNorm GaussianRationalNormClearing.nine (fstT (sndT (sndT (sndT (sndT (run C N m)))))))
      (RationalArithmetic.multiply (GaussianEuclideanDistanceName.fraction GaussianDominantSyntax.four one) (GaussianOffDominantSum.selectedScore C N)) :=
  RationalArgmin.rationalLE_congr (RationalAlgebra.multiply_congr (.eqRefl _)
    (GaussianRationalProductWitness.qnormSq_congr (returned_point C N m))).eqSymm (.eqRefl _)
    (source_normalized_bound C N _ hInput (precision_positive _ _ _))

theorem returned_width (C N m : PTm n) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE
      (RationalArithmetic.add (fstT (sndT (sndT (sndT (run C N m)))))
        (RationalArithmetic.negative (fstT (sndT (sndT (run C N m))))))
      (GaussianEuclideanDistanceName.fraction one (GaussianEuclideanPointDistance.unit m)) :=
  RationalArgmin.rationalLE_congr (RationalAlgebra.add_congr (returned_upper C N m)
    (RationalAlgebra.negative_congr (returned_lower C N m))).eqSymm (.eqRefl _) (source_cofinal_width C N m)

theorem actual_source_magnitude_cut_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianBalancedRadiusSyntax.input (var 0) (var 1) ⟶ sourceCut (var 0) (var 1)) :=
  closeUniv 2 (.impI (source_magnitude_cut _ _ Prf.hyp0))

theorem actual_source_sample_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianBalancedRadiusSyntax.input (var 0) (var 1) ⟶ le one (var 2) ⟶
      RationalArgmin.rationalLE (GaussianRationalNormClearing.weightedNorm GaussianRationalNormClearing.nine (sourcePoint (var 0) (var 1) (var 2)))
        (RationalArithmetic.multiply (GaussianEuclideanDistanceName.fraction GaussianDominantSyntax.four one) (GaussianOffDominantSum.selectedScore (var 0) (var 1)))) :=
  closeUniv 3 (.impI (.impI (source_normalized_bound _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_source_cofinal_width_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (RationalArgmin.rationalLE
      (RationalArithmetic.add (sourceUpper (var 0) (var 1) (sourcePrecision (var 0) (var 1) (var 2)))
        (RationalArithmetic.negative (sourceLower (var 0) (var 1) (sourcePrecision (var 0) (var 1) (var 2)))))
      (GaussianEuclideanDistanceName.fraction one (GaussianEuclideanPointDistance.unit (var 2)))) :=
  closeUniv 3 (source_cofinal_width _ _ _)

theorem actual_individual_brackets_closed (s : Side) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le one (var 5) ⟶ lt (var 6) (length (original s (var 2) (var 3))) ⟶
      (RationalArgmin.rationalLE (GaussianRationalMetric.qnormSq (lowerPoint s (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)))
        (GaussianRationalMetric.qnormSq (entry (original s (var 2) (var 3)) (var 6))) ⋏
      RationalArgmin.rationalLE (GaussianRationalMetric.qnormSq (entry (original s (var 2) (var 3)) (var 6)))
        (GaussianRationalMetric.qnormSq (upperPoint s (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))))) :=
  closeUniv 7 (.impI (.impI (.andI (lower_point_bound _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)
    (upper_point_bound _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0))))

theorem actual_radial_term_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianRationalMetric.qnormSq (GaussianOffDominantTerms.term (var 0) (var 1) (radialPoint (var 0) (var 1)) (var 2)) ≐
      RationalArithmetic.multiply (GaussianRationalMetric.qnormSq (GaussianBalancedRadiusSyntax.coefficient (var 0) (var 1) (var 2)))
        (RationalNonnegativePowers.power (GaussianOffDominantTerms.radiusNumerator (var 0) (var 1))
          (GaussianOffDominantTerms.radiusDenominator (var 0) (var 1)) (two*var 2))) :=
  closeUniv 3 (radial_term_norm _ _ _)

theorem original_monic_sum_cut_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianTranslatedBalancedRadius.inputContract (var 0) (var 1) ⟶
      le one (GaussianTranslatedBalancedRadius.residual (var 0) (var 2)) ⟶
      sourceCut (GaussianRationalTranslation.translated (var 0) (var 1) (var 2)) (var 1)) :=
  closeUniv 3 (.impI (.impI (original_monic_magnitude_cut _ _ _ Prf.hyp1 Prf.hyp0)))

theorem original_nonmonic_sum_cut_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianBalancedRadius.inputContract (var 0) (var 1) ⟶
      le one (GaussianTranslatedBalancedRadius.residual (var 0) (var 2)) ⟶
      sourceCut (GaussianRationalTranslation.translated (var 0) (var 1) (var 2)) (var 1)) :=
  closeUniv 3 (.impI (.impI (original_nonmonic_magnitude_cut _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_magnitude_sampler_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)

theorem actual_returned_magnitude_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianBalancedRadiusSyntax.input (var 0) (var 1) ⟶
      RationalArgmin.rationalLE
        (GaussianRationalNormClearing.weightedNorm GaussianRationalNormClearing.nine (fstT (sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2))))))))
        (RationalArithmetic.multiply (GaussianEuclideanDistanceName.fraction GaussianDominantSyntax.four one) (GaussianOffDominantSum.selectedScore (var 0) (var 1)))) :=
  closeUniv 3 (.impI (returned_bound _ _ _ Prf.hyp0))

theorem actual_returned_width_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (RationalArgmin.rationalLE
      (RationalArithmetic.add (fstT (sndT (sndT (sndT (run (var 0) (var 1) (var 2))))))
        (RationalArithmetic.negative (fstT (sndT (sndT (run (var 0) (var 1) (var 2)))))))
      (GaussianEuclideanDistanceName.fraction one (GaussianEuclideanPointDistance.unit (var 2)))) :=
  closeUniv 3 (returned_width _ _ _)

end LeanProofs.IPRA.Analysis.GaussianOffDominantMagnitudeSum
