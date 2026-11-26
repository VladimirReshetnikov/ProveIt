import IPRADerivations.Analysis.RationalArithmetic.RationalPhiFeatures
import IPRADerivations.Analysis.RationalArithmetic.RationalSubspaceCoverSearch
import IPRADerivations.Analysis.RationalArithmetic.RationalCurvePointsGaussianEmbedding
import IPRADerivations.Foundations.FiniteCoverAssignment
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual Phi_s feature tuples and first-cover point groups

The source tuple has exactly the coordinates (1,x,...,x^s,y). The global
finite cover decision runs on that actual tuple. Original membership tests
assign each original point to its first covering span. The groups preserve
raw point codes, distinctness, curve equations and the original Phi span
memberships. Their actual cardinal sum is the original list length.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalPhiCoverAssignment

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalPhiFeatures (dimension features)
open RationalRowSpanGaussianEmbedding (hasCoefficients)
open RationalSuperellipticNormDegree (pointPowers point_power_at)
open RationalCurvePointsGaussianEmbedding (distinct distinctFrom distinct_at)
open RationalArgmin (rationalEq rationalEq_congr)
open GaussianRationalFiberGrouping (abscissa ordinate)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open LeanProofs.IPRA.Foundations.FiniteCoverAssignment
  (hasCover groupBounds group_length group_lookup index_bound indices_increasing group_test)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def pointFeature (s v : PTm n) : PTm n := features s (fstT v) (sndT v)
def featureBody : PTm 2 := pointFeature (fstT (var 1)) (entry (sndT (var 1)) (var 0))
def featureList (s P : PTm n) : PTm n := sequence featureBody (length P) (pairT s P)
def candidate (s D g v : PTm n) : PTm n := RationalOriginalSpanMembership.test
  (entry D g) (length (entry D g)) (dimension s) (pointFeature s v)
def data (s D : PTm n) : PTm n := pairT s D
def testBody : PTm 3 := eqb (candidate (fstT (var 2)) (sndT (var 2)) (var 0) (var 1)) one
def cover (s P D : PTm n) : Fm PTm n := RationalFiniteSpanCover.covered (featureList s P) D (dimension s)
def members (A R s P : PTm n) : Fm PTm n := .all (lt (var 0) (length (Syn.shift P)) ⟶
  hasCoefficients (Syn.shift A) (Syn.shift R) (dimension (Syn.shift s)) (pointFeature (Syn.shift s) (entry (Syn.shift P) (var 0))))
def group (s P D g : PTm n) : PTm n := Foundations.FiniteCoverAssignment.group testBody P (length D) (data s D) g

@[simp] theorem subst_pointFeature {q : ℕ} (σ : Fin n → PTm q) (s v : PTm n) :
    Syn.subst σ (pointFeature s v) = pointFeature (Syn.subst σ s) (Syn.subst σ v) := by simp [pointFeature]
@[simp] theorem subst_featureList {q : ℕ} (σ : Fin n → PTm q) (s P : PTm n) :
    Syn.subst σ (featureList s P) = featureList (Syn.subst σ s) (Syn.subst σ P) := by simp [featureList]
@[simp] theorem subst_candidate {q : ℕ} (σ : Fin n → PTm q) (s D g v : PTm n) :
    Syn.subst σ (candidate s D g v) = candidate (Syn.subst σ s) (Syn.subst σ D) (Syn.subst σ g) (Syn.subst σ v) := by simp [candidate]
@[simp] theorem subst_data {q : ℕ} (σ : Fin n → PTm q) (s D : PTm n) :
    Syn.subst σ (data s D) = data (Syn.subst σ s) (Syn.subst σ D) := by simp [data]
@[simp] theorem subst_cover {q : ℕ} (σ : Fin n → PTm q) (s P D : PTm n) :
    (cover s P D).subst σ = cover (Syn.subst σ s) (Syn.subst σ P) (Syn.subst σ D) := by simp [cover]
@[simp] theorem subst_members {q : ℕ} (σ : Fin n → PTm q) (A R s P : PTm n) :
    (members A R s P).subst σ = members (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ s) (Syn.subst σ P) := by simp [members,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_group {q : ℕ} (σ : Fin n → PTm q) (s P D g : PTm n) :
    Syn.subst σ (group s P D g) = group (Syn.subst σ s) (Syn.subst σ P) (Syn.subst σ D) (Syn.subst σ g) := by simp [group]

private theorem point_feature_congr {s t v w : PTm n} (hs : Γ ⊢[PRAAx] s ≐ t) (hv : Γ ⊢[PRAAx] v ≐ w) : Γ ⊢[PRAAx]
    pointFeature s v ≐ pointFeature t w := by
  ipra_congr (pointFeature (var 0) (var 1) : PTm 2) with [hs, hv]
theorem feature_body_at (s P i : PTm n) : Γ ⊢[PRAAx] inst2 featureBody i (pairT s P) ≐ pointFeature s (entry P i) := by
  simp only [featureBody,inst2,subst_pointFeature,Foundations.MasterCertificate.subst_entry,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact point_feature_congr (fst_pair _ _) (entry_congr (snd_pair _ _) (.eqRefl _))
theorem feature_list_length (s P : PTm n) : Γ ⊢[PRAAx] length (featureList s P) ≐ length P := sequence_length _ _ _
theorem feature_list_lookup (s P i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length P)) : Γ ⊢[PRAAx]
    entry (featureList s P) i ≐ pointFeature s (entry P i) := (sequence_decode featureBody (x := pairT s P) hi).eqTrans (feature_body_at _ _ _)

private theorem candidate_congr {s t D E : PTm n} (g v : PTm n) (hs : Γ ⊢[PRAAx] s ≐ t) (hD : Γ ⊢[PRAAx] D ≐ E) : Γ ⊢[PRAAx]
    candidate s D g v ≐ candidate t E g v := by
  ipra_congr (candidate (var 0) (var 1) (var 2) (var 3) : PTm 4) with [hs, hD, .eqRefl g, .eqRefl v]
theorem test_body_at (s D g v : PTm n) : Γ ⊢[PRAAx] inst3 testBody g v (data s D) ≐ eqb (candidate s D g v) one := by
  simp only [testBody,inst3,subst_eqb,subst_candidate,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]
  exact Foundations.FiniteFiberGrouping.eqb_congr (candidate_congr g v (fst_pair _ _) (snd_pair _ _)) (.eqRefl one)
theorem candidate_complete (s D g v : PTm n) (h : Γ ⊢[PRAAx] hasCoefficients (entry D g) (length (entry D g)) (dimension s) (pointFeature s v)) : Γ ⊢[PRAAx]
    inst3 testBody g v (data s D) ≐ one := (test_body_at s D g v).eqTrans (eqb_of_eq (RationalOriginalSpanMembership.test_complete _ _ _ _ h))
theorem candidate_sound (s D g v : PTm n) (h : Γ ⊢[PRAAx] neg (inst3 testBody g v (data s D) ≐ zero)) : Γ ⊢[PRAAx]
    hasCoefficients (entry D g) (length (entry D g)) (dimension s) (pointFeature s v) := by
  have accepted := Foundations.FiniteFiberGrouping.equality_of_nonzero_eqb
    (.impI (.impE h.wk ((test_body_at s D g v).wk.eqTrans Prf.hyp0)))
  exact (RationalOriginalSpanMembership.test_iff _ _ _ _).iffMp accepted

theorem covered_at (s P D i : PTm n) (h : Γ ⊢[PRAAx] cover s P D) (hi : Γ ⊢[PRAAx] lt i (length P)) : Γ ⊢[PRAAx]
    RationalFiniteSpanCover.coveredAt D (dimension s) (pointFeature s (entry P i)) := by
  have old := RationalFiniteSpanCover.covered_at (featureList s P) D (dimension s) i h
    (lt_congr (.eqRefl _) (feature_list_length s P).eqSymm hi)
  let φ := RationalFiniteSpanCover.coveredAt (Syn.shift D) (dimension (Syn.shift s)) (var 0)
  have start : Γ ⊢[PRAAx] φ.subst (Syn.inst (entry (featureList s P) i)) := by
    simpa only [φ,RationalFiniteSpanCover.subst_coveredAt,RationalPhiFeatures.subst_dimension,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using old
  simpa only [φ,RationalFiniteSpanCover.subst_coveredAt,RationalPhiFeatures.subst_dimension,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
    Prf.eqSubst1 φ (feature_list_lookup s P i hi) start

theorem covered_point_reflected (s D v : PTm n) (h : Γ ⊢[PRAAx] RationalFiniteSpanCover.coveredAt D (dimension s) (pointFeature s v)) : Γ ⊢[PRAAx]
    hasCover testBody (length D) v (data s D) := by
  refine .exE h ?_
  let Δ := (lt (var 0) (length (Syn.shift D)) ⋏ hasCoefficients (entry (Syn.shift D) (var 0))
    (length (entry (Syn.shift D) (var 0))) (dimension (Syn.shift s)) (pointFeature (Syn.shift s) (Syn.shift v))) :: Γ.map Fm.shift
  have hit := candidate_complete (Γ := Δ) (Syn.shift s) (Syn.shift D) (var 0) (Syn.shift v) (.andE₂ Prf.hyp0)
  have out : Δ ⊢[PRAAx] hasCover testBody (length (Syn.shift D)) (Syn.shift v) (data (Syn.shift s) (Syn.shift D)) := by
    refine .exI (var 0) ?_
    have nz : Δ ⊢[PRAAx] neg (inst3 testBody (var 0) (Syn.shift v) (data (Syn.shift s) (Syn.shift D)) ≐ zero) :=
      .impI (succ_ne_zero (hit.wk.eqSymm.eqTrans Prf.hyp0))
    simpa [hasCover] using Prf.andI (.andE₁ (Prf.hyp0 : Δ ⊢[PRAAx] _)) nz
  simpa [Δ,Fm.shift,Syn.shift] using out

theorem generic_cover (s P D : PTm n) (h : Γ ⊢[PRAAx] cover s P D) : Γ ⊢[PRAAx]
    Foundations.FiniteCoverAssignment.cover testBody P (length D) (data s D) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] cover (Syn.shift s) (Syn.shift P) (Syn.shift D) := by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_data,Foundations.SequenceComposition.subst_length] using
    covered_point_reflected (Syn.shift s) (Syn.shift D) (entry (Syn.shift P) (var 0))
      (covered_at _ _ _ _ hs.wk (Prf.hyp0 : lt (var 0) (length (Syn.shift P)) :: Γ.map Fm.shift ⊢[PRAAx] _))

theorem group_members (s P D g : PTm n) (h : Γ ⊢[PRAAx] cover s P D) : Γ ⊢[PRAAx]
    members (entry D g) (length (entry D g)) s (group s P D g) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] cover (Syn.shift s) (Syn.shift P) (Syn.shift D) := by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  let G := group (Syn.shift s) (Syn.shift P) (Syn.shift D) (Syn.shift g)
  let Δ := lt (var 0) (length G) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (Foundations.FiniteCoverAssignment.groupSize testBody (Syn.shift P) (length (Syn.shift D)) (data (Syn.shift s) (Syn.shift D)) (Syn.shift g)) :=
    lt_congr (.eqRefl _) (group_length _ _ _ _ _) Prf.hyp0
  have hit := group_test testBody (Syn.shift P) (length (Syn.shift D)) (data (Syn.shift s) (Syn.shift D)) (Syn.shift g) (var 0)
    (generic_cover _ _ _ hs.wk) hi
  simpa only [Δ,G,Syn.shift,subst_group,Foundations.MasterCertificate.subst_entry,Foundations.SequenceComposition.subst_length] using
    candidate_sound (Syn.shift s) (Syn.shift D) (Syn.shift g) (entry G (var 0)) hit

private theorem group_power_at (f r s P D g i : PTm n) (h : Γ ⊢[PRAAx] pointPowers f r P)
    (hi : Γ ⊢[PRAAx] lt i (length (group s P D g))) : Γ ⊢[PRAAx]
    rationalEq (RationalScalarPowerGaussianEmbedding.power (ordinate (group s P D g) i) r)
      (RationalPolynomialGaussianEmbedding.evaluate f (abscissa (group s P D g) i)) := by
  have hb := lt_congr (.eqRefl i) (group_length testBody P (length D) (data s D) g) hi
  have eq := group_lookup testBody P (length D) (data s D) g i hb
  have original := point_power_at f r P _ h (index_bound testBody P (length D) (data s D) g i hb)
  have py := congrAp2 RationalScalarPowerGaussianEmbedding.powerF (.eqRefl r) (congrSnd eq)
  have px := congrAp3 RationalPolynomialGaussianEmbedding.hornerF (.eqRefl (length f)) (.eqRefl f) (congrFst eq)
  exact rationalEq_congr py.eqSymm px.eqSymm original

theorem group_powers (f r s P D g : PTm n) (h : Γ ⊢[PRAAx] pointPowers f r P) : Γ ⊢[PRAAx] pointPowers f r (group s P D g) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] pointPowers (Syn.shift f) (Syn.shift r) (Syn.shift P) := by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_group,RationalScalarPowerGaussianEmbedding.subst_power,
    RationalPolynomialGaussianEmbedding.subst_evaluate,GaussianRationalFiberGrouping.subst_abscissa,GaussianRationalFiberGrouping.subst_ordinate] using
    group_power_at (Syn.shift f) (Syn.shift r) (Syn.shift s) (Syn.shift P) (Syn.shift D) (Syn.shift g) (var 0) hs.wk Prf.hyp0

private theorem group_distinct_at (s P D g i j : PTm n) (h : Γ ⊢[PRAAx] distinct P)
    (hi : Γ ⊢[PRAAx] lt i (length (group s P D g))) (hj : Γ ⊢[PRAAx] lt j (length (group s P D g)))
    (hij : Γ ⊢[PRAAx] lt i j) : Γ ⊢[PRAAx]
    neg (rationalEq (abscissa (group s P D g) j) (abscissa (group s P D g) i) ⋏
      rationalEq (ordinate (group s P D g) j) (ordinate (group s P D g) i)) := by
  let I := Foundations.FiniteCoverAssignment.indices testBody P (length D) (data s D) g
  have size := group_length (Γ := Γ) testBody P (length D) (data s D) g
  have bi := lt_congr (.eqRefl i) size hi
  have bj := lt_congr (.eqRefl j) size hj
  have ei := group_lookup testBody P (length D) (data s D) g i bi
  have ej := group_lookup testBody P (length D) (data s D) g j bj
  have original := distinct_at P (entry I i) (entry I j) h
    (index_bound testBody P (length D) (data s D) g i bi) (index_bound testBody P (length D) (data s D) g j bj)
    (indices_increasing testBody P (length D) (data s D) g i j hij bj)
  exact .impI (.impE original.wk (.andI
    (rationalEq_congr (congrFst ej.wk) (congrFst ei.wk) (.andE₁ Prf.hyp0))
    (rationalEq_congr (congrSnd ej.wk) (congrSnd ei.wk) (.andE₂ Prf.hyp0))))

theorem group_distinct (s P D g : PTm n) (h : Γ ⊢[PRAAx] distinct P) : Γ ⊢[PRAAx] distinct (group s P D g) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] distinct (Syn.shift P) := by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  let G := group (Syn.shift s) (Syn.shift P) (Syn.shift D) (Syn.shift g)
  let Δ := lt (var 0) (length G) :: Γ.map Fm.shift
  have hg : Δ ⊢[PRAAx] lt (var 0) (length G) := Prf.hyp0
  have inner : Δ ⊢[PRAAx] distinctFrom G (var 0) := by
    refine .allI (.impI (.impI ?_))
    let i := Syn.shift (var 0 : PTm (n+1))
    let G' := group (Syn.shift (Syn.shift s)) (Syn.shift (Syn.shift P)) (Syn.shift (Syn.shift D)) (Syn.shift (Syn.shift g))
    have hgs : Δ.map Fm.shift ⊢[PRAAx] lt i (length G') := by
      simpa only [i,G,G',Fm.shift,subst_lt,Foundations.SequenceComposition.subst_length,subst_group,Syn.shift] using hg.shift
    have hDs : Δ.map Fm.shift ⊢[PRAAx] distinct (Syn.shift (Syn.shift P)) := by
      simpa only [Fm.shift,RationalCurvePointsGaussianEmbedding.subst_distinct,Syn.shift] using (hs.wk : Δ ⊢[PRAAx] distinct (Syn.shift P)).shift
    simpa only [i,G,G',Syn.shift,subst_group,GaussianRationalFiberGrouping.subst_abscissa,GaussianRationalFiberGrouping.subst_ordinate,
      RationalArgmin.subst_rationalEq,Fm.subst_and] using group_distinct_at (Syn.shift (Syn.shift s)) (Syn.shift (Syn.shift P))
        (Syn.shift (Syn.shift D)) (Syn.shift (Syn.shift g)) i (var 0) hDs.wk.wk hgs.wk.wk Prf.hyp1 Prf.hyp0
  simpa only [Δ,G,Syn.shift,subst_group,Foundations.SequenceComposition.subst_length] using inner

def total (s P D : PTm n) : PTm n := Foundations.FiniteCoverAssignment.total testBody P (length D) (data s D)
def bounds (s P D m : PTm n) : Fm PTm n := groupBounds testBody P (length D) (data s D) m
@[simp] theorem subst_total {q : ℕ} (σ : Fin n → PTm q) (s P D : PTm n) :
    Syn.subst σ (total s P D) = total (Syn.subst σ s) (Syn.subst σ P) (Syn.subst σ D) := by simp [total]
@[simp] theorem subst_bounds {q : ℕ} (σ : Fin n → PTm q) (s P D m : PTm n) :
    (bounds s P D m).subst σ = bounds (Syn.subst σ s) (Syn.subst σ P) (Syn.subst σ D) (Syn.subst σ m) := by simp [bounds]
theorem cardinal_partition (s P D : PTm n) (h : Γ ⊢[PRAAx] cover s P D) : Γ ⊢[PRAAx] total s P D ≐ length P :=
  Foundations.FiniteCoverAssignment.cardinal_partition _ _ _ _ (generic_cover s P D h)
theorem count_from_groups (s P D m : PTm n) (h : Γ ⊢[PRAAx] cover s P D) (hb : Γ ⊢[PRAAx] bounds s P D m) : Γ ⊢[PRAAx]
    le (length P) (length D*m) := Foundations.FiniteCoverAssignment.cover_count _ _ _ _ _ (generic_cover s P D h) hb

/-- The exact source Cover_{M,s}: its tuple is the original Phi_s list. -/
def sourceCoverBit (s P M : PTm n) : PTm n := RationalSubspaceCoverSearch.coverBit (featureList s P) M (dimension s)
def selectedFamily (s P M : PTm n) : PTm n := RationalSubspaceCoverSearch.chosen (featureList s P) M (dimension s)
@[simp] theorem subst_sourceCoverBit {q : ℕ} (σ : Fin n → PTm q) (s P M : PTm n) :
    Syn.subst σ (sourceCoverBit s P M) = sourceCoverBit (Syn.subst σ s) (Syn.subst σ P) (Syn.subst σ M) := by simp [sourceCoverBit]
@[simp] theorem subst_selectedFamily {q : ℕ} (σ : Fin n → PTm q) (s P M : PTm n) :
    Syn.subst σ (selectedFamily s P M) = selectedFamily (Syn.subst σ s) (Syn.subst σ P) (Syn.subst σ M) := by simp [selectedFamily]
theorem source_cover_bit_cases (s P M : PTm n) : Γ ⊢[PRAAx] (sourceCoverBit s P M ≐ zero) ⋎ (sourceCoverBit s P M ≐ one) :=
  RationalSubspaceCoverSearch.cover_bit_cases _ _ _
theorem source_candidate_bound (s P M : PTm n) : Γ ⊢[PRAAx]
    RationalSubspaceCoverCandidates.bound (featureList s P) M ≐ pw two (length P*M) :=
  Combinatorics.BinomialTheorem.congrPw (.eqRefl two) (congrMul (feature_list_length s P) (.eqRefl M))
theorem selected_family_length (s P M : PTm n) : Γ ⊢[PRAAx] length (selectedFamily s P M) ≐ M :=
  RationalSubspaceCoverSearch.chosen_length _ _ _
theorem selected_certificate (s P M : PTm n) (h : Γ ⊢[PRAAx] sourceCoverBit s P M ≐ one) : Γ ⊢[PRAAx]
    RationalFiniteSpanCover.family (selectedFamily s P M) (dimension s) ⋏ cover s P (selectedFamily s P M) :=
  RationalSubspaceCoverSearch.test_sound _ _ _ _ (RationalSubspaceCoverSearch.selected_success _ _ _
    (RationalSubspaceCoverSearch.cover_bit_found _ _ _ h))
theorem selected_cover (s P M : PTm n) (h : Γ ⊢[PRAAx] sourceCoverBit s P M ≐ one) : Γ ⊢[PRAAx]
    cover s P (selectedFamily s P M) := .andE₂ (selected_certificate s P M h)
theorem selected_group_members (s P M g : PTm n) (h : Γ ⊢[PRAAx] sourceCoverBit s P M ≐ one) : Γ ⊢[PRAAx]
    members (entry (selectedFamily s P M) g) (length (entry (selectedFamily s P M) g)) s (group s P (selectedFamily s P M) g) :=
  group_members _ _ _ _ (selected_cover s P M h)
theorem selected_partition (s P M : PTm n) (h : Γ ⊢[PRAAx] sourceCoverBit s P M ≐ one) : Γ ⊢[PRAAx]
    total s P (selectedFamily s P M) ≐ length P := cardinal_partition _ _ _ (selected_cover s P M h)

theorem bounds_intro (s P D m : PTm n) (h : Γ ⊢[PRAAx] .all (lt (var 0) (length (Syn.shift D)) ⟶
    le (length (group (Syn.shift s) (Syn.shift P) (Syn.shift D) (var 0))) (Syn.shift m))) : Γ ⊢[PRAAx] bounds s P D m := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (Syn.shift D)) :: Γ.map Fm.shift
  have rule : Δ ⊢[PRAAx] lt (var 0) (length (Syn.shift D)) ⟶
      le (length (group (Syn.shift s) (Syn.shift P) (Syn.shift D) (var 0))) (Syn.shift m) := by simpa using h.allOpen.wk
  simpa only [Δ,Syn.shift,subst_data,Foundations.SequenceComposition.subst_length] using
    le_congr (group_length testBody (Syn.shift P) (length (Syn.shift D)) (data (Syn.shift s) (Syn.shift D)) (var 0)) (.eqRefl _)
      (.impE rule Prf.hyp0)

theorem selected_family_at (s P M g : PTm n) (h : Γ ⊢[PRAAx] sourceCoverBit s P M ≐ one) (hg : Γ ⊢[PRAAx] lt g M) : Γ ⊢[PRAAx]
    RationalSuperellipticSubspace.properSpan (entry (selectedFamily s P M) g) (length (entry (selectedFamily s P M) g)) (dimension s) :=
  RationalFiniteSpanCover.family_at _ _ _ (.andE₁ (selected_certificate s P M h))
    (lt_congr (.eqRefl _) (selected_family_length s P M).eqSymm hg)
theorem selected_count_from_groups (s P M m : PTm n) (h : Γ ⊢[PRAAx] sourceCoverBit s P M ≐ one)
    (hb : Γ ⊢[PRAAx] bounds s P (selectedFamily s P M) m) : Γ ⊢[PRAAx] le (length P) (m*M) :=
  le_congr (.eqRefl _) ((congrMul (selected_family_length s P M) (.eqRefl m)).eqTrans (mul_comm M m))
    (count_from_groups _ _ _ _ (selected_cover s P M h) hb)

def selectedGroups (s P M : PTm n) : PTm n := Foundations.FiniteCoverAssignment.groups testBody P
  (length (selectedFamily s P M)) (data s (selectedFamily s P M))
def selectedTotal (s P M : PTm n) : PTm n := total s P (selectedFamily s P M)
def featureListF : PR 2 := PTm.toPR (featureList (var 0) (var 1))
def groupF : PR 4 := PTm.toPR (group (var 0) (var 1) (var 2) (var 3))
def output (s P M : PTm n) : PTm n := pairT (sourceCoverBit s P M) (pairT (selectedFamily s P M)
  (pairT (featureList s P) (pairT (selectedGroups s P M) (selectedTotal s P M))))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (s P M : PTm n) : PTm n := app outputF ![s,P,M]
@[simp] theorem subst_selectedGroups {q : ℕ} (σ : Fin n → PTm q) (s P M : PTm n) :
    Syn.subst σ (selectedGroups s P M) = selectedGroups (Syn.subst σ s) (Syn.subst σ P) (Syn.subst σ M) := by simp [selectedGroups]
@[simp] theorem subst_selectedTotal {q : ℕ} (σ : Fin n → PTm q) (s P M : PTm n) :
    Syn.subst σ (selectedTotal s P M) = selectedTotal (Syn.subst σ s) (Syn.subst σ P) (Syn.subst σ M) := by simp [selectedTotal]
@[simp] theorem subst_output {q : ℕ} (σ : Fin n → PTm q) (s P M : PTm n) :
    Syn.subst σ (output s P M) = output (Syn.subst σ s) (Syn.subst σ P) (Syn.subst σ M) := by simp [output]
@[simp] theorem subst_run {q : ℕ} (σ : Fin n → PTm q) (s P M : PTm n) :
    Syn.subst σ (run s P M) = run (Syn.subst σ s) (Syn.subst σ P) (Syn.subst σ M) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem feature_list_program_at (s P : PTm n) : Γ ⊢[PRAAx] app featureListF ![s,P] ≐ featureList s P := by
  simpa [featureListF] using toPR_eq (Γ := Γ) (featureList (var 0) (var 1) : PTm 2) ![s,P]
theorem group_program_at (s P D g : PTm n) : Γ ⊢[PRAAx] app groupF ![s,P,D,g] ≐ group s P D g := by
  simpa [groupF] using toPR_eq (Γ := Γ) (group (var 0) (var 1) (var 2) (var 3) : PTm 4) ![s,P,D,g]
theorem program_at (s P M : PTm n) : Γ ⊢[PRAAx] run s P M ≐ output s P M := by
  simpa [run,outputF,output,Matrix.cons_val_succ',Matrix.cons_val_zero'] using
    toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![s,P,M]
theorem returned_bit (s P M : PTm n) : Γ ⊢[PRAAx] fstT (run s P M) ≐ sourceCoverBit s P M :=
  (congrFst (program_at s P M)).eqTrans (fst_pair _ _)
theorem returned_family (s P M : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run s P M)) ≐ selectedFamily s P M :=
  (congrFst ((congrSnd (program_at s P M)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_features (s P M : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run s P M))) ≐ featureList s P :=
  (congrFst ((congrSnd ((congrSnd (program_at s P M)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
private theorem returned_tail (s P M : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run s P M))) ≐ pairT (selectedGroups s P M) (selectedTotal s P M) := by
  have e := (congrSnd (program_at (Γ := Γ) s P M)).eqTrans (snd_pair _ _)
  have e' := (congrSnd e).eqTrans (snd_pair _ _)
  exact (congrSnd e').eqTrans (snd_pair _ _)
theorem returned_groups (s P M : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run s P M)))) ≐ selectedGroups s P M :=
  (congrFst (returned_tail s P M)).eqTrans (fst_pair _ _)
theorem returned_total (s P M : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (run s P M)))) ≐ selectedTotal s P M :=
  (congrSnd (returned_tail s P M)).eqTrans (snd_pair _ _)
theorem selected_groups_length (s P M : PTm n) : Γ ⊢[PRAAx] length (selectedGroups s P M) ≐ M :=
  (Foundations.FiniteCoverAssignment.groups_length testBody P (length (selectedFamily s P M)) (data s (selectedFamily s P M))).eqTrans
    (selected_family_length s P M)
theorem returned_partition (s P M : PTm n) (h : Γ ⊢[PRAAx] sourceCoverBit s P M ≐ one) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (sndT (run s P M)))) ≐ length P := (returned_total s P M).eqTrans (selected_partition s P M h)

theorem actual_original_feature_list_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (length (var 1)) ⟶ entry (featureList (var 0) (var 1)) (var 2) ≐
      features (var 0) (abscissa (var 1) (var 2)) (ordinate (var 1) (var 2))) := closeUniv 3 (.impI (feature_list_lookup _ _ _ Prf.hyp0))
theorem actual_original_phi_group_members_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (cover (var 0) (var 1) (var 2) ⟶ members (entry (var 2) (var 3)) (length (entry (var 2) (var 3)))
      (var 0) (group (var 0) (var 1) (var 2) (var 3))) := closeUniv 4 (.impI (group_members _ _ _ _ Prf.hyp0))
theorem actual_original_phi_group_distinct_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (distinct (var 1) ⟶ distinct (group (var 0) (var 1) (var 2) (var 3))) := closeUniv 4 (.impI (group_distinct _ _ _ _ Prf.hyp0))
theorem actual_original_phi_group_curve_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (pointPowers (var 0) (var 1) (var 3) ⟶ pointPowers (var 0) (var 1) (group (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (group_powers _ _ _ _ _ _ Prf.hyp0))
theorem actual_phi_partition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (cover (var 0) (var 1) (var 2) ⟶ total (var 0) (var 1) (var 2) ≐ length (var 1)) := closeUniv 3 (.impI (cardinal_partition _ _ _ Prf.hyp0))
theorem actual_phi_selected_family_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (sourceCoverBit (var 0) (var 1) (var 2) ≐ one ⟶
      RationalFiniteSpanCover.family (selectedFamily (var 0) (var 1) (var 2)) (dimension (var 0)) ⋏
        cover (var 0) (var 1) (selectedFamily (var 0) (var 1) (var 2))) := closeUniv 3 (.impI (selected_certificate _ _ _ Prf.hyp0))
theorem actual_phi_conditional_cover_count_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (sourceCoverBit (var 0) (var 1) (var 2) ≐ one ⟶ bounds (var 0) (var 1) (selectedFamily (var 0) (var 1) (var 2)) (var 3) ⟶
      le (length (var 1)) (var 3*var 2)) := closeUniv 4 (.impI (.impI (selected_count_from_groups _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_phi_source_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem actual_returned_phi_partition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (sourceCoverBit (var 0) (var 1) (var 2) ≐ one ⟶ sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2))))) ≐ length (var 1)) :=
  closeUniv 3 (.impI (returned_partition _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.RationalPhiCoverAssignment
