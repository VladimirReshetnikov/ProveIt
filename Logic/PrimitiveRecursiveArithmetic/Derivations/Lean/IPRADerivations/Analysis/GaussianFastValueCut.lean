import IPRADerivations.Analysis.GaussianRootSchedule
import IPRADerivations.Analysis.GaussianEuclideanDistanceName
import IPRADerivations.Analysis.GaussianRationalSlackRemoval
import IPRADerivations.Analysis.GaussianReconstructionRoots
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual fast Gaussian names and finite envelope transfer

A fixed PR2 supplies arbitrary original Gaussian-rational observations.
Their numerical regularity modulus is packed into the persistent data of
an actual normalized PR2 name. Canonical recoding preserves decoded value,
without requiring canonical raw input codes. A genuine regularity law and
finite dyadic envelopes imply the exact represented radius cut. The proof
removes slack from each fixed rational observation before normalizing its
precision; no represented limit or target-cut assumption is used.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianFastValueCut

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded distanceBounded)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (ofGaussian represents positive_product)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (unit unit_positive subst_unit)
open LeanProofs.IPRA.Analysis.GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def recode (z : PTm n) : PTm n := ofGaussian (rawGaussian z) (rawDen z)
def normalizer (L : PTm n) : PTm n := GaussianRootSchedule.binaryLength L+two
def exponent (L k : PTm n) : PTm n := k+normalizer L
def value (f : PR 2) (L x k : PTm n) : PTm n := recode (ap2 f (exponent L k) x)
def regular (f : PR 2) (L x : PTm n) : Fm PTm n := .all (.all
  (distanceBounded (ap2 f (var 1) (Syn.shift (Syn.shift x))) (ap2 f (var 0) (Syn.shift (Syn.shift x)))
    (Syn.shift (Syn.shift L)*(unit (var 1)+unit (var 0))) (unit (var 1)*unit (var 0))))
def rawEnvelope (f : PR 2) (x A B K : PTm n) : Fm PTm n := .all
  (bounded (ap2 f (var 0) (Syn.shift x)) (Syn.shift A*unit (var 0)+Syn.shift K*Syn.shift B)
    (Syn.shift B*unit (var 0)))
def valueCut (f : PR 2) (L x A B : PTm n) : Fm PTm n := .all
  (bounded (value f (Syn.shift L) (Syn.shift x) (var 0)) (Syn.shift A*unit (var 0)+Syn.shift B)
    (Syn.shift B*unit (var 0)))

@[simp] theorem subst_recode {m : ℕ} (σ : Fin n → PTm m) (z : PTm n) :
    Syn.subst σ (recode z) = recode (Syn.subst σ z) := by simp [recode]
@[simp] theorem subst_normalizer {m : ℕ} (σ : Fin n → PTm m) (L : PTm n) :
    Syn.subst σ (normalizer L) = normalizer (Syn.subst σ L) := by simp [normalizer]
@[simp] theorem subst_exponent {m : ℕ} (σ : Fin n → PTm m) (L k : PTm n) :
    Syn.subst σ (exponent L k) = exponent (Syn.subst σ L) (Syn.subst σ k) := by simp [exponent]
@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (L x k : PTm n) :
    Syn.subst σ (value f L x k) = value f (Syn.subst σ L) (Syn.subst σ x) (Syn.subst σ k) := by simp [value]
@[simp] theorem subst_regular {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (L x : PTm n) :
    (regular f L x).subst σ = regular f (Syn.subst σ L) (Syn.subst σ x) := by
  simp [regular,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_rawEnvelope {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x A B K : PTm n) :
    (rawEnvelope f x A B K).subst σ = rawEnvelope f (Syn.subst σ x) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ K) := by
  simp [rawEnvelope,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_valueCut {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (L x A B : PTm n) :
    (valueCut f L x A B).subst σ = valueCut f (Syn.subst σ L) (Syn.subst σ x) (Syn.subst σ A) (Syn.subst σ B) := by
  simp [valueCut,Syn.subst_shift,Syn.shift_subst]

theorem recode_represents (z : PTm n) : Γ ⊢[PRAAx] represents (recode z) (rawGaussian z) (rawDen z) :=
  GaussianRationalHorner.ofGaussian_represents _ _ (raw_den_positive z)

theorem recode_canonical (z : PTm n) : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (recode z) :=
  GaussianRationalHorner.ofGaussian_canonical _ _ (raw_den_positive z)

theorem recode_bound_iff (z A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    Fm.iff (bounded (recode z) A B) (bounded z A B) := by
  have old := GaussianRationalMetric.bounded_iff z (rawGaussian z) (rawDen z) A B (raw_den_positive z) hB (raw_represents z)
  have fresh := GaussianRationalMetric.bounded_iff (recode z) (rawGaussian z) (rawDen z) A B (raw_den_positive z) hB (recode_represents z)
  exact fresh.iffTrans old.iffSymm

theorem recode_distance (z : PTm n) : Γ ⊢[PRAAx] distanceBounded (recode z) z zero one := by
  apply (GaussianRationalMetric.bounded_difference_iff _ _ _ _ _ _ _ (raw_den_positive z) (le_refl _)
    (recode_represents z) (raw_represents z)).iffMpr
  have nz := natEq ((GaussianRootAlgebra.normSq_equal (GaussianRootAlgebra.sub_self (Γ := Γ) (rawGaussian z))).eqTrans
    ComplexLogarithmRemainder.normSq_zero)
  apply le_of_eq_add (d := zero)
  apply deriveNat
  ipra_simps
  rw [nz]
  ring

theorem recode_distance_bound (z w A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] distanceBounded z w A B) : Γ ⊢[PRAAx] distanceBounded (recode z) (recode w) A B := by
  have first := distance_radius_mono _ _ zero one zero B (le_refl _) hB
    (le_of_eq_add (d := zero) (by ipra_ring)) (recode_distance z)
  have last := distance_radius_mono _ _ zero one zero B (le_refl _) hB
    (le_of_eq_add (d := zero) (by ipra_ring))
    (GaussianRationalDistanceOrder.distance_symmetric _ _ _ _ (le_refl one) (recode_distance w))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hB (distance_triangle_same _ _ _ _ _ _ hB first h) last)

theorem regular_at (f : PR 2) (L x s t : PTm n) (h : Γ ⊢[PRAAx] regular f L x) : Γ ⊢[PRAAx]
    distanceBounded (ap2 f s x) (ap2 f t x) (L*(unit s+unit t)) (unit s*unit t) := by
  have first : Γ ⊢[PRAAx] .all (distanceBounded (ap2 f (Syn.shift s) (Syn.shift x))
      (ap2 f (var 0) (Syn.shift x)) (Syn.shift L*(unit (Syn.shift s)+unit (var 0)))
      (unit (Syn.shift s)*unit (var 0))) := by
    simpa only [regular,Fm.subst_all,GaussianRationalMetric.subst_distanceBounded,subst_ap2,subst_unit,
      PTm.subst_add,PTm.subst_mul,Syn.subst_var,Syn.up_zero,Syn.up_one,Syn.up_succ,
      Foundations.BoundedFormulas.subst_up_shift',Syn.inst_zero,Syn.inst_succ,Syn.subst_inst_shift,Syn.shift_var] using h.allE s
  simpa only [GaussianRationalMetric.subst_distanceBounded,subst_ap2,subst_unit,PTm.subst_add,PTm.subst_mul,
    Syn.subst_var,Syn.inst_zero,Syn.inst_succ,Syn.subst_inst_shift] using first.allE t

theorem raw_envelope_at (f : PR 2) (x A B K s : PTm n) (h : Γ ⊢[PRAAx] rawEnvelope f x A B K) : Γ ⊢[PRAAx]
    bounded (ap2 f s x) (A*unit s+K*B) (B*unit s) := by simpa [rawEnvelope] using h.allE s

theorem exponent_unit (L k : PTm n) : Γ ⊢[PRAAx] unit (exponent L k) ≐ unit k*unit (normalizer L) := pw_add _ _ _
theorem normalizer_budget (L : PTm n) : Γ ⊢[PRAAx] le L (unit (normalizer L)) :=
  le_trans (Prf.andE₁ (GaussianRootSchedule.binary_length_correct _))
    (GaussianFactorBudget.power_monotone_length _ _ _ (le_succ_self one) (le_add_right _ _))
theorem query_budget (L k : PTm n) : Γ ⊢[PRAAx] le (L*unit k) (unit (exponent L k)) := by
  have h := le_mul_mono (normalizer_budget (Γ := Γ) L) (le_refl (unit k))
  exact le_congr (.eqRefl _) ((mul_comm _ _).eqTrans (exponent_unit L k).eqSymm) h

theorem regularity_budget (L s t : PTm n) : Γ ⊢[PRAAx]
    le ((L*(unit (exponent L s)+unit (exponent L t)))*(unit s*unit t))
      ((unit s+unit t)*(unit (exponent L s)*unit (exponent L t))) := by
  have h := le_mul_mono (normalizer_budget (Γ := Γ) L)
    (le_refl ((unit s+unit t)*unit (normalizer L)*unit s*unit t))
  have hs := natEq (exponent_unit (Γ := Γ) L s)
  have ht := natEq (exponent_unit (Γ := Γ) L t)
  apply le_congr ?_ ?_ h
  · apply deriveNat
    ipra_simps
    rw [hs,ht]
    ring
  · apply deriveNat
    ipra_simps
    rw [hs,ht]
    ring

theorem value_regular_at (f : PR 2) (L x s t : PTm n) (h : Γ ⊢[PRAAx] regular f L x) : Γ ⊢[PRAAx]
    distanceBounded (value f L x s) (value f L x t) (unit s+unit t) (unit s*unit t) :=
  distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (unit_positive _) (unit_positive _))
    (positive_product _ _ (unit_positive _) (unit_positive _)) (regularity_budget L s t)
    (recode_distance_bound _ _ _ _ (positive_product _ _ (unit_positive _) (unit_positive _))
      (regular_at f L x (exponent L s) (exponent L t) h))

/-- Compare a fixed raw query to every later rational observation. The
result has the desired base radius plus a dyadic slack independent of s. -/
theorem fixed_query_slack (f : PR 2) (L x A B K r s : PTm n)
    (hReg : Γ ⊢[PRAAx] regular f L x) (hB : Γ ⊢[PRAAx] le one B)
    (hEnv : Γ ⊢[PRAAx] rawEnvelope f x A B K) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (ap2 f r x) (A*unit r+L*B) (B*unit r) (L+K) s := by
  have dh := positive_product (Γ := Γ) _ _ (unit_positive r) (unit_positive s)
  have bh := positive_product (Γ := Γ) _ _ hB (unit_positive s)
  have br := positive_product (Γ := Γ) _ _ hB (unit_positive r)
  have triangle := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ dh bh
    (regular_at f L x r s hReg) (raw_envelope_at f x A B K s hEnv)
  have cross : Γ ⊢[PRAAx]
      le ((L*(unit r+unit s)*(B*unit s)+(A*unit s+K*B)*(unit r*unit s))*((B*unit r)*unit s))
        (((A*unit r+L*B)*unit s+(L+K)*(B*unit r))*((unit r*unit s)*(B*unit s))) :=
    le_of_eq_add (d := zero) (by ipra_ring)
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (positive_product _ _ dh bh) (positive_product _ _ br (unit_positive s)) cross triangle

/-- Exact finite slack removal at a fixed original rational query. -/
theorem fixed_query_bound (f : PR 2) (L x A B K r : PTm n)
    (hReg : Γ ⊢[PRAAx] regular f L x) (hB : Γ ⊢[PRAAx] le one B)
    (hEnv : Γ ⊢[PRAAx] rawEnvelope f x A B K) : Γ ⊢[PRAAx]
    bounded (ap2 f r x) (A*unit r+L*B) (B*unit r) := by
  apply GaussianRationalSlackRemoval.slack_removal _ _ _ (L+K) (positive_product _ _ hB (unit_positive r))
  refine .allI ?_
  have reg : Γ.map Fm.shift ⊢[PRAAx] regular f (Syn.shift L) (Syn.shift x) := by
    simpa only [Fm.shift,subst_regular,Syn.shift] using hReg.shift
  have b : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hB.shift
  have env : Γ.map Fm.shift ⊢[PRAAx] rawEnvelope f (Syn.shift x) (Syn.shift A) (Syn.shift B) (Syn.shift K) := by
    simpa only [Fm.shift,subst_rawEnvelope,Syn.shift] using hEnv.shift
  simpa only [Syn.shift,subst_ap2,subst_unit,PTm.subst_add,PTm.subst_mul] using
    fixed_query_slack f (Syn.shift L) (Syn.shift x) (Syn.shift A) (Syn.shift B) (Syn.shift K) (Syn.shift r) (var 0) reg b env

theorem value_cut_at (f : PR 2) (L x A B K k : PTm n)
    (hReg : Γ ⊢[PRAAx] regular f L x) (hB : Γ ⊢[PRAAx] le one B)
    (hEnv : Γ ⊢[PRAAx] rawEnvelope f x A B K) : Γ ⊢[PRAAx]
    bounded (value f L x k) (A*unit k+B) (B*unit k) := by
  have raw := fixed_query_bound f L x A B K (exponent L k) hReg hB hEnv
  have oldDen := positive_product (Γ := Γ) _ _ hB (unit_positive (exponent L k))
  have newDen := positive_product (Γ := Γ) _ _ hB (unit_positive k)
  have gap := natEq (eq_add_of_le (query_budget (Γ := Γ) L k))
  have cross : Γ ⊢[PRAAx]
      le ((A*unit (exponent L k)+L*B)*(B*unit k)) ((A*unit k+B)*(B*unit (exponent L k))) := by
    apply le_of_eq_add (d := B*B*PTm.monus (unit (exponent L k)) (L*unit k))
    apply deriveNat
    ipra_simps
    rw [gap]
    ring
  exact (recode_bound_iff _ _ _ newDen).iffMpr
    (GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ oldDen newDen cross raw)

theorem envelope_to_value_cut (f : PR 2) (L x A B K : PTm n)
    (hReg : Γ ⊢[PRAAx] regular f L x) (hB : Γ ⊢[PRAAx] le one B)
    (hEnv : Γ ⊢[PRAAx] rawEnvelope f x A B K) : Γ ⊢[PRAAx] valueCut f L x A B := by
  refine .allI ?_
  have reg : Γ.map Fm.shift ⊢[PRAAx] regular f (Syn.shift L) (Syn.shift x) := by
    simpa only [Fm.shift,subst_regular,Syn.shift] using hReg.shift
  have b : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hB.shift
  have env : Γ.map Fm.shift ⊢[PRAAx] rawEnvelope f (Syn.shift x) (Syn.shift A) (Syn.shift B) (Syn.shift K) := by
    simpa only [Fm.shift,subst_rawEnvelope,Syn.shift] using hEnv.shift
  exact value_cut_at f _ _ _ _ _ (var 0) reg b env

/-- Literal normalized differences satisfy the four-operand identity. The
common denominator is computed from the four actual decoded inputs. -/
theorem difference_identity_from_representations (a b c d α β γ δ E : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (ha : Γ ⊢[PRAAx] represents a α E)
    (hb : Γ ⊢[PRAAx] represents b β E) (hc : Γ ⊢[PRAAx] represents c γ E)
    (hd : Γ ⊢[PRAAx] represents d δ E) : Γ ⊢[PRAAx]
    GaussianRationalMetric.qsub (GaussianRationalMetric.qsub a b) (GaussianRationalMetric.qsub c d) ≐
      GaussianRationalMetric.qsub (GaussianRationalMetric.qsub a c) (GaussianRationalMetric.qsub b d) := by
  have left := GaussianRationalMetric.qsub_represents _ _ _ _ _ hE
    (GaussianRationalMetric.qsub_represents _ _ _ _ _ hE ha hb)
    (GaussianRationalMetric.qsub_represents _ _ _ _ _ hE hc hd)
  have right := GaussianRationalMetric.qsub_represents _ _ _ _ _ hE
    (GaussianRationalMetric.qsub_represents _ _ _ _ _ hE ha hc)
    (GaussianRationalMetric.qsub_represents _ _ _ _ _ hE hb hd)
  apply GaussianRationalHorner.canonical_unique _ _ _ _ (GaussianRationalMetric.qsub_canonical _ _)
    (GaussianRationalMetric.qsub_canonical _ _) hE (hrv := right)
  apply GaussianRationalHorner.represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := left)
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub] <;> ring

theorem difference_identity (a b c d : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalMetric.qsub (GaussianRationalMetric.qsub a b) (GaussianRationalMetric.qsub c d) ≐
      GaussianRationalMetric.qsub (GaussianRationalMetric.qsub a c) (GaussianRationalMetric.qsub b d) := by
  let E := GaussianRationalSyntheticDivision.remainingDen a b c d
  have hE : Γ ⊢[PRAAx] le one E := GaussianRationalSyntheticDivision.remaining_den_positive _ _ _ _
  have ha := GaussianRationalSyntheticDivision.rescale_to a (rawGaussian a) (rawDen a)
    (rawDen b*rawDen c*rawDen d) E (raw_represents (Γ := Γ) a)
    (by unfold E GaussianRationalSyntheticDivision.remainingDen; ipra_ring)
  have hb := GaussianRationalSyntheticDivision.rescale_to b (rawGaussian b) (rawDen b)
    (rawDen a*rawDen c*rawDen d) E (raw_represents (Γ := Γ) b)
    (by unfold E GaussianRationalSyntheticDivision.remainingDen; ipra_ring)
  have hc := GaussianRationalSyntheticDivision.rescale_to c (rawGaussian c) (rawDen c)
    (rawDen a*rawDen b*rawDen d) E (raw_represents (Γ := Γ) c)
    (by unfold E GaussianRationalSyntheticDivision.remainingDen; ipra_ring)
  have hd := GaussianRationalSyntheticDivision.rescale_to d (rawGaussian d) (rawDen d)
    (rawDen a*rawDen b*rawDen c) E (raw_represents (Γ := Γ) d)
    (by unfold E GaussianRationalSyntheticDivision.remainingDen; ipra_ring)
  exact difference_identity_from_representations _ _ _ _ _ _ _ _ E hE ha hb hc hd

theorem distance_difference (a b c d A B C D : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hac : Γ ⊢[PRAAx] distanceBounded a c A B) (hbd : Γ ⊢[PRAAx] distanceBounded b d C D) : Γ ⊢[PRAAx]
    distanceBounded (GaussianRationalMetric.qsub a b) (GaussianRationalMetric.qsub c d) (A*D+C*B) (B*D) :=
  GaussianRationalReciprocal.bound_congr (difference_identity a b c d).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianRationalReciprocal.bounded_difference _ _ _ _ _ _ hB hD hac hbd)

theorem distance_difference_same (a b c d A C B : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hac : Γ ⊢[PRAAx] distanceBounded a c A B)
    (hbd : Γ ⊢[PRAAx] distanceBounded b d C B) : Γ ⊢[PRAAx]
    distanceBounded (GaussianRationalMetric.qsub a b) (GaussianRationalMetric.qsub c d) (A+C) B :=
  distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hB hB) hB
    (le_of_eq_add (d := zero) (by ipra_ring)) (distance_difference a b c d A B C B hB hB hac hbd)

def differenceF (f g : PR 2) : PR 2 := PTm.toPR
  (GaussianRationalMetric.qsub (ap2 f (var 0) (var 1)) (ap2 g (var 0) (var 1)) : PTm 2)

theorem difference_at (f g : PR 2) (s x : PTm n) : Γ ⊢[PRAAx]
    ap2 (differenceF f g) s x ≐ GaussianRationalMetric.qsub (ap2 f s x) (ap2 g s x) := by
  change Γ ⊢[PRAAx] PTm.app (differenceF f g) ![s,x] ≐ GaussianRationalMetric.qsub (ap2 f s x) (ap2 g s x)
  simpa only [differenceF,GaussianRationalMetric.subst_qsub,subst_ap2,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.tail_cons] using
    toPR_eq (Γ := Γ) (GaussianRationalMetric.qsub (ap2 f (var 0) (var 1)) (ap2 g (var 0) (var 1)) : PTm 2) ![s,x]

theorem difference_regular_at (f g : PR 2) (L M x s t : PTm n)
    (hf : Γ ⊢[PRAAx] regular f L x) (hg : Γ ⊢[PRAAx] regular g M x) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (differenceF f g) s x) (ap2 (differenceF f g) t x)
      ((L+M)*(unit s+unit t)) (unit s*unit t) :=
  distance_congr (difference_at f g s x).eqSymm (difference_at f g t x).eqSymm (by ipra_ring) (.eqRefl _)
    (distance_difference_same _ _ _ _ _ _ _ (positive_product _ _ (unit_positive s) (unit_positive t))
      (regular_at f L x s t hf) (regular_at g M x s t hg))

theorem difference_regular (f g : PR 2) (L M x : PTm n)
    (hf : Γ ⊢[PRAAx] regular f L x) (hg : Γ ⊢[PRAAx] regular g M x) : Γ ⊢[PRAAx] regular (differenceF f g) (L+M) x := by
  refine .allI (.allI ?_)
  have f2 : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] regular f (Syn.shift (Syn.shift L)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,subst_regular,Syn.shift] using hf.shift.shift
  have g2 : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] regular g (Syn.shift (Syn.shift M)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,subst_regular,Syn.shift] using hg.shift.shift
  simpa only [Syn.shift,PTm.subst_add] using difference_regular_at f g _ _ _ (var 1) (var 0) f2 g2

def nameData (L x : PTm n) : PTm n := pairT L x
def nameBody (f : PR 2) : PTm 2 := value f (fstT (var 1)) (sndT (var 1)) (var 0)
def nameF (f : PR 2) : PR 2 := PTm.toPR (nameBody f)
def radiusCut (f : PR 2) (L x A B : PTm n) : Fm PTm n := .all
  (bounded (ap2 (nameF f) (var 0) (nameData (Syn.shift L) (Syn.shift x)))
    (Syn.shift A*unit (var 0)+Syn.shift B) (Syn.shift B*unit (var 0)))

@[simp] theorem subst_nameData {m : ℕ} (σ : Fin n → PTm m) (L x : PTm n) :
    Syn.subst σ (nameData L x) = nameData (Syn.subst σ L) (Syn.subst σ x) := by simp [nameData]
@[simp] theorem subst_radiusCut {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (L x A B : PTm n) :
    (radiusCut f L x A B).subst σ = radiusCut f (Syn.subst σ L) (Syn.subst σ x) (Syn.subst σ A) (Syn.subst σ B) := by
  simp [radiusCut,Syn.subst_shift,Syn.shift_subst]

theorem value_congr (f : PR 2) {L L' x x' k k' : PTm n}
    (hL : Γ ⊢[PRAAx] L ≐ L') (hx : Γ ⊢[PRAAx] x ≐ x') (hk : Γ ⊢[PRAAx] k ≐ k') : Γ ⊢[PRAAx]
    value f L x k ≐ value f L' x' k' := by
  ipra_congr (value f (var 0) (var 1) (var 2) : PTm 3) with [hL, hx, hk]

theorem name_at (f : PR 2) (L x k : PTm n) : Γ ⊢[PRAAx]
    ap2 (nameF f) k (nameData L x) ≐ value f L x k := by
  have base : Γ ⊢[PRAAx] ap2 (nameF f) k (nameData L x) ≐ value f (fstT (nameData L x)) (sndT (nameData L x)) k := by
    simpa [nameF,nameBody,ap2] using toPR_eq (Γ := Γ) (nameBody f) ![k,nameData L x]
  exact base.eqTrans (value_congr f (fst_pair _ _) (snd_pair _ _) (.eqRefl _))

theorem name_canonical (f : PR 2) (L x k : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (ap2 (nameF f) k (nameData L x)) :=
  GaussianRationalHorner.canonical_congr (name_at f L x k) (recode_canonical _)

theorem name_fast (f : PR 2) (L x : PTm n) (h : Γ ⊢[PRAAx] regular f L x) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN (nameF f) (nameData L x) := by
  refine .allI (.allI ?_)
  have reg : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] regular f (Syn.shift (Syn.shift L)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,subst_regular,Syn.shift] using h.shift.shift
  simpa only [Syn.shift,subst_nameData,GaussianCoefficientNameBounds.unit,GaussianEuclideanPointDistance.unit] using
    distance_congr (name_at f (Syn.shift (Syn.shift L)) (Syn.shift (Syn.shift x)) (var 1)).eqSymm
      (name_at f (Syn.shift (Syn.shift L)) (Syn.shift (Syn.shift x)) (var 0)).eqSymm
      (.eqRefl _) (.eqRefl _) (value_regular_at f _ _ (var 1) (var 0) reg)

/-- The represented radius comparison is a cut on the actual PR2 name.
Its all-slack envelope is an input finite bound, not the desired cut. -/
theorem envelope_to_cut (f : PR 2) (L x A B K : PTm n)
    (hReg : Γ ⊢[PRAAx] regular f L x) (hB : Γ ⊢[PRAAx] le one B)
    (hEnv : Γ ⊢[PRAAx] rawEnvelope f x A B K) : Γ ⊢[PRAAx] radiusCut f L x A B := by
  refine .allI ?_
  have reg : Γ.map Fm.shift ⊢[PRAAx] regular f (Syn.shift L) (Syn.shift x) := by
    simpa only [Fm.shift,subst_regular,Syn.shift] using hReg.shift
  have b : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hB.shift
  have env : Γ.map Fm.shift ⊢[PRAAx] rawEnvelope f (Syn.shift x) (Syn.shift A) (Syn.shift B) (Syn.shift K) := by
    simpa only [Fm.shift,subst_rawEnvelope,Syn.shift] using hEnv.shift
  exact GaussianRationalReciprocal.bound_congr (name_at f _ _ (var 0)).eqSymm (.eqRefl _) (.eqRefl _)
    (value_cut_at f _ _ _ _ _ (var 0) reg b env)

theorem generic_fast_gaussian_name_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (regular f (var 0) (var 1) ⟶ GaussianEuclideanDistanceName.pointCN (nameF f) (nameData (var 0) (var 1))) :=
  closeUniv 2 (.impI (name_fast _ _ _ Prf.hyp0))

theorem finite_envelope_to_cut_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (regular f (var 0) (var 1) ⟶ le one (var 3) ⟶ rawEnvelope f (var 1) (var 2) (var 3) (var 4) ⟶
      radiusCut f (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 5 (.impI (.impI (.impI (envelope_to_cut _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem difference_distance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (le one (var 5) ⟶ le one (var 7) ⟶ distanceBounded (var 0) (var 2) (var 4) (var 5) ⟶
      distanceBounded (var 1) (var 3) (var 6) (var 7) ⟶
        distanceBounded (GaussianRationalMetric.qsub (var 0) (var 1)) (GaussianRationalMetric.qsub (var 2) (var 3))
          (var 4*var 7+var 6*var 5) (var 5*var 7)) :=
  closeUniv 8 (.impI (.impI (.impI (.impI
    (distance_difference _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem difference_regularity_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (regular f (var 0) (var 2) ⟶ regular g (var 1) (var 2) ⟶ regular (differenceF f g) (var 0+var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (difference_regular _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem fast_value_program_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap2 (nameF f) (var 2) (nameData (var 0) (var 1)) ≐ value f (var 0) (var 1) (var 2)) :=
  closeUniv 3 (name_at _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianFastValueCut
