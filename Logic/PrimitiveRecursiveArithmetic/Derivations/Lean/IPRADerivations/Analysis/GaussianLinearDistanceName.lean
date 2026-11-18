import IPRADerivations.Analysis.GaussianEuclideanDistanceUpperCut
import IPRADerivations.Analysis.GaussianRootSchedule

/-!
# Actual nonnegative affine Euclidean distance names

The observations are normalized fractions M*d_s+A/B using the actual
natural numerator and denominator of the finite Euclidean distance sample.
An internally computed precision shift yields a genuine fast scalar name.
Its regularity is derived from point CN and the actual finite-distance
program, without a supplied output-name or affine-variation law.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianLinearDistanceName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianEuclideanPointDistance (unit unit_positive subst_unit)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (pointCN distanceSample upper_of_representations)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceUpperCut (numerator denominator denominator_positive sample_represents)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def rawNumerator (point : PR 2) (T x M A B s : PTm n) : PTm n :=
  M*numerator point T x s*B+A*denominator point T x s
def rawDenominator (point : PR 2) (T x B s : PTm n) : PTm n := B*denominator point T x s
def rawSample (point : PR 2) (T x M A B s : PTm n) : PTm n :=
  RationalIntegerNormalization.normalize (ZT.ofNat (rawNumerator point T x M A B s)) (rawDenominator point T x B s)
def normalizer (M : PTm n) : PTm n := GaussianRootSchedule.binaryLength M+two
def exponent (M k : PTm n) : PTm n := k+normalizer M
def sample (point : PR 2) (T x M A B k : PTm n) : PTm n := rawSample point T x M A B (exponent M k)

@[simp] theorem subst_rawNumerator {l : ℕ} (σ : Fin n → PTm l) (point : PR 2) (T x M A B s : PTm n) :
    Syn.subst σ (rawNumerator point T x M A B s) = rawNumerator point (Syn.subst σ T) (Syn.subst σ x)
      (Syn.subst σ M) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ s) := by simp [rawNumerator]
@[simp] theorem subst_rawDenominator {l : ℕ} (σ : Fin n → PTm l) (point : PR 2) (T x B s : PTm n) :
    Syn.subst σ (rawDenominator point T x B s) = rawDenominator point (Syn.subst σ T) (Syn.subst σ x)
      (Syn.subst σ B) (Syn.subst σ s) := by simp [rawDenominator]
@[simp] theorem subst_rawSample {l : ℕ} (σ : Fin n → PTm l) (point : PR 2) (T x M A B s : PTm n) :
    Syn.subst σ (rawSample point T x M A B s) = rawSample point (Syn.subst σ T) (Syn.subst σ x)
      (Syn.subst σ M) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ s) := by simp [rawSample]
@[simp] theorem subst_normalizer {l : ℕ} (σ : Fin n → PTm l) (M : PTm n) :
    Syn.subst σ (normalizer M) = normalizer (Syn.subst σ M) := by simp [normalizer]
@[simp] theorem subst_exponent {l : ℕ} (σ : Fin n → PTm l) (M k : PTm n) :
    Syn.subst σ (exponent M k) = exponent (Syn.subst σ M) (Syn.subst σ k) := by simp [exponent]
@[simp] theorem subst_sample {l : ℕ} (σ : Fin n → PTm l) (point : PR 2) (T x M A B k : PTm n) :
    Syn.subst σ (sample point T x M A B k) = sample point (Syn.subst σ T) (Syn.subst σ x)
      (Syn.subst σ M) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ k) := by simp [sample]

theorem raw_denominator_positive (point : PR 2) (T x B s : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] le one (rawDenominator point T x B s) := positive_product _ _ hB (denominator_positive point T x s)

theorem raw_represents (point : PR 2) (T x M A B s : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (rawSample point T x M A B s) (ZT.ofNat (rawNumerator point T x M A B s))
      (rawDenominator point T x B s) :=
  RationalIntegerNormalization.normalize_preserves_value _ _ (raw_denominator_positive point T x B s hB)

theorem raw_canonical (point : PR 2) (T x M A B s : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    RationalNormalForm.wellFormed (rawSample point T x M A B s) :=
  RationalNormalForm.normalize_well_formed _ _ (raw_denominator_positive point T x B s hB)

/-- Converse finite value transport for the original scalar upper bound.
Only decoded positive denominators are cancelled. -/
theorem upper_to_cleared (u v P E Q F a b : PTm n)
    (hu : Γ ⊢[PRAAx] RationalArithmetic.represents u (ZT.ofNat P) E)
    (hv : Γ ⊢[PRAAx] RationalArithmetic.represents v (ZT.ofNat Q) F)
    (h : Γ ⊢[PRAAx] RationalValueBounds.upper u v a b) : Γ ⊢[PRAAx]
    le (b*F*P) (b*Q*E+a*E*F) := by
  have eu := ZT.toZ_eq hu
  have ev := ZT.toZ_eq hv
  have gap := natEq (eq_add_of_le h)
  apply RationalValueBounds.positive_cancel (positive_product _ _
    (RationalValueBounds.denominator_positive u) (RationalValueBounds.denominator_positive v))
  refine le_of_eq_add (d := E*F*PTm.monus
    (b*RationalValueBounds.crossLeft v u+a*denominatorOf u*denominatorOf v) (b*RationalValueBounds.crossLeft u v)) ?_
  apply deriveNat
  simp only [RationalArithmetic.represents,ZT.toZ_mul,ZT.toZ_ofNat] at eu ev
  simp only [ZT.toZ] at eu ev
  unfold RationalValueBounds.crossLeft at gap ⊢
  ipra_simps
  linear_combination -𝔞(b)*𝔞(F)*𝔞(denominatorOf v)*eu+
    𝔞(b)*𝔞(E)*𝔞(denominatorOf u)*ev+𝔞(E)*𝔞(F)*gap

/-- Exact affine transport of a genuine scalar variation estimate. The
constant term cancels and the nonnegative multiplier remains exact. -/
theorem raw_upper (point : PR 2) (T x M A B s t a b : PTm n)
    (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] RationalValueBounds.upper (distanceSample point T x s) (distanceSample point T x t) a b) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (rawSample point T x M A B s) (rawSample point T x M A B t) (M*a) b := by
  have raw := upper_to_cleared _ _ _ _ _ _ _ _ (GaussianEuclideanDistanceUpperCut.sample_represents point T x s) (GaussianEuclideanDistanceUpperCut.sample_represents point T x t) h
  have scaled := le_mul_mono (le_refl (M*B*B)) raw
  apply upper_of_representations _ _ _ _ _ _ _ _ (raw_denominator_positive point T x B s hB)
    (raw_denominator_positive point T x B t hB) (raw_represents point T x M A B s hB) (raw_represents point T x M A B t hB)
  exact le_congr (by unfold rawDenominator rawNumerator; ipra_ring) (by unfold rawDenominator rawNumerator; ipra_ring)
    (add_le_add_right (b*A*B*denominator point T x s*denominator point T x t) scaled)

theorem raw_radius (point : PR 2) (T x M A B s t a b : PTm n)
    (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] RationalValueBounds.radius (distanceSample point T x s) (distanceSample point T x t) a b) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (rawSample point T x M A B s) (rawSample point T x M A B t) (M*a) b :=
  RationalValueBounds.radius_of_upper _ _ _ _
    (raw_upper point T x M A B s t a b hB (RationalValueBounds.upper_of_radius _ _ _ _ h))
    (raw_upper point T x M A B t s a b hB (RationalValueBounds.upper_of_radius _ _ _ _ (RationalValueBounds.radius_symmetric _ _ _ _ h)))

theorem raw_nonnegative (point : PR 2) (T x M A B s : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (GaussianEuclideanDistanceName.fraction zero one) (rawSample point T x M A B s) :=
  GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _ (le_refl _) (raw_denominator_positive point T x B s hB)
    (GaussianEuclideanDistanceName.fraction_represents _ _ (le_refl _)) (raw_represents point T x M A B s hB)
    (le_congr (mul_zero _).eqSymm (by ipra_ring) (zero_le (rawNumerator point T x M A B s)))

theorem exponent_unit (M k : PTm n) : Γ ⊢[PRAAx] unit (exponent M k) ≐ unit k*unit (normalizer M) := pw_add _ _ _
theorem normalizer_budget (M : PTm n) : Γ ⊢[PRAAx] le M (unit (normalizer M)) :=
  le_trans (Prf.andE₁ (GaussianRootSchedule.binary_length_correct _))
    (GaussianFactorBudget.power_monotone_length _ _ _ (le_succ_self one) (le_add_right _ _))

theorem regularity_budget (M s t : PTm n) : Γ ⊢[PRAAx]
    le ((M*(unit (exponent M s)+unit (exponent M t)))*(unit s*unit t))
      ((unit s+unit t)*(unit (exponent M s)*unit (exponent M t))) := by
  have h := le_mul_mono (normalizer_budget (Γ := Γ) M)
    (le_refl ((unit s+unit t)*unit (normalizer M)*unit s*unit t))
  have hs := natEq (exponent_unit (Γ := Γ) M s)
  have ht := natEq (exponent_unit (Γ := Γ) M t)
  apply le_congr ?_ ?_ h
  · apply deriveNat
    ipra_simps
    rw [hs,ht]
    ring
  · apply deriveNat
    ipra_simps
    rw [hs,ht]
    ring

theorem sample_represents (point : PR 2) (T x M A B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (sample point T x M A B k)
      (ZT.ofNat (rawNumerator point T x M A B (exponent M k))) (rawDenominator point T x B (exponent M k)) :=
  raw_represents point T x M A B (exponent M k) hB

theorem sample_canonical (point : PR 2) (T x M A B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    RationalNormalForm.wellFormed (sample point T x M A B k) := raw_canonical point T x M A B (exponent M k) hB

theorem sample_nonnegative (point : PR 2) (T x M A B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (GaussianEuclideanDistanceName.fraction zero one) (sample point T x M A B k) :=
  raw_nonnegative point T x M A B (exponent M k) hB

/-- Actual distance-name fastness and exact affine variation yield fast
samples at the internally selected observation precisions. -/
theorem sample_radius (point : PR 2) (T x M A B s t : PTm n)
    (hCN : Γ ⊢[PRAAx] pointCN point x) (hT : Γ ⊢[PRAAx] le one (length T)) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (sample point T x M A B s) (sample point T x M A B t)
      (unit s+unit t) (unit s*unit t) :=
  RationalValueBounds.radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive _) (unit_positive _))
    (raw_radius point T x M A B (exponent M s) (exponent M t) _ _ hB
      (GaussianEuclideanDistanceName.sample_radius point T x (exponent M s) (exponent M t) hCN hT))
    (regularity_budget M s t)

def fastScalar (point : PR 2) (T x M A B : PTm n) : Fm PTm n := .all (.all
  (RationalValueBounds.radius
    (sample point (Syn.shift (Syn.shift T)) (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift M)) (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift B)) (var 1))
    (sample point (Syn.shift (Syn.shift T)) (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift M)) (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift B)) (var 0))
    (unit (var 1)+unit (var 0)) (unit (var 1)*unit (var 0))))

@[simp] theorem subst_fastScalar {l : ℕ} (σ : Fin n → PTm l) (point : PR 2) (T x M A B : PTm n) :
    (fastScalar point T x M A B).subst σ = fastScalar point (Syn.subst σ T) (Syn.subst σ x)
      (Syn.subst σ M) (Syn.subst σ A) (Syn.subst σ B) := by simp [fastScalar,Syn.subst_shift,Syn.shift_subst]

theorem fast_scalar (point : PR 2) (T x M A B : PTm n)
    (hCN : Γ ⊢[PRAAx] pointCN point x) (hT : Γ ⊢[PRAAx] le one (length T)) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    fastScalar point T x M A B := by
  refine .allI (.allI ?_)
  have cn : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointCN point (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,GaussianEuclideanDistanceName.subst_pointCN,Syn.shift] using hCN.shift.shift
  have ne : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (length (Syn.shift (Syn.shift T))) := by
    simpa only [Fm.shift,subst_le,subst_length,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Syn.shift] using hT.shift.shift
  have bp : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift B)) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Syn.shift] using hB.shift.shift
  exact sample_radius point _ _ _ _ _ (var 1) (var 0) cn ne bp

def nameData (T x M A B : PTm n) : PTm n := pairT T (pairT x (pairT M (pairT A B)))
def nameBody (point : PR 2) : PTm 2 := sample point (fstT (var 1)) (fstT (sndT (var 1)))
  (fstT (sndT (sndT (var 1)))) (fstT (sndT (sndT (sndT (var 1))))) (sndT (sndT (sndT (sndT (var 1))))) (var 0)
def nameF (point : PR 2) : PR 2 := PTm.toPR (nameBody point)

@[simp] theorem subst_nameData {l : ℕ} (σ : Fin n → PTm l) (T x M A B : PTm n) :
    Syn.subst σ (nameData T x M A B) = nameData (Syn.subst σ T) (Syn.subst σ x) (Syn.subst σ M) (Syn.subst σ A) (Syn.subst σ B) := by
  simp [nameData]

theorem sample_congr (point : PR 2) {T T' x x' M M' A A' B B' k k' : PTm n}
    (hT : Γ ⊢[PRAAx] T ≐ T') (hx : Γ ⊢[PRAAx] x ≐ x') (hM : Γ ⊢[PRAAx] M ≐ M')
    (hA : Γ ⊢[PRAAx] A ≐ A') (hB : Γ ⊢[PRAAx] B ≐ B') (hk : Γ ⊢[PRAAx] k ≐ k') : Γ ⊢[PRAAx]
    sample point T x M A B k ≐ sample point T' x' M' A' B' k' := by
  have e5 : (![T,x,M,A,B,k] : Fin 6 → PTm n) 5 = k := rfl
  have e5' : (![T',x',M',A',B',k'] : Fin 6 → PTm n) 5 = k' := rfl
  simpa only [subst_sample,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,e5,e5',Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (sample point (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6)
      (σ := ![T,x,M,A,B,k]) (σ' := ![T',x',M',A',B',k'])
      (fun i => by fin_cases i; exact hT; exact hx; exact hM; exact hA; exact hB; exact hk)

theorem name_at (point : PR 2) (T x M A B k : PTm n) : Γ ⊢[PRAAx]
    ap2 (nameF point) k (nameData T x M A B) ≐ sample point T x M A B k := by
  have base : Γ ⊢[PRAAx] ap2 (nameF point) k (nameData T x M A B) ≐
      sample point (fstT (nameData T x M A B)) (fstT (sndT (nameData T x M A B)))
        (fstT (sndT (sndT (nameData T x M A B)))) (fstT (sndT (sndT (sndT (nameData T x M A B)))))
        (sndT (sndT (sndT (sndT (nameData T x M A B))))) k := by
    simpa [nameF,nameBody,ap2] using toPR_eq (Γ := Γ) (nameBody point) ![k,nameData T x M A B]
  have t1 : Γ ⊢[PRAAx] sndT (nameData T x M A B) ≐ pairT x (pairT M (pairT A B)) := snd_pair _ _
  have t2 : Γ ⊢[PRAAx] sndT (sndT (nameData T x M A B)) ≐ pairT M (pairT A B) :=
    (congrSnd t1).eqTrans (snd_pair _ _)
  have t3 : Γ ⊢[PRAAx] sndT (sndT (sndT (nameData T x M A B))) ≐ pairT A B :=
    (congrSnd t2).eqTrans (snd_pair _ _)
  exact base.eqTrans (sample_congr point (fst_pair _ _) ((congrFst t1).eqTrans (fst_pair _ _))
    ((congrFst t2).eqTrans (fst_pair _ _)) ((congrFst t3).eqTrans (fst_pair _ _))
    ((congrSnd t3).eqTrans (snd_pair _ _)) (.eqRefl _))

def scalarCN (f : PR 2) (x : PTm n) : Fm PTm n := .all (.all
  (RationalValueBounds.radius (ap2 f (var 1) (Syn.shift (Syn.shift x))) (ap2 f (var 0) (Syn.shift (Syn.shift x)))
    (unit (var 1)+unit (var 0)) (unit (var 1)*unit (var 0))))

@[simp] theorem subst_scalarCN {l : ℕ} (σ : Fin n → PTm l) (f : PR 2) (x : PTm n) :
    (scalarCN f x).subst σ = scalarCN f (Syn.subst σ x) := by simp [scalarCN,Syn.subst_shift,Syn.shift_subst]

theorem name_fast (point : PR 2) (T x M A B : PTm n)
    (hCN : Γ ⊢[PRAAx] pointCN point x) (hT : Γ ⊢[PRAAx] le one (length T)) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    scalarCN (nameF point) (nameData T x M A B) := by
  refine .allI (.allI ?_)
  have cn : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointCN point (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,GaussianEuclideanDistanceName.subst_pointCN,Syn.shift] using hCN.shift.shift
  have ne : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (length (Syn.shift (Syn.shift T))) := by
    simpa only [Fm.shift,subst_le,subst_length,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Syn.shift] using hT.shift.shift
  have bp : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift B)) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Syn.shift] using hB.shift.shift
  simpa only [Syn.shift,subst_nameData] using
    RationalValueBounds.radius_congr (name_at point (Syn.shift (Syn.shift T)) (Syn.shift (Syn.shift x))
      (Syn.shift (Syn.shift M)) (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift B)) (var 1)).eqSymm
      (name_at point (Syn.shift (Syn.shift T)) (Syn.shift (Syn.shift x))
        (Syn.shift (Syn.shift M)) (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift B)) (var 0)).eqSymm
      (.eqRefl _) (.eqRefl _) (sample_radius point _ _ _ _ _ (var 1) (var 0) cn ne bp)

/-- The returned normalized numerator is literally the canonical scalar
arithmetic M*d_s+A/B, rather than a separate code with an assumed meaning. -/
theorem raw_affine (point : PR 2) (T x M A B s : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    rawSample point T x M A B s ≐ RationalArithmetic.add
      (RationalArithmetic.multiply (GaussianEuclideanDistanceName.fraction M one) (distanceSample point T x s))
      (GaussianEuclideanDistanceName.fraction A B) := by
  have epos := denominator_positive (Γ := Γ) point T x s
  have mr := RationalRepresentations.represents_multiply (Γ := Γ) _ _ _ _ _ _
    (GaussianEuclideanDistanceName.fraction_represents M one (le_refl _)) (GaussianEuclideanDistanceUpperCut.sample_represents point T x s)
  have ar := RationalRepresentations.represents_add (Γ := Γ) _ _ _ _ _ _ mr
    (GaussianEuclideanDistanceName.fraction_represents A B hB)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (raw_canonical point T x M A B s hB)
    (RationalArithmetic.add_guard _ _) (raw_represents point T x M A B s hB) ar
    (raw_denominator_positive point T x B s hB) (positive_product _ _ (positive_product _ _ (le_refl one) epos) hB)
  apply ZT.derive
  simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]
  unfold rawNumerator rawDenominator
  ipra_simps
  ring

theorem name_nonnegative (point : PR 2) (T x M A B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (GaussianEuclideanDistanceName.fraction zero one) (ap2 (nameF point) k (nameData T x M A B)) :=
  RationalArgmin.rationalLE_congr (.eqRefl _) (name_at point T x M A B k).eqSymm (sample_nonnegative point T x M A B k hB)

theorem name_canonical (point : PR 2) (T x M A B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    RationalNormalForm.wellFormed (ap2 (nameF point) k (nameData T x M A B)) := by
  have h := Prf.eqSubst (Ax := PRAAx) (Γ := Γ) (RationalNormalForm.wellFormed (var 0) : Fm PTm 1)
    (σ := ![sample point T x M A B k]) (σ' := ![ap2 (nameF point) k (nameData T x M A B)])
    (fun i => by fin_cases i; exact (name_at point T x M A B k).eqSymm)
    (by simpa only [RationalNormalForm.subst_wellFormed,Syn.subst_var,Matrix.cons_val_zero] using sample_canonical point T x M A B k hB)
  simpa only [RationalNormalForm.subst_wellFormed,Syn.subst_var,Matrix.cons_val_zero] using h

theorem linear_distance_name_closed (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (pointCN point (var 1) ⟶ le one (length (var 0)) ⟶ le one (var 4) ⟶
      scalarCN (nameF point) (nameData (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (name_fast _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem linear_distance_sample_fast_closed (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (pointCN point (var 1) ⟶ le one (length (var 0)) ⟶ le one (var 4) ⟶
      fastScalar point (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (fast_scalar _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem linear_distance_nonnegative_canonical_closed (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 4) ⟶
      ((RationalArgmin.rationalLE (GaussianEuclideanDistanceName.fraction zero one)
        (ap2 (nameF point) (var 5) (nameData (var 0) (var 1) (var 2) (var 3) (var 4)))) ⋏
       RationalNormalForm.wellFormed (ap2 (nameF point) (var 5) (nameData (var 0) (var 1) (var 2) (var 3) (var 4))))) :=
  closeUniv 6 (.impI (.andI (name_nonnegative _ _ _ _ _ _ _ Prf.hyp0) (name_canonical _ _ _ _ _ _ _ Prf.hyp0)))

theorem linear_distance_literal_affine_closed (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 4) ⟶ rawSample point (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐
      RationalArithmetic.add
        (RationalArithmetic.multiply (GaussianEuclideanDistanceName.fraction (var 2) one)
          (distanceSample point (var 0) (var 1) (var 5))) (GaussianEuclideanDistanceName.fraction (var 3) (var 4))) :=
  closeUniv 6 (.impI (raw_affine _ _ _ _ _ _ _ Prf.hyp0))

theorem linear_distance_program_closed (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (ap2 (nameF point) (var 5) (nameData (var 0) (var 1) (var 2) (var 3) (var 4)) ≐
      sample point (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) := closeUniv 6 (name_at _ _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianLinearDistanceName
