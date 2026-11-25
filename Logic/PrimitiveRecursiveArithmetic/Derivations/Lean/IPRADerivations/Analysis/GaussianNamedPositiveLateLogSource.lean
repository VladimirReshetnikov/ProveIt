import IPRADerivations.Analysis.GaussianNamedPositiveLogarithm
import IPRADerivations.Analysis.GaussianNamedRightHalfPlane
import IPRADerivations.Analysis.RationalRepresentedUpper

/-!
# Positive logarithm input from the actual late samples of a real name

The retiming reads the original program after its certified positivity
threshold. It preserves the original name and gives each retained sample
the exact compact guards needed by the positive logarithm evaluator.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedPositiveLateLogSource

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (re)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN fraction fraction_represents)
open GaussianExponentialReference (unit_monotone)
open GaussianNameBounds (U sample_bound)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans point_at)
open GaussianNamedRightHalfPlane (source threshold actual_late_margin)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (canonical canonical_congr positive_product)
open GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open GaussianRationalMetric (distanceBounded)
open GaussianSignedNameExponentialOrder (realSamples real_sample_at)
open RationalValueBounds (upper upper_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def retimedF (f : PR 2) : PR 2 :=
  PTm.toPR (ap2 f (var 0+sndT (var 1)) (fstT (var 1)) : PTm 2)

def retimedData (x A : PTm n) : PTm n := pairT x (threshold A)

@[simp] theorem subst_retimedData {m : ℕ} (σ : Fin n → PTm m) (x A : PTm n) :
    Syn.subst σ (retimedData x A) = retimedData (Syn.subst σ x) (Syn.subst σ A) := by
  simp [retimedData]

theorem sample_at (f : PR 2) (p x A : PTm n) :
    Γ ⊢[PRAAx] ap2 (retimedF f) p (retimedData x A) ≐ ap2 f (p+threshold A) x := by
  let d := retimedData x A
  have time : Syn.subst (![p,d] : Fin 2 → PTm n) (var 0+sndT (var 1)) = p+sndT d := by
    rw [LeanProofs.IPRA.PTm.subst_add]
    simp only [subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  have raw : Γ ⊢[PRAAx] ap2 (retimedF f) p d ≐ ap2 f (p+sndT d) (fstT d) := by
    have program := toPR_eq (Γ := Γ) (ap2 f (var 0+sndT (var 1)) (fstT (var 1)) : PTm 2) ![p,d]
    rw [subst_ap2,time,subst_fstT,Syn.subst_var] at program
    exact program
  exact raw.eqTrans (congrAp2 f (congrAdd (.eqRefl p) (snd_pair x (threshold A))) (fst_pair x (threshold A)))

private theorem original_observations (f : PR 2) (p q x A : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] distanceBounded (ap2 f p x) (ap2 (retimedF f) q (retimedData x A))
      (unit p+unit q) (unit p*unit q) := by
  let r := q+threshold A
  have grow : Γ ⊢[PRAAx] le (unit q) (unit r) := unit_monotone (le_add_right q (threshold A))
  have comparison := point_at f x p r hf
  refine distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive r))
    (positive_product _ _ (unit_positive p) (unit_positive q)) ?_
    (distance_congr (.eqRefl _) (sample_at f q x A).eqSymm (.eqRefl _) (.eqRefl _) comparison)
  ipra_le 𝔞(unit p*unit p)*sl grow

theorem original_cross (f : PR 2) (x A : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] crossEquivalent f (retimedF f) x (retimedData x A) := by
  refine .allI (.allI ?_)
  let sh (a : PTm n) := Syn.shift (Syn.shift a)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointCN f (sh x) := by
    simpa [Fm.shift,Syn.shift,sh] using hf.shift.shift
  simpa only [crossEquivalent,subst_retimedData,Syn.shift,sh] using
    original_observations f (var 1) (var 0) (sh x) (sh A) hs

theorem name_regular (f : PR 2) (x A : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] pointCN (retimedF f) (retimedData x A) := by
  have h := original_cross f x A hf
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ h) h

private theorem exact_late_lower (f : PR 2) (x A p : PTm n) (hs : Γ ⊢[PRAAx] source f x A)
    (hp : Γ ⊢[PRAAx] le (threshold A) p) :
    Γ ⊢[PRAAx] upper (fraction one (two*A)) (fstT (ap2 f p x)) zero one := by
  let q := ap2 f p x
  let E := two*A
  let B := rawDen q
  let v := re (rawGaussian q)
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ (le_succ_self one) hs.andE₂.andE₁
  have hm : Γ ⊢[PRAAx] zle (ZT.ofNat B) (ZT.ofNat E*v) := actual_late_margin f x A p hs hp
  apply RationalRepresentedUpper.from_signed (fraction one E) (fstT q) (ZT.ofNat one) v E B zero one
    hE (raw_den_positive q) (fraction_represents one E hE) (raw_represents q).andE₁
  apply PolynomialBisection.zle_congr (h := hm)
  · simp only [RationalRepresentedUpper.left,ZT.toZ_mul,ZT.toZ_ofNat]
    ipra_simps
    ring
  · simp only [RationalRepresentedUpper.right,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]
    ipra_simps
    ring

theorem late_sample_admissible (f : PR 2) (x A p : PTm n) (hs : Γ ⊢[PRAAx] source f x A)
    (hr : Γ ⊢[PRAAx] realSamples f x) (hp : Γ ⊢[PRAAx] le (threshold A) p) :
    Γ ⊢[PRAAx] canonical (ap2 f p x) ⋏
      GaussianPositiveCompactInputDecoding.source (ap2 f p x) (two*A) (U f x) := by
  have sample := real_sample_at f x p hr
  exact .andI sample.andE₁ (.andI sample.andE₂
    (.andI (positive_product _ _ (le_succ_self one) hs.andE₂.andE₁)
      (.andI (exact_late_lower f x A p hs hp) (sample_bound f x p hs.andE₁))))

private theorem retimed_admissible_at (f : PR 2) (x A p : PTm n) (hs : Γ ⊢[PRAAx] source f x A)
    (hr : Γ ⊢[PRAAx] realSamples f x) :
    Γ ⊢[PRAAx] canonical (ap2 (retimedF f) p (retimedData x A)) ⋏
      GaussianPositiveCompactInputDecoding.source (ap2 (retimedF f) p (retimedData x A)) (two*A) (U f x) := by
  have source := late_sample_admissible f x A (p+threshold A) hs hr (le_add_left (threshold A) p)
  have eq := sample_at (Γ := Γ) f p x A
  exact .andI (canonical_congr eq source.andE₁) (.andI
    (RationalGaussianEmbedding.axis_congr eq.eqSymm source.andE₂.andE₁)
    (.andI source.andE₂.andE₂.andE₁ (.andI
      (upper_congr (.eqRefl _) (congrFst eq).eqSymm (.eqRefl _) (.eqRefl _) source.andE₂.andE₂.andE₂.andE₁)
      (GaussianRationalReciprocal.bound_congr eq.eqSymm (.eqRefl _) (.eqRefl _) source.andE₂.andE₂.andE₂.andE₂))))

theorem positive_source (f : PR 2) (x A : PTm n) (hs : Γ ⊢[PRAAx] source f x A)
    (hr : Γ ⊢[PRAAx] realSamples f x) :
    Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source (retimedF f) (retimedData x A) (two*A) (U f x) := by
  refine .andI (name_regular f x A hs.andE₁)
    (.andI (positive_product _ _ (le_succ_self one) hs.andE₂.andE₁) (.allI ?_))
  have hss : Γ.map Fm.shift ⊢[PRAAx] source f (Syn.shift x) (Syn.shift A) := by
    simpa [Fm.shift,Syn.shift] using hs.shift
  have hrs : Γ.map Fm.shift ⊢[PRAAx] realSamples f (Syn.shift x) := by
    simpa [Fm.shift,Syn.shift] using hr.shift
  simpa only [GaussianNamedPositiveLogarithm.admissible,Syn.shift,subst_retimedData,GaussianNameBounds.subst_U,
    PTm.subst_mul,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    retimed_admissible_at f (Syn.shift x) (Syn.shift A) (var 0) hss hrs

theorem actual_original_positive_late_retiming_sample_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap2 (retimedF f) (var 0) (retimedData (var 1) (var 2)) ≐ ap2 f (var 0+threshold (var 2)) (var 1)) :=
  closeUniv 3 (sample_at f _ _ _)

theorem actual_original_positive_late_log_source_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((source f (var 0) (var 1) ⋏ realSamples f (var 0)) ⟶
      (crossEquivalent f (retimedF f) (var 0) (retimedData (var 0) (var 1)) ⋏
        GaussianNamedPositiveLogarithm.source (retimedF f) (retimedData (var 0) (var 1)) (two*var 1) (U f (var 0)))) :=
  closeUniv 2 (.impI (.andI (original_cross f _ _ Prf.hyp0.andE₁.andE₁)
    (positive_source f _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianNamedPositiveLateLogSource
