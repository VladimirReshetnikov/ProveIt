import IPRADerivations.Analysis.GaussianUpperTimeLogarithmBound
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual integer logarithmic powers above time one

The unchanged original logarithm observations and the exact finite
harmonic reference give a sharp rational time-power majorant. The
numerical exponent j is unrestricted. A computed original power clock
absorbs the proved gain into one dyadic and returns a genuine regular
name using the existing FastValueCut program.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianUpperTimeLogarithmPower

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianPositiveRationalLogarithm (source sample logF name_regular)
open GaussianRationalReciprocal (power bound_congr bounded_power)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianEuclideanDistanceName (pointCN)
open GaussianFastValueCut (exponent)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def gain (j a : PTm n) : PTm n := j*pw (a+one) (pred j)
def rawPower (p j a b : PTm n) : PTm n := power (sample p a b) j
def rawTerm (p x : PTm n) : PTm n := rawPower p (fstT x) (fstT (sndT x)) (sndT (sndT x))
def rawF : PR 2 := PTm.toPR (rawTerm (var 0) (var 1))
def inputData (j a b : PTm n) : PTm n := pairT j (pairT a b)
def nameF : PR 2 := GaussianFastValueCut.nameF rawF
def data (j a b : PTm n) : PTm n := GaussianFastValueCut.nameData (gain j a) (inputData j a b)
def clock (p j a : PTm n) : PTm n := exponent (gain j a) p

@[simp] theorem subst_gain {m : ℕ} (σ : Fin n → PTm m) (j a : PTm n) :
    Syn.subst σ (gain j a) = gain (Syn.subst σ j) (Syn.subst σ a) := by simp [gain]
@[simp] theorem subst_rawPower {m : ℕ} (σ : Fin n → PTm m) (p j a b : PTm n) :
    Syn.subst σ (rawPower p j a b) = rawPower (Syn.subst σ p) (Syn.subst σ j) (Syn.subst σ a) (Syn.subst σ b) := by simp [rawPower]
@[simp] theorem subst_rawTerm {m : ℕ} (σ : Fin n → PTm m) (p x : PTm n) :
    Syn.subst σ (rawTerm p x) = rawTerm (Syn.subst σ p) (Syn.subst σ x) := by simp [rawTerm]
@[simp] theorem subst_inputData {m : ℕ} (σ : Fin n → PTm m) (j a b : PTm n) :
    Syn.subst σ (inputData j a b) = inputData (Syn.subst σ j) (Syn.subst σ a) (Syn.subst σ b) := by simp [inputData]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (j a b : PTm n) :
    Syn.subst σ (data j a b) = data (Syn.subst σ j) (Syn.subst σ a) (Syn.subst σ b) := by simp [data]
@[simp] theorem subst_clock {m : ℕ} (σ : Fin n → PTm m) (p j a : PTm n) :
    Syn.subst σ (clock p j a) = clock (Syn.subst σ p) (Syn.subst σ j) (Syn.subst σ a) := by simp [clock]

theorem raw_at (p j a b : PTm n) : Γ ⊢[PRAAx] ap2 rawF p (inputData j a b) ≐ rawPower p j a b := by
  have first : Γ ⊢[PRAAx] ap2 rawF p (inputData j a b) ≐ rawTerm p (inputData j a b) :=
    by simpa [rawF,ap2] using toPR_eq (Γ := Γ) (rawTerm (var 0) (var 1) : PTm 2) ![p,inputData j a b]
  apply first.eqTrans
  ipra_congr (rawPower (var 0) (var 1) (var 2) (var 3) : PTm 4) with
    [.eqRefl p, (show _ ⊢[PRAAx] fstT (inputData j a b) ≐ j from fst_pair _ _),
      (show _ ⊢[PRAAx] fstT (sndT (inputData j a b)) ≐ a from (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)),
      (show _ ⊢[PRAAx] sndT (sndT (inputData j a b)) ≐ b from (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))] using [rawTerm]

theorem original_uniform_bound (p a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hba : Γ ⊢[PRAAx] le b a) : Γ ⊢[PRAAx]
    bounded (sample p a b) (a+one) one :=
  bounded_radius_mono _ _ _ _ _ (positive_product _ _ hs.andE₂ (unit_positive p)) (le_refl one)
    (by ipra_le (𝔞 a*𝔞(unit p))*sl hs.andE₂+𝔞 b*sl (unit_positive (Γ := Γ) p))
    (GaussianUpperTimeLogarithmBound.original_sample_bound p a b hs hba)

theorem harmonic_uniform_bound (p a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hba : Γ ⊢[PRAAx] le b a) : Γ ⊢[PRAAx]
    bounded (GaussianHarmonicLogarithmName.sample p a b) (a+one) one :=
  bounded_radius_mono _ _ _ _ _ hb (le_refl one)
    (by ipra_le 𝔞 a*sl hb+𝔞 b)
    (GaussianUpperTimeLogarithmBound.harmonic_sample_bound p a b hb hba)

theorem original_harmonic_power_distance (p q j a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hba : Γ ⊢[PRAAx] le b a) : Γ ⊢[PRAAx]
    distanceBounded (rawPower p j a b) (power (GaussianHarmonicLogarithmName.sample q a b) j)
      (gain j a*(unit p+unit q)) (unit p*unit q) :=
  distance_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianRationalPowerDifference.power_distance_bound _ _ (a+one) _ _ j
      (positive_product _ _ (unit_positive p) (unit_positive q))
      (original_uniform_bound p a b hs hba) (harmonic_uniform_bound q a b hs.andE₂ hba)
      (GaussianHarmonicLogarithmName.independent_original p q a b hs))

theorem original_power_slack (p q j a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hba : Γ ⊢[PRAAx] le b a) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (rawPower p j a b)
      (pw a j*unit p+gain j a*pw b j) (pw b j*unit p) (gain j a) q := by
  have hb := GaussianPolynomialPerturbation.power_positive b j hs.andE₂
  have near := original_harmonic_power_distance p q j a b hs hba
  have exactBound := bounded_power _ a b j hs.andE₂ (GaussianUpperTimeLogarithmBound.harmonic_sample_bound q a b hs.andE₂ hba)
  have joined := GaussianReconstructionRoots.norm_from_distance _ _ _ _ (pw a j) (pw b j)
    (positive_product _ _ (unit_positive p) (unit_positive q)) hb near exactBound
  exact bound_congr (.eqRefl _) (by dsimp only [unit]; ipra_ring) (by dsimp only [unit]; ipra_ring) joined

/-- This is the literal j-th power of the unchanged original log sample,
with its actual amplification gain and requested precision retained. -/
theorem original_power_bound (p j a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hba : Γ ⊢[PRAAx] le b a) : Γ ⊢[PRAAx]
    bounded (rawPower p j a b) (pw a j*unit p+gain j a*pw b j) (pw b j*unit p) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ (gain j a)
    (positive_product _ _ (GaussianPolynomialPerturbation.power_positive b j hs.andE₂) (unit_positive p)) (original_power_slack p _ j a b hs hba)

theorem original_power_regularity (p q j a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hba : Γ ⊢[PRAAx] le b a) : Γ ⊢[PRAAx]
    distanceBounded (rawPower p j a b) (rawPower q j a b) (gain j a*(unit p+unit q)) (unit p*unit q) :=
  distance_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianRationalPowerDifference.power_distance_bound _ _ (a+one) _ _ j
      (positive_product _ _ (unit_positive p) (unit_positive q))
      (original_uniform_bound p a b hs hba) (original_uniform_bound q a b hs hba)
      (GaussianNameEquivalence.point_at logF (GaussianPositiveRationalLogarithm.data a b) p q (name_regular a b hs)))

theorem raw_regular (j a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hba : Γ ⊢[PRAAx] le b a) : Γ ⊢[PRAAx]
    GaussianFastValueCut.regular rawF (gain j a) (inputData j a b) := by
  refine .allI (.allI ?_)
  have ss : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (Syn.shift (Syn.shift a)) (Syn.shift (Syn.shift b)) :=
    by simpa [Fm.shift,Syn.shift] using hs.shift.shift
  have bs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le (Syn.shift (Syn.shift b)) (Syn.shift (Syn.shift a)) :=
    by simpa [Fm.shift,Syn.shift] using hba.shift.shift
  simpa only [GaussianFastValueCut.regular,Syn.shift,subst_gain,subst_inputData] using
    distance_congr (raw_at (var 1) (Syn.shift (Syn.shift j)) (Syn.shift (Syn.shift a)) (Syn.shift (Syn.shift b))).eqSymm
      (raw_at (var 0) (Syn.shift (Syn.shift j)) (Syn.shift (Syn.shift a)) (Syn.shift (Syn.shift b))).eqSymm (.eqRefl _) (.eqRefl _)
      (original_power_regularity (var 1) (var 0) (Syn.shift (Syn.shift j)) (Syn.shift (Syn.shift a)) (Syn.shift (Syn.shift b)) ss bs)

theorem name_regular (j a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hba : Γ ⊢[PRAAx] le b a) : Γ ⊢[PRAAx]
    pointCN nameF (data j a b) := GaussianFastValueCut.name_fast rawF (gain j a) (inputData j a b) (raw_regular j a b hs hba)

theorem sample_at (p j a b : PTm n) : Γ ⊢[PRAAx] ap2 nameF p (data j a b) ≐ rawPower (clock p j a) j a b :=
  (GaussianFastValueCut.name_at rawF (gain j a) (inputData j a b) p).eqTrans
    ((GaussianNameArithmetic.recode_congr (raw_at (clock p j a) j a b)).eqTrans
      (GaussianExponentialReference.recode_fixed _ (GaussianRationalReciprocal.power_canonical _ _)))

theorem original_named_power_bound (p j a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hba : Γ ⊢[PRAAx] le b a) : Γ ⊢[PRAAx]
    bounded (ap2 nameF p (data j a b)) (pw a j*unit p+pw b j) (pw b j*unit p) := by
  have hb := GaussianPolynomialPerturbation.power_positive b j hs.andE₂
  have query : Γ ⊢[PRAAx] le (gain j a*unit p) (unit (clock p j a)) := GaussianFastValueCut.query_budget _ _
  have reduced : Γ ⊢[PRAAx] bounded (rawPower (clock p j a) j a b) (pw a j*unit p+pw b j) (pw b j*unit p) :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ hb (unit_positive (clock p j a)))
    (positive_product _ _ hb (unit_positive p))
    (by ipra_le (𝔞(pw b j)*𝔞(pw b j))*sl query)
    (original_power_bound (clock p j a) j a b hs hba)
  exact bound_congr (sample_at p j a b).eqSymm (.eqRefl _) (.eqRefl _) reduced

theorem actual_original_upper_time_logarithm_power_name_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((source (var 1) (var 2) ⋏ le (var 2) (var 1)) ⟶ pointCN nameF (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (name_regular _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem actual_original_upper_time_logarithm_named_power_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((source (var 2) (var 3) ⋏ le (var 3) (var 2)) ⟶
      bounded (ap2 nameF (var 0) (data (var 1) (var 2) (var 3)))
        (pw (var 2) (var 1)*unit (var 0)+pw (var 3) (var 1)) (pw (var 3) (var 1)*unit (var 0))) :=
  closeUniv 4 (.impI (original_named_power_bound _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianUpperTimeLogarithmPower
