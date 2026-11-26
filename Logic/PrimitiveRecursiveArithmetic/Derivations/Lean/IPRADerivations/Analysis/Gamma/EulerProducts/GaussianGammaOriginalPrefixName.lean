import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaOriginalPrefixRegularity

/-!
# A genuine name for the original C19 finite coefficient prefix

The actual raw observation remains the original prefixValue program.
Its proved numerical modulus supplies an explicit FastValueCut clock.
The resulting genuine name has the original C19 comparison to C7 with
the exact M_(2R)*2^(-d-1) tail and independent observation precisions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaOriginalPrefixName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaOriginalC19Prefix (prefixValue)
open GaussianGammaOriginalPrefixRegularity (modulus)
open GaussianGammaCanonicalExponent (source)
open GaussianGammaC9Bound (majorant)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ app)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rawData (z R B d : PTm n) : PTm n := pairT z (pairT R (pairT B d))
def rawValue (p x : PTm n) : PTm n := app GaussianGammaOriginalC19Prefix.prefixF
  ![p,fstT x,fstT (sndT x),fstT (sndT (sndT x)),sndT (sndT (sndT x))]
def rawF : PR 2 := PTm.toPR (rawValue (var 0) (var 1))
def nameF : PR 2 := GaussianFastValueCut.nameF rawF
def data (z R B d : PTm n) : PTm n := GaussianFastValueCut.nameData (modulus R d) (rawData z R B d)
def clock (p R d : PTm n) : PTm n := GaussianFastValueCut.exponent (modulus R d) p
def sample (p z R B d : PTm n) : PTm n := ap2 nameF p (data z R B d)
@[simp] theorem subst_rawData {l : ℕ} (σ : Fin n → PTm l) (z R B d : PTm n) :
    Syn.subst σ (rawData z R B d) = rawData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ d) := by simp [rawData]
@[simp] theorem subst_rawValue {l : ℕ} (σ : Fin n → PTm l) (p x : PTm n) :
    Syn.subst σ (rawValue p x) = rawValue (Syn.subst σ p) (Syn.subst σ x) := by
  simp only [rawValue,PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> simp
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (z R B d : PTm n) :
    Syn.subst σ (data z R B d) = data (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ d) := by simp [data]
@[simp] theorem subst_clock {l : ℕ} (σ : Fin n → PTm l) (p R d : PTm n) :
    Syn.subst σ (clock p R d) = clock (Syn.subst σ p) (Syn.subst σ R) (Syn.subst σ d) := by simp [clock]
@[simp] theorem subst_sample {l : ℕ} (σ : Fin n → PTm l) (p z R B d : PTm n) :
    Syn.subst σ (sample p z R B d) = sample (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ d) := by simp [sample]

theorem raw_value_at (p z R B d : PTm n) : Γ ⊢[PRAAx] rawValue p (rawData z R B d) ≐ prefixValue p z R B d := by
  have t := snd_pair (Γ := Γ) z (pairT R (pairT B d))
  have u := (congrSnd t).eqTrans (snd_pair R (pairT B d))
  have decoded : Γ ⊢[PRAAx] rawValue p (rawData z R B d) ≐ app GaussianGammaOriginalC19Prefix.prefixF ![p,z,R,B,d] := by
    unfold rawValue
    apply congrApp GaussianGammaOriginalC19Prefix.prefixF
    intro i
    fin_cases i
    · exact .eqRefl _
    · exact fst_pair _ _
    · exact (congrFst t).eqTrans (fst_pair R (pairT B d))
    · exact (congrFst u).eqTrans (fst_pair B d)
    · exact (congrSnd u).eqTrans (snd_pair B d)
  exact decoded.eqTrans (GaussianGammaOriginalC19Prefix.prefix_program p z R B d)

theorem raw_at (p z R B d : PTm n) : Γ ⊢[PRAAx] ap2 rawF p (rawData z R B d) ≐ prefixValue p z R B d :=
  (show Γ ⊢[PRAAx] ap2 rawF p (rawData z R B d) ≐ rawValue p (rawData z R B d) by
    simpa only [rawF,ap2,subst_rawValue,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
      toPR_eq (Γ := Γ) (rawValue (var 0) (var 1) : PTm 2) ![p,rawData z R B d]).eqTrans (raw_value_at p z R B d)

theorem raw_regular (z R B d : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    GaussianFastValueCut.regular rawF (modulus R d) (rawData z R B d) := by
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B)) := by
    simpa [Fm.shift,Syn.shift] using h.shift.shift
  refine .allI (.allI ?_)
  have actual := distance_congr (Γ := (Γ.map Fm.shift).map Fm.shift)
    (raw_at (var 1) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift d))).eqSymm
    (raw_at (var 0) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift d))).eqSymm
    (.eqRefl _) (.eqRefl _)
      (GaussianGammaOriginalPrefixRegularity.original_prefix_regularity (var 1) (var 0)
        (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift d)) hs)
  simpa only [GaussianFastValueCut.regular,Syn.shift,subst_rawData,GaussianGammaOriginalPrefixRegularity.subst_modulus,
    GaussianGammaInputPrecisionNorm.radiusNumerator,GaussianGammaInputPrecisionNorm.radiusDenominator,unit] using actual

theorem name_regular (z R B d : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx] pointCN nameF (data z R B d) :=
  GaussianFastValueCut.name_fast rawF (modulus R d) (rawData z R B d) (raw_regular z R B d h)

theorem sample_at (p z R B d : PTm n) : Γ ⊢[PRAAx] sample p z R B d ≐ prefixValue (clock p R d) z R B d :=
  (GaussianFastValueCut.name_at rawF (modulus R d) (rawData z R B d) p).eqTrans
    ((GaussianNameArithmetic.recode_congr (raw_at (clock p R d) z R B d)).eqTrans
      (GaussianNamedSmallPerturbationTransport.recode_fixed _ (GaussianRationalPowerExpansion.prefix_canonical _ _ _ _)))
theorem clock_later (p R d : PTm n) : Γ ⊢[PRAAx] le p (clock p R d) := le_add_right _ _

theorem rate_budget (D N p q s : PTm n) (hq : Γ ⊢[PRAAx] le q s) : Γ ⊢[PRAAx]
    le (rateNumerator D N p s*rateDenominator N p q) (rateNumerator D N p q*rateDenominator N p s) := by
  have grow : Γ ⊢[PRAAx] le (unit q) (unit s) := GaussianFactorBudget.power_monotone_length two q s (le_succ_self one) hq
  have e := natEq (eq_add_of_le grow)
  refine le_of_eq_add (d := N*N*unit p*unit p*monus (unit s) (unit q)) ?_
  apply deriveNat
  unfold rateNumerator rateDenominator
  ipra_simps
  rw [e]
  ring

theorem original_named_C19_bound (p q z R B d : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    distanceBounded (GaussianGammaC7Name.sample p z R B) (sample q z R B d)
      (rateNumerator (majorant (two*R)) (GaussianGammaOriginalC19Prefix.denominator d) p q)
      (rateDenominator (GaussianGammaOriginalC19Prefix.denominator d) p q) := by
  have hD : Γ ⊢[PRAAx] le one (GaussianGammaOriginalC19Prefix.denominator d) := unit_positive (succ d)
  exact distance_radius_mono _ _ _ _ _ _
    (GaussianNamedInverseRate.denominator_positive _ p (clock q R d) hD)
    (GaussianNamedInverseRate.denominator_positive _ p q hD)
    (rate_budget _ _ p q (clock q R d) (clock_later q R d))
    (distance_congr (.eqRefl _) (sample_at q z R B d).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianGammaOriginalC19Prefix.original_C19_observation_bound p (clock q R d) z R B d h))

theorem original_actual_C19_prefix_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) ⟶ pointCN nameF (data (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (name_regular _ _ _ _ Prf.hyp0))
theorem original_actual_named_C19_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 2) (var 3) (var 4) ⟶ distanceBounded
      (GaussianGammaC7Name.sample (var 0) (var 2) (var 3) (var 4)) (sample (var 1) (var 2) (var 3) (var 4) (var 5))
      (rateNumerator (majorant (two*var 3)) (GaussianGammaOriginalC19Prefix.denominator (var 5)) (var 0) (var 1))
      (rateDenominator (GaussianGammaOriginalC19Prefix.denominator (var 5)) (var 0) (var 1))) :=
  closeUniv 6 (.impI (original_named_C19_bound _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaOriginalPrefixName
