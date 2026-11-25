import IPRADerivations.Analysis.GaussianGammaNegativeIntervalCriticalComparison
import IPRADerivations.Analysis.GaussianGammaNegativeIntervalDerivativeTargetRescale
import IPRADerivations.Analysis.GaussianGammaNegativeIntervalLogAbsoluteProperness
import IPRADerivations.Analysis.LogisticName

/-!
# Stationary log-absolute Gamma comparison at arbitrary rational inputs

Clear the two input denominators, preserve the pole margins and the
derivative residual, then apply the common-denominator comparison.
Transport of independent observations retains the original error budget
and the squared rational separation. Equal inputs have zero separation.
-/

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalCriticalRationalComparison

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCompactCutoffSplit (add_data_congr)
open GaussianGammaInputProperness (code_data_cross)
open GaussianGammaMinimumChord (absDelta)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeCriticalEndpoints (mesh)
open GaussianGammaNegativeIntervalChordInverse (poleMargin)
open GaussianGammaNegativeIntervalCriticalComparison (base_guard base_margin)
open GaussianGammaNegativeIntervalCriticalDerivativeZero (argumentNumerator argumentDenominator)
open GaussianGammaNegativeIntervalCriticalQuotientZero (stage)
open GaussianGammaNegativeIntervalLogAbsolute (name_regular)
open GaussianGammaNegativeIntervalLogAbsoluteProperness (log_absolute_rescale)
open GaussianGammaNegativeIntervalRescale (guard_rescale)
open GaussianGammaNegativeIntervalStationaryBudget (comparisonCost)
open GaussianNameEquivalence (cross_at cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (sum_right_error zeroF zero_fast)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator denominator_positive)
open GaussianNamedRealOrderTransport (upperSlack precision remove_upper_slack)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qadd qzero positive_product)
open GaussianRationalSyntheticDivision (qadd_congr qzero_add)
open GaussianStirlingGammaFractionalIncrementObservations (scalar_upper)
open RationalValueBounds (upper upper_mono upper_congr upper_triangle)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (monus num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "L" => GaussianGammaNegativeIntervalLogAbsolute.nameF
local notation "ld" => GaussianGammaNegativeIntervalLogAbsolute.nameData
local notation "T" => GaussianGammaNegativeIntervalDerivativeTarget.nameF
local notation "td" => GaussianGammaNegativeIntervalDerivativeTarget.data
local notation "g" => GaussianGammaNegativeIntervalLogThinChord.margin

def rationalMargin (a b c d : PTm n) : PTm n :=
  fraction (absDelta (d*a) (b*c)*absDelta (d*a) (b*c)) (num 16*(b*d)*(b*d))

@[simp] theorem subst_rationalMargin {m : ℕ} (σ : Fin n → PTm m) (a b c d : PTm n) :
    Syn.subst σ (rationalMargin a b c d) = rationalMargin (Syn.subst σ a) (Syn.subst σ b)
      (Syn.subst σ c) (Syn.subst σ d) := by simp [rationalMargin]

theorem margin_readback (a b c d : PTm n) : Γ ⊢[PRAAx] g (d*a) (b*c) (d*b) ≐ rationalMargin a b c d :=
  GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) (by ipra_ring)

theorem pole_margin_rescale (a b K D : PTm n) (h : Γ ⊢[PRAAx] poleMargin a b K) :
    Γ ⊢[PRAAx] poleMargin (D*a) (D*b) K := by
  exact .andI
    (le_congr (mul_comm _ _) (by ipra_ring) (mul_le_mul_right D h.andE₁))
    (le_congr (mul_comm _ _)
      ((by ipra_ring : Γ ⊢[PRAAx] K*monus b a*D ≐ K*(D*monus b a)).eqTrans
        (congrMul (.eqRefl K) (LogisticName.monus_scale b a D).eqSymm))
      (mul_le_mul_right D h.andE₂))

private theorem pole_margin_congr (a b d K : PTm n) (eq : Γ ⊢[PRAAx] b ≐ d) (h : Γ ⊢[PRAAx] poleMargin a b K) :
    Γ ⊢[PRAAx] poleMargin a d K :=
  .andI (le_congr eq (.eqRefl _) h.andE₁)
    (le_congr eq (congrMul (.eqRefl _) (congrMonus eq (.eqRefl _))) h.andE₂)

private theorem guard_congr (a b d : PTm n) (eq : Γ ⊢[PRAAx] b ≐ d) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] guard a d :=
  .andI h.andE₁ (lt_congr (.eqRefl _) eq h.andE₂)

private theorem log_data_congr {a a' b b' N : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] ld a b N ≐ ld a' b' N := by
  simpa only [GaussianGammaNegativeIntervalLogAbsolute.subst_nameData, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using
    Prf.eqCongr (ld (var 0) (var 1) (var 2) : PTm 3) (σ := ![a,b,N]) (σ' := ![a',b',N])
      (fun i => by fin_cases i; exact ha; exact hb; exact .eqRefl N)

private theorem rational_cases (a c : PTm n) : Γ ⊢[PRAAx] (lt a c ⋎ lt c a) ⋎ a ≐ c := by
  refine .orE (lt_or_le a c) (.orI₁ (.orI₁ Prf.hyp0)) ?_
  exact .orE (lt_or_eq_of_le Prf.hyp0) (.orI₁ (.orI₂ Prf.hyp0)) (.orI₂ Prf.hyp0.eqSymm)

private theorem equal_comparison (p q k a c b N C : PTm n) (ha : Γ ⊢[PRAAx] guard a b)
    (hc : Γ ⊢[PRAAx] guard c b) (eq : Γ ⊢[PRAAx] a ≐ c) : Γ ⊢[PRAAx]
    upper (fstT (qadd (g a c b) (ap2 L p (ld a b N)))) (fstT (ap2 L q (ld c b N)))
      (rateNumerator C (unit k) p q) (rateDenominator (unit k) p q) := by
  let x := ap2 L p (ld a b N)
  have e0 : Γ ⊢[PRAAx] absDelta a c ≐ zero :=
    (congrAdd (congrMonus eq.eqSymm (.eqRefl _)) (congrMonus (.eqRefl _) eq.eqSymm)).eqTrans
      ((congrAdd (monus_self a) (monus_self a)).eqTrans (by ipra_ring))
  have hB := positive_product _ _ RationalAlgebra.two_positive (le_trans ha.andE₁ (le_of_lt ha.andE₂))
  have hd : Γ ⊢[PRAAx] le one (num 4*(two*b)*(two*b)) :=
    positive_product _ _ (positive_product _ _ (by ipra_le 3) hB) hB
  have ez : Γ ⊢[PRAAx] g a c b ≐ qzero :=
    (GaussianCompactRiemannName.fraction_congr _ _ _ _ ((congrMul e0 e0).eqTrans (by ipra_ring)) (.eqRefl _)).eqTrans
      (GaussianGammaRationalWendelBoundary.fraction_zero _ hd)
  have can : Γ ⊢[PRAAx] GaussianRationalHorner.canonical x :=
    (GaussianSignedNameExponentialOrder.real_sample_at L (ld a b N) p
      (GaussianGammaNegativeIntervalLogAbsolute.name_real a b N)).andE₁
  have erase := (qadd_congr ez (.eqRefl x)).eqTrans (qzero_add x can)
  have agree := code_data_cross L _ _ (name_regular a b N ha) (name_regular c b N hc) (log_data_congr eq (.eqRefl b))
  have hpq := positive_product _ _ (unit_positive (Γ := Γ) p) (unit_positive q)
  have atom := scalar_upper _ _ _ _ hpq (cross_at _ _ _ _ p q agree)
  exact upper_congr (congrFst erase).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (upper_mono _ _ _ _ _ _ hpq atom (by unfold rateNumerator rateDenominator; ipra_le 𝔞(C)*𝔞(unit p)^2*𝔞(unit q)^2))

private theorem common_stationary (p q k a c b N K C z : PTm n)
    (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c b)
    (hma : Γ ⊢[PRAAx] poleMargin a b K) (hmc : Γ ⊢[PRAAx] poleMargin c b K)
    (residual : Γ ⊢[PRAAx] independentRate T zeroF (td a b N) z C (unit k)) : Γ ⊢[PRAAx]
    upper (fstT (qadd (g a c b) (ap2 L p (ld a b N)))) (fstT (ap2 L q (ld c b N)))
      (rateNumerator (comparisonCost N C) (unit k) p q) (rateDenominator (unit k) p q) :=
  .orE (rational_cases a c)
    (GaussianGammaNegativeIntervalStationaryBudget.stationary_at p q k a c b N K C z
      ha.wk hc.wk Prf.hyp0 hma.wk hmc.wk residual.wk)
    (equal_comparison p q k a c b N (comparisonCost N C) ha.wk hc.wk Prf.hyp0)

private theorem transfer_comparison (p q k a b c d N K C z t : PTm n)
    (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c d)
    (hma : Γ ⊢[PRAAx] poleMargin a b K) (hmc : Γ ⊢[PRAAx] poleMargin c d K)
    (residual : Γ ⊢[PRAAx] independentRate T zeroF (td a b N) z C (unit k)) : Γ ⊢[PRAAx]
    upperSlack (fstT (qadd (rationalMargin a b c d) (ap2 L p (ld a b N)))) (fstT (ap2 L q (ld c d N)))
      (rateNumerator (comparisonCost N C) (unit k) p q) (rateDenominator (unit k) p q) (num 4) t := by
  let A := d*a
  let D := d*b
  let V := b*c
  let m := rationalMargin a b c d
  have hb := le_trans ha.andE₁ (le_of_lt ha.andE₂)
  have hd := le_trans hc.andE₁ (le_of_lt hc.andE₂)
  have hA := guard_rescale a b d ha hd
  have hV := guard_rescale c d b hc hb
  have eD := mul_comm (Γ := Γ) b d
  have hVD := guard_congr V (b*d) D eD hV
  have hAV := pole_margin_rescale _ _ K d hma
  have hVV := pole_margin_congr _ _ _ K eD (pole_margin_rescale _ _ K b hmc)
  have left := cross_symm _ _ _ _ (log_absolute_rescale a b d N ha hd)
  have right := cross_trans _ _ _ _ _ _
    (code_data_cross L _ _ (name_regular V D N hVD) (name_regular V (b*d) N hV)
      (log_data_congr (.eqRefl _) eD.eqSymm)) (log_absolute_rescale c d b N hc hb)
  have update := GaussianGammaNegativeIntervalDerivativeTargetRescale.original_rescale a b N d ha hd
  have hk := unit_positive (Γ := Γ) k
  have moved := GaussianNamedRateTransport.transport T zeroF T zeroF (td a b N) z (td A D N) z
    C (unit k) hk residual update (cross_refl _ _ (zero_fast z))
  have ht := unit_positive (Γ := Γ) t
  have hPT := positive_product _ _ (unit_positive p) ht
  have hTQ := positive_product _ _ ht (unit_positive q)
  have inside := common_stationary t t k A V D N K C z hA hVD hAV hVV moved
  have exactMargin := qadd_congr (margin_readback (Γ := Γ) a b c d) (.eqRefl (ap2 L t (ld A D N)))
  have middle := upper_congr (congrFst exactMargin) (.eqRefl _) (.eqRefl _) (.eqRefl _) inside
  have l := scalar_upper _ _ _ _ hPT (sum_right_error m _ _ _ _ hPT (cross_at _ _ _ _ p t left))
  have r := scalar_upper _ _ _ _ hTQ (cross_at _ _ _ _ t q right)
  have joined := upper_triangle _ _ _ _ _ _ _ (upper_triangle _ _ _ _ _ _ _ l middle) r
  apply upper_mono _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ hPT (denominator_positive _ _ _ hk)) hTQ) joined
  unfold rateNumerator rateDenominator
  ipra_le 0

theorem stationary_at (p q k a b c d N K C z : PTm n)
    (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c d)
    (hma : Γ ⊢[PRAAx] poleMargin a b K) (hmc : Γ ⊢[PRAAx] poleMargin c d K)
    (residual : Γ ⊢[PRAAx] independentRate T zeroF (td a b N) z C (unit k)) : Γ ⊢[PRAAx]
    upper (fstT (qadd (rationalMargin a b c d) (ap2 L p (ld a b N)))) (fstT (ap2 L q (ld c d N)))
      (rateNumerator (comparisonCost N C) (unit k) p q) (rateDenominator (unit k) p q) :=
  remove_upper_slack _ _ _ _ (num 4) (transfer_comparison p q k a b c d N K C z
    (precision _ _ _ (num 4)) ha hc hma hmc residual)

theorem selected_comparison (p q k c d N K : PTm n) (hc : Γ ⊢[PRAAx] guard c d)
    (hK : Γ ⊢[PRAAx] le (mesh N) K) (hm : Γ ⊢[PRAAx] poleMargin c d K) : Γ ⊢[PRAAx]
    upper (fstT (qadd (rationalMargin (argumentNumerator k N) (argumentDenominator k N) c d)
      (ap2 L p (ld (argumentNumerator k N) (argumentDenominator k N) N)))) (fstT (ap2 L q (ld c d N)))
      (rateNumerator (comparisonCost N two) (unit (stage k)) p q) (rateDenominator (unit (stage k)) p q) :=
  stationary_at p q (stage k) (argumentNumerator k N) (argumentDenominator k N) c d N K two qzero
    (base_guard k N) hc (base_margin k N K hK) hm (GaussianGammaNegativeIntervalCriticalResidualRate.original_rate k N)

theorem actual_original_negative_interval_selected_rational_comparison_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      ((guard (var 3) (var 4) ⋏ (le (mesh (var 5)) (var 6) ⋏ poleMargin (var 3) (var 4) (var 6))) ⟶
        upper (fstT (qadd (rationalMargin (argumentNumerator (var 2) (var 5)) (argumentDenominator (var 2) (var 5)) (var 3) (var 4))
          (ap2 L (var 0) (ld (argumentNumerator (var 2) (var 5)) (argumentDenominator (var 2) (var 5)) (var 5)))))
          (fstT (ap2 L (var 1) (ld (var 3) (var 4) (var 5))))
          (rateNumerator (comparisonCost (var 5) two) (unit (stage (var 2))) (var 0) (var 1))
          (rateDenominator (unit (stage (var 2))) (var 0) (var 1))) :=
  closeUniv 7 (.impI (selected_comparison _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalCriticalRationalComparison
