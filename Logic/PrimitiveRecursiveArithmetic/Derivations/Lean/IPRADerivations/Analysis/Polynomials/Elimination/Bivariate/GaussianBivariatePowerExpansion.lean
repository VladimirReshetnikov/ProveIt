import IPRADerivations.Analysis.Polynomials.CompanionMatrices.GaussianPolynomialMultiplicationMatrix
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianRationalPowerExpansion

/-!
# Finite power sums for the original bivariate evaluator

Reading the descending `Y` rows by their original exponents gives an
outer sum of powers of `Y`. Each row uses the existing ascending `X`
power sum. Both numerical bounds and the original data stay internal.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBivariatePowerExpansion

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianPolynomialMonicCompanion (values values_length values_lookup rowShape row_shape_at)
open LeanProofs.IPRA.Analysis.GaussianPolynomialMultiplicationMatrix (slot slot_pred slot_range)
open LeanProofs.IPRA.Analysis.GaussianRationalFiniteSum (sum sum_index_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate hornerF qmul)
open LeanProofs.IPRA.Analysis.GaussianRationalPowerExpansion (termBody terms_length power_expansion term_body_at)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (power powerF)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qmul_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (pred)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def powerSum (C N x : PTm n) : PTm n := sum termBody (succ N) (GaussianRationalPowerExpansion.data C N x)

theorem evaluate_power_sum (C N x : PTm n) (h : Γ ⊢[PRAAx] length C ≐ succ N) :
    Γ ⊢[PRAAx] evaluate C x ≐ powerSum C N x :=
  (power_expansion C N x h).eqTrans (congrAp3 hornerF (terms_length C N x) (.eqRefl _) (.eqRefl _))

def data (G m a x y : PTm n) : PTm n := pairT G (pairT m (pairT a (pairT x y)))

def rowBody : PTm 2 :=
  qmul (powerSum (entry (fstT (var 1)) (slot (fstT (sndT (var 1))) (var 0)))
    (fstT (sndT (sndT (var 1)))) (fstT (sndT (sndT (sndT (var 1))))))
    (power (sndT (sndT (sndT (sndT (var 1))))) (var 0))

def bivariateSum (G m a x y : PTm n) : PTm n := sum rowBody m (data G m a x y)

@[simp] theorem subst_powerSum {l : ℕ} (σ : Fin n → PTm l) (C N x : PTm n) :
    Syn.subst σ (powerSum C N x) = powerSum (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ x) := by
  simp [powerSum]

@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (G m a x y : PTm n) :
    Syn.subst σ (data G m a x y) = data (Syn.subst σ G) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ x) (Syn.subst σ y) := by
  simp [data]

theorem row_body_at (G m a x y i : PTm n) : Γ ⊢[PRAAx]
    inst2 rowBody i (data G m a x y) ≐ qmul (powerSum (entry G (slot m i)) a x) (power y i) := by
  have rest := snd_pair (Γ := Γ) G (pairT m (pairT a (pairT x y)))
  have afterM := (congrSnd rest).eqTrans (snd_pair m (pairT a (pairT x y)))
  have afterA := (congrSnd afterM).eqTrans (snd_pair a (pairT x y))
  have mEq := (congrFst rest).eqTrans (fst_pair m (pairT a (pairT x y)))
  have aEq := (congrFst afterM).eqTrans (fst_pair a (pairT x y))
  have xEq := (congrFst afterA).eqTrans (fst_pair x y)
  have yEq := (congrSnd afterA).eqTrans (snd_pair x y)
  simp only [inst2,rowBody,GaussianRationalHorner.subst_qmul,GaussianRationalReciprocal.subst_power,
    subst_powerSum,Foundations.MasterCertificate.subst_entry,GaussianPolynomialMultiplicationMatrix.subst_slot,
    subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  have slotEq := congrMonus mEq (Prf.eqRefl (succ i))
  have rowEq := entry_congr (fst_pair G (pairT m (pairT a (pairT x y)))) slotEq
  exact qmul_congr (sum_index_congr _ (congrSucc aEq) (congrPairT rowEq (congrPairT aEq xEq)))
    (congrAp2 powerF (.eqRefl _) yEq)

theorem evaluated_term (G m a x y i : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hG : Γ ⊢[PRAAx] rowShape G m a) (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx]
    inst2 termBody i (GaussianRationalPowerExpansion.data (values G m x) (pred m) y) ≐ inst2 rowBody i (data G m a x y) := by
  have rowIndex := slot_range m i hi
  have source := (entry_congr (.eqRefl (values G m x)) (slot_pred m i hm).eqSymm).eqTrans (values_lookup _ _ _ _ rowIndex)
  have exp := source.eqTrans (evaluate_power_sum _ _ _ (row_shape_at G m a (slot m i) hG rowIndex))
  exact (term_body_at _ _ _ _).eqTrans ((qmul_congr exp (.eqRefl _)).eqTrans (row_body_at _ _ _ _ _ _).eqSymm)

theorem bivariate_expansion (G m a x y : PTm n) (hm : Γ ⊢[PRAAx] le one m) (hG : Γ ⊢[PRAAx] rowShape G m a) :
    Γ ⊢[PRAAx] evaluate (values G m x) y ≐ bivariateSum G m a x y := by
  have shape : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift G) (Syn.shift m) (Syn.shift a) := by
    simpa [Fm.shift,Syn.shift] using hG.shift
  have positive : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by
    simpa [Fm.shift,Syn.shift] using hm.shift
  have size := RationalIntegerNormalization.positive_form hm
  have expansion := evaluate_power_sum (values G m x) (pred m) y ((values_length G m x).eqTrans size)
  refine expansion.eqTrans ((sum_index_congr termBody size.eqSymm (.eqRefl _)).eqTrans ?_)
  refine GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simpa [Syn.shift] using evaluated_term (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift x) (Syn.shift y)
    (var 0) positive.wk shape.wk Prf.hyp0

theorem actual_bivariate_expansion_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ rowShape (var 0) (var 1) (var 2) ⟶
      evaluate (values (var 0) (var 1) (var 3)) (var 4) ≐ bivariateSum (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (bivariate_expansion _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBivariatePowerExpansion
