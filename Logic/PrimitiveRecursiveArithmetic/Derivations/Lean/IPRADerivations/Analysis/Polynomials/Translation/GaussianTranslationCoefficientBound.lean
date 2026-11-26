import IPRADerivations.Analysis.Polynomials.Translation.GaussianTranslationScaledCoefficients
import IPRADerivations.Foundations.BoundedSyntaxBackwardInduction

/-!
# Quantitative recovery of every original nonconstant coefficient

Backward induction on the actual synthetic-quotient rows bounds each
radius-weighted coefficient by 2^(N-j) times the actual largest weighted
translated coefficient. The omitted j=k=0 cell is exactly the constant
coefficient, which is not among the positive-degree maximands. All row
lengths and indices are internal; the bounded observation is compiled to
a genuine QF induction. No inverse translation, maximum, representation
or row invariant is an incoming premise of the final theorem.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianTranslationCoefficientBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalRelativeNormAlgebra (relative relative_congr relative_weight_mono)
open LeanProofs.IPRA.Analysis.GaussianRationalRelativeTwoTerm (norm_order_relative sub_bound unit_product_left)
open LeanProofs.IPRA.Analysis.GaussianTranslationScaledCoefficients (scaledCoefficient)
open LeanProofs.IPRA.Analysis.GaussianTranslationCoefficientMaximum (base term)
open LeanProofs.IPRA.Analysis.GaussianRationalTranslationStages (remaining)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qmul)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub bounded)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def input (C N z A B : PTm n) : Fm PTm n := length C ≐ succ N ⋏
  (le one N ⋏ (le one B ⋏ (le B A ⋏ bounded z A B)))
def weight (N j : PTm n) : PTm n := pw two (remaining N j)
def cell (C N z A B j k : PTm n) : Fm PTm n :=
  relative (scaledCoefficient C N z A B j k) (weight N j) one (base C N z A B)
def row (C N z A B j : PTm n) : Fm PTm n := .all
  (lt (var 0) (succ (remaining (Syn.shift N) (Syn.shift j))) ⟶ le one (Syn.shift j+var 0) ⟶
    cell (Syn.shift C) (Syn.shift N) (Syn.shift z) (Syn.shift A) (Syn.shift B) (Syn.shift j) (var 0))

@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (C N z A B : PTm n) :
    (input C N z A B).subst σ = input (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z)
      (Syn.subst σ A) (Syn.subst σ B) := by simp [input]
@[simp] theorem subst_weight {m : ℕ} (σ : Fin n → PTm m) (N j : PTm n) :
    Syn.subst σ (weight N j) = weight (Syn.subst σ N) (Syn.subst σ j) := by simp [weight]
@[simp] theorem subst_cell {m : ℕ} (σ : Fin n → PTm m) (C N z A B j k : PTm n) :
    (cell C N z A B j k).subst σ = cell (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z)
      (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ j) (Syn.subst σ k) := by simp [cell]
@[simp] theorem subst_row {m : ℕ} (σ : Fin n → PTm m) (C N z A B j : PTm n) :
    (row C N z A B j).subst σ = row (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z)
      (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ j) := by
  simp [row,Syn.subst_shift,Syn.shift_subst]

def relativeSyntax (u W L b : PTm n) : BFm n := .le
  (RationalArgmin.left (GaussianRationalNormClearing.weightedNorm (L*L) u) (GaussianRationalNormClearing.weightedNorm (W*W) b))
  (RationalArgmin.left (GaussianRationalNormClearing.weightedNorm (W*W) b) (GaussianRationalNormClearing.weightedNorm (L*L) u))
def rowSyntax (C N z A B j : PTm n) : BFm n := .all (succ (remaining N j))
  (.imp (.le one (Syn.shift j+var 0)) (relativeSyntax
    (scaledCoefficient (Syn.shift C) (Syn.shift N) (Syn.shift z) (Syn.shift A) (Syn.shift B) (Syn.shift j) (var 0))
    (weight (Syn.shift N) (Syn.shift j)) one (base (Syn.shift C) (Syn.shift N) (Syn.shift z) (Syn.shift A) (Syn.shift B))))
theorem row_formula (C N z A B j : PTm n) : formula (rowSyntax C N z A B j) = row C N z A B j := by
  simp [rowSyntax,relativeSyntax,formula,row,cell,relative,RationalArgmin.rationalLE,Syn.shift,BFm.le,le]

theorem weight_positive (N j : PTm n) : Γ ⊢[PRAAx] le one (weight N j) :=
  GaussianPolynomialPerturbation.power_positive two _ (le_succ_self one)
theorem weight_terminal (N : PTm n) : Γ ⊢[PRAAx] weight N N ≐ one :=
  (congrAp2 powF (monus_self N) (.eqRefl two)).eqTrans (pw_zero two)
theorem weight_double (N j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    weight N j ≐ weight N (succ j)+weight N (succ j) :=
  ((congrAp2 powF (GaussianRationalTranslationStages.remaining_step N j hj) (.eqRefl two)).eqTrans
    (pw_succ two (remaining N (succ j)))).eqTrans (by unfold weight; ipra_ring)
theorem weight_increase (N j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    le (weight N (succ j)) (weight N j) :=
  le_of_eq_add (weight_double N j hj)

theorem row_at (C N z A B j k : PTm n) (h : Γ ⊢[PRAAx] row C N z A B j)
    (hk : Γ ⊢[PRAAx] le k (remaining N j)) (hp : Γ ⊢[PRAAx] le one (j+k)) : Γ ⊢[PRAAx]
    cell C N z A B j k := by
  have rule : Γ ⊢[PRAAx] lt k (succ (remaining N j)) ⟶ le one (j+k) ⟶ cell C N z A B j k := by
    simpa [row] using h.allE k
  exact .impE (.impE rule ((succ_monus_succ _ _).eqTrans hk)) hp

theorem terminal_at (C N z A B k : PTm n) (hInput : Γ ⊢[PRAAx] input C N z A B)
    (hk : Γ ⊢[PRAAx] le k (remaining N N)) : Γ ⊢[PRAAx] cell C N z A B N k := by
  have k0 : Γ ⊢[PRAAx] k ≐ zero := le_antisymm (le_congr (.eqRefl _) (monus_self N) hk) (zero_le k)
  have value := (GaussianTranslationScaledCoefficients.scaledCoefficient_index_congr C N z A B N k0).eqTrans
    (GaussianTranslationScaledCoefficients.terminal_coefficient C N z A B (Prf.andE₁ hInput))
  have hN := Prf.andE₁ (Prf.andE₂ hInput)
  exact relative_congr value.eqSymm (weight_terminal N).eqSymm (.eqRefl _) (.eqRefl _)
    (norm_order_relative _ _ (GaussianTranslationCoefficientMaximum.winner_maximal C N z A B N hN hN (le_refl N)))

theorem terminal_row (C N z A B : PTm n) (hInput : Γ ⊢[PRAAx] input C N z A B) : Γ ⊢[PRAAx]
    row C N z A B N := by
  refine .allI (.impI (.impI ?_))
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift C) (Syn.shift N) (Syn.shift z) (Syn.shift A) (Syn.shift B) := by
    simpa only [Fm.shift,subst_input,Syn.shift] using hInput.shift
  exact terminal_at _ _ _ _ _ _ hs.wk.wk ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp1)

theorem combine_step (C N z A B j k a b : PTm n) (hj : Γ ⊢[PRAAx] lt j N)
    (ht : Γ ⊢[PRAAx] bounded (GaussianRationalTravelScaling.ratio A B z) one one)
    (he : Γ ⊢[PRAAx] scaledCoefficient C N z A B j k ≐ qsub a (qmul (GaussianRationalTravelScaling.ratio A B z) b))
    (ha : Γ ⊢[PRAAx] relative a (weight N (succ j)) one (base C N z A B))
    (hb : Γ ⊢[PRAAx] relative b (weight N (succ j)) one (base C N z A B)) : Γ ⊢[PRAAx]
    cell C N z A B j k :=
  relative_congr he.eqSymm (weight_double N j hj).eqSymm (.eqRefl _) (.eqRefl _)
    (sub_bound _ _ _ _ _ ha (unit_product_left _ _ _ _ _ ht hb))

/-- All local row inputs below are actual smaller-stage observations,
not a supplied coefficient inversion or global bound. -/
theorem backward_at (C N z A B j k : PTm n) (hInput : Γ ⊢[PRAAx] input C N z A B)
    (hj : Γ ⊢[PRAAx] lt j N) (hk : Γ ⊢[PRAAx] le k (remaining N j))
    (hp : Γ ⊢[PRAAx] le one (j+k)) (hRow : Γ ⊢[PRAAx] row C N z A B (succ j)) : Γ ⊢[PRAAx]
    cell C N z A B j k := by
  have hLen := Prf.andE₁ hInput
  have hN := Prf.andE₁ (Prf.andE₂ hInput)
  have hB := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ hInput))
  have hBA := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ hInput)))
  have hz := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ hInput)))
  have hA := le_trans hB hBA
  have ht := GaussianRationalTravelScaling.ratio_unit A B z hB hBA hz
  have next_positive (i : PTm n) : Γ ⊢[PRAAx] le one (succ j+i) :=
    le_of_eq_add (d := j+i) (by ipra_ring)
  refine .orE (zero_or_succ k) ?_ ?_
  · have jpos : (k ≐ zero)::Γ ⊢[PRAAx] le one j :=
      le_congr (.eqRefl _) ((congrAdd (.eqRefl _) Prf.hyp0).eqTrans (add_zero j)) hp.wk
    have first := relative_weight_mono _ _ _ _ _ (weight_positive (Γ := (k ≐ zero)::Γ) N (succ j))
      (norm_order_relative _ _ (GaussianTranslationCoefficientMaximum.winner_maximal C N z A B j hN.wk jpos (le_of_lt hj.wk)))
    have second : (k ≐ zero)::Γ ⊢[PRAAx] cell C N z A B (succ j) zero :=
      row_at C N z A B (succ j) zero hRow.wk (zero_le _) (next_positive zero).wk
    have atZero := combine_step C N z A B j zero _ _ hj.wk ht.wk
      (GaussianTranslationScaledCoefficients.constant_coefficient C N z A B j hLen.wk hA.wk hB.wk hj.wk) first second
    exact relative_congr (GaussianTranslationScaledCoefficients.scaledCoefficient_index_congr C N z A B j Prf.hyp0.eqSymm)
      (.eqRefl _) (.eqRefl _) (.eqRefl _) atZero
  · have kpos : (k ≐ succ (pred k))::Γ ⊢[PRAAx] le one k :=
      le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ _)
    have predRange : (k ≐ succ (pred k))::Γ ⊢[PRAAx] le (pred k) (remaining N (succ j)) :=
      (succ_monus_succ _ _).eqSymm.eqTrans
        (le_congr Prf.hyp0 (GaussianRationalTranslationStages.remaining_step N j hj.wk) hk.wk)
    have first := row_at C N z A B (succ j) (pred k) hRow.wk predRange (next_positive (pred k)).wk
    refine .orE (lt_or_le k (remaining N j)) ?_ ?_
    · have nextRange : lt k (remaining N j)::(k ≐ succ (pred k))::Γ ⊢[PRAAx]
          le k (remaining N (succ j)) :=
        (succ_monus_succ _ _).eqSymm.eqTrans
          (le_congr (.eqRefl _) (GaussianRationalTranslationStages.remaining_step N j hj.wk.wk) Prf.hyp0)
      exact combine_step C N z A B j k _ _ hj.wk.wk ht.wk.wk
        (GaussianTranslationScaledCoefficients.interior_coefficient C N z A B j k hA.wk.wk hB.wk.wk hj.wk.wk kpos.wk Prf.hyp0)
        first.wk (row_at _ _ _ _ _ _ _ hRow.wk.wk nextRange (next_positive k).wk.wk)
    · have equalIndex : le (remaining N j) k::(k ≐ succ (pred k))::Γ ⊢[PRAAx] k ≐ remaining N j :=
        le_antisymm hk.wk.wk Prf.hyp0
      exact relative_congr
        (GaussianTranslationScaledCoefficients.leading_coefficient_at C N z A B j k hj.wk.wk equalIndex).eqSymm
        (.eqRefl _) (.eqRefl _) (.eqRefl _)
        (relative_weight_mono _ _ _ _ _ (weight_increase N j hj.wk.wk) first.wk)

theorem backward_row (C N z A B j : PTm n) (hInput : Γ ⊢[PRAAx] input C N z A B)
    (hj : Γ ⊢[PRAAx] lt j N) (hRow : Γ ⊢[PRAAx] row C N z A B (succ j)) : Γ ⊢[PRAAx]
    row C N z A B j := by
  refine .allI (.impI (.impI ?_))
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift C) (Syn.shift N) (Syn.shift z) (Syn.shift A) (Syn.shift B) := by
    simpa only [Fm.shift,subst_input,Syn.shift] using hInput.shift
  have js : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift j) (Syn.shift N) := by
    simpa only [Fm.shift,subst_lt,Syn.shift] using hj.shift
  have rs : Γ.map Fm.shift ⊢[PRAAx] row (Syn.shift C) (Syn.shift N) (Syn.shift z)
      (Syn.shift A) (Syn.shift B) (succ (Syn.shift j)) := by
    simpa only [Fm.shift,subst_row,ConciseIPRA.PTm.subst_succ,Syn.shift] using hRow.shift
  exact backward_at _ _ _ _ _ _ _ hs.wk.wk js.wk.wk
    ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp1) Prf.hyp0 rs.wk.wk

theorem all_rows (C N z A B j : PTm n) (hInput : Γ ⊢[PRAAx] input C N z A B)
    (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx] row C N z A B j := by
  let S := rowSyntax (Syn.shift C) (Syn.shift N) (Syn.shift z) (Syn.shift A) (Syn.shift B) (var 0)
  have terminal : Γ ⊢[PRAAx] (formula S).subst (Syn.inst N) := by
    simpa only [S,row_formula,subst_row,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using terminal_row C N z A B hInput
  have step : Γ ⊢[PRAAx] Foundations.BoundedSyntaxBackwardInduction.localStep S N := by
    simp only [Foundations.BoundedSyntaxBackwardInduction.localStep,S,row_formula,
      subst_row,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
    refine .allI (.impI (.impI ?_))
    have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift C) (Syn.shift N) (Syn.shift z) (Syn.shift A) (Syn.shift B) := by
      simpa only [Fm.shift,subst_input,Syn.shift] using hInput.shift
    exact backward_row _ _ _ _ _ (var 0) hs.wk.wk Prf.hyp1 Prf.hyp0
  simpa only [S,row_formula,subst_row,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
    Foundations.BoundedSyntaxBackwardInduction.backward_induction_at S N j terminal step hj

/-- The stronger 2^N bound holds even for the zero polynomial. The actual
maximum and all backward coefficient bounds have been constructed. -/
theorem original_coefficient_bound (C N z A B k : PTm n) (hInput : Γ ⊢[PRAAx] input C N z A B)
    (hk : Γ ⊢[PRAAx] le one k) (hkN : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    relative (entry C (monus N k)) (pw two N) one (base C N z A B) := by
  have rows := all_rows C N z A B zero hInput (zero_le N)
  have scaled := row_at C N z A B zero k rows (le_congr (.eqRefl _) (monus_zero N).eqSymm hkN)
    (le_congr (.eqRefl _) (zero_add k).eqSymm hk)
  have actual := relative_congr (GaussianTranslationScaledCoefficients.original_coefficient C N z A B k)
    (.eqRefl _) (.eqRefl _) (.eqRefl _) scaled
  have hB := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ hInput))
  have hBA := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ hInput)))
  have unscaled := GaussianRationalTravelScaling.unscale_relative A B k
    (GaussianTranslatedNonconstant.recode (entry C (monus N k))) hB hBA
    (GaussianTranslatedNonconstant.recode_canonical _)
  have joined := GaussianRationalRelativeNormAlgebra.relative_trans _ _ _ _ _ _ _ unscaled actual
  have value : Γ ⊢[PRAAx] relative (GaussianTranslatedNonconstant.recode (entry C (monus N k)))
      (pw two N) one (base C N z A B) :=
    relative_congr (.eqRefl _) ((one_mul _).eqTrans (congrAp2 powF (monus_zero N) (.eqRefl two)))
      (one_mul one) (.eqRefl _) joined
  exact RationalArgmin.rationalLE_congr
    (RationalAlgebra.multiply_congr (.eqRefl _) (GaussianRationalRelativeTwoTerm.norm_recode _)) (.eqRefl _) value

/-- This recovers the packet's original F=N*2^N constant by weakening the
proved stronger bound. No nonconstant or positive-maximum guard is needed. -/
theorem source_coefficient_bound (C N z A B k : PTm n) (hInput : Γ ⊢[PRAAx] input C N z A B)
    (hk : Γ ⊢[PRAAx] le one k) (hkN : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    relative (entry C (monus N k)) (N*pw two N) one (base C N z A B) :=
  relative_weight_mono _ _ _ _ _
    (le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (pw two N) (Prf.andE₁ (Prf.andE₂ hInput))))
    (original_coefficient_bound C N z A B k hInput hk hkN)

theorem returned_coefficient_bound (C N z A B k : PTm n) (hInput : Γ ⊢[PRAAx] input C N z A B)
    (hk : Γ ⊢[PRAAx] le one k) (hkN : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    relative (entry C (monus N k)) (pw two N) one
      (sndT (GaussianTranslationCoefficientMaximum.run C N z A B)) :=
  relative_congr (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianTranslationCoefficientMaximum.returned_value C N z A B).eqSymm
    (original_coefficient_bound C N z A B k hInput hk hkN)

theorem quantitative_translation_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ le one (var 5) ⟶ le (var 5) (var 1) ⟶
      relative (entry (var 0) (monus (var 1) (var 5))) (pw two (var 1)) one
        (base (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 6 (.impI (.impI (.impI (original_coefficient_bound _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem source_quantitative_translation_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ le one (var 5) ⟶ le (var 5) (var 1) ⟶
      relative (entry (var 0) (monus (var 1) (var 5))) ((var 1)*pw two (var 1)) one
        (base (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 6 (.impI (.impI (.impI (source_coefficient_bound _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem returned_quantitative_translation_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ le one (var 5) ⟶ le (var 5) (var 1) ⟶
      relative (entry (var 0) (monus (var 1) (var 5))) (pw two (var 1)) one
        (sndT (GaussianTranslationCoefficientMaximum.run (var 0) (var 1) (var 2) (var 3) (var 4)))) :=
  closeUniv 6 (.impI (.impI (.impI (returned_coefficient_bound _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianTranslationCoefficientBound
