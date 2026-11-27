import IPRADerivations.Algebra.QuadraticTowerMultiplicationNegative
import IPRADerivations.Algebra.QuadraticTowerSignCoherence
import IPRADerivations.Algebra.QuadraticIntegerSignDispatch
import IPRADerivations.Algebra.QuadraticRationalSignDispatch

/-!
# Actual numerical-tower sign under negation

All depths, caps, words and raw data remain numerical. The sign table's
actual three-tag dispatch is paired with its coefficientwise negative
input. The SAME computed norm and conditional third input are retained.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.QuadraticTowerSignNegation

open_ipra
open LeanProofs.IPRA.Analysis
open QuadraticTowerSignRecipe (read tagProduct dispatch)
open QuadraticTowerArrayCodec (arrayHeight code horizon normalized)
open QuadraticTowerCoefficientArithmetic (negated)
open QuadraticTowerMultiplicationHeight (radicandsHeight word)
open QuadraticTowerMultiplicationTable (budget leftHalf rightHalf)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)
open LeanProofs.IPRA.Foundations.BoundedReflection (eqb_cases eq_of_eqb)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def opposite (s : PTm n) : PTm n := tagProduct two s
ipra_subst opposite
theorem opposite_congr {s t : PTm n} (e : Γ ⊢[PRAAx] s ≐ t) : Γ ⊢[PRAAx] opposite s ≐ opposite t :=
  QuadraticTowerSignRecipe.tag_product_congr (.eqRefl two) e
theorem opposite_zero : Γ ⊢[PRAAx] opposite (zero : PTm n) ≐ zero :=
  QuadraticTowerSignRecipe.tag_product_zero_right _ _ (.eqRefl _)
theorem opposite_one : Γ ⊢[PRAAx] opposite (one : PTm n) ≐ two := QuadraticIntegerSignDispatch.tag_product_two_one
theorem opposite_two : Γ ⊢[PRAAx] opposite (two : PTm n) ≐ one := QuadraticIntegerSignDispatch.tag_product_two_two

theorem tag_cases (s : PTm n) (hs : Γ ⊢[PRAAx] lt s (succ two)) : Γ ⊢[PRAAx]
    (s ≐ zero) ⋎ ((s ≐ one) ⋎ (s ≐ two)) := by
  refine .orE (lt_or_le s one) ?_ ?_
  · exact .orI₁ (le_antisymm ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0) (zero_le _))
  · refine .orE (lt_or_le s two) ?_ ?_
    · exact .orI₂ (.orI₁ (le_antisymm ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0) Prf.hyp1))
    · exact .orI₂ (.orI₂ (le_antisymm ((succ_monus_succ _ _).eqSymm.eqTrans hs.wk.wk) Prf.hyp0))

theorem opposite_involution (s : PTm n) (hs : Γ ⊢[PRAAx] lt s (succ two)) : Γ ⊢[PRAAx] opposite (opposite s) ≐ s := by
  refine .orE (tag_cases s hs) ?_ ?_
  · exact (opposite_congr (opposite_congr Prf.hyp0)).eqTrans
      ((opposite_congr opposite_zero).eqTrans (opposite_zero.eqTrans Prf.hyp0.eqSymm))
  · refine .orE Prf.hyp0 ?_ ?_
    · exact (opposite_congr (opposite_congr Prf.hyp0)).eqTrans
        ((opposite_congr opposite_one).eqTrans (opposite_two.eqTrans Prf.hyp0.eqSymm))
    · exact (opposite_congr (opposite_congr Prf.hyp0)).eqTrans
        ((opposite_congr opposite_two).eqTrans (opposite_one.eqTrans Prf.hyp0.eqSymm))

theorem opposite_zero_reflect (s : PTm n) (hs : Γ ⊢[PRAAx] lt s (succ two))
    (hz : Γ ⊢[PRAAx] opposite s ≐ zero) : Γ ⊢[PRAAx] s ≐ zero :=
  (opposite_involution s hs).eqSymm.eqTrans ((opposite_congr hz).eqTrans opposite_zero)
theorem opposite_nonzero (s : PTm n) (hs : Γ ⊢[PRAAx] lt s (succ two))
    (hn : Γ ⊢[PRAAx] neg (s ≐ zero)) : Γ ⊢[PRAAx] neg (opposite s ≐ zero) :=
  .impI (.impE hn.wk (opposite_zero_reflect s hs.wk Prf.hyp0))
theorem opposite_different (s t : PTm n) (hs : Γ ⊢[PRAAx] lt s (succ two)) (ht : Γ ⊢[PRAAx] lt t (succ two))
    (hn : Γ ⊢[PRAAx] neg (s ≐ t)) : Γ ⊢[PRAAx] neg (opposite s ≐ opposite t) :=
  .impI (.impE hn.wk ((opposite_involution s hs.wk).eqSymm.eqTrans
    ((opposite_congr Prf.hyp0).eqTrans (opposite_involution t ht.wk))))

theorem tag_product_unit (s : PTm n) (hs : Γ ⊢[PRAAx] lt s (succ two)) : Γ ⊢[PRAAx] tagProduct one s ≐ s := by
  refine .orE (tag_cases s hs) ?_ ?_
  · exact (QuadraticTowerSignRecipe.tag_product_zero_right _ _ Prf.hyp0).eqTrans Prf.hyp0.eqSymm
  · refine .orE Prf.hyp0 ?_ ?_
    · exact (QuadraticTowerSignRecipe.tag_product_congr (.eqRefl one) Prf.hyp0).eqTrans
        (QuadraticIntegerSignDispatch.tag_product_one_one.eqTrans Prf.hyp0.eqSymm)
    · exact (QuadraticTowerSignRecipe.tag_product_congr (.eqRefl one) Prf.hyp0).eqTrans
        (QuadraticIntegerSignDispatch.tag_product_one_two.eqTrans Prf.hyp0.eqSymm)

theorem negative_tag_product (s t : PTm n) (hs : Γ ⊢[PRAAx] lt s (succ two)) (ht : Γ ⊢[PRAAx] lt t (succ two)) : Γ ⊢[PRAAx]
    tagProduct (opposite s) t ≐ opposite (tagProduct s t) := by
  refine .orE (tag_cases s hs) ?_ ?_
  · exact (QuadraticTowerSignRecipe.tag_product_congr ((opposite_congr Prf.hyp0).eqTrans opposite_zero) (.eqRefl t)).eqTrans
      ((QuadraticTowerSignRecipe.tag_product_zero_left _ _ (.eqRefl _)).eqTrans
        ((opposite_congr (QuadraticTowerSignRecipe.tag_product_zero_left _ _ Prf.hyp0)).eqTrans opposite_zero).eqSymm)
  · refine .orE Prf.hyp0 ?_ ?_
    · exact (QuadraticTowerSignRecipe.tag_product_congr ((opposite_congr Prf.hyp0).eqTrans opposite_one) (.eqRefl t)).eqTrans
        ((opposite_congr ((QuadraticTowerSignRecipe.tag_product_congr Prf.hyp0 (.eqRefl t)).eqTrans (tag_product_unit t ht.wk.wk))).eqSymm)
    · exact (QuadraticTowerSignRecipe.tag_product_congr ((opposite_congr Prf.hyp0).eqTrans opposite_two) (.eqRefl t)).eqTrans
        ((tag_product_unit t ht.wk.wk).eqTrans
          ((opposite_congr (QuadraticTowerSignRecipe.tag_product_congr Prf.hyp0 (.eqRefl t))).eqTrans (opposite_involution t ht.wk.wk)).eqSymm)

theorem equality_cases (s t : PTm n) : Γ ⊢[PRAAx] (s ≐ t) ⋎ neg (s ≐ t) := by
  refine .orE (eqb_cases s t) ?_ ?_
  · exact .orI₂ (.impI (succ_ne_zero' _ ((eqb_of_eq Prf.hyp0).eqSymm.eqTrans Prf.hyp1)))
  · exact .orI₁ (eq_of_eqb Prf.hyp0)

theorem dispatch_negative_zero (s t u : PTm n) (ht : Γ ⊢[PRAAx] lt t (succ two)) (hu : Γ ⊢[PRAAx] lt u (succ two))
    (hz : Γ ⊢[PRAAx] s ≐ zero) : Γ ⊢[PRAAx]
    dispatch (opposite s) (opposite t) u ≐ opposite (dispatch s t u) :=
  (QuadraticTowerSignRecipe.dispatch_a_zero _ _ _ ((opposite_congr hz).eqTrans opposite_zero)).eqTrans
    ((negative_tag_product t u ht hu).eqTrans (opposite_congr (QuadraticTowerSignRecipe.dispatch_a_zero _ _ _ hz)).eqSymm)
theorem dispatch_negative_bzero (s t u : PTm n) (hs : Γ ⊢[PRAAx] lt s (succ two))
    (hn : Γ ⊢[PRAAx] neg (s ≐ zero)) (hz : Γ ⊢[PRAAx] t ≐ zero) : Γ ⊢[PRAAx]
    dispatch (opposite s) (opposite t) u ≐ opposite (dispatch s t u) :=
  (QuadraticTowerSignRecipe.dispatch_b_zero _ _ _ (opposite_nonzero s hs hn) ((opposite_congr hz).eqTrans opposite_zero)).eqTrans
    (opposite_congr (QuadraticTowerSignRecipe.dispatch_b_zero _ _ _ hn hz)).eqSymm
theorem dispatch_negative_same (s t u : PTm n) (hs : Γ ⊢[PRAAx] lt s (succ two)) (ht : Γ ⊢[PRAAx] lt t (succ two))
    (sn : Γ ⊢[PRAAx] neg (s ≐ zero)) (tn : Γ ⊢[PRAAx] neg (t ≐ zero)) (eq : Γ ⊢[PRAAx] s ≐ t) : Γ ⊢[PRAAx]
    dispatch (opposite s) (opposite t) u ≐ opposite (dispatch s t u) :=
  (QuadraticTowerSignRecipe.dispatch_same _ _ _ (opposite_nonzero s hs sn) (opposite_nonzero t ht tn) (opposite_congr eq)).eqTrans
    (opposite_congr (QuadraticTowerSignRecipe.dispatch_same _ _ _ sn tn eq)).eqSymm
theorem dispatch_negative_opposite (s t u : PTm n) (hs : Γ ⊢[PRAAx] lt s (succ two)) (ht : Γ ⊢[PRAAx] lt t (succ two))
    (hu : Γ ⊢[PRAAx] lt u (succ two)) (sn : Γ ⊢[PRAAx] neg (s ≐ zero)) (tn : Γ ⊢[PRAAx] neg (t ≐ zero))
    (ne : Γ ⊢[PRAAx] neg (s ≐ t)) : Γ ⊢[PRAAx] dispatch (opposite s) (opposite t) u ≐ opposite (dispatch s t u) :=
  (QuadraticTowerSignRecipe.dispatch_opposite _ _ _ (opposite_nonzero s hs sn) (opposite_nonzero t ht tn) (opposite_different s t hs ht ne)).eqTrans
    ((negative_tag_product s u hs hu).eqTrans (opposite_congr (QuadraticTowerSignRecipe.dispatch_opposite _ _ _ sn tn ne)).eqSymm)

theorem dispatch_negative (s t u : PTm n) (hs : Γ ⊢[PRAAx] lt s (succ two)) (ht : Γ ⊢[PRAAx] lt t (succ two))
    (hu : Γ ⊢[PRAAx] lt u (succ two)) : Γ ⊢[PRAAx] dispatch (opposite s) (opposite t) u ≐ opposite (dispatch s t u) := by
  refine .orE (equality_cases s zero) ?_ ?_
  · exact dispatch_negative_zero s t u ht.wk hu.wk Prf.hyp0
  · refine .orE (equality_cases t zero) ?_ ?_
    · exact dispatch_negative_bzero s t u hs.wk.wk Prf.hyp1 Prf.hyp0
    · refine .orE (equality_cases s t) ?_ ?_
      · exact dispatch_negative_same s t u hs.wk.wk.wk ht.wk.wk.wk (.hyp (by simp)) (.hyp (by simp)) Prf.hyp0
      · exact dispatch_negative_opposite s t u hs.wk.wk.wk ht.wk.wk.wk hu.wk.wk.wk (.hyp (by simp)) (.hyp (by simp)) Prf.hyp0


theorem ground_negative (q : PTm n) : Γ ⊢[PRAAx]
    QuadraticTowerSignTable.groundTag (RationalArithmetic.negative q) ≐ opposite (QuadraticTowerSignTable.groundTag q) :=
  (QuadraticTowerSignTable.ground_tag_native _).eqTrans
    ((QuadraticRationalSignDispatch.tag_of_representation _ _ _ (RationalArgmin.denominator_positive q)
      (RationalArithmetic.negative_value q)).eqTrans
        ((QuadraticIntegerSignDispatch.tag_product_negative (RationalSupMetric.numeratorOf q)).eqSymm.eqTrans
          (opposite_congr (QuadraticTowerSignTable.ground_tag_native q).eqSymm)))

theorem base_read_original (B A : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight zero A B) : Γ ⊢[PRAAx]
    read zero B (QuadraticTowerSignTable.base B) A ≐ QuadraticTowerSignTable.groundTag (entry A zero) :=
  (QuadraticTowerSignCoherence.base_read_ground B A ha).eqTrans
    (QuadraticTowerSignTable.ground_tag_proper _ _ (RationalArithmetic.recode_equal _))
theorem base_negative (B A : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight zero A B) : Γ ⊢[PRAAx]
    read zero B (QuadraticTowerSignTable.base B) (negated zero A) ≐ opposite (read zero B (QuadraticTowerSignTable.base B) A) :=
  (base_read_original B _ (QuadraticTowerSignRecipe.negated_height zero A B ha)).eqTrans
    ((QuadraticTowerSignTable.ground_tag_congr (QuadraticTowerCoefficientArithmetic.negated_lookup zero A zero
      QuadraticTowerCoefficientArithmetic.base_index)).eqTrans
        ((ground_negative _).eqTrans (opposite_congr (base_read_original B A ha).eqSymm)))

def rowLaw (h B D S b u : PTm n) : Fm PTm n := radicandsHeight D h b ⟶
  arrayHeight h (word h b u) b ⟶ read h B S (negated h (word h b u)) ≐ opposite (read h B S (word h b u))
def atHeight (h B D S b : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift (horizon h b)) ⟶ rowLaw (Syn.shift h) (Syn.shift B) (Syn.shift D) (Syn.shift S) (Syn.shift b) (var 0))
def localLaw (h B D S : PTm n) : Fm PTm n := .all
  (lt (var 0) (succ (Syn.shift B)) ⟶ atHeight (Syn.shift h) (Syn.shift B) (Syn.shift D) (Syn.shift S) (var 0))
ipra_subst rowLaw
@[simp] theorem subst_atHeight {k : ℕ} (σ : Fin n → PTm k) (h B D S b : PTm n) :
    (atHeight h B D S b).subst σ = atHeight (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ S) (Syn.subst σ b) := by
  simp [atHeight,Syn.subst_shift,Syn.shift_subst]
  simp only [Syn.shift,QuadraticTowerArrayCodec.subst_horizon,Syn.subst_subst]
ipra_subst localLaw [Syn.subst_shift, Syn.shift_subst]

def rowSyntax (h B D S b u : PTm n) : BFm n := .imp (QuadraticTowerMultiplicationHeight.radicandsSyntax D h b)
  (.imp (QuadraticTowerMultiplicationHeight.heightSyntax h (word h b u) b)
    (.eq (read h B S (negated h (word h b u))) (opposite (read h B S (word h b u)))))
def heightRowsSyntax (h B D S b : PTm n) : BFm n := .all (horizon h b)
  (rowSyntax (Syn.shift h) (Syn.shift B) (Syn.shift D) (Syn.shift S) (Syn.shift b) (var 0))
def localSyntax (h B D S : PTm n) : BFm n := .all (succ B)
  (heightRowsSyntax (Syn.shift h) (Syn.shift B) (Syn.shift D) (Syn.shift S) (var 0))
theorem row_formula (h B D S b u : PTm n) : formula (rowSyntax h B D S b u) = rowLaw h B D S b u := by
  simp [rowSyntax,rowLaw,formula,QuadraticTowerMultiplicationHeight.radicands_formula,QuadraticTowerMultiplicationHeight.height_formula]
theorem height_rows_formula (h B D S b : PTm n) : formula (heightRowsSyntax h B D S b) = atHeight h B D S b := by
  simp [heightRowsSyntax,atHeight,formula,row_formula]
theorem local_formula (h B D S : PTm n) : formula (localSyntax h B D S) = localLaw h B D S := by
  simp [localSyntax,localLaw,formula,height_rows_formula]

theorem local_at (h B D S b u : PTm n) (hL : Γ ⊢[PRAAx] localLaw h B D S)
    (hb : Γ ⊢[PRAAx] le b B) (hu : Γ ⊢[PRAAx] lt u (horizon h b))
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h (word h b u) b) : Γ ⊢[PRAAx]
    read h B S (negated h (word h b u)) ≐ opposite (read h B S (word h b u)) := by
  have bg : Γ ⊢[PRAAx] lt b (succ B) ⟶ atHeight h B D S b := by simpa [localLaw] using hL.allE b
  have heightRule := Prf.impE bg ((succ_monus_succ _ _).eqTrans hb)
  have ug : Γ ⊢[PRAAx] lt u (horizon h b) ⟶ rowLaw h B D S b u := by simpa [atHeight] using heightRule.allE u
  exact .impE (.impE (.impE ug hu) hD) ha

theorem read_negative (h B D S b A : PTm n) (hL : Γ ⊢[PRAAx] localLaw h B D S)
    (hb : Γ ⊢[PRAAx] le b B) (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b) : Γ ⊢[PRAAx]
    read h B S (negated h A) ≐ opposite (read h B S A) := by
  have aw := QuadraticTowerMultiplicationHeight.restored_height h A b b ha (le_refl _)
  have av := QuadraticTowerMultiplicationCoherence.restored_values h A b ha
  have middle := local_at h B D S b (code h A b) hL hb (QuadraticTowerArrayCodec.code_bound h A b ha) hD aw
  exact (QuadraticTowerSignCoherence.read_values_proper h B S _ _
    (QuadraticTowerCoefficientArithmetic.negated_proper h _ A av)).eqSymm.eqTrans
      (middle.eqTrans (opposite_congr (QuadraticTowerSignCoherence.read_values_proper h B S _ A av)))


theorem negated_normalized (h A : PTm n) : Γ ⊢[PRAAx] negated h (normalized h A) ≐ negated h A :=
  (QuadraticTowerArrayNormalization.normalized_negated h (normalized h A)).eqSymm.eqTrans
    ((QuadraticTowerArrayNormalization.normalized_proper h _ _
      (QuadraticTowerCoefficientArithmetic.negated_proper h _ A (QuadraticTowerOperandProperness.normalized_values h A))).eqTrans
        (QuadraticTowerArrayNormalization.normalized_negated h A))


/-- The actual a=0 query still reads d; only the other branch reads norm. -/
theorem third_input_negative (h B D S A b : PTm n) (hb : Γ ⊢[PRAAx] le b B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b) (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b)
    (first : Γ ⊢[PRAAx] QuadraticTowerSignRecipe.firstTag h B D S (negated (succ h) A) ≐
      opposite (QuadraticTowerSignRecipe.firstTag h B D S A)) : Γ ⊢[PRAAx]
    QuadraticTowerSignRecipe.thirdInput h B D S (negated (succ h) A) ≐ QuadraticTowerSignRecipe.thirdInput h B D S A := by
  refine .orE (equality_cases (QuadraticTowerSignRecipe.firstTag h B D S A) zero) ?_ ?_
  · have nz := first.wk.eqTrans ((opposite_congr Prf.hyp0).eqTrans opposite_zero)
    exact (QuadraticTowerSignRecipe.third_when_a_zero h B D S _ nz).eqTrans
      (QuadraticTowerSignRecipe.third_when_a_zero h B D S A Prf.hyp0).eqSymm
  · have nz : neg (QuadraticTowerSignRecipe.firstTag h B D S A ≐ zero) :: Γ ⊢[PRAAx]
        neg (QuadraticTowerSignRecipe.firstTag h B D S (negated (succ h) A) ≐ zero) := by
      refine .impI (.impE Prf.hyp1 ?_)
      exact opposite_zero_reflect _ (QuadraticTowerSignRecipe.read_bound _ _ _ _)
        (first.wk.wk.eqSymm.eqTrans Prf.hyp0)
    exact (QuadraticTowerSignRecipe.third_when_a_nonzero h B D S _ nz).eqTrans
      ((QuadraticTowerMultiplicationNegative.norm_negative h B D A b hb.wk hD.wk ha.wk).eqTrans
        (QuadraticTowerSignRecipe.third_when_a_nonzero h B D S A Prf.hyp0).eqSymm)

/-- The finite lower predicate is used only for the two actual negative
halves. The actual third input is literally unchanged. -/
theorem recipe_negative (h B D S b A : PTm n) (hL : Γ ⊢[PRAAx] localLaw h (budget h B D) D S)
    (hb : Γ ⊢[PRAAx] le b B) (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b)
    (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b) : Γ ⊢[PRAAx]
    QuadraticTowerSignRecipe.recipe h B D S (negated (succ h) A) ≐ opposite (QuadraticTowerSignRecipe.recipe h B D S A) := by
  let K := budget h B D
  have bK := le_trans hb (QuadraticTowerSignEmbedding.budget_inflation h B D)
  have rh := QuadraticTowerMultiplicationHeight.radicands_prefix D h (succ h) b hD (le_succ_self h)
  have a0 := QuadraticTowerMultiplicationHeight.left_height h A b ha
  have a1 := QuadraticTowerMultiplicationHeight.right_height h A b ha
  have first : Γ ⊢[PRAAx] QuadraticTowerSignRecipe.firstTag h B D S (negated (succ h) A) ≐
      opposite (QuadraticTowerSignRecipe.firstTag h B D S A) :=
    (QuadraticTowerSignRecipe.read_operand_congr h K S _ _ (QuadraticTowerMultiplicationNegative.left_negative h A)).eqTrans
      (read_negative h K D S b (leftHalf h A) hL bK rh a0)
  have second : Γ ⊢[PRAAx] QuadraticTowerSignRecipe.secondTag h B D S (negated (succ h) A) ≐
      opposite (QuadraticTowerSignRecipe.secondTag h B D S A) :=
    (QuadraticTowerSignRecipe.read_operand_congr h K S _ _ (QuadraticTowerMultiplicationNegative.right_negative h A)).eqTrans
      (read_negative h K D S b (rightHalf h A) hL bK rh a1)
  have third : Γ ⊢[PRAAx] QuadraticTowerSignRecipe.thirdTag h B D S (negated (succ h) A) ≐ QuadraticTowerSignRecipe.thirdTag h B D S A :=
    QuadraticTowerSignRecipe.read_operand_congr h K S _ _ (third_input_negative h B D S A b hb hD ha first)
  exact (QuadraticTowerSignCoherence.dispatch_congr first second third).eqTrans
    (dispatch_negative _ _ _ (QuadraticTowerSignRecipe.read_bound _ _ _ _)
      (QuadraticTowerSignRecipe.read_bound _ _ _ _) (QuadraticTowerSignRecipe.read_bound _ _ _ _))

theorem step_negative_at (h B D S b A : PTm n) (hL : Γ ⊢[PRAAx] localLaw h (budget h B D) D S)
    (hb : Γ ⊢[PRAAx] le b B) (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b)
    (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b) : Γ ⊢[PRAAx]
    read (succ h) B (QuadraticTowerSignTable.step h B S D) (negated (succ h) A) ≐
      opposite (read (succ h) B (QuadraticTowerSignTable.step h B S D) A) := by
  have an := QuadraticTowerMultiplicationZero.normalized_height (succ h) A b ha
  have left := (QuadraticTowerSignCoherence.step_read_normalized h B S D _
    (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ (QuadraticTowerSignRecipe.negated_height (succ h) A b ha) hb)).eqTrans
      ((QuadraticTowerSignTable.recipe_operand_congr _ _ _ _ _ _ (QuadraticTowerArrayNormalization.normalized_negated (succ h) A)).eqTrans
        ((QuadraticTowerSignTable.recipe_operand_congr _ _ _ _ _ _ (negated_normalized (succ h) A).eqSymm).eqTrans
          (recipe_negative h B D S b (normalized (succ h) A) hL hb hD an)))
  exact left.eqTrans (opposite_congr (QuadraticTowerSignCoherence.step_read_normalized h B S D A
    (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ ha hb)).eqSymm)

theorem local_step (h B D S : PTm n) (hL : Γ ⊢[PRAAx] localLaw h (budget h B D) D S) : Γ ⊢[PRAAx]
    localLaw (succ h) B D (QuadraticTowerSignTable.step h B S D) := by
  have ls : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      localLaw (Syn.shift (Syn.shift h)) (budget (Syn.shift (Syn.shift h)) (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift D)))
        (Syn.shift (Syn.shift D)) (Syn.shift (Syn.shift S)) := by
    simpa only [Fm.shift,subst_localLaw,QuadraticTowerMultiplicationTable.subst_budget,Syn.shift] using hL.shift.shift
  refine .allI (.impI (.allI (.impI (.impI (.impI ?_)))))
  let h' := Syn.shift (Syn.shift h)
  let B' := Syn.shift (Syn.shift B)
  let D' := Syn.shift (Syn.shift D)
  let S' := Syn.shift (Syn.shift S)
  let b := (var 1 : PTm (n+2))
  let u := (var 0 : PTm (n+2))
  let R := horizon (succ h') b
  let Δ := arrayHeight (succ h') (word (succ h') b u) b :: radicandsHeight D' (succ h') b ::
    lt u R :: lt b (succ B') :: (Γ.map Fm.shift).map Fm.shift
  have ha : Δ ⊢[PRAAx] arrayHeight (succ h') (word (succ h') b u) b := Prf.hyp0
  have hd : Δ ⊢[PRAAx] radicandsHeight D' (succ h') b := .hyp (by simp [Δ])
  have hbRange : Δ ⊢[PRAAx] lt b (succ B') := .hyp (by simp [Δ])
  have hb : Δ ⊢[PRAAx] le b B' := (succ_monus_succ _ _).eqSymm.eqTrans hbRange
  have lower : Δ ⊢[PRAAx] localLaw h' (budget h' B' D') D' S' := ls.wk.wk.wk.wk
  simpa [Δ,h',B',D',S',b,u,R,Fm.shift,Syn.shift] using
    step_negative_at (Γ := Δ) h' B' D' S' b (word (succ h') b u) lower hb hd ha


theorem local_base (B D : PTm n) : Γ ⊢[PRAAx] localLaw zero B D (QuadraticTowerSignTable.base B) := by
  refine .allI (.impI (.allI (.impI (.impI (.impI ?_)))))
  let B' := Syn.shift (Syn.shift B)
  let D' := Syn.shift (Syn.shift D)
  let b := (var 1 : PTm (n+2))
  let u := (var 0 : PTm (n+2))
  let R := horizon zero b
  let Δ := arrayHeight zero (word zero b u) b :: radicandsHeight D' zero b ::
    lt u R :: lt b (succ B') :: (Γ.map Fm.shift).map Fm.shift
  have hbRange : Δ ⊢[PRAAx] lt b (succ B') := .hyp (by simp [Δ])
  have hb : Δ ⊢[PRAAx] le b B' := (succ_monus_succ _ _).eqSymm.eqTrans hbRange
  have ha : Δ ⊢[PRAAx] arrayHeight zero (word zero b u) b := Prf.hyp0
  simpa [Δ,B',D',b,u,R,Fm.shift,Syn.shift] using base_negative (Γ := Δ) B' (word zero b u)
    (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ ha hb)

theorem local_congr {h h' B B' D D' S S' : PTm n} (hh : Γ ⊢[PRAAx] h ≐ h') (hb : Γ ⊢[PRAAx] B ≐ B')
    (hd : Γ ⊢[PRAAx] D ≐ D') (hs : Γ ⊢[PRAAx] S ≐ S') (p : Γ ⊢[PRAAx] localLaw h B D S) : Γ ⊢[PRAAx] localLaw h' B' D' S' := by
  have proof := Prf.eqSubst (Γ := Γ) (localLaw (var 0) (var 1) (var 2) (var 3) : Fm PTm 4)
    ![h,B,D,S] ![h',B',D',S'] (fun i => by fin_cases i; exact hh; exact hb; exact hd; exact hs) (by simpa using p)
  simpa using proof

open QuadraticTowerMultiplicationHeight (cap)
open QuadraticTowerSignCoherence (state state_zero state_succ)

def forwardLaw (H B D t : PTm n) : Fm PTm n := le t H ⟶ localLaw t (cap H B t D) D (state H B t D)
def forwardSyntax (H B D t : PTm n) : BFm n := .imp (.le t H) (localSyntax t (cap H B t D) D (state H B t D))
ipra_subst forwardLaw
theorem forward_formula (H B D t : PTm n) : formula (forwardSyntax H B D t) = forwardLaw H B D t := by
  simp [forwardSyntax,forwardLaw,formula,local_formula,BFm.le,le]

theorem forward_zero (H B D : PTm n) : Γ ⊢[PRAAx] forwardLaw H B D zero :=
  .impI (local_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (state_zero H B D).wk.eqSymm (local_base _ D))
theorem forward_step (H B D t : PTm n) (ih : Γ ⊢[PRAAx] forwardLaw H B D t) : Γ ⊢[PRAAx] forwardLaw H B D (succ t) := by
  refine .impI ?_
  let Δ := le (succ t) H :: Γ
  have ht : Δ ⊢[PRAAx] lt t H := Prf.hyp0
  have previous : Δ ⊢[PRAAx] localLaw t (cap H B t D) D (state H B t D) :=
    .impE ih.wk (le_trans (le_succ_self t) ht)
  have adjusted : Δ ⊢[PRAAx] localLaw t (budget t (cap H B (succ t) D) D) D (state H B t D) :=
    local_congr (.eqRefl _) (QuadraticTowerMultiplicationHeight.cap_link H B t D ht) (.eqRefl _) (.eqRefl _) previous
  have next := local_step t (cap H B (succ t) D) D (state H B t D) adjusted
  exact local_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (state_succ H B t D).eqSymm next

theorem forward_all (H B D : PTm n) : Γ ⊢[PRAAx] .all
    (formula (forwardSyntax (Syn.shift H) (Syn.shift B) (Syn.shift D) (var 0))) := by
  refine Foundations.BoundedSyntaxInduction.induction_of_formula _ (forward_formula _ _ _ _) ?_ ?_
  · simpa only [subst_forwardLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using forward_zero (Γ := Γ) H B D
  · simpa only [subst_forwardLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
      forward_step (Syn.shift H) (Syn.shift B) (Syn.shift D) (var 0) (Prf.hyp0 (Γ := Γ.map Fm.shift))

theorem table_negation (h B D : PTm n) : Γ ⊢[PRAAx] localLaw h B D (QuadraticTowerSignTable.table h B D) := by
  have gate : Γ ⊢[PRAAx] forwardLaw h B D h := by
    simpa only [forward_formula,subst_forwardLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using (forward_all (Γ := Γ) h B D).allE h
  have terminal : Γ ⊢[PRAAx] localLaw h (cap h B h D) D (state h B h D) := .impE gate (le_refl h)
  exact local_congr (.eqRefl _) (Foundations.BackwardDemand.horizon_final QuadraticTowerMultiplicationTable.demandF h B D)
    (.eqRefl _) (.eqRefl _) terminal

/-- Uniform sign negation for the SAME actual returned query. -/
theorem query_negative (h B D A b : PTm n) (hb : Γ ⊢[PRAAx] le b B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b) : Γ ⊢[PRAAx]
    QuadraticTowerSignTable.query h B D (negated h A) ≐ opposite (QuadraticTowerSignTable.query h B D A) :=
  read_negative h B D _ b A (table_negation h B D) hb hD ha

theorem query_zero_iff (h B D A b : PTm n) (hb : Γ ⊢[PRAAx] le b B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b) : Γ ⊢[PRAAx]
    Fm.iff (QuadraticTowerSignTable.query h B D (negated h A) ≐ zero) (QuadraticTowerSignTable.query h B D A ≐ zero) :=
  .andI (.impI (opposite_zero_reflect _ (QuadraticTowerSignTable.query_bound _ _ _ _)
    ((query_negative h B D A b hb.wk hD.wk ha.wk).eqSymm.eqTrans Prf.hyp0)))
    (.impI ((query_negative h B D A b hb.wk hD.wk ha.wk).eqTrans ((opposite_congr Prf.hyp0).eqTrans opposite_zero)))

theorem query_positive_iff (h B D A b : PTm n) (hb : Γ ⊢[PRAAx] le b B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b) : Γ ⊢[PRAAx]
    Fm.iff (QuadraticTowerSignTable.query h B D (negated h A) ≐ one) (QuadraticTowerSignTable.query h B D A ≐ two) := by
  refine .andI (.impI ?_) (.impI ?_)
  · exact (opposite_involution _ (QuadraticTowerSignTable.query_bound _ _ _ _)).eqSymm.eqTrans
      ((opposite_congr ((query_negative h B D A b hb.wk hD.wk ha.wk).eqSymm.eqTrans Prf.hyp0)).eqTrans opposite_one)
  · exact (query_negative h B D A b hb.wk hD.wk ha.wk).eqTrans ((opposite_congr Prf.hyp0).eqTrans opposite_two)


def source (h B D A b : PTm n) : Fm PTm n := le b B ⋏ (radicandsHeight D h b ⋏ arrayHeight h A b)
ipra_subst source

def output (h B D A : PTm n) : PTm n := pairT (negated h A)
  (pairT (QuadraticTowerSignTable.query h B D (negated h A))
    (pairT (QuadraticTowerSignTable.query h B D A) (opposite (QuadraticTowerSignTable.query h B D A))))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (h B D A : PTm n) : PTm n := PTm.app outputF ![h,B,D,A]
ipra_subst output
ipra_subst run

theorem program_at (h B D A : PTm n) : Γ ⊢[PRAAx] run h B D A ≐ output h B D A := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![h,B,D,A]
theorem returned_array (h B D A : PTm n) : Γ ⊢[PRAAx] fstT (run h B D A) ≐ negated h A :=
  (program_at _ _ _ _).fstE
theorem returned_tail (h B D A : PTm n) : Γ ⊢[PRAAx] sndT (run h B D A) ≐
    pairT (QuadraticTowerSignTable.query h B D (negated h A))
      (pairT (QuadraticTowerSignTable.query h B D A) (opposite (QuadraticTowerSignTable.query h B D A))) :=
  (program_at _ _ _ _).sndE
theorem returned_negative (h B D A : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run h B D A)) ≐ QuadraticTowerSignTable.query h B D (negated h A) :=
  (returned_tail _ _ _ _).fstE
theorem returned_comparison (h B D A : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run h B D A)) ≐
    pairT (QuadraticTowerSignTable.query h B D A) (opposite (QuadraticTowerSignTable.query h B D A)) :=
  (returned_tail _ _ _ _).sndE
theorem returned_original (h B D A : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run h B D A))) ≐ QuadraticTowerSignTable.query h B D A :=
  (returned_comparison _ _ _ _).fstE
theorem returned_opposite (h B D A : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run h B D A))) ≐ opposite (QuadraticTowerSignTable.query h B D A) :=
  (returned_comparison _ _ _ _).sndE

theorem returned_equal (h B D A b : PTm n) (p : Γ ⊢[PRAAx] source h B D A b) : Γ ⊢[PRAAx]
    fstT (sndT (run h B D A)) ≐ sndT (sndT (sndT (run h B D A))) :=
  (returned_negative _ _ _ _).eqTrans ((query_negative h B D A b p.andE₁ p.andE₂.andE₁ p.andE₂.andE₂).eqTrans (returned_opposite _ _ _ _).eqSymm)
theorem returned_zero_iff (h B D A b : PTm n) (p : Γ ⊢[PRAAx] source h B D A b) : Γ ⊢[PRAAx]
    Fm.iff (fstT (sndT (run h B D A)) ≐ zero) (fstT (sndT (sndT (run h B D A))) ≐ zero) := by
  refine .andI (.impI ?_) (.impI ?_)
  · exact (returned_original _ _ _ _).eqTrans
      (.impE (query_zero_iff h B D A b p.andE₁.wk p.andE₂.andE₁.wk p.andE₂.andE₂.wk).andE₁
        ((returned_negative _ _ _ _).eqSymm.eqTrans Prf.hyp0))
  · exact (returned_negative _ _ _ _).eqTrans
      (.impE (query_zero_iff h B D A b p.andE₁.wk p.andE₂.andE₁.wk p.andE₂.andE₂.wk).andE₂
        ((returned_original _ _ _ _).eqSymm.eqTrans Prf.hyp0))

theorem actual_three_tag_dispatch_negation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 0) (succ two) ⟶ lt (var 1) (succ two) ⟶ lt (var 2) (succ two) ⟶
      dispatch (opposite (var 0)) (opposite (var 1)) (var 2) ≐ opposite (dispatch (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (.impI (dispatch_negative _ _ _ (.hyp (by simp)) Prf.hyp1 Prf.hyp0))))
theorem actual_original_rational_ground_sign_negative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (QuadraticTowerSignTable.groundTag (RationalArithmetic.negative (var 0)) ≐ opposite (QuadraticTowerSignTable.groundTag (var 0))) :=
  closeUniv 1 (ground_negative _)
theorem actual_sign_negation_finite_predicate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (localLaw (var 0) (var 1) (var 2) (QuadraticTowerSignTable.table (var 0) (var 1) (var 2))) :=
  closeUniv 3 (table_negation _ _ _)
theorem actual_sign_negation_state_induction_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (.all (formula (forwardSyntax (Syn.shift (var 0)) (Syn.shift (var 1)) (Syn.shift (var 2)) (var 0)))) :=
  closeUniv 3 (forward_all _ _ _)
theorem original_actual_uniform_sign_negation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      QuadraticTowerSignTable.query (var 0) (var 1) (var 2) (negated (var 0) (var 3)) ≐
        opposite (QuadraticTowerSignTable.query (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 5 (.impI (query_negative _ _ _ _ (var 4) Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))
theorem original_actual_uniform_sign_zero_iff_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      Fm.iff (QuadraticTowerSignTable.query (var 0) (var 1) (var 2) (negated (var 0) (var 3)) ≐ zero)
        (QuadraticTowerSignTable.query (var 0) (var 1) (var 2) (var 3) ≐ zero)) :=
  closeUniv 5 (.impI (query_zero_iff _ _ _ _ (var 4) Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))
theorem original_actual_uniform_sign_reversal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      Fm.iff (QuadraticTowerSignTable.query (var 0) (var 1) (var 2) (negated (var 0) (var 3)) ≐ one)
        (QuadraticTowerSignTable.query (var 0) (var 1) (var 2) (var 3) ≐ two)) :=
  closeUniv 5 (.impI (query_positive_iff _ _ _ _ (var 4) Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))
theorem actual_sign_negation_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (program_at _ _ _ _)
theorem original_returned_sign_negation_equal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      fstT (sndT (run (var 0) (var 1) (var 2) (var 3))) ≐ sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3))))) :=
  closeUniv 5 (.impI (returned_equal _ _ _ _ (var 4) Prf.hyp0))
theorem original_returned_sign_negation_zero_iff_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      Fm.iff (fstT (sndT (run (var 0) (var 1) (var 2) (var 3))) ≐ zero)
        (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3)))) ≐ zero)) :=
  closeUniv 5 (.impI (returned_zero_iff _ _ _ _ (var 4) Prf.hyp0))

end LeanProofs.IPRA.Algebra.QuadraticTowerSignNegation
