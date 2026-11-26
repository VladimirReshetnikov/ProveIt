import IPRADerivations.Algebra.QuadraticTowerOppositeMultiplier
import IPRADerivations.Algebra.QuadraticTowerExtensionSign

/-!
# Original opposite-sign dispatch and its actual multiplier certificate

The actual conditional third query is the ORIGINAL norm read. Opposite
original lower tags identify the selected signed-norm sign with the
ORIGINAL parent sign. The concrete returned-product and cone adapters
retain their derived numerical caps; no lower cone-closure provider or
semantic-zero-to-literal-zero premise is supplied.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.QuadraticTowerOppositeSignCertificate

open_ipra
open QuadraticTowerArrayCodec (arrayHeight normalized)
open QuadraticTowerCoefficientArithmetic (added negated added_congr negated_congr)
open QuadraticTowerMultiplicationTable (budget leftHalf rightHalf query)
open QuadraticTowerMultiplicationHeight (radicandsHeight)
open QuadraticTowerSignRecipe (norm thirdTag firstTag secondTag tagProduct)
open QuadraticTowerConeTest (lowerFirst lowerSecond lowerRadicand)
open QuadraticTowerOppositeMultiplier (signedNorm)
open QuadraticTowerExtensionSign (sourceCap returnedProduct returnedNorm productSign)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The original recipe's norm ignores the actual coefficient
normalization of its original parent operand, even as a total program. -/
theorem norm_normalized (h B D A : PTm n) : Γ ⊢[PRAAx]
    norm h B D (normalized (succ h) A) ≐ norm h B D A := by
  let K := budget h B D
  have aa := (QuadraticTowerMultiplicationNegative.query_operands_congr (Γ := Γ) h K D
    (QuadraticTowerArrayNormalization.left_half_normalized h A)
    (QuadraticTowerArrayNormalization.left_half_normalized h A)).eqTrans
      (QuadraticTowerOperandProperness.query_normalized h K D _ _)
  have bb := (QuadraticTowerMultiplicationNegative.query_operands_congr (Γ := Γ) h K D
    (QuadraticTowerArrayNormalization.right_half_normalized h A)
    (QuadraticTowerArrayNormalization.right_half_normalized h A)).eqTrans
      (QuadraticTowerOperandProperness.query_normalized h K D _ _)
  exact added_congr (.eqRefl h) aa (negated_congr (.eqRefl h)
    (QuadraticTowerMultiplicationNegative.query_operands_congr h K D (.eqRefl (entry D h)) bb))

theorem third_original (h B D A : PTm n) (hn : Γ ⊢[PRAAx] neg (lowerFirst h B D A ≐ zero)) : Γ ⊢[PRAAx]
    thirdTag h B D (QuadraticTowerSignTable.table h (budget h B D) D) (normalized (succ h) A) ≐
      QuadraticTowerSignTable.query h (budget h B D) D (norm h B D A) := by
  have firstNonzero := QuadraticIntegerSignDispatch.nonzero_from_code (QuadraticTowerConeTest.first_normalized h B D A) hn
  have actual := (QuadraticTowerSignRecipe.third_when_a_nonzero h B D
    (QuadraticTowerSignTable.table h (budget h B D) D) (normalized (succ h) A) firstNonzero).eqTrans (norm_normalized h B D A)
  exact QuadraticTowerSignRecipe.read_operand_congr _ _ _ _ _ actual

theorem parent_opposite (h B D A : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A B)
    (hf : Γ ⊢[PRAAx] neg (lowerFirst h B D A ≐ zero))
    (hs : Γ ⊢[PRAAx] neg (lowerSecond h B D A ≐ zero))
    (hd : Γ ⊢[PRAAx] neg (lowerFirst h B D A ≐ lowerSecond h B D A)) : Γ ⊢[PRAAx]
    QuadraticTowerSignTable.query (succ h) B D A ≐
      tagProduct (lowerFirst h B D A) (QuadraticTowerSignTable.query h (budget h B D) D (norm h B D A)) := by
  let S := QuadraticTowerSignTable.table h (budget h B D) D
  have first := QuadraticTowerConeTest.first_normalized (Γ := Γ) h B D A
  have second := QuadraticTowerConeTest.second_normalized (Γ := Γ) h B D A
  have different : Γ ⊢[PRAAx] neg (firstTag h B D S (normalized (succ h) A) ≐ secondTag h B D S (normalized (succ h) A)) :=
    .impI (.impE hd.wk ((first.wk.eqSymm.eqTrans Prf.hyp0).eqTrans second.wk))
  exact (QuadraticTowerSignTable.query_succ h B D A ha).eqTrans
    ((QuadraticTowerSignRecipe.dispatch_opposite _ _ _
      (QuadraticIntegerSignDispatch.nonzero_from_code first hf)
      (QuadraticIntegerSignDispatch.nonzero_from_code second hs) different).eqTrans
        (QuadraticTowerSignRecipe.tag_product_congr first (third_original h B D A hf)))

theorem parent_plus (h B D A b : PTm n) (p : Γ ⊢[PRAAx] QuadraticTowerConeTest.source h B D A b)
    (hf : Γ ⊢[PRAAx] lowerFirst h B D A ≐ one) (hs : Γ ⊢[PRAAx] lowerSecond h B D A ≐ two) : Γ ⊢[PRAAx]
    QuadraticTowerSignTable.query (succ h) B D A ≐ QuadraticTowerSignTable.query h (budget h B D) D (norm h B D A) := by
  have different : Γ ⊢[PRAAx] neg (lowerFirst h B D A ≐ lowerSecond h B D A) :=
    .impI (.impE QuadraticIntegerSignDispatch.different_one_two ((hf.wk.eqSymm.eqTrans Prf.hyp0).eqTrans hs.wk))
  exact (parent_opposite h B D A
    (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ p.andE₂.andE₂ p.andE₁)
    (QuadraticIntegerSignDispatch.nonzero_from_code hf QuadraticIntegerSignDispatch.nonzero_one)
    (QuadraticIntegerSignDispatch.nonzero_from_code hs QuadraticIntegerSignDispatch.nonzero_two) different).eqTrans
      ((QuadraticTowerSignRecipe.tag_product_congr hf (.eqRefl _)).eqTrans
        (QuadraticTowerSignNegation.tag_product_unit _ (QuadraticTowerSignTable.query_bound _ _ _ _)))

theorem parent_minus (h B D A b : PTm n) (p : Γ ⊢[PRAAx] QuadraticTowerConeTest.source h B D A b)
    (hf : Γ ⊢[PRAAx] lowerFirst h B D A ≐ two) (hs : Γ ⊢[PRAAx] lowerSecond h B D A ≐ one) : Γ ⊢[PRAAx]
    QuadraticTowerSignTable.query (succ h) B D A ≐
      QuadraticTowerSignNegation.opposite (QuadraticTowerSignTable.query h (budget h B D) D (norm h B D A)) := by
  have different : Γ ⊢[PRAAx] neg (lowerFirst h B D A ≐ lowerSecond h B D A) :=
    .impI (.impE QuadraticIntegerSignDispatch.different_two_one ((hf.wk.eqSymm.eqTrans Prf.hyp0).eqTrans hs.wk))
  exact (parent_opposite h B D A
    (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ p.andE₂.andE₂ p.andE₁)
    (QuadraticIntegerSignDispatch.nonzero_from_code hf QuadraticIntegerSignDispatch.nonzero_two)
    (QuadraticIntegerSignDispatch.nonzero_from_code hs QuadraticIntegerSignDispatch.nonzero_one) different).eqTrans
      (QuadraticTowerSignRecipe.tag_product_congr hf (.eqRefl _))

theorem signed_norm_sign (h B D A b : PTm n) (p : Γ ⊢[PRAAx] QuadraticTowerOppositeMultiplier.input h B D A b) : Γ ⊢[PRAAx]
    QuadraticTowerSignTable.query h (budget h B D) D (signedNorm h B D A) ≐ QuadraticTowerSignTable.query (succ h) B D A := by
  refine .orE p.andE₂.andE₁ ?_ ?_
  · exact (QuadraticTowerSignRecipe.read_operand_congr _ _ _ _ _ (QuadraticTowerOppositeMultiplier.signedNorm_plus h B D A Prf.hyp0.andE₁)).eqTrans
      (parent_plus h B D A b p.andE₁.wk Prf.hyp0.andE₁ Prf.hyp0.andE₂).eqSymm
  · have lower := QuadraticTowerMultiplicationHeight.radicands_mono D h b (sourceCap h b)
      (QuadraticTowerMultiplicationHeight.radicands_prefix D h (succ h) b p.andE₁.andE₂.andE₁ (le_succ_self h))
      (QuadraticTowerGrowth.growth_inflation _ _)
    have height := QuadraticTowerSignRecipe.norm_height h B D A b p.andE₁.andE₁ p.andE₁.andE₂.andE₁ p.andE₁.andE₂.andE₂
    have negative := QuadraticTowerSignNegation.query_negative h (budget h B D) D (norm h B D A) (sourceCap h b)
      (QuadraticTowerExtensionSign.original_child_cap h B D A b p.andE₁) lower height
    exact (QuadraticTowerSignRecipe.read_operand_congr _ _ _ _ _ (QuadraticTowerOppositeMultiplier.signedNorm_minus h B D A Prf.hyp0.andE₁)).eqTrans
      (negative.wk.eqTrans (parent_minus h B D A b p.andE₁.wk Prf.hyp0.andE₁ Prf.hyp0.andE₂).eqSymm)

theorem returned_norm_sign (h B D A b : PTm n) (p : Γ ⊢[PRAAx] QuadraticTowerOppositeMultiplier.input h B D A b) : Γ ⊢[PRAAx]
    QuadraticTowerExtensionSign.normSign h B D A ≐ QuadraticTowerSignTable.query (succ h) B D A :=
  (QuadraticTowerSignRecipe.read_operand_congr h (budget h B D) (QuadraticTowerSignTable.table h (budget h B D) D)
    _ _ (QuadraticTowerOppositeMultiplier.returned_norm h B D A)).eqTrans (signed_norm_sign h B D A b p)

/-- The product is the SAME actual field returned by OppositeMultiplier,
and the comparison is with the ORIGINAL parent query, not an output law. -/
theorem returned_product_sign (h B D A b : PTm n) (p : Γ ⊢[PRAAx] QuadraticTowerOppositeMultiplier.input h B D A b) : Γ ⊢[PRAAx]
    productSign h B D A b ≐ QuadraticTowerSignTable.query (succ h) B D A :=
  (QuadraticTowerExtensionSign.returned_product_sign h B D A b p).eqTrans (returned_norm_sign h B D A b p)

theorem returned_multiplier_positive (h B D A b : PTm n) (p : Γ ⊢[PRAAx] QuadraticTowerOppositeMultiplier.input h B D A b) : Γ ⊢[PRAAx]
    QuadraticTowerSignTable.query (succ h) B D (fstT (QuadraticTowerOppositeMultiplier.run h B D A)) ≐ one :=
  (QuadraticTowerSignRecipe.read_operand_congr (succ h) B (QuadraticTowerSignTable.table (succ h) B D) _ _
    (QuadraticTowerOppositeMultiplier.returned_multiplier h B D A)).eqTrans
      (QuadraticTowerOppositeMultiplier.original_certificate h B D A b p).andE₂.andE₁

theorem product_inserted (h B D A b : PTm n) (p : Γ ⊢[PRAAx] QuadraticTowerOppositeMultiplier.input h B D A b) : Γ ⊢[PRAAx]
    returnedProduct h B D A ≐ QuadraticTowerExtensionSign.inserted h (signedNorm h B D A) :=
  (QuadraticTowerOppositeMultiplier.returned_product h B D A).eqTrans
    ((QuadraticTowerOppositeMultiplier.original_certificate h B D A b p).andE₂.andE₂.eqTrans
      (QuadraticTowerExtensionSign.inserted_signedNorm h B D A).eqSymm)

theorem lower_first_congr (h B D : PTm n) {A C : PTm n} (e : Γ ⊢[PRAAx] A ≐ C) : Γ ⊢[PRAAx]
    lowerFirst h B D A ≐ lowerFirst h B D C := by
  ipra_congr (lowerFirst (var 0) (var 1) (var 2) (var 3) : PTm 4) with [.eqRefl h, .eqRefl B, .eqRefl D, e]
theorem lower_second_congr (h B D : PTm n) {A C : PTm n} (e : Γ ⊢[PRAAx] A ≐ C) : Γ ⊢[PRAAx]
    lowerSecond h B D A ≐ lowerSecond h B D C := by
  ipra_congr (lowerSecond (var 0) (var 1) (var 2) (var 3) : PTm 4) with [.eqRefl h, .eqRefl B, .eqRefl D, e]

theorem inserted_first (h B D L : PTm n) : Γ ⊢[PRAAx]
    lowerFirst h B D (QuadraticTowerExtensionSign.inserted h L) ≐ QuadraticTowerSignTable.query h (budget h B D) D L :=
  (QuadraticTowerConeTest.first_normalized h B D (QuadraticTowerExtensionSign.inserted h L)).eqSymm.eqTrans
    (QuadraticTowerExtensionSign.first_tag h B D L)
theorem inserted_second (h B D L : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    lowerSecond h B D (QuadraticTowerExtensionSign.inserted h L) ≐ zero :=
  (QuadraticTowerConeTest.second_normalized h B D (QuadraticTowerExtensionSign.inserted h L)).eqSymm.eqTrans
    (QuadraticTowerExtensionSign.second_tag h B D L hB)

theorem product_first (h B D A b : PTm n) (p : Γ ⊢[PRAAx] QuadraticTowerOppositeMultiplier.input h B D A b) : Γ ⊢[PRAAx]
    lowerFirst h (sourceCap h b) D (returnedProduct h B D A) ≐ QuadraticTowerSignTable.query (succ h) B D A := by
  let T := sourceCap h b
  have lower := QuadraticTowerMultiplicationHeight.radicands_mono D h b T
    (QuadraticTowerMultiplicationHeight.radicands_prefix D h (succ h) b p.andE₁.andE₂.andE₁ (le_succ_self h))
    (QuadraticTowerGrowth.growth_inflation _ _)
  have coherent := QuadraticTowerSignCoherence.query_cap_independent h (budget h T D) (budget h B D) D (signedNorm h B D A) T
    (QuadraticTowerSignEmbedding.budget_inflation h T D) (QuadraticTowerExtensionSign.original_child_cap h B D A b p.andE₁)
    lower (QuadraticTowerExtensionSign.signedNorm_height h B D A b p.andE₁)
  exact (lower_first_congr h T D (product_inserted h B D A b p)).eqTrans
    ((inserted_first h T D (signedNorm h B D A)).eqTrans (coherent.eqTrans (signed_norm_sign h B D A b p)))

theorem product_second (h B D A b : PTm n) (p : Γ ⊢[PRAAx] QuadraticTowerOppositeMultiplier.input h B D A b) : Γ ⊢[PRAAx]
    lowerSecond h (sourceCap h b) D (returnedProduct h B D A) ≐ zero :=
  (lower_second_congr h (sourceCap h b) D (product_inserted h B D A b p)).eqTrans
    (inserted_second h (sourceCap h b) D (signedNorm h B D A) (QuadraticTowerExtensionSign.sourceCap_positive h B D A b p.andE₁))

theorem product_radicand (h B D A b : PTm n) (p : Γ ⊢[PRAAx] QuadraticTowerOppositeMultiplier.input h B D A b) : Γ ⊢[PRAAx]
    lowerRadicand h (sourceCap h b) D ≐ one := by
  let T := sourceCap h b
  have bg : Γ ⊢[PRAAx] le b T := QuadraticTowerGrowth.growth_inflation _ _
  have lower := QuadraticTowerMultiplicationHeight.radicands_prefix D h (succ h) b p.andE₁.andE₂.andE₁ (le_succ_self h)
  have dh := QuadraticTowerMultiplicationHeight.radicand_at D (succ h) b h p.andE₁.andE₂.andE₁ (le_refl _)
  exact (QuadraticTowerSignCoherence.query_cap_independent h (budget h T D) (budget h B D) D (entry D h) b
    (le_trans bg (QuadraticTowerSignEmbedding.budget_inflation h T D))
    (le_trans p.andE₁.andE₁ (QuadraticTowerSignEmbedding.budget_inflation h B D)) lower dh).eqTrans p.andE₂.andE₂

theorem product_source (h B D A b : PTm n) (p : Γ ⊢[PRAAx] QuadraticTowerOppositeMultiplier.input h B D A b) : Γ ⊢[PRAAx]
    QuadraticTowerConeTest.source h (sourceCap h b) D (returnedProduct h B D A) (sourceCap h b) := by
  have height := QuadraticTowerMultiplicationHeight.array_congr (.eqRefl (succ h)) (product_inserted h B D A b p).eqSymm (.eqRefl _)
    (QuadraticTowerExtensionSign.inserted_height h (signedNorm h B D A) (sourceCap h b)
      (QuadraticTowerExtensionSign.sourceCap_positive h B D A b p.andE₁) (QuadraticTowerExtensionSign.signedNorm_height h B D A b p.andE₁))
  exact .andI (le_refl _) (.andI
    (QuadraticTowerMultiplicationHeight.radicands_mono _ _ _ _ p.andE₁.andE₂.andE₁ (QuadraticTowerGrowth.growth_inflation _ _)) height)

theorem positive_product_flag (h B D A b : PTm n) (p : Γ ⊢[PRAAx] QuadraticTowerOppositeMultiplier.input h B D A b)
    (hp : Γ ⊢[PRAAx] QuadraticTowerSignTable.query (succ h) B D A ≐ one) : Γ ⊢[PRAAx]
    QuadraticTowerConeTest.flag h (sourceCap h b) D (returnedProduct h B D A) ≐ one := by
  have first := (product_first h B D A b p).eqTrans hp
  exact .impE (QuadraticTowerConeTest.flag_reflection _ _ _ _).andE₂
    (.andI (.orI₂ first) (.andI (.orI₁ (product_second h B D A b p)) (.andI (.orI₁ first) (product_radicand h B D A b p))))

/-- Positive original parent sign gives a genuine computed cone witness
for the actual returned product, including all FOUR actual addresses. -/
theorem positive_product_certificate (h B D A b : PTm n) (p : Γ ⊢[PRAAx] QuadraticTowerOppositeMultiplier.input h B D A b)
    (hp : Γ ⊢[PRAAx] QuadraticTowerSignTable.query (succ h) B D A ≐ one) : Γ ⊢[PRAAx]
    (QuadraticTowerConeTest.flag h (sourceCap h b) D (returnedProduct h B D A) ≐ one) ⋏
      ((productSign h B D A b ≐ one) ⋏ QuadraticTowerConeTest.addresses h (sourceCap h b) D (returnedProduct h B D A)) :=
  .andI (positive_product_flag h B D A b p hp)
    (QuadraticTowerConeTest.source_certificate h (sourceCap h b) D (returnedProduct h B D A) (sourceCap h b)
      (product_source h B D A b p) (positive_product_flag h B D A b p hp))

def negativeProduct (h B D A : PTm n) : PTm n := negated (succ h) (returnedProduct h B D A)
ipra_subst negativeProduct

theorem negative_product_first (h B D A b : PTm n) (p : Γ ⊢[PRAAx] QuadraticTowerOppositeMultiplier.input h B D A b) : Γ ⊢[PRAAx]
    lowerFirst h (sourceCap h b) D (negativeProduct h B D A) ≐
      QuadraticTowerSignNegation.opposite (QuadraticTowerSignTable.query (succ h) B D A) := by
  let T := sourceCap h b
  have source := product_source h B D A b p
  have negative := QuadraticTowerSignNegation.query_negative h (budget h T D) D (leftHalf h (returnedProduct h B D A)) T
    (QuadraticTowerSignEmbedding.budget_inflation h T D)
    (QuadraticTowerMultiplicationHeight.radicands_prefix D h (succ h) T source.andE₂.andE₁ (le_succ_self h))
    (QuadraticTowerMultiplicationHeight.left_height h _ T source.andE₂.andE₂)
  exact (QuadraticTowerSignRecipe.read_operand_congr h (budget h T D) (QuadraticTowerSignTable.table h (budget h T D) D)
    _ _ (QuadraticTowerMultiplicationNegative.left_negative h (returnedProduct h B D A))).eqTrans
      (negative.eqTrans (QuadraticTowerSignNegation.opposite_congr (product_first h B D A b p)))

theorem negative_product_second (h B D A b : PTm n) (p : Γ ⊢[PRAAx] QuadraticTowerOppositeMultiplier.input h B D A b) : Γ ⊢[PRAAx]
    lowerSecond h (sourceCap h b) D (negativeProduct h B D A) ≐ zero := by
  let T := sourceCap h b
  have source := product_source h B D A b p
  have negative := QuadraticTowerSignNegation.query_negative h (budget h T D) D (rightHalf h (returnedProduct h B D A)) T
    (QuadraticTowerSignEmbedding.budget_inflation h T D)
    (QuadraticTowerMultiplicationHeight.radicands_prefix D h (succ h) T source.andE₂.andE₁ (le_succ_self h))
    (QuadraticTowerMultiplicationHeight.right_height h _ T source.andE₂.andE₂)
  exact (QuadraticTowerSignRecipe.read_operand_congr h (budget h T D) (QuadraticTowerSignTable.table h (budget h T D) D)
    _ _ (QuadraticTowerMultiplicationNegative.right_negative h (returnedProduct h B D A))).eqTrans
      (negative.eqTrans ((QuadraticTowerSignNegation.opposite_congr (product_second h B D A b p)).eqTrans QuadraticTowerSignNegation.opposite_zero))

theorem negative_product_flag (h B D A b : PTm n) (p : Γ ⊢[PRAAx] QuadraticTowerOppositeMultiplier.input h B D A b)
    (hp : Γ ⊢[PRAAx] QuadraticTowerSignTable.query (succ h) B D A ≐ two) : Γ ⊢[PRAAx]
    QuadraticTowerConeTest.flag h (sourceCap h b) D (negativeProduct h B D A) ≐ one := by
  have first := (negative_product_first h B D A b p).eqTrans
    ((QuadraticTowerSignNegation.opposite_congr hp).eqTrans QuadraticTowerSignNegation.opposite_two)
  exact .impE (QuadraticTowerConeTest.flag_reflection _ _ _ _).andE₂
    (.andI (.orI₂ first) (.andI (.orI₁ (negative_product_second h B D A b p)) (.andI (.orI₁ first) (product_radicand h B D A b p))))

theorem negative_product_certificate (h B D A b : PTm n) (p : Γ ⊢[PRAAx] QuadraticTowerOppositeMultiplier.input h B D A b)
    (hp : Γ ⊢[PRAAx] QuadraticTowerSignTable.query (succ h) B D A ≐ two) : Γ ⊢[PRAAx]
    (QuadraticTowerConeTest.flag h (sourceCap h b) D (negativeProduct h B D A) ≐ one) ⋏
      ((QuadraticTowerSignTable.query (succ h) (sourceCap h b) D (negativeProduct h B D A) ≐ one) ⋏
        QuadraticTowerConeTest.addresses h (sourceCap h b) D (negativeProduct h B D A)) := by
  have source := product_source h B D A b p
  have negSource : Γ ⊢[PRAAx] QuadraticTowerConeTest.source h (sourceCap h b) D (negativeProduct h B D A) (sourceCap h b) :=
    .andI (le_refl _) (.andI source.andE₂.andE₁ (QuadraticTowerSignRecipe.negated_height (succ h) _ (sourceCap h b) source.andE₂.andE₂))
  exact .andI (negative_product_flag h B D A b p hp)
    (QuadraticTowerConeTest.source_certificate h (sourceCap h b) D (negativeProduct h B D A) (sourceCap h b)
      negSource (negative_product_flag h B D A b p hp))

/-- Actual sign zero is preserved by this computed multiplier. This is
not an assertion that the raw returned array is literally zeroArray. -/
theorem zero_product_sign (h B D A b : PTm n) (p : Γ ⊢[PRAAx] QuadraticTowerOppositeMultiplier.input h B D A b)
    (hz : Γ ⊢[PRAAx] QuadraticTowerSignTable.query (succ h) B D A ≐ zero) : Γ ⊢[PRAAx] productSign h B D A b ≐ zero :=
  (returned_product_sign h B D A b p).eqTrans hz

/-! Actual numerical certificate observations: original parent tag,
returned-product tag, its two oriented cone flags and the derived cap. -/
def output (h B D A b : PTm n) : PTm n := pairT (QuadraticTowerSignTable.query (succ h) B D A)
  (pairT (productSign h B D A b)
    (pairT (QuadraticTowerConeTest.flag h (sourceCap h b) D (returnedProduct h B D A))
      (pairT (QuadraticTowerConeTest.flag h (sourceCap h b) D (negativeProduct h B D A)) (sourceCap h b))))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (h B D A b : PTm n) : PTm n := PTm.app outputF ![h,B,D,A,b]
ipra_subst output
ipra_subst run

theorem program_at (h B D A b : PTm n) : Γ ⊢[PRAAx] run h B D A b ≐ output h B D A b := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![h,B,D,A,b]
theorem returned_original_tag (h B D A b : PTm n) : Γ ⊢[PRAAx] fstT (run h B D A b) ≐ QuadraticTowerSignTable.query (succ h) B D A :=
  (program_at _ _ _ _ _).fstE
theorem returned_product_tail (h B D A b : PTm n) : Γ ⊢[PRAAx] sndT (run h B D A b) ≐
    pairT (productSign h B D A b)
      (pairT (QuadraticTowerConeTest.flag h (sourceCap h b) D (returnedProduct h B D A))
        (pairT (QuadraticTowerConeTest.flag h (sourceCap h b) D (negativeProduct h B D A)) (sourceCap h b))) :=
  (program_at _ _ _ _ _).sndE
theorem returned_product_tag (h B D A b : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run h B D A b)) ≐ productSign h B D A b :=
  (returned_product_tail _ _ _ _ _).fstE
theorem returned_flags (h B D A b : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run h B D A b)) ≐
    pairT (QuadraticTowerConeTest.flag h (sourceCap h b) D (returnedProduct h B D A))
      (pairT (QuadraticTowerConeTest.flag h (sourceCap h b) D (negativeProduct h B D A)) (sourceCap h b)) :=
  (returned_product_tail _ _ _ _ _).sndE
theorem returned_positive_flag (h B D A b : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run h B D A b))) ≐
    QuadraticTowerConeTest.flag h (sourceCap h b) D (returnedProduct h B D A) :=
  (returned_flags _ _ _ _ _).fstE
theorem returned_negative_pair (h B D A b : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run h B D A b))) ≐
    pairT (QuadraticTowerConeTest.flag h (sourceCap h b) D (negativeProduct h B D A)) (sourceCap h b) :=
  (returned_flags _ _ _ _ _).sndE
theorem returned_negative_flag (h B D A b : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run h B D A b)))) ≐
    QuadraticTowerConeTest.flag h (sourceCap h b) D (negativeProduct h B D A) :=
  (returned_negative_pair _ _ _ _ _).fstE
theorem returned_cap (h B D A b : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (run h B D A b)))) ≐ sourceCap h b :=
  (returned_negative_pair _ _ _ _ _).sndE

theorem returned_tags_equal (h B D A b : PTm n) (p : Γ ⊢[PRAAx] QuadraticTowerOppositeMultiplier.input h B D A b) : Γ ⊢[PRAAx]
    fstT (sndT (run h B D A b)) ≐ fstT (run h B D A b) :=
  (returned_product_tag h B D A b).eqTrans ((returned_product_sign h B D A b p).eqTrans (returned_original_tag h B D A b).eqSymm)
theorem returned_positive_success (h B D A b : PTm n) (p : Γ ⊢[PRAAx] QuadraticTowerOppositeMultiplier.input h B D A b)
    (hp : Γ ⊢[PRAAx] fstT (run h B D A b) ≐ one) : Γ ⊢[PRAAx] fstT (sndT (sndT (run h B D A b))) ≐ one :=
  (returned_positive_flag h B D A b).eqTrans (positive_product_flag h B D A b p ((returned_original_tag h B D A b).eqSymm.eqTrans hp))
theorem returned_negative_success (h B D A b : PTm n) (p : Γ ⊢[PRAAx] QuadraticTowerOppositeMultiplier.input h B D A b)
    (hp : Γ ⊢[PRAAx] fstT (run h B D A b) ≐ two) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run h B D A b)))) ≐ one :=
  (returned_negative_flag h B D A b).eqTrans (negative_product_flag h B D A b p ((returned_original_tag h B D A b).eqSymm.eqTrans hp))

theorem actual_original_norm_normalization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (norm (var 0) (var 1) (var 2) (normalized (succ (var 0)) (var 3)) ≐ norm (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (norm_normalized _ _ _ _)
theorem original_opposite_selected_norm_sign_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (QuadraticTowerOppositeMultiplier.input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      QuadraticTowerSignTable.query (var 0) (budget (var 0) (var 1) (var 2)) (var 2) (signedNorm (var 0) (var 1) (var 2) (var 3)) ≐
        QuadraticTowerSignTable.query (succ (var 0)) (var 1) (var 2) (var 3)) :=
  closeUniv 5 (.impI (signed_norm_sign _ _ _ _ (var 4) Prf.hyp0))
theorem original_returned_product_parent_sign_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (QuadraticTowerOppositeMultiplier.input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      productSign (var 0) (var 1) (var 2) (var 3) (var 4) ≐ QuadraticTowerSignTable.query (succ (var 0)) (var 1) (var 2) (var 3)) :=
  closeUniv 5 (.impI (returned_product_sign _ _ _ _ (var 4) Prf.hyp0))
theorem original_positive_opposite_product_certificate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (QuadraticTowerOppositeMultiplier.input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      QuadraticTowerSignTable.query (succ (var 0)) (var 1) (var 2) (var 3) ≐ one ⟶
        (QuadraticTowerConeTest.flag (var 0) (sourceCap (var 0) (var 4)) (var 2) (returnedProduct (var 0) (var 1) (var 2) (var 3)) ≐ one) ⋏
          ((productSign (var 0) (var 1) (var 2) (var 3) (var 4) ≐ one) ⋏
            QuadraticTowerConeTest.addresses (var 0) (sourceCap (var 0) (var 4)) (var 2) (returnedProduct (var 0) (var 1) (var 2) (var 3)))) :=
  closeUniv 5 (.impI (.impI (positive_product_certificate _ _ _ _ (var 4) Prf.hyp1 Prf.hyp0)))
theorem original_negative_opposite_product_certificate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (QuadraticTowerOppositeMultiplier.input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      QuadraticTowerSignTable.query (succ (var 0)) (var 1) (var 2) (var 3) ≐ two ⟶
        (QuadraticTowerConeTest.flag (var 0) (sourceCap (var 0) (var 4)) (var 2) (negativeProduct (var 0) (var 1) (var 2) (var 3)) ≐ one) ⋏
          ((QuadraticTowerSignTable.query (succ (var 0)) (sourceCap (var 0) (var 4)) (var 2) (negativeProduct (var 0) (var 1) (var 2) (var 3)) ≐ one) ⋏
            QuadraticTowerConeTest.addresses (var 0) (sourceCap (var 0) (var 4)) (var 2) (negativeProduct (var 0) (var 1) (var 2) (var 3)))) :=
  closeUniv 5 (.impI (.impI (negative_product_certificate _ _ _ _ (var 4) Prf.hyp1 Prf.hyp0)))
theorem original_zero_opposite_product_sign_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (QuadraticTowerOppositeMultiplier.input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      QuadraticTowerSignTable.query (succ (var 0)) (var 1) (var 2) (var 3) ≐ zero ⟶ productSign (var 0) (var 1) (var 2) (var 3) (var 4) ≐ zero) :=
  closeUniv 5 (.impI (.impI (zero_product_sign _ _ _ _ (var 4) Prf.hyp1 Prf.hyp0)))
theorem actual_opposite_sign_certificate_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) := closeUniv 5 (program_at _ _ _ _ _)
theorem actual_opposite_sign_certificate_returned_cap_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))) ≐ sourceCap (var 0) (var 4)) := closeUniv 5 (returned_cap _ _ _ _ _)
theorem original_opposite_sign_certificate_returned_tags_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (QuadraticTowerOppositeMultiplier.input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))) ≐ fstT (run (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (returned_tags_equal _ _ _ _ (var 4) Prf.hyp0))
theorem original_returned_positive_cone_flag_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (QuadraticTowerOppositeMultiplier.input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      fstT (run (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ one ⟶ fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))) ≐ one) :=
  closeUniv 5 (.impI (.impI (returned_positive_success _ _ _ _ (var 4) Prf.hyp1 Prf.hyp0)))
theorem original_returned_negative_cone_flag_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (QuadraticTowerOppositeMultiplier.input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      fstT (run (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ two ⟶ fstT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))) ≐ one) :=
  closeUniv 5 (.impI (.impI (returned_negative_success _ _ _ _ (var 4) Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Algebra.QuadraticTowerOppositeSignCertificate
