import IPRADerivations.Algebra.QuadraticTowerConeTest
import IPRADerivations.Algebra.QuadraticTowerOppositeMultiplier

/-!
# The actual sign of a lower array inserted into the next extension

The actual normalized lower array and literal zero upper half give the
SAME lower query sign at the true compiled child budget. The actual
opposite-sign multiplier's returned product is specialized to its
returned signed norm using derived height and true budget coherence.
No lower ordered-domain provider or semantic zero ideal is assumed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.QuadraticTowerExtensionSign

open_ipra
open QuadraticTowerArrayCodec (arrayHeight normalized)
open QuadraticTowerCoefficients (width)
open QuadraticTowerScalarArrays (zeroArray)
open QuadraticTowerMultiplicationTable (budget)
open QuadraticTowerMultiplicationHeight (radicandsHeight)
open QuadraticTowerScalarBudget (growth)
open QuadraticTowerOppositeMultiplier (signedNorm)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (append)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def inserted (h L : PTm n) : PTm n := append (normalized h L) (zeroArray h)
ipra_subst inserted

theorem inserted_height (h L B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (ha : Γ ⊢[PRAAx] arrayHeight h L B) : Γ ⊢[PRAAx] arrayHeight (succ h) (inserted h L) B :=
  QuadraticTowerMultiplicationHeight.append_height h _ _ B
    (QuadraticTowerMultiplicationZero.normalized_height h L B ha) (QuadraticTowerScalarArrays.zero_array_height h B hB)
    (QuadraticTowerArrayCodec.normalized_length h L) (QuadraticTowerScalarArrays.zero_length h)

theorem first_tag (h B D L : PTm n) : Γ ⊢[PRAAx]
    QuadraticTowerSignRecipe.firstTag h B D (QuadraticTowerSignTable.table h (budget h B D) D)
      (normalized (succ h) (inserted h L)) ≐ QuadraticTowerSignTable.query h (budget h B D) D L :=
  (QuadraticTowerConeTest.first_normalized h B D (inserted h L)).eqTrans
    ((QuadraticTowerSignCoherence.read_values_proper h (budget h B D)
      (QuadraticTowerSignTable.table h (budget h B D) D) _ _
      (QuadraticTowerMultiplicationRecurrence.left_join_values h _ _ (QuadraticTowerArrayCodec.normalized_length h L))).eqTrans
        (QuadraticTowerSignCoherence.read_values_proper h (budget h B D)
          (QuadraticTowerSignTable.table h (budget h B D) D) _ L (QuadraticTowerOperandProperness.normalized_values h L)))

theorem second_tag (h B D L : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    QuadraticTowerSignRecipe.secondTag h B D (QuadraticTowerSignTable.table h (budget h B D) D)
      (normalized (succ h) (inserted h L)) ≐ zero :=
  (QuadraticTowerConeTest.second_normalized h B D (inserted h L)).eqTrans
    ((QuadraticTowerSignCoherence.read_values_proper h (budget h B D)
      (QuadraticTowerSignTable.table h (budget h B D) D) _ _
      (QuadraticTowerMultiplicationRecurrence.right_join_values h _ _ (QuadraticTowerArrayCodec.normalized_length h L)
        (QuadraticTowerScalarArrays.zero_length h))).eqTrans
          (QuadraticTowerSignEmbedding.zero_query h (budget h B D) D
            (le_trans hB (QuadraticTowerSignEmbedding.budget_inflation h B D))))

/-- The actual conditional third query is irrelevant when the inserted
upper coefficient is zero. No radicand positivity or sign rule is assumed. -/
theorem query_inserted (h B D L : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (ha : Γ ⊢[PRAAx] arrayHeight h L B) : Γ ⊢[PRAAx]
    QuadraticTowerSignTable.query (succ h) B D (inserted h L) ≐ QuadraticTowerSignTable.query h (budget h B D) D L :=
  (QuadraticTowerSignTable.query_succ h B D (inserted h L) (inserted_height h L B hB ha)).eqTrans
    ((QuadraticTowerSignEmbedding.dispatch_b_zero_total _ _ _ (second_tag h B D L hB)).eqTrans (first_tag h B D L))

def sourceCap (h b : PTm n) : PTm n := growth (QuadraticTowerGrowth.path (succ h)) b
ipra_subst sourceCap

/-- Every selected signed norm is an actual constructed normalized array,
even away from the opposite-sign input predicate. -/
theorem signedNorm_fixed (h B D A : PTm n) : Γ ⊢[PRAAx] normalized h (signedNorm h B D A) ≐ signedNorm h B D A := by
  have selected : Γ ⊢[PRAAx] (signedNorm h B D A ≐ QuadraticTowerSignRecipe.norm h B D A) ⋎
      (signedNorm h B D A ≐ QuadraticTowerCoefficientArithmetic.negated h (QuadraticTowerSignRecipe.norm h B D A)) :=
    Foundations.GuardedTotalization.sel_cases (Foundations.BoundedReflection.eqb_cases _ _)
  refine .orE selected ?_ ?_
  · exact (QuadraticTowerAdditionLaws.normalized_congr h Prf.hyp0).eqTrans
      ((QuadraticTowerArrayNormalization.normalized_added h _ _).eqTrans Prf.hyp0.eqSymm)
  · exact (QuadraticTowerAdditionLaws.normalized_congr h Prf.hyp0).eqTrans
      ((QuadraticTowerArrayNormalization.normalized_negated h _).eqTrans Prf.hyp0.eqSymm)

theorem inserted_signedNorm (h B D A : PTm n) : Γ ⊢[PRAAx]
    inserted h (signedNorm h B D A) ≐ append (signedNorm h B D A) (zeroArray h) :=
  QuadraticTowerCoefficients.append_congr (signedNorm_fixed h B D A) (.eqRefl _)

theorem sourceCap_positive (h B D A b : PTm n)
    (p : Γ ⊢[PRAAx] QuadraticTowerConeTest.source h B D A b) : Γ ⊢[PRAAx] le one (sourceCap h b) :=
  le_trans (QuadraticTowerMultiplicationUnit.array_height_floor (succ h) A b p.andE₂.andE₂)
    (QuadraticTowerGrowth.growth_inflation _ _)

/-- The ORIGINAL computed norm height supplies the bound; it is not an
assumed height of the selected output. -/
theorem signedNorm_height (h B D A b : PTm n)
    (p : Γ ⊢[PRAAx] QuadraticTowerConeTest.source h B D A b) : Γ ⊢[PRAAx]
    arrayHeight h (signedNorm h B D A) (sourceCap h b) := by
  have norm := QuadraticTowerSignRecipe.norm_height h B D A b p.andE₁ p.andE₂.andE₁ p.andE₂.andE₂
  have selected : Γ ⊢[PRAAx] (signedNorm h B D A ≐ QuadraticTowerSignRecipe.norm h B D A) ⋎
      (signedNorm h B D A ≐ QuadraticTowerCoefficientArithmetic.negated h (QuadraticTowerSignRecipe.norm h B D A)) :=
    Foundations.GuardedTotalization.sel_cases (Foundations.BoundedReflection.eqb_cases _ _)
  refine .orE selected ?_ ?_
  · exact QuadraticTowerMultiplicationHeight.array_congr (.eqRefl h) Prf.hyp0.eqSymm (.eqRefl _) norm.wk
  · exact QuadraticTowerMultiplicationHeight.array_congr (.eqRefl h) Prf.hyp0.eqSymm (.eqRefl _)
      (QuadraticTowerSignRecipe.negated_height h _ (sourceCap h b) norm.wk)

theorem original_child_cap (h B D A b : PTm n)
    (p : Γ ⊢[PRAAx] QuadraticTowerConeTest.source h B D A b) : Γ ⊢[PRAAx] le (sourceCap h b) (budget h B D) :=
  QuadraticTowerGrowth.path_growth_budget h B D b p.andE₁

/-- The SAME original product, at the explicitly computed sufficient cap,
has the sign of the SAME signed norm at its ORIGINAL child budget. -/
theorem product_sign (h B D A b : PTm n) (p : Γ ⊢[PRAAx] QuadraticTowerOppositeMultiplier.input h B D A b) : Γ ⊢[PRAAx]
    QuadraticTowerSignTable.query (succ h) (sourceCap h b) D
      (QuadraticTowerMultiplicationTable.query (succ h) B D (QuadraticTowerOppositeMultiplier.multiplier h B D A) A) ≐
    QuadraticTowerSignTable.query h (budget h B D) D (signedNorm h B D A) := by
  let T := sourceCap h b
  have e := (QuadraticTowerOppositeMultiplier.original_certificate h B D A b p).andE₂.andE₂.eqTrans
    (inserted_signedNorm h B D A).eqSymm
  have insertedSign := query_inserted h T D (signedNorm h B D A) (sourceCap_positive h B D A b p.andE₁)
    (signedNorm_height h B D A b p.andE₁)
  have lower := QuadraticTowerMultiplicationHeight.radicands_mono D h b T
    (QuadraticTowerMultiplicationHeight.radicands_prefix D h (succ h) b p.andE₁.andE₂.andE₁ (le_succ_self h))
    (QuadraticTowerGrowth.growth_inflation _ _)
  have transport := QuadraticTowerSignCoherence.query_cap_independent h (budget h T D) (budget h B D) D
    (signedNorm h B D A) T (QuadraticTowerSignEmbedding.budget_inflation h T D) (original_child_cap h B D A b p.andE₁)
    lower (signedNorm_height h B D A b p.andE₁)
  exact (QuadraticTowerSignRecipe.read_operand_congr (succ h) T (QuadraticTowerSignTable.table (succ h) T D) _ _ e).eqTrans
    (insertedSign.eqTrans transport)

def returnedNorm (h B D A : PTm n) : PTm n := fstT (sndT (sndT (sndT (sndT (QuadraticTowerOppositeMultiplier.run h B D A)))))
def returnedProduct (h B D A : PTm n) : PTm n := fstT (sndT (sndT (sndT (QuadraticTowerOppositeMultiplier.run h B D A))))
def productSign (h B D A b : PTm n) : PTm n := QuadraticTowerSignTable.query (succ h) (sourceCap h b) D (returnedProduct h B D A)
def normSign (h B D A : PTm n) : PTm n := QuadraticTowerSignTable.query h (budget h B D) D (returnedNorm h B D A)
ipra_subst returnedNorm
ipra_subst returnedProduct
ipra_subst productSign
ipra_subst normSign

theorem returned_norm_height (h B D A b : PTm n)
    (p : Γ ⊢[PRAAx] QuadraticTowerConeTest.source h B D A b) : Γ ⊢[PRAAx]
    arrayHeight h (returnedNorm h B D A) (sourceCap h b) :=
  QuadraticTowerMultiplicationHeight.array_congr (.eqRefl h) (QuadraticTowerOppositeMultiplier.returned_norm h B D A).eqSymm
    (.eqRefl _) (signedNorm_height h B D A b p)

theorem returned_norm_address (h B D A b : PTm n)
    (p : Γ ⊢[PRAAx] QuadraticTowerConeTest.source h B D A b) : Γ ⊢[PRAAx]
    lt (QuadraticTowerArrayCodec.code h (returnedNorm h B D A) (budget h B D)) (QuadraticTowerArrayCodec.horizon h (budget h B D)) :=
  QuadraticTowerArrayCodec.code_bound h _ (budget h B D)
    (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ (returned_norm_height h B D A b p) (original_child_cap h B D A b p))

theorem returned_product_sign (h B D A b : PTm n) (p : Γ ⊢[PRAAx] QuadraticTowerOppositeMultiplier.input h B D A b) : Γ ⊢[PRAAx]
    productSign h B D A b ≐ normSign h B D A :=
  (QuadraticTowerSignRecipe.read_operand_congr (succ h) (sourceCap h b)
    (QuadraticTowerSignTable.table (succ h) (sourceCap h b) D) _ _ (QuadraticTowerOppositeMultiplier.returned_product h B D A)).eqTrans
      ((product_sign h B D A b p).eqTrans
        (QuadraticTowerSignRecipe.read_operand_congr h (budget h B D) (QuadraticTowerSignTable.table h (budget h B D) D)
          _ _ (QuadraticTowerOppositeMultiplier.returned_norm h B D A).eqSymm))

def output (h B D A b : PTm n) : PTm n := pairT (inserted h (returnedNorm h B D A))
  (pairT (productSign h B D A b) (pairT (normSign h B D A) (sourceCap h b)))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (h B D A b : PTm n) : PTm n := PTm.app outputF ![h,B,D,A,b]
ipra_subst output
ipra_subst run

theorem program_at (h B D A b : PTm n) : Γ ⊢[PRAAx] run h B D A b ≐ output h B D A b := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![h,B,D,A,b]
theorem returned_inserted (h B D A b : PTm n) : Γ ⊢[PRAAx]
    fstT (run h B D A b) ≐ inserted h (returnedNorm h B D A) :=
  (program_at _ _ _ _ _).fstE
theorem returned_sign_pair (h B D A b : PTm n) : Γ ⊢[PRAAx] sndT (run h B D A b) ≐
    pairT (productSign h B D A b) (pairT (normSign h B D A) (sourceCap h b)) :=
  (program_at _ _ _ _ _).sndE
theorem returned_product_tag (h B D A b : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run h B D A b)) ≐ productSign h B D A b :=
  (returned_sign_pair _ _ _ _ _).fstE
theorem returned_norm_pair (h B D A b : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run h B D A b)) ≐ pairT (normSign h B D A) (sourceCap h b) :=
  (returned_sign_pair _ _ _ _ _).sndE
theorem returned_norm_tag (h B D A b : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run h B D A b))) ≐ normSign h B D A :=
  (returned_norm_pair _ _ _ _ _).fstE
theorem returned_cap (h B D A b : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run h B D A b))) ≐ sourceCap h b :=
  (returned_norm_pair _ _ _ _ _).sndE
theorem returned_equal (h B D A b : PTm n) (p : Γ ⊢[PRAAx] QuadraticTowerOppositeMultiplier.input h B D A b) : Γ ⊢[PRAAx]
    fstT (sndT (run h B D A b)) ≐ fstT (sndT (sndT (run h B D A b))) :=
  (returned_product_tag h B D A b).eqTrans ((returned_product_sign h B D A b p).eqTrans (returned_norm_tag h B D A b).eqSymm)

theorem original_lower_array_insertion_sign_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ arrayHeight (var 0) (var 3) (var 1) ⟶
      QuadraticTowerSignTable.query (succ (var 0)) (var 1) (var 2) (inserted (var 0) (var 3)) ≐
        QuadraticTowerSignTable.query (var 0) (budget (var 0) (var 1) (var 2)) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (query_inserted _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_signed_norm_insertion_normalized_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (normalized (var 0) (signedNorm (var 0) (var 1) (var 2) (var 3)) ≐ signedNorm (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (signedNorm_fixed _ _ _ _)
theorem original_signed_norm_derived_height_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (QuadraticTowerConeTest.source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      arrayHeight (var 0) (returnedNorm (var 0) (var 1) (var 2) (var 3)) (sourceCap (var 0) (var 4))) :=
  closeUniv 5 (.impI (returned_norm_height _ _ _ _ (var 4) Prf.hyp0))
theorem original_signed_norm_actual_address_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (QuadraticTowerConeTest.source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      lt (QuadraticTowerArrayCodec.code (var 0) (returnedNorm (var 0) (var 1) (var 2) (var 3)) (budget (var 0) (var 1) (var 2)))
        (QuadraticTowerArrayCodec.horizon (var 0) (budget (var 0) (var 1) (var 2)))) :=
  closeUniv 5 (.impI (returned_norm_address _ _ _ _ (var 4) Prf.hyp0))
theorem original_returned_product_signed_norm_sign_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (QuadraticTowerOppositeMultiplier.input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      productSign (var 0) (var 1) (var 2) (var 3) (var 4) ≐ normSign (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 5 (.impI (returned_product_sign _ _ _ _ (var 4) Prf.hyp0))
theorem actual_extension_insertion_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) := closeUniv 5 (program_at _ _ _ _ _)
theorem actual_extension_insertion_returned_cap_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))) ≐ sourceCap (var 0) (var 4)) := closeUniv 5 (returned_cap _ _ _ _ _)
theorem original_extension_insertion_returned_tags_equal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (QuadraticTowerOppositeMultiplier.input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))) ≐ fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))) :=
  closeUniv 5 (.impI (returned_equal _ _ _ _ (var 4) Prf.hyp0))

end LeanProofs.IPRA.Algebra.QuadraticTowerExtensionSign
