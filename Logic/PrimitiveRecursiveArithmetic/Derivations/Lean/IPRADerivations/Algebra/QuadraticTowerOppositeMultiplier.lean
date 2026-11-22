import IPRADerivations.Algebra.QuadraticTowerComparisonSymmetry
import IPRADerivations.Algebra.QuadraticTowerConeTest

/-!
# Actual opposite-sign tower multipliers

The original coefficientwise conjugate multipliers are fixed-width
constructed arrays. Their SAME numerical multiplication query equals
the original sign recipe's actual norm, with a literal zero second half.
Only the original height and radicand-height bounds are used. The later
cone certificate concerns the actual lower sign tags; general cone
closure and mathematical sign correctness remain separate.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.QuadraticTowerOppositeMultiplier

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open QuadraticTowerCoefficients (width)
open QuadraticTowerArrayCodec (arrayHeight normalized)
open QuadraticTowerCoefficientArithmetic (added negated added_congr negated_congr)
open QuadraticTowerMultiplicationTable (query budget leftHalf rightHalf)
open QuadraticTowerMultiplicationHeight (radicandsHeight)
open QuadraticTowerScalarBudget (amp growth)
open QuadraticTowerScalarArrays (zeroArray)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (append length)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel sel_one sel_zero)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def wPlus (h A : PTm n) : PTm n := append (normalized h (leftHalf h A)) (negated h (rightHalf h A))
def wMinus (h A : PTm n) : PTm n := append (negated h (leftHalf h A)) (normalized h (rightHalf h A))
@[simp] theorem subst_wPlus {k : ℕ} (σ : Fin n → PTm k) (h A : PTm n) :
    Syn.subst σ (wPlus h A) = wPlus (Syn.subst σ h) (Syn.subst σ A) := by simp [wPlus]
@[simp] theorem subst_wMinus {k : ℕ} (σ : Fin n → PTm k) (h A : PTm n) :
    Syn.subst σ (wMinus h A) = wMinus (Syn.subst σ h) (Syn.subst σ A) := by simp [wMinus]

/-- Original joined coefficients enter the actual five-call recipe by
bounded field-value properness, without an arbitrary raw-code eta. -/
theorem joined_query (h B D L R A : PTm n)
    (hl : Γ ⊢[PRAAx] length L ≐ width h) (hr : Γ ⊢[PRAAx] length R ≐ width h)
    (hw : Γ ⊢[PRAAx] arrayHeight (succ h) (append L R) B)
    (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A B) : Γ ⊢[PRAAx]
    query (succ h) B D (append L R) A ≐ append
      (added h (query h (budget h B D) D L (leftHalf h A))
        (query h (budget h B D) D (query h (budget h B D) D R (rightHalf h A)) (entry D h)))
      (added h (query h (budget h B D) D L (rightHalf h A))
        (query h (budget h B D) D R (leftHalf h A))) := by
  let K := budget h B D
  have l := QuadraticTowerMultiplicationRecurrence.left_join_values h L R hl
  have r := QuadraticTowerMultiplicationRecurrence.right_join_values h L R hl hr
  have ac := QuadraticTowerOperandProperness.query_operands_proper h K D _ L _ (leftHalf h A) l
    (QuadraticTowerMultiplicationZero.values_refl h _)
  have be := QuadraticTowerOperandProperness.query_operands_proper h K D _ R _ (rightHalf h A) r
    (QuadraticTowerMultiplicationZero.values_refl h _)
  have bed := QuadraticTowerMultiplicationNegative.query_operands_congr h K D be (.eqRefl (entry D h))
  have ae := QuadraticTowerOperandProperness.query_operands_proper h K D _ L _ (rightHalf h A) l
    (QuadraticTowerMultiplicationZero.values_refl h _)
  have bc := QuadraticTowerOperandProperness.query_operands_proper h K D _ R _ (leftHalf h A) r
    (QuadraticTowerMultiplicationZero.values_refl h _)
  exact (QuadraticTowerMultiplicationRecurrence.query_succ_original h B D (append L R) A hw ha).eqTrans
    ((QuadraticTowerMultiplicationRecurrence.recipe_components _ _ _ _ _ _).eqTrans
      (QuadraticTowerCoefficients.append_congr (added_congr (.eqRefl h) ac bed) (added_congr (.eqRefl h) ae bc)))

theorem wPlus_height (h A b : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b) : Γ ⊢[PRAAx]
    arrayHeight (succ h) (wPlus h A) b :=
  QuadraticTowerMultiplicationHeight.append_height h _ _ b
    (QuadraticTowerMultiplicationZero.normalized_height h _ b (QuadraticTowerMultiplicationHeight.left_height h A b ha))
    (QuadraticTowerSignRecipe.negated_height h _ b (QuadraticTowerMultiplicationHeight.right_height h A b ha))
    (QuadraticTowerArrayCodec.normalized_length _ _) (QuadraticTowerCoefficientArithmetic.negated_length _ _)

theorem wMinus_height (h A b : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b) : Γ ⊢[PRAAx]
    arrayHeight (succ h) (wMinus h A) b :=
  QuadraticTowerMultiplicationHeight.append_height h _ _ b
    (QuadraticTowerSignRecipe.negated_height h _ b (QuadraticTowerMultiplicationHeight.left_height h A b ha))
    (QuadraticTowerMultiplicationZero.normalized_height h _ b (QuadraticTowerMultiplicationHeight.right_height h A b ha))
    (QuadraticTowerCoefficientArithmetic.negated_length _ _) (QuadraticTowerArrayCodec.normalized_length _ _)

/-- Both source multipliers use the SAME original norm and actual query.
No nonzero or sign correctness premise is used in these ring identities. -/
theorem products (h B D A b : PTm n) (hb : Γ ⊢[PRAAx] le b B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b) (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b) : Γ ⊢[PRAAx]
    (query (succ h) B D (wPlus h A) A ≐ append (QuadraticTowerSignRecipe.norm h B D A) (zeroArray h)) ⋏
    (query (succ h) B D (wMinus h A) A ≐ append (negated h (QuadraticTowerSignRecipe.norm h B D A)) (zeroArray h)) := by
  let K := budget h B D
  let a := leftHalf h A
  let c := rightHalf h A
  let g := growth (QuadraticTowerGrowth.path h) b
  let aa := query h K D a a
  let cc := query h K D c c
  let dc := query h K D (entry D h) cc
  let ac := query h K D a c
  have bg : Γ ⊢[PRAAx] le b g := QuadraticTowerGrowth.growth_inflation _ _
  have gAmp : Γ ⊢[PRAAx] le (amp g) K := QuadraticTowerMultiplicationDistributivity.lower_sum_budget h B D b hb
  have bAmp := le_trans (QuadraticTowerGrowth.amp_mono bg) gAmp
  have gK := le_trans (QuadraticTowerGrowth.amp_inflation g) gAmp
  have bK := le_trans bg gK
  have lower := QuadraticTowerMultiplicationHeight.radicands_prefix D h (succ h) b hD (le_succ_self h)
  have ah := QuadraticTowerMultiplicationHeight.left_height h A b ha
  have ch := QuadraticTowerMultiplicationHeight.right_height h A b ha
  have ccH : Γ ⊢[PRAAx] arrayHeight h cc g := QuadraticTowerMultiplicationHeight.query_height h K D c c b bK lower ch ch
  have dH := QuadraticTowerMultiplicationHeight.array_mono h (entry D h) b g
    (QuadraticTowerMultiplicationHeight.radicand_at D (succ h) b h hD (le_refl (succ h))) bg
  have lowerG := QuadraticTowerMultiplicationHeight.radicands_mono D h b g lower bg
  have commDC : Γ ⊢[PRAAx] query h K D cc (entry D h) ≐ dc :=
    QuadraticTowerMultiplicationCommutativity.query_commutative h K D cc (entry D h) g gK lowerG ccH dH
  have commAC : Γ ⊢[PRAAx] query h K D c a ≐ ac :=
    QuadraticTowerMultiplicationCommutativity.query_commutative h K D c a b bK lower ch ah
  have normAA : Γ ⊢[PRAAx] query h K D (normalized h a) a ≐ aa :=
    QuadraticTowerOperandProperness.query_operands_proper h K D _ a a a
      (QuadraticTowerOperandProperness.normalized_values h a) (QuadraticTowerMultiplicationZero.values_refl h a)
  have normAC : Γ ⊢[PRAAx] query h K D (normalized h a) c ≐ ac :=
    QuadraticTowerOperandProperness.query_operands_proper h K D _ a c c
      (QuadraticTowerOperandProperness.normalized_values h a) (QuadraticTowerMultiplicationZero.values_refl h c)
  have negCC := QuadraticTowerMultiplicationNegative.query_left_negative h K D c c b bAmp lower ch ch
  have negCA : Γ ⊢[PRAAx] query h K D (negated h c) a ≐ negated h ac :=
    (QuadraticTowerMultiplicationNegative.query_left_negative h K D c a b bAmp lower ch ah).eqTrans
      (negated_congr (.eqRefl h) commAC)
  have negCCd : Γ ⊢[PRAAx] query h K D (query h K D (negated h c) c) (entry D h) ≐ negated h dc :=
    (QuadraticTowerMultiplicationNegative.query_operands_congr h K D negCC (.eqRefl _)).eqTrans
      ((QuadraticTowerMultiplicationNegative.query_left_negative h K D cc (entry D h) g gAmp lowerG ccH dH).eqTrans
        (negated_congr (.eqRefl h) commDC))
  have plus : Γ ⊢[PRAAx] query (succ h) B D (wPlus h A) A ≐ append (QuadraticTowerSignRecipe.norm h B D A) (zeroArray h) :=
    (joined_query h B D _ _ A (QuadraticTowerArrayCodec.normalized_length _ _) (QuadraticTowerCoefficientArithmetic.negated_length _ _)
      (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ (wPlus_height h A b ha) hb)
      (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ ha hb)).eqTrans
        (QuadraticTowerCoefficients.append_congr (added_congr (.eqRefl h) normAA negCCd)
          ((added_congr (.eqRefl h) normAC negCA).eqTrans (QuadraticTowerDifferenceIdentities.difference_self h ac)))
  have negAA := QuadraticTowerMultiplicationNegative.query_left_negative h K D a a b bAmp lower ah ah
  have normCC : Γ ⊢[PRAAx] query h K D (normalized h c) c ≐ cc :=
    QuadraticTowerOperandProperness.query_operands_proper h K D _ c c c
      (QuadraticTowerOperandProperness.normalized_values h c) (QuadraticTowerMultiplicationZero.values_refl h c)
  have normCAd : Γ ⊢[PRAAx] query h K D (query h K D (normalized h c) c) (entry D h) ≐ dc :=
    (QuadraticTowerMultiplicationNegative.query_operands_congr h K D normCC (.eqRefl _)).eqTrans commDC
  have negAC := QuadraticTowerMultiplicationNegative.query_left_negative h K D a c b bAmp lower ah ch
  have normCA : Γ ⊢[PRAAx] query h K D (normalized h c) a ≐ ac :=
    (QuadraticTowerOperandProperness.query_operands_proper h K D _ c a a
      (QuadraticTowerOperandProperness.normalized_values h c) (QuadraticTowerMultiplicationZero.values_refl h a)).eqTrans commAC
  have minus : Γ ⊢[PRAAx] query (succ h) B D (wMinus h A) A ≐ append (negated h (QuadraticTowerSignRecipe.norm h B D A)) (zeroArray h) :=
    (joined_query h B D _ _ A (QuadraticTowerCoefficientArithmetic.negated_length _ _) (QuadraticTowerArrayCodec.normalized_length _ _)
      (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ (wMinus_height h A b ha) hb)
      (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ ha hb)).eqTrans
        (QuadraticTowerCoefficients.append_congr
          ((added_congr (.eqRefl h) negAA normCAd).eqTrans
            ((QuadraticTowerMultiplicationCommutativity.added_commutative h _ _).eqTrans
              (QuadraticTowerComparisonSymmetry.difference_swapped h aa dc)))
          ((added_congr (.eqRefl h) negAC normCA).eqTrans
            ((QuadraticTowerMultiplicationCommutativity.added_commutative h _ _).eqTrans
              (QuadraticTowerDifferenceIdentities.difference_self h ac))))
  exact .andI plus minus

theorem wPlus_first (h B D A : PTm n) : Γ ⊢[PRAAx]
    QuadraticTowerConeTest.lowerFirst h B D (wPlus h A) ≐ QuadraticTowerConeTest.lowerFirst h B D A :=
  (QuadraticTowerSignCoherence.read_values_proper h (budget h B D)
    (QuadraticTowerSignTable.table h (budget h B D) D) _ _
    (QuadraticTowerMultiplicationRecurrence.left_join_values h _ _ (QuadraticTowerArrayCodec.normalized_length _ _))).eqTrans
      (QuadraticTowerSignCoherence.read_values_proper h (budget h B D)
        (QuadraticTowerSignTable.table h (budget h B D) D) _ _ (QuadraticTowerOperandProperness.normalized_values h _))

theorem wMinus_second (h B D A : PTm n) : Γ ⊢[PRAAx]
    QuadraticTowerConeTest.lowerSecond h B D (wMinus h A) ≐ QuadraticTowerConeTest.lowerSecond h B D A :=
  (QuadraticTowerSignCoherence.read_values_proper h (budget h B D)
    (QuadraticTowerSignTable.table h (budget h B D) D) _ _
    (QuadraticTowerMultiplicationRecurrence.right_join_values h _ _ (QuadraticTowerCoefficientArithmetic.negated_length _ _)
      (QuadraticTowerArrayCodec.normalized_length _ _))).eqTrans
      (QuadraticTowerSignCoherence.read_values_proper h (budget h B D)
        (QuadraticTowerSignTable.table h (budget h B D) D) _ _ (QuadraticTowerOperandProperness.normalized_values h _))

theorem wPlus_second (h B D A b : PTm n) (hb : Γ ⊢[PRAAx] le b B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b) (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b) : Γ ⊢[PRAAx]
    QuadraticTowerConeTest.lowerSecond h B D (wPlus h A) ≐
      QuadraticTowerSignNegation.opposite (QuadraticTowerConeTest.lowerSecond h B D A) :=
  (QuadraticTowerSignCoherence.read_values_proper h (budget h B D)
    (QuadraticTowerSignTable.table h (budget h B D) D) _ _
    (QuadraticTowerMultiplicationRecurrence.right_join_values h _ _ (QuadraticTowerArrayCodec.normalized_length _ _)
      (QuadraticTowerCoefficientArithmetic.negated_length _ _))).eqTrans
      (QuadraticTowerSignNegation.query_negative h (budget h B D) D (rightHalf h A) b
        (le_trans hb (QuadraticTowerSignEmbedding.budget_inflation h B D))
        (QuadraticTowerMultiplicationHeight.radicands_prefix D h (succ h) b hD (le_succ_self h))
        (QuadraticTowerMultiplicationHeight.right_height h A b ha))

theorem wMinus_first (h B D A b : PTm n) (hb : Γ ⊢[PRAAx] le b B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b) (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b) : Γ ⊢[PRAAx]
    QuadraticTowerConeTest.lowerFirst h B D (wMinus h A) ≐
      QuadraticTowerSignNegation.opposite (QuadraticTowerConeTest.lowerFirst h B D A) :=
  (QuadraticTowerSignCoherence.read_values_proper h (budget h B D)
    (QuadraticTowerSignTable.table h (budget h B D) D) _ _
    (QuadraticTowerMultiplicationRecurrence.left_join_values h _ _ (QuadraticTowerCoefficientArithmetic.negated_length _ _))).eqTrans
      (QuadraticTowerSignNegation.query_negative h (budget h B D) D (leftHalf h A) b
        (le_trans hb (QuadraticTowerSignEmbedding.budget_inflation h B D))
        (QuadraticTowerMultiplicationHeight.radicands_prefix D h (succ h) b hD (le_succ_self h))
        (QuadraticTowerMultiplicationHeight.left_height h A b ha))

theorem wPlus_flag (h B D A b : PTm n) (hb : Γ ⊢[PRAAx] le b B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b) (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b)
    (hs : Γ ⊢[PRAAx] QuadraticTowerConeTest.lowerFirst h B D A ≐ one)
    (ht : Γ ⊢[PRAAx] QuadraticTowerConeTest.lowerSecond h B D A ≐ two)
    (hd : Γ ⊢[PRAAx] QuadraticTowerConeTest.lowerRadicand h B D ≐ one) : Γ ⊢[PRAAx]
    QuadraticTowerConeTest.flag h B D (wPlus h A) ≐ one := by
  have first := (wPlus_first h B D A).eqTrans hs
  have second := (wPlus_second h B D A b hb hD ha).eqTrans
    ((QuadraticTowerSignNegation.opposite_congr ht).eqTrans QuadraticTowerSignNegation.opposite_two)
  exact .impE (QuadraticTowerConeTest.flag_reflection h B D (wPlus h A)).andE₂
    (.andI (.orI₂ first) (.andI (.orI₂ second) (.andI (.orI₁ first) hd)))

theorem wMinus_flag (h B D A b : PTm n) (hb : Γ ⊢[PRAAx] le b B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b) (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b)
    (hs : Γ ⊢[PRAAx] QuadraticTowerConeTest.lowerFirst h B D A ≐ two)
    (ht : Γ ⊢[PRAAx] QuadraticTowerConeTest.lowerSecond h B D A ≐ one)
    (hd : Γ ⊢[PRAAx] QuadraticTowerConeTest.lowerRadicand h B D ≐ one) : Γ ⊢[PRAAx]
    QuadraticTowerConeTest.flag h B D (wMinus h A) ≐ one := by
  have first := (wMinus_first h B D A b hb hD ha).eqTrans
    ((QuadraticTowerSignNegation.opposite_congr hs).eqTrans QuadraticTowerSignNegation.opposite_two)
  have second := (wMinus_second h B D A).eqTrans ht
  exact .impE (QuadraticTowerConeTest.flag_reflection h B D (wMinus h A)).andE₂
    (.andI (.orI₂ first) (.andI (.orI₂ second) (.andI (.orI₁ first) hd)))

theorem wPlus_positive (h B D A b : PTm n) (hb : Γ ⊢[PRAAx] le b B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b) (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b)
    (hs : Γ ⊢[PRAAx] QuadraticTowerConeTest.lowerFirst h B D A ≐ one)
    (ht : Γ ⊢[PRAAx] QuadraticTowerConeTest.lowerSecond h B D A ≐ two)
    (hd : Γ ⊢[PRAAx] QuadraticTowerConeTest.lowerRadicand h B D ≐ one) : Γ ⊢[PRAAx]
    QuadraticTowerSignTable.query (succ h) B D (wPlus h A) ≐ one :=
  QuadraticTowerConeTest.query_positive h B D _
    (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ (wPlus_height h A b ha) hb)
    (wPlus_flag h B D A b hb hD ha hs ht hd)

theorem wMinus_positive (h B D A b : PTm n) (hb : Γ ⊢[PRAAx] le b B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b) (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b)
    (hs : Γ ⊢[PRAAx] QuadraticTowerConeTest.lowerFirst h B D A ≐ two)
    (ht : Γ ⊢[PRAAx] QuadraticTowerConeTest.lowerSecond h B D A ≐ one)
    (hd : Γ ⊢[PRAAx] QuadraticTowerConeTest.lowerRadicand h B D ≐ one) : Γ ⊢[PRAAx]
    QuadraticTowerSignTable.query (succ h) B D (wMinus h A) ≐ one :=
  QuadraticTowerConeTest.query_positive h B D _
    (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ (wMinus_height h A b ha) hb)
    (wMinus_flag h B D A b hb hD ha hs ht hd)

/-- The selected multiplier uses the ORIGINAL lower first sign tag. -/
def choosePlus (h B D A : PTm n) : PTm n := eqb (QuadraticTowerConeTest.lowerFirst h B D A) one
def multiplier (h B D A : PTm n) : PTm n := sel (choosePlus h B D A) (wPlus h A) (wMinus h A)
def signedNorm (h B D A : PTm n) : PTm n := sel (choosePlus h B D A)
  (QuadraticTowerSignRecipe.norm h B D A) (negated h (QuadraticTowerSignRecipe.norm h B D A))
def oppositeTags (h B D A : PTm n) : Fm PTm n :=
  (((QuadraticTowerConeTest.lowerFirst h B D A ≐ one) ⋏ (QuadraticTowerConeTest.lowerSecond h B D A ≐ two)) ⋎
    ((QuadraticTowerConeTest.lowerFirst h B D A ≐ two) ⋏ (QuadraticTowerConeTest.lowerSecond h B D A ≐ one))) ⋏
      (QuadraticTowerConeTest.lowerRadicand h B D ≐ one)
def input (h B D A b : PTm n) : Fm PTm n := QuadraticTowerConeTest.source h B D A b ⋏ oppositeTags h B D A
@[simp] theorem subst_choosePlus {k : ℕ} (σ : Fin n → PTm k) (h B D A : PTm n) :
    Syn.subst σ (choosePlus h B D A) = choosePlus (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ A) := by simp [choosePlus]
@[simp] theorem subst_multiplier {k : ℕ} (σ : Fin n → PTm k) (h B D A : PTm n) :
    Syn.subst σ (multiplier h B D A) = multiplier (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ A) := by simp [multiplier,sel]
@[simp] theorem subst_signedNorm {k : ℕ} (σ : Fin n → PTm k) (h B D A : PTm n) :
    Syn.subst σ (signedNorm h B D A) = signedNorm (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ A) := by simp [signedNorm,sel]
@[simp] theorem subst_oppositeTags {k : ℕ} (σ : Fin n → PTm k) (h B D A : PTm n) :
    (oppositeTags h B D A).subst σ = oppositeTags (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ A) := by simp [oppositeTags]
@[simp] theorem subst_input {k : ℕ} (σ : Fin n → PTm k) (h B D A b : PTm n) :
    (input h B D A b).subst σ = input (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ A) (Syn.subst σ b) := by simp [input]

theorem choice_positive (h B D A : PTm n) (hs : Γ ⊢[PRAAx] QuadraticTowerConeTest.lowerFirst h B D A ≐ one) : Γ ⊢[PRAAx]
    choosePlus h B D A ≐ one := eqb_of_eq hs
theorem choice_negative (h B D A : PTm n) (hs : Γ ⊢[PRAAx] QuadraticTowerConeTest.lowerFirst h B D A ≐ two) : Γ ⊢[PRAAx]
    choosePlus h B D A ≐ zero := eqb_zero_of_gt (lt_congr (.eqRefl _) hs.eqSymm (le_refl two))

theorem multiplier_plus (h B D A : PTm n) (hs : Γ ⊢[PRAAx] QuadraticTowerConeTest.lowerFirst h B D A ≐ one) : Γ ⊢[PRAAx]
    multiplier h B D A ≐ wPlus h A := sel_one (choice_positive h B D A hs)
theorem multiplier_minus (h B D A : PTm n) (hs : Γ ⊢[PRAAx] QuadraticTowerConeTest.lowerFirst h B D A ≐ two) : Γ ⊢[PRAAx]
    multiplier h B D A ≐ wMinus h A := sel_zero (choice_negative h B D A hs)
theorem signedNorm_plus (h B D A : PTm n) (hs : Γ ⊢[PRAAx] QuadraticTowerConeTest.lowerFirst h B D A ≐ one) : Γ ⊢[PRAAx]
    signedNorm h B D A ≐ QuadraticTowerSignRecipe.norm h B D A := sel_one (choice_positive h B D A hs)
theorem signedNorm_minus (h B D A : PTm n) (hs : Γ ⊢[PRAAx] QuadraticTowerConeTest.lowerFirst h B D A ≐ two) : Γ ⊢[PRAAx]
    signedNorm h B D A ≐ negated h (QuadraticTowerSignRecipe.norm h B D A) := sel_zero (choice_negative h B D A hs)

theorem flag_operand_congr (h B D : PTm n) {A C : PTm n} (e : Γ ⊢[PRAAx] A ≐ C) : Γ ⊢[PRAAx]
    QuadraticTowerConeTest.flag h B D A ≐ QuadraticTowerConeTest.flag h B D C := by
  simpa using Prf.eqCongr (QuadraticTowerConeTest.flag (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![h,B,D,A]) (σ' := ![h,B,D,C]) (fun i => by fin_cases i; exact .eqRefl _; exact .eqRefl _; exact .eqRefl _; exact e)

def certificate (h B D A : PTm n) : Fm PTm n :=
  (QuadraticTowerConeTest.flag h B D (multiplier h B D A) ≐ one) ⋏
    ((QuadraticTowerSignTable.query (succ h) B D (multiplier h B D A) ≐ one) ⋏
      (query (succ h) B D (multiplier h B D A) A ≐ append (signedNorm h B D A) (zeroArray h)))
@[simp] theorem subst_certificate {k : ℕ} (σ : Fin n → PTm k) (h B D A : PTm n) :
    (certificate h B D A).subst σ = certificate (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ A) := by simp [certificate]

theorem certificate_plus (h B D A b : PTm n) (p : Γ ⊢[PRAAx] QuadraticTowerConeTest.source h B D A b)
    (hs : Γ ⊢[PRAAx] QuadraticTowerConeTest.lowerFirst h B D A ≐ one)
    (ht : Γ ⊢[PRAAx] QuadraticTowerConeTest.lowerSecond h B D A ≐ two)
    (hd : Γ ⊢[PRAAx] QuadraticTowerConeTest.lowerRadicand h B D ≐ one) : Γ ⊢[PRAAx] certificate h B D A := by
  have w := multiplier_plus h B D A hs
  have flag := (flag_operand_congr h B D w).eqTrans (wPlus_flag h B D A b p.andE₁ p.andE₂.andE₁ p.andE₂.andE₂ hs ht hd)
  have sign := (QuadraticTowerSignRecipe.read_operand_congr (succ h) B (QuadraticTowerSignTable.table (succ h) B D) _ _ w).eqTrans
    (wPlus_positive h B D A b p.andE₁ p.andE₂.andE₁ p.andE₂.andE₂ hs ht hd)
  have product := (QuadraticTowerMultiplicationNegative.query_operands_congr (succ h) B D w (.eqRefl A)).eqTrans
    ((products h B D A b p.andE₁ p.andE₂.andE₁ p.andE₂.andE₂).andE₁.eqTrans
      (QuadraticTowerCoefficients.append_congr (signedNorm_plus h B D A hs).eqSymm (.eqRefl _)))
  exact .andI flag (.andI sign product)

theorem certificate_minus (h B D A b : PTm n) (p : Γ ⊢[PRAAx] QuadraticTowerConeTest.source h B D A b)
    (hs : Γ ⊢[PRAAx] QuadraticTowerConeTest.lowerFirst h B D A ≐ two)
    (ht : Γ ⊢[PRAAx] QuadraticTowerConeTest.lowerSecond h B D A ≐ one)
    (hd : Γ ⊢[PRAAx] QuadraticTowerConeTest.lowerRadicand h B D ≐ one) : Γ ⊢[PRAAx] certificate h B D A := by
  have w := multiplier_minus h B D A hs
  have flag := (flag_operand_congr h B D w).eqTrans (wMinus_flag h B D A b p.andE₁ p.andE₂.andE₁ p.andE₂.andE₂ hs ht hd)
  have sign := (QuadraticTowerSignRecipe.read_operand_congr (succ h) B (QuadraticTowerSignTable.table (succ h) B D) _ _ w).eqTrans
    (wMinus_positive h B D A b p.andE₁ p.andE₂.andE₁ p.andE₂.andE₂ hs ht hd)
  have product := (QuadraticTowerMultiplicationNegative.query_operands_congr (succ h) B D w (.eqRefl A)).eqTrans
    ((products h B D A b p.andE₁ p.andE₂.andE₁ p.andE₂.andE₂).andE₂.eqTrans
      (QuadraticTowerCoefficients.append_congr (signedNorm_minus h B D A hs).eqSymm (.eqRefl _)))
  exact .andI flag (.andI sign product)

/-- Original opposite lower tags and positive radicand produce a real
computed cone witness and its literal original signed-norm product. -/
theorem original_certificate (h B D A b : PTm n) (p : Γ ⊢[PRAAx] input h B D A b) : Γ ⊢[PRAAx] certificate h B D A :=
  .orE p.andE₂.andE₁
    (certificate_plus h B D A b p.andE₁.wk Prf.hyp0.andE₁ Prf.hyp0.andE₂ p.andE₂.andE₂.wk)
    (certificate_minus h B D A b p.andE₁.wk Prf.hyp0.andE₁ Prf.hyp0.andE₂ p.andE₂.andE₂.wk)

/-! The actual fixed-arity compiler returns its chosen multiplier, both
computed tests, the SAME product, signed norm and lower budget. -/
def output (h B D A : PTm n) : PTm n := pairT (multiplier h B D A)
  (pairT (QuadraticTowerConeTest.flag h B D (multiplier h B D A))
    (pairT (QuadraticTowerSignTable.query (succ h) B D (multiplier h B D A))
      (pairT (query (succ h) B D (multiplier h B D A) A) (pairT (signedNorm h B D A) (budget h B D)))))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (h B D A : PTm n) : PTm n := PTm.app outputF ![h,B,D,A]
@[simp] theorem subst_output {k : ℕ} (σ : Fin n → PTm k) (h B D A : PTm n) :
    Syn.subst σ (output h B D A) = output (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ A) := by simp [output]
@[simp] theorem subst_run {k : ℕ} (σ : Fin n → PTm k) (h B D A : PTm n) :
    Syn.subst σ (run h B D A) = run (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ A) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (h B D A : PTm n) : Γ ⊢[PRAAx] run h B D A ≐ output h B D A := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![h,B,D,A]
theorem returned_multiplier (h B D A : PTm n) : Γ ⊢[PRAAx] fstT (run h B D A) ≐ multiplier h B D A :=
  (congrFst (program_at _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_tests (h B D A : PTm n) : Γ ⊢[PRAAx] sndT (run h B D A) ≐
    pairT (QuadraticTowerConeTest.flag h B D (multiplier h B D A))
      (pairT (QuadraticTowerSignTable.query (succ h) B D (multiplier h B D A))
        (pairT (query (succ h) B D (multiplier h B D A) A) (pairT (signedNorm h B D A) (budget h B D)))) :=
  (congrSnd (program_at _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_flag (h B D A : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run h B D A)) ≐ QuadraticTowerConeTest.flag h B D (multiplier h B D A) :=
  (congrFst (returned_tests _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_sign_tail (h B D A : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run h B D A)) ≐
    pairT (QuadraticTowerSignTable.query (succ h) B D (multiplier h B D A))
      (pairT (query (succ h) B D (multiplier h B D A) A) (pairT (signedNorm h B D A) (budget h B D))) :=
  (congrSnd (returned_tests _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_sign (h B D A : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run h B D A))) ≐
    QuadraticTowerSignTable.query (succ h) B D (multiplier h B D A) :=
  (congrFst (returned_sign_tail _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_product_tail (h B D A : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run h B D A))) ≐
    pairT (query (succ h) B D (multiplier h B D A) A) (pairT (signedNorm h B D A) (budget h B D)) :=
  (congrSnd (returned_sign_tail _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_product (h B D A : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run h B D A)))) ≐
    query (succ h) B D (multiplier h B D A) A :=
  (congrFst (returned_product_tail _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_norm_tail (h B D A : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (run h B D A)))) ≐
    pairT (signedNorm h B D A) (budget h B D) :=
  (congrSnd (returned_product_tail _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_norm (h B D A : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (sndT (run h B D A))))) ≐ signedNorm h B D A :=
  (congrFst (returned_norm_tail _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_cap (h B D A : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (sndT (run h B D A))))) ≐ budget h B D :=
  (congrSnd (returned_norm_tail _ _ _ _)).eqTrans (snd_pair _ _)

theorem returned_success (h B D A b : PTm n) (p : Γ ⊢[PRAAx] input h B D A b) : Γ ⊢[PRAAx]
    (fstT (sndT (run h B D A)) ≐ one) ⋏
      ((fstT (sndT (sndT (run h B D A))) ≐ one) ⋏
        (fstT (sndT (sndT (sndT (run h B D A)))) ≐
          append (fstT (sndT (sndT (sndT (sndT (run h B D A)))))) (zeroArray h))) := by
  have result := original_certificate h B D A b p
  exact .andI ((returned_flag _ _ _ _).eqTrans result.andE₁)
    (.andI ((returned_sign _ _ _ _).eqTrans result.andE₂.andE₁)
      ((returned_product _ _ _ _).eqTrans (result.andE₂.andE₂.eqTrans
        (QuadraticTowerCoefficients.append_congr (returned_norm _ _ _ _).eqSymm (.eqRefl _)))))

theorem original_opposite_signed_norm_products_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (var 1) ⟶ radicandsHeight (var 2) (succ (var 0)) (var 4) ⟶ arrayHeight (succ (var 0)) (var 3) (var 4) ⟶
      ((query (succ (var 0)) (var 1) (var 2) (wPlus (var 0) (var 3)) (var 3) ≐
        append (QuadraticTowerSignRecipe.norm (var 0) (var 1) (var 2) (var 3)) (zeroArray (var 0))) ⋏
       (query (succ (var 0)) (var 1) (var 2) (wMinus (var 0) (var 3)) (var 3) ≐
        append (negated (var 0) (QuadraticTowerSignRecipe.norm (var 0) (var 1) (var 2) (var 3))) (zeroArray (var 0))))) :=
  closeUniv 5 (.impI (.impI (.impI (products _ _ _ _ (var 4) (.hyp (by simp)) Prf.hyp1 Prf.hyp0))))
theorem original_opposite_multiplier_certificate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ certificate (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 5 (.impI (original_certificate _ _ _ _ (var 4) Prf.hyp0))
theorem original_positive_negative_multiplier_flag_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (QuadraticTowerConeTest.source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      QuadraticTowerConeTest.lowerFirst (var 0) (var 1) (var 2) (var 3) ≐ one ⟶
      QuadraticTowerConeTest.lowerSecond (var 0) (var 1) (var 2) (var 3) ≐ two ⟶
      QuadraticTowerConeTest.lowerRadicand (var 0) (var 1) (var 2) ≐ one ⟶
        QuadraticTowerConeTest.flag (var 0) (var 1) (var 2) (wPlus (var 0) (var 3)) ≐ one) := by
  apply closeUniv 5
  refine .impI (.impI (.impI (.impI ?_)))
  let Δ : List (Fm PTm 5) := [QuadraticTowerConeTest.lowerRadicand (var 0) (var 1) (var 2) ≐ one,
    QuadraticTowerConeTest.lowerSecond (var 0) (var 1) (var 2) (var 3) ≐ two,
    QuadraticTowerConeTest.lowerFirst (var 0) (var 1) (var 2) (var 3) ≐ one,
    QuadraticTowerConeTest.source (var 0) (var 1) (var 2) (var 3) (var 4)]
  have source : Δ ⊢[PRAAx] QuadraticTowerConeTest.source (var 0) (var 1) (var 2) (var 3) (var 4) := .hyp (by simp [Δ])
  exact wPlus_flag _ _ _ _ (var 4) source.andE₁ source.andE₂.andE₁ source.andE₂.andE₂ (.hyp (by simp)) Prf.hyp1 Prf.hyp0
theorem original_negative_positive_multiplier_flag_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (QuadraticTowerConeTest.source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      QuadraticTowerConeTest.lowerFirst (var 0) (var 1) (var 2) (var 3) ≐ two ⟶
      QuadraticTowerConeTest.lowerSecond (var 0) (var 1) (var 2) (var 3) ≐ one ⟶
      QuadraticTowerConeTest.lowerRadicand (var 0) (var 1) (var 2) ≐ one ⟶
        QuadraticTowerConeTest.flag (var 0) (var 1) (var 2) (wMinus (var 0) (var 3)) ≐ one) := by
  apply closeUniv 5
  refine .impI (.impI (.impI (.impI ?_)))
  let Δ : List (Fm PTm 5) := [QuadraticTowerConeTest.lowerRadicand (var 0) (var 1) (var 2) ≐ one,
    QuadraticTowerConeTest.lowerSecond (var 0) (var 1) (var 2) (var 3) ≐ one,
    QuadraticTowerConeTest.lowerFirst (var 0) (var 1) (var 2) (var 3) ≐ two,
    QuadraticTowerConeTest.source (var 0) (var 1) (var 2) (var 3) (var 4)]
  have source : Δ ⊢[PRAAx] QuadraticTowerConeTest.source (var 0) (var 1) (var 2) (var 3) (var 4) := .hyp (by simp [Δ])
  exact wMinus_flag _ _ _ _ (var 4) source.andE₁ source.andE₂.andE₁ source.andE₂.andE₂ (.hyp (by simp)) Prf.hyp1 Prf.hyp0
theorem actual_opposite_multiplier_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (program_at _ _ _ _)
theorem actual_opposite_multiplier_returned_array_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (fstT (run (var 0) (var 1) (var 2) (var 3)) ≐ multiplier (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (returned_multiplier _ _ _ _)
theorem actual_opposite_multiplier_returned_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (sndT (sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3)))))) ≐ budget (var 0) (var 1) (var 2)) := closeUniv 4 (returned_cap _ _ _ _)
theorem original_opposite_multiplier_returned_certificate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      ((fstT (sndT (run (var 0) (var 1) (var 2) (var 3))) ≐ one) ⋏
        ((fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3)))) ≐ one) ⋏
          (fstT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3))))) ≐
            append (fstT (sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3))))))) (zeroArray (var 0)))))) :=
  closeUniv 5 (.impI (returned_success _ _ _ _ (var 4) Prf.hyp0))

end LeanProofs.IPRA.Algebra.QuadraticTowerOppositeMultiplier
