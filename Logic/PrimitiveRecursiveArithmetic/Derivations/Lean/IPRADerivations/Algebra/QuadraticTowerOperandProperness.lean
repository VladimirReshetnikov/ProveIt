import IPRADerivations.Algebra.QuadraticTowerArrayNormalization

/-!
# Original rational-value operands of the actual tower table

Bounded equality of the original rational coefficient values gives exactly
the same constructed normalized code, packed address and actual table
query. No input height or table correctness law is needed for this
same-cap fact. Under the original height guards the actual successor query
uses the same cap-independent normalized operands; its ground query is the
actual original rational product. This is an operand interface, not yet
equality of multiplication tables constructed with different budgets.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Algebra.QuadraticTowerOperandProperness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis
open QuadraticTowerCoefficients (width singleton)
open QuadraticTowerArrayCodec (arrayHeight normalized code)
open QuadraticTowerCoefficientArithmetic (equalValues)
open QuadraticTowerArrayNormalization (normalized_proper restored_normalized)
open QuadraticTowerMultiplicationTable
  (address lookup query table recipe budget)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem packed_congr {A C W V S T : PTm n}
    (hA : Γ ⊢[PRAAx] A ≐ C) (hW : Γ ⊢[PRAAx] W ≐ V) (hS : Γ ⊢[PRAAx] S ≐ T) : Γ ⊢[PRAAx]
    QuadraticTowerArrayCodec.packed A W S ≐ QuadraticTowerArrayCodec.packed C V T := by
  simpa [QuadraticTowerArrayCodec.subst_packed] using
    Prf.eqCongr (QuadraticTowerArrayCodec.packed (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![A,W,S]) (σ' := ![C,V,T])
      (fun i => by fin_cases i; exact hA; exact hW; exact hS)

theorem code_proper (h A C B : PTm n) (hV : Γ ⊢[PRAAx] equalValues h A C) :
    Γ ⊢[PRAAx] code h A B ≐ code h C B :=
  packed_congr (normalized_proper h A C hV) (.eqRefl _) (.eqRefl _)

theorem address_proper (h B A A' C C' : PTm n)
    (hA : Γ ⊢[PRAAx] equalValues h A A') (hC : Γ ⊢[PRAAx] equalValues h C C') :
    Γ ⊢[PRAAx] address h B A C ≐ address h B A' C' :=
  congrAdd (congrMul (code_proper h A A' B hA) (.eqRefl _)) (code_proper h C C' B hC)

theorem lookup_proper (h B T A A' C C' : PTm n)
    (hA : Γ ⊢[PRAAx] equalValues h A A') (hC : Γ ⊢[PRAAx] equalValues h C C') :
    Γ ⊢[PRAAx] lookup h B T A C ≐ lookup h B T A' C' :=
  entry_congr (.eqRefl _) (address_proper h B A A' C C' hA hC)

theorem query_operands_proper (h B D A A' C C' : PTm n)
    (hA : Γ ⊢[PRAAx] equalValues h A A') (hC : Γ ⊢[PRAAx] equalValues h C C') :
    Γ ⊢[PRAAx] query h B D A C ≐ query h B D A' C' :=
  lookup_proper h B (table h B D) A A' C C' hA hC

theorem normalized_values (h A : PTm n) : Γ ⊢[PRAAx] equalValues h (normalized h A) A := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (width (Syn.shift h)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (width (Syn.shift h)) := Prf.hyp0
  have value := RationalArgmin.rationalEq_congr
    (QuadraticTowerArrayCodec.normalized_lookup (Γ := Δ) (Syn.shift h) (Syn.shift A) (var 0) hi).eqSymm
      (.eqRefl _) (RationalArithmetic.recode_equal _)
  simpa only [Δ,Syn.shift,QuadraticTowerCoefficients.subst_width,
    QuadraticTowerArrayCodec.subst_normalized] using value

theorem query_normalized (h B D A C : PTm n) : Γ ⊢[PRAAx]
    query h B D (normalized h A) (normalized h C) ≐ query h B D A C :=
  query_operands_proper h B D _ A _ C (normalized_values h A) (normalized_values h C)

theorem scalar_equal_of_canonical (a b : PTm n)
    (ha : Γ ⊢[PRAAx] RationalNormalForm.wellFormed a)
    (hb : Γ ⊢[PRAAx] RationalNormalForm.wellFormed b)
    (hv : Γ ⊢[PRAAx] RationalArgmin.rationalEq a b) : Γ ⊢[PRAAx] a ≐ b :=
  (RationalNormalForm.normalize_fixed_point a ha).eqSymm.eqTrans
    ((RationalGaussianEmbedding.scalar_recode_equal a b hv).eqTrans
      (RationalNormalForm.normalize_fixed_point b hb))

theorem scalar_product_recoded (a b : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.multiply (RationalArithmetic.recode a) (RationalArithmetic.recode b) ≐
      RationalArithmetic.multiply a b :=
  scalar_equal_of_canonical _ _ (RationalArithmetic.multiply_guard _ _) (RationalArithmetic.multiply_guard _ _)
    (QuadraticRationalRepresentationInvariance.scalar_multiply_congr _ _ _ _
      (RationalArithmetic.recode_equal a) (RationalArithmetic.recode_equal b))

theorem query_succ_normalized (h B D A C : PTm n)
    (hA : Γ ⊢[PRAAx] arrayHeight (succ h) A B)
    (hC : Γ ⊢[PRAAx] arrayHeight (succ h) C B) : Γ ⊢[PRAAx]
    query (succ h) B D A C ≐ recipe h B (table h (budget h B D) D) D
      (normalized (succ h) A) (normalized (succ h) C) :=
  (QuadraticTowerMultiplicationTable.query_succ h B D A C hA hC).eqTrans
    (QuadraticTowerMultiplicationTable.recipe_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (restored_normalized _ _ _ hA) (restored_normalized _ _ _ hC))

theorem ground_digit (A B : PTm n) (hA : Γ ⊢[PRAAx] arrayHeight zero A B) : Γ ⊢[PRAAx]
    QuadraticTowerArrayCodec.digit (QuadraticTowerScalarBudget.codeCap B) (code zero A B) zero ≐
      RationalArithmetic.recode (entry A zero) := by
  have hi : Γ ⊢[PRAAx] lt zero (width zero) := QuadraticTowerCoefficientArithmetic.base_index
  exact (QuadraticTowerArrayCodec.packed_digit _ _ _ _
    (QuadraticTowerArrayCodec.normalized_bounded zero A B hA) hi).eqTrans
      (QuadraticTowerArrayCodec.normalized_lookup zero A zero hi)

theorem singleton_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx]
    singleton a ≐ singleton b := by
  simpa [QuadraticTowerCoefficients.subst_singleton] using
    Prf.eqCongr (singleton (var 0) : PTm 1) (σ := ![a]) (σ' := ![b])
      (fun i => by fin_cases i; exact h)

theorem query_zero_original (B D A C : PTm n)
    (hA : Γ ⊢[PRAAx] arrayHeight zero A B) (hC : Γ ⊢[PRAAx] arrayHeight zero C B) : Γ ⊢[PRAAx]
    query zero B D A C ≐ singleton (RationalArithmetic.multiply (entry A zero) (entry C zero)) :=
  (QuadraticTowerMultiplicationTable.query_zero B D A C hA hC).eqTrans
    (singleton_congr ((RationalAlgebra.multiply_congr (ground_digit A B hA) (ground_digit C B hC)).eqTrans
      (scalar_product_recoded _ _)))

theorem returned_query_proper (h B D A A' C C' : PTm n)
    (hA : Γ ⊢[PRAAx] equalValues h A A') (hC : Γ ⊢[PRAAx] equalValues h C C') : Γ ⊢[PRAAx]
    PTm.app QuadraticTowerMultiplicationTable.queryF ![h,B,D,A,C] ≐
      PTm.app QuadraticTowerMultiplicationTable.queryF ![h,B,D,A',C'] :=
  (QuadraticTowerMultiplicationTable.query_program_at _ _ _ _ _).eqTrans
    ((query_operands_proper h B D A A' C C' hA hC).eqTrans
      (QuadraticTowerMultiplicationTable.query_program_at _ _ _ _ _).eqSymm)

theorem actual_array_code_values_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (equalValues (var 0) (var 1) (var 2) ⟶ code (var 0) (var 1) (var 3) ≐ code (var 0) (var 2) (var 3)) :=
  closeUniv 4 (.impI (code_proper _ _ _ _ Prf.hyp0))

theorem actual_table_address_values_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (equalValues (var 0) (var 2) (var 3) ⟶ equalValues (var 0) (var 4) (var 5) ⟶
      address (var 0) (var 1) (var 2) (var 4) ≐ address (var 0) (var 1) (var 3) (var 5)) :=
  closeUniv 6 (.impI (.impI (address_proper _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_table_query_values_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (equalValues (var 0) (var 3) (var 4) ⟶ equalValues (var 0) (var 5) (var 6) ⟶
      query (var 0) (var 1) (var 2) (var 3) (var 5) ≐ query (var 0) (var 1) (var 2) (var 4) (var 6)) :=
  closeUniv 7 (.impI (.impI (query_operands_proper _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_table_query_normalized_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (query (var 0) (var 1) (var 2) (normalized (var 0) (var 3)) (normalized (var 0) (var 4)) ≐
      query (var 0) (var 1) (var 2) (var 3) (var 4)) := closeUniv 5 (query_normalized _ _ _ _ _)

theorem actual_original_scalar_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (RationalArithmetic.multiply (RationalArithmetic.recode (var 0)) (RationalArithmetic.recode (var 1)) ≐
      RationalArithmetic.multiply (var 0) (var 1)) := closeUniv 2 (scalar_product_recoded _ _)

theorem actual_normalized_query_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (arrayHeight (succ (var 0)) (var 3) (var 1) ⟶ arrayHeight (succ (var 0)) (var 4) (var 1) ⟶
      query (succ (var 0)) (var 1) (var 2) (var 3) (var 4) ≐ recipe (var 0) (var 1)
        (table (var 0) (budget (var 0) (var 1) (var 2)) (var 2)) (var 2)
        (normalized (succ (var 0)) (var 3)) (normalized (succ (var 0)) (var 4))) :=
  closeUniv 5 (.impI (.impI (query_succ_normalized _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_ground_query_original_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (arrayHeight zero (var 2) (var 0) ⟶ arrayHeight zero (var 3) (var 0) ⟶
      query zero (var 0) (var 1) (var 2) (var 3) ≐
        singleton (RationalArithmetic.multiply (entry (var 2) zero) (entry (var 3) zero))) :=
  closeUniv 4 (.impI (.impI (query_zero_original _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_returned_query_values_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (equalValues (var 0) (var 3) (var 4) ⟶ equalValues (var 0) (var 5) (var 6) ⟶
      PTm.app QuadraticTowerMultiplicationTable.queryF ![var 0,var 1,var 2,var 3,var 5] ≐
        PTm.app QuadraticTowerMultiplicationTable.queryF ![var 0,var 1,var 2,var 4,var 6]) :=
  closeUniv 7 (.impI (.impI (returned_query_proper _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Algebra.QuadraticTowerOperandProperness
