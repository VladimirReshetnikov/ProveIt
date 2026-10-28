import ZFCinPA.ValidatorSourceFullSeed222

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace LeanProofs.ZFCinPA.ValidatorSourceFullSeed222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222 ValidatorRelationalCore222 ValidatorSeedPadding222
open ValidatorFormulaEncoder222 ValidatorEnvironmentVacuity222 ValidatorEnvironmentStreams222
open ValidatorSourceFullSeed222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The retained statement contains BOTH native conjuncts. -/
theorem full_pair (bound p a b : V) (ha : a≤bound) (hb : b≤bound) :
    CProv (ex (seedLabel bound p)
      (conj (ArithmeticSeedTemplates222.clos a b (seedLabel bound p) p)
        (ArithmeticSeedTemplates222.req b (seedLabel bound p) p))) :=
  bounded_seed_pair bound p a b ha hb

theorem exact_quoted_body (K : SetTheorySemiproposition 2) :
    fullSeedBodyVal (⌜K⌝ : V) = (⌜fullSeedBodyMeta K⌝ : V) := fullSeedBodyVal_quote K

theorem exact_raw_typed_body (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    fullSeedBodyVal K.val = (fullSeedBody K).val := fullSeedBodyVal_eq K

/-- Original parameter17 occurs under a source binder. The image theorem
must retain F and cannot replace this matrix by a closed standard example. -/
def parameterMatrix : SetTheorySemiproposition 2 :=
  ∀⁰ ((FirstOrder.Semiformula.rel Language.Mem.mem
    ![(#0 : SyntacticSemiterm ℒₛₑₜ 3),&17]) 🡒 seedMem 3 2 1)

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2]

theorem arbitrary_internal (p F s : V) (hp : IsSemiformula ℒₛₑₜ 2 p)
    (hs : StreamFree s F) :
    ∃ d : V, ArithmeticHistory222.value d=encode F 0 s (fullSeedBodyVal p)+1 :=
  typed_fullSeed_witness hp F s hs

theorem nested_parameter (F s : V) (hs : StreamFree s F) :
    CProv (encode F 0 s (⌜fullSeedBodyMeta parameterMatrix⌝ : V)) :=
  quoted_fullSeed_image parameterMatrix F s hs

/-- Adjacent even steps overlap the original stream. No Apart premise is
required of the requested output stream. -/
theorem overlapping_stream (K : Bootstrapping.Semiformula V ℒₛₑₜ 2)
    (F s : V) (hs : StreamFree s F) :
    CProv (encode F 0 (s+2) (fullSeedBody K).val) :=
  fullSeed_image K F (s+2) (streamFree_next hs)

theorem actual_even_stream (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    CProv (encode 0 0 2 (fullSeedBody K).val) :=
  fullSeed_image K 0 2 (streamFree_of_bounds (by simp) (by simp))

theorem truth_matrix (F s : V) (hs : StreamFree s F) :
    CProv (encode F 0 s (fullSeedBody (⊤ : Bootstrapping.Semiformula V ℒₛₑₜ 2)).val) :=
  fullSeed_image _ F s hs

theorem falsum_matrix (F s : V) (hs : StreamFree s F) :
    CProv (encode F 0 s (fullSeedBody (⊥ : Bootstrapping.Semiformula V ℒₛₑₜ 2)).val) :=
  fullSeed_image _ F s hs

#print axioms bounded_seed_pair
#print axioms encode_stack_relabel
#print axioms matrix_congr
#print axioms matrix_vac
#print axioms fullSeedBody_quote
#print axioms fullSeedBodyVal_eq
#print axioms fullSeedBodyVal_quote
#print axioms fullSeed_image
#print axioms typed_fullSeed_image
#print axioms typed_fullSeed_witness
#print axioms quoted_fullSeed_image
#print axioms arbitrary_internal
#print axioms nested_parameter
#print axioms overlapping_stream
#print axioms actual_even_stream
#print axioms truth_matrix
#print axioms falsum_matrix

end LeanProofs.ZFCinPA.ValidatorSourceFullSeed222Checks
