import PA194ModelSepRootGraph
import PA194ModelStandardNoFree
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem sepRootPure_shift_fixed (p : V) (hp : IsSemiformula SourceL 1 p)
    (hshift : shift SourceL p = p) : shift SourceL (sepRootPure p) = sepRootPure p := by
  have hr : SourceL.IsRel (2 : V) (1 : V) := by
    change (“k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” : ArithmeticSemisentence 2).Evalb ![(2 : V), 1]
    simp
  have hv01 : IsUTermVec SourceL 2 (?[ ^#(0 : V), ^#(1 : V)] : V) := by simp
  have hv02 : IsUTermVec SourceL 2 (?[ ^#(0 : V), ^#(2 : V)] : V) := by simp
  have hA : IsUFormula SourceL (^nrel (2 : V) 1 (?[ ^#(0 : V), ^#(1 : V)] : V)) := by simpa only [IsUFormula.nrel] using And.intro hr hv01
  have hB : IsUFormula SourceL (^rel (2 : V) 1 (?[ ^#(0 : V), ^#(2 : V)] : V)) := by simpa only [IsUFormula.rel] using And.intro hr hv02
  have hC : IsUFormula SourceL (^nrel (2 : V) 1 (?[ ^#(0 : V), ^#(2 : V)] : V)) := by simpa only [IsUFormula.nrel] using And.intro hr hv02
  have hD : IsUFormula SourceL (^rel (2 : V) 1 (?[ ^#(0 : V), ^#(1 : V)] : V)) := by simpa only [IsUFormula.rel] using And.intro hr hv01
  have ua {a b : V} (ha : IsUFormula SourceL a) (hb : IsUFormula SourceL b) : IsUFormula SourceL (a ^⋏ b) := by simpa only [IsUFormula.and] using And.intro ha hb
  have uo {a b : V} (ha : IsUFormula SourceL a) (hb : IsUFormula SourceL b) : IsUFormula SourceL (a ^⋎ b) := by simpa only [IsUFormula.or] using And.intro ha hb
  have uall {a : V} (ha : IsUFormula SourceL a) : IsUFormula SourceL (^∀ a) := by simpa only [IsUFormula.all] using ha
  have uex {a : V} (ha : IsUFormula SourceL a) : IsUFormula SourceL (^∃ a) := by simpa only [IsUFormula.ex] using ha
  have ht0 : IsUTerm SourceL (^#(0 : V)) := by simp
  have ht1 : IsUTerm SourceL (^#(1 : V)) := by simp
  have ht2 : IsUTerm SourceL (^#(2 : V)) := by simp
  have hu := hp.isUFormula
  have hn := hu.neg
  simp only [sepRootPure, shift_all (uex (uall (ua (uo hA (ua hB hu)) (uo (uo hC hn) hD)))),
    shift_exs (uall (ua (uo hA (ua hB hu)) (uo (uo hC hn) hD))),
    shift_all (ua (uo hA (ua hB hu)) (uo (uo hC hn) hD)),
    shift_and (uo hA (ua hB hu)) (uo (uo hC hn) hD),
    shift_or hA (ua hB hu), shift_and hB hu,
    shift_or (uo hC hn) hD, shift_or hC hn,
    shift_rel hr hv01, shift_rel hr hv02, shift_nrel hr hv01, shift_nrel hr hv02,
    shift_neg hp, hshift, termShiftVec_cons₂ ht0 ht1, termShiftVec_cons₂ ht0 ht2, termShift_bvar]
#print axioms sepRootPure_shift_fixed
end generic
end PA194ModelLogic
