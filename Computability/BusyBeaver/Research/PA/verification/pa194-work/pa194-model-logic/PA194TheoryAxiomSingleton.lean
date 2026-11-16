import PA194ConditionalProofCompiler
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194FormulaDispatcher
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (U : Theory PA194PAeq.language) [U.Δ₁] (T : Theory SourceL) [T.Δ₁]

theorem theoryAxiom_of_singletons {param : V} (hparam : ParametersValid 0 0 param)
    (hsupply : ∀ p : V, IsSemiformula PA194PAeq.language 0 p → p ∈ U.Δ₁Class →
      p < len (nth param 1) → Provable T (translateFormula param p)) :
    ∀ s p, IsFormulaSet PA194PAeq.language s → p ∈ s → p ∈ U.Δ₁Class →
      axm s p < len (nth param 1) → ∃ e, DerivationOf T e (translatedSequent param s) := by
  intro s p hs hp hu hsize
  have hlen : ∀ q ∈ s, q < len (nth param 1) := seqMembers_bounded (lt_trans (seq_lt_axm s p) hsize)
  have hscope : IsSemiformula PA194PAeq.language 0 p := hs p hp
  obtain ⟨d,hd⟩ := hsupply p hscope hu (hlen p hp)
  have hmember : translateFormula param p ∈ translatedSequent param s := translatedSequent_mem.mpr ⟨p,hp,rfl⟩
  have hsubset : ({translateFormula param p} : V) ⊆ translatedSequent param s := by
    intro q hq
    have : q = translateFormula param p := by simpa using hq
    subst q
    exact hmember
  refine ⟨wkRule (translatedSequent param s) d, ?_, ?_⟩
  · simp
  · exact Derivation.wkRule (translatedSequent_valid hparam hs hlen) hsubset hd
#print axioms theoryAxiom_of_singletons
end generic
end PA194FormulaDispatcher
