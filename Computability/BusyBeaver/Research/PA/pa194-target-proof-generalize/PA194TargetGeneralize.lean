import PA194TargetProofLeaf
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194TargetGeneralize
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194PathIterator PA194TermShiftCodeModel PA194CloseVariable PA194TargetCantor PA194TargetLeaves
 PA194TargetStep PA194TargetSound PA194TargetExtendedStep PA194ParamHistory PA194StackCode PA194StackHistory
 PA194TargetGuardedHistory PA194TargetVectorLength PA194TargetProofLeaf
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem prefix_def (f g : M → M) (bound : M)
    (hf : 𝚺₁-Function₁ f) (hg : 𝚺₁-Function₁ g) :
    𝚺₁-Predicate (fun n => n ≤ bound → f n = g n) := by
  haveI := hf
  haveI := hg
  definability

theorem prefix_history (program line n : M) (hn : n ≤ len program) :
    F autoHistory ![n,concat program line,0] = F autoHistory ![n,program,0] := by
  have hf : 𝚺₁-Function₁ (fun n : M => F autoHistory ![n,concat program line,0]) :=
    PA194CodeInstance.unary_of_three autoHistory (concat program line) 0
  have hg : 𝚺₁-Function₁ (fun n : M => F autoHistory ![n,program,0]) :=
    PA194CodeInstance.unary_of_three autoHistory program 0
  have hdef := prefix_def _ _ (len program) hf hg
  have hgeneral : ∀ k : M, k ≤ len program → F autoHistory ![k,concat program line,0] = F autoHistory ![k,program,0] := by
    intro k
    induction k using ISigma1.sigma1_succ_induction with
    | hP => exact hdef
    | zero =>
      intro _
      change F (PA194ParamHistory.historyCode autoNext) ![0,concat program line,0] = F (PA194ParamHistory.historyCode autoNext) ![0,program,0]
      rw [PA194ParamHistory.modelBase,PA194ParamHistory.modelBase]
    | succ k ih =>
      intro hlen
      have hklt : k < len program := lt_iff_succ_le.mpr hlen
      have hkle : k ≤ len program := le_of_lt hklt
      rw [autoHistory_step,autoHistory_step,len_concat,if_pos (lt_trans hklt (lt_add_one (len program))),
        if_pos hklt,concat_nth_lt _ _ hklt,ih hkle]
  exact hgeneral n hn

theorem generalize_closed (label result : M) : TargetProvable result → TargetProvable (allValue label result) := by
  rintro ⟨program,hpos,hroot⟩
  let line : M := pair 1 (pair label 0)
  let program' := concat program line
  refine ⟨program', ?_⟩
  constructor
  · simp [program']
  · rw [rootCode_model]
    have hpref := prefix_history program line (len program) (le_refl _)
    have hres : F lookup ![0,F autoHistory ![len program,program,0]] = result+1 := by
      simpa [rootCode_model] using hroot
    change F lookup ![0,F autoHistory ![len (concat program line),concat program line,0]] = _
    rw [len_concat,autoHistory_newest,len_concat,if_pos (lt_add_one (len program)),concat_nth_len,hpref]
    rw [fallback (len program) _ 1 (pair label 0) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),gen_step]
    rw [if_pos hpos,PA194TargetGen.check_model,hres,if_neg (by simp),modelPredAddOne]

#print axioms prefix_history
#print axioms generalize_closed
end models
end PA194TargetGeneralize
