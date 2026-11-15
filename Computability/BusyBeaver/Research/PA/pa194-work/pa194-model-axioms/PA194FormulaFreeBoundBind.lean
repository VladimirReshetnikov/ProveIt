import PA194FreeBoundBind
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194BindSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance freeBoundFormulaBindZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance freeBoundFormulaBindOne : One M := ⟨F oneCode Fin.elim0⟩
local instance freeBoundFormulaBindAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance freeBoundFormulaBindMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance freeBoundFormulaBindLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance freeBoundFormulaBindIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem bindFormula_freeBound (p k : M) (hp : IsUFormula SourceL p) :
    IsUFormula SourceL (bindFormula k p) ∧ formulaFreeBound (bindFormula k p) = formulaFreeBound p - 1 := by
  let K := p+k
  haveI : 𝚺₁-Function₂ (bindFormula : M → M → M) := bindFormula_definable
  haveI : 𝚺₁-Function₁ (formulaFreeBound : M → M) := formulaFreeBound_definable
  have hdef : 𝚺₁-Predicate (fun q : M => ∀ d ≤ K, q+d ≤ K →
      IsUFormula SourceL (bindFormula d q) ∧ formulaFreeBound (bindFormula d q) = formulaFreeBound q - 1) := by
    definability
  have hall : ∀ q, IsUFormula SourceL q → ∀ d ≤ K, q+d ≤ K →
      IsUFormula SourceL (bindFormula d q) ∧ formulaFreeBound (bindFormula d q) = formulaFreeBound q - 1 := by
    intro q hq
    apply IsUFormula.ISigma1.sigma1_succ_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ q hq
    · intro arity r v hr hv d hd hbound
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      obtain ⟨a,b,ha,hb,rfl⟩ := IsUTermVec.two_iff.mp hv
      have ha' := bindTerm_UTerm d a ha
      have hb' := bindTerm_UTerm d b hb
      have h1 : (?[a,b] : M).[1] = b := by
        have he : (1 : M) = (0 : M)+1 := by simp
        rw [he,nth_adjoin_succ,nth_adjoin_zero]
      have hv' : IsUTermVec SourceL 2 (bindPair d ?[a,b]) := by
        simp [bindPair, nth_adjoin_zero, h1, ha',hb']
      rw [bindFormula_rel d 2 r ?[a,b] hr (by simp [ha,hb])]
      constructor
      · simp [hr,hv']
      · rw [formulaFreeBound_rel _ _ _ hr hv', formulaFreeBound_rel _ _ _ hr (by simp [ha,hb])]
        exact pairFreeBound_bind d a b ha hb
    · intro arity r v hr hv d hd hbound
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      obtain ⟨a,b,ha,hb,rfl⟩ := IsUTermVec.two_iff.mp hv
      have ha' := bindTerm_UTerm d a ha
      have hb' := bindTerm_UTerm d b hb
      have h1 : (?[a,b] : M).[1] = b := by
        have he : (1 : M) = (0 : M)+1 := by simp
        rw [he,nth_adjoin_succ,nth_adjoin_zero]
      have hv' : IsUTermVec SourceL 2 (bindPair d ?[a,b]) := by
        simp [bindPair, nth_adjoin_zero, h1, ha',hb']
      rw [bindFormula_nrel d 2 r ?[a,b] hr (by simp [ha,hb])]
      constructor
      · simp [hr,hv']
      · rw [formulaFreeBound_nrel _ _ _ hr hv', formulaFreeBound_nrel _ _ _ hr (by simp [ha,hb])]
        exact pairFreeBound_bind d a b ha hb
    · intro d hd hbound
      simp [bindFormula_verum,formulaFreeBound_verum]
    · intro d hd hbound
      simp [bindFormula_falsum,formulaFreeBound_falsum]
    · intro a b ha hb iha ihb d hd hbound
      have hleA : a ≤ a ^⋏ b := le_of_lt <| lt_of_le_of_lt
        (le_trans (le_pair_left a b) (le_pair_right (4 : M) (pair a b))) (lt_add_one _)
      have hleB : b ≤ a ^⋏ b := le_of_lt <| lt_of_le_of_lt
        (le_trans (le_pair_right a b) (le_pair_right (4 : M) (pair a b))) (lt_add_one _)
      have hA : a+d ≤ K := le_trans (by simpa only [add_comm] using add_le_add_right hleA d) hbound
      have hB : b+d ≤ K := le_trans (by simpa only [add_comm] using add_le_add_right hleB d) hbound
      obtain ⟨ha',hba⟩ := iha d hd hA
      obtain ⟨hb',hbb⟩ := ihb d hd hB
      rw [bindFormula_and d a b ha hb]
      constructor
      · simp [ha',hb']
      · rw [formulaFreeBound_and _ _ ha' hb',formulaFreeBound_and _ _ ha hb,hba,hbb,max_tsub_one]
    · intro a b ha hb iha ihb d hd hbound
      have hleA : a ≤ a ^⋎ b := le_of_lt <| lt_of_le_of_lt
        (le_trans (le_pair_left a b) (le_pair_right (5 : M) (pair a b))) (lt_add_one _)
      have hleB : b ≤ a ^⋎ b := le_of_lt <| lt_of_le_of_lt
        (le_trans (le_pair_right a b) (le_pair_right (5 : M) (pair a b))) (lt_add_one _)
      have hA : a+d ≤ K := le_trans (by simpa only [add_comm] using add_le_add_right hleA d) hbound
      have hB : b+d ≤ K := le_trans (by simpa only [add_comm] using add_le_add_right hleB d) hbound
      obtain ⟨ha',hba⟩ := iha d hd hA
      obtain ⟨hb',hbb⟩ := ihb d hd hB
      rw [bindFormula_or d a b ha hb]
      constructor
      · simp [ha',hb']
      · rw [formulaFreeBound_or _ _ ha' hb',formulaFreeBound_or _ _ ha hb,hba,hbb,max_tsub_one]
    · intro a ha ih d hd hbound
      have hle : a+1 ≤ ^∀ a := by
        change a+1 ≤ pair (6 : M) a+1
        simpa only [add_comm] using add_le_add_right (le_pair_right (6 : M) a) 1
      have hA : a+(d+1) ≤ K := le_trans (by
        have hh := add_le_add_right hle d
        simpa only [add_assoc,add_comm,add_left_comm] using hh) hbound
      have hd1 : d+1 ≤ K := le_trans (by
        have hz : (0 : M) ≤ a := zero_le
        simpa only [zero_add,add_comm] using add_le_add_right hz (d+1)) hA
      obtain ⟨ha',hba⟩ := ih (d+1) hd1 hA
      rw [bindFormula_all d a ha]
      constructor
      · simp [ha']
      · rw [formulaFreeBound_all _ ha',formulaFreeBound_all _ ha,hba]
    · intro a ha ih d hd hbound
      have hle : a+1 ≤ ^∃ a := by
        change a+1 ≤ pair (7 : M) a+1
        simpa only [add_comm] using add_le_add_right (le_pair_right (7 : M) a) 1
      have hA : a+(d+1) ≤ K := le_trans (by
        have hh := add_le_add_right hle d
        simpa only [add_assoc,add_comm,add_left_comm] using hh) hbound
      have hd1 : d+1 ≤ K := le_trans (by
        have hz : (0 : M) ≤ a := zero_le
        simpa only [zero_add,add_comm] using add_le_add_right hz (d+1)) hA
      obtain ⟨ha',hba⟩ := ih (d+1) hd1 hA
      rw [bindFormula_ex d a ha]
      constructor
      · simp [ha']
      · rw [formulaFreeBound_ex _ ha',formulaFreeBound_ex _ ha,hba]
  have hk : k ≤ K := by
    have hz : (0 : M) ≤ p := zero_le
    simpa only [K,zero_add,add_zero,add_comm] using add_le_add_right hz k
  exact hall p hp k hk (by simp [K])

#print axioms bindFormula_freeBound
end models
end PA194BindSource
