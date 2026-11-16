import PA194PAeqOpeningFormulaRules
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.OpeningQVec
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqBind
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
/-- Scoped formula closure preserves well-formedness and reopens to the input. -/
theorem bindFormula_scope_open (p : M) (hp : IsSemiformula language 0 p) :
    IsSemiformula language 1 (bindFormula 0 p) ∧
      LO.FirstOrder.Arithmetic.Bootstrapping.free language (bindFormula 0 p) = p := by
  let K := p
  obtain ⟨s,hs,hl⟩ := sourceQVec_exists_trace (?[ ^&(0 : M)] : M) K
  haveI : 𝚺₁-Function₂ (bindFormula : M → M → M) := bindFormula_defined.to_definable
  have hdef : 𝚺₁-Predicate (fun q : M => ∀ k ≤ K, q+k ≤ K → IsSemiformula language k q →
      IsSemiformula language (k+1) (bindFormula k q) ∧ openingFormula s k (bindFormula k q) = q) := by
    unfold openingFormula
    definability
  have hall : ∀ q, IsUFormula language q → ∀ k ≤ K, q+k ≤ K → IsSemiformula language k q →
      IsSemiformula language (k+1) (bindFormula k q) ∧ openingFormula s k (bindFormula k q) = q := by
    intro q hq
    apply IsUFormula.ISigma1.sigma1_succ_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ q hq
    · intro arity r v hr hv k hk hbound hscope
      have hvec := (IsSemiformula.rel.mp hscope).2
      constructor
      · exact bindFormula_scope hscope.isUFormula k k (le_refl k) hscope
      · exact opening_bind_positiveAtom K s k arity r v hs hl hk hr hvec
    · intro arity r v hr hv k hk hbound hscope
      have hvec := (IsSemiformula.nrel.mp hscope).2
      constructor
      · exact bindFormula_scope hscope.isUFormula k k (le_refl k) hscope
      · exact opening_bind_negativeAtom K s k arity r v hs hl hk hr hvec
    · intro k hk hbound hscope
      simp [bindFormula_verum,openingFormula,shift_verum,substs_verum]
    · intro k hk hbound hscope
      simp [bindFormula_falsum,openingFormula,shift_falsum,substs_falsum]
    · intro a b ha hb iha ihb k hk hbound hscope
      have hleA : a ≤ a ^⋏ b := le_of_lt <| lt_of_le_of_lt
        (le_trans (le_pair_left a b) (le_pair_right (4 : M) (pair a b))) (lt_add_one _)
      have hleB : b ≤ a ^⋏ b := le_of_lt <| lt_of_le_of_lt
        (le_trans (le_pair_right a b) (le_pair_right (4 : M) (pair a b))) (lt_add_one _)
      have hA : a+k ≤ K := le_trans (by simpa only [add_comm] using add_le_add_right hleA k) hbound
      have hB : b+k ≤ K := le_trans (by simpa only [add_comm] using add_le_add_right hleB k) hbound
      obtain ⟨hsa,hsb⟩ := IsSemiformula.and.mp hscope
      obtain ⟨hsa',hopenA⟩ := iha k hk hA hsa
      obtain ⟨hsb',hopenB⟩ := ihb k hk hB hsb
      rw [bindFormula_and ha hb]
      constructor
      · exact IsSemiformula.and.mpr ⟨hsa',hsb'⟩
      · rw [openingFormula_and s k _ _ hsa'.isUFormula hsb'.isUFormula,hopenA,hopenB]
    · intro a b ha hb iha ihb k hk hbound hscope
      have hleA : a ≤ a ^⋎ b := le_of_lt <| lt_of_le_of_lt
        (le_trans (le_pair_left a b) (le_pair_right (5 : M) (pair a b))) (lt_add_one _)
      have hleB : b ≤ a ^⋎ b := le_of_lt <| lt_of_le_of_lt
        (le_trans (le_pair_right a b) (le_pair_right (5 : M) (pair a b))) (lt_add_one _)
      have hA : a+k ≤ K := le_trans (by simpa only [add_comm] using add_le_add_right hleA k) hbound
      have hB : b+k ≤ K := le_trans (by simpa only [add_comm] using add_le_add_right hleB k) hbound
      obtain ⟨hsa,hsb⟩ := IsSemiformula.or.mp hscope
      obtain ⟨hsa',hopenA⟩ := iha k hk hA hsa
      obtain ⟨hsb',hopenB⟩ := ihb k hk hB hsb
      rw [bindFormula_or ha hb]
      constructor
      · exact IsSemiformula.or.mpr ⟨hsa',hsb'⟩
      · rw [openingFormula_or s k _ _ hsa'.isUFormula hsb'.isUFormula,hopenA,hopenB]
    · intro a ha ih k hk hbound hscope
      have hle : a+1 ≤ ^∀ a := by
        change a+1 ≤ pair (6 : M) a+1
        simpa only [add_comm] using add_le_add_right (le_pair_right (6 : M) a) 1
      have hA : a+(k+1) ≤ K := le_trans (by
        have hh := add_le_add_right hle k
        simpa only [add_assoc,add_comm,add_left_comm] using hh) hbound
      have hk1 : k+1 ≤ K := le_trans (by
        have hz : (0 : M) ≤ a := zero_le
        simpa only [zero_add,add_comm] using add_le_add_right hz (k+1)) hA
      have hka : k < K := lt_iff_succ_le.mpr hk1
      have hsa : IsSemiformula language (k+1) a := by simpa only [IsSemiformula.all] using hscope
      obtain ⟨hsa',hopen⟩ := ih (k+1) hk1 hA hsa
      rw [bindFormula_all ha]
      constructor
      · exact IsSemiformula.all.mpr (by simpa only [add_assoc] using hsa')
      · rw [openingFormula_all K s k _ hs hl hka hsa'.isUFormula,hopen]
    · intro a ha ih k hk hbound hscope
      have hle : a+1 ≤ ^∃ a := by
        change a+1 ≤ pair (7 : M) a+1
        simpa only [add_comm] using add_le_add_right (le_pair_right (7 : M) a) 1
      have hA : a+(k+1) ≤ K := le_trans (by
        have hh := add_le_add_right hle k
        simpa only [add_assoc,add_comm,add_left_comm] using hh) hbound
      have hk1 : k+1 ≤ K := le_trans (by
        have hz : (0 : M) ≤ a := zero_le
        simpa only [zero_add,add_comm] using add_le_add_right hz (k+1)) hA
      have hka : k < K := lt_iff_succ_le.mpr hk1
      have hsa : IsSemiformula language (k+1) a := by simpa only [IsSemiformula.exs] using hscope
      obtain ⟨hsa',hopen⟩ := ih (k+1) hk1 hA hsa
      rw [bindFormula_exs ha]
      constructor
      · exact IsSemiformula.exs.mpr (by simpa only [add_assoc] using hsa')
      · rw [openingFormula_ex K s k _ hs hl hka hsa'.isUFormula,hopen]
  have h0 := hall p hp.isUFormula 0 (show (0 : M) ≤ K from zero_le) (by simp [K]) hp
  have hs0 := sourceQVec_trace_start (?[ ^&(0 : M)] : M) s hs
  constructor
  · simpa only [zero_add] using h0.1
  · simpa only [openingFormula,hs0,LO.FirstOrder.Arithmetic.Bootstrapping.free,substs1] using h0.2

#print axioms bindFormula_scope_open
end PA194PAeq.OpeningQVec
