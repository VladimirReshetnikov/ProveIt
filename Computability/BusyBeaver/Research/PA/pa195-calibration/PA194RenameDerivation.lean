import PA194RenameDerivationCases
/-! Model-uniform bounded IΣ₁ induction proving internal PA derivability
is preserved by the expanded free-label renaming family. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000
namespace PA194RenameDerivation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
open PA194GenericRenameBase PA194GenericRenameAxiom PA194GenericRenameRules PA194RenameShiftCompatibility PA194RenameSubstitution PA194RenameContexts PA194RenameDerivationCases PA194ExpandedRename
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def mapped (k a o e s : M) : M :=
  renameSet expandedGraph packedRen expandedGraph_correct (pair k (pair a (pair o e))) s

def invariant (bound d : M) : Prop := ∀ k < bound+1, ∀ a < bound+1, ∀ o < bound+1, ∀ e < bound+1,
  k+d ≤ bound → o+d ≤ bound → Derivable (𝗣𝗔 : ArithmeticTheory) (mapped k a o e (fstIdx d))

lemma invariant_defined (bound : M) : 𝚺₁-Predicate (invariant bound) := by
  haveI : 𝚺₁-Function₂ (renameSet expandedGraph (packedRen (M := M)) (expandedGraph_correct (M := M))) :=
    (renameSet_defined expandedGraph (packedRen (M := M)) (expandedGraph_correct (M := M))).to_definable
  unfold invariant mapped
  definability

lemma child_bound (k child parent bound : M) (hchild : child < parent) (h : k+parent ≤ bound) :
    k+child ≤ bound := le_trans (add_le_add (le_refl k) (le_of_lt hchild)) h

lemma child_succ_bound (k child parent bound : M) (hchild : child < parent) (h : k+parent ≤ bound) :
    (k+1)+child ≤ bound := by
  apply le_trans _ h
  simpa [add_assoc,add_comm,add_left_comm] using add_le_add (le_refl k) (lt_iff_succ_le.mp hchild)



lemma derivation_rename_bounded (bound d : M) (hd : Bootstrapping.Derivation (𝗣𝗔 : ArithmeticTheory) d) : invariant bound d := by
  apply Derivation.induction1 𝚺 (invariant_defined bound) hd
  · intro s hs φ hφ hn
    unfold invariant
    intro k hk a ha o ho e he hkd hod
    simp only [fstIdx_axL]
    exact axl_rule expandedGraph packedRen expandedGraph_correct _ φ s hs hφ hn
  · intro s hs hmem
    unfold invariant
    intro k hk a ha o ho e he hkd hod
    simp only [fstIdx_verumIntro]
    exact verum_rule expandedGraph packedRen expandedGraph_correct _ s hs hmem
  · intro s hs φ ψ dp dq hmem hdp hdq ihp ihq
    unfold invariant
    intro k hk a ha o ho e he hkd hod
    simp only [fstIdx_andIntro]
    have hparts := IsSemiformula.and.mp (hs (φ ^⋏ ψ) hmem)
    apply and_rule expandedGraph packedRen expandedGraph_correct _ φ ψ s hparts.1.isUFormula hparts.2.isUFormula hmem
    · have h := ihp k hk a ha o ho e he (child_bound _ _ _ _ (dp_lt_andIntro s φ ψ dp dq) hkd)
        (child_bound _ _ _ _ (dp_lt_andIntro s φ ψ dp dq) hod)
      simpa [mapped,hdp.1] using h
    · have h := ihq k hk a ha o ho e he (child_bound _ _ _ _ (dq_lt_andIntro s φ ψ dp dq) hkd)
        (child_bound _ _ _ _ (dq_lt_andIntro s φ ψ dp dq) hod)
      simpa [mapped,hdq.1] using h
  · intro s hs φ ψ dp hmem hdp ih
    unfold invariant
    intro k hk a ha o ho e he hkd hod
    simp only [fstIdx_orIntro]
    have hparts := IsSemiformula.or.mp (hs (φ ^⋎ ψ) hmem)
    apply or_rule expandedGraph packedRen expandedGraph_correct _ φ ψ s hparts.1.isUFormula hparts.2.isUFormula hmem
    have h := ih k hk a ha o ho e he (child_bound _ _ _ _ (d_lt_orIntro s φ ψ dp) hkd)
      (child_bound _ _ _ _ (d_lt_orIntro s φ ψ dp) hod)
    simpa [mapped,hdp.1] using h
  · intro s hs φ dp hmem hdp ih
    unfold invariant
    intro k hk a ha o ho e he hkd hod
    simp only [fstIdx_allIntro]
    have hφ : IsSemiformula ℒₒᵣ 1 φ := by simpa using (IsSemiformula.all.mp (hs (^∀ φ) hmem))
    have hkd' : (k+1)+dp ≤ bound := child_succ_bound k dp (allIntro s φ dp) bound (s_lt_allIntro s φ dp) hkd
    have hk' : k+1 < bound+1 := le_iff_lt_succ.mp (le_trans le_self_add hkd')
    have hod' : o+dp ≤ bound := child_bound o dp (allIntro s φ dp) bound (s_lt_allIntro s φ dp) hod
    have hpre := ih (k+1) hk' a ha o ho e he hkd' hod'
    apply all_rule expandedGraph packedRen expandedGraph_correct (pair (k+1) (pair a (pair o e))) (pair k (pair a (pair o e))) φ s hφ hs hmem
    · simpa [packedRen] using lift_zero k a o e
    · intro x; simpa [packedRen] using lift_succ k a o e x
    · simpa [mapped,hdp.1] using hpre
  · intro s hs φ t dp hmem ht hdp ih
    unfold invariant
    intro k hk a ha o ho e he hkd hod
    simp only [fstIdx_exsIntro]
    have hφ : IsSemiformula ℒₒᵣ 1 φ := by simpa using (IsSemiformula.exs.mp (hs (^∃ φ) hmem))
    apply ex_rule expandedGraph packedRen expandedGraph_correct _ φ t s hφ ht hmem
    have h := ih k hk a ha o ho e he (child_bound _ _ _ _ (d_lt_exsIntro s φ t dp) hkd)
      (child_bound _ _ _ _ (d_lt_exsIntro s φ t dp) hod)
    simpa [mapped,hdp.1] using h
  · intro s hs dp hsub hd ih
    unfold invariant
    intro k hk a ha o ho e he hkd hod
    simp only [fstIdx_wkRule]
    apply wk_rule expandedGraph packedRen expandedGraph_correct _ (fstIdx dp) s hs hsub
    exact ih k hk a ha o ho e he (child_bound _ _ _ _ (d_lt_wkRule s dp) hkd)
      (child_bound _ _ _ _ (d_lt_wkRule s dp) hod)
  · intro s hs dp heq hd ih
    unfold invariant
    intro k hk a ha o ho e he hkd hod
    simp only [fstIdx_shiftRule]
    subst s
    rcases zero_or_succ k with (rfl | ⟨k,rfl⟩)
    · rcases zero_or_succ a with (rfl | ⟨a,rfl⟩)
      · have hod' : (o+1)+dp ≤ bound := child_succ_bound o dp (shiftRule (setShift ℒₒᵣ (fstIdx dp)) dp) bound (d_lt_shiftRule _ _) hod
        have ho' : o+1 < bound+1 := le_iff_lt_succ.mp (le_trans le_self_add hod')
        have hz : (0 : M) < bound+1 := lt_of_le_of_lt zero_le (lt_add_one bound)
        have hkd' : 0+dp ≤ bound := child_bound 0 dp _ bound (d_lt_shiftRule _ _) hkd
        have hpre := ih 0 hz 0 hz (o+1) ho' 0 hz hkd' hod'
        apply shift_rule_noshift expandedGraph packedRen expandedGraph_correct (pair 0 (pair 0 (pair o e))) (pair 0 (pair 0 (pair (o+1) 0))) (fstIdx dp) hd.isFormulaSet
        · intro x; simpa [packedRen] using shift_zero_exception_zero o e x
        · exact hpre
      · have hod' : (o+1)+dp ≤ bound := child_succ_bound o dp (shiftRule (setShift ℒₒᵣ (fstIdx dp)) dp) bound (d_lt_shiftRule _ _) hod
        have ho' : o+1 < bound+1 := le_iff_lt_succ.mp (le_trans le_self_add hod')
        have hz : (0 : M) < bound+1 := lt_of_le_of_lt zero_le (lt_add_one bound)
        have ha' : a < bound+1 := lt_trans (lt_add_one a) ha
        have hkd' : 0+dp ≤ bound := child_bound 0 dp _ bound (d_lt_shiftRule _ _) hkd
        have hpre := ih 0 hz a ha' (o+1) ho' e he hkd' hod'
        apply shift_rule_noshift expandedGraph packedRen expandedGraph_correct (pair 0 (pair (a+1) (pair o e))) (pair 0 (pair a (pair (o+1) e))) (fstIdx dp) hd.isFormulaSet
        · intro x; simpa [packedRen] using shift_zero_exception_succ a o e x
        · exact hpre
    · have hk' : k < bound+1 := lt_trans (lt_add_one k) hk
      have hkd' : k+dp ≤ bound := child_bound k dp _ bound (d_lt_shiftRule _ _) (le_trans (add_le_add (le_of_lt (lt_add_one k)) (le_refl _)) hkd)
      have hod' : o+dp ≤ bound := child_bound o dp _ bound (d_lt_shiftRule _ _) hod
      have hpre := ih k hk' a ha o ho e he hkd' hod'
      apply shift_rule expandedGraph packedRen expandedGraph_correct (pair (k+1) (pair a (pair o e))) (pair k (pair a (pair o e))) (fstIdx dp) hd.isFormulaSet
      · intro x; simpa [packedRen] using lift_succ k a o e x
      · exact hpre
  · intro s hs φ dp dq hdp hdq ihp ihq
    unfold invariant
    intro k hk a ha o ho e he hkd hod
    simp only [fstIdx_cutRule]
    have hφ : IsFormula ℒₒᵣ φ := hdp.isFormulaSet φ (by simp)
    apply cut_rule expandedGraph packedRen expandedGraph_correct _ φ s hφ
    · have h := ihp k hk a ha o ho e he (child_bound _ _ _ _ (d₁_lt_cutRule s φ dp dq) hkd)
        (child_bound _ _ _ _ (d₁_lt_cutRule s φ dp dq) hod)
      simpa [mapped,hdp.1] using h
    · have h := ihq k hk a ha o ho e he (child_bound _ _ _ _ (d₂_lt_cutRule s φ dp dq) hkd)
        (child_bound _ _ _ _ (d₂_lt_cutRule s φ dp dq) hod)
      simpa [mapped,hdq.1] using h
  · intro s hs φ hmem haxiom
    unfold invariant
    intro k hk a ha o ho e he hkd hod
    simp only [fstIdx_axm]
    exact root_rule expandedGraph packedRen expandedGraph_correct _ φ s hs hmem haxiom


theorem derivation_rename (d k a o e : M) (hd : Bootstrapping.Derivation (𝗣𝗔 : ArithmeticTheory) d) :
    Derivable (𝗣𝗔 : ArithmeticTheory) (mapped k a o e (fstIdx d)) := by
  let b : M := (k+d)+(o+d)+a+e
  have hkd : k+d ≤ b := by
    dsimp [b]
    exact le_trans (le_trans le_self_add le_self_add) le_self_add
  have hod : o+d ≤ b := by
    dsimp [b]
    exact le_trans (le_trans le_add_self le_self_add) le_self_add
  have ha : a ≤ b := by
    dsimp [b]
    exact le_trans le_add_self le_self_add
  have he : e ≤ b := by
    dsimp [b]
    exact le_add_self
  have hk : k ≤ b := le_trans le_self_add hkd
  have ho : o ≤ b := le_trans le_self_add hod
  exact derivation_rename_bounded b d hd k (le_iff_lt_succ.mp hk) a (le_iff_lt_succ.mp ha)
    o (le_iff_lt_succ.mp ho) e (le_iff_lt_succ.mp he) hkd hod

theorem derivable_rename (s k a o e : M) (h : Derivable (𝗣𝗔 : ArithmeticTheory) s) :
    Derivable (𝗣𝗔 : ArithmeticTheory) (mapped k a o e s) := by
  obtain ⟨d,hd⟩ := h
  simpa [hd.1] using derivation_rename d k a o e hd.2

#print axioms derivation_rename_bounded
#print axioms derivation_rename
#print axioms derivable_rename


end models
end PA194RenameDerivation
