import PA194TargetGeneralize
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194TargetReplay
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194PathIterator PA194TermShiftCodeModel PA194CloseVariable PA194TargetCantor PA194TargetLeaves
 PA194TargetStep PA194TargetSound PA194TargetExtendedStep PA194ParamHistory PA194StackCode PA194StackHistory
 PA194TargetGuardedHistory PA194TargetVectorLength PA194TargetProofLeaf PA194TargetGeneralize
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

def AgreeAccepted (n old new : M) : Prop :=
  ∀ i < n, F lookup ![i,old] ≠ 0 → F lookup ![i,new] = F lookup ![i,old]

theorem gen_replay (n n' old new label offset result : M)
    (hn : n ≤ n') (ha : AgreeAccepted n old new)
    (h : F step ![n,old,pair 1 (pair label offset)] = result+1) :
    F step ![n',new,pair 1 (pair label offset)] = result+1 := by
  rw [gen_step] at h ⊢
  by_cases ho : offset < n
  · rw [if_pos ho] at h
    have ho' : offset < n' := lt_of_lt_of_le ho hn
    rw [if_pos ho']
    have hnon : F lookup ![offset,old] ≠ 0 := by
      intro hz
      rw [PA194TargetGen.check_model,hz,if_pos rfl] at h
      exact zero_ne_add_one result h
    rw [ha offset ho hnon]
    exact h
  · rw [if_neg ho] at h
    exact False.elim (zero_ne_add_one result h)

theorem mp_replay (n n' old new result conclusion minor major : M)
    (hn : n ≤ n') (ha : AgreeAccepted n old new)
    (h : F step ![n,old,pair 2 (pair conclusion (pair minor major))] = result+1) :
    F step ![n',new,pair 2 (pair conclusion (pair minor major))] = result+1 := by
  rw [mp_step] at h ⊢
  by_cases hm : minor < n
  · rw [if_pos hm] at h
    by_cases hM : major < n
    · rw [if_pos hM] at h
      rw [if_pos (lt_of_lt_of_le hm hn),if_pos (lt_of_lt_of_le hM hn)]
      have hmn : F lookup ![minor,old] ≠ 0 := by
        intro hz
        rw [PA194TargetMP.check_model,hz,if_pos rfl] at h
        exact zero_ne_add_one result h
      have hMn : F lookup ![major,old] ≠ 0 := by
        intro hz
        rw [PA194TargetMP.check_model,if_neg hmn,hz,if_pos rfl] at h
        exact zero_ne_add_one result h
      rw [ha minor hm hmn,ha major hM hMn]
      exact h
    · rw [if_neg hM] at h
      exact False.elim (zero_ne_add_one result h)
  · rw [if_neg hm] at h
    exact False.elim (zero_ne_add_one result h)

theorem step_replay (n n' old new line result : M)
    (hn : n ≤ n') (ha : AgreeAccepted n old new)
    (h : F step ![n,old,line] = result+1) : F step ![n',new,line] = result+1 := by
  obtain ⟨t,p,hl⟩ : ∃ t p, line = pair t p := ⟨π₁ line, π₂ line, (pair_unpair line).symm⟩
  rw [hl] at h ⊢
  by_cases ht0 : t = 0
  · subst t
    rw [← pair_unpair p,leaf_step] at h ⊢
    exact h
  · by_cases ht1 : t = 1
    · subst t
      rw [← pair_unpair p] at h ⊢
      exact gen_replay n n' old new _ _ result hn ha h
    · by_cases ht2 : t = 2
      · subst t
        rw [← pair_unpair p,← pair_unpair (π₂ p)] at h ⊢
        exact mp_replay n n' old new result _ _ _ hn ha h
      · have hz := other_sound (fun _ => False) n old t p ht0 ht1 ht2
        rcases hz with hz | hz
        · rw [hz] at h
          exact False.elim (zero_ne_add_one result h)
        · exact False.elim hz

theorem extended_replay (n n' old new line result : M)
    (hn : n ≤ n') (ha : AgreeAccepted n old new)
    (h : F extended ![n,old,line] = result+1) : F extended ![n',new,line] = result+1 := by
  obtain ⟨t,p,hl⟩ : ∃ t p, line = pair t p := ⟨π₁ line, π₂ line, (pair_unpair line).symm⟩
  obtain ⟨a,p2,hp⟩ : ∃ a p2, p = pair a p2 := ⟨π₁ p, π₂ p, (pair_unpair p).symm⟩
  obtain ⟨b,p3,hp2⟩ : ∃ b p3, p2 = pair b p3 := ⟨π₁ p2, π₂ p2, (pair_unpair p2).symm⟩
  obtain ⟨c,u,hp3⟩ : ∃ c u, p3 = pair c u := ⟨π₁ p3, π₂ p3, (pair_unpair p3).symm⟩
  rw [hl,hp,hp2,hp3] at h ⊢
  by_cases ht3 : t = 3
  · subst t
    rw [tag3] at h ⊢
    exact h
  · by_cases ht4 : t = 4
    · subst t
      rw [tag4] at h ⊢
      exact h
    · by_cases ht5 : t = 5
      · subst t
        rw [tag5] at h ⊢
        exact h
      · by_cases ht6 : t = 6
        · subst t
          rw [tag6] at h ⊢
          exact h
        · by_cases ht7 : t = 7
          · subst t
            rw [tag7] at h ⊢
            exact h
          · by_cases ht8 : t = 8
            · subst t
              rw [tag8] at h ⊢
              exact h
            · by_cases ht9 : t = 9
              · subst t
                rw [tag9] at h ⊢
                exact h
              · by_cases ht10 : t = 10
                · subst t
                  rw [tag10] at h ⊢
                  exact h
                · rw [fallback n old t _ ht3 ht4 ht5 ht6 ht7 ht8 ht9 ht10] at h
                  rw [fallback n' new t _ ht3 ht4 ht5 ht6 ht7 ht8 ht9 ht10]
                  exact step_replay n n' old new _ result hn ha h

#print axioms step_replay
#print axioms extended_replay
#print axioms gen_replay
#print axioms mp_replay
end models
end PA194TargetReplay
