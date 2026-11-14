import PA194TargetRho8
import PA194TargetSound
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194TargetExtendedStep
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194PathIterator PA194TermShiftCodeModel PA194CloseVariable PA194NumeralCode PA194TargetCantor
 PA194TargetLeaves PA194TargetGate PA194TargetRho8 PA194TargetStep PA194TargetSound
 PA194BranchSeed PA194StackCode PA194StackHistory PA194ParamHistory

def app4 {n : Nat} (f : Code 4) (a b c d : Code n) : Code n :=
  .comp f (.cons a (.cons b (.cons c (.cons d (.nil n)))))
noncomputable def arg3 : Code 3 := unary firstProjection z
noncomputable def arg4 : Code 3 := unary secondProjection z
noncomputable def h2 : Code 3 := unary .succ (app3 head2 PA194TargetStep.x PA194TargetStep.y arg3)
noncomputable def h3 : Code 3 := unary .succ (app3 head3 PA194TargetStep.x PA194TargetStep.y arg3)
noncomputable def h4 : Code 3 := unary .succ (app3 head4 PA194TargetStep.x PA194TargetStep.y arg3)
noncomputable def h5 : Code 3 := unary .succ (bin head5 PA194TargetStep.x PA194TargetStep.y)
noncomputable def h6 : Code 3 := unary .succ (app3 head6 PA194TargetStep.x PA194TargetStep.y arg3)
noncomputable def h8 : Code 3 := app4 checkRho8 PA194TargetStep.x PA194TargetStep.y arg3 arg4
noncomputable def hGate : Code 3 := app3 checkGate PA194TargetStep.x PA194TargetStep.y arg3
noncomputable def hDiag : Code 3 := unary .succ (unary diagonal PA194TargetStep.x)
/-- Tags 3–10 append the missing leaves; other tags use the prior partial step. -/
noncomputable def extended : Code 3 :=
  selectAmong (bin equalityCode lineTag (numeralCode 3 3)) h2
  (selectAmong (bin equalityCode lineTag (numeralCode 3 4)) h3
  (selectAmong (bin equalityCode lineTag (numeralCode 3 5)) h4
  (selectAmong (bin equalityCode lineTag (numeralCode 3 6)) h5
  (selectAmong (bin equalityCode lineTag (numeralCode 3 7)) h6
  (selectAmong (bin equalityCode lineTag (numeralCode 3 8)) h8
  (selectAmong (bin equalityCode lineTag (numeralCode 3 9)) hGate
  (selectAmong (bin equalityCode lineTag (numeralCode 3 10)) hDiag step)))))))

noncomputable def nextExtended : Code 4 := app3 extended (.proj 0) (.proj 1) (bin lookup (.proj 0) (.proj 2))
noncomputable def historyExtended : Code 3 := PA194ParamHistory.historyCode nextExtended

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun a b => F addCode ![a,b]⟩
local instance : Mul M := ⟨fun a b => F mulCode ![a,b]⟩
local instance : LT M := ⟨fun a b => Structure.rel (L := language) Language.ORing.Rel.lt ![a,b]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem app4_model {n : Nat} (f : Code 4) (a b c d : Code n) (e : Fin n → M) :
    F (app4 f a b c d) e = F f ![F a e,F b e,F c e,F d e] := by
  rw [app4,modelComposition]
  congr 1
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.cases rfl (fun k => ?_) j
  refine Fin.cases rfl (fun l => ?_) k
  exact Fin.cases rfl (fun t => Fin.elim0 t) l

theorem args (n hist tag a b c u : M) :
    let e := ![n,hist,pair tag (pair a (pair b (pair c u)))]
    F lineTag e = tag ∧ F PA194TargetStep.x e = a ∧ F PA194TargetStep.y e = b ∧ F arg3 e = c ∧ F arg4 e = u := by
  simp only [lineTag,linePayload,PA194TargetStep.x,PA194TargetStep.y,z,tail,arg3,arg4,modelUnary,modelProjection,
    modelPi1Code firstProjection firstProjection_certified,
    modelPi2Code secondProjection secondProjection_certified,pi₁_pair,pi₂_pair]
  simp

theorem tag3 (n hist a b c u : M) :
    F extended ![n,hist,pair 3 (pair a (pair b (pair c u)))] = head2Value a b c + 1 := by
  have hf := args n hist 3 a b c u
  simp only [extended,modelChooseEqual,hf.1,modelNumeralCode]
  norm_num
  rw [h2,modelUnary,modelSucc,app3_model,hf.2.1,hf.2.2.1,hf.2.2.2.1,head2_model]

theorem tag4 (n hist a b c u : M) :
    F extended ![n,hist,pair 4 (pair a (pair b (pair c u)))] = head3Value a b c + 1 := by
  have hf := args n hist 4 a b c u
  simp only [extended,modelChooseEqual,hf.1,modelNumeralCode]
  norm_num
  rw [h3,modelUnary,modelSucc,app3_model,hf.2.1,hf.2.2.1,hf.2.2.2.1,head3_model]

theorem tag5 (n hist a b c u : M) :
    F extended ![n,hist,pair 5 (pair a (pair b (pair c u)))] = head4Value a b c + 1 := by
  have hf := args n hist 5 a b c u
  simp only [extended,modelChooseEqual,hf.1,modelNumeralCode]
  norm_num
  rw [h4,modelUnary,modelSucc,app3_model,hf.2.1,hf.2.2.1,hf.2.2.2.1,head4_model]

theorem tag6 (n hist a b c u : M) :
    F extended ![n,hist,pair 6 (pair a (pair b (pair c u)))] = head5Value a b + 1 := by
  have hf := args n hist 6 a b c u
  simp only [extended,modelChooseEqual,hf.1,modelNumeralCode]
  norm_num
  rw [h5,modelUnary,modelSucc,modelBin,hf.2.1,hf.2.2.1,head5_model]

theorem tag7 (n hist a b c u : M) :
    F extended ![n,hist,pair 7 (pair a (pair b (pair c u)))] = head6Value a b c + 1 := by
  have hf := args n hist 7 a b c u
  simp only [extended,modelChooseEqual,hf.1,modelNumeralCode]
  norm_num
  rw [h6,modelUnary,modelSucc,app3_model,hf.2.1,hf.2.2.1,hf.2.2.2.1,head6_model]

theorem tag8 (n hist a b c u : M) :
    F extended ![n,hist,pair 8 (pair a (pair b (pair c u)))] =
      if a < u then 0 else rho8Value a b c u + 1 := by
  have hf := args n hist 8 a b c u
  simp only [extended,modelChooseEqual,hf.1,modelNumeralCode]
  norm_num
  rw [h8,app4_model,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2,checkRho8_model]

theorem tag9 (n hist a b c u : M) :
    F extended ![n,hist,pair 9 (pair a (pair b (pair c u)))] =
      if c = a then 0 else if c = b then 0 else oldBundleValue a b c + 1 := by
  have hf := args n hist 9 a b c u
  simp only [extended,modelChooseEqual,hf.1,modelNumeralCode]
  norm_num
  rw [hGate,app3_model,hf.2.1,hf.2.2.1,hf.2.2.2.1,checkGate_model]

theorem tag10 (n hist a b c u : M) :
    F extended ![n,hist,pair 10 (pair a (pair b (pair c u)))] = diagonalValue a + 1 := by
  have hf := args n hist 10 a b c u
  simp only [extended,modelChooseEqual,hf.1,modelNumeralCode]
  norm_num
  rw [hDiag,modelUnary,modelSucc,modelUnary,hf.2.1]
  have hv : (fun _ : Fin 1 => a) = ![a] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [hv,diagonal_model]

theorem fallback (n hist t payload : M)
    (h3 : t ≠ 3) (h4 : t ≠ 4) (h5 : t ≠ 5) (h6 : t ≠ 6)
    (h7 : t ≠ 7) (h8 : t ≠ 8) (h9 : t ≠ 9) (h10 : t ≠ 10) :
    F extended ![n,hist,pair t payload] = F step ![n,hist,pair t payload] := by
  have hf := fields n hist t payload
  simp only [extended,modelChooseEqual,hf.1,modelNumeralCode]
  norm_num at *
  simp only [h3,h4,h5,h6,h7,h8,h9,h10,if_false]

structure LeafClosure (G : M → Prop) : Prop where
  head2 : ∀ a b c, G (head2Value a b c)
  head3 : ∀ a b c, G (head3Value a b c)
  head4 : ∀ a b c, G (head4Value a b c)
  head5 : ∀ a b, G (head5Value a b)
  head6 : ∀ a b c, G (head6Value a b c)
  rho8 : ∀ a b c u, u ≤ a → G (rho8Value a b c u)
  gate : ∀ a b c, c ≠ a → c ≠ b → G (oldBundleValue a b c)
  diagonal : ∀ a, G (diagonalValue a)

theorem extended_sound (G : M → Prop)
    (hLeaf : ∀ a b, G (F machineHead1 ![a,b]))
    (hGen : ∀ label a, G a → G (allValue label a))
    (hMP : ∀ a b, G a → G (impValue a b) → G b)
    (hNew : LeafClosure G)
    (n hist line : M) (hh : GoodHistory G n hist) : GoodValue G (F extended ![n,hist,line]) := by
  obtain ⟨t,p,hl⟩ : ∃ t p, line = pair t p := ⟨π₁ line, π₂ line, (pair_unpair line).symm⟩
  obtain ⟨a,p2,hp⟩ : ∃ a p2, p = pair a p2 := ⟨π₁ p, π₂ p, (pair_unpair p).symm⟩
  obtain ⟨b,p3,hp2⟩ : ∃ b p3, p2 = pair b p3 := ⟨π₁ p2, π₂ p2, (pair_unpair p2).symm⟩
  obtain ⟨c,u,hp3⟩ : ∃ c u, p3 = pair c u := ⟨π₁ p3, π₂ p3, (pair_unpair p3).symm⟩
  rw [hl,hp,hp2,hp3]
  by_cases ht3 : t = 3
  · rw [ht3,tag3]
    exact (good_value_accepted G _).mpr (hNew.head2 a b c)
  · by_cases ht4 : t = 4
    · rw [ht4,tag4]
      exact (good_value_accepted G _).mpr (hNew.head3 a b c)
    · by_cases ht5 : t = 5
      · rw [ht5,tag5]
        exact (good_value_accepted G _).mpr (hNew.head4 a b c)
      · by_cases ht6 : t = 6
        · rw [ht6,tag6]
          exact (good_value_accepted G _).mpr (hNew.head5 a b)
        · by_cases ht7 : t = 7
          · rw [ht7,tag7]
            exact (good_value_accepted G _).mpr (hNew.head6 a b c)
          · by_cases ht8 : t = 8
            · rw [ht8,tag8]
              by_cases guard : a < u
              · rw [if_pos guard]; exact Or.inl rfl
              · rw [if_neg guard]
                exact (good_value_accepted G _).mpr (hNew.rho8 a b c u (le_of_not_gt guard))
            · by_cases ht9 : t = 9
              · rw [ht9,tag9]
                by_cases ha : c = a
                · rw [if_pos ha]; exact Or.inl rfl
                · rw [if_neg ha]
                  by_cases hb : c = b
                  · rw [if_pos hb]; exact Or.inl rfl
                  · rw [if_neg hb]
                    exact (good_value_accepted G _).mpr (hNew.gate a b c ha hb)
              · by_cases ht10 : t = 10
                · rw [ht10,tag10]
                  exact (good_value_accepted G _).mpr (hNew.diagonal a)
                · rw [fallback n hist t _ ht3 ht4 ht5 ht6 ht7 ht8 ht9 ht10]
                  exact PA194TargetSound.step_sound G hLeaf hGen hMP n hist _ hh

theorem next_model (n hist program spare : M) :
    F nextExtended ![n,hist,program,spare] = F extended ![n,hist,program.[n]] := by
  rw [nextExtended,app3_model,modelProjection,modelProjection,modelBin,modelProjection,modelProjection]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  change F extended ![n,hist,F lookup ![n,program]] = _
  have h : F lookup ![n,program] = program.[n] := PA194SearchVector.lookup_nth n program
  rw [h]

theorem history_base (program spare : M) : F historyExtended ![0,program,spare] = 0 :=
  PA194ParamHistory.modelBase nextExtended program spare

theorem history_step (n program spare : M) :
    F historyExtended ![n+1,program,spare] =
      pair (F extended ![n,F historyExtended ![n,program,spare],program.[n]])
        (F historyExtended ![n,program,spare])+1 := by
  rw [historyExtended,PA194ParamHistory.modelStep,next_model]

theorem history_newest (n program spare : M) :
    F lookup ![0,F historyExtended ![n+1,program,spare]] =
      F extended ![n,F historyExtended ![n,program,spare],program.[n]] := by
  rw [history_step]
  exact modelLookupZero firstProjection secondProjection firstProjection_certified _ _

theorem history_earlier (n i program spare : M) :
    F lookup ![i+1,F historyExtended ![n+1,program,spare]] =
      F lookup ![i,F historyExtended ![n,program,spare]] := by
  rw [history_step]
  exact modelLookupConsSucc firstProjection secondProjection secondProjection_certified _ _ _

theorem history_sound (G : M → Prop) (hG : 𝚺₁-Predicate G)
    (hLeaf : ∀ a b, G (F machineHead1 ![a,b]))
    (hGen : ∀ label a, G a → G (allValue label a))
    (hMP : ∀ a b, G a → G (impValue a b) → G b)
    (hNew : LeafClosure G)
    (program spare n : M) : GoodHistory G n (F historyExtended ![n,program,spare]) := by
  have hf : 𝚺₁-Function₁ (fun n : M => F historyExtended ![n,program,spare]) :=
    PA194CodeInstance.unary_of_three historyExtended program spare
  have hdef := relation_substitution_def (GoodHistory G) _ (goodHistory_definable G hG) hf
  induction n using ISigma1.sigma1_succ_induction with
  | hP => exact hdef
  | zero =>
    intro i hi
    exact False.elim (not_lt_zero hi)
  | succ n ih =>
    intro i hi
    rcases zero_or_succ i with rfl | ⟨j,rfl⟩
    · rw [history_newest]
      exact extended_sound G hLeaf hGen hMP hNew n _ _ ih
    · rw [history_earlier]
      apply ih j
      exact (add_lt_add_iff_right 1).mp hi

theorem accepted_sound (G : M → Prop) (hG : 𝚺₁-Predicate G)
    (hLeaf : ∀ a b, G (F machineHead1 ![a,b]))
    (hGen : ∀ label a, G a → G (allValue label a))
    (hMP : ∀ a b, G a → G (impValue a b) → G b)
    (hNew : LeafClosure G)
    (program spare n i v : M) (hi : i < n)
    (hv : F lookup ![i,F historyExtended ![n,program,spare]] = v+1) : G v := by
  have h := history_sound G hG hLeaf hGen hMP hNew program spare n i hi
  rw [hv] at h
  exact (good_value_accepted G v).mp h

#print axioms history_sound
#print axioms accepted_sound

#print axioms extended_sound

#print axioms tag3
#print axioms tag4
#print axioms tag5
#print axioms tag6
#print axioms tag7
#print axioms tag8
#print axioms tag9
#print axioms tag10
#print axioms fallback
end models
end PA194TargetExtendedStep
