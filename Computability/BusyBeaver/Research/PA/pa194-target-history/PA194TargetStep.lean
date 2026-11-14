import PA194TargetGen
import PA194SearchVector
/-! A partial finite target-proof history interpreter. Only h1, generalization,
and modus ponens are handled; global proof soundness is not yet established. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194TargetStep
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194PathIterator PA194TermShiftCodeModel PA194NumeralCode PA194CloseVariable PA194TargetCantor
 PA194BranchSeed PA194StackCode PA194StackHistory PA194ParamHistory

def app3 {n : Nat} (f : Code 3) (a b c : Code n) : Code n :=
  .comp f (.cons a (.cons b (.cons c (.nil n))))
noncomputable def lineTag : Code 3 := unary firstProjection (.proj 2)
noncomputable def linePayload : Code 3 := unary secondProjection (.proj 2)
noncomputable def x : Code 3 := unary firstProjection linePayload
noncomputable def tail : Code 3 := unary secondProjection linePayload
noncomputable def y : Code 3 := unary firstProjection tail
noncomputable def z : Code 3 := unary secondProjection tail
noncomputable def lookup : Code 2 := lookupCode (stackComponent firstProjection) (stackComponent secondProjection)
noncomputable def previous (offset : Code 3) : Code 3 := bin lookup offset (.proj 1)
noncomputable def leaf : Code 3 := unary PA194Head1Checker.check
  (bin pairCode (numeralCode 3 2) linePayload)
noncomputable def gen : Code 3 :=
  selectAmong (bin ltBitCode tail (.proj 0)) (bin PA194TargetGen.checkGen (previous tail) x) (.zero 3)
noncomputable def mp : Code 3 :=
  selectAmong (bin ltBitCode y (.proj 0))
    (selectAmong (bin ltBitCode z (.proj 0))
      (app3 PA194TargetMP.checkMP (previous y) (previous z) x) (.zero 3)) (.zero 3)
/-- Line is `pair(tag,payload)`: tags 0,1,2 are h1, gen and MP. -/
noncomputable def step : Code 3 :=
  selectAmong (bin equalityCode lineTag (numeralCode 3 0)) leaf
    (selectAmong (bin equalityCode lineTag (numeralCode 3 1)) gen
      (selectAmong (bin equalityCode lineTag (numeralCode 3 2)) mp (.zero 3)))
/-- Stage, reverse history, encoded line vector, and a spare fixed parameter. -/
noncomputable def next : Code 4 := app3 step (.proj 0) (.proj 1) (bin lookup (.proj 0) (.proj 2))
noncomputable def history : Code 3 := PA194ParamHistory.historyCode next

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

theorem app3_model {n : Nat} (f : Code 3) (a b c : Code n) (e : Fin n → M) :
    F (app3 f a b c) e = F f ![F a e,F b e,F c e] := by
  rw [app3,modelComposition]
  congr 1
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.cases rfl (fun k => ?_) j
  exact Fin.cases rfl (fun l => Fin.elim0 l) k

theorem fields (n hist tag0 payload0 : M) :
    let e := ![n,hist,pair tag0 payload0]
    F lineTag e = tag0 ∧ F linePayload e = payload0 := by
  simp only [lineTag,linePayload,modelUnary,modelProjection,
    modelPi1Code firstProjection firstProjection_certified,
    modelPi2Code secondProjection secondProjection_certified,pi₁_pair,pi₂_pair]
  simp

theorem payload_fields (n hist tag0 a b : M) :
    let e := ![n,hist,pair tag0 (pair a b)]
    F x e = a ∧ F tail e = b := by
  simp only [x,tail,linePayload,modelUnary,modelProjection,
    modelPi1Code firstProjection firstProjection_certified,
    modelPi2Code secondProjection secondProjection_certified,pi₁_pair,pi₂_pair]
  simp

theorem payload3_fields (n hist tag0 a b c : M) :
    let e := ![n,hist,pair tag0 (pair a (pair b c))]
    F x e = a ∧ F y e = b ∧ F z e = c := by
  simp only [x,y,z,tail,linePayload,modelUnary,modelProjection,
    modelPi1Code firstProjection firstProjection_certified,
    modelPi2Code secondProjection secondProjection_certified,pi₁_pair,pi₂_pair]
  simp

theorem leaf_step (n hist a b : M) :
    F step ![n,hist,pair 0 (pair a b)] = F PA194Head1Checker.check ![pair 2 (pair a b)] := by
  have hf := fields n hist 0 (pair a b)
  simp only [step,modelChooseEqual,hf.1,modelNumeralCode]
  norm_num
  rw [leaf,modelUnary,modelBin,modelNumeralCode,hf.2,modelPairCode]
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

theorem gen_step (n hist label offset : M) :
    F step ![n,hist,pair 1 (pair label offset)] =
      if offset < n then F PA194TargetGen.checkGen ![F lookup ![offset,hist],label] else 0 := by
  have hf := fields n hist 1 (pair label offset)
  have hp := payload_fields n hist 1 label offset
  simp only [step,modelChooseEqual,hf.1,modelNumeralCode]
  norm_num
  rw [gen,modelChooseLess,hp.2,modelProjection]
  simp only [Matrix.cons_val_zero]
  by_cases h : offset < n
  · rw [if_pos h,if_pos h,modelBin,previous,modelBin,hp.2,hp.1,modelProjection]
    simp only [Matrix.cons_val_one,Matrix.cons_val_zero]
  · rw [if_neg h,if_neg h,PRAMultiplication.modelZero]
    rfl

theorem mp_step (n hist conclusion minor major : M) :
    F step ![n,hist,pair 2 (pair conclusion (pair minor major))] =
      if minor < n then if major < n then
        F PA194TargetMP.checkMP ![F lookup ![minor,hist],F lookup ![major,hist],conclusion]
      else 0 else 0 := by
  have hf := fields n hist 2 (pair conclusion (pair minor major))
  have hp := payload3_fields n hist 2 conclusion minor major
  simp only [step,modelChooseEqual,hf.1,modelNumeralCode]
  norm_num
  rw [mp,modelChooseLess,hp.2.1,modelProjection]
  simp only [Matrix.cons_val_zero]
  by_cases hm : minor < n
  · rw [if_pos hm,if_pos hm,modelChooseLess,hp.2.2,modelProjection]
    simp only [Matrix.cons_val_zero]
    by_cases ha : major < n
    · rw [if_pos ha,if_pos ha,app3_model,previous,previous,modelBin,modelBin,hp.2.1,hp.2.2,hp.1]
      simp only [modelProjection,Matrix.cons_val_one,Matrix.cons_val_zero]
    · rw [if_neg ha,if_neg ha,PRAMultiplication.modelZero]
      rfl
  · rw [if_neg hm,if_neg hm,PRAMultiplication.modelZero]
    rfl

theorem next_model (n hist program spare : M) :
    F next ![n,hist,program,spare] = F step ![n,hist,program.[n]] := by
  rw [next,app3_model,modelProjection,modelProjection,modelBin,modelProjection,modelProjection]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  change F step ![n,hist,F lookup ![n,program]] = _
  have h : F lookup ![n,program] = program.[n] := PA194SearchVector.lookup_nth n program
  rw [h]

theorem history_base (program spare : M) : F history ![0,program,spare] = 0 :=
  PA194ParamHistory.modelBase next program spare

theorem history_step (n program spare : M) :
    F history ![n+1,program,spare] =
      pair (F step ![n,F history ![n,program,spare],program.[n]])
        (F history ![n,program,spare])+1 := by
  rw [history,PA194ParamHistory.modelStep,next_model]

theorem history_newest (n program spare : M) :
    F lookup ![0,F history ![n+1,program,spare]] =
      F step ![n,F history ![n,program,spare],program.[n]] := by
  rw [history_step]
  exact modelLookupZero firstProjection secondProjection firstProjection_certified _ _

theorem history_earlier (n i program spare : M) :
    F lookup ![i+1,F history ![n+1,program,spare]] =
      F lookup ![i,F history ![n,program,spare]] := by
  rw [history_step]
  exact modelLookupConsSucc firstProjection secondProjection secondProjection_certified _ _ _

#print axioms history_newest
#print axioms history_earlier

#print axioms history_base
#print axioms history_step

#print axioms gen_step
#print axioms mp_step

#print axioms leaf_step
end models
end PA194TargetStep
