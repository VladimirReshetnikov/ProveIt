import PA194TargetStep
import PA194CodeInstance
/-! Internal induction for the partial target proof history. The three
closure hypotheses are explicit; this is not a full target soundness theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194TargetSound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194NumeralCode PA194CloseVariable PA194TargetCantor
 PA194StackCode PA194StackHistory PA194ParamHistory PA194TargetStep
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

def GoodValue (G : M → Prop) (v : M) : Prop := v = 0 ∨ G (F predCode (fun _ => v))
def GoodHistory (G : M → Prop) (n h : M) : Prop := ∀ i < n, GoodValue G (F lookup ![i,h])

theorem good_value_accepted (G : M → Prop) (a : M) : GoodValue G (a+1) ↔ G a := by
  unfold GoodValue
  rw [modelPredAddOne]
  simp

theorem goodHistory_def (G : M → Prop) (f : M → M → M) (pred : M → M)
    (hG : 𝚺₁-Predicate G) (hf : 𝚺₁-Function₂ f) (hp : 𝚺₁-Function₁ pred) :
    𝚺₁-Relation (fun n h => ∀ i < n, f i h = 0 ∨ G (pred (f i h))) := by
  haveI := hG
  haveI := hf
  haveI := hp
  definability

theorem goodHistory_definable (G : M → Prop) (hG : 𝚺₁-Predicate G) :
    𝚺₁-Relation (GoodHistory G) := by
  have hf : 𝚺₁-Function₂ (fun i h : M => F lookup ![i,h]) := by
    have h : 𝚺₁.DefinableFunction (fun v : Fin 2 → M => F lookup v) :=
      HierarchySymbol.Defined.to_definable _ (PA194CodeGraph.modelGraph (M := M) lookup)
    convert h using 1
    funext v
    exact congrArg (fun e : Fin 2 → M => F lookup e) (Matrix.fun_eq_vec_two v).symm
  have hp : 𝚺₁-Function₁ (fun v : M => F predCode (fun _ => v)) := by
    have h : 𝚺₁.DefinableFunction (fun v : Fin 1 → M => F predCode v) :=
      HierarchySymbol.Defined.to_definable _ (PA194CodeGraph.modelGraph (M := M) predCode)
    convert h using 1
    funext v
    change F predCode (fun _ => v 0) = F predCode v
    congr 1
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  exact goodHistory_def G _ _ hG hf hp

theorem leaf_sound (G : M → Prop)
    (hLeaf : ∀ a b, G (F machineHead1 ![a,b])) (n hist a b : M) :
    GoodValue G (F step ![n,hist,pair 0 (pair a b)]) := by
  rw [leaf_step, PA194Head1Checker.check_model]
  simp only [pi₁_pair,pi₂_pair]
  norm_num
  exact (good_value_accepted G _).mpr (hLeaf a b)

theorem gen_sound (G : M → Prop)
    (hGen : ∀ label a, G a → G (allValue label a))
    (n hist label offset : M) (hh : GoodHistory G n hist) :
    GoodValue G (F step ![n,hist,pair 1 (pair label offset)]) := by
  rw [gen_step]
  by_cases ho : offset < n
  · rw [if_pos ho]
    have hv := hh offset ho
    rcases zero_or_succ (F lookup ![offset,hist]) with hz | ⟨a,ha⟩
    · rw [PA194TargetGen.check_model,hz,if_pos rfl]
      exact Or.inl rfl
    · have hg : G a := by
        rw [ha] at hv
        exact (good_value_accepted G a).mp hv
      rw [PA194TargetGen.check_model,ha,if_neg (by simp),modelPredAddOne]
      exact (good_value_accepted G _).mpr (hGen label a hg)
  · rw [if_neg ho]
    exact Or.inl rfl

theorem mp_sound (G : M → Prop)
    (hMP : ∀ a b, G a → G (impValue a b) → G b)
    (n hist b minor major : M) (hh : GoodHistory G n hist) :
    GoodValue G (F step ![n,hist,pair 2 (pair b (pair minor major))]) := by
  rw [mp_step]
  by_cases hm : minor < n
  · rw [if_pos hm]
    by_cases hM : major < n
    · rw [if_pos hM]
      have hminor := hh minor hm
      have hmajor := hh major hM
      rcases zero_or_succ (F lookup ![minor,hist]) with hz | ⟨a,ha⟩
      · rw [PA194TargetMP.check_model,hz,if_pos rfl]
        exact Or.inl rfl
      · have hGa : G a := by rw [ha] at hminor; exact (good_value_accepted G a).mp hminor
        rcases zero_or_succ (F lookup ![major,hist]) with hz | ⟨c,hc⟩
        · rw [PA194TargetMP.check_model,ha,if_neg (by simp),hz,if_pos rfl]
          exact Or.inl rfl
        · have hGc : G c := by rw [hc] at hmajor; exact (good_value_accepted G c).mp hmajor
          rw [PA194TargetMP.check_model,ha,if_neg (by simp),hc,if_neg (by simp),modelPredAddOne]
          by_cases he : c+1 = impValue a b + 1
          · rw [if_pos he]
            have he' : c = impValue a b := add_right_cancel he
            exact (good_value_accepted G b).mpr (hMP a b hGa (he' ▸ hGc))
          · rw [if_neg he]
            exact Or.inl rfl
    · rw [if_neg hM]; exact Or.inl rfl
  · rw [if_neg hm]; exact Or.inl rfl

theorem other_sound (G : M → Prop) (n hist t payload : M)
    (h0 : t ≠ 0) (h1 : t ≠ 1) (h2 : t ≠ 2) :
    GoodValue G (F step ![n,hist,pair t payload]) := by
  have hf := fields n hist t payload
  simp only [step,modelChooseEqual,hf.1,modelNumeralCode]
  norm_num at *
  simp only [h0,h1,h2,if_false,PRAMultiplication.modelZero]
  exact Or.inl rfl

theorem step_sound (G : M → Prop)
    (hLeaf : ∀ a b, G (F machineHead1 ![a,b]))
    (hGen : ∀ label a, G a → G (allValue label a))
    (hMP : ∀ a b, G a → G (impValue a b) → G b)
    (n hist line : M) (hh : GoodHistory G n hist) : GoodValue G (F step ![n,hist,line]) := by
  have hline : line = pair (π₁ line) (π₂ line) := (pair_unpair line).symm
  rw [hline]
  by_cases h0 : π₁ line = 0
  · rw [h0, ← pair_unpair (π₂ line)]
    exact leaf_sound G hLeaf n hist _ _
  · by_cases h1 : π₁ line = 1
    · rw [h1, ← pair_unpair (π₂ line)]
      exact gen_sound G hGen n hist _ _ hh
    · by_cases h2 : π₁ line = 2
      · rw [h2, ← pair_unpair (π₂ line), ← pair_unpair (π₂ (π₂ line))]
        exact mp_sound G hMP n hist _ _ _ hh
      · exact other_sound G n hist _ _ h0 h1 h2

theorem relation_substitution_def (R : M → M → Prop) (f : M → M)
    (hR : 𝚺₁-Relation R) (hf : 𝚺₁-Function₁ f) :
    𝚺₁-Predicate (fun n => R n (f n)) := by
  haveI := hR
  haveI := hf
  definability

theorem history_sound (G : M → Prop) (hG : 𝚺₁-Predicate G)
    (hLeaf : ∀ a b, G (F machineHead1 ![a,b]))
    (hGen : ∀ label a, G a → G (allValue label a))
    (hMP : ∀ a b, G a → G (impValue a b) → G b)
    (program spare n : M) : GoodHistory G n (F history ![n,program,spare]) := by
  have hf : 𝚺₁-Function₁ (fun n : M => F history ![n,program,spare]) :=
    PA194CodeInstance.unary_of_three history program spare
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
      exact step_sound G hLeaf hGen hMP n _ _ ih
    · rw [history_earlier]
      apply ih j
      exact (add_lt_add_iff_right 1).mp hi

theorem accepted_sound (G : M → Prop) (hG : 𝚺₁-Predicate G)
    (hLeaf : ∀ a b, G (F machineHead1 ![a,b]))
    (hGen : ∀ label a, G a → G (allValue label a))
    (hMP : ∀ a b, G a → G (impValue a b) → G b)
    (program spare n i y : M) (hi : i < n)
    (hy : F lookup ![i,F history ![n,program,spare]] = y+1) : G y := by
  have hv := history_sound G hG hLeaf hGen hMP program spare n i hi
  rw [hy] at hv
  exact (good_value_accepted G y).mp hv

#print axioms accepted_sound

#print axioms history_sound

#print axioms step_sound

#print axioms leaf_sound
#print axioms gen_sound
#print axioms mp_sound

#print axioms goodHistory_definable
end models
end PA194TargetSound
