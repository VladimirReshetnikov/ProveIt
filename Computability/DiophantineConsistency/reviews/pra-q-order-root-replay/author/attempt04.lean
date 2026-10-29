import DiophantineConsistency.PRASubReconstruct
import DiophantineConsistency.PRANonzeroCharacter
import DiophantineConsistency.PRAQCompatibility

/-! The ordered-ring Robinson Q order clause in candidate PRA. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAQOrder
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAAddition PRAExhaustion
  PRAAdditionCommutativity PRASubAddition PRASubReconstruct PRANonzeroCharacter PRAQCompatibility

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelLtBit (x y : M) :
    Structure.func (L := language) ltBitCode ![x,y] =
      Structure.func (L := language) nonzeroCode
        (fun _ => Structure.func (L := language) subCode ![y,x]) := by
  have h := modelComposition (M := M) nonzeroCode
    (.cons (.comp subCode (.cons (.proj 1) (.cons (.proj 0) (.nil 2)))) (.nil 2)) ![x,y]
  have hs := modelSwapComposition (M := M) subCode x y
  have ha : (fun i => Structure.func (L := language)
      (getCode (.cons (.comp subCode (.cons (.proj 1) (.cons (.proj 0) (.nil 2)))) (.nil 2)) i) ![x,y]) =
      fun _ => Structure.func (L := language) subCode ![y,x] := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    exact hs
  change Structure.func (L := language) ltBitCode ![x,y] = _ at h
  rw [ha] at h
  exact h

theorem modelLtBitDefinition (x y : M) :
    Structure.rel (L := language) Language.ORing.Rel.lt ![x,y] ↔
    Structure.func (L := language) ltBitCode ![x,y] =
      Structure.func (L := language) oneCode Fin.elim0 := by
  have h := Theory.models (T := PRA) M (Or.inr BasicAxiom.orderDefinition)
  simp only [models_iff, orderDefinition, Semiformula.eval_allClosure, LogicalConnective.iff] at h
  have h := h ![x,y]
  change Semiformula.EvalAux (inferInstance : Structure language M) Empty.elim ![x,y] _ at h
  simp [Semiformula.EvalAux, Semiformula.neg, eqRel, applyCode, Function.comp_def] at h
  have hz : (fun i : Fin 0 => Semiterm.val ![x,y] Empty.elim (Fin.elim0 i : TermN 2)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [hz] at h
  have hv : (fun i : Fin 2 => Semiterm.val ![x,y] Empty.elim (![.bvar 0, .bvar 1] i : TermN 2)) = ![x,y] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [hv] at h
  tauto

theorem modelLtDifference (x y : M) :
    Structure.rel (L := language) Language.ORing.Rel.lt ![x,y] ↔
    Structure.func (L := language) subCode ![y,x] ≠
      Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
  rw [modelLtBitDefinition, modelLtBit, modelNonzeroCharacter]

theorem modelLtWitness (x y : M) :
    Structure.rel (L := language) Language.ORing.Rel.lt ![x,y] ↔
      ∃ c, Structure.func (L := language) addCode
        ![x, Structure.func (L := language) Code.succ (fun _ => c)] = y := by
  rw [modelLtDifference]
  constructor
  · intro hn
    have hr := (modelReconstruct x y).resolve_left hn
    have hex := modelExhaustion (M := M)
    simp only [models_iff, exhaustionSentence, Semiformula.eval_univCl, Semiformula.eval_all] at hex
    let d := Structure.func (L := language) subCode ![y,x]
    have h := (body_eval d (fun _ => y)).mp (hex (fun _ => y) d)
    have hs := h.resolve_left hn
    refine ⟨Structure.func (L := language) predCode (fun _ => d), ?_⟩
    rw [hs]
    exact hr
  · rintro ⟨c, hc⟩
    rw [←hc, modelSubAdd]
    exact modelSuccNeZero c

local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

omit [Nonempty M] [M↓[language] ⊧* PRA] in
private theorem reduct_eq :
    (inferInstance : Structure language M).lMap embedding = Arithmetic.standardModel M := by
  apply Structure.ext
  · funext k f v
    cases f with
    | zero =>
      have hv : v = Fin.elim0 := Subsingleton.elim _ _
      rw [hv]
      rfl
    | one =>
      have hv : v = Fin.elim0 := Subsingleton.elim _ _
      rw [hv]
      rfl
    | add =>
      rw [Matrix.fun_eq_vec_two v]
      rfl
    | mul =>
      rw [Matrix.fun_eq_vec_two v]
      rfl
  · funext k r v
    cases r with
    | eq =>
      apply propext
      change Structure.rel (L := language) Language.Eq.eq v ↔ v 0 = v 1
      exact Structure.eq_lang
    | lt =>
      rw [Matrix.fun_eq_vec_two v]
      rfl

theorem model_qLtDef : M↓[language] ⊧ Semiformula.lMap embedding qLtDef := by
  have h : Semiformula.Eval (s := Arithmetic.standardModel M) ![] Empty.elim qLtDef := by
    simp [qLtDef]
    intro x y
    have hh := modelLtWitness x y
    trace_state
    sorry
  simp only [models_iff, Semiformula.eval_lMap]
  change Semiformula.Eval (s := (inferInstance : Structure language M).lMap embedding) ![] Empty.elim qLtDef
  rw [reduct_eq]
  exact h

end models
end DiophantineConsistency.PRAQOrder
