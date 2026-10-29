import DiophantineConsistency.PRATheory
import Foundation.FirstOrder.Completeness.CounterModel

/-! The designated addition code's successor law in the candidate PRA theory. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAAddOne
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory

instance : 𝗘𝗤 language ⪯ PRA :=
  Entailment.WeakerThan.ofSubset (fun _ h => Or.inl (Or.inl (Or.inl h)))

def addOneSentence : Sentence language :=
  equalClosure (n := 1) (applyCode addCode (Fin.cases (.bvar 0) (fun _ => applyCode oneCode Fin.elim0)))
    (applyCode .succ (fun _ => .bvar 0))

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

omit [Structure.Eq language M] in
theorem modelDefiningEquation {φ : Sentence language} (h : DefiningEquation φ) : M↓[language] ⊧ φ :=
  Theory.models (T := PRA) M (Or.inl (Or.inl (Or.inr h)))

omit [Nonempty M] [M↓[language] ⊧* PRA] in
private theorem eqRel (v : Fin 2 → M) :
    Structure.rel (L := language) Language.ORing.Rel.eq v ↔ v 0 = v 1 := by
  change Structure.rel (L := language) Language.Eq.eq v ↔ _
  exact Structure.eq_lang

theorem modelComposition {m n : ℕ} (f : Code m) (g : Codes n m) (e : Fin n → M) :
    Structure.func (L := language) (Code.comp f g) e =
      Structure.func (L := language) f (fun i => Structure.func (L := language) (getCode g i) e) := by
  have h := modelDefiningEquation (M := M) (DefiningEquation.composition f g)
  simp only [models_iff, compositionEquation, equalClosure, Semiformula.eval_allClosure,
    Semiformula.eval_rel] at h
  have h' := (eqRel _).mp (h e)
  simpa [applyCode, vars, Function.comp_def] using h'


theorem modelProjection {n : ℕ} (i : Fin n) (e : Fin n → M) :
    Structure.func (L := language) (Code.proj i) e = e i := by
  have h := modelDefiningEquation (M := M) (DefiningEquation.projection i)
  simp only [models_iff, projectionEquation, equalClosure, Semiformula.eval_allClosure,
    Semiformula.eval_rel] at h
  have h' := (eqRel _).mp (h e)
  simpa [applyCode, vars, Function.comp_def] using h'

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
private theorem val_cases {n k : ℕ} (a : TermN k) (b : Fin n → TermN k) (e : Fin k → M) :
    (fun i => Semiterm.val e Empty.elim (Fin.cases a b i)) =
      Fin.cases (Semiterm.val e Empty.elim a) (fun i => Semiterm.val e Empty.elim (b i)) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem modelBase {n : ℕ} (f : Code n) (g : Code (n+2)) (e : Fin n → M) :
    Structure.func (L := language) (Code.prec f g)
        (Fin.cases (Structure.func (L := language) (Code.zero 0) Fin.elim0) e) =
      Structure.func (L := language) f e := by
  have h := modelDefiningEquation (M := M) (DefiningEquation.recursionBase f g)
  simp only [models_iff, recursionBaseEquation, equalClosure, Semiformula.eval_allClosure,
    Semiformula.eval_rel] at h
  have h' := (eqRel _).mp (h e)
  have hz : (fun i : Fin 0 => Semiterm.val e Empty.elim (Fin.elim0 i : TermN n)) =
      (Fin.elim0 : Fin 0 → M) := by
    funext i
    exact Fin.elim0 i
  simpa [applyCode, vars, Function.comp_def, val_cases, hz] using h'

theorem modelStep {n : ℕ} (f : Code n) (g : Code (n+2)) (e : Fin (n+1) → M) :
    Structure.func (L := language) (Code.prec f g)
        (Fin.cases (Structure.func (L := language) Code.succ (fun _ => e 0)) (fun i => e i.succ)) =
      Structure.func (L := language) g
        (Fin.cases (e 0) (Fin.cases (Structure.func (L := language) (Code.prec f g) e)
          (fun i => e i.succ))) := by
  have h := modelDefiningEquation (M := M) (DefiningEquation.recursionStep f g)
  simp only [models_iff, recursionStepEquation, equalClosure, Semiformula.eval_allClosure,
    Semiformula.eval_rel] at h
  have h' := (eqRel _).mp (h e)
  have he : Fin.cases (e 0) (fun i => e i.succ) = e := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  simpa [applyCode, Function.comp_def, val_cases, he] using h'

theorem modelAddOne (x : M) :
    Structure.func (L := language) addCode
      ![x, Structure.func (L := language) oneCode Fin.elim0] =
    Structure.func (L := language) Code.succ (fun _ => x) := by
  let z : M := Structure.func (L := language) (Code.zero 0) Fin.elim0
  have hone := modelComposition (M := M) Code.succ (.cons (.zero 0) (.nil 0)) Fin.elim0
  have ha := modelComposition (M := M) addCore (.cons (.proj 1) (.cons (.proj 0) (.nil 2)))
    ![x, Structure.func (L := language) oneCode Fin.elim0]
  have hb := modelBase (M := M) (Code.proj (0 : Fin 1))
    (Code.comp Code.succ (.cons (.proj (1 : Fin 3)) (.nil 3))) ![x]
  have hs := modelStep (M := M) (Code.proj (0 : Fin 1))
    (Code.comp Code.succ (.cons (.proj (1 : Fin 3)) (.nil 3))) ![z, x]
  have hg := modelComposition (M := M) Code.succ (.cons (.proj (1 : Fin 3)) (.nil 3))
    ![z, Structure.func (L := language) addCore ![z, x], x]
  change Structure.func (L := language) oneCode Fin.elim0 =
    Structure.func (L := language) Code.succ (fun _ => z) at hone
  have harg : (fun i => Structure.func (L := language)
      (getCode (.cons (.proj 1) (.cons (.proj 0) (.nil 2))) i)
      ![x, Structure.func (L := language) oneCode Fin.elim0]) =
      ![Structure.func (L := language) oneCode Fin.elim0, x] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact modelProjection (M := M) 1 _
    · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      exact modelProjection (M := M) 0 _
  change Structure.func (L := language) addCode
      ![x, Structure.func (L := language) oneCode Fin.elim0] =
    Structure.func (L := language) addCore _ at ha
  rw [harg] at ha
  change Structure.func (L := language) addCore ![z,x] = x at hb
  change Structure.func (L := language) addCore
      ![Structure.func (L := language) Code.succ (fun _ => z), x] =
    Structure.func (L := language) (Code.comp Code.succ (.cons (.proj (1 : Fin 3)) (.nil 3)))
      ![z, Structure.func (L := language) addCore ![z,x], x] at hs
  rw [hone] at ha
  rw [ha, hs, hg, hb]


end models
end DiophantineConsistency.PRAAddOne
