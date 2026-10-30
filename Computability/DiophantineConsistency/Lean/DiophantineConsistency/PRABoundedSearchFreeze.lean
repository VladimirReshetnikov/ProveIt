import DiophantineConsistency.PRABoundedSearchBound

/-! Once bounded search finds a bad value, its result remains fixed. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRABoundedSearchFreeze
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAAddition PRAOpenInduction
  PRASelectCode PRABoundedSearchCode PRABoundedSearchInvariant

private def parameters (n : ℕ) : Fin n → Semiterm language ℕ 1 := fun i => .fvar i.val
private def startTerm (n : ℕ) : Semiterm language ℕ 1 := .fvar n
private def currentTerm {n : ℕ} (good : Code (n+1)) : Semiterm language ℕ 1 :=
  .func (searchCode good) (Fin.cases (.func addCode ![startTerm n, .bvar 0]) (parameters n))
private def initialTerm {n : ℕ} (good : Code (n+1)) : Semiterm language ℕ 1 :=
  .func (searchCode good) (Fin.cases (startTerm n) (parameters n))
private def freezeBody {n : ℕ} (good : Code (n+1)) : Semiformula language ℕ 1 :=
  Semiformula.rel Language.ORing.Rel.eq ![currentTerm good, initialTerm good]

theorem freezeBody_open {n : ℕ} (good : Code (n+1)) : (freezeBody good).Open := by
  simp [freezeBody, Semiformula.Open]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

omit [Nonempty M] [M↓[language] ⊧* PRA] in
private theorem freezeBody_eval {n : ℕ} (good : Code (n+1)) (x : M) (e : ℕ → M) :
    (freezeBody good).Eval ![x] e ↔
      Structure.func (L := language) (searchCode good)
        (Fin.cases (Structure.func (L := language) addCode ![e n,x]) (fun i : Fin n => e i.val)) =
      Structure.func (L := language) (searchCode good) (Fin.cases (e n) (fun i : Fin n => e i.val)) := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] (freezeBody good) ↔ _
  dsimp only [freezeBody, Semiformula.EvalAux]
  rw [eqRel]
  have hc : (Semiterm.val ![x] e ∘ Fin.cases (.func addCode ![startTerm n, .bvar 0]) (parameters n)) =
      Fin.cases (Structure.func (L := language) addCode ![e n,x]) (fun i : Fin n => e i.val) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [startTerm, Semiterm.val_func]
    · rfl
  have hi : (Semiterm.val ![x] e ∘ Fin.cases (startTerm n) (parameters n)) =
      Fin.cases (e n) (fun i : Fin n => e i.val) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  simp [currentTerm, initialTerm, Semiterm.val_func, hc, hi]

theorem modelSearchStepBad {n : ℕ} (good : Code (n+1)) (x : M) (e : ℕ → M)
    (hbad : Structure.func (L := language) good
      (Fin.cases (Structure.func (L := language) (searchCode good)
        (Fin.cases x (fun i : Fin n => e i.val))) (fun i : Fin n => e i.val)) =
      Structure.func (L := language) (Code.zero 0) Fin.elim0) :
    Structure.func (L := language) (searchCode good)
      (Fin.cases (Structure.func (L := language) Code.succ (fun _ => x)) (fun i : Fin n => e i.val)) =
    Structure.func (L := language) (searchCode good) (Fin.cases x (fun i : Fin n => e i.val)) := by
  exact (modelSearchStepCases good x (fun i => e i.val)).1 hbad

theorem modelSearchFreeze {n : ℕ} (good : Code (n+1)) (start shift : M) (e : ℕ → M)
    (hbad : Structure.func (L := language) good
      (Fin.cases (Structure.func (L := language) (searchCode good)
        (Fin.cases start (fun i : Fin n => e i.val))) (fun i : Fin n => e i.val)) =
      Structure.func (L := language) (Code.zero 0) Fin.elim0) :
    Structure.func (L := language) (searchCode good)
      (Fin.cases (Structure.func (L := language) addCode ![start,shift]) (fun i : Fin n => e i.val)) =
    Structure.func (L := language) (searchCode good) (Fin.cases start (fun i : Fin n => e i.val)) := by
  let z : M := Structure.func (L := language) (Code.zero 0) Fin.elim0
  let s : M → M := fun x => Structure.func (L := language) Code.succ (fun _ => x)
  let params : Fin n → M := fun i => e i.val
  let e' : ℕ → M := fun i => if h : i < n then e i else start
  let find : M → M := fun x => Structure.func (L := language) (searchCode good) (Fin.cases x params)
  let g : M → M := fun x => Structure.func (L := language) good (Fin.cases x params)
  have hp : (fun i : Fin n => e' i.val) = params := by funext i; simp [e', params, i.isLt]
  have he : e' n = start := by simp [e']
  have hall : (freezeBody good).Eval ![shift] e' := by
    apply modelOpenInduction (M := M) (freezeBody good) (freezeBody_open good) e'
    · apply (freezeBody_eval good z e').mpr
      rw [he,hp]
      change find (Structure.func (L := language) addCode ![start,z]) = find start
      rw [modelAddZero]
    · intro t ht
      apply (freezeBody_eval good (s t) e').mpr
      rw [he,hp]
      change find (Structure.func (L := language) addCode ![start,s t]) = find start
      rw [modelAddSucc]
      have hi := (freezeBody_eval good t e').mp ht
      rw [he,hp] at hi
      change find (Structure.func (L := language) addCode ![start,t]) = find start at hi
      have hb : g (find (Structure.func (L := language) addCode ![start,t])) = z := by
        rw [hi]
        exact hbad
      have hn := modelSearchStepBad good (Structure.func (L := language) addCode ![start,t]) e hb
      exact hn.trans hi
  have hc := (freezeBody_eval good shift e').mp hall
  rw [he,hp] at hc
  exact hc

end models
end DiophantineConsistency.PRABoundedSearchFreeze
