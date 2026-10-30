import DiophantineConsistency.PRAOpenInduction

/-! Primitive-recursive witnessing along a quantifier-free induction. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAPrimitiveRecursionInduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAOpenInduction

def iterateCode {n : ℕ} (base : Code n) (step : Code (n+2)) : Code (n+1) := .prec base step

theorem iterateCode_primrec {n : ℕ} (base : Code n) (step : Code (n+2)) :
    Primrec (eval (iterateCode base step)) := eval_primrec _

private def params1 (n : ℕ) : Fin n → Semiterm language ℕ 1 := fun i => .fvar i.val
private def recursiveBody {n : ℕ} (pred : Code (n+2)) (base : Code n) (step : Code (n+2)) :
    Semiproposition language 1 :=
  Semiformula.rel Language.ORing.Rel.eq
    ![.func pred (Fin.cases (.bvar 0) (Fin.cases
        (.func (iterateCode base step) (Fin.cases (.bvar 0) (params1 n))) (params1 n))),
      .func oneCode Fin.elim0]

theorem recursiveBody_open {n : ℕ} (pred : Code (n+2)) (base : Code n) (step : Code (n+2)) :
    (recursiveBody pred base step).Open := by simp [recursiveBody, Semiformula.Open]

private def params0 (n : ℕ) : Fin n → Term language ℕ := fun i => .fvar i.val
private def params2 (n : ℕ) : Fin n → Semiterm language ℕ 2 := fun i => .fvar i.val

def baseFormula {n : ℕ} (pred : Code (n+2)) (base : Code n) : Proposition language :=
  Semiformula.rel Language.ORing.Rel.eq
    ![.func pred (Fin.cases (.func (Code.zero 0) Fin.elim0)
      (Fin.cases (.func base (params0 n)) (params0 n))), .func oneCode Fin.elim0]

def stepFormula {n : ℕ} (pred : Code (n+2)) (step : Code (n+2)) : Proposition language :=
  ∀⁰ ∀⁰ ((Semiformula.rel Language.ORing.Rel.eq
    ![.func pred (Fin.cases (.bvar 1) (Fin.cases (.bvar 0) (params2 n))), .func oneCode Fin.elim0]) 🡒
    (Semiformula.rel Language.ORing.Rel.eq
      ![.func pred (Fin.cases (.func Code.succ ![.bvar 1]) (Fin.cases
        (.func step (Fin.cases (.bvar 1) (Fin.cases (.bvar 0) (params2 n)))) (params2 n))), .func oneCode Fin.elim0]))

def recursiveSentence {n : ℕ} (pred : Code (n+2)) (base : Code n) (step : Code (n+2)) : Sentence language :=
  ((baseFormula pred base ⋏ stepFormula pred step) 🡒 (∀⁰ recursiveBody pred base step)).univCl

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

omit [Nonempty M] [M↓[language] ⊧* PRA] in
private theorem recursiveBody_eval {n : ℕ} (pred : Code (n+2)) (base : Code n) (step : Code (n+2))
    (x : M) (e : ℕ → M) : (recursiveBody pred base step).Eval ![x] e ↔
    let params := fun i : Fin n => e i.val
    let iterate := Structure.func (L := language) (iterateCode base step) (Fin.cases x params)
    Structure.func (L := language) pred (Fin.cases x (Fin.cases iterate params)) =
      Structure.func (L := language) oneCode Fin.elim0 := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] (recursiveBody pred base step) ↔ _
  dsimp only [recursiveBody, Semiformula.EvalAux]
  rw [eqRel]
  have hi : (Semiterm.val ![x] e ∘ Fin.cases (.bvar 0) (params1 n)) =
      Fin.cases x (fun i : Fin n => e i.val) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  have hp : (Semiterm.val ![x] e ∘ Fin.cases (.bvar 0) (Fin.cases
      (.func (iterateCode base step) (Fin.cases (.bvar 0) (params1 n))) (params1 n))) =
      Fin.cases x (Fin.cases (Structure.func (L := language) (iterateCode base step)
        (Fin.cases x (fun i : Fin n => e i.val))) (fun i : Fin n => e i.val)) := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases ?_ (fun _ => rfl) j
    change Structure.func (L := language) (iterateCode base step)
      (Semiterm.val ![x] e ∘ Fin.cases (.bvar 0) (params1 n)) = _
    rw [hi]
    rfl
  have hz : (Semiterm.val (L := language) ![x] e ∘ Fin.elim0) = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simp [Semiterm.val_func, hp, hz]

/-- If a PR predicate has a PR base witness and a PR successor update,
open induction proves that its recursively generated witnesses work at every
index, in every candidate-PRA model and for every parameter valuation. -/
theorem modelRecursiveWitness {n : ℕ} (pred : Code (n+2)) (base : Code n) (step : Code (n+2))
    (e : ℕ → M)
    (hbase : Structure.func (L := language) pred (Fin.cases
      (Structure.func (L := language) (Code.zero 0) Fin.elim0)
      (Fin.cases (Structure.func (L := language) base (fun i : Fin n => e i.val)) (fun i => e i.val))) =
      Structure.func (L := language) oneCode Fin.elim0)
    (hstep : ∀ x y, Structure.func (L := language) pred
      (Fin.cases x (Fin.cases y (fun i : Fin n => e i.val))) = Structure.func (L := language) oneCode Fin.elim0 →
      Structure.func (L := language) pred (Fin.cases (Structure.func (L := language) Code.succ (fun _ => x))
        (Fin.cases (Structure.func (L := language) step (Fin.cases x (Fin.cases y (fun i : Fin n => e i.val))))
          (fun i : Fin n => e i.val))) = Structure.func (L := language) oneCode Fin.elim0) :
    ∀ x, Structure.func (L := language) pred (Fin.cases x (Fin.cases
      (Structure.func (L := language) (iterateCode base step) (Fin.cases x (fun i : Fin n => e i.val)))
      (fun i : Fin n => e i.val))) = Structure.func (L := language) oneCode Fin.elim0 := by
  let z : M := Structure.func (L := language) (Code.zero 0) Fin.elim0
  let s : M → M := fun x => Structure.func (L := language) Code.succ (fun _ => x)
  let params : Fin n → M := fun i => e i.val
  let iter : M → M := fun x => Structure.func (L := language) (iterateCode base step) (Fin.cases x params)
  let p : M → M → M := fun x y => Structure.func (L := language) pred (Fin.cases x (Fin.cases y params))
  let next : M → M → M := fun x y => Structure.func (L := language) step (Fin.cases x (Fin.cases y params))
  intro x
  apply (recursiveBody_eval pred base step x e).mp
  apply modelOpenInduction (M := M) (recursiveBody pred base step) (recursiveBody_open pred base step) e
  · apply (recursiveBody_eval pred base step z e).mpr
    change p z (iter z) = _
    have hb := modelBase (M := M) base step params
    change iter z = Structure.func (L := language) base params at hb
    rw [hb]
    exact hbase
  · intro t ht
    apply (recursiveBody_eval pred base step (s t) e).mpr
    change p (s t) (iter (s t)) = _
    have hs := modelStep (M := M) base step (Fin.cases t params)
    change iter (s t) = next t (iter t) at hs
    rw [hs]
    apply hstep
    exact (recursiveBody_eval pred base step t e).mp ht

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem baseFormula_eval {n : ℕ} (pred : Code (n+2)) (base : Code n) (e : ℕ → M) :
    (baseFormula pred base).Eval ![] e ↔
      Structure.func (L := language) pred (Fin.cases
        (Structure.func (L := language) (Code.zero 0) Fin.elim0)
        (Fin.cases (Structure.func (L := language) base (fun i : Fin n => e i.val)) (fun i => e i.val))) =
        Structure.func (L := language) oneCode Fin.elim0 := by
  rw [baseFormula, Semiformula.eval_rel, eqRel]
  have hz : (Semiterm.val (L := language) ![] e ∘ Fin.elim0) = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  have hb : (Semiterm.val (L := language) ![] e ∘ params0 n) = (fun i : Fin n => e i.val) := by funext i; rfl
  have hp : (Semiterm.val ![] e ∘ Fin.cases (.func (Code.zero 0) Fin.elim0)
      (Fin.cases (.func base (params0 n)) (params0 n))) =
      Fin.cases (Structure.func (L := language) (Code.zero 0) Fin.elim0)
        (Fin.cases (Structure.func (L := language) base (fun i : Fin n => e i.val)) (fun i => e i.val)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Structure.func (L := language) (Code.zero 0) (Semiterm.val ![] e ∘ Fin.elim0) = _
      rw [hz]
      rfl
    · refine Fin.cases ?_ (fun _ => rfl) j
      change Structure.func (L := language) base (Semiterm.val ![] e ∘ params0 n) = _
      rw [hb]
      rfl
  change Structure.func (L := language) pred (Semiterm.val ![] e ∘ Fin.cases (.func (Code.zero 0) Fin.elim0)
      (Fin.cases (.func base (params0 n)) (params0 n))) =
      Structure.func (L := language) oneCode (Semiterm.val ![] e ∘ Fin.elim0) ↔ _
  rw [hp,hz]

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem stepFormula_eval {n : ℕ} (pred : Code (n+2)) (step : Code (n+2)) (e : ℕ → M) :
    (stepFormula pred step).Eval ![] e ↔ ∀ x y,
      Structure.func (L := language) pred (Fin.cases x (Fin.cases y (fun i : Fin n => e i.val))) =
          Structure.func (L := language) oneCode Fin.elim0 →
        Structure.func (L := language) pred (Fin.cases (Structure.func (L := language) Code.succ (fun _ => x))
          (Fin.cases (Structure.func (L := language) step (Fin.cases x (Fin.cases y (fun i : Fin n => e i.val))))
            (fun i : Fin n => e i.val))) = Structure.func (L := language) oneCode Fin.elim0 := by
  simp only [stepFormula, Semiformula.eval_all]
  apply forall_congr'
  intro x
  apply forall_congr'
  intro y
  have hz : (Semiterm.val (L := language) ![y,x] e ∘ Fin.elim0) = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  have hold : (Semiterm.val ![y,x] e ∘ Fin.cases (.bvar 1) (Fin.cases (.bvar 0) (params2 n))) =
      Fin.cases x (Fin.cases y (fun i : Fin n => e i.val)) := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) i
  have hsucc : (Semiterm.val ![y,x] e ∘ ![(.bvar 1 : Semiterm language ℕ 2)]) = (fun _ => x) := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  have hnew : (Semiterm.val ![y,x] e ∘ Fin.cases (.func Code.succ ![.bvar 1]) (Fin.cases
      (.func step (Fin.cases (.bvar 1) (Fin.cases (.bvar 0) (params2 n)))) (params2 n))) =
      Fin.cases (Structure.func (L := language) Code.succ (fun _ => x))
        (Fin.cases (Structure.func (L := language) step (Fin.cases x (Fin.cases y (fun i : Fin n => e i.val))))
          (fun i : Fin n => e i.val)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Structure.func (L := language) Code.succ (Semiterm.val ![y,x] e ∘ ![.bvar 1]) = _
      rw [hsucc]
      rfl
    · refine Fin.cases ?_ (fun _ => rfl) j
      change Structure.func (L := language) step
        (Semiterm.val ![y,x] e ∘ Fin.cases (.bvar 1) (Fin.cases (.bvar 0) (params2 n))) = _
      rw [hold]
      rfl
  simp [Semiformula.imp_eq, Semiformula.eval_rel, Semiformula.eval_nrel, eqRel,
    Semiterm.val_func, hold, hnew, hz]
  classical
  tauto

theorem modelRecursiveSentence {n : ℕ} (pred : Code (n+2)) (base : Code n) (step : Code (n+2)) :
    M↓[language] ⊧ recursiveSentence pred base step := by
  simp only [models_iff, recursiveSentence, Semiformula.eval_univCl]
  intro e
  have hr : (baseFormula pred base).Eval ![] e → (stepFormula pred step).Eval ![] e →
      ∀ x, (recursiveBody pred base step).Eval ![x] e := by
    intro hb hs x
    exact (recursiveBody_eval pred base step x e).mpr
      (modelRecursiveWitness pred base step e ((baseFormula_eval pred base e).mp hb)
        ((stepFormula_eval pred step e).mp hs) x)
  simpa using hr

end models

theorem PRA_proves_recursiveSentence {n : ℕ} (pred : Code (n+2)) (base : Code n) (step : Code (n+2)) :
    PRA ⊢ recursiveSentence pred base step := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelRecursiveSentence pred base step

end DiophantineConsistency.PRAPrimitiveRecursionInduction
