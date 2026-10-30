import DiophantineConsistency.PRAPrimitiveRecursionInduction
import DiophantineConsistency.HerbrandAllInstantiation
import DiophantineConsistency.HerbrandExistentialSideSelection
/-! From actual fixed base and step witness proofs, obtain the existential
induction conclusion with a recursively computed primitive-recursive witness. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAJoostenWitnessedRule
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAPrimitiveRecursionInduction

private def params2 (n : ℕ) : Fin n → Semiterm language ℕ 2 := fun i => .fvar i.val
private def params1 (n : ℕ) : Fin n → Semiterm language ℕ 1 := fun i => .fvar i.val

def existentialBody {n : ℕ} (pred : Code (n+2)) : Semiproposition language 1 :=
  ∃⁰ (Semiformula.rel Language.ORing.Rel.eq
    ![.func pred (Fin.cases (.bvar 1) (Fin.cases (.bvar 0) (params2 n))),
      .func oneCode Fin.elim0])

def witnessedBody {n : ℕ} (pred : Code (n+2)) (base : Code n) (step : Code (n+2)) :
    Semiproposition language 1 :=
  Semiformula.rel Language.ORing.Rel.eq
    ![.func pred (Fin.cases (.bvar 0) (Fin.cases
        (.func (iterateCode base step) (Fin.cases (.bvar 0) (params1 n))) (params1 n))),
      .func oneCode Fin.elim0]

private def params0 (n : ℕ) : Fin n → Term language ℕ := fun i => .fvar i.val
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
omit [Nonempty M] [M↓[language] ⊧* PRA] in
private theorem witnessedBody_eval {n : ℕ} (pred : Code (n+2)) (base : Code n) (step : Code (n+2))
    (x : M) (e : ℕ → M) : (witnessedBody pred base step).Eval ![x] e ↔
    let params := fun i : Fin n => e i.val
    let iterate := Structure.func (L := language) (iterateCode base step) (Fin.cases x params)
    Structure.func (L := language) pred (Fin.cases x (Fin.cases iterate params)) =
      Structure.func (L := language) oneCode Fin.elim0 := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] (witnessedBody pred base step) ↔ _
  dsimp only [witnessedBody, Semiformula.EvalAux]
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


end models

theorem modelWitnessedBody {M : Type} [Structure language M] [Structure.Eq language M]
    {n : ℕ} (pred : Code (n+2)) (base : Code n) (step : Code (n+2)) (e : ℕ → M) (x : M) :
    (witnessedBody pred base step).Eval ![x] e → (existentialBody pred).Eval ![x] e := by
  intro h
  rw [existentialBody, Semiformula.eval_ex]
  refine ⟨Structure.func (L := language) (iterateCode base step)
    (Fin.cases x (fun i : Fin n => e i.val)), ?_⟩
  simp only [witnessedBody, Semiformula.eval_rel, eqRel] at h ⊢
  have hz1 : (Semiterm.val (L := language) ![x] e ∘ (Fin.elim0 : Fin 0 → Semiterm language ℕ 1)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  have hz2 (y : M) : (Semiterm.val (L := language) ![y,x] e ∘ (Fin.elim0 : Fin 0 → Semiterm language ℕ 2)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  have hv1 : (Semiterm.val (L := language) ![x] e ∘ Fin.cases (.bvar 0) (params1 n)) =
      Fin.cases x (fun i : Fin n => e i.val) := by
    funext i; exact Fin.cases rfl (fun _ => rfl) i
  have hv2 (y : M) : (Semiterm.val (L := language) ![y,x] e ∘ Fin.cases (.bvar 1)
      (Fin.cases (.bvar 0) (params2 n))) = Fin.cases x (Fin.cases y (fun i : Fin n => e i.val)) := by
    funext i; refine Fin.cases rfl (fun j => ?_) i; exact Fin.cases rfl (fun _ => rfl) j
  have hv3 : (Semiterm.val (L := language) ![x] e ∘ Fin.cases (.bvar 0)
      (Fin.cases (.func (iterateCode base step) (Fin.cases (.bvar 0) (params1 n))) (params1 n))) =
      Fin.cases x (Fin.cases (Structure.func (L := language) (iterateCode base step)
        (Fin.cases x (fun i : Fin n => e i.val))) (fun i : Fin n => e i.val)) := by
    funext i; refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases ?_ (fun _ => rfl) j
    change Structure.func (L := language) (iterateCode base step)
      (Semiterm.val ![x] e ∘ Fin.cases (.bvar 0) (params1 n)) = _
    rw [hv1]
    rfl
  change Structure.func (L := language) pred (Semiterm.val ![x] e ∘ Fin.cases (.bvar 0)
    (Fin.cases (.func (iterateCode base step) (Fin.cases (.bvar 0) (params1 n))) (params1 n))) =
    Structure.func (L := language) oneCode (Semiterm.val ![x] e ∘ Fin.elim0) at h
  change Structure.func (L := language) pred (Semiterm.val ![_,x] e ∘ Fin.cases (.bvar 1)
    (Fin.cases (.bvar 0) (params2 n))) = Structure.func (L := language) oneCode
      (Semiterm.val ![_,x] e ∘ Fin.elim0)
  rw [hv3,hz1] at h
  rw [hv2,hz2]
  exact h

theorem PRA_proves_witnessed_rule {n : ℕ} (pred : Code (n+2)) (base : Code n) (step : Code (n+2))
    (hb : PRA ⊢ (baseFormula pred base).univCl)
    (hs : PRA ⊢ (stepFormula pred step).univCl) :
    PRA ⊢ (∀⁰ existentialBody pred).univCl := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  have hbase := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hb
  have hstep := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hs
  simp only [models_iff, Semiformula.eval_univCl] at hbase hstep ⊢
  intro e
  have hall : ∀ x : M, (witnessedBody pred base step).Eval ![x] e := by
    intro x
    apply (witnessedBody_eval pred base step x e).mpr
    exact modelRecursiveWitness pred base step e ((baseFormula_eval pred base e).mp (hbase e))
      ((stepFormula_eval pred step e).mp (hstep e)) x
  simp only [Semiformula.eval_all]
  intro x
  exact modelWitnessedBody pred base step e x (hall x)

open PRAHerbrandSelection HerbrandAllInstantiation PRATermCompilation

def baseMatrix {n : ℕ} (pred : Code (n+2)) : Semisentence language (n+1) :=
  Semiformula.rel Language.ORing.Rel.eq
    ![.func pred (Fin.cases (.func (Code.zero 0) Fin.elim0) (Fin.cases (.bvar 0)
        (fun i : Fin n => .bvar i.succ))), .func oneCode Fin.elim0]

theorem baseMatrix_open {n : ℕ} (pred : Code (n+2)) : (baseMatrix pred).Open := by
  simp [baseMatrix, Semiformula.Open]

section base_models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem modelBaseMatrix {n : ℕ} (pred : Code (n+2)) (y : M) (v : Fin n → M) :
    (baseMatrix pred).Eval (Fin.cases y v) Empty.elim ↔
      Structure.func (L := language) pred (Fin.cases
        (Structure.func (L := language) (Code.zero 0) Fin.elim0) (Fin.cases y v)) =
        Structure.func (L := language) oneCode Fin.elim0 := by
  simp only [baseMatrix, Semiformula.eval_rel, eqRel]
  change Structure.func (L := language) pred (Semiterm.val (L := language) (Fin.cases y v) Empty.elim ∘
    Fin.cases (.func (Code.zero 0) Fin.elim0) (Fin.cases (.bvar 0) (fun i : Fin n => .bvar i.succ))) =
      Structure.func (L := language) oneCode (Semiterm.val (Fin.cases y v) Empty.elim ∘ Fin.elim0) ↔ _
  have hz : (Semiterm.val (L := language) (Fin.cases y v) Empty.elim ∘ Fin.elim0) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  have hv : (Semiterm.val (L := language) (Fin.cases y v) Empty.elim ∘
      Fin.cases (.func (Code.zero 0) Fin.elim0) (Fin.cases (.bvar 0) (fun i : Fin n => .bvar i.succ))) =
      Fin.cases (Structure.func (L := language) (Code.zero 0) Fin.elim0) (Fin.cases y v) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Structure.func (L := language) (Code.zero 0)
        (Semiterm.val (Fin.cases y v) Empty.elim ∘ Fin.elim0) = _
      rw [hz]
      rfl
    · exact Fin.cases rfl (fun _ => rfl) j
  rw [hv,hz]

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem modelBaseSelection {n : ℕ} (pred : Code (n+2)) (base : Code n) (v : Fin n → M) :
    (openMatrixAt (baseMatrix pred) base).Eval v Empty.elim ↔
      Structure.func (L := language) pred (Fin.cases
        (Structure.func (L := language) (Code.zero 0) Fin.elim0)
        (Fin.cases (Structure.func (L := language) base v) v)) =
        Structure.func (L := language) oneCode Fin.elim0 := by
  rw [openMatrixAt, Semiformula.eval_substs]
  have hv : (Semiterm.val (L := language) v Empty.elim ∘
      Fin.cases (applyCode base (vars n)) (vars n)) =
      Fin.cases (Structure.func (L := language) base v) v := by
    funext i
    refine Fin.cases ?_ (fun _ => rfl) i
    change Structure.func (L := language) base (Semiterm.val v Empty.elim ∘ vars n) = _
    congr 1
  rw [hv]
  exact modelBaseMatrix pred _ v
end base_models

theorem PRA_exists_base_witness {n : ℕ} (pred : Code (n+2))
    (p : PRA ⊢ (∀⁰* ∃⁰ baseMatrix pred)) :
    ∃ base : Code n, PRA ⊢ (baseFormula pred base).univCl := by
  obtain ⟨base,_,hbase⟩ := PRA_witness_of_exists (baseMatrix pred) (baseMatrix_open pred) p
  refine ⟨base, ?_⟩
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hbase
  simp only [models_iff, Semiformula.eval_allClosure] at hm
  simp only [models_iff, Semiformula.eval_univCl]
  intro e
  apply (baseFormula_eval pred base e).mpr
  exact (modelBaseSelection pred base (fun i : Fin n => e i.val)).mp (hm _)

open PRAUniversalCandidate HerbrandParameterizedWitness HerbrandContextualTreeSelection
  HerbrandExistentialSideSelection HerbrandUniversalTree

def stepSide {n : ℕ} (pred : Code (n+2)) : Semisentence language (n+2) :=
  Semiformula.nrel Language.ORing.Rel.eq
    ![.func pred (fun i => .bvar i), .func oneCode Fin.elim0]

def stepMatrix {n : ℕ} (pred : Code (n+2)) : Semisentence language ((n+2)+1) :=
  Semiformula.rel Language.ORing.Rel.eq
    ![.func pred (Fin.cases (.func Code.succ ![.bvar 1]) (Fin.cases (.bvar 0)
        (fun i : Fin n => .bvar i.succ.succ.succ))), .func oneCode Fin.elim0]

theorem stepSide_open {n : ℕ} (pred : Code (n+2)) : (stepSide pred).Open := by
  simp [stepSide, Semiformula.Open]

theorem stepMatrix_open {n : ℕ} (pred : Code (n+2)) : (stepMatrix pred).Open := by
  simp [stepMatrix, Semiformula.Open]

section step_models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem modelStepSide {n : ℕ} (pred : Code (n+2)) (v : Fin (n+2) → M) :
    (stepSide pred).Eval v Empty.elim ↔
      Structure.func (L := language) pred v ≠ Structure.func (L := language) oneCode Fin.elim0 := by
  simp only [stepSide, Semiformula.eval_nrel, eqRel]
  have hv : (Semiterm.val (L := language) v Empty.elim ∘ fun i => .bvar i) = v := by funext i; rfl
  have hz : (Semiterm.val (L := language) v Empty.elim ∘ Fin.elim0) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  change ¬(Structure.func (L := language) pred (Semiterm.val v Empty.elim ∘ fun i => .bvar i) =
    Structure.func (L := language) oneCode (Semiterm.val v Empty.elim ∘ Fin.elim0)) ↔ _
  rw [hv,hz]

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem modelStepMatrix {n : ℕ} (pred : Code (n+2)) (w : M) (v : Fin (n+2) → M) :
    (stepMatrix pred).Eval (Fin.cases w v) Empty.elim ↔
      Structure.func (L := language) pred
        (Fin.cases (Structure.func (L := language) Code.succ ![v 0])
          (Fin.cases w (fun i : Fin n => v i.succ.succ))) =
        Structure.func (L := language) oneCode Fin.elim0 := by
  simp only [stepMatrix, Semiformula.eval_rel, eqRel]
  change Structure.func (L := language) pred (Semiterm.val (L := language) (Fin.cases w v) Empty.elim ∘
    Fin.cases (.func Code.succ ![.bvar 1]) (Fin.cases (.bvar 0)
      (fun i : Fin n => .bvar i.succ.succ.succ))) =
    Structure.func (L := language) oneCode (Semiterm.val (Fin.cases w v) Empty.elim ∘ Fin.elim0) ↔ _
  have hz : (Semiterm.val (L := language) (Fin.cases w v) Empty.elim ∘ Fin.elim0) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  have hs : (Semiterm.val (L := language) (Fin.cases w v) Empty.elim ∘ ![.bvar 1]) = ![v 0] := by
    funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
  have hv : (Semiterm.val (L := language) (Fin.cases w v) Empty.elim ∘
      Fin.cases (.func Code.succ ![.bvar 1]) (Fin.cases (.bvar 0)
        (fun i : Fin n => .bvar i.succ.succ.succ))) =
      Fin.cases (Structure.func (L := language) Code.succ ![v 0])
        (Fin.cases w (fun i : Fin n => v i.succ.succ)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Structure.func (L := language) Code.succ
        (Semiterm.val (Fin.cases w v) Empty.elim ∘ ![.bvar 1]) = _
      rw [hs]
      rfl
    · exact Fin.cases rfl (fun _ => rfl) j
  rw [hv,hz]

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem modelStepSelection {n : ℕ} (pred : Code (n+2)) (step : Code (n+2))
    (v : Fin (n+2) → M) :
    (openMatrixAt (stepMatrix pred) step).Eval v Empty.elim ↔
      Structure.func (L := language) pred
        (Fin.cases (Structure.func (L := language) Code.succ ![v 0])
          (Fin.cases (Structure.func (L := language) step v) (fun i : Fin n => v i.succ.succ))) =
        Structure.func (L := language) oneCode Fin.elim0 := by
  rw [openMatrixAt, Semiformula.eval_substs]
  have hv : (Semiterm.val (L := language) v Empty.elim ∘
      Fin.cases (applyCode step (vars (n+2))) (vars (n+2))) =
      Fin.cases (Structure.func (L := language) step v) v := by
    funext i
    refine Fin.cases ?_ (fun _ => rfl) i
    change Structure.func (L := language) step (Semiterm.val v Empty.elim ∘ vars (n+2)) = _
    congr 1
  rw [hv]
  exact modelStepMatrix pred _ v
end step_models

theorem PRA_exists_step_witness {n : ℕ} (pred : Code (n+2))
    (p : UniversalAxiom ⊢ ((parameterSide (stepSide pred)) ⋎
      (∃⁰ (parameterMatrix (stepMatrix pred)))).univCl) :
    ∃ step : Code (n+2), PRA ⊢ (stepFormula pred step).univCl := by
  obtain ⟨step,_,hstep⟩ := PRA_exists_selected (stepSide pred) (stepMatrix pred)
    (stepMatrix_open pred) (.base (stepSide_open pred)) p
  refine ⟨step, ?_⟩
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hstep
  simp only [models_iff, Semiformula.eval_allClosure] at hm
  simp only [models_iff, Semiformula.eval_univCl]
  intro e
  apply (stepFormula_eval pred step e).mpr
  intro x y hxy
  let v : Fin (n+2) → M := Fin.cases x (Fin.cases y (fun i : Fin n => e i.val))
  have hv := hm v
  change (stepSide pred).Eval v Empty.elim ∨ (openMatrixAt (stepMatrix pred) step).Eval v Empty.elim at hv
  rcases hv with hfalse | hgood
  · have hn := (modelStepSide pred v).mp hfalse
    exact False.elim (hn hxy)
  · have hs : ![x] = (fun _ : Fin 1 => x) := by
      funext i
      exact Fin.cases rfl (fun j => Fin.elim0 j) i
    simpa [v, hs] using (modelStepSelection pred step v).mp hgood

/-- Joosten's rule for an explicitly coded open predicate: the step premise
is displayed as the universally closed parameterized disjunction
`pred(x,y,params) ≠ 1 ∨ ∃w pred(succ x,w,params) = 1`. -/
theorem PRA_proves_rule_of_contextual_step {n : ℕ} (pred : Code (n+2))
    (hbase : PRA ⊢ (∀⁰* ∃⁰ baseMatrix pred))
    (hstep : PRA ⊢ ((parameterSide (stepSide pred)) ⋎
      (∃⁰ (parameterMatrix (stepMatrix pred)))).univCl) :
    PRA ⊢ (∀⁰ existentialBody pred).univCl := by
  obtain ⟨base,hbase'⟩ := PRA_exists_base_witness pred hbase
  obtain ⟨step,hstep'⟩ := PRA_exists_step_witness pred
    (PRAUniversalEquivalence.universal_proves_candidate hstep)
  exact PRA_proves_witnessed_rule pred base step hbase' hstep'
end DiophantineConsistency.PRAJoostenWitnessedRule
