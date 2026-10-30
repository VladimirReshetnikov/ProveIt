import DiophantineConsistency.PRABoundedWitness

/-! Parameterized bounded induction in candidate PRA via characteristic codes. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRABoundedInduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAOpenInduction PRAFormulaParameters
  PRABoundedCharacteristic PRABoundedFormula PRABoundedWitness

theorem packParameters_bounded {n : ℕ} (φ : Semiproposition language n) (hφ : Hierarchy 𝚺 0 φ) :
    Hierarchy 𝚺 0 (packParameters φ) := by
  apply (Hierarchy.rew_iff (ω := (Rew.emb : Rew language Empty _ ℕ _))).mp
  rw [packParameters_emb]
  exact Hierarchy.rew _ hφ

private def characteristicBody {n : ℕ} (c : Code (n+1)) : Semiproposition language 1 :=
  Semiformula.rel Language.ORing.Rel.eq
    ![.func c (Fin.cases (.bvar 0) (fun i : Fin n => .fvar i.val)), .func oneCode Fin.elim0]

private theorem characteristicBody_open {n : ℕ} (c : Code (n+1)) : (characteristicBody c).Open := by
  simp [characteristicBody, Semiformula.Open]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
private theorem castCode_eval {n m : ℕ} (h : n = m) (c : Code n) (v : Fin m → M) :
    Structure.func (L := language) (h ▸ c) v =
      Structure.func (L := language) c (fun i => v (Fin.cast h i)) := by
  cases h
  rfl

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
private theorem packedEval (φ : Semiproposition language 1) (x : M) (e : ℕ → M) :
    let k := φ.fvSup
    let h : 1+k = k+1 := Nat.add_comm 1 k
    let v : Fin (1+k) → M := fun i => Fin.cases x (fun j : Fin k => e j.val) (Fin.cast h i)
    (packParameters φ).Eval v Empty.elim ↔ φ.Eval ![x] e := by
  dsimp only
  rw [packParameters_eval φ _ (fun i => e (i + φ.fvSup))]
  have hb : (fun i : Fin 1 =>
      Fin.cases x (fun j : Fin φ.fvSup => e j.val)
        (Fin.cast (Nat.add_comm 1 φ.fvSup) (i.castAdd φ.fvSup))) = ![x] := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    rfl
  have hf : (fun i => if hi : i < φ.fvSup then
      Fin.cases x (fun j : Fin φ.fvSup => e j.val)
        (Fin.cast (Nat.add_comm 1 φ.fvSup) (Fin.natAdd 1 ⟨i,hi⟩))
      else e ((i - φ.fvSup) + φ.fvSup)) = e := by
    funext i
    by_cases hi : i < φ.fvSup
    · simp only [hi, ↓reduceDIte]
      have hpos : Fin.cast (Nat.add_comm 1 φ.fvSup) (Fin.natAdd 1 ⟨i,hi⟩) =
          (⟨i,hi⟩ : Fin φ.fvSup).succ := by
        apply Fin.ext
        simp [Nat.add_comm]
      rw [hpos]
      rfl
    · simp only [hi, ↓reduceDIte]
      congr 1
      omega
  rw [hb, hf]

local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Structure.Zero language M := ⟨by
  simp only [Semiterm.Operator.val, Semiterm.Operator.Zero.zero, Semiterm.val_func]
  have h : (Semiterm.val ![] Empty.elim ∘ (![] : Fin 0 → Semiterm language Empty 0)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [h]
  rfl⟩
local instance : Structure.One language M := ⟨by
  simp only [Semiterm.Operator.val, Semiterm.Operator.One.one, Semiterm.val_func]
  have h : (Semiterm.val ![] Empty.elim ∘ (![] : Fin 0 → Semiterm language Empty 0)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [h]
  rfl⟩
local instance : Structure.Add language M := ⟨fun _ _ => rfl⟩

omit [Nonempty M] [M↓[language] ⊧* PRA] in
private theorem characteristicBody_eval {n : ℕ} (c : Code (n+1)) (x : M) (e : ℕ → M) :
    (characteristicBody c).Eval ![x] e ↔
      Structure.func (L := language) c (Fin.cases x (fun i : Fin n => e i.val)) =
        Structure.func (L := language) oneCode Fin.elim0 := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] (characteristicBody c) ↔ _
  dsimp only [characteristicBody, Semiformula.EvalAux]
  rw [eqRel]
  have he : (Semiterm.val (L := language) ![x] e ∘ Fin.cases (.bvar 0) (fun i : Fin n => .fvar i.val)) =
      Fin.cases x (fun i : Fin n => e i.val) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  have hz : (Semiterm.val (L := language) ![x] e ∘ Fin.elim0) = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simp [Semiterm.val_func, he, hz]

theorem modelBoundedInductionAxiom (φ : Semiproposition language 1) (hφ : Hierarchy 𝚺 0 φ) :
    M↓[language] ⊧ (succInd φ).univCl := by
  obtain ⟨c,_,_,hc⟩ := PRA_proves_boundedBooleanCharacteristic (packParameters φ) (packParameters_bounded φ hφ)
  let k := φ.fvSup
  let h : 1+k = k+1 := Nat.add_comm 1 k
  let good : Code (k+1) := h ▸ c
  have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hc
  simp only [models_iff, Semiformula.eval_univCl]
  intro e
  have rule : φ.Eval ![(Structure.func (L := language) (Code.zero 0) Fin.elim0 : M)] e →
      (∀ x, φ.Eval ![x] e → φ.Eval ![Structure.func (L := language) Code.succ (fun _ => x)] e) →
        ∀ x, φ.Eval ![x] e := by
    intro hBase hStep
    let z : M := Structure.func (L := language) (Code.zero 0) Fin.elim0
    let s : M → M := fun x => Structure.func (L := language) Code.succ (fun _ => x)
    let params : Fin k → M := fun i => e i.val
    have hChar (x : M) : (characteristicBody good).Eval ![x] e ↔ φ.Eval ![x] e := by
      rw [characteristicBody_eval]
      have hc' := modelCharacteristicMatrix c (packParameters φ) hm
        (fun i => Fin.cases x params (Fin.cast h i))
      have he := packedEval (M := M) φ x e
      change Structure.func (L := language) (h ▸ c) (Fin.cases x params) = _ ↔ _
      rw [castCode_eval]
      change (characteristicMatrix c).Eval _ Empty.elim ↔ _ at hc'
      let v : Fin (1+k) → M := fun i => Fin.cases x params (Fin.cast h i)
      have hz : (Semiterm.val (L := language) v Empty.elim ∘ Fin.elim0) = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
      change (characteristicMatrix c).Eval v Empty.elim ↔ _ at hc'
      simp [characteristicMatrix, Semiformula.eval_rel, eqRel, applyCode, Semiterm.val_func, hz] at hc'
      exact hc'.trans he
    intro x
    apply (hChar x).mp
    apply modelOpenInduction (M := M) (characteristicBody good) (characteristicBody_open good) e
    · exact (hChar z).mpr hBase
    · intro y hy
      exact (hChar (s y)).mpr (hStep y ((hChar y).mp hy))
  have ruleAdd : φ.Eval ![(0 : M)] e →
      (∀ x, φ.Eval ![x] e → φ.Eval ![x + 1] e) → ∀ x, φ.Eval ![x] e := by
    intro hb hs x
    apply rule hb ?_ x
    intro y hy
    have he := hs y hy
    change φ.Eval ![Structure.func (L := language) addCode
      ![y, Structure.func (L := language) oneCode Fin.elim0]] e at he
    rw [modelAddOne] at he
    exact he
  simpa [succInd, Semiformula.eval_substs, Semiterm.Operator.numeral_zero,
    Semiterm.Operator.numeral_one, Structure.Zero.zero, Structure.One.one] using ruleAdd

end models

theorem PRA_proves_boundedInduction (φ : Semiproposition language 1) (hφ : Hierarchy 𝚺 0 φ) :
    PRA ⊢ (succInd φ).univCl := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelBoundedInductionAxiom φ hφ

end DiophantineConsistency.PRABoundedInduction
