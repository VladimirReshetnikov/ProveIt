import DiophantineConsistency.PRAUniversalModelLemmas

/-! Candidate open induction from the universal bounded-search axioms. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAUniversalInduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAFormulaParameters
  PRAOpenFormulaCompiler PRAOpenFormulaCoverage PRAEqualityCode PRACharacteristicBit
  PRABooleanOps PRABoundedSearchCode PRABoundedSearchInvariant PRABoundedSearchMinimal
  PRABoundedSearchUniversalRule PRAUniversalCandidate PRAUniversalModelLemmas

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* UniversalAxiom]

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* UniversalAxiom] in
private theorem castCode_eval {n m : ℕ} (h : n = m) (c : Code n) (v : Fin m → M) :
    Structure.func (L := language) (h ▸ c) v =
      Structure.func (L := language) c (fun i => v (Fin.cast h i)) := by
  cases h
  rfl

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* UniversalAxiom] in
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

theorem modelOpenInductionAxiom (φ : Semiproposition language 1) (hφ : φ.Open) :
    M↓[language] ⊧ (succInd φ).univCl := by
  have hpacked := packParameters_open φ hφ
  obtain ⟨p, _, hp⟩ := parseFormula_open (packParameters φ) hpacked
  let k := φ.fvSup
  let h : 1+k = k+1 := Nat.add_comm 1 k
  let c : Code (1+k) := compileFormula equalityCode p
  let good : Code (k+1) := h ▸ c
  simp only [models_iff, Semiformula.eval_univCl]
  intro e
  have rule : φ.Eval ![(Structure.func (L := language) (Code.zero 0) Fin.elim0 : M)] e →
      (∀ x, φ.Eval ![x] e → φ.Eval ![Structure.func (L := language) Code.succ (fun _ => x)] e) →
        ∀ x, φ.Eval ![x] e := by
    intro hBase hStep
    let z : M := Structure.func (L := language) (Code.zero 0) Fin.elim0
    let o : M := Structure.func (L := language) oneCode Fin.elim0
    let s : M → M := fun x => Structure.func (L := language) Code.succ (fun _ => x)
    let d : M → M := fun x => Structure.func (L := language) predCode (fun _ => x)
    let params : Fin k → M := fun i => e i.val
    let g : M → M := fun x => Structure.func (L := language) good (Fin.cases x params)
    let find : M → M := fun x => Structure.func (L := language) (searchCode good) (Fin.cases x params)
    have hChar (x : M) : g x = o ↔ φ.Eval ![x] e := by
      have hc := modelCompiledCorrect (M := M) p
        (fun i => Fin.cases x params (Fin.cast h i))
      rw [hp] at hc
      have he := packedEval (M := M) φ x e
      change Structure.func (L := language) c
        (fun i => Fin.cases x params (Fin.cast h i)) = o ↔ _ at hc
      dsimp only at he
      change Structure.func (L := language) (h ▸ c) (Fin.cases x params) = o ↔ _
      rw [castCode_eval]
      exact hc.trans he
    have hBits (x : M) : g x = z ∨ g x = o := by
      have hb := modelCompiledBit (M := M) p (fun i => Fin.cases x params (Fin.cast h i))
      change IsBit (Structure.func (L := language) (h ▸ c) (Fin.cases x params))
      rw [castCode_eval]
      exact hb
    have hCand (x : M) : g (find x) = z ∨ find x = x := by
      have hs := Theory.models (T := UniversalAxiom) M (UniversalAxiom.searchCandidate good)
      exact (candidateSentence_iff good).mp hs e x
    have hMin (x : M) : find x = z ∨ g (d (find x)) ≠ z := by
      have hs := Theory.models (T := UniversalAxiom) M (UniversalAxiom.searchMinimal good)
      exact (minimalSentence_iff good).mp hs e x
    have hb : g z = o := (hChar z).mpr hBase
    have hs : ∀ x, g x = o → g (s x) = o := by
      intro x hx
      exact (hChar (s x)).mpr (hStep x ((hChar x).mp hx))
    intro x
    apply (hChar x).mp
    exact inductionFromSearch z o s d g find (modelOneNeZero (M := M))
      (modelExhaustion (M := M)) hBits hCand hMin hb hs x
  have ruleAdd : φ.Eval ![(0 : M)] e →
      (∀ x, φ.Eval ![x] e → φ.Eval ![x + 1] e) → ∀ x, φ.Eval ![x] e := by
    intro hb hs x
    apply rule hb ?_ x
    intro y hy
    have he := hs y hy
    change φ.Eval ![Structure.func (L := language) addCode
      ![y, Structure.func (L := language) oneCode Fin.elim0]] e at he
    rw [PRAUniversalModelLemmas.modelAddOne] at he
    exact he
  simpa [succInd, Semiformula.eval_substs, Semiterm.Operator.numeral_zero,
    Semiterm.Operator.numeral_one, Structure.Zero.zero, Structure.One.one] using ruleAdd

end models
end DiophantineConsistency.PRAUniversalInduction
