import DiophantineConsistency.PRABoundedSearchInvariant
import DiophantineConsistency.PRAModelIOpenPairing
set_option autoImplicit false
namespace DiophantineConsistency.PRAWitnessFold
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAOpenInduction
  PRAModelIOpenPairing PRATermCompilation

def foldStep {n : ℕ} (f : Code (n+1)) : Code (n+2) :=
  .comp addCode (.cons (.proj (1 : Fin (n+2)))
    (.cons (.comp f (.cons (.proj (0 : Fin (n+2)))
      (pack n (fun i => .proj i.succ.succ)))) (.nil (n+2))))

def foldCode {n : ℕ} (f : Code (n+1)) : Code (n+1) := .prec (.zero n) (foldStep f)

theorem foldCode_primrec {n : ℕ} (f : Code (n+1)) : Primrec (eval (foldCode f)) :=
  eval_primrec (foldCode f)

private def parameters (n : ℕ) : Fin n → Semiterm language ℕ 1 := fun i => .fvar (i.val+1)
private def foldTerm {n : ℕ} (f : Code (n+1)) : Semiterm language ℕ 1 :=
  .func (foldCode f) (Fin.cases (.bvar 0) (parameters n))
private def valueTerm {n : ℕ} (f : Code (n+1)) : Semiterm language ℕ 1 :=
  .func f (Fin.cases (.fvar 0) (parameters n))
private def invariantBody {n : ℕ} (f : Code (n+1)) : Semiformula language ℕ 1 :=
  Semiformula.nrel Language.ORing.Rel.lt ![.fvar 0, .bvar 0] ⋎
    Semiformula.nrel Language.ORing.Rel.lt ![foldTerm f, valueTerm f]
private theorem invariantBody_open {n : ℕ} (f : Code (n+1)) : (invariantBody f).Open := by
  simp [invariantBody, Semiformula.Open]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelFoldZero {n : ℕ} (f : Code (n+1)) (e : Fin n → M) :
    Structure.func (L := language) (foldCode f)
      (Fin.cases (Structure.func (L := language) (Code.zero 0) Fin.elim0) e) =
      Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
  have h := modelBase (M := M) (.zero n) (foldStep f) e
  exact h.trans (PRAMultiplication.modelZero e)

theorem modelFoldStep {n : ℕ} (f : Code (n+1)) (x : M) (e : Fin n → M) :
    Structure.func (L := language) (foldCode f)
      (Fin.cases (Structure.func (L := language) Code.succ (fun _ => x)) e) =
    Structure.func (L := language) addCode
      ![Structure.func (L := language) (foldCode f) (Fin.cases x e),
        Structure.func (L := language) f (Fin.cases x e)] := by
  have hs := modelStep (.zero n) (foldStep f) (Fin.cases x e)
  change Structure.func (L := language) (foldCode f)
    (Fin.cases (Structure.func (L := language) Code.succ (fun _ => x)) e) =
    Structure.func (L := language) (foldStep f)
    (Fin.cases x (Fin.cases (Structure.func (L := language) (foldCode f) (Fin.cases x e)) e)) at hs
  rw [hs, foldStep, modelComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact modelProjection 1 _
  · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
    simp only [getCode, Fin.cases_succ, Fin.cases_zero]
    rw [modelComposition]
    congr 1
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · exact modelProjection 0 _
    · simp only [getCode, getCode_pack]
      exact modelProjection k.succ.succ _

local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
private theorem invariantBody_eval {n : ℕ} (f : Code (n+1)) (x : M) (e : ℕ → M) :
    (invariantBody f).Eval ![x] e ↔
    ¬ e 0 < x ∨ ¬ Structure.func (L := language) (foldCode f)
       (Fin.cases x (fun i : Fin n => e (i.val+1))) <
       Structure.func (L := language) f (Fin.cases (e 0) (fun i : Fin n => e (i.val+1))) := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] (invariantBody f) ↔ _
  dsimp only [invariantBody, Semiformula.EvalAux]
  have hf : (Semiterm.val ![x] e ∘ Fin.cases (.bvar 0) (parameters n)) =
      Fin.cases x (fun i : Fin n => e (i.val+1)) := by
    simpa only [Function.comp_def, Semiterm.val_bvar, Semiterm.val_fvar,
      Matrix.cons_val_zero, parameters] using val_cases (.bvar 0) (parameters n) ![x] e
  have hv : (Semiterm.val ![x] e ∘ Fin.cases (.fvar 0) (parameters n)) =
      Fin.cases (e 0) (fun i : Fin n => e (i.val+1)) := by
    simpa only [Function.comp_def, Semiterm.val_fvar, parameters] using
      val_cases (.fvar 0) (parameters n) ![x] e
  have h0 : (Semiterm.val ![x] e ∘ ![(.fvar 0 : Semiterm language ℕ 1), .bvar 0]) = ![e 0,x] := by
    simpa only [Semiterm.val_bvar, Semiterm.val_fvar, Matrix.cons_val_zero] using
      val_pair ![x] e (.fvar 0) (.bvar 0)
  have h1 : (Semiterm.val ![x] e ∘ ![foldTerm f, valueTerm f]) =
      ![Structure.func (L := language) (foldCode f) (Fin.cases x (fun i : Fin n => e (i.val+1))),
        Structure.func (L := language) f (Fin.cases (e 0) (fun i : Fin n => e (i.val+1)))] := by
    simpa only [Semiterm.val_func, foldTerm, valueTerm, hf, hv] using
      val_pair ![x] e (foldTerm f) (valueTerm f)
  change (¬ Structure.rel (L := language) Language.ORing.Rel.lt
      (Semiterm.val ![x] e ∘ ![.fvar 0, .bvar 0]) ∨
    ¬ Structure.rel (L := language) Language.ORing.Rel.lt
      (Semiterm.val ![x] e ∘ ![foldTerm f, valueTerm f])) ↔ _
  rw [h0, h1]
  rfl


/-- In every candidate-PRA model, every value with index below the bound
is bounded by the primitive-recursively accumulated sum. -/
theorem modelFoldBounds {n : ℕ} (f : Code (n+1)) (e : ℕ → M) (k : M) :
    let params := fun i : Fin n => e (i.val+1)
    ¬ e 0 < k ∨ ¬ Structure.func (L := language) (foldCode f) (Fin.cases k params) <
      Structure.func (L := language) f (Fin.cases (e 0) params) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let params : Fin n → M := fun i => e (i.val+1)
  let find : M → M := fun x => Structure.func (L := language) (foldCode f) (Fin.cases x params)
  let value : M → M := fun x => Structure.func (L := language) f (Fin.cases x params)
  apply (invariantBody_eval f k e).mp
  apply modelOpenInduction (M := M) (invariantBody f) (invariantBody_open f) e
  · apply (invariantBody_eval f 0 e).mpr
    change ¬ e 0 < 0 ∨ ¬ find 0 < value (e 0)
    exact Or.inl (by simp)
  · intro t ht
    let st := Structure.func (L := language) Code.succ (fun _ => t)
    apply (invariantBody_eval f st e).mpr
    change ¬ e 0 < st ∨ ¬ find st < value (e 0)
    by_cases hlt : e 0 < st
    · right
      have heq : st = t+1 := (modelAddOne t).symm
      have hi : e 0 ≤ t := lt_succ_iff_le.mp (heq ▸ hlt)
      have hbound : value (e 0) ≤ find t + value t := by
        rcases le_iff_lt_or_eq.mp hi with hi | hi
        · have ih := (invariantBody_eval f t e).mp ht
          change ¬ e 0 < t ∨ ¬ find t < value (e 0) at ih
          have hv : value (e 0) ≤ find t := le_of_not_gt (ih.resolve_left (not_not.mpr hi))
          exact le_trans hv le_self_add
        · rw [hi]
          exact le_add_self
      have hf := modelFoldStep f t params
      change find st = find t + value t at hf
      exact not_lt_of_ge (hf ▸ hbound)
    · exact Or.inl hlt


/-- The concrete local bound `p+1`, aggregated for all `p < k`.
This is the candidate-theory interface for the separately verified
`fstIdxDef` local witness majorant; it does not prove that majorant. -/
theorem modelIndexSuccBound (i k : M)
    (hi : Structure.rel (L := language) Language.ORing.Rel.lt ![i,k]) :
    ¬ Structure.rel (L := language) Language.ORing.Rel.lt
      ![Structure.func (L := language) (foldCode Code.succ) ![k],
        Structure.func (L := language) Code.succ (fun _ => i)] := by
  have h := modelFoldBounds Code.succ (fun _ => i) k
  have hb := h.resolve_left (not_not.mpr hi)
  change ¬ Structure.func (L := language) (foldCode Code.succ) ![k] <
    Structure.func (L := language) Code.succ (fun _ => i)
  have hk : (fun j : Fin 1 => Fin.cases k (fun _ : Fin 0 => i) j) = ![k] := by
    funext j
    exact Fin.cases rfl (fun j => Fin.elim0 j) j
  have hi' : (fun j : Fin 1 => Fin.cases i (fun _ : Fin 0 => i) j) = (fun _ => i) := by
    funext j
    exact Fin.cases rfl (fun j => Fin.elim0 j) j
  rw [hk, hi'] at hb
  exact hb


end models
end DiophantineConsistency.PRAWitnessFold
