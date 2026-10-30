import DiophantineConsistency.PRAPairedInductionMatrix
import DiophantineConsistency.PRABoundedPairGraph
import DiophantineConsistency.PRANonzeroCharacter
set_option autoImplicit false
namespace DiophantineConsistency.PRAPairedInductionSemantics
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAPairedInductionMatrix
open PRABoundedPairGraph PRANonzeroCharacter PRAOpenOneInduction
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelPairedZero (ψ₀ ψ₁ : Semisentence language 3) (c : M) :
    ∃ t : M, ∀ x y : M,
      (pairedMatrix ψ₀ ψ₁).Eval ![x,y,t] Empty.elim ↔ ψ₀.Eval ![x,y,c] Empty.elim := by
  let z : M := Structure.func (L := language) (Code.zero 0) Fin.elim0
  let o : M := Structure.func (L := language) oneCode Fin.elim0
  obtain ⟨t,hgraph,hunique,_,hbound⟩ := modelPairGraphBounded z c
  refine ⟨t, fun x y => ?_⟩
  change ((branch ψ₀ (Code.zero 0) ⋎ branch ψ₁ oneCode).Eval ![x,y,t] Empty.elim) ↔ _
  change ((branch ψ₀ (Code.zero 0)).Eval ![x,y,t] Empty.elim ∨
    (branch ψ₁ oneCode).Eval ![x,y,t] Empty.elim) ↔ _
  rw [branch_eval, branch_eval]
  constructor
  · intro h
    rcases h with ⟨d,_,hg,hψ⟩ | ⟨d,_,hg,_⟩
    · have hd := (hunique z d hg).2
      simpa [hd] using hψ
    · have he := (hunique o d hg).1
      exact False.elim (modelOneNeZero (M := M) he)
  · intro hψ
    left
    exact ⟨c,hbound,hgraph,hψ⟩

theorem modelPairedOne (ψ₀ ψ₁ : Semisentence language 3) (c : M) :
    ∃ t : M, ∀ x y : M,
      (pairedMatrix ψ₀ ψ₁).Eval ![x,y,t] Empty.elim ↔ ψ₁.Eval ![x,y,c] Empty.elim := by
  let z : M := Structure.func (L := language) (Code.zero 0) Fin.elim0
  let o : M := Structure.func (L := language) oneCode Fin.elim0
  obtain ⟨t,hgraph,hunique,_,hbound⟩ := modelPairGraphBounded o c
  refine ⟨t, fun x y => ?_⟩
  change ((branch ψ₀ (Code.zero 0) ⋎ branch ψ₁ oneCode).Eval ![x,y,t] Empty.elim) ↔ _
  change ((branch ψ₀ (Code.zero 0)).Eval ![x,y,t] Empty.elim ∨
    (branch ψ₁ oneCode).Eval ![x,y,t] Empty.elim) ↔ _
  rw [branch_eval, branch_eval]
  constructor
  · intro h
    rcases h with ⟨d,_,hg,_⟩ | ⟨d,_,hg,hψ⟩
    · have he := (hunique z d hg).1
      exact False.elim (modelOneNeZero (M := M) he.symm)
    · have hd := (hunique o d hg).2
      simpa [hd] using hψ
  · intro hψ
    right
    exact ⟨c,hbound,hgraph,hψ⟩

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

theorem modelOpenSuccInd (ψ : Semisentence language 3) (e : ℕ → M) :
    (succInd (openSigma ψ)).Eval ![] e ↔
      ((openSigma ψ).Eval ![Structure.func (L := language) (Code.zero 0) Fin.elim0] e →
       (∀ x : M, (openSigma ψ).Eval ![x] e →
         (openSigma ψ).Eval ![Structure.func (L := language) Code.succ (fun _ => x)] e) →
       ∀ x : M, (openSigma ψ).Eval ![x] e) := by
  simp [succInd, Semiformula.eval_substs, Semiterm.Operator.numeral_zero,
    Semiterm.Operator.numeral_one, Structure.Zero.zero, Structure.One.one]
  change ((openSigma ψ).Eval ![(0 : M)] e →
    (∀ x : M, (openSigma ψ).Eval ![x] e → (openSigma ψ).Eval ![x+1] e) →
      ∀ x : M, (openSigma ψ).Eval ![x] e) ↔ _
  have hz : (0 : M) = Structure.func (L := language) (Code.zero 0) Fin.elim0 := rfl
  have hs (x : M) : x+1 = Structure.func (L := language) Code.succ (fun _ => x) := by
    change Structure.func (L := language) addCode
      ![x, Structure.func (L := language) oneCode Fin.elim0] = _
    exact modelAddOne x
  simp only [hz, hs]

theorem modelPairedSuccInd_zero (ψ₀ ψ₁ : Semisentence language 3)
    (h : M↓[language] ⊧ (succInd (openSigma (pairedMatrix ψ₀ ψ₁))).univCl) :
    M↓[language] ⊧ (succInd (openSigma ψ₀)).univCl := by
  simp only [models_iff, Semiformula.eval_univCl] at h ⊢
  intro e
  obtain ⟨t,ht⟩ := modelPairedZero ψ₀ ψ₁ (e 0)
  let e' : ℕ → M := Function.update e 0 t
  have hc (x : M) : (openSigma (pairedMatrix ψ₀ ψ₁)).Eval ![x] e' ↔
      (openSigma ψ₀).Eval ![x] e := by
    rw [modelOpenSigma, modelOpenSigma]
    simp only [e', Function.update_self]
    exact exists_congr (ht x)
  have hi := (modelOpenSuccInd _ e').mp (h e')
  apply (modelOpenSuccInd _ e).mpr
  intro hb hs x
  apply (hc x).mp
  apply hi ((hc _).mpr hb)
  intro z hz
  exact (hc _).mpr (hs z ((hc z).mp hz))

theorem modelPairedSuccInd_one (ψ₀ ψ₁ : Semisentence language 3)
    (h : M↓[language] ⊧ (succInd (openSigma (pairedMatrix ψ₀ ψ₁))).univCl) :
    M↓[language] ⊧ (succInd (openSigma ψ₁)).univCl := by
  simp only [models_iff, Semiformula.eval_univCl] at h ⊢
  intro e
  obtain ⟨t,ht⟩ := modelPairedOne ψ₀ ψ₁ (e 0)
  let e' : ℕ → M := Function.update e 0 t
  have hc (x : M) : (openSigma (pairedMatrix ψ₀ ψ₁)).Eval ![x] e' ↔
      (openSigma ψ₁).Eval ![x] e := by
    rw [modelOpenSigma, modelOpenSigma]
    simp only [e', Function.update_self]
    exact exists_congr (ht x)
  have hi := (modelOpenSuccInd _ e').mp (h e')
  apply (modelOpenSuccInd _ e).mpr
  intro hb hs x
  apply (hc x).mp
  apply hi ((hc _).mpr hb)
  intro z hz
  exact (hc _).mpr (hs z ((hc z).mp hz))
end models
end DiophantineConsistency.PRAPairedInductionSemantics
