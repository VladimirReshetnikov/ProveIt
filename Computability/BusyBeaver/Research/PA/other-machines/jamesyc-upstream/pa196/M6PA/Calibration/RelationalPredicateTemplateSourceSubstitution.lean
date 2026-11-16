module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateSourceTerms
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language

theorem atomValue_sourceSubst {s r k : Nat} (rel : Relation k) (ts : Fin k→Term s)
    (σ : Fin s→Term r) (P b c f : V)
    (hb : ∀i : Fin s,nth c (i:Nat)=termValue (σ i) b f) :
    atomValue rel ((Rew.subst σ) ∘ ts) P b f=atomValue rel ts P c f := by
  cases rel <;> simp only [atomValue,Function.comp_apply,termValue_sourceSubst _ σ b c f hb]

theorem formulaValue_sourceSubst {s r : Nat} (p : Formula s) (σ : Fin s→Term r)
    {n P b c f : V} (h : EnvironmentsValid (r:V) n b f) (hc : IsSemitermVec L (s:V) n c)
    (hb : ∀i : Fin s,nth c (i:Nat)=termValue (σ i) b f)
    (hf : ∀j i,(σ j).FVar? i→(i:V)<len f) :
    formulaValue (Semiformula.rewAux (Rew.subst σ) p) P b f=formulaValue p P c f := by
  induction p generalizing r n b c f with
  | verum => rfl
  | falsum => rfl
  | rel rel ts => exact atomValue_sourceSubst rel ts σ P b c f hb
  | nrel rel ts => simp only [Semiformula.rewAux,formulaValue,atomValue_sourceSubst rel ts σ P b c f hb]
  | and p q ihp ihq => simp only [Semiformula.rewAux,formulaValue,ihp σ h hc hb hf,ihq σ h hc hb hf]
  | or p q ihp ihq => simp only [Semiformula.rewAux,formulaValue,ihp σ h hc hb hf,ihq σ h hc hb hf]
  | @all s p ih =>
    have henv : EnvironmentsValid ((r+1:Nat):V) (n+1) (bindBound b) (bindFree f) := by
      simpa only [Nat.cast_add,Nat.cast_one] using bindEnvironments_valid h
    have hc' : IsSemitermVec L ((s+1:Nat):V) (n+1) (bindBound c) := by
      simpa only [Nat.cast_add,Nat.cast_one,bindBound] using (NumericPAeqTerm.shiftTerms_isSemitermVec hc).adjoin (show IsSemiterm L (n+1) (qqBvar 0) by simp)
    have hf' : ∀j i,((Semiterm.bvar 0 : Term (r+1)) :> (Rew.bShift ∘ σ) $ j).FVar? i→(i:V)<len (bindFree f) := by
      intro j i hi
      cases j using Fin.cases with
      | zero => simp at hi
      | succ j => simpa [bindFree,NumericPAeqTerm.shiftTerms_length h.2] using hf j i (by simpa using hi)
    simp only [Semiformula.rewAux,Rew.q_subst,formulaValue]
    rw [ih _ henv hc' (sourceSubst_bind_agreement σ h hc hb hf) hf']
  | @exs s p ih =>
    have henv : EnvironmentsValid ((r+1:Nat):V) (n+1) (bindBound b) (bindFree f) := by
      simpa only [Nat.cast_add,Nat.cast_one] using bindEnvironments_valid h
    have hc' : IsSemitermVec L ((s+1:Nat):V) (n+1) (bindBound c) := by
      simpa only [Nat.cast_add,Nat.cast_one,bindBound] using (NumericPAeqTerm.shiftTerms_isSemitermVec hc).adjoin (show IsSemiterm L (n+1) (qqBvar 0) by simp)
    have hf' : ∀j i,((Semiterm.bvar 0 : Term (r+1)) :> (Rew.bShift ∘ σ) $ j).FVar? i→(i:V)<len (bindFree f) := by
      intro j i hi
      cases j using Fin.cases with
      | zero => simp at hi
      | succ j => simpa [bindFree,NumericPAeqTerm.shiftTerms_length h.2] using hf j i (by simpa using hi)
    simp only [Semiformula.rewAux,Rew.q_subst,formulaValue]
    rw [ih _ henv hc' (sourceSubst_bind_agreement σ h hc hb hf) hf']

theorem formulaValue_sourceSubst_one (p : Formula 1) (t : Term 0) {n P f : V}
    (hf : IsSemitermVec L (len f) n f) (ht : ∀i,t.FVar? i→(i:V)<len f) :
    formulaValue (p/[t]) P 0 f=formulaValue p P (termValue t 0 f ∷ 0) f := by
  have h : EnvironmentsValid (0:V) n 0 f := ⟨by simp,hf⟩
  apply formulaValue_sourceSubst p ![t] (by simpa using h)
    (by simpa using IsSemitermVec.singleton.mpr (termValue_isSemiterm t (by simpa using h) ht))
  · intro i; fin_cases i; simp
  · intro j; fin_cases j; simpa using ht

#print axioms atomValue_sourceSubst
#print axioms formulaValue_sourceSubst
#print axioms formulaValue_sourceSubst_one
end M6.PA.RelationalPredicateTemplate

