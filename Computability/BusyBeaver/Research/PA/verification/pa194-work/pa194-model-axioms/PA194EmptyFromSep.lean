import PA194FoundationOrdinalInductionUniform
namespace M6.PA.RelationalSource.Ordinal
open LO LO.FirstOrder ND

def emptyFromFalseSeparation : ND.Proof [separationFormula (⊥ : Formula 1)] emptyFormula := by
  let Γ : List Form := [separationFormula (⊥ : Formula 1)]
  have hs : ND.Proof Γ (separationFormula (⊥ : Formula 1)) := assumption (by simp [Γ])
  have hex := predicateTraceFromSeparation (⊥ : Formula 1) 0 hs
  apply exsElim hex
  let σ : Formula 1 := predicateTrace (⊥ : Formula 1) (Rew.bShift (.fvar 0)) (.bvar 0)
  let Δ : List Form := σ.free :: shifted Γ
  have hσ : ND.Proof Δ (predicateTrace (⊥ : Formula 1) (.fvar 1) (.fvar 0)) := by
    have h : ND.Proof Δ σ.free := assumption (by simp [Δ])
    convert h using 1
    dsimp [σ]
    traceSyntax
    finishSourceSyntax
  have he : ND.Proof Δ (∃⁰ ∀⁰ (notMemAtom 1 0)) := by
    apply exsIntro (∀⁰ notMemAtom 1 0) (.fvar 0)
    apply allIntro
    let tr : Form := predicateTrace (⊥ : Formula 1) (.fvar 2) (.fvar 1)
    have ht : ND.Proof (shifted Δ) tr := by
      have h := shiftProof hσ
      convert h using 1
      simp only [tr]
      traceSyntax
      finishSourceSyntax
    have hi := predicateTraceAt (⊥ : Formula 1) 2 1 0 ht
    have hf := andLeft hi
    apply byContradiction
    let n : Form := ∼(Semiformula.rewAux (Rew.subst ![.fvar 0]).q (notMemAtom 1 0)).free
    change ND.Proof (n :: shifted Δ) ⊥
    have hn : ND.Proof (n :: shifted Δ) n := assumption (by simp)
    have hm : ND.Proof (n :: shifted Δ) (ND.mem (.fvar 1) (.fvar 0)) := by
      convert hn using 1
      dsimp [n,Semiformula.free,Rewriting.free,Rewriting.shift,Rewriting.subst,app_eq_rewAux,
        Semiformula.rewAux,Semiformula.neg,Semiformula.neg_eq,notMemAtom,ND.mem]
      finishSourceSyntax
    have hforward : ND.Proof (shifted Δ) (ND.mem (.fvar 1) (.fvar 0) 🡒
        (ND.mem (.fvar 2) (.fvar 0) ⋏ ⊥)) := by
      change ND.Proof (shifted Δ) (sourceImply (ND.mem (.fvar 1) (.fvar 0)) (ND.mem (.fvar 2) (.fvar 0) ⋏ ⊥))
      simpa [Rewriting.subst,app_eq_rewAux,Semiformula.rewAux] using hf
    exact andRight (mp hm (up hforward n))
  convert he using 1
  simp [emptyFormula, Semiformula.shift, Rewriting.shift, app_eq_rewAux, Semiformula.rewAux, notMemAtom, Function.comp_def]
  finishSourceSyntax
#print axioms emptyFromFalseSeparation
end M6.PA.RelationalSource.Ordinal
