import PA194ModelAdjunctiveTheory
import PA194FoundationOrdinalInductionUniform
namespace M6.PA.RelationalSource.Ordinal
open LO LO.FirstOrder ND
open scoped LO.FirstOrder
open M6.PA.RelationalSource PA194ModelLogic
theorem relExt_syntax : (PA194RelExtTypedTranslation.sourceRelExt : Proposition M6.PA.RelationalSource.language) =
    ∀⁰ ∀⁰ ∀⁰ ∀⁰ ((eqAtom 0 2 ⋏ (eqAtom 1 3 ⋏ ⊤)) 🡒 (memAtom 1 0 🡒 memAtom 3 2)) := by
  change Semiformula.rewAux Rew.emb PA194RelExtTypedTranslation.sourceRelExt = _
  simp [PA194RelExtTypedTranslation.sourceRelExt, Theory.Eq.relExt, allClosure_succ,
    Semiformula.rewAux, Semiformula.imp_eq, Semiformula.neg, eqAtom, memAtom, Matrix.conj, Function.comp_def]
  constructor
  · constructor
    · change Semiformula.rewAux Rew.emb (Semiformula.nrel Relation.eq ![#0,#2] : Semisentence M6.PA.RelationalSource.language 4) = _
      simp only [Semiformula.rewAux,Function.comp_def]
      congr 1
      funext i
      exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
    · change Semiformula.rewAux Rew.emb (Semiformula.nrel Relation.eq ![#1,#3] : Semisentence M6.PA.RelationalSource.language 4) = _
      simp only [Semiformula.rewAux,Function.comp_def]
      congr 1
      funext i
      exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
  · constructor <;> funext i <;> exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i


def relExtForm : Form := ∀⁰ ∀⁰ ∀⁰ ∀⁰
  ((eqAtom 0 2 ⋏ (eqAtom 1 3 ⋏ ⊤)) 🡒 (memAtom 1 0 🡒 memAtom 3 2))

def congruenceFromRelExt : ND.Proof [relExtForm] congruenceFormula := by
  let Γ : List Form := [relExtForm]
  have hroot : ND.Proof Γ relExtForm := assumption (by simp [Γ])
  apply allIntro
  apply allIntro
  apply allIntro
  apply allIntro
  let Δ := shifted (shifted (shifted (shifted Γ)))
  have hclosed : ND.Proof Δ relExtForm := by
    have h := shiftProof (shiftProof (shiftProof (shiftProof hroot)))
    convert h using 1
    simp only [relExtForm,eqAtom,memAtom]
    sourceSyntaxEq
  have hax := allElim _ (.fvar 3) (allElim _ (.fvar 2) (allElim _ (.fvar 1) (allElim _ (.fvar 0) hclosed)))
  have hax' : ND.Proof Δ ((ND.eq (.fvar 3) (.fvar 1) ⋏
      (ND.eq (.fvar 2) (.fvar 0) ⋏ ⊤)) 🡒 ND.mem (.fvar 2) (.fvar 3) 🡒 ND.mem (.fvar 0) (.fvar 1)) := by
    convert hax using 1
    dsimp [relExtForm,eqAtom,memAtom,ND.eq,ND.mem]
    sourceSyntaxEq
  have hmain : ND.Proof Δ (ND.eq (.fvar 3) (.fvar 1) 🡒 ND.eq (.fvar 2) (.fvar 0) 🡒
      ND.mem (.fvar 2) (.fvar 3) 🡒 ND.mem (.fvar 0) (.fvar 1)) := by
    apply impIntro
    apply impIntro
    apply impIntro
    let Θ : List Form := ND.mem (.fvar 2) (.fvar 3) :: ND.eq (.fvar 2) (.fvar 0) :: ND.eq (.fvar 3) (.fvar 1) :: Δ
    change ND.Proof Θ _
    have he1 : ND.Proof Θ (ND.eq (.fvar 3) (.fvar 1)) := assumption (by simp [Θ])
    have he2 : ND.Proof Θ (ND.eq (.fvar 2) (.fvar 0)) := assumption (by simp [Θ])
    have hm : ND.Proof Θ (ND.mem (.fvar 2) (.fvar 3)) := assumption (by simp [Θ])
    have ht : ND.Proof Θ ⊤ := closed LO.FirstOrder.Derivation.verum
    have hax'' := weaken hax' (Δ := Θ) (by intro q hq; simp [Θ, hq])
    exact mp hm (mp (andIntro he1 (andIntro he2 ht)) hax'')
  convert hmain using 1
  dsimp [congruenceFormula,eqAtom,notEqAtom,memAtom,notMemAtom,ND.eq,ND.mem]
  sourceSyntaxEq

#print axioms congruenceFromRelExt
end M6.PA.RelationalSource.Ordinal
