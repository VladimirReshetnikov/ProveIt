import PA194FoundationAdjunctionEquality
namespace M6.PA.RelationalSource
open LO LO.FirstOrder
namespace ND

def transportAllFromEquality {Γ : List Form} (b : Term)
    (reflexive : Proof Γ reflexivityFormula) (symmetric : Proof Γ symmetryFormula)
    (congruent : Proof Γ congruenceFormula) : Proof Γ (transportAll b) := by
  cases b with
  | bvar i => nomatch i
  | func f _ => nomatch f
  | fvar bi =>
    apply allIntro
    have hr : Proof (shifted Γ) reflexivityFormula := by
      convert shiftProof reflexive using 1 <;> dsimp [reflexivityFormula,eqAtom] <;> sourceSyntaxEq
    have hs : Proof (shifted Γ) symmetryFormula := by
      convert shiftProof symmetric using 1 <;> dsimp [symmetryFormula,eqAtom,notEqAtom] <;> sourceSyntaxEq
    have hg : Proof (shifted Γ) congruenceFormula := by
      convert shiftProof congruent using 1 <;>
        dsimp [congruenceFormula,eqAtom,notEqAtom,memAtom,notMemAtom] <;> sourceSyntaxEq
    change Proof (shifted Γ) (Semiformula.rewAux Rew.free
      (transportFormula (Rew.bShift (.fvar bi)) (.bvar 0)))
    convert transportFromEquality (.fvar (bi+1)) (.fvar 0) hr hs hg using 1 <;> sourceSyntaxEq

def exactAdjunctionFromAxioms (a b : Term) :
    Proof (adjunctionAxioms a b) (adjunctionExists a b) := by
  cases a with
  | bvar i => nomatch i
  | func f _ => nomatch f
  | fvar ai =>
    cases b with
    | bvar i => nomatch i
    | func f _ => nomatch f
    | fvar bi =>
      apply exactAdjunction (.fvar ai) (.fvar bi)
      · have h := allElim _ (.fvar bi) (allElim _ (.fvar ai)
          (assumption (Γ := adjunctionAxioms (.fvar ai) (.fvar bi))
            (p := weakAdjunctionFormula) (by simp [adjunctionAxioms])))
        convert h using 1 <;> dsimp [weakAdjunctionFormula,memAtom] <;> sourceSyntaxEq
      · exact assumption (by simp [adjunctionAxioms])
      · exact transportAllFromEquality (.fvar bi)
          (assumption (by simp [adjunctionAxioms]))
          (assumption (by simp [adjunctionAxioms]))
          (assumption (by simp [adjunctionAxioms]))

#print axioms exactAdjunctionFromAxioms
end ND
end M6.PA.RelationalSource
