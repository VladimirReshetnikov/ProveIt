import PA194FoundationAdjunctionExistence
namespace M6.PA.RelationalSource
open LO LO.FirstOrder
namespace ND

/-- Membership transport is derived from the literal equality-base formulas.
No extensionality or equality-vacuity axiom is inserted. -/
def transportFromEquality {Γ : List Form} (b w : Term)
    (reflexive : Proof Γ reflexivityFormula) (symmetric : Proof Γ symmetryFormula)
    (congruent : Proof Γ congruenceFormula) : Proof Γ (transportFormula b w) := by
  cases b with
  | bvar i => nomatch i
  | func f _ => nomatch f
  | fvar bi =>
    cases w with
    | bvar i => nomatch i
    | func f _ => nomatch f
    | fvar wi =>
      apply allIntro
      let x : Term := .fvar 0
      let b' : Term := .fvar (bi+1)
      let w' : Term := .fvar (wi+1)
      have hr := allElim _ w' (shiftProof reflexive)
      have hs := allElim _ b' (allElim _ x (shiftProof symmetric))
      have hg := allElim _ w' (allElim _ x (allElim _ w' (allElim _ b' (shiftProof congruent))))
      have hr' : Proof (shifted Γ) (eq w' w') := by
        convert hr using 1 <;> dsimp [reflexivityFormula,eqAtom,w'] <;> sourceSyntaxEq
      have hs' : Proof (shifted Γ) (eq x b' 🡒 eq b' x) := by
        convert hs using 1 <;> dsimp [symmetryFormula,eqAtom,notEqAtom,x,b'] <;> sourceSyntaxEq
      have hg' : Proof (shifted Γ) (eq b' x 🡒 eq w' w' 🡒 mem w' b' 🡒 mem w' x) := by
        convert hg using 1 <;>
          dsimp [congruenceFormula,eqAtom,notEqAtom,memAtom,notMemAtom,x,b',w'] <;> sourceSyntaxEq
      have h : Proof (shifted Γ) (eq x b' 🡒 mem w' b' 🡒 mem w' x) := by
        apply impIntro
        apply impIntro
        let he : Proof (mem w' b' :: eq x b' :: shifted Γ) (eq b' x) :=
          mp (assumption (by simp)) (weaken hs' (by intro y hy; simp [hy]))
        exact mp (assumption (by simp))
          (mp (weaken hr' (by intro y hy; simp [hy]))
            (mp he (weaken hg' (by intro y hy; simp [hy]))))
      change Proof (shifted Γ) (Semiformula.rewAux Rew.free
        (eq (.bvar 0) (Rew.bShift (.fvar bi)) 🡒 mem (Rew.bShift (.fvar wi)) (Rew.bShift (.fvar bi)) 🡒
          mem (Rew.bShift (.fvar wi)) (.bvar 0)))
      convert h using 1 <;> dsimp [x,b',w'] <;> sourceSyntaxEq

#print axioms transportFromEquality
end ND
end M6.PA.RelationalSource
