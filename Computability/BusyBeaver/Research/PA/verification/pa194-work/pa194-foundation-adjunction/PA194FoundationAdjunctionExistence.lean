import PA194FoundationAdjunctionLogic
namespace M6.PA.RelationalSource
open LO LO.FirstOrder
namespace ND

def weakInstance (a b : Semiterm language Nat n) : Semiproposition language n :=
  ∃⁰ (coverFormula (Rew.bShift a) (.bvar 0) ⋏ mem (.bvar 0) (Rew.bShift b))
def transportAll (b : Semiterm language Nat n) : Semiproposition language n :=
  ∀⁰ transportFormula (Rew.bShift b) (.bvar 0)
def separationExists (a b w : Semiterm language Nat n) : Semiproposition language n :=
  ∃⁰ separationInstance (Rew.bShift a) (Rew.bShift b) (Rew.bShift w) (.bvar 0)

def up {Γ : List Form} {p : Form} (d : Proof Γ p) (q : Form) : Proof (q::Γ) p :=
  weaken d (by intro x hx; simp [hx])

macro "finishSourceSyntax" : tactic => `(tactic|
  repeat' first
    | rfl
    | (funext i; exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i)
    | (change Semiformula.and _ _ = Semiformula.and _ _; congr 1)
    | (change Semiformula.or _ _ = Semiformula.or _ _; congr 1)
    | (change Semiformula.all _ = Semiformula.all _; congr 1)
    | (change Semiformula.exs _ = Semiformula.exs _; congr 1)
    | (change Semiformula.rel _ _ = Semiformula.rel _ _; congr 1)
    | (change Semiformula.nrel _ _ = Semiformula.nrel _ _; congr 1))

macro "sourceSyntaxEq" : tactic => `(tactic|
  (simp only [weakInstance,separationAll,transportAll,adjunctionExists,separationExists,
    coverFormula,transportFormula,separationInstance,adjunctionInstance,
    mem,eq,property,sourceIff,sourceImply,Semiformula.shift,Semiformula.free,
    Rewriting.shift,Rewriting.free,Rewriting.subst,app_eq_rewAux,
    Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq];
   finishSourceSyntax))

/-- Both existential witnesses are handled by Foundation's eigenvariable
rule, rather than choosing a set in Lean's ambient semantics. -/
def filterSeparation {Γ : List Form} (a b w : Term)
    (cover : Proof Γ (coverFormula a w)) (point : Proof Γ (mem w b))
    (transport : Proof Γ (transportFormula b w))
    (sep : Proof Γ (separationExists a b w)) : Proof Γ (adjunctionExists a b) := by
  cases a with
  | bvar i => nomatch i
  | func f _ => nomatch f
  | fvar ai =>
    cases b with
    | bvar i => nomatch i
    | func f _ => nomatch f
    | fvar bi =>
      cases w with
      | bvar i => nomatch i
      | func f _ => nomatch f
      | fvar wi =>
        apply exsElim sep
        apply exsIntro _ (.fvar 0)
        let σ : Semiproposition language 1 := separationInstance (Rew.bShift (.fvar ai)) (Rew.bShift (.fvar bi))
          (Rew.bShift (.fvar wi)) (.bvar 0)
        let C := σ.free :: shifted Γ
        have hc : Proof C (coverFormula (.fvar (ai+1)) (.fvar (wi+1))) := by
          have h := up (shiftProof cover) σ.free
          change Proof C (Semiformula.rewAux Rew.shift (coverFormula (.fvar ai) (.fvar wi))) at h
          convert h using 1 <;> sourceSyntaxEq
        have hp : Proof C (mem (.fvar (wi+1)) (.fvar (bi+1))) := by
          have h := up (shiftProof point) σ.free
          change Proof C (Semiformula.rewAux Rew.shift (mem (.fvar wi) (.fvar bi))) at h
          convert h using 1 <;> sourceSyntaxEq
        have ht : Proof C (transportFormula (.fvar (bi+1)) (.fvar (wi+1))) := by
          have h := up (shiftProof transport) σ.free
          change Proof C (Semiformula.rewAux Rew.shift (transportFormula (.fvar bi) (.fvar wi))) at h
          convert h using 1 <;> sourceSyntaxEq
        have hs : Proof C (separationInstance (.fvar (ai+1)) (.fvar (bi+1)) (.fvar (wi+1)) (.fvar 0)) := by
          have h : Proof C σ.free := assumption (by simp [C])
          change Proof C (Semiformula.rewAux Rew.free σ) at h
          convert h using 1 <;> dsimp [σ] <;> sourceSyntaxEq
        change Proof C (Semiformula.rewAux (Rew.subst ![Semiterm.fvar 0])
          (Semiformula.rewAux (Rew.q Rew.shift)
            (adjunctionInstance (Rew.bShift (.fvar ai)) (Rew.bShift (.fvar bi)) (.bvar 0))))
        convert filterContainer (.fvar (ai+1)) (.fvar (bi+1)) (.fvar (wi+1)) (.fvar 0) hc hp ht hs using 1 <;>
          sourceSyntaxEq

def exactAdjunction {Γ : List Form} (a b : Term)
    (weak : Proof Γ (weakInstance a b)) (sep : Proof Γ (separationAll a b))
    (transport : Proof Γ (transportAll b)) : Proof Γ (adjunctionExists a b) := by
  cases a with
  | bvar i => nomatch i
  | func f _ => nomatch f
  | fvar ai =>
    cases b with
    | bvar i => nomatch i
    | func f _ => nomatch f
    | fvar bi =>
      apply exsElim weak
      let σ : Semiproposition language 1 := coverFormula (Rew.bShift (.fvar ai)) (.bvar 0) ⋏ mem (.bvar 0) (Rew.bShift (.fvar bi))
      let C := σ.free :: shifted Γ
      have hw : Proof C σ.free := assumption (by simp [C])
      have hc : Proof C (coverFormula (.fvar (ai+1)) (.fvar 0)) := by
        have h := andLeft hw
        change Proof C (Semiformula.rewAux Rew.free (coverFormula (Rew.bShift (.fvar ai)) (.bvar 0))) at h
        convert h using 1 <;> sourceSyntaxEq
      have hp : Proof C (mem (.fvar 0) (.fvar (bi+1))) := by
        have h := andRight hw
        change Proof C (Semiformula.rewAux Rew.free (mem (.bvar 0) (Rew.bShift (.fvar bi)))) at h
        convert h using 1 <;> sourceSyntaxEq
      have ht : Proof C (transportFormula (.fvar (bi+1)) (.fvar 0)) := by
        have h := allElim _ (.fvar 0) (up (shiftProof transport) σ.free)
        change Proof C (Semiformula.rewAux (Rew.subst ![Semiterm.fvar 0])
          (Semiformula.rewAux (Rew.q Rew.shift) (transportFormula (Rew.bShift (.fvar bi)) (.bvar 0)))) at h
        convert h using 1 <;> sourceSyntaxEq
      have hs : Proof C (separationExists (.fvar (ai+1)) (.fvar (bi+1)) (.fvar 0)) := by
        have h := allElim _ (.fvar 0) (up (shiftProof sep) σ.free)
        change Proof C (Semiformula.rewAux (Rew.subst ![Semiterm.fvar 0])
          (Semiformula.rewAux (Rew.q Rew.shift)
            (.exs (separationInstance (Rew.bShift (Rew.bShift (.fvar ai)))
              (Rew.bShift (Rew.bShift (.fvar bi))) (.bvar 1) (.bvar 0))))) at h
        convert h using 1 <;> sourceSyntaxEq
      change Proof C (Semiformula.rewAux Rew.shift (adjunctionExists (.fvar ai) (.fvar bi)))
      convert filterSeparation (.fvar (ai+1)) (.fvar (bi+1)) (.fvar 0) hc hp ht hs using 1 <;>
        sourceSyntaxEq

#print axioms filterSeparation
#print axioms exactAdjunction
end ND
end M6.PA.RelationalSource

