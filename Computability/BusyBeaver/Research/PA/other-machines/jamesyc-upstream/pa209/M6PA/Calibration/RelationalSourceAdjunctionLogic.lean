module
public import M6PA.Theory
public import M6PA.Calibration.RelationalSourceND
public import M6PA.Calibration.RelationalSourceRewritingAtoms
public import M6PA.Calibration.RelationalSourceSeparation
@[expose] public section

/-! Logical filtering step for exact adjunction. All results are actual
Foundation LK proof terms; the eventual set axiom suppliers remain separate. -/
namespace M6.PA.RelationalSource
open FFL FFL.FirstOrder
macro "finishSourceFormula" : tactic => `(tactic|
  repeat' first
    | rfl
    | (funext i; exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i)
    | (change Semiformula.and _ _ = Semiformula.and _ _; apply congrArg₂ (@Semiformula.and language Nat 0))
    | (change Semiformula.or _ _ = Semiformula.or _ _; apply congrArg₂ (@Semiformula.or language Nat 0))
    | (change @Semiformula.rel language Nat 0 2 Relation.mem _ = @Semiformula.rel language Nat 0 2 Relation.mem _; apply congrArg (@Semiformula.rel language Nat 0 2 Relation.mem))
    | (change @Semiformula.nrel language Nat 0 2 Relation.mem _ = @Semiformula.nrel language Nat 0 2 Relation.mem _; apply congrArg (@Semiformula.nrel language Nat 0 2 Relation.mem))
    | (change @Semiformula.rel language Nat 0 2 Relation.eq _ = @Semiformula.rel language Nat 0 2 Relation.eq _; apply congrArg (@Semiformula.rel language Nat 0 2 Relation.eq))
    | (change @Semiformula.nrel language Nat 0 2 Relation.eq _ = @Semiformula.nrel language Nat 0 2 Relation.eq _; apply congrArg (@Semiformula.nrel language Nat 0 2 Relation.eq)))
namespace ND

def shiftProof {Γ : List Form} {p : Form} (d : Proof Γ p) : Proof (shifted Γ) p.shift :=
  d.shift.cast (by simp [negatives_shifted,Rewriting.shifts])

def filterPoint {Γ : List Form} {p q r s t : Form}
    (cover : Proof Γ (p 🡒 r)) (point : Proof Γ t)
    (transport : Proof Γ (q 🡒 t 🡒 r))
    (separation : Proof Γ ((s 🡒 r ⋏ (p ⋎ q)) ⋏ ((r ⋏ (p ⋎ q)) 🡒 s))) :
    Proof Γ ((s 🡒 (p ⋎ q)) ⋏ ((p ⋎ q) 🡒 s)) := by
  let fw : Proof Γ (s 🡒 (p ⋎ q)) := impIntro <|
    andRight (mp (assumption (by simp)) (weaken (andLeft separation) (by intro y hy; simp [hy])))
  let hp : Proof (p::p ⋎ q::Γ) r :=
    mp (assumption (by simp)) (weaken cover (by intro y hy; simp [hy]))
  let hq : Proof (q::p ⋎ q::Γ) r :=
    mp (weaken point (by intro y hy; simp [hy])) (mp (assumption (by simp)) (weaken transport (by intro y hy; simp [hy])))
  let hr : Proof (p ⋎ q::Γ) r := orElim (assumption (by simp)) hp hq
  let bw : Proof Γ ((p ⋎ q) 🡒 s) := impIntro <|
    mp (andIntro hr (assumption (by simp))) (weaken (andRight separation) (by intro y hy; simp [hy]))
  exact andIntro fw bw

abbrev Term := Semiterm language Nat 0

def mem (a x : Semiterm language Nat n) : Semiproposition language n := .rel .mem ![x,a]
def eq (x y : Semiterm language Nat n) : Semiproposition language n := .rel .eq ![x,y]
def property (a b x : Semiterm language Nat n) := mem a x ⋎ eq x b

def coverFormula (a w : Semiterm language Nat n) : Semiproposition language n :=
  ∀¹ (mem (Rew.bShift a) (.bvar 0) 🡒 mem (Rew.bShift w) (.bvar 0))
def transportFormula (b w : Semiterm language Nat n) : Semiproposition language n :=
  ∀¹ (eq (.bvar 0) (Rew.bShift b) 🡒
    mem (Rew.bShift w) (Rew.bShift b) 🡒 mem (Rew.bShift w) (.bvar 0))
def separationInstance (a b w c : Semiterm language Nat n) : Semiproposition language n :=
  ∀¹ sourceIff (mem (Rew.bShift c) (.bvar 0))
    (mem (Rew.bShift w) (.bvar 0) ⋏ property (Rew.bShift a) (Rew.bShift b) (.bvar 0))
def adjunctionInstance (a b c : Semiterm language Nat n) : Semiproposition language n :=
  ∀¹ sourceIff (mem (Rew.bShift c) (.bvar 0))
    (property (Rew.bShift a) (Rew.bShift b) (.bvar 0))

/-- Quantified exact membership after filtering a weak container. -/
def filterContainer {Γ : List Form} (a b w c : Term)
    (cover : Proof Γ (coverFormula a w)) (point : Proof Γ (mem w b))
    (transport : Proof Γ (transportFormula b w))
    (separation : Proof Γ (separationInstance a b w c)) :
    Proof Γ (adjunctionInstance a b c) := by
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
        cases c with
        | bvar i => nomatch i
        | func f _ => nomatch f
        | fvar ci =>
          apply allIntro
          have hc := allElim _ (.fvar 0) (shiftProof cover)
          have ht := allElim _ (.fvar 0) (shiftProof transport)
          have hs := allElim _ (.fvar 0) (shiftProof separation)
          have hp := shiftProof point
          change Proof (shifted Γ) (Semiformula.rewAux (Rew.subst ![Semiterm.fvar 0])
            (Semiformula.rewAux (Rew.q Rew.shift)
              (mem (Rew.bShift (.fvar ai)) (.bvar 0) 🡒 mem (Rew.bShift (.fvar wi)) (.bvar 0)))) at hc
          change Proof (shifted Γ) (Semiformula.rewAux (Rew.subst ![Semiterm.fvar 0])
            (Semiformula.rewAux (Rew.q Rew.shift)
              (eq (.bvar 0) (Rew.bShift (.fvar bi)) 🡒
                mem (Rew.bShift (.fvar wi)) (Rew.bShift (.fvar bi)) 🡒
                mem (Rew.bShift (.fvar wi)) (.bvar 0)))) at ht
          change Proof (shifted Γ) (Semiformula.rewAux (Rew.subst ![Semiterm.fvar 0])
            (Semiformula.rewAux (Rew.q Rew.shift)
              (sourceIff (mem (Rew.bShift (.fvar ci)) (.bvar 0))
                (mem (Rew.bShift (.fvar wi)) (.bvar 0) ⋏
                  property (Rew.bShift (.fvar ai)) (Rew.bShift (.fvar bi)) (.bvar 0))))) at hs
          change Proof (shifted Γ) (Semiformula.rewAux Rew.shift (mem (.fvar wi) (.fvar bi))) at hp
          have hc' : Proof (shifted Γ)
              (mem (.fvar (ai+1)) (.fvar 0) 🡒 mem (.fvar (wi+1)) (.fvar 0)) := by
            convert hc using 1 <;>
              simp only [mem,eq,property,sourceIff,sourceImply,Semiformula.shift,Semiformula.free,
                Rewriting.shift,Rewriting.free,Rewriting.subst,app_eq_rewAux,
                Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_rel,Semiformula.neg_nrel,Semiformula.neg_eq] <;>
              finishSourceFormula
          have ht' : Proof (shifted Γ)
              (eq (.fvar 0) (.fvar (bi+1)) 🡒 mem (.fvar (wi+1)) (.fvar (bi+1)) 🡒
                mem (.fvar (wi+1)) (.fvar 0)) := by
            convert ht using 1 <;>
              simp only [mem,eq,property,sourceIff,sourceImply,Semiformula.shift,Semiformula.free,
                Rewriting.shift,Rewriting.free,Rewriting.subst,app_eq_rewAux,
                Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_rel,Semiformula.neg_nrel,Semiformula.neg_eq] <;>
              finishSourceFormula
          have hs' : Proof (shifted Γ)
              (sourceIff (mem (.fvar (ci+1)) (.fvar 0))
                (mem (.fvar (wi+1)) (.fvar 0) ⋏ property (.fvar (ai+1)) (.fvar (bi+1)) (.fvar 0))) := by
            convert hs using 1 <;>
              simp only [mem,eq,property,sourceIff,sourceImply,Semiformula.shift,Semiformula.free,
                Rewriting.shift,Rewriting.free,Rewriting.subst,app_eq_rewAux,
                Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_rel,Semiformula.neg_nrel,Semiformula.neg_eq] <;>
              finishSourceFormula
          have hp' : Proof (shifted Γ) (mem (.fvar (wi+1)) (.fvar (bi+1))) := by
            convert hp using 1 <;>
              simp only [mem,eq,property,sourceIff,sourceImply,Semiformula.shift,Semiformula.free,
                Rewriting.shift,Rewriting.free,Rewriting.subst,app_eq_rewAux,
                Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_rel,Semiformula.neg_nrel,Semiformula.neg_eq] <;>
              finishSourceFormula
          change Proof (shifted Γ) (Semiformula.rewAux Rew.free
            (sourceIff (mem (Rew.bShift (.fvar ci)) (.bvar 0))
              (property (Rew.bShift (.fvar ai)) (Rew.bShift (.fvar bi)) (.bvar 0))))
          convert filterPoint hc' hp' ht' hs' using 1 <;>
              simp only [mem,eq,property,sourceIff,sourceImply,Semiformula.shift,Semiformula.free,
                Rewriting.shift,Rewriting.free,Rewriting.subst,app_eq_rewAux,
                Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_rel,Semiformula.neg_nrel,Semiformula.neg_eq] <;>
              finishSourceFormula

#print axioms filterPoint
#print axioms filterContainer
end ND
end M6.PA.RelationalSource

