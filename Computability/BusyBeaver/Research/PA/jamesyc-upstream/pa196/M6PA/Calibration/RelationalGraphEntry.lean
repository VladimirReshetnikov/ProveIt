module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPairSupplier
@[expose] public section

/-! Concrete graph entries and monotonicity under raw adjunction. Graph members
are real Kuratowski witnesses, not a replacement graph predicate. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def edge (g a b : Term n) : Formula n :=
  ∃¹ (mem (Rew.bShift g) (.bvar 0) ⋏
    kuratowski (.bvar 0) (Rew.bShift a) (Rew.bShift b))
def inclusion (g h : Term n) : Formula n :=
  ∀¹ ∀¹ sourceImply (edge (Rew.bShift (Rew.bShift g)) (.bvar 1) (.bvar 0))
    (edge (Rew.bShift (Rew.bShift h)) (.bvar 1) (.bvar 0))

macro "graphSyntax" : tactic => `(tactic|
  (simp only [edge,inclusion,kuratowskiExists,adjunction,singleton,pair,kuratowski,
    mem,eq,sourceIff,sourceImply,Semiformula.shift,Semiformula.free,
    Rewriting.shift,Rewriting.free,Rewriting.subst,app_eq_rewAux,
    Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq];
    finishSourceSyntax))

def edgeFromEntry {Γ : List Form} (g a b p : Nat)
    (hm : ND.Proof Γ (mem (.fvar g) (.fvar p)))
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar a) (.fvar b))) :
    ND.Proof Γ (edge (.fvar g) (.fvar a) (.fvar b)) := by
  apply exsIntro _ (.fvar p)
  convert andIntro hm hp using 1 ; graphSyntax

def adjunctionPreservesEdge {Γ : List Form} (g p h a b : Nat)
    (ha : ND.Proof Γ (adjunction (.fvar g) (.fvar p) (.fvar h)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar a) (.fvar b))) :
    ND.Proof Γ (edge (.fvar h) (.fvar a) (.fvar b)) := by
  apply exsElim he
  let σ : Formula 1 := mem (.fvar g) (.bvar 0) ⋏ kuratowski (.bvar 0) (.fvar a) (.fvar b)
  let C := σ.free :: shifted Γ
  have hh : ND.Proof C (mem (.fvar (g+1)) (.fvar 0) ⋏
      kuratowski (.fvar 0) (.fvar (a+1)) (.fvar (b+1))) := by
    have h0 : ND.Proof C σ.free := assumption (by simp [C])
    convert h0 using 1 ; dsimp [σ] ; graphSyntax
  have hi := adjunctionAt (g+1) (p+1) (h+1) 0 (up (adjunctionShift g p h ha) σ.free)
  have hm := mp (ND.orLeft (andLeft hh)) (andRight hi)
  have out := edgeFromEntry (h+1) (a+1) (b+1) 0 hm (andRight hh)
  convert out using 1 <;> (dsimp [C,σ] <;> graphSyntax)

def adjunctionInclusion {Γ : List Form} (g p h : Nat)
    (ha : ND.Proof Γ (adjunction (.fvar g) (.fvar p) (.fvar h))) :
    ND.Proof Γ (inclusion (.fvar g) (.fvar h)) := by
  apply allIntro
  apply allIntro
  have ha' := adjunctionShift (g+1) (p+1) (h+1) (adjunctionShift g p h ha)
  have result : ND.Proof (shifted (shifted Γ))
      (sourceImply (edge (.fvar (g+1+1)) (.fvar 1) (.fvar 0))
        (edge (.fvar (h+1+1)) (.fvar 1) (.fvar 0))) := by
    apply impIntro
    exact adjunctionPreservesEdge (g+1+1) (p+1+1) (h+1+1) 1 0
      (up ha' _) (assumption (by simp))
  convert result using 1 ; graphSyntax

#print axioms edgeFromEntry
#print axioms adjunctionPreservesEdge
#print axioms adjunctionInclusion
end M6.PA.RelationalSource.PairGraph
