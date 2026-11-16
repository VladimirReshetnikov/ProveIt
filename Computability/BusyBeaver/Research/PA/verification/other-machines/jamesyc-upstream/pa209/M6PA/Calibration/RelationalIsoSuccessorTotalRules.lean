module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoSuccessorTyped
public import M6PA.Calibration.RelationalGraphOutputExtension
@[expose] public section

/-! Real left and right witnesses persist under an exact graph extension. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Formula)

def inputIntro {Γ : List Form} (g x y : Nat)
    (he : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y))) :
    ND.Proof Γ (∃¹ edge (.fvar g) (.bvar 0) (.fvar y)) := by
  apply exsIntro _ (.fvar x)
  convert he using 1 <;> isoSyntax

def preservesInput {Γ : List Form} (g h a b y : Nat)
    (hx : ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar a) (.fvar b)))
    (he : ND.Proof Γ (∃¹ edge (.fvar g) (.bvar 0) (.fvar y))) :
    ND.Proof Γ (∃¹ edge (.fvar h) (.bvar 0) (.fvar y)) := by
  apply exsElim he
  let body : Formula 1 := edge (.fvar g) (.bvar 0) (.fvar y)
  let C := body.free :: shifted Γ
  have old : ND.Proof C (edge (.fvar (g+1)) (.fvar 0) (.fvar (y+1))) := by
    have v : ND.Proof C body.free := assumption (by simp [C])
    convert v using 1 <;> (dsimp [body] <;> isoSyntax)
  have out := inputIntro (h+1) 0 (y+1)
    (exactPreservesEdge (g+1) (h+1) (a+1) (b+1) 0 (y+1)
      (up (exactShift g h a b hx) body.free) old)
  convert out using 1 <;> (dsimp [C,body] <;> isoSyntax)

def successorLeftAt {Γ : List Form} (E : FormulaEquality Γ) (g h a b c x : Nat)
    (hg : ND.Proof Γ (graphLeftTotal (.fvar g) (.fvar a)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar c)))
    (hx : ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar a) (.fvar b)))
    (hm : ND.Proof Γ (mem (.fvar c) (.fvar x))) :
    ND.Proof Γ (hasOutput (.fvar h) (.fvar x)) := by
  apply orElim (mp hm (andLeft (Ordinal.successorAt a c x hs)))
  · let p : Form := mem (.fvar a) (.fvar x)
    exact preservesOutput g h a b x (up hx p)
      (orderLeftAt g a x (up hg p) (assumption (by simp [p])))
  · let p : Form := eq (.fvar x) (.fvar a)
    exact insertedOutput (E.weaken (fun q hq => List.mem_cons_of_mem p hq))
      g h a b x (up hx p) (assumption (by simp [p]))

def successorRightAt {Γ : List Form} (E : FormulaEquality Γ) (g h a b d y : Nat)
    (hg : ND.Proof Γ (graphRightTotal (.fvar g) (.fvar b)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar b) (.fvar d)))
    (hx : ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar a) (.fvar b)))
    (hm : ND.Proof Γ (mem (.fvar d) (.fvar y))) :
    ND.Proof Γ (∃¹ edge (.fvar h) (.bvar 0) (.fvar y)) := by
  apply orElim (mp hm (andLeft (Ordinal.successorAt b d y hs)))
  · let p : Form := mem (.fvar b) (.fvar y)
    exact preservesInput g h a b y (up hx p)
      (orderRightAt g b y (up hg p) (assumption (by simp [p])))
  · let p : Form := eq (.fvar y) (.fvar b)
    have hy : ND.Proof (p::Γ) p := assumption (by simp)
    let EE := E.weaken (fun q hq => List.mem_cons_of_mem p hq)
    have edgeNew := mp (ND.orRight (andIntro (EE.reflexive (.fvar a)) hy))
      (andRight (exactAt g h a b a y (up hx p)))
    exact inputIntro h a y edgeNew

#print axioms preservesInput
#print axioms successorLeftAt
#print axioms successorRightAt
end M6.PA.RelationalSource.PairGraph
