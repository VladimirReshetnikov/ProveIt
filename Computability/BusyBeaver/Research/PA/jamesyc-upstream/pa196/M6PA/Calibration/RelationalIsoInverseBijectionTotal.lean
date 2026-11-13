module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoInverseReverseEdge
@[expose] public section

/-! Both totality directions for the actual reversed graph. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def inverseLeftAt {Γ : List Form} (E : FormulaEquality Γ) (g a b h y : Nat)
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (hf : ND.Proof Γ (graphFunctional (.fvar g)))
    (hr : ND.Proof Γ (graphRightTotal (.fvar g) (.fvar b)))
    (hc : ND.Proof Γ (inverseCoverage (.fvar g) (.fvar a) (.fvar h)))
    (hm : ND.Proof Γ (mem (.fvar b) (.fvar y))) :
    ND.Proof Γ (∃¹ edge (.fvar h) (.fvar y) (.bvar 0)) := by
  apply exsElim (orderRightAt g b y hr hm)
  let σ : Formula 1 := edge (.fvar g) (.bvar 0) (.fvar y)
  let C := σ.free :: shifted Γ
  have hh : ND.Proof C (edge (.fvar (g+1)) (.fvar 0) (.fvar (y+1))) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> inverseSyntax)
  have ff : ND.Proof C (graphFunctional (.fvar (g+1))) := by
    convert up (shiftProof hf) σ.free using 1 <;> inverseSyntax
  have hx := andLeft (orderTypedAt (g+1) (a+1) (b+1) 0 (y+1) (up (orderTypedShift g a b ht) σ.free) hh)
  have he := inverseReverseEdge (E.shifted.weaken (fun p hp => List.mem_cons_of_mem σ.free hp))
    (g+1) (a+1) (h+1) 0 (y+1) ff (up (inverseCoverageShift g a h hc) σ.free) hx hh
  have out : ND.Proof C (∃¹ edge (.fvar (h+1)) (.fvar (y+1)) (.bvar 0)) := by
    apply exsIntro _ (.fvar 0)
    convert he using 1 <;> inverseSyntax
  convert out using 1 <;> (dsimp [C,σ] <;> inverseSyntax)

def inverseRightAt {Γ : List Form} (g a h x : Nat)
    (hc : ND.Proof Γ (inverseCoverage (.fvar g) (.fvar a) (.fvar h)))
    (hm : ND.Proof Γ (mem (.fvar a) (.fvar x))) :
    ND.Proof Γ (∃¹ edge (.fvar h) (.bvar 0) (.fvar x)) := by
  apply exsElim (inverseCoverageAt g a h x hc hm)
  let σ : Formula 1 := edge (.fvar h) (.bvar 0) (.fvar x) ⋏ edge (.fvar g) (.fvar x) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hh : ND.Proof C (edge (.fvar (h+1)) (.fvar 0) (.fvar (x+1)) ⋏
      edge (.fvar (g+1)) (.fvar (x+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> inverseSyntax)
  have out : ND.Proof C (∃¹ edge (.fvar (h+1)) (.bvar 0) (.fvar (x+1))) := by
    apply exsIntro _ (.fvar 0)
    convert andLeft hh using 1 <;> inverseSyntax
  convert out using 1 <;> (dsimp [C,σ] <;> inverseSyntax)

def inverseLeftTotal {Γ : List Form} (E : FormulaEquality Γ) (g a b h : Nat)
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (hf : ND.Proof Γ (graphFunctional (.fvar g)))
    (hr : ND.Proof Γ (graphRightTotal (.fvar g) (.fvar b)))
    (hc : ND.Proof Γ (inverseCoverage (.fvar g) (.fvar a) (.fvar h))) :
    ND.Proof Γ (graphLeftTotal (.fvar h) (.fvar b)) := by
  apply allIntro
  let d : Form := mem (.fvar (b+1)) (.fvar 0)
  have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
  have ff : ND.Proof (shifted Γ) (graphFunctional (.fvar (g+1))) := by
    convert shiftProof hf using 1 <;> inverseSyntax
  have out := inverseLeftAt (E.shifted.weaken (fun p hp => List.mem_cons_of_mem d hp))
    (g+1) (a+1) (b+1) (h+1) 0 (up (orderTypedShift g a b ht) d) (up ff d)
    (up (orderRightShift g b hr) d) (up (inverseCoverageShift g a h hc) d) hd
  convert impIntro out using 1 <;> (dsimp [d] <;> inverseSyntax)

def inverseRightTotal {Γ : List Form} (g a h : Nat)
    (hc : ND.Proof Γ (inverseCoverage (.fvar g) (.fvar a) (.fvar h))) :
    ND.Proof Γ (graphRightTotal (.fvar h) (.fvar a)) := by
  apply allIntro
  let d : Form := mem (.fvar (a+1)) (.fvar 0)
  have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
  have out := inverseRightAt (g+1) (a+1) (h+1) 0 (up (inverseCoverageShift g a h hc) d) hd
  convert impIntro out using 1 <;> (dsimp [d] <;> inverseSyntax)

#print axioms inverseLeftAt
#print axioms inverseRightAt
#print axioms inverseLeftTotal
#print axioms inverseRightTotal
end M6.PA.RelationalSource.PairGraph
