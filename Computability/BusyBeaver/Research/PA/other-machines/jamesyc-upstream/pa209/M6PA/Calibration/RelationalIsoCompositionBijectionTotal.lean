module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoCompositionRealizeEdge
public import M6PA.Calibration.RelationalIsoCompositionEdgeRightTotal
@[expose] public section

/-! Both totality directions for the actual finite composition graph. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def compositionLeftAt {Γ : List Form} (g h a k x : Nat)
    (hc : ND.Proof Γ (compositionCoverage (.fvar g) (.fvar h) (.fvar a) (.fvar k)))
    (hx : ND.Proof Γ (mem (.fvar a) (.fvar x))) :
    ND.Proof Γ (∃¹ edge (.fvar k) (.fvar x) (.bvar 0)) := by
  apply exsElim (compositionCoverageAt g h a k x hc hx)
  let σ : Formula 1 := edge (.fvar k) (.fvar x) (.bvar 0) ⋏ compositionEdge (.fvar g) (.fvar h) (.fvar x) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hh : ND.Proof C (edge (.fvar (k+1)) (.fvar (x+1)) (.fvar 0) ⋏
      compositionEdge (.fvar (g+1)) (.fvar (h+1)) (.fvar (x+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> compositionSyntax)
  have out : ND.Proof C (∃¹ edge (.fvar (k+1)) (.fvar (x+1)) (.bvar 0)) := by
    apply exsIntro _ (.fvar 0)
    convert andLeft hh using 1 <;> compositionSyntax
  convert out using 1 <;> (dsimp [C,σ] <;> compositionSyntax)

def compositionRightAt {Γ : List Form} (E : FormulaEquality Γ) (g h a b c k z : Nat)
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (hu : ND.Proof Γ (graphTyped (.fvar h) (.fvar b) (.fvar c)))
    (fg : ND.Proof Γ (graphFunctional (.fvar g)))
    (fh : ND.Proof Γ (graphFunctional (.fvar h)))
    (rg : ND.Proof Γ (graphRightTotal (.fvar g) (.fvar b)))
    (rh : ND.Proof Γ (graphRightTotal (.fvar h) (.fvar c)))
    (hc : ND.Proof Γ (compositionCoverage (.fvar g) (.fvar h) (.fvar a) (.fvar k)))
    (hz : ND.Proof Γ (mem (.fvar c) (.fvar z))) :
    ND.Proof Γ (∃¹ edge (.fvar k) (.bvar 0) (.fvar z)) := by
  apply exsElim (compositionInputAt g h b c z hu rg rh hz)
  let σ : Formula 1 := compositionEdge (.fvar g) (.fvar h) (.bvar 0) (.fvar z)
  let C := σ.free :: shifted Γ
  have hh : ND.Proof C (compositionEdge (.fvar (g+1)) (.fvar (h+1)) (.fvar 0) (.fvar (z+1))) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> compositionSyntax)
  have gg : ND.Proof C (graphFunctional (.fvar (g+1))) := by
    convert up (shiftProof fg) σ.free using 1 <;> compositionSyntax
  have ff : ND.Proof C (graphFunctional (.fvar (h+1))) := by
    convert up (shiftProof fh) σ.free using 1 <;> compositionSyntax
  have hx := andLeft (compositionEdgeTyped (g+1) (h+1) (a+1) (b+1) (c+1) 0 (z+1)
    (up (orderTypedShift g a b ht) σ.free) (up (orderTypedShift h b c hu) σ.free) hh)
  have he := compositionRealizeEdge (E.shifted.weaken (fun p hp => List.mem_cons_of_mem σ.free hp))
    (g+1) (h+1) (a+1) (k+1) 0 (z+1) gg ff (up (compositionCoverageShift g h a k hc) σ.free) hx hh
  have out : ND.Proof C (∃¹ edge (.fvar (k+1)) (.bvar 0) (.fvar (z+1))) := by
    apply exsIntro _ (.fvar 0)
    convert he using 1 <;> compositionSyntax
  convert out using 1 <;> (dsimp [C,σ] <;> compositionSyntax)

def compositionLeftTotal {Γ : List Form} (g h a k : Nat)
    (hc : ND.Proof Γ (compositionCoverage (.fvar g) (.fvar h) (.fvar a) (.fvar k))) :
    ND.Proof Γ (graphLeftTotal (.fvar k) (.fvar a)) := by
  apply allIntro
  let d : Form := mem (.fvar (a+1)) (.fvar 0)
  have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
  have out := compositionLeftAt (g+1) (h+1) (a+1) (k+1) 0 (up (compositionCoverageShift g h a k hc) d) hd
  convert impIntro out using 1 <;> (dsimp [d] <;> compositionSyntax)

def compositionRightTotal {Γ : List Form} (E : FormulaEquality Γ) (g h a b c k : Nat)
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (hu : ND.Proof Γ (graphTyped (.fvar h) (.fvar b) (.fvar c)))
    (fg : ND.Proof Γ (graphFunctional (.fvar g)))
    (fh : ND.Proof Γ (graphFunctional (.fvar h)))
    (rg : ND.Proof Γ (graphRightTotal (.fvar g) (.fvar b)))
    (rh : ND.Proof Γ (graphRightTotal (.fvar h) (.fvar c)))
    (hc : ND.Proof Γ (compositionCoverage (.fvar g) (.fvar h) (.fvar a) (.fvar k))) :
    ND.Proof Γ (graphRightTotal (.fvar k) (.fvar c)) := by
  apply allIntro
  let d : Form := mem (.fvar (c+1)) (.fvar 0)
  have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
  have gg : ND.Proof (shifted Γ) (graphFunctional (.fvar (g+1))) := by
    convert shiftProof fg using 1 <;> compositionSyntax
  have ff : ND.Proof (shifted Γ) (graphFunctional (.fvar (h+1))) := by
    convert shiftProof fh using 1 <;> compositionSyntax
  have out := compositionRightAt (E.shifted.weaken (fun p hp => List.mem_cons_of_mem d hp))
    (g+1) (h+1) (a+1) (b+1) (c+1) (k+1) 0 (up (orderTypedShift g a b ht) d)
    (up (orderTypedShift h b c hu) d) (up gg d) (up ff d)
    (up (orderRightShift g b rg) d) (up (orderRightShift h c rh) d) (up (compositionCoverageShift g h a k hc) d) hd
  convert impIntro out using 1 <;> (dsimp [d] <;> compositionSyntax)

#print axioms compositionLeftAt
#print axioms compositionRightAt
#print axioms compositionLeftTotal
#print axioms compositionRightTotal
end M6.PA.RelationalSource.PairGraph
