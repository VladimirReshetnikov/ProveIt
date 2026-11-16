module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoGreatestRules
public import M6PA.Calibration.RelationalGraphFunctionalExtension
@[expose] public section

/-! Greatest-image witnesses are obtained from actual right totality, not
from a surjectivity assumption about unrepresented objects. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Formula)

def imageGreatestAt {Γ : List Form} (E : FormulaEquality Γ) (g a b p q y : Nat)
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (hr : ND.Proof Γ (graphRightTotal (.fvar g) (.fvar b)))
    (hf : ND.Proof Γ (graphFunctional (.fvar g)))
    (ho : ND.Proof Γ (graphOrder (.fvar g)))
    (hp : ND.Proof Γ (Ordinal.greatest (.fvar a) (.fvar p)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar p) (.fvar q)))
    (hy : ND.Proof Γ (mem (.fvar b) (.fvar y))) :
    ND.Proof Γ (eq (.fvar y) (.fvar q) ⋎ mem (.fvar q) (.fvar y)) := by
  apply exsElim (orderRightAt g b y hr hy)
  let body : Formula 1 := edge (.fvar g) (.bvar 0) (.fvar y)
  let C := body.free :: shifted Γ
  have hx : ND.Proof C (edge (.fvar (g+1)) (.fvar 0) (.fvar (y+1))) := by
    have h : ND.Proof C body.free := assumption (by simp [C])
    convert h using 1 <;> (dsimp [body] <;> isoSyntax)
  have ee : ND.Proof C (edge (.fvar (g+1)) (.fvar (p+1)) (.fvar (q+1))) := by
    have h := up (shiftProof he) body.free
    convert h using 1 <;> isoSyntax
  have out := imageGreatestEdge (E.shifted.weaken (fun r hr => List.mem_cons_of_mem body.free hr))
    (g+1) (a+1) (b+1) (p+1) (q+1) 0 (y+1)
    (up (orderTypedShift g a b ht) body.free) (up (graphFunctionalShift g hf) body.free)
    (up (orderOrderShift g ho) body.free) (up (Ordinal.greatestShift a p hp) body.free) ee hx
  convert out using 1 <;> (dsimp [C,body] <;> isoSyntax)

def imageGreatest {Γ : List Form} (E : FormulaEquality Γ) (g a b p q : Nat)
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (hr : ND.Proof Γ (graphRightTotal (.fvar g) (.fvar b)))
    (hf : ND.Proof Γ (graphFunctional (.fvar g)))
    (ho : ND.Proof Γ (graphOrder (.fvar g)))
    (hp : ND.Proof Γ (Ordinal.greatest (.fvar a) (.fvar p)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar p) (.fvar q))) :
    ND.Proof Γ (Ordinal.greatest (.fvar b) (.fvar q)) := by
  apply andIntro (andRight (orderTypedAt g a b p q ht he))
  apply allIntro
  let premise : Form := mem (.fvar (b+1)) (.fvar 0)
  have ee : ND.Proof (premise::shifted Γ) (edge (.fvar (g+1)) (.fvar (p+1)) (.fvar (q+1))) := by
    have h := up (shiftProof he) premise
    convert h using 1 <;> isoSyntax
  have out := imageGreatestAt (E.shifted.weaken (fun r hr => List.mem_cons_of_mem premise hr))
    (g+1) (a+1) (b+1) (p+1) (q+1) 0
    (up (orderTypedShift g a b ht) premise) (up (orderRightShift g b hr) premise)
    (up (graphFunctionalShift g hf) premise) (up (orderOrderShift g ho) premise)
    (up (Ordinal.greatestShift a p hp) premise) ee (assumption (by simp [premise]))
  convert impIntro out using 1 <;> (dsimp [premise] <;> isoSyntax)

#print axioms imageGreatestAt
#print axioms imageGreatest
end M6.PA.RelationalSource.PairGraph
