module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationCompactSyntax
public import M6PA.Calibration.RelationalMultiplicationPreviousIntro
@[expose] public section
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
set_option maxHeartbeats 600000
attribute [local irreducible] addResult addPrefix mulPrefix

def mulPreservePrevious {Γ : List Form} (g h a b base x y : Nat)
    (hx : ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar a) (.fvar b)))
    (hp : ND.Proof Γ (mulPrevious (.fvar g) (.fvar base) (.fvar x) (.fvar y))) :
    ND.Proof Γ (mulPrevious (.fvar h) (.fvar base) (.fvar x) (.fvar y)) := by
  apply exsElim hp
  let σ : Formula 1 := edge (.fvar g) (.fvar x) (.bvar 0) ⋏ addResult (.bvar 0) (.fvar base) (.fvar y)
  let C := σ.free :: shifted Γ
  have hc : ND.Proof C (edge (.fvar (g+1)) (.fvar (x+1)) (.fvar 0) ⋏
      addResult (.fvar 0) (.fvar (base+1)) (.fvar (y+1))) := by
    have h0 : ND.Proof C σ.free := assumption (by simp [C])
    convert h0 using 1 ; dsimp [σ]; mulCompactSyntax
  have he := exactPreservesEdge (g+1) (h+1) (a+1) (b+1) (x+1) 0
    (up (exactShift g h a b hx) σ.free) (andLeft hc)
  have out := mulPreviousIntro (h+1) (base+1) (x+1) (y+1) 0 he (andRight hc)
  convert out using 1 <;> (dsimp [C,σ] <;> mulCompactSyntax)

#print axioms mulPreservePrevious

end M6.PA.RelationalSource.PairGraph
