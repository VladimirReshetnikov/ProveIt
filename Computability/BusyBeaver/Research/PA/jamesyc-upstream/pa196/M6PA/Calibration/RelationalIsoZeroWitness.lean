module
public import M6PA.Theory
public import M6PA.Calibration.RelationalOrderIsoRules
@[expose] public section

/-! Typed total graph witnesses cannot connect a nonempty side to an empty
side. These are constructive existential eliminations, not cardinality facts. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def rightTotalZeroFalse {Γ : List Form} (g a b y : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar a)))
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (hr : ND.Proof Γ (graphRightTotal (.fvar g) (.fvar b)))
    (hy : ND.Proof Γ (mem (.fvar b) (.fvar y))) : ND.Proof Γ ⊥ := by
  apply exsElim (orderRightAt g b y hr hy)
  let σ : Formula 1 := edge (.fvar g) (.bvar 0) (.fvar y)
  let C := σ.free :: shifted Γ
  have he : ND.Proof C (edge (.fvar (g+1)) (.fvar 0) (.fvar (y+1))) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> isoSyntax)
  have hm := andLeft (orderTypedAt (g+1) (a+1) (b+1) 0 (y+1) (up (orderTypedShift g a b ht) σ.free) he)
  have bot := contradiction hm (Ordinal.zeroNotMem (a+1) 0 (up (Ordinal.zeroShift a hz) σ.free))
  exact bot

def leftTotalZeroFalse {Γ : List Form} (g a b x : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar b)))
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (hl : ND.Proof Γ (graphLeftTotal (.fvar g) (.fvar a)))
    (hx : ND.Proof Γ (mem (.fvar a) (.fvar x))) : ND.Proof Γ ⊥ := by
  apply exsElim (orderLeftAt g a x hl hx)
  let σ : Formula 1 := edge (.fvar g) (.fvar x) (.bvar 0)
  let C := σ.free :: shifted Γ
  have he : ND.Proof C (edge (.fvar (g+1)) (.fvar (x+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> isoSyntax)
  have hm := andRight (orderTypedAt (g+1) (a+1) (b+1) (x+1) 0 (up (orderTypedShift g a b ht) σ.free) he)
  exact contradiction hm (Ordinal.zeroNotMem (b+1) 0 (up (Ordinal.zeroShift b hz) σ.free))

#print axioms rightTotalZeroFalse
#print axioms leftTotalZeroFalse
end M6.PA.RelationalSource.PairGraph
