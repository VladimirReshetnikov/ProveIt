import PA194OrderIsoGreatestExists
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula)

def noMemberOfIsoSource {Γ : List Form} (g a b x : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar b)))
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (hl : ND.Proof Γ (graphLeftTotal (.fvar g) (.fvar a))) :
    ND.Proof Γ (∼mem (.fvar a) (.fvar x)) := by
  apply byContradiction
  let C := ∼∼mem (.fvar a) (.fvar x) :: Γ
  have hx : ND.Proof C (mem (.fvar a) (.fvar x)) := by
    simpa [C] using (assumption (p := ∼∼mem (.fvar a) (.fvar x)) (by simp [C]))
  let hex := leftTotalAtLocal g a x (up hl _) hx
  apply exsElim hex
  let φ : Formula 1 := edge (.fvar g) (.fvar x) (.bvar 0)
  let D := φ.free :: shifted C
  have he : ND.Proof D (edge (.fvar (g+1)) (.fvar (x+1)) (.fvar 0)) := by
    have hd : ND.Proof D φ.free := assumption (by simp [D])
    convert hd using 1 <;> (dsimp [φ] <;> isoSyntax)
  have ht' : ND.Proof D (graphTyped (.fvar (g+1)) (.fvar (a+1)) (.fvar (b+1))) := by
    have hd := up (shiftProof (up ht (∼∼mem (.fvar a) (.fvar x)))) φ.free
    convert hd using 1 <;> isoSyntax
  have hz' : ND.Proof D (Ordinal.zero (.fvar (b+1))) := by
    have hd := up (shiftProof (up hz (∼∼mem (.fvar a) (.fvar x)))) φ.free
    convert hd using 1 <;> isoSyntax
  have hb := typedEdgeRight (g+1) (a+1) (b+1) (x+1) 0 ht' he
  have hn := zeroAt (b+1) 0 hz'
  convert contradiction hb hn using 1 <;> isoSyntax

def zeroFromBijectionReverse {Γ : List Form} (g a b : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar b)))
    (hb : ND.Proof Γ (orderBijection (.fvar g) (.fvar a) (.fvar b))) :
    ND.Proof Γ (Ordinal.zero (.fvar a)) := by
  have ht := andLeft (andRight hb)
  have hl := andLeft (andRight (andRight hb))
  have hz' : ND.Proof (shifted Γ) (Ordinal.zero (.fvar (b+1))) := by
    convert shiftProof hz using 1 <;> isoSyntax
  have ht' : ND.Proof (shifted Γ) (graphTyped (.fvar (g+1)) (.fvar (a+1)) (.fvar (b+1))) := by
    convert shiftProof ht using 1 <;> isoSyntax
  have hl' : ND.Proof (shifted Γ) (graphLeftTotal (.fvar (g+1)) (.fvar (a+1))) := by
    convert shiftProof hl using 1 <;> isoSyntax
  have hm := noMemberOfIsoSource (g+1) (a+1) (b+1) 0 hz' ht' hl'
  apply allIntro
  convert hm using 1 <;> isoSyntax

def zeroFromIsoReverse {Γ : List Form} (a b : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar b)))
    (hi : ND.Proof Γ (orderIso (.fvar a) (.fvar b))) :
    ND.Proof Γ (Ordinal.zero (.fvar a)) := by
  apply exsElim hi
  let φ : Formula 1 := orderBijection (.bvar 0) (.fvar a) (.fvar b)
  let D := φ.free :: shifted Γ
  have hb : ND.Proof D (orderBijection (.fvar 0) (.fvar (a+1)) (.fvar (b+1))) := by
    have hd : ND.Proof D φ.free := assumption (by simp [D])
    convert hd using 1 <;> (dsimp [φ] <;> isoSyntax)
  have hz' : ND.Proof D (Ordinal.zero (.fvar (b+1))) := by
    have hd := up (shiftProof hz) φ.free
    convert hd using 1 <;> isoSyntax
  have out := zeroFromBijectionReverse 0 (a+1) (b+1) hz' hb
  convert out using 1 <;> isoSyntax
#print axioms noMemberOfIsoSource
#print axioms zeroFromBijectionReverse
#print axioms zeroFromIsoReverse
end M6.PA.RelationalSource.PairGraph
