module
public import M6PA.Theory
public import M6PA.Calibration.RelationalKuratowskiTransport
@[expose] public section

/-! Exact pointwise classification of graph edges after adjoining a concrete
Kuratowski entry. The reverse direction and uniqueness are finite proofs. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula EqualityProofs eqRefl eqSymm equalityTransShift)

def classified (g a b x y : Term n) : Formula n :=
  edge g x y ⋎ (eq x a ⋏ eq y b)

def classifyEdge {Γ : List Form} (e : EqualityProofs Γ)
    (et : ND.Proof Γ transitivityFormula) (g p h a b x y : Nat)
    (ha : ND.Proof Γ (adjunction (.fvar g) (.fvar p) (.fvar h)))
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar a) (.fvar b)))
    (he : ND.Proof Γ (edge (.fvar h) (.fvar x) (.fvar y))) :
    ND.Proof Γ (classified (.fvar g) (.fvar a) (.fvar b) (.fvar x) (.fvar y)) := by
  apply exsElim he
  let σ : Formula 1 := mem (.fvar h) (.bvar 0) ⋏ kuratowski (.bvar 0) (.fvar x) (.fvar y)
  let C := σ.free :: shifted Γ
  have hc : ND.Proof C (mem (.fvar (h+1)) (.fvar 0) ⋏
      kuratowski (.fvar 0) (.fvar (x+1)) (.fvar (y+1))) := by
    have h0 : ND.Proof C σ.free := assumption (by simp [C])
    convert h0 using 1 ; dsimp [σ] ; graphSyntax
  let ee := e.shift.up σ.free
  have ett := up (equalityTransShift et) σ.free
  have hpp := up (kuratowskiShift p a b hp) σ.free
  have hai := adjunctionAt (g+1) (p+1) (h+1) 0 (up (adjunctionShift g p h ha) σ.free)
  have hm := mp (andLeft hc) (andLeft hai)
  have result : ND.Proof C (classified (.fvar (g+1)) (.fvar (a+1)) (.fvar (b+1))
      (.fvar (x+1)) (.fvar (y+1))) := by
    apply orElim hm
    · exact ND.orLeft (edgeFromEntry (g+1) (x+1) (y+1) 0
        (assumption (by simp)) (up (andRight hc) _))
    · have hk := kuratowskiContainer (ee.up (eq (.fvar 0) (.fvar (p+1)))) 0 (p+1) (x+1) (y+1)
        (assumption (by simp)) (up (andRight hc) _)
      exact ND.orRight (kuratowskiDecode (ee.up _) (up ett _) (p+1) (x+1) (y+1) (a+1) (b+1)
        hk (up hpp _))
  convert result using 1 <;> (dsimp [C,σ,classified] <;> graphSyntax)

def classifiedEdge {Γ : List Form} (e : EqualityProofs Γ)
    (et : ND.Proof Γ transitivityFormula) (g p h a b x y : Nat)
    (ha : ND.Proof Γ (adjunction (.fvar g) (.fvar p) (.fvar h)))
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar a) (.fvar b)))
    (hc : ND.Proof Γ (classified (.fvar g) (.fvar a) (.fvar b) (.fvar x) (.fvar y))) :
    ND.Proof Γ (edge (.fvar h) (.fvar x) (.fvar y)) := by
  apply orElim hc
  · exact adjunctionPreservesEdge g p h x y (up ha _) (assumption (by simp))
  · let q : Form := eq (.fvar x) (.fvar a) ⋏ eq (.fvar y) (.fvar b)
    have hd : ND.Proof (q::Γ) q := assumption (by simp)
    have hx := eqSymm (e.up q) x a (andLeft hd)
    have hy := eqSymm (e.up q) y b (andRight hd)
    have hk := kuratowskiCoordinate (e.up q) (up et q) p a b x y hx hy (up hp q)
    exact insertedEdge g p h x y (up ha q) hk (eqRefl (e.up q) p)

def exactExtension (g h a b : Term n) : Formula n :=
  ∀¹ ∀¹ sourceIff (edge (Rew.bShift (Rew.bShift h)) (.bvar 1) (.bvar 0))
    (classified (Rew.bShift (Rew.bShift g)) (Rew.bShift (Rew.bShift a))
      (Rew.bShift (Rew.bShift b)) (.bvar 1) (.bvar 0))

def adjunctionExact {Γ : List Form} (e : EqualityProofs Γ)
    (et : ND.Proof Γ transitivityFormula) (g p h a b : Nat)
    (ha : ND.Proof Γ (adjunction (.fvar g) (.fvar p) (.fvar h)))
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar a) (.fvar b))) :
    ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar a) (.fvar b)) := by
  apply allIntro
  apply allIntro
  have ee := e.shift.shift
  have ett := equalityTransShift (equalityTransShift et)
  have haa := adjunctionShift (g+1) (p+1) (h+1) (adjunctionShift g p h ha)
  have hpp := kuratowskiShift (p+1) (a+1) (b+1) (kuratowskiShift p a b hp)
  have result : ND.Proof (shifted (shifted Γ))
      (sourceIff (edge (.fvar (h+1+1)) (.fvar 1) (.fvar 0))
        (classified (.fvar (g+1+1)) (.fvar (a+1+1)) (.fvar (b+1+1)) (.fvar 1) (.fvar 0))) := by
    apply andIntro
    · apply impIntro
      exact classifyEdge (ee.up _) (up ett _) (g+1+1) (p+1+1) (h+1+1) (a+1+1) (b+1+1) 1 0
        (up haa _) (up hpp _) (assumption (by simp))
    · apply impIntro
      exact classifiedEdge (ee.up _) (up ett _) (g+1+1) (p+1+1) (h+1+1) (a+1+1) (b+1+1) 1 0
        (up haa _) (up hpp _) (assumption (by simp))
  convert result using 1 ; dsimp [exactExtension,classified] ; graphSyntax

#print axioms classifyEdge
#print axioms classifiedEdge
#print axioms adjunctionExact
end M6.PA.RelationalSource.PairGraph

