import PA194OrderIsoExtrema
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula)

/-- Every edge of h is an edge of g; no set-inclusion assumption is hidden. -/
def edgeSubgraph {n : Nat} (h g : Ordinal.Term n) : Ordinal.Formula n :=
  ∀⁰ ∀⁰ (edge (Rew.bShift (Rew.bShift h)) (.bvar 1) (.bvar 0) 🡒
    edge (Rew.bShift (Rew.bShift g)) (.bvar 1) (.bvar 0))

theorem edgeSubgraph_eq_inclusion {n : Nat} (h g : Ordinal.Term n) :
    edgeSubgraph h g = inclusion h g := rfl

def edgeSubAt {Γ : List Form} (h g x y : Nat)
    (hs : ND.Proof Γ (edgeSubgraph (.fvar h) (.fvar g)))
    (he : ND.Proof Γ (edge (.fvar h) (.fvar x) (.fvar y))) :
    ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y)) := by
  have h : ND.Proof Γ (edge (.fvar h) (.fvar x) (.fvar y) 🡒
      edge (.fvar g) (.fvar x) (.fvar y)) := by
    convert allElim _ (.fvar y) (allElim _ (.fvar x) hs) using 1 <;> (try simp only [edgeSubgraph]) <;> (try isoSyntax)
  exact mp he h

def edgeSubShift {Γ : List Form} (h g : Nat)
    (hs : ND.Proof Γ (edgeSubgraph (.fvar h) (.fvar g))) :
    ND.Proof (shifted Γ) (edgeSubgraph (.fvar (h+1)) (.fvar (g+1))) := by
  convert shiftProof hs using 1 <;> (try simp only [edgeSubgraph]) <;> (try isoSyntax)

/-- Functional graphs remain functional when edges are restricted. -/
def functionalSubgraph {Γ : List Form} (h g : Nat)
    (hs : ND.Proof Γ (edgeSubgraph (.fvar h) (.fvar g)))
    (hf : ND.Proof Γ (graphFunctional (.fvar g))) :
    ND.Proof Γ (graphFunctional (.fvar h)) := by
  apply allIntro
  apply allIntro
  apply allIntro
  let q : Form := edge (.fvar (h+1+1+1)) (.fvar 2) (.fvar 1) ⋏
    edge (.fvar (h+1+1+1)) (.fvar 2) (.fvar 0)
  let D := q :: shifted (shifted (shifted Γ))
  have hq : ND.Proof D q := assumption (by simp [D])
  have hsub : ND.Proof D (edgeSubgraph (.fvar (h+1+1+1)) (.fvar (g+1+1+1))) :=
    up (edgeSubShift (h+1+1) (g+1+1) (edgeSubShift (h+1) (g+1) (edgeSubShift h g hs))) q
  have hfun : ND.Proof D (graphFunctional (.fvar (g+1+1+1))) := by
    have h := up (shiftProof (shiftProof (shiftProof hf))) q
    convert h using 1 <;> isoSyntax
  have he1 := edgeSubAt (h+1+1+1) (g+1+1+1) 2 1 hsub (andLeft hq)
  have he2 := edgeSubAt (h+1+1+1) (g+1+1+1) 2 0 hsub (andRight hq)
  have out := impIntro (functionalAt (g+1+1+1) 2 1 0 hfun he1 he2)
  convert out using 1 <;> (try dsimp [D,q]) <;> (try isoSyntax)

def injectiveAtLocal {Γ : List Form} (g x y z : Nat)
    (hi : ND.Proof Γ (graphInjective (.fvar g)))
    (hx : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar z)))
    (hy : ND.Proof Γ (edge (.fvar g) (.fvar y) (.fvar z))) :
    ND.Proof Γ (eq (.fvar x) (.fvar y)) := by
  have h : ND.Proof Γ (sourceImply (edge (.fvar g) (.fvar x) (.fvar z) ⋏
      edge (.fvar g) (.fvar y) (.fvar z)) (eq (.fvar x) (.fvar y))) := by
    convert allElim _ (.fvar z) (allElim _ (.fvar y) (allElim _ (.fvar x) hi)) using 1 <;> isoSyntax
  exact mp (andIntro hx hy) h

def injectiveSubgraph {Γ : List Form} (h g : Nat)
    (hs : ND.Proof Γ (edgeSubgraph (.fvar h) (.fvar g)))
    (hi : ND.Proof Γ (graphInjective (.fvar g))) :
    ND.Proof Γ (graphInjective (.fvar h)) := by
  apply allIntro
  apply allIntro
  apply allIntro
  let q : Form := edge (.fvar (h+1+1+1)) (.fvar 2) (.fvar 0) ⋏
    edge (.fvar (h+1+1+1)) (.fvar 1) (.fvar 0)
  let D := q :: shifted (shifted (shifted Γ))
  have hq : ND.Proof D q := assumption (by simp [D])
  have hsub : ND.Proof D (edgeSubgraph (.fvar (h+1+1+1)) (.fvar (g+1+1+1))) :=
    up (edgeSubShift (h+1+1) (g+1+1) (edgeSubShift (h+1) (g+1) (edgeSubShift h g hs))) q
  have hinj : ND.Proof D (graphInjective (.fvar (g+1+1+1))) := by
    have h := up (shiftProof (shiftProof (shiftProof hi))) q
    convert h using 1 <;> isoSyntax
  have he1 := edgeSubAt (h+1+1+1) (g+1+1+1) 2 0 hsub (andLeft hq)
  have he2 := edgeSubAt (h+1+1+1) (g+1+1+1) 1 0 hsub (andRight hq)
  have out := impIntro (injectiveAtLocal (g+1+1+1) 2 1 0 hinj he1 he2)
  convert out using 1 <;> (try dsimp [D,q]) <;> (try isoSyntax)

def orderSubgraph {Γ : List Form} (h g : Nat)
    (hs : ND.Proof Γ (edgeSubgraph (.fvar h) (.fvar g)))
    (ho : ND.Proof Γ (graphOrder (.fvar g))) :
    ND.Proof Γ (graphOrder (.fvar h)) := by
  apply allIntro
  apply allIntro
  apply allIntro
  apply allIntro
  let q : Form := edge (.fvar (h+1+1+1+1)) (.fvar 3) (.fvar 1) ⋏
    edge (.fvar (h+1+1+1+1)) (.fvar 2) (.fvar 0)
  let D := q :: shifted (shifted (shifted (shifted Γ)))
  have hq : ND.Proof D q := assumption (by simp [D])
  have hsub : ND.Proof D (edgeSubgraph (.fvar (h+1+1+1+1)) (.fvar (g+1+1+1+1))) :=
    up (edgeSubShift (h+1+1+1) (g+1+1+1) (edgeSubShift (h+1+1) (g+1+1) (edgeSubShift (h+1) (g+1) (edgeSubShift h g hs)))) q
  have horder : ND.Proof D (graphOrder (.fvar (g+1+1+1+1))) := by
    have h := up (shiftProof (shiftProof (shiftProof (shiftProof ho)))) q
    convert h using 1 <;> isoSyntax
  have he1 := edgeSubAt (h+1+1+1+1) (g+1+1+1+1) 3 1 hsub (andLeft hq)
  have he2 := edgeSubAt (h+1+1+1+1) (g+1+1+1+1) 2 0 hsub (andRight hq)
  have out := impIntro (graphOrderAt (g+1+1+1+1) 3 2 1 0 horder he1 he2)
  convert out using 1 <;> (try dsimp [D,q]) <;> (try isoSyntax)

def subsetAtLocal {Γ : List Form} (h g z : Nat)
    (hs : ND.Proof Γ (Ordinal.subset (.fvar h) (.fvar g)))
    (hz : ND.Proof Γ (mem (.fvar h) (.fvar z))) : ND.Proof Γ (mem (.fvar g) (.fvar z)) := by
  have h : ND.Proof Γ (mem (.fvar h) (.fvar z) 🡒 mem (.fvar g) (.fvar z)) := by
    convert allElim _ (.fvar z) hs using 1 <;> (try isoSyntax)
  exact mp hz h

def subsetPreservesEdge {Γ : List Form} (h g x y : Nat)
    (hs : ND.Proof Γ (Ordinal.subset (.fvar h) (.fvar g)))
    (he : ND.Proof Γ (edge (.fvar h) (.fvar x) (.fvar y))) :
    ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y)) := by
  apply exsElim he
  let φ : Ordinal.Formula 1 := mem (.fvar h) (.bvar 0) ⋏ kuratowski (.bvar 0) (.fvar x) (.fvar y)
  let D := φ.free :: shifted Γ
  have hp : ND.Proof D (mem (.fvar (h+1)) (.fvar 0) ⋏
      kuratowski (.fvar 0) (.fvar (x+1)) (.fvar (y+1))) := by
    have hd : ND.Proof D φ.free := assumption (by simp [D])
    convert hd using 1 <;> (dsimp [φ] <;> isoSyntax)
  have hs' : ND.Proof D (Ordinal.subset (.fvar (h+1)) (.fvar (g+1))) := by
    have hd := up (shiftProof hs) φ.free
    convert hd using 1 <;> isoSyntax
  have hm := subsetAtLocal (h+1) (g+1) 0 hs' (andLeft hp)
  have out := edgeFromEntry (g+1) (x+1) (y+1) 0 hm (andRight hp)
  convert out using 1 <;> isoSyntax

def subsetImpliesEdgeSubgraph {Γ : List Form} (h g : Nat)
    (hs : ND.Proof Γ (Ordinal.subset (.fvar h) (.fvar g))) :
    ND.Proof Γ (edgeSubgraph (.fvar h) (.fvar g)) := by
  apply allIntro
  apply allIntro
  let q : Form := edge (.fvar (h+1+1)) (.fvar 1) (.fvar 0)
  let D := q :: shifted (shifted Γ)
  have he : ND.Proof D q := assumption (by simp [D])
  have hs' : ND.Proof D (Ordinal.subset (.fvar (h+1+1)) (.fvar (g+1+1))) := by
    have hd := up (shiftProof (shiftProof hs)) q
    convert hd using 1 <;> isoSyntax
  have out := impIntro (subsetPreservesEdge (h+1+1) (g+1+1) 1 0 hs' he)
  convert out using 1 <;> (try dsimp [D,q,edgeSubgraph]) <;> (try isoSyntax)

#print axioms edgeSubgraph_eq_inclusion
#print axioms subsetAtLocal
#print axioms subsetPreservesEdge
#print axioms subsetImpliesEdgeSubgraph
#print axioms injectiveAtLocal
#print axioms injectiveSubgraph
#print axioms orderSubgraph
#print axioms edgeSubAt
#print axioms edgeSubShift
#print axioms functionalSubgraph
end M6.PA.RelationalSource.PairGraph
