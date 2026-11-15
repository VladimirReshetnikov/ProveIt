import PA194FoundationFormulaCongruence
import PA194OrderIsoZero
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula)

def graphOrderAt {Γ : List Form} (g x y u v : Nat)
    (ho : ND.Proof Γ (graphOrder (.fvar g)))
    (hxu : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar u)))
    (hyv : ND.Proof Γ (edge (.fvar g) (.fvar y) (.fvar v))) :
    ND.Proof Γ (sourceIff (mem (.fvar x) (.fvar y)) (mem (.fvar u) (.fvar v))) := by
  have h : ND.Proof Γ (sourceImply
      (edge (.fvar g) (.fvar x) (.fvar u) ⋏ edge (.fvar g) (.fvar y) (.fvar v))
      (sourceIff (mem (.fvar x) (.fvar y)) (mem (.fvar u) (.fvar v)))) := by
    convert allElim _ (.fvar v) (allElim _ (.fvar u) (allElim _ (.fvar y) (allElim _ (.fvar x) ho))) using 1 <;> isoSyntax
  exact mp (andIntro hxu hyv) h

def typedEdgeRight {Γ : List Form} (g a b x y : Nat)
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y))) :
    ND.Proof Γ (mem (.fvar b) (.fvar y)) := by
  have h : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y) 🡒
      (mem (.fvar a) (.fvar x) ⋏ mem (.fvar b) (.fvar y))) := by
    convert allElim _ (.fvar y) (allElim _ (.fvar x) ht) using 1 <;> isoSyntax
  exact andRight (mp he h)

def functionalAt {Γ : List Form} (g x y z : Nat)
    (hf : ND.Proof Γ (graphFunctional (.fvar g)))
    (hy : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y)))
    (hz : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar z))) :
    ND.Proof Γ (eq (.fvar y) (.fvar z)) := by
  have h : ND.Proof Γ (sourceImply (edge (.fvar g) (.fvar x) (.fvar y) ⋏
      edge (.fvar g) (.fvar x) (.fvar z)) (eq (.fvar y) (.fvar z))) := by
    convert allElim _ (.fvar z) (allElim _ (.fvar y) (allElim _ (.fvar x) hf)) using 1 <;> isoSyntax
  exact mp (andIntro hy hz) h

def edgeInputTransfer {Γ : List Form} (E : FormulaEquality Γ) (g x u y : Nat)
    (hxu : ND.Proof Γ (eq (.fvar x) (.fvar u)))
    (h : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y))) :
    ND.Proof Γ (edge (.fvar g) (.fvar u) (.fvar y)) := by
  have hp : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![.fvar x]) (edge (.fvar g) (.bvar 0) (.fvar y))) := by
    convert h using 1 <;> isoSyntax
  have ht := E.substituteOne (edge (.fvar g) (.bvar 0) (.fvar y)) (.fvar x) (.fvar u) hxu hp
  convert ht using 1 <;> isoSyntax

def greatestAtLocal {Γ : List Form} (a x w : Nat) (hg : ND.Proof Γ (Ordinal.greatest (.fvar a) (.fvar x)))
    (hw : ND.Proof Γ (mem (.fvar a) (.fvar w))) :
    ND.Proof Γ (eq (.fvar w) (.fvar x) ⋎ mem (.fvar x) (.fvar w)) := by
  have h : ND.Proof Γ (mem (.fvar a) (.fvar w) 🡒
      (eq (.fvar w) (.fvar x) ⋎ mem (.fvar x) (.fvar w))) := by
    convert allElim _ (.fvar w) (andRight hg) using 1 <;> isoSyntax
  exact mp hw h

/-- Images of points below a greatest point stay below its image. -/
def greatestImagesCompared {Γ : List Form} (E : FormulaEquality Γ) (g a b x y w z : Nat)
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (hf : ND.Proof Γ (graphFunctional (.fvar g)))
    (ho : ND.Proof Γ (graphOrder (.fvar g)))
    (hg : ND.Proof Γ (Ordinal.greatest (.fvar a) (.fvar x)))
    (hxy : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y)))
    (hwz : ND.Proof Γ (edge (.fvar g) (.fvar w) (.fvar z))) :
    ND.Proof Γ (eq (.fvar z) (.fvar y) ⋎ mem (.fvar y) (.fvar z)) := by
  have hw := typedEdgeLeft g a b w z ht hwz
  have cases := greatestAtLocal a x w hg hw
  apply orElim cases
  · let q : Form := eq (.fvar w) (.fvar x)
    have heq : ND.Proof (q :: Γ) q := assumption (by simp)
    have E' := E.weaken (fun p hp => List.mem_cons_of_mem q hp)
    have hxz := edgeInputTransfer E' g w x z heq (up hwz q)
    have he := functionalAt g x y z (up hf q) (up hxy q) hxz
    exact orLeft (E'.symmetryOf he)
  · let q : Form := mem (.fvar x) (.fvar w)
    have hm : ND.Proof (q :: Γ) q := assumption (by simp)
    have hiff := graphOrderAt g x w y z (up ho q) (up hxy q) (up hwz q)
    exact orRight (mp hm (andLeft hiff))

def greatestImageAt {Γ : List Form} (E : FormulaEquality Γ) (g a b x y z : Nat)
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (hf : ND.Proof Γ (graphFunctional (.fvar g)))
    (ho : ND.Proof Γ (graphOrder (.fvar g)))
    (hr : ND.Proof Γ (graphRightTotal (.fvar g) (.fvar b)))
    (hg : ND.Proof Γ (Ordinal.greatest (.fvar a) (.fvar x)))
    (hxy : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y)))
    (hz : ND.Proof Γ (mem (.fvar b) (.fvar z))) :
    ND.Proof Γ (eq (.fvar z) (.fvar y) ⋎ mem (.fvar y) (.fvar z)) := by
  have hex := rightTotalAt g b z hr hz
  apply exsElim hex
  let φ : Formula 1 := edge (.fvar g) (.bvar 0) (.fvar z)
  let D := φ.free :: shifted Γ
  have hwz : ND.Proof D (edge (.fvar (g+1)) (.fvar 0) (.fvar (z+1))) := by
    have h : ND.Proof D φ.free := assumption (by simp [D])
    convert h using 1 <;> (dsimp [φ] <;> isoSyntax)
  let E' := E.shifted.weaken (fun p hp => List.mem_cons_of_mem φ.free hp)
  have ht' : ND.Proof D (graphTyped (.fvar (g+1)) (.fvar (a+1)) (.fvar (b+1))) := by
    have h := up (shiftProof ht) φ.free
    convert h using 1 <;> isoSyntax
  have hf' : ND.Proof D (graphFunctional (.fvar (g+1))) := by
    have h := up (shiftProof hf) φ.free
    convert h using 1 <;> isoSyntax
  have ho' : ND.Proof D (graphOrder (.fvar (g+1))) := by
    have h := up (shiftProof ho) φ.free
    convert h using 1 <;> isoSyntax
  have hg' : ND.Proof D (Ordinal.greatest (.fvar (a+1)) (.fvar (x+1))) := by
    have h := up (shiftProof hg) φ.free
    convert h using 1 <;> isoSyntax
  have hxy' : ND.Proof D (edge (.fvar (g+1)) (.fvar (x+1)) (.fvar (y+1))) := by
    have h := up (shiftProof hxy) φ.free
    convert h using 1 <;> isoSyntax
  have out := greatestImagesCompared E' (g+1) (a+1) (b+1) (x+1) (y+1) 0 (z+1) ht' hf' ho' hg' hxy' hwz
  convert out using 1 <;> isoSyntax

/-- An order-bijection maps a greatest element to a greatest element. -/
def greatestImage {Γ : List Form} (E : FormulaEquality Γ) (g a b x y : Nat)
    (hb : ND.Proof Γ (orderBijection (.fvar g) (.fvar a) (.fvar b)))
    (hg : ND.Proof Γ (Ordinal.greatest (.fvar a) (.fvar x)))
    (hxy : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y))) :
    ND.Proof Γ (Ordinal.greatest (.fvar b) (.fvar y)) := by
  have ht := andLeft (andRight hb)
  have hr := andLeft (andRight (andRight (andRight hb)))
  have hf := andLeft (andRight (andRight (andRight (andRight hb))))
  have ho := andRight (andRight (andRight (andRight (andRight (andRight hb)))))
  apply andIntro (typedEdgeRight g a b x y ht hxy)
  apply allIntro
  let q : Form := mem (.fvar (b+1)) (.fvar 0)
  let D := q :: shifted Γ
  have hz : ND.Proof D q := assumption (by simp [D])
  let E' := E.shifted.weaken (fun p hp => List.mem_cons_of_mem q hp)
  have ht' : ND.Proof D (graphTyped (.fvar (g+1)) (.fvar (a+1)) (.fvar (b+1))) := by
    have h := up (shiftProof ht) q
    convert h using 1 <;> isoSyntax
  have hf' : ND.Proof D (graphFunctional (.fvar (g+1))) := by
    have h := up (shiftProof hf) q
    convert h using 1 <;> isoSyntax
  have ho' : ND.Proof D (graphOrder (.fvar (g+1))) := by
    have h := up (shiftProof ho) q
    convert h using 1 <;> isoSyntax
  have hr' : ND.Proof D (graphRightTotal (.fvar (g+1)) (.fvar (b+1))) := by
    have h := up (shiftProof hr) q
    convert h using 1 <;> isoSyntax
  have hg' : ND.Proof D (Ordinal.greatest (.fvar (a+1)) (.fvar (x+1))) := by
    have h := up (shiftProof hg) q
    convert h using 1 <;> isoSyntax
  have hxy' : ND.Proof D (edge (.fvar (g+1)) (.fvar (x+1)) (.fvar (y+1))) := by
    have h := up (shiftProof hxy) q
    convert h using 1 <;> isoSyntax
  have hcmp := greatestImageAt E' (g+1) (a+1) (b+1) (x+1) (y+1) 0 ht' hf' ho' hr' hg' hxy' hz
  have hcond := impIntro hcmp
  convert hcond using 1 <;> (try dsimp [D,q]) <;> (try isoSyntax)

#print axioms greatestImage
#print axioms greatestImageAt
#print axioms greatestImagesCompared
#print axioms functionalAt
#print axioms edgeInputTransfer
#print axioms greatestAtLocal
#print axioms graphOrderAt
#print axioms typedEdgeRight
end M6.PA.RelationalSource.PairGraph
