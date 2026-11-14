import PA194FoundationPairTransport
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (EqualityProofs eqRefl eqSymm eqTrans memContainer)

def singletonSelf {Γ : List Form} (e : EqualityProofs Γ) (a s : Nat)
    (hs : ND.Proof Γ (singleton (.fvar a) (.fvar s))) :
    ND.Proof Γ (mem (.fvar s) (.fvar a)) :=
  mp (eqRefl e a) (andRight (singletonAt a s a hs))

def pairLeft {Γ : List Form} (e : EqualityProofs Γ) (a b p : Nat)
    (hp : ND.Proof Γ (pair (.fvar a) (.fvar b) (.fvar p))) :
    ND.Proof Γ (mem (.fvar p) (.fvar a)) :=
  mp (ND.orLeft (eqRefl e a)) (andRight (pairAt a b p a hp))

def pairRight {Γ : List Form} (e : EqualityProofs Γ) (a b p : Nat)
    (hp : ND.Proof Γ (pair (.fvar a) (.fvar b) (.fvar p))) :
    ND.Proof Γ (mem (.fvar p) (.fvar b)) :=
  mp (ND.orRight (eqRefl e b)) (andRight (pairAt a b p b hp))

def singletonDecode {Γ : List Form} (e : EqualityProofs Γ) (a b s t : Nat)
    (hs : ND.Proof Γ (singleton (.fvar a) (.fvar s)))
    (ht : ND.Proof Γ (singleton (.fvar b) (.fvar t)))
    (hst : ND.Proof Γ (eq (.fvar s) (.fvar t))) :
    ND.Proof Γ (eq (.fvar a) (.fvar b)) :=
  mp (memContainer e s t a hst (singletonSelf e a s hs)) (andLeft (singletonAt b t a ht))

def singletonPairDecode {Γ : List Form} (e : EqualityProofs Γ) (a b c s t : Nat)
    (hs : ND.Proof Γ (singleton (.fvar a) (.fvar s)))
    (ht : ND.Proof Γ (pair (.fvar b) (.fvar c) (.fvar t)))
    (hst : ND.Proof Γ (eq (.fvar s) (.fvar t))) :
    ND.Proof Γ (eq (.fvar a) (.fvar b) ⋏ eq (.fvar a) (.fvar c)) := by
  have hts := eqSymm e s t hst
  have hb := memContainer e t s b hts (pairLeft e b c t ht)
  have hc := memContainer e t s c hts (pairRight e b c t ht)
  exact andIntro (eqSymm e b a (mp hb (andLeft (singletonAt a s b hs))))
    (eqSymm e c a (mp hc (andLeft (singletonAt a s c hs))))

def pairSameFirstDecode {Γ : List Form} (e : EqualityProofs Γ)
    (et : ND.Proof Γ transitivityFormula) (a b c d t u : Nat)
    (ht : ND.Proof Γ (pair (.fvar a) (.fvar b) (.fvar t)))
    (hu : ND.Proof Γ (pair (.fvar c) (.fvar d) (.fvar u)))
    (hac : ND.Proof Γ (eq (.fvar a) (.fvar c)))
    (htu : ND.Proof Γ (eq (.fvar t) (.fvar u))) :
    ND.Proof Γ (eq (.fvar b) (.fvar d)) := by
  have hb := mp (memContainer e t u b htu (pairRight e a b t ht)) (andLeft (pairAt c d u b hu))
  have hd := mp (memContainer e u t d (eqSymm e t u htu) (pairRight e c d u hu))
    (andLeft (pairAt a b t d ht))
  apply orElim hb
  · apply orElim (up hd (eq (.fvar b) (.fvar c)))
    · let C := eq (.fvar d) (.fvar a) :: eq (.fvar b) (.fvar c) :: Γ
      have hbc : ND.Proof C (eq (.fvar b) (.fvar c)) := assumption (by simp [C])
      have hda : ND.Proof C (eq (.fvar d) (.fvar a)) := assumption (by simp [C])
      have ee := (e.up (eq (.fvar b) (.fvar c))).up (eq (.fvar d) (.fvar a))
      have ett := up (up et (eq (.fvar b) (.fvar c))) (eq (.fvar d) (.fvar a))
      have hca := eqSymm ee a c (up (up hac _) _)
      exact eqTrans ett b a d (eqTrans ett b c a hbc hca) (eqSymm ee d a hda)
    · exact eqSymm ((e.up _).up _) d b (assumption (by simp))
  · exact assumption (by simp)

#print axioms singletonDecode
#print axioms singletonPairDecode
#print axioms pairSameFirstDecode
end M6.PA.RelationalSource.PairGraph
