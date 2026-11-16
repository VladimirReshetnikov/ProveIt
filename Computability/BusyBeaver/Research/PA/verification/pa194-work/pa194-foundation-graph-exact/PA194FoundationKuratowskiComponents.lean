import PA194FoundationPairDecoding
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (EqualityProofs eqRefl eqSymm eqTrans)

structure Components (Γ : List Form) (p a b s t : Nat) where
  single : ND.Proof Γ (singleton (.fvar a) (.fvar s))
  inner : ND.Proof Γ (pair (.fvar a) (.fvar b) (.fvar t))
  outer : ND.Proof Γ (pair (.fvar s) (.fvar t) (.fvar p))

def Components.up {Γ : List Form} {p a b s t : Nat}
    (h : Components Γ p a b s t) (q : Form) : Components (q::Γ) p a b s t where
  single := ND.up h.single q
  inner := ND.up h.inner q
  outer := ND.up h.outer q

def componentFirst {Γ : List Form} (e : EqualityProofs Γ) (p a b c d s t u v : Nat)
    (h : Components Γ p a b s t) (k : Components Γ p c d u v) :
    ND.Proof Γ (eq (.fvar a) (.fvar c)) := by
  have hm := pairLeft e s t p h.outer
  have hc := mp hm (andLeft (pairAt u v p s k.outer))
  apply orElim hc
  · exact singletonDecode (e.up _) a c s u (up h.single _) (up k.single _) (assumption (by simp))
  · exact andLeft (singletonPairDecode (e.up _) a c d s v (up h.single _) (up k.inner _)
      (assumption (by simp)))

def componentSecond {Γ : List Form} (e : EqualityProofs Γ)
    (et : ND.Proof Γ transitivityFormula) (p a b c d s t u v : Nat)
    (h : Components Γ p a b s t) (k : Components Γ p c d u v) :
    ND.Proof Γ (eq (.fvar b) (.fvar d)) := by
  have hac := componentFirst e p a b c d s t u v h k
  have ht := mp (pairRight e s t p h.outer) (andLeft (pairAt u v p t k.outer))
  have hv := mp (pairRight e u v p k.outer) (andLeft (pairAt s t p v h.outer))
  apply orElim ht
  · let q : Form := eq (.fvar t) (.fvar u)
    have htu : ND.Proof (q::Γ) q := assumption (by simp)
    have hcb := singletonPairDecode (e.up q) c a b u t (up k.single q) (up h.inner q)
      (eqSymm (e.up q) t u htu)
    have hbc := eqSymm (e.up q) c b (andRight hcb)
    apply orElim (up hv q)
    · let r : Form := eq (.fvar v) (.fvar s)
      have hvs : ND.Proof (r::q::Γ) r := assumption (by simp)
      have had := singletonPairDecode ((e.up q).up r) a c d s v
        (up (up h.single q) r) (up (up k.inner q) r)
        (eqSymm ((e.up q).up r) v s hvs)
      have hca := up (andLeft hcb) r
      exact eqTrans (up (up et q) r) b a d
        (eqTrans (up (up et q) r) b c a (up hbc r) hca) (andRight had)
    · let r : Form := eq (.fvar v) (.fvar t)
      have hvt : ND.Proof (r::q::Γ) r := assumption (by simp)
      have hvu := eqTrans (up (up et q) r) v t u hvt (up htu r)
      have hcd := singletonPairDecode ((e.up q).up r) c c d u v
        (up (up k.single q) r) (up (up k.inner q) r)
        (eqSymm ((e.up q).up r) v u hvu)
      exact eqTrans (up (up et q) r) b c d (up hbc r) (andRight hcd)
  · exact pairSameFirstDecode (e.up _) (up et _) a b c d t v
      (up h.inner _) (up k.inner _) (up hac _) (assumption (by simp))

#print axioms componentFirst
#print axioms componentSecond
end M6.PA.RelationalSource.PairGraph
