import PA194FoundationOrdinalInductionPredecessor

/-! The local irreflexivity argument in the minimum-counterexample template.
No assumption that all sets are irreflexive is used. -/
namespace M6.PA.RelationalSource.Ordinal
open LO LO.FirstOrder ND

def leastExcludesMember {Γ : List Form} (e : EqualityProofs Γ) (c b m : Nat)
    (hb : ND.Proof Γ (domain (.fvar b)))
    (hl : ND.Proof Γ (least (.fvar c) (.fvar b)))
    (hm : ND.Proof Γ (mem (.fvar b) (.fvar m))) :
    ND.Proof Γ (∼mem (.fvar c) (.fvar m)) := by
  apply byContradiction
  have hc : ND.Proof (∼∼mem (.fvar c) (.fvar m) :: Γ) (mem (.fvar c) (.fvar m)) := by
    simpa using (assumption (p := ∼∼mem (.fvar c) (.fvar m)) (by simp))
  have hsplit := leastAt c b m (up hl _) hc
  apply orElim hsplit
  · have hm' : ND.Proof (eq (.fvar b) (.fvar m) :: ∼∼mem (.fvar c) (.fvar m) :: Γ) (mem (.fvar m) (.fvar m)) := memContainer ((e.up _).up _) b m m (assumption (by simp)) (up (up hm _) _)
    exact contradiction hm' (up (up (memberIrAt b m (andRight hb) hm) _) _)
  · have cycle : ND.Proof (mem (.fvar m) (.fvar b) :: ∼∼mem (.fvar c) (.fvar m) :: Γ) (mem (.fvar b) (.fvar b)) := transitiveAt b m b (up (up (andLeft (andLeft hb)) _) _)
      (up (up hm _) _) (assumption (by simp))
    exact contradiction cycle (up (up (containerIr b (andRight hb)) _) _)

/-- If a represented trace records the bad members, every member below its
least point satisfies the property. The local instance is supplied explicitly. -/
def leastMemberGood {Γ : List Form} (e : EqualityProofs Γ) (c b m : Nat) (q : Form)
    (hb : ND.Proof Γ (domain (.fvar b)))
    (hl : ND.Proof Γ (least (.fvar c) (.fvar b)))
    (hm : ND.Proof Γ (mem (.fvar b) (.fvar m)))
    (hbad : ND.Proof Γ (∼q 🡒 mem (.fvar c) (.fvar m))) : ND.Proof Γ q := by
  apply byContradiction
  exact contradiction (mp (assumption (by simp)) (up hbad _))
    (up (leastExcludesMember e c b m hb hl hm) _)

def subsetReflexive {Γ : List Form} (b : Nat) :
    ND.Proof Γ (subset (.fvar b) (.fvar b)) := by
  apply allIntro
  have h : ND.Proof (shifted Γ)
      (mem (.fvar (b+1)) (.fvar 0) 🡒 mem (.fvar (b+1)) (.fvar 0)) :=
    impIntro (assumption (by simp))
  convert h using 1 ; ordinalSyntax

def notZeroNonempty {Γ : List Form} (b : Nat)
    (h : ND.Proof Γ (∼zero (.fvar b))) : ND.Proof Γ (nonempty (.fvar b)) := by
  apply byContradiction
  have hz : ND.Proof (∼nonempty (.fvar b) :: Γ) (zero (.fvar b)) := by
    have hn : ND.Proof (∼nonempty (.fvar b) :: Γ) (∼nonempty (.fvar b)) :=
      assumption (by simp)
    convert hn using 1 ; ordinalSyntax
  exact contradiction hz (up h _)

def domainGreatest {Γ : List Form} (b : Nat)
    (h : ND.Proof Γ (domain (.fvar b)))
    (hn : ND.Proof Γ (nonempty (.fvar b))) : ND.Proof Γ (greatestExists (.fvar b)) :=
  andRight (internalExtremaAt b b (andRight (andRight (andRight (andLeft h))))
    (subsetReflexive b) hn)

#print axioms leastExcludesMember
#print axioms leastMemberGood
#print axioms domainGreatest
end M6.PA.RelationalSource.Ordinal
