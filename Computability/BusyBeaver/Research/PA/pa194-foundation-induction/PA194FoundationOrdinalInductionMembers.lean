import PA194FoundationOrdinalSuccessorClosure

/-! Downward closure of the five-clause ordinal domain. These finite ND
proof transformations preserve every ambient assumption and use no equality
axiom, extensionality, global irreflexivity, or semantic completeness.
Independently authored against the mathematical specification at busy-beaver
84049b5e753190cf328cbc2d2710791ad32ad59c. -/
namespace M6.PA.RelationalSource.Ordinal
open LO LO.FirstOrder ND

def memberShift {Γ : List Form} (a b : Nat)
    (d : ND.Proof Γ (mem (.fvar a) (.fvar b))) :
    ND.Proof (shifted Γ) (mem (.fvar (a+1)) (.fvar (b+1))) := by
  convert shiftProof d using 1 ; ordinalSyntax

def domainShift {Γ : List Form} (a : Nat)
    (d : ND.Proof Γ (domain (.fvar a))) :
    ND.Proof (shifted Γ) (domain (.fvar (a+1))) := by
  convert shiftProof d using 1 ; ordinalSyntax

def memberSubset {Γ : List Form} (a b : Nat)
    (ht : ND.Proof Γ (transitive (.fvar a)))
    (hm : ND.Proof Γ (mem (.fvar a) (.fvar b))) :
    ND.Proof Γ (subset (.fvar b) (.fvar a)) := by
  apply allIntro
  have h : ND.Proof (shifted Γ) (mem (.fvar (b+1)) (.fvar 0) 🡒 mem (.fvar (a+1)) (.fvar 0)) := impIntro (transitiveAt (a+1) (b+1) 0
    (up (transitiveShift a ht) _) (up (memberShift a b hm) _)
    (assumption (by simp)))
  convert h using 1 ; ordinalSyntax

def subsetCompose {Γ : List Form} (a b c : Nat)
    (hab : ND.Proof Γ (subset (.fvar a) (.fvar b)))
    (hbc : ND.Proof Γ (subset (.fvar b) (.fvar c))) :
    ND.Proof Γ (subset (.fvar a) (.fvar c)) := by
  apply allIntro
  have h : ND.Proof (shifted Γ) (mem (.fvar (a+1)) (.fvar 0) 🡒 mem (.fvar (c+1)) (.fvar 0)) := impIntro (subsetAt (b+1) (c+1) 0 (up (subsetShift b c hbc) _)
    (subsetAt (a+1) (b+1) 0 (up (subsetShift a b hab) _)
      (assumption (by simp))))
  convert h using 1 ; ordinalSyntax

def subsetMemberTransitive {Γ : List Form} (a b : Nat)
    (hs : ND.Proof Γ (subset (.fvar b) (.fvar a)))
    (ht : ND.Proof Γ (memberTransitive (.fvar a))) :
    ND.Proof Γ (memberTransitive (.fvar b)) := by
  apply allIntro
  have h : ND.Proof (shifted Γ) (mem (.fvar (b+1)) (.fvar 0) 🡒 transitive (.fvar 0)) := impIntro (memberTransitiveAt (a+1) 0 (up (memberTransitiveShift a ht) _)
    (subsetAt (b+1) (a+1) 0 (up (subsetShift b a hs) _) (assumption (by simp))))
  convert h using 1 ; ordinalSyntax

def subsetMemberIr {Γ : List Form} (a b : Nat)
    (hs : ND.Proof Γ (subset (.fvar b) (.fvar a)))
    (ht : ND.Proof Γ (memberIr (.fvar a))) :
    ND.Proof Γ (memberIr (.fvar b)) := by
  apply allIntro
  have h : ND.Proof (shifted Γ) (mem (.fvar (b+1)) (.fvar 0) 🡒 ∼mem (.fvar 0) (.fvar 0)) := impIntro (memberIrAt (a+1) 0 (up (memberIrShift a ht) _)
    (subsetAt (b+1) (a+1) 0 (up (subsetShift b a hs) _) (assumption (by simp))))
  convert h using 1 ; ordinalSyntax

def subsetMemberLinear {Γ : List Form} (a b : Nat)
    (hs : ND.Proof Γ (subset (.fvar b) (.fvar a)))
    (hl : ND.Proof Γ (memberLinear (.fvar a))) :
    ND.Proof Γ (memberLinear (.fvar b)) := by
  apply allIntro
  apply allIntro
  let p : Form := mem (.fvar (b+1+1)) (.fvar 1) ⋏ mem (.fvar (b+1+1)) (.fvar 0)
  have hp : ND.Proof (p :: shifted (shifted Γ)) p := assumption (by simp)
  have ds := up (subsetShift (b+1) (a+1) (subsetShift b a hs)) p
  have dl := up (memberLinearShift (a+1) (memberLinearShift a hl)) p
  have h := impIntro (memberLinearAt (a+1+1) 1 0 dl
    (subsetAt (b+1+1) (a+1+1) 1 ds (andLeft hp))
    (subsetAt (b+1+1) (a+1+1) 0 ds (andRight hp)))
  convert h using 1 ; dsimp [p] ; ordinalSyntax

def subsetInternalExtrema {Γ : List Form} (a b : Nat)
    (hs : ND.Proof Γ (subset (.fvar b) (.fvar a)))
    (he : ND.Proof Γ (internalExtrema (.fvar a))) :
    ND.Proof Γ (internalExtrema (.fvar b)) := by
  apply allIntro
  let p : Form := subset (.fvar 0) (.fvar (b+1)) ⋏ nonempty (.fvar 0)
  have hp : ND.Proof (p :: shifted Γ) p := assumption (by simp)
  have h := impIntro (internalExtremaAt (a+1) 0 (up (internalExtremaShift a he) p)
    (subsetCompose 0 (b+1) (a+1) (andLeft hp) (up (subsetShift b a hs) p)) (andRight hp))
  convert h using 1 ; dsimp [p] ; extremaSyntax

/-- Every member of a represented ordinal is again in the full domain. -/
def memberDomain {Γ : List Form} (a b : Nat)
    (ha : ND.Proof Γ (domain (.fvar a)))
    (hm : ND.Proof Γ (mem (.fvar a) (.fvar b))) :
    ND.Proof Γ (domain (.fvar b)) := by
  have hr := andLeft ha
  have ht := andLeft hr
  have hmt := andLeft (andRight hr)
  have hs := memberSubset a b ht hm
  exact andIntro (andIntro (memberTransitiveAt a b hmt hm)
    (andIntro (subsetMemberTransitive a b hs hmt)
      (andIntro (subsetMemberLinear a b hs (andLeft (andRight (andRight hr))))
        (subsetInternalExtrema a b hs (andRight (andRight (andRight hr)))))))
    (subsetMemberIr a b hs (andRight ha))

#print axioms subsetCompose
#print axioms subsetInternalExtrema
#print axioms memberDomain
end M6.PA.RelationalSource.Ordinal
