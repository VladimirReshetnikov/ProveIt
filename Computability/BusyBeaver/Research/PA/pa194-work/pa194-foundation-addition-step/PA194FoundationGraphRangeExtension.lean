import PA194FoundationGraphDomainExtension

/-! Full ordinal range preservation under exact graph extension. Raw output
equalities transport the entire five-clause domain formula. -/
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND

def graphRangeShift {Γ : List Form} (g : Nat)
    (h : ND.Proof Γ (graphRange (.fvar g))) :
    ND.Proof (shifted Γ) (graphRange (.fvar (g+1))) := by
  convert shiftProof h using 1 ; traceSyntax

def rangeExtensionAt {Γ : List Form} (E : FormulaEquality Γ) (g h a b x y : Nat)
    (hr : ND.Proof Γ (graphRange (.fvar g)))
    (hx : ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar a) (.fvar b)))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (he : ND.Proof Γ (edge (.fvar h) (.fvar x) (.fvar y))) :
    ND.Proof Γ (Ordinal.domain (.fvar y)) := by
  have hc := mp he (andLeft (exactAt g h a b x y hx))
  apply orElim hc
  · exact graphRangeAt g x y (up hr _) (assumption (by simp))
  · let q : Form := eq (.fvar x) (.fvar a) ⋏ eq (.fvar y) (.fvar b)
    have hp : ND.Proof (q::Γ) q := assumption (by simp)
    let EE := E.weaken (fun r h => List.mem_cons_of_mem q h)
    exact domainTransport EE b y (EE.symmetryOf (andRight hp)) (up hb q)

def graphRangeExtension {Γ : List Form} (E : FormulaEquality Γ) (g h a b : Nat)
    (hr : ND.Proof Γ (graphRange (.fvar g)))
    (hx : ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar a) (.fvar b)))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b))) :
    ND.Proof Γ (graphRange (.fvar h)) := by
  apply allIntro
  apply allIntro
  have rr := graphRangeShift (g+1) (graphRangeShift g hr)
  have xx := exactShift (g+1) (h+1) (a+1) (b+1) (exactShift g h a b hx)
  have bb := domainShift (b+1) (domainShift b hb)
  have result : ND.Proof (shifted (shifted Γ))
      (sourceImply (edge (.fvar (h+1+1)) (.fvar 1) (.fvar 0)) (Ordinal.domain (.fvar 0))) := by
    apply impIntro
    let q : Form := edge (.fvar (h+1+1)) (.fvar 1) (.fvar 0)
    let EE := E.shifted.shifted.weaken (fun r h => List.mem_cons_of_mem q h)
    exact rangeExtensionAt EE (g+1+1) (h+1+1) (a+1+1) (b+1+1) 1 0
      (up rr q) (up xx q) (up bb q) (assumption (by simp [q]))
  convert result using 1 ; traceSyntax

#print axioms rangeExtensionAt
#print axioms graphRangeExtension
end M6.PA.RelationalSource.PairGraph
