module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoEndpointFresh
public import M6PA.Calibration.RelationalOrdinalInductionMembers
@[expose] public section

/-! Injectivity of the extension, using freshness of the old range endpoint. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def injectiveExtensionAt {Γ : List Form} (E : FormulaEquality Γ) (g h a b x y z : Nat)
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hi : ND.Proof Γ (graphInjective (.fvar g)))
    (hx : ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar a) (.fvar b)))
    (he : ND.Proof Γ (edge (.fvar h) (.fvar x) (.fvar z)))
    (hf : ND.Proof Γ (edge (.fvar h) (.fvar y) (.fvar z))) :
    ND.Proof Γ (eq (.fvar x) (.fvar y)) := by
  have ce := mp he (andLeft (exactAt g h a b x z hx))
  have cf := mp hf (andLeft (exactAt g h a b y z hx))
  apply orElim ce
  · let p : Form := edge (.fvar g) (.fvar x) (.fvar z)
    apply orElim (up cf p)
    · exact orderInjectiveAt g x y z (up (up hi p) _)
        (assumption (by simp [p])) (assumption (by simp))
    · let q : Form := eq (.fvar y) (.fvar a) ⋏ eq (.fvar z) (.fvar b)
      have hq : ND.Proof (q::p::Γ) q := assumption (by simp)
      let EE := E.weaken (fun r hr => List.mem_cons_of_mem q (List.mem_cons_of_mem p hr))
      exact botElim (typedOutputClash EE g a b x z (up (up ht p) q) (up (up hb p) q)
        (assumption (by simp [p])) (andRight hq))
  · let p : Form := eq (.fvar x) (.fvar a) ⋏ eq (.fvar z) (.fvar b)
    apply orElim (up cf p)
    · let q : Form := edge (.fvar g) (.fvar y) (.fvar z)
      have hp : ND.Proof (q::p::Γ) p := assumption (by simp)
      let EE := E.weaken (fun r hr => List.mem_cons_of_mem q (List.mem_cons_of_mem p hr))
      exact botElim (typedOutputClash EE g a b y z (up (up ht p) q) (up (up hb p) q)
        (assumption (by simp [q])) (andRight hp))
    · let q : Form := eq (.fvar y) (.fvar a) ⋏ eq (.fvar z) (.fvar b)
      have hp : ND.Proof (q::p::Γ) p := assumption (by simp)
      have hq : ND.Proof (q::p::Γ) q := assumption (by simp)
      let EE := E.weaken (fun r hr => List.mem_cons_of_mem q (List.mem_cons_of_mem p hr))
      exact EE.transitivityOf (andLeft hp) (EE.symmetryOf (andLeft hq))

def successorGraphInjective {Γ : List Form} (E : FormulaEquality Γ) (g h a b : Nat)
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hi : ND.Proof Γ (graphInjective (.fvar g)))
    (hx : ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar a) (.fvar b))) :
    ND.Proof Γ (graphInjective (.fvar h)) := by
  apply allIntro
  apply allIntro
  apply allIntro
  let p : Form := edge (.fvar (h+1+1+1)) (.fvar 2) (.fvar 0) ⋏
    edge (.fvar (h+1+1+1)) (.fvar 1) (.fvar 0)
  have hp : ND.Proof (p::shifted (shifted (shifted Γ))) p := assumption (by simp)
  let EE := E.shifted.shifted.shifted.weaken (fun q hq => List.mem_cons_of_mem p hq)
  have tt := orderTypedShift (g+1+1) (a+1+1) (b+1+1)
    (orderTypedShift (g+1) (a+1) (b+1) (orderTypedShift g a b ht))
  have bb := Ordinal.domainShift (b+1+1) (Ordinal.domainShift (b+1) (Ordinal.domainShift b hb))
  have ii := orderInjectiveShift (g+1+1) (orderInjectiveShift (g+1) (orderInjectiveShift g hi))
  have xx := exactShift (g+1+1) (h+1+1) (a+1+1) (b+1+1)
    (exactShift (g+1) (h+1) (a+1) (b+1) (exactShift g h a b hx))
  have out := injectiveExtensionAt EE (g+1+1+1) (h+1+1+1) (a+1+1+1) (b+1+1+1) 2 1 0
    (up tt p) (up bb p) (up ii p) (up xx p) (andLeft hp) (andRight hp)
  convert impIntro out using 1 <;> (dsimp [p] <;> isoSyntax)

#print axioms injectiveExtensionAt
#print axioms successorGraphInjective
end M6.PA.RelationalSource.PairGraph
