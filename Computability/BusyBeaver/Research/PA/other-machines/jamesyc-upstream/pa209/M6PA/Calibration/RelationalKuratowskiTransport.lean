module
public import M6PA.Theory
public import M6PA.Calibration.RelationalKuratowskiDecoder
@[expose] public section

/-! Coordinate and container transport for the existential pair formula, using
only the literal ordinary equality premises and finite witness elimination. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (EqualityProofs eqSymm memContainer equalityTransShift)

def pairContainer {Γ : List Form} (e : EqualityProofs Γ) (a b p q : Nat)
    (hpq : ND.Proof Γ (eq (.fvar p) (.fvar q)))
    (hp : ND.Proof Γ (pair (.fvar a) (.fvar b) (.fvar p))) :
    ND.Proof Γ (pair (.fvar a) (.fvar b) (.fvar q)) := by
  apply allIntro
  have hi := pairAt (a+1) (b+1) (p+1) 0 (pairShift a b p hp)
  have he := eqShift p q hpq
  have hr := eqSymm e.shift (p+1) (q+1) he
  have result : ND.Proof (shifted Γ) (sourceIff (mem (.fvar (q+1)) (.fvar 0))
      (eq (.fvar 0) (.fvar (a+1)) ⋎ eq (.fvar 0) (.fvar (b+1)))) := by
    apply andIntro
    · apply impIntro
      have hm := memContainer (e.shift.up (mem (.fvar (q+1)) (.fvar 0))) (q+1) (p+1) 0
        (up hr _) (assumption (by simp))
      exact mp hm (up (andLeft hi) _)
    · apply impIntro
      have hm := mp (assumption (by simp))
        (up (andRight hi) (eq (.fvar 0) (.fvar (a+1)) ⋎ eq (.fvar 0) (.fvar (b+1))))
      exact memContainer (e.shift.up _) (p+1) (q+1) 0 (up he _) hm
  convert result using 1 ; graphSyntax

def kuratowskiContainer {Γ : List Form} (e : EqualityProofs Γ) (p q a b : Nat)
    (hpq : ND.Proof Γ (eq (.fvar p) (.fvar q)))
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar a) (.fvar b))) :
    ND.Proof Γ (kuratowski (.fvar q) (.fvar a) (.fvar b)) := by
  apply eliminate p a b _ hp
  intro Δ incl hc
  let ee := equalityWeaken e.shift.shift incl
  have he := ND.weaken (eqShift (p+1) (q+1) (eqShift p q hpq)) incl
  have hout := pairContainer ee 1 0 (p+1+1) (q+1+1) he hc.outer
  have result := kuratowskiIntro (q+1+1) (a+1+1) (b+1+1) 1 0 hc.single hc.inner hout
  convert result using 1 ; graphSyntax

def kuratowskiCoordinate {Γ : List Form} (e : EqualityProofs Γ)
    (et : ND.Proof Γ transitivityFormula) (p a b c d : Nat)
    (hac : ND.Proof Γ (eq (.fvar a) (.fvar c)))
    (hbd : ND.Proof Γ (eq (.fvar b) (.fvar d)))
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar a) (.fvar b))) :
    ND.Proof Γ (kuratowski (.fvar p) (.fvar c) (.fvar d)) := by
  apply eliminate p a b _ hp
  intro Δ incl hc
  let ee := equalityWeaken e.shift.shift incl
  have ett := ND.weaken (equalityTransShift (equalityTransShift et)) incl
  have he := ND.weaken (eqShift (a+1) (c+1) (eqShift a c hac)) incl
  have hf := ND.weaken (eqShift (b+1) (d+1) (eqShift b d hbd)) incl
  have hs := singletonCoordinate ee ett (a+1+1) (c+1+1) 1 he hc.single
  have ht := pairCoordinate ee ett (a+1+1) (b+1+1) (c+1+1) (d+1+1) 0 he hf hc.inner
  have result := kuratowskiIntro (p+1+1) (c+1+1) (d+1+1) 1 0 hs ht hc.outer
  convert result using 1 ; graphSyntax

#print axioms pairContainer
#print axioms kuratowskiContainer
#print axioms kuratowskiCoordinate
end M6.PA.RelationalSource.PairGraph

