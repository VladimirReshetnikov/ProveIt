module
public import M6PA.Theory
public import M6PA.Calibration.RelationalKuratowskiElimination
@[expose] public section

/-! Actual finite coordinate uniqueness for the existential raw Kuratowski
formula. Equality is decoded from real witnesses, without extensionality. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (EqualityProofs equalityTransShift)

def equalityWeaken {Γ Δ : List Form} (e : EqualityProofs Γ)
    (incl : ∀ x, x ∈ Γ → x ∈ Δ) : EqualityProofs Δ where
  reflexive := ND.weaken e.reflexive incl
  symmetric := ND.weaken e.symmetric incl
  congruent := ND.weaken e.congruent incl

def kuratowskiShift {Γ : List Form} (p a b : Nat)
    (h : ND.Proof Γ (kuratowski (.fvar p) (.fvar a) (.fvar b))) :
    ND.Proof (shifted Γ) (kuratowski (.fvar (p+1)) (.fvar (a+1)) (.fvar (b+1))) := by
  convert shiftProof h using 1 ; graphSyntax

def decodeAgainstComponents {Γ : List Form} (e : EqualityProofs Γ)
    (et : ND.Proof Γ transitivityFormula) (p a b c d s t : Nat)
    (h : Components Γ p a b s t)
    (k : ND.Proof Γ (kuratowski (.fvar p) (.fvar c) (.fvar d))) :
    ND.Proof Γ (eq (.fvar a) (.fvar c) ⋏ eq (.fvar b) (.fvar d)) := by
  apply eliminate p c d _ k
  intro Δ incl kc
  let ee := equalityWeaken e.shift.shift incl
  have ett := ND.weaken (equalityTransShift (equalityTransShift et)) incl
  have hh := h.shift.shift.weaken incl
  have hf := componentFirst ee (p+1+1) (a+1+1) (b+1+1) (c+1+1) (d+1+1)
    (s+1+1) (t+1+1) 1 0 hh kc
  have hs := componentSecond ee ett (p+1+1) (a+1+1) (b+1+1) (c+1+1) (d+1+1)
    (s+1+1) (t+1+1) 1 0 hh kc
  convert andIntro hf hs using 1 ; graphSyntax

def kuratowskiDecode {Γ : List Form} (e : EqualityProofs Γ)
    (et : ND.Proof Γ transitivityFormula) (p a b c d : Nat)
    (h : ND.Proof Γ (kuratowski (.fvar p) (.fvar a) (.fvar b)))
    (k : ND.Proof Γ (kuratowski (.fvar p) (.fvar c) (.fvar d))) :
    ND.Proof Γ (eq (.fvar a) (.fvar c) ⋏ eq (.fvar b) (.fvar d)) := by
  apply eliminate p a b _ h
  intro Δ incl hc
  let ee := equalityWeaken e.shift.shift incl
  have ett := ND.weaken (equalityTransShift (equalityTransShift et)) incl
  have kk := ND.weaken (kuratowskiShift (p+1) (c+1) (d+1) (kuratowskiShift p c d k)) incl
  have result := decodeAgainstComponents ee ett (p+1+1) (a+1+1) (b+1+1)
    (c+1+1) (d+1+1) 1 0 hc kk
  convert result using 1 ; graphSyntax

#print axioms decodeAgainstComponents
#print axioms kuratowskiDecode
end M6.PA.RelationalSource.PairGraph

