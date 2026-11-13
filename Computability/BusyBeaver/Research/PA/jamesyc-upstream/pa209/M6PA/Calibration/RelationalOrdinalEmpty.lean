module
public import M6PA.Theory
public import M6PA.Calibration.RelationalOrdinalDomain
public import M6PA.Calibration.RelationalSourceAdjunctionExistence
public import M6PA.Calibration.RelationalSourceEmpty
public import M6PA.Calibration.RelationalSourceContext
@[expose] public section

/-! Empty ordinal representatives, constructed as actual Foundation LK proof
terms. Existential elimination uses the capture-aware eigenvariable rule. -/
namespace M6.PA.RelationalSource.Ordinal
open FFL FFL.FirstOrder ND

macro "ordinalSyntax" : tactic => `(tactic|
  (simp only [zero,subset,transitive,memberTransitive,memberLinear,nonempty,
    least,greatest,internalExtrema,representative,memberIr,domain,inhabited,
    mem,eq,Semiformula.shift,Semiformula.free,
    Rewriting.shift,Rewriting.free,Rewriting.subst,app_eq_rewAux,
    Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq];
   finishSourceSyntax))

def zeroShift {Γ : List Form} (i : Nat) (d : ND.Proof Γ (zero (.fvar i))) :
    ND.Proof (shifted Γ) (zero (.fvar (i+1))) := by
  convert shiftProof d using 1 ; ordinalSyntax

def zeroNotMem {Γ : List Form} (i j : Nat) (d : ND.Proof Γ (zero (.fvar i))) :
    ND.Proof Γ (∼mem (.fvar i) (.fvar j)) := by
  convert allElim _ (.fvar j) d using 1 ; ordinalSyntax

def zeroTransitive {Γ : List Form} (i : Nat) (d : ND.Proof Γ (zero (.fvar i))) :
    ND.Proof Γ (transitive (.fvar i)) := by
  apply allIntro
  have d1 := zeroShift i d
  apply allIntro
  have dn := zeroNotMem (i+1+1) 1 (zeroShift (i+1) d1)
  have h : ND.Proof (shifted (shifted Γ))
      ((mem (.fvar (i+1+1)) (.fvar 1) ⋏ mem (.fvar 1) (.fvar 0)) 🡒
        mem (.fvar (i+1+1)) (.fvar 0)) := impIntro <|
    botElim (contradiction (andLeft (assumption (p := mem (.fvar (i+1+1)) (.fvar 1) ⋏ mem (.fvar 1) (.fvar 0)) (by simp))) (up dn _))
  convert h using 1 ; ordinalSyntax

def zeroMemberTransitive {Γ : List Form} (i : Nat) (d : ND.Proof Γ (zero (.fvar i))) :
    ND.Proof Γ (memberTransitive (.fvar i)) := by
  apply allIntro
  have dn := zeroNotMem (i+1) 0 (zeroShift i d)
  have h : ND.Proof (shifted Γ)
      (mem (.fvar (i+1)) (.fvar 0) 🡒 transitive (.fvar 0)) := impIntro <|
    botElim (contradiction (assumption (by simp)) (up dn _))
  convert h using 1 ; ordinalSyntax

def zeroMemberLinear {Γ : List Form} (i : Nat) (d : ND.Proof Γ (zero (.fvar i))) :
    ND.Proof Γ (memberLinear (.fvar i)) := by
  apply allIntro
  apply allIntro
  have dn := zeroNotMem (i+1+1) 1 (zeroShift (i+1) (zeroShift i d))
  have h : ND.Proof (shifted (shifted Γ))
      ((mem (.fvar (i+1+1)) (.fvar 1) ⋏ mem (.fvar (i+1+1)) (.fvar 0)) 🡒
        (eq (.fvar 1) (.fvar 0) ⋎ (mem (.fvar 0) (.fvar 1) ⋎ mem (.fvar 1) (.fvar 0)))) := impIntro <|
    botElim (contradiction
      (andLeft (assumption (p := mem (.fvar (i+1+1)) (.fvar 1) ⋏ mem (.fvar (i+1+1)) (.fvar 0)) (by simp)))
      (up dn _))
  convert h using 1 ; ordinalSyntax

def zeroMemberIr {Γ : List Form} (i : Nat) (d : ND.Proof Γ (zero (.fvar i))) :
    ND.Proof Γ (memberIr (.fvar i)) := by
  apply allIntro
  have dn := zeroNotMem (i+1) 0 (zeroShift i d)
  have h : ND.Proof (shifted Γ)
      (mem (.fvar (i+1)) (.fvar 0) 🡒 ∼mem (.fvar 0) (.fvar 0)) := impIntro <|
    botElim (contradiction (assumption (by simp)) (up dn _))
  convert h using 1 ; ordinalSyntax

/-- A represented nonempty subset of an empty representative is impossible.
The membership witness is local to `exsElim` and both premises are shifted. -/
def zeroSubsetNonemptyFalse {Γ : List Form} (i j : Nat)
    (d : ND.Proof Γ (zero (.fvar i)))
    (hs : ND.Proof Γ (subset (.fvar j) (.fvar i)))
    (hne : ND.Proof Γ (nonempty (.fvar j))) : ND.Proof Γ ⊥ := by
  apply exsElim hne
  let σ : Formula 1 := mem (Rew.bShift (.fvar j)) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hx : ND.Proof C (mem (.fvar (j+1)) (.fvar 0)) := by
    have h : ND.Proof C σ.free := assumption (by simp [C])
    convert h using 1 ; dsimp [σ] ; ordinalSyntax
  have hsub : ND.Proof C (mem (.fvar (j+1)) (.fvar 0) 🡒 mem (.fvar (i+1)) (.fvar 0)) := by
    have h := allElim _ (.fvar 0) (up (shiftProof hs) σ.free)
    convert h using 1 ; ordinalSyntax
  have hn := up (zeroNotMem (i+1) 0 (zeroShift i d)) σ.free
  exact contradiction (mp hx hsub) hn

def zeroInternalExtrema {Γ : List Form} (i : Nat) (d : ND.Proof Γ (zero (.fvar i))) :
    ND.Proof Γ (internalExtrema (.fvar i)) := by
  apply allIntro
  let p : Form := subset (.fvar 0) (.fvar (i+1)) ⋏ nonempty (.fvar 0)
  have hp : ND.Proof (p :: shifted Γ) p := assumption (by simp)
  have hb := zeroSubsetNonemptyFalse (i+1) 0 (up (zeroShift i d) p) (andLeft hp) (andRight hp)
  have h : ND.Proof (shifted Γ)
      (p 🡒 ((∃¹ least (Rew.bShift (.fvar 0)) (.bvar 0)) ⋏
        (∃¹ greatest (Rew.bShift (.fvar 0)) (.bvar 0)))) := impIntro (botElim hb)
  convert h using 1 ; dsimp [p] ; ordinalSyntax

/-- Pure logical supplier: empty representatives are ordinal-domain members. -/
def zeroDomain {Γ : List Form} (a : Term 0) (d : ND.Proof Γ (zero a)) :
    ND.Proof Γ (domain a) := by
  cases a with
  | bvar i => nomatch i
  | func f _ => nomatch f
  | fvar i =>
    exact andIntro (andIntro (zeroTransitive i d)
      (andIntro (zeroMemberTransitive i d)
        (andIntro (zeroMemberLinear i d) (zeroInternalExtrema i d)))) (zeroMemberIr i d)

/-- Empty-set existence supplies ordinal-domain inhabitation, with no further
nonlogical premise. -/
def emptyInhabited {Γ : List Form} (d : ND.Proof Γ emptyFormula) :
    ND.Proof Γ inhabited := by
  apply exsElim d
  let σ : Formula 1 := zero (.bvar 0)
  let C := σ.free :: shifted Γ
  have hz : ND.Proof C (zero (.fvar 0)) := by
    have h : ND.Proof C σ.free := assumption (by simp [C])
    convert h using 1 ; dsimp [σ] ; ordinalSyntax
  have hd := zeroDomain (.fvar 0) hz
  apply exsIntro _ (.fvar 0)
  convert hd using 1 ; ordinalSyntax

def emptyInhabitedDerivation : ND.Proof [emptyFormula] inhabited :=
  emptyInhabited (assumption (by simp))

/-- Finite actual-basis domain inhabitation. The sole nonlogical supplier is
empty-set existence; the budget explicitly accounts for the full LK proof. -/
def inhabitedSupplier (f : Nat → Nat) (lo z : Nat) (hlo : 0 < lo)
    (hf : ∀ i, f i < lo) (hz : lo+1 < z)
    (hbudget : lo + lkBudget emptyInhabitedDerivation ≤ z) :
    NativeCalculus.ActualBasis.Proof (code inhabited f lo z) := by
  apply compileContext [emptyFormula] inhabited emptyInhabitedDerivation f lo z hlo hf hbudget
  intro p hp
  have he : p = emptyFormula := by simpa using hp
  subst p
  exact emptySupplier f lo z hz

#print axioms inhabitedSupplier
#print axioms emptyInhabited
#print axioms zeroDomain
#print axioms zeroSubsetNonemptyFalse
#print axioms zeroTransitive
#print axioms zeroMemberTransitive
#print axioms zeroMemberLinear
#print axioms zeroMemberIr
end M6.PA.RelationalSource.Ordinal

