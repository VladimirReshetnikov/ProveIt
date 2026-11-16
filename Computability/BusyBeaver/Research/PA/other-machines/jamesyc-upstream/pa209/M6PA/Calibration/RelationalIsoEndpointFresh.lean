module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoSuccessorTyped
@[expose] public section

/-! Old order-bijection edges cannot use either ordinal container as a
coordinate. Only local member irreflexivity is used. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Formula)

def typedInputClash {Γ : List Form} (E : FormulaEquality Γ) (g a b x y : Nat)
    (hg : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (ha : ND.Proof Γ (Ordinal.domain (.fvar a)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y)))
    (hx : ND.Proof Γ (eq (.fvar x) (.fvar a))) : ND.Proof Γ ⊥ := by
  have hm := andLeft (orderTypedAt g a b x y hg he)
  exact contradiction (Ordinal.memElement E.core a x a hx hm)
    (Ordinal.containerIr a (andRight ha))

def typedOutputClash {Γ : List Form} (E : FormulaEquality Γ) (g a b x y : Nat)
    (hg : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y)))
    (hy : ND.Proof Γ (eq (.fvar y) (.fvar b))) : ND.Proof Γ ⊥ := by
  have hm := andRight (orderTypedAt g a b x y hg he)
  exact contradiction (Ordinal.memElement E.core b y b hy hm)
    (Ordinal.containerIr b (andRight hb))

def typedEndpointOutputFalse {Γ : List Form} (g a b : Nat)
    (hg : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (ha : ND.Proof Γ (Ordinal.domain (.fvar a)))
    (ho : ND.Proof Γ (hasOutput (.fvar g) (.fvar a))) : ND.Proof Γ ⊥ := by
  apply exsElim ho
  let body : Formula 1 := edge (.fvar g) (.fvar a) (.bvar 0)
  let C := body.free :: shifted Γ
  have he : ND.Proof C (edge (.fvar (g+1)) (.fvar (a+1)) (.fvar 0)) := by
    have h : ND.Proof C body.free := assumption (by simp [C])
    convert h using 1 <;> (dsimp [body] <;> isoSyntax)
  have hm := andLeft (orderTypedAt (g+1) (a+1) (b+1) (a+1) 0
    (up (orderTypedShift g a b hg) body.free) he)
  have hn := up (Ordinal.memberIrShift a (andRight ha)) body.free
  convert contradiction hm (Ordinal.containerIr (a+1) hn) using 1 <;> rfl

def typedNoEndpointOutput {Γ : List Form} (g a b : Nat)
    (hg : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (ha : ND.Proof Γ (Ordinal.domain (.fvar a))) :
    ND.Proof Γ (hasOutput (.fvar g) (.fvar a)).neg := by
  apply byContradiction
  let premise : Form := (hasOutput (.fvar g) (.fvar a)).neg.neg
  have he : ND.Proof (premise::Γ) (hasOutput (.fvar g) (.fvar a)) := by
    simpa [premise,Semiformula.neg_neg] using (assumption (Γ := premise::Γ) (p := premise) (by simp))
  exact typedEndpointOutputFalse g a b (up hg premise) (up ha premise) he

#print axioms typedInputClash
#print axioms typedOutputClash
#print axioms typedNoEndpointOutput
end M6.PA.RelationalSource.PairGraph
