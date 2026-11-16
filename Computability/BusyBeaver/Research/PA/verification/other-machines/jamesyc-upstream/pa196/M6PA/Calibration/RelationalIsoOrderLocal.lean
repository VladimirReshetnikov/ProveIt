module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoEndpointFresh
@[expose] public section

/-! Local ordinal membership exclusions and finite biconditional assembly. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def isoIffOfBoth {Γ : List Form} (p q : Form) (hp : ND.Proof Γ p) (hq : ND.Proof Γ q) :
    ND.Proof Γ (sourceIff p q) :=
  andIntro (impIntro (up hq p)) (impIntro (up hp q))

def isoIffOfNeither {Γ : List Form} (p q : Form) (hp : ND.Proof Γ p.neg) (hq : ND.Proof Γ q.neg) :
    ND.Proof Γ (sourceIff p q) := by
  apply andIntro
  · apply impIntro
    exact botElim (contradiction (assumption (by simp)) (up hp p))
  · apply impIntro
    exact botElim (contradiction (assumption (by simp)) (up hq q))

def memberEndpointClash {Γ : List Form} (a x : Nat)
    (ha : ND.Proof Γ (Ordinal.domain (.fvar a)))
    (hx : ND.Proof Γ (mem (.fvar a) (.fvar x)))
    (hm : ND.Proof Γ (mem (.fvar x) (.fvar a))) : ND.Proof Γ ⊥ := by
  have self := Ordinal.transitiveAt a x a (andLeft (andLeft ha)) hx hm
  exact contradiction self (Ordinal.containerIr a (andRight ha))

def memberNoEqualEndpoint {Γ : List Form} (E : FormulaEquality Γ) (a x u : Nat)
    (ha : ND.Proof Γ (Ordinal.domain (.fvar a)))
    (hx : ND.Proof Γ (mem (.fvar a) (.fvar x)))
    (hu : ND.Proof Γ (eq (.fvar u) (.fvar a))) :
    ND.Proof Γ (mem (.fvar x) (.fvar u)).neg := by
  apply byContradiction
  let p : Form := (mem (.fvar x) (.fvar u)).neg.neg
  have hm : ND.Proof (p::Γ) (mem (.fvar x) (.fvar u)) := by
    simpa [p,Semiformula.neg_neg] using (assumption (Γ := p::Γ) (p := p) (by simp))
  let EE := E.weaken (fun q hq => List.mem_cons_of_mem p hq)
  exact memberEndpointClash a x (up ha p) (up hx p)
    (Ordinal.memElement EE.core x u a (up hu p) hm)

def equalEndpointsNoMem {Γ : List Form} (E : FormulaEquality Γ) (a x u : Nat)
    (ha : ND.Proof Γ (Ordinal.domain (.fvar a)))
    (hx : ND.Proof Γ (eq (.fvar x) (.fvar a)))
    (hu : ND.Proof Γ (eq (.fvar u) (.fvar a))) :
    ND.Proof Γ (mem (.fvar x) (.fvar u)).neg := by
  apply byContradiction
  let p : Form := (mem (.fvar x) (.fvar u)).neg.neg
  have hm : ND.Proof (p::Γ) (mem (.fvar x) (.fvar u)) := by
    simpa [p,Semiformula.neg_neg] using (assumption (Γ := p::Γ) (p := p) (by simp))
  let EE := E.weaken (fun q hq => List.mem_cons_of_mem p hq)
  have self := Ordinal.memElement EE.core a u a (up hu p)
    (Ordinal.memContainer EE.core x a u (up hx p) hm)
  exact contradiction self (Ordinal.containerIr a (andRight (up ha p)))

#print axioms memberEndpointClash
#print axioms memberNoEqualEndpoint
#print axioms equalEndpointsNoMem
end M6.PA.RelationalSource.PairGraph
