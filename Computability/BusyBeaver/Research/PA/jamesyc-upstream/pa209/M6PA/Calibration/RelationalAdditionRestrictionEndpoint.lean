module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionRestrictionPrefix
public import M6PA.Calibration.RelationalAdditionResultWitness
@[expose] public section

namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addPrefix

def addPredecessorResult (t base out : Term n) : Formula n :=
  ∃¹ (Ordinal.domain (.bvar 0) ⋏
    (addResult (Rew.bShift t) (Rew.bShift base) (.bvar 0) ⋏
      Ordinal.successor (.bvar 0) (Rew.bShift out)))

set_option maxHeartbeats 600000 in
def restrictionEndpointPrevious {Γ : List Form} (E : FormulaEquality Γ)
    (t base e g h out : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar e)))
    (hp : ND.Proof Γ (addPrefix (.fvar t) (.fvar base) (.fvar e) (.fvar h)))
    (hr : ND.Proof Γ (graphRestriction (.fvar t) (.fvar g) (.fvar h)))
    (hv : ND.Proof Γ (addPrevious (.fvar g) (.fvar t) (.fvar out))) :
    ND.Proof Γ (addPredecessorResult (.fvar t) (.fvar base) (.fvar out)) := by
  apply exsElim hv
  let body : Formula 1 := edge (.fvar g) (.fvar t) (.bvar 0) ⋏ Ordinal.successor (.bvar 0) (.fvar out)
  let C := body.free :: shifted Γ
  have hd : ND.Proof C (edge (.fvar (g+1)) (.fvar (t+1)) (.fvar 0) ⋏
      Ordinal.successor (.fvar 0) (.fvar (out+1))) := by
    have hh : ND.Proof C body.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [body] <;> previousSyntax)
  have ee := E.shifted.weaken (fun q hq => List.mem_cons_of_mem body.free hq)
  have pp := up (prefixShift t base e h hp) body.free
  have he := restrictionIntro (t+1) (g+1) (h+1) (t+1) 0
    (up (graphRestrictionShift t g h hr) body.free) (andLeft hd)
    (ND.orRight (ee.reflexive (.fvar (t+1))))
  have parts := pp
  unfold addPrefix at parts
  have dom := graphRangeAt (h+1) (t+1) 0 (andLeft (andRight (andRight parts))) he
  have res := addResultIntro (t+1) (base+1) 0 (e+1) (h+1)
    (up (Ordinal.zeroShift e hz) body.free) pp he
  have result : ND.Proof C (addPredecessorResult (.fvar (t+1)) (.fvar (base+1)) (.fvar (out+1))) := by
    apply exsIntro _ (.fvar 0)
    convert andIntro dom (andIntro res (andRight hd)) using 1 <;>
      ((try simp only [addPredecessorResult]); prefixSyntax)
  convert result using 1 <;> (dsimp [C,body] <;> (try simp only [addPredecessorResult]) <;> prefixSyntax)

#print axioms restrictionEndpointPrevious
end M6.PA.RelationalSource.PairGraph
