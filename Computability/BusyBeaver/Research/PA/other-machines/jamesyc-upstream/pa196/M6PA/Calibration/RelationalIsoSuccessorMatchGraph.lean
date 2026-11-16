module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoPredecessorWitness
public import M6PA.Calibration.RelationalIsoPredecessorCutWitness
@[expose] public section

/-! A real image predecessor also carries an actual predecessor isomorphism. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] orderIso
set_option maxHeartbeats 600000

def isoPredecessorMatch (p b : Term n) : Formula n :=
  ∃¹ (Ordinal.domain (.bvar 0) ⋏
    (Ordinal.successor (.bvar 0) (Rew.bShift b) ⋏ orderIso (Rew.bShift p) (.bvar 0)))

def successorMatchFromGraph {Γ : List Form} (E : FormulaEquality Γ) (g a b p : Nat)
    (hsep : ND.Proof Γ closedStrictSeparation)
    (hg : ND.Proof Γ (orderBijection (.fvar g) (.fvar a) (.fvar b)))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar p) (.fvar a))) :
    ND.Proof Γ (isoPredecessorMatch (.fvar p) (.fvar b)) := by
  apply exsElim (successorImageWitness E g a b p hg hb hs)
  let body : Formula 1 := Ordinal.domain (.bvar 0) ⋏
    (Ordinal.successor (.bvar 0) (.fvar b) ⋏ edge (.fvar g) (.fvar p) (.bvar 0))
  let C := body.free :: shifted Γ
  have hd : ND.Proof C (Ordinal.domain (.fvar 0) ⋏
      (Ordinal.successor (.fvar 0) (.fvar (b+1)) ⋏
        edge (.fvar (g+1)) (.fvar (p+1)) (.fvar 0))) := by
    have hh : ND.Proof C body.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [body] <;> isoSyntax)
  have iso := predecessorCutIso (g+1) (a+1) (b+1) (p+1) 0
    ⟨E.shifted.weaken (fun r hr => List.mem_cons_of_mem body.free hr),
      up (predecessorClosedSeparationShift hsep) body.free,
      up (orderBijectionShift g a b hg) body.free,
      up (Ordinal.successorShift p a hs) body.free,
      andLeft (andRight hd),andRight (andRight hd)⟩
  have out : ND.Proof C (isoPredecessorMatch (.fvar (p+1)) (.fvar (b+1))) := by
    apply exsIntro _ (.fvar 0)
    convert andIntro (andLeft hd) (andIntro (andLeft (andRight hd)) iso) using 1 <;>
      ((try simp only [isoPredecessorMatch]) <;> isoSyntax)
  convert out using 1 <;> (dsimp [C,body] <;> (try simp only [isoPredecessorMatch]) <;> isoSyntax)

#print axioms successorMatchFromGraph
end M6.PA.RelationalSource.PairGraph
