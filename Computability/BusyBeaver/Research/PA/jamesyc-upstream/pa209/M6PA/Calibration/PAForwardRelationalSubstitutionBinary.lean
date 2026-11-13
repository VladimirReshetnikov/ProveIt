module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalSubstitutionSuccessor
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
open PairGraph
attribute [local irreducible] Ordinal.domain value orderIso addResult mulResult

@[simp] theorem singleBoundSubst_binary {n : Nat} (op : BinaryOperation)
    (u : SourceTerm n) (t v : SourceTerm (n+1)) :
    singleBoundSubst u (op.term t v) = op.term (singleBoundSubst u t) (singleBoundSubst u v) := by
  cases op <;> simp only [BinaryOperation.term, Presentation.add, Presentation.mul,
    singleBoundSubst_func]
  all_goals
    congr 1
    funext i
    fin_cases i <;> rfl

/-- Both pairs of existential input witnesses are retained. The final step is
full two-input arithmetic coherence, not equality of chosen representatives. -/
def substitutionBinary {n : Nat} (op : BinaryOperation) (t v : SourceTerm (n+1))
    (iht : SubstitutionCompatible t) (ihv : SubstitutionCompatible v) :
    SubstitutionCompatible (op.term t v) := by
  intro u Γ A b f a Hu H ha r s hr hs
  have H0 : IsoCoverage Γ (Fin.cases a b) (Fin.cases a b) f f t := by cases op <;> exact H 0
  have H1 : IsoCoverage Γ (Fin.cases a b) (Fin.cases a b) f f v := by cases op <;> exact H 1
  have hr' : ND.Proof Γ (value (op.term (singleBoundSubst u t) (singleBoundSubst u v)) b f r) := by
    simpa only [singleBoundSubst_binary] using hr
  apply binaryValueElim op (singleBoundSubst u t) (singleBoundSubst u v) b f r _ hr'
  let p := binaryWitness op (singleBoundSubst u t) (singleBoundSubst u v) b f r
  have hp : ND.Proof (p :: shifted (shifted Γ)) p := assumption (by simp)
  have hs' : ND.Proof (p :: shifted (shifted Γ))
      (value (op.term t v) (freeShiftEnv (freeShiftEnv (Fin.cases a b)))
        (freeShiftEnv (freeShiftEnv f)) (Rew.shift (Rew.shift s))) := by
    simpa only [value_shift] using up (shiftProof (shiftProof hs)) p
  apply binaryValueElim op t v _ _ _ _ hs'
  let q := binaryWitness op t v (freeShiftEnv (freeShiftEnv (Fin.cases a b)))
    (freeShiftEnv (freeShiftEnv f)) (Rew.shift (Rew.shift s))
  have hq : ND.Proof (q :: shifted (shifted (p :: shifted (shifted Γ)))) q := assumption (by simp)
  have hp' : ND.Proof (q :: shifted (shifted (p :: shifted (shifted Γ))))
      (value (singleBoundSubst u t) (freeShiftEnv (freeShiftEnv (freeShiftEnv (freeShiftEnv b))))
        (freeShiftEnv (freeShiftEnv (freeShiftEnv (freeShiftEnv f)))) (.fvar 3) ⋏
       (value (singleBoundSubst u v) (freeShiftEnv (freeShiftEnv (freeShiftEnv (freeShiftEnv b))))
        (freeShiftEnv (freeShiftEnv (freeShiftEnv (freeShiftEnv f)))) (.fvar 2) ⋏
        op.result (.fvar 3) (.fvar 2) (Rew.shift (Rew.shift (Rew.shift (Rew.shift r)))))) := by
    convert up (shiftProof (shiftProof hp)) q using 1 <;>
      (dsimp [p,binaryWitness]; coherenceShiftSyntax; rfl)
  let A' := (A.shift.shift.up p).shift.shift.up q
  have Hu' := IsoCoverage.up u (IsoCoverage.shift u (IsoCoverage.shift u
    (IsoCoverage.up u (IsoCoverage.shift u (IsoCoverage.shift u Hu)) p))) q
  have H0' := IsoCoverage.up t (IsoCoverage.shift t (IsoCoverage.shift t
    (IsoCoverage.up t (IsoCoverage.shift t (IsoCoverage.shift t H0)) p))) q
  have H1' := IsoCoverage.up v (IsoCoverage.shift v (IsoCoverage.shift v
    (IsoCoverage.up v (IsoCoverage.shift v (IsoCoverage.shift v H1)) p))) q
  have ha' := up (shiftProof (shiftProof (up (shiftProof (shiftProof ha)) p))) q
  have hi := iht u A' _ _ (Rew.shift (Rew.shift (Rew.shift (Rew.shift a)))) Hu'
    (by simpa only [freeShiftEnv_cons] using H0')
    (by simpa only [value_shift] using ha') (.fvar 3) (.fvar 1) (andLeft hp')
    (by simpa only [freeShiftEnv_cons] using andLeft hq)
  have hj := ihv u A' _ _ (Rew.shift (Rew.shift (Rew.shift (Rew.shift a)))) Hu'
    (by simpa only [freeShiftEnv_cons] using H1')
    (by simpa only [value_shift] using ha') (.fvar 2) (.fvar 0) (andLeft (andRight hp'))
    (by simpa only [freeShiftEnv_cons] using andLeft (andRight hq))
  have out := binaryIsoAt op A' _ _ _ _ _ _
    (valueDomain _ _ _ _ (andLeft hp')) (valueDomain _ _ _ _ (andLeft hq))
    (valueDomain _ _ _ _ (andLeft (andRight hp'))) (valueDomain _ _ _ _ (andLeft (andRight hq)))
    hi hj (andRight (andRight hp')) (andRight (andRight hq))
  convert out using 1 <;> coherenceShiftSyntax

#print axioms substitutionBinary
end M6.PA.ForwardRelational
