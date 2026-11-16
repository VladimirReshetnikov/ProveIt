module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalSubstitutionRealizedSuccessor
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
open PairGraph
attribute [local irreducible] Ordinal.domain value orderIso addResult mulResult

theorem sourceRew_binary {n k : Nat} (σ : Rew Presentation.language Nat n Nat k)
    (op : BinaryOperation) (t v : SourceTerm n) :
    σ (op.term t v) = op.term (σ t) (σ v) := by
  cases op <;> simp only [BinaryOperation.term, Presentation.add, Presentation.mul, Rew.func]
  all_goals
    congr 1
    funext i
    fin_cases i <;> rfl

/-- Both pairs of existential input witnesses are retained. The final step is
full two-input arithmetic coherence, not equality of chosen representatives. -/
def realizedBinary {n : Nat} (op : BinaryOperation) (t v : SourceTerm n)
    (iht : RealizedTermCompatible t) (ihv : RealizedTermCompatible v) :
    RealizedTermCompatible (op.term t v) := by
  intro k σ Γ A b f c g H r s hr hs
  have H0 : TermRealization Γ σ b f c g t := by cases op <;> exact H 0
  have H1 : TermRealization Γ σ b f c g v := by cases op <;> exact H 1
  have hr' : ND.Proof Γ (value (op.term (σ t) (σ v)) b f r) := by
    simpa only [sourceRew_binary] using hr
  apply binaryValueElim op (σ t) (σ v) b f r _ hr'
  let p := binaryWitness op (σ t) (σ v) b f r
  have hp : ND.Proof (p :: shifted (shifted Γ)) p := assumption (by simp)
  have hs' : ND.Proof (p :: shifted (shifted Γ))
      (value (op.term t v) (freeShiftEnv (freeShiftEnv c))
        (freeShiftEnv (freeShiftEnv g)) (Rew.shift (Rew.shift s))) := by
    simpa only [value_shift] using up (shiftProof (shiftProof hs)) p
  apply binaryValueElim op t v _ _ _ _ hs'
  let q := binaryWitness op t v (freeShiftEnv (freeShiftEnv c))
    (freeShiftEnv (freeShiftEnv g)) (Rew.shift (Rew.shift s))
  have hq : ND.Proof (q :: shifted (shifted (p :: shifted (shifted Γ)))) q := assumption (by simp)
  have hp' : ND.Proof (q :: shifted (shifted (p :: shifted (shifted Γ))))
      (value (σ t) (freeShiftEnv (freeShiftEnv (freeShiftEnv (freeShiftEnv b))))
        (freeShiftEnv (freeShiftEnv (freeShiftEnv (freeShiftEnv f)))) (.fvar 3) ⋏
       (value (σ v) (freeShiftEnv (freeShiftEnv (freeShiftEnv (freeShiftEnv b))))
        (freeShiftEnv (freeShiftEnv (freeShiftEnv (freeShiftEnv f)))) (.fvar 2) ⋏
        op.result (.fvar 3) (.fvar 2) (Rew.shift (Rew.shift (Rew.shift (Rew.shift r)))))) := by
    convert up (shiftProof (shiftProof hp)) q using 1 <;>
      (dsimp [p,binaryWitness]; coherenceShiftSyntax; rfl)
  let A' := (A.shift.shift.up p).shift.shift.up q
  have H0' := TermRealization.up t (TermRealization.shift t (TermRealization.shift t
    (TermRealization.up t (TermRealization.shift t (TermRealization.shift t H0)) p))) q
  have H1' := TermRealization.up v (TermRealization.shift v (TermRealization.shift v
    (TermRealization.up v (TermRealization.shift v (TermRealization.shift v H1)) p))) q
  have hi := iht σ A' _ _ _ _ H0' _ _ (andLeft hp') (andLeft hq)
  have hj := ihv σ A' _ _ _ _ H1' _ _ (andLeft (andRight hp')) (andLeft (andRight hq))
  have out := binaryIsoAt op A'.coherence _ _ _ _ _ _
    (valueDomain _ _ _ _ (andLeft hp')) (valueDomain _ _ _ _ (andLeft hq))
    (valueDomain _ _ _ _ (andLeft (andRight hp'))) (valueDomain _ _ _ _ (andLeft (andRight hq)))
    hi hj (andRight (andRight hp')) (andRight (andRight hq))
  convert out using 1 <;> coherenceShiftSyntax

#print axioms realizedBinary
end M6.PA.ForwardRelational
