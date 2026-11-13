module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalCoherenceSuccessor
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
open PairGraph
attribute [local irreducible] Ordinal.domain value orderIso addResult mulResult

/-- The full two-input arithmetic coherence theorem, never raw output equality. -/
def binaryIsoAt {Γ : List Form} (op : BinaryOperation) (A : CoherencePremises Γ)
    (x y b c r s : Term 0)
    (hx : ND.Proof Γ (Ordinal.domain x)) (hy : ND.Proof Γ (Ordinal.domain y))
    (hb : ND.Proof Γ (Ordinal.domain b)) (hc : ND.Proof Γ (Ordinal.domain c))
    (hi : ND.Proof Γ (orderIso x y)) (hj : ND.Proof Γ (orderIso b c))
    (hr : ND.Proof Γ (op.result x b r)) (hs : ND.Proof Γ (op.result y c s)) :
    ND.Proof Γ (orderIso r s) := by
  obtain ⟨x,rfl⟩ := groundName x
  obtain ⟨y,rfl⟩ := groundName y
  obtain ⟨b,rfl⟩ := groundName b
  obtain ⟨c,rfl⟩ := groundName c
  obtain ⟨r,rfl⟩ := groundName r
  obtain ⟨s,rfl⟩ := groundName s
  cases op with
  | addition => exact additionCoherenceApply x y b c r s A.addition hx hy hb hc hi hj hr hs
  | multiplication => exact multiplicationCoherenceApply x y b c r s A.multiplication hx hy hb hc hi hj hr hs

def binaryValuesCoherent {n : Nat} (op : BinaryOperation) (u v : SourceTerm n)
    (ihu : ValuesCoherent u) (ihv : ValuesCoherent v) : ValuesCoherent (op.term u v) := by
  intro Γ A b b' f f' H r s hr hs
  have H0 : IsoCoverage Γ b b' f f' u := by cases op <;> exact H 0
  have H1 : IsoCoverage Γ b b' f f' v := by cases op <;> exact H 1
  apply binaryValueElim op u v b f r _ hr
  let p := binaryWitness op u v b f r
  have hp : ND.Proof (p :: shifted (shifted Γ)) p := assumption (by simp)
  have hs' : ND.Proof (p :: shifted (shifted Γ))
      (value (op.term u v) (freeShiftEnv (freeShiftEnv b'))
        (freeShiftEnv (freeShiftEnv f')) (Rew.shift (Rew.shift s))) := by
    simpa only [value_shift] using up (shiftProof (shiftProof hs)) p
  apply binaryValueElim op u v _ _ _ _ hs'
  let q := binaryWitness op u v (freeShiftEnv (freeShiftEnv b'))
    (freeShiftEnv (freeShiftEnv f')) (Rew.shift (Rew.shift s))
  have hq : ND.Proof (q :: shifted (shifted (p :: shifted (shifted Γ)))) q := assumption (by simp)
  have hp' : ND.Proof (q :: shifted (shifted (p :: shifted (shifted Γ))))
      (value u (freeShiftEnv (freeShiftEnv (freeShiftEnv (freeShiftEnv b))))
        (freeShiftEnv (freeShiftEnv (freeShiftEnv (freeShiftEnv f)))) (.fvar 3) ⋏
       (value v (freeShiftEnv (freeShiftEnv (freeShiftEnv (freeShiftEnv b))))
        (freeShiftEnv (freeShiftEnv (freeShiftEnv (freeShiftEnv f)))) (.fvar 2) ⋏
        op.result (.fvar 3) (.fvar 2) (Rew.shift (Rew.shift (Rew.shift (Rew.shift r)))))) := by
    convert up (shiftProof (shiftProof hp)) q using 1 <;>
      (dsimp [p,binaryWitness]; coherenceShiftSyntax; rfl)
  let A' := (A.shift.shift.up p).shift.shift.up q
  have H0' := IsoCoverage.up u (IsoCoverage.shift u (IsoCoverage.shift u
    (IsoCoverage.up u (IsoCoverage.shift u (IsoCoverage.shift u H0)) p))) q
  have H1' := IsoCoverage.up v (IsoCoverage.shift v (IsoCoverage.shift v
    (IsoCoverage.up v (IsoCoverage.shift v (IsoCoverage.shift v H1)) p))) q
  have hi := ihu A' _ _ _ _ H0' _ _ (andLeft hp') (andLeft hq)
  have hj := ihv A' _ _ _ _ H1' _ _ (andLeft (andRight hp')) (andLeft (andRight hq))
  have out := binaryIsoAt op A' _ _ _ _ _ _
    (valueDomain u _ _ _ (andLeft hp')) (valueDomain u _ _ _ (andLeft hq))
    (valueDomain v _ _ _ (andLeft (andRight hp'))) (valueDomain v _ _ _ (andLeft (andRight hq)))
    hi hj (andRight (andRight hp')) (andRight (andRight hq))
  convert out using 1 <;> coherenceShiftSyntax

#print axioms binaryIsoAt
#print axioms binaryValuesCoherent
end M6.PA.ForwardRelational
