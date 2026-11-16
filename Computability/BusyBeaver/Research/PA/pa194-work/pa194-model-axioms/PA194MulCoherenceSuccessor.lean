import PA194MulCoherenceOutputs
import PA194MulResultPredecessorClosed
import PA194FoundationIsoSuccessorMatch
import PA194InclusiveSeparationClosure
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192
namespace PA194MulCoherence
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardMulZero PA194MulRecurrenceNew
attribute [local irreducible] mulResult orderIso Ordinal.domain Ordinal.successor

def successorCoherence {Γ : List Form} (E : FormulaEquality Γ) (p x y b c r s : Nat)
    (haddition : ND.Proof Γ addCoherenceStatement)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (hstrict : ND.Proof Γ closedStrictSeparation) (hinclusive : ND.Proof Γ closedInclusiveSeparation)
    (hp : ND.Proof Γ (Ordinal.domain (.fvar p)))
    (hy : ND.Proof Γ (Ordinal.domain (.fvar y)))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hc : ND.Proof Γ (Ordinal.domain (.fvar c)))
    (hsucc : ND.Proof Γ (Ordinal.successor (.fvar p) (.fvar x)))
    (hih : ND.Proof Γ (coherence (.fvar p)))
    (hxy : ND.Proof Γ (orderIso (.fvar x) (.fvar y)))
    (hbc : ND.Proof Γ (orderIso (.fvar b) (.fvar c)))
    (hr : ND.Proof Γ (mulResult (.fvar x) (.fvar b) (.fvar r)))
    (hs : ND.Proof Γ (mulResult (.fvar y) (.fvar c) (.fvar s))) :
    ND.Proof Γ (orderIso (.fvar r) (.fvar s)) := by
  apply ND.exsElim (orderIsoSuccessorMatchClosed E x y p hstrict hy hsucc hxy)
  let body : Ordinal.Formula 1 := Ordinal.domain (.bvar 0) ⋏
    (Ordinal.successor (.bvar 0) (.fvar y) ⋏ orderIso (.fvar p) (.bvar 0))
  let C := body.free :: ND.shifted Γ
  have hd : ND.Proof C (Ordinal.domain (.fvar 0) ⋏
      (Ordinal.successor (.fvar 0) (.fvar (y+1)) ⋏ orderIso (.fvar (p+1)) (.fvar 0))) := by
    have hh : ND.Proof C body.free := ND.assumption (by simp [C])
    convert hh using 1 <;> (dsimp [body] <;> simp [Semiformula.free,Rewriting.free,Semiformula.rewAux,Ordinal.domain_rew,Ordinal.successor_rew,orderIso_rew,Rew.free,Rew.q,Rew.func])
  let inc : ∀ z, z ∈ ND.shifted Γ → z ∈ C := fun z hz => List.mem_cons_of_mem body.free hz
  let EE := E.shifted.weaken inc
  have sep : ND.Proof C closedInclusiveSeparation := by
    have h : ND.Proof (ND.shifted Γ) closedInclusiveSeparation := by
      simpa only [PA194InclusiveSeparationClosure.closedSep_shift] using ND.shiftProof hinclusive
    exact ND.weaken h inc
  let I : Frame C (p+1) 0 (b+1) (c+1) :=
    ⟨ND.weaken (additionClosedShift haddition) inc,EE,
      ND.weaken (emptyClosedShift hempty) inc,ND.weaken (adjunctionClosedShift hadj) inc,
      ND.weaken (PA194MulCoherence.shift p hih) inc,ND.andLeft hd,
      ND.weaken (Ordinal.domainShift b hb) inc,ND.weaken (Ordinal.domainShift c hc) inc,
      ND.andRight (ND.andRight hd),ND.weaken (isoShift b c hbc) inc⟩
  have leftPrevious := resultPredecessorClosed EE (p+1) (x+1) (b+1) (r+1)
    (ND.weaken (Ordinal.domainShift p hp) inc) (ND.weaken (Ordinal.successorShift p x hsucc) inc)
    (ND.weaken (resultShift x b r hr) inc) sep
  have rightPrevious := resultPredecessorClosed EE 0 (y+1) (c+1) (s+1)
    (ND.andLeft hd) (ND.andLeft (ND.andRight hd)) (ND.weaken (resultShift y c s hs) inc) sep
  have out := outputs (p+1) 0 (b+1) (c+1) (r+1) (s+1) I leftPrevious rightPrevious
  convert out using 1 <;> (dsimp [C,body] <;> simp [Semiformula.shift,Rewriting.shift,Semiformula.rewAux,orderIso_rew,Rew.shift,Rew.q,Rew.func])
#print axioms successorCoherence
end PA194MulCoherence
