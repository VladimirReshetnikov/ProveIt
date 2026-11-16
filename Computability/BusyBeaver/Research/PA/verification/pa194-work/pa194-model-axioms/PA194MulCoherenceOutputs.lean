import PA194MulCoherenceFrame
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192
namespace PA194MulCoherence
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardMulZero PA194MulRecurrenceNew
attribute [local irreducible] addResult mulResult orderIso Ordinal.domain

def outputRight {Γ : List Form} (p q b c r s v : Nat) (I : Frame Γ p q b c)
    (hv : ND.Proof Γ (Ordinal.domain (.fvar v)))
    (hp : ND.Proof Γ (mulResult (.fvar p) (.fvar b) (.fvar v)))
    (hr : ND.Proof Γ (addResult (.fvar v) (.fvar b) (.fvar r)))
    (hs : ND.Proof Γ (predecessorResult (.fvar q) (.fvar c) (.fvar s))) :
    ND.Proof Γ (orderIso (.fvar r) (.fvar s)) := by
  apply ND.exsElim hs
  let body : Ordinal.Formula 1 := Ordinal.domain (.bvar 0) ⋏
    (mulResult (.fvar q) (.fvar c) (.bvar 0) ⋏ addResult (.bvar 0) (.fvar c) (.fvar s))
  let C := body.free :: ND.shifted Γ
  have hd : ND.Proof C (Ordinal.domain (.fvar 0) ⋏
      (mulResult (.fvar (q+1)) (.fvar (c+1)) (.fvar 0) ⋏
        addResult (.fvar 0) (.fvar (c+1)) (.fvar (s+1)))) := by
    have hh : ND.Proof C body.free := ND.assumption (by simp [C])
    convert hh using 1 <;> (dsimp [body] <;> simp [Semiformula.free,Rewriting.free,Semiformula.rewAux,Ordinal.domain_rew,mulResult_rew,addResult_rew,Rew.free,Rew.q,Rew.func])
  let inc : ∀ z, z ∈ ND.shifted Γ → z ∈ C := fun z hz => List.mem_cons_of_mem body.free hz
  let J := I.shift.weaken inc
  have iso := frameUse (p+1) (q+1) (b+1) (c+1) (v+1) 0 J
    (ND.weaken (resultShift p b v hp) inc) (ND.andLeft (ND.andRight hd))
  have out := additionCoherenceApply (v+1) 0 (b+1) (c+1) (r+1) (s+1) J.addition
    (ND.weaken (Ordinal.domainShift v hv) inc) (ND.andLeft hd) J.leftBaseDomain J.rightBaseDomain
    iso J.baseIso (ND.weaken (additionShift v b r hr) inc) (ND.andRight (ND.andRight hd))
  convert out using 1 <;> (dsimp [C,body] <;> simp [Semiformula.shift,Rewriting.shift,Semiformula.rewAux,orderIso_rew,Rew.shift,Rew.q,Rew.func])

def outputs {Γ : List Form} (p q b c r s : Nat) (I : Frame Γ p q b c)
    (hr : ND.Proof Γ (predecessorResult (.fvar p) (.fvar b) (.fvar r)))
    (hs : ND.Proof Γ (predecessorResult (.fvar q) (.fvar c) (.fvar s))) :
    ND.Proof Γ (orderIso (.fvar r) (.fvar s)) := by
  apply ND.exsElim hr
  let body : Ordinal.Formula 1 := Ordinal.domain (.bvar 0) ⋏
    (mulResult (.fvar p) (.fvar b) (.bvar 0) ⋏ addResult (.bvar 0) (.fvar b) (.fvar r))
  let C := body.free :: ND.shifted Γ
  have hd : ND.Proof C (Ordinal.domain (.fvar 0) ⋏
      (mulResult (.fvar (p+1)) (.fvar (b+1)) (.fvar 0) ⋏
        addResult (.fvar 0) (.fvar (b+1)) (.fvar (r+1)))) := by
    have hh : ND.Proof C body.free := ND.assumption (by simp [C])
    convert hh using 1 <;> (dsimp [body] <;> simp [Semiformula.free,Rewriting.free,Semiformula.rewAux,Ordinal.domain_rew,mulResult_rew,addResult_rew,Rew.free,Rew.q,Rew.func])
  let inc : ∀ z, z ∈ ND.shifted Γ → z ∈ C := fun z hz => List.mem_cons_of_mem body.free hz
  let J := I.shift.weaken inc
  have out := outputRight (p+1) (q+1) (b+1) (c+1) (r+1) (s+1) 0 J
    (ND.andLeft hd) (ND.andLeft (ND.andRight hd)) (ND.andRight (ND.andRight hd))
    (ND.weaken (predecessorShift q c s hs) inc)
  convert out using 1 <;> (dsimp [C,body] <;> simp [Semiformula.shift,Rewriting.shift,Semiformula.rewAux,orderIso_rew,Rew.shift,Rew.q,Rew.func])
#print axioms outputRight
#print axioms outputs
end PA194MulCoherence
