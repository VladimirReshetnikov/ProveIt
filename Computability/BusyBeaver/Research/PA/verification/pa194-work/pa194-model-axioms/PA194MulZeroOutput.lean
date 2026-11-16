import PA194MulPrefixZeroOutput
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194MulRecurrenceNew
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardMulZero
attribute [local irreducible] addResult mulPrefix mulResult

def zeroResultPayload {n : Nat} (x base out e : Term n) : Formula n :=
  ∃⁰ (Ordinal.zero (Rew.bShift e) ⋏
    (mulPrefix (Rew.bShift x) (Rew.bShift base) (Rew.bShift e) (.bvar 0) ⋏
      edge (.bvar 0) (Rew.bShift x) (Rew.bShift out)))

def payloadZeroOutput {Γ : List Form} (E : FormulaEquality Γ) (x base out e : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar x)))
    (hp : ND.Proof Γ (zeroResultPayload (.fvar x) (.fvar base) (.fvar out) (.fvar e))) :
    ND.Proof Γ (Ordinal.zero (.fvar out)) := by
  apply ND.exsElim hp
  let σ : Ordinal.Formula 1 := Ordinal.zero (.fvar e) ⋏
    (mulPrefix (.fvar x) (.fvar base) (.fvar e) (.bvar 0) ⋏ edge (.bvar 0) (.fvar x) (.fvar out))
  let C := σ.free :: ND.shifted Γ
  have hd : ND.Proof C (Ordinal.zero (.fvar (e+1)) ⋏
      (mulPrefix (.fvar (x+1)) (.fvar (base+1)) (.fvar (e+1)) (.fvar 0) ⋏
        edge (.fvar 0) (.fvar (x+1)) (.fvar (out+1)))) := by
    have hh : ND.Proof C σ.free := ND.assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> simp [Semiformula.free,Rewriting.free,Semiformula.rewAux,Ordinal.zero_rew,mulPrefix_rew,edge_rew,Rew.free,Rew.q,Rew.func])
  let E' := E.shifted.weaken (fun q hq => List.mem_cons_of_mem σ.free hq)
  have heq := prefixZeroOutput E' (x+1) (base+1) (e+1) 0 (out+1) (ND.up (Ordinal.zeroShift x hz) σ.free)
    (ND.andLeft (ND.andRight hd)) (ND.andRight (ND.andRight hd))
  have outp := zeroTransport E' (e+1) (out+1) (E'.symmetryOf heq) (ND.andLeft hd)
  convert outp using 1 <;> (dsimp [C,σ] <;> simp [Semiformula.shift,Rewriting.shift,Semiformula.rewAux,Ordinal.zero_rew,Rew.shift,Rew.q,Rew.func])

def resultZeroOutput {Γ : List Form} (E : FormulaEquality Γ) (x base out : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar x)))
    (hp : ND.Proof Γ (mulResult (.fvar x) (.fvar base) (.fvar out))) :
    ND.Proof Γ (Ordinal.zero (.fvar out)) := by
  have hpParts := hp
  unfold mulResult at hpParts
  apply ND.exsElim hpParts
  let σ : Ordinal.Formula 1 := ∃⁰ (Ordinal.zero (.bvar 1) ⋏
    (mulPrefix (.fvar x) (.fvar base) (.bvar 1) (.bvar 0) ⋏ edge (.bvar 0) (.fvar x) (.fvar out)))
  let C := σ.free :: ND.shifted Γ
  have hd : ND.Proof C (zeroResultPayload (.fvar (x+1)) (.fvar (base+1)) (.fvar (out+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := ND.assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ,zeroResultPayload] <;> simp [Semiformula.free,Rewriting.free,Semiformula.rewAux,Ordinal.zero_rew,mulPrefix_rew,edge_rew,Rew.free,Rew.q,Rew.func])
  let E' := E.shifted.weaken (fun q hq => List.mem_cons_of_mem σ.free hq)
  have result := payloadZeroOutput E' (x+1) (base+1) (out+1) 0 (ND.up (Ordinal.zeroShift x hz) σ.free) hd
  convert result using 1 <;> (dsimp [C,σ] <;> simp [Semiformula.shift,Rewriting.shift,Semiformula.rewAux,Ordinal.zero_rew,Rew.shift,Rew.q,Rew.func])
#print axioms payloadZeroOutput
#print axioms resultZeroOutput
end PA194MulRecurrenceNew
