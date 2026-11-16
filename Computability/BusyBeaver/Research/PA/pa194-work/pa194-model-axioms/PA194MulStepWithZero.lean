import PA194MulPrefixStep
import PA194MulPrefixZero
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194MulRecurrenceNew
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardMulZero PA194MulPrefixZero
attribute [local irreducible] addResult mulPrefix

def stepWithZero {Γ : List Form} (E : FormulaEquality Γ) (top u base z g : Nat)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (htop : ND.Proof Γ (Ordinal.domain (.fvar top)))
    (hu : ND.Proof Γ (Ordinal.domain (.fvar u)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar top) (.fvar u)))
    (hz : ND.Proof Γ (Ordinal.zero (.fvar z)))
    (hp : ND.Proof Γ (mulPrefix (.fvar top) (.fvar base) (.fvar z) (.fvar g)))
    (hadd : ND.Proof Γ (additionSupply base)) :
    ND.Proof Γ (mulPrefixExists (.fvar u) (.fvar base)) := by
  apply ND.exsElim (stepWitness E top u base z g hempty hadj htop hu hs hp hadd)
  let σ : Ordinal.Formula 1 := mulPrefix (.fvar u) (.fvar base) (.fvar z) (.bvar 0)
  let C := σ.free :: ND.shifted Γ
  have hg : ND.Proof C (mulPrefix (.fvar (u+1)) (.fvar (base+1)) (.fvar (z+1)) (.fvar 0)) := by
    have h0 : ND.Proof C σ.free := ND.assumption (by simp [C])
    convert h0 using 1 <;> (dsimp [σ] <;> simp [Semiformula.free,Rewriting.free,Semiformula.rewAux,mulPrefix_rew,Rew.free,Rew.q,Rew.func])
  have out := prefixExistsIntro (u+1) (base+1) (z+1) 0 (ND.up (Ordinal.zeroShift z hz) σ.free) hg
  convert out using 1 <;> (dsimp [C,σ,mulPrefixExists] <;> simp [Semiformula.shift,Rewriting.shift,Semiformula.rewAux,Ordinal.zero_rew,mulPrefix_rew,Rew.shift,Rew.q,Rew.func])
#print axioms stepWithZero
end PA194MulRecurrenceNew
