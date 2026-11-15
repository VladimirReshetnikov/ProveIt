import PA194ZeroIsoSuccFalse
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194ForwardZeroSucc
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
variable {Γ : List Form}

def existsSuccFalse (a b c : Nat) (E : FormulaEquality Γ)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar a)))
    (hi : ND.Proof Γ (orderIso (.fvar a) (.fvar b)))
    (he : ND.Proof Γ (∃⁰ ((Ordinal.domain (.bvar 0) ⋏ eq (.bvar 0) (.fvar c)) ⋏
      Ordinal.successor (.bvar 0) (.fvar b)))) : ND.Proof Γ ⊥ := by
  apply ND.exsElim he
  let P : Ordinal.Formula 1 := (Ordinal.domain (.bvar 0) ⋏ eq (.bvar 0) (.fvar c)) ⋏
    Ordinal.successor (.bvar 0) (.fvar b)
  let Δ := P.free :: ND.shifted Γ
  have ep : ND.Proof Δ P.free := ND.assumption (by simp [Δ])
  have hs : ND.Proof Δ (Ordinal.successor (.fvar 0) (.fvar (b+1))) := by
    have hh := ND.andRight ep
    convert hh using 1 <;> (try dsimp [P] <;> simp only [Ordinal.successor,sourceIff,sourceImply] <;> isoSyntax)
  have hz' : ND.Proof Δ (Ordinal.zero (.fvar (a+1))) := by
    have hh := ND.up (ND.shiftProof hz) P.free
    convert hh using 1 <;> isoSyntax
  have hi' : ND.Proof Δ (orderIso (.fvar (a+1)) (.fvar (b+1))) := by
    have hh := ND.up (ND.shiftProof hi) P.free
    convert hh using 1 <;> isoSyntax
  have E' : FormulaEquality Δ := E.shifted.weaken (fun _ hp => List.mem_cons_of_mem _ hp)
  have out := zeroIsoSuccFalse (a+1) (b+1) 0 E' hz' hi' hs
  convert out using 1 <;> isoSyntax
#print axioms existsSuccFalse
end PA194ForwardZeroSucc
