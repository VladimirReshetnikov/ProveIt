import PA194ZeroIsoSuccExists
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194ForwardZeroSucc
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
variable {Γ : List Form}

def zeroSuccEqAt (a : Nat) : Form :=
  ∃⁰ ∃⁰ ((Ordinal.domain (.bvar 1) ⋏ Ordinal.zero (.bvar 1)) ⋏
    ((Ordinal.domain (.bvar 0) ⋏ (∃⁰ ((Ordinal.domain (.bvar 0) ⋏ eq (.bvar 0) (.fvar a)) ⋏
      Ordinal.successor (.bvar 0) (.bvar 1)))) ⋏ orderIso (.bvar 1) (.bvar 0)))

def equalityFalse (a : Nat) (E : FormulaEquality Γ) (he : ND.Proof Γ (zeroSuccEqAt a)) : ND.Proof Γ ⊥ := by
  let P : Ordinal.Formula 1 := ∃⁰ ((Ordinal.domain (.bvar 1) ⋏ Ordinal.zero (.bvar 1)) ⋏
    ((Ordinal.domain (.bvar 0) ⋏ (∃⁰ ((Ordinal.domain (.bvar 0) ⋏ eq (.bvar 0) (.fvar a)) ⋏
      Ordinal.successor (.bvar 0) (.bvar 1)))) ⋏ orderIso (.bvar 1) (.bvar 0)))
  have hp : ND.Proof Γ (∃⁰ P) := by convert he using 1 <;> rfl
  apply ND.exsElim hp
  let Δ := P.free :: ND.shifted Γ
  let Q : Ordinal.Formula 1 := ((Ordinal.domain (.fvar 0) ⋏ Ordinal.zero (.fvar 0)) ⋏
    ((Ordinal.domain (.bvar 0) ⋏ (∃⁰ ((Ordinal.domain (.bvar 0) ⋏ eq (.bvar 0) (.fvar (a+1))) ⋏
      Ordinal.successor (.bvar 0) (.bvar 1)))) ⋏ orderIso (.fvar 0) (.bvar 0)))
  have hq : ND.Proof Δ (∃⁰ Q) := by
    have h := ND.assumption (Γ := Δ) (p := P.free) (by simp [Δ])
    convert h using 1 <;> (dsimp [P,Q] <;> simp only [Ordinal.successor,sourceIff,sourceImply] <;> isoSyntax)
  apply ND.exsElim hq
  let Ψ := Q.free :: ND.shifted Δ
  have hall : ND.Proof Ψ ((Ordinal.domain (.fvar 1) ⋏ Ordinal.zero (.fvar 1)) ⋏
    ((Ordinal.domain (.fvar 0) ⋏ (∃⁰ ((Ordinal.domain (.bvar 0) ⋏ eq (.bvar 0) (.fvar (a+2))) ⋏
      Ordinal.successor (.bvar 0) (.fvar 0)))) ⋏ orderIso (.fvar 1) (.fvar 0))) := by
    have h := ND.assumption (Γ := Ψ) (p := Q.free) (by simp [Ψ])
    convert h using 1 <;> (dsimp [Q] <;> simp only [Ordinal.successor,sourceIff,sourceImply] <;> isoSyntax)
  have hz := ND.andRight (ND.andLeft hall)
  have hi := ND.andRight (ND.andRight hall)
  have hsucc := ND.andRight (ND.andLeft (ND.andRight hall))
  have E1 : FormulaEquality Δ := E.shifted.weaken (fun _ hp => List.mem_cons_of_mem _ hp)
  have E2 : FormulaEquality Ψ := E1.shifted.weaken (fun _ hp => List.mem_cons_of_mem _ hp)
  have out := existsSuccFalse 1 0 (a+2) E2 hz hi hsucc
  convert out using 1 <;> isoSyntax
#print axioms equalityFalse
end PA194ForwardZeroSucc
