import PA194ForwardTyped
import PA194FoundationFormulaCongruence
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace M6.PA.RelationalSource
open LO LO.FirstOrder ND
open Ordinal (Term Formula)
open M6.PA.RelationalSource.PairGraph

def successorVariableValue (x z : Nat) : Form :=
  PA194ForwardTyped.value (PA194PAeq.succ (.bvar 0)) ![.fvar x] (fun i => .fvar i) (.fvar z)

def successorSourceTransport {Γ : List Form} (E : FormulaEquality Γ) (x y z : Nat)
    (hxy : ND.Proof Γ (eq (.fvar x) (.fvar y)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar x) (.fvar z))) :
    ND.Proof Γ (Ordinal.successor (.fvar y) (.fvar z)) := by
  have hp : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![.fvar x]) (Ordinal.successor (.bvar 0) (.fvar z))) := by
    convert hs using 1 <;> successorSyntax
  have out := E.substituteOne (Ordinal.successor (.bvar 0) (.fvar z)) (.fvar x) (.fvar y) hxy hp
  convert out using 1 <;> successorSyntax

def domainTransport {Γ : List Form} (E : FormulaEquality Γ) (x y : Nat)
    (hxy : ND.Proof Γ (eq (.fvar x) (.fvar y)))
    (hd : ND.Proof Γ (Ordinal.domain (.fvar x))) : ND.Proof Γ (Ordinal.domain (.fvar y)) := by
  have hp : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![.fvar x]) (Ordinal.domain (.bvar 0))) := by
    convert hd using 1 <;> (try ordinalSyntax)
  have out := E.substituteOne (Ordinal.domain (.bvar 0)) (.fvar x) (.fvar y) hxy hp
  convert out using 1 <;> (try ordinalSyntax)

/-- Normalize the value of a successor applied to a source variable. -/
def successorVariableValue_forward {Γ : List Form} (E : FormulaEquality Γ) (x z : Nat)
    (h : ND.Proof Γ (successorVariableValue x z)) :
    ND.Proof Γ (Ordinal.domain (.fvar x) ⋏ (Ordinal.domain (.fvar z) ⋏ Ordinal.successor (.fvar x) (.fvar z))) := by
  have h0 : ND.Proof Γ (Ordinal.domain (.fvar z) ⋏ (∃⁰
      ((Ordinal.domain (.bvar 0) ⋏ eq (.bvar 0) (.fvar x)) ⋏ Ordinal.successor (.bvar 0) (.fvar z)))) := by
    convert h using 1 <;> (simp [successorVariableValue,PA194ForwardTyped.value,PA194PAeq.succ,PA194ForwardTyped.shiftEnv] <;> isoSyntax)
  have hz := andLeft h0
  have he := andRight h0
  apply exsElim he
  let σ : Formula 1 := (Ordinal.domain (.bvar 0) ⋏ eq (.bvar 0) (.fvar x)) ⋏ Ordinal.successor (.bvar 0) (.fvar z)
  let Δ := σ.free :: shifted Γ
  have inc : ∀ r, r ∈ shifted Γ → r ∈ Δ := fun r hr => List.mem_cons_of_mem _ hr
  let E' := E.shifted.weaken inc
  have hw : ND.Proof Δ ((Ordinal.domain (.fvar 0) ⋏ eq (.fvar 0) (.fvar (x+1))) ⋏ Ordinal.successor (.fvar 0) (.fvar (z+1))) := by
    have hmem : ND.Proof Δ σ.free := assumption (by simp [Δ])
    convert hmem using 1 <;> (dsimp [σ] <;> isoSyntax)
  have hx := domainTransport E' 0 (x+1) (andRight (andLeft hw)) (andLeft (andLeft hw))
  have hs := successorSourceTransport E' 0 (x+1) (z+1) (andRight (andLeft hw)) (andRight hw)
  have hz' : ND.Proof Δ (Ordinal.domain (.fvar (z+1))) := by
    have h := ND.weaken (ND.shiftProof hz) inc
    convert h using 1 <;> (try ordinalSyntax)
  have out := andIntro hx (andIntro hz' hs)
  convert out using 1 <;> (dsimp [σ,Δ] <;> isoSyntax)

def successorVariableValue_backward {Γ : List Form} (E : FormulaEquality Γ) (x z : Nat)
    (h : ND.Proof Γ (Ordinal.domain (.fvar x) ⋏ (Ordinal.domain (.fvar z) ⋏ Ordinal.successor (.fvar x) (.fvar z)))) :
    ND.Proof Γ (successorVariableValue x z) := by
  let σ : Formula 1 := (Ordinal.domain (.bvar 0) ⋏ eq (.bvar 0) (.fvar x)) ⋏ Ordinal.successor (.bvar 0) (.fvar z)
  have hw : ND.Proof Γ (σ/[.fvar x]) := by
    have h' := andIntro (andIntro (andLeft h) (E.reflexive (.fvar x))) (andRight (andRight h))
    convert h' using 1 <;> (dsimp [σ] <;> isoSyntax)
  have out := andIntro (andLeft (andRight h)) (exsIntro σ (.fvar x) hw)
  convert out using 1 <;> (simp [successorVariableValue,PA194ForwardTyped.value,PA194PAeq.succ,PA194ForwardTyped.shiftEnv] <;> isoSyntax)

#print axioms successorSourceTransport
#print axioms domainTransport
#print axioms successorVariableValue_forward
#print axioms successorVariableValue_backward
end M6.PA.RelationalSource
