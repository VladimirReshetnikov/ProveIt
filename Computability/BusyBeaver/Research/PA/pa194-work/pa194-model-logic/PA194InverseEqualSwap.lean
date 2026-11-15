import PA194InverseEqualIntro
import PA194InverseSymmetryInputs
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194InverseEqual
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194InverseSymmetryInputs
variable {Γ : List Form}

def equalSwapWithLeft (a b x : Nat) (I : Inputs Γ)
    (hx : ND.Proof Γ (Ordinal.domain (.fvar x) ⋏ eq (.fvar x) (.fvar a)))
    (he : ND.Proof Γ (∃⁰ ((Ordinal.domain (.bvar 0) ⋏ eq (.bvar 0) (.fvar b)) ⋏
      orderIso (.fvar x) (.bvar 0)))) : ND.Proof Γ (equalAt b a) := by
  apply ND.exsElim he
  let P : Ordinal.Formula 1 := (Ordinal.domain (.bvar 0) ⋏ eq (.bvar 0) (.fvar b)) ⋏
    orderIso (.fvar x) (.bvar 0)
  let Δ := P.free :: ND.shifted Γ
  have hp : ND.Proof Δ ((Ordinal.domain (.fvar 0) ⋏ eq (.fvar 0) (.fvar (b+1))) ⋏
      orderIso (.fvar (x+1)) (.fvar 0)) := by
    have h := ND.assumption (Γ := Δ) (p := P.free) (by simp [Δ])
    convert h using 1
    simp [P,Semiformula.free,Rewriting.free,Semiformula.rewAux,domain_rew,orderIso_rew,eq,Rew.free,Rew.q]
  have hx' : ND.Proof Δ (Ordinal.domain (.fvar (x+1)) ⋏ eq (.fvar (x+1)) (.fvar (a+1))) := by
    have h := ND.up (ND.shiftProof hx) P.free
    convert h using 1
    change _ = Semiformula.rewAux Rew.shift _
    simp [Semiformula.rewAux,domain_rew,eq,Rew.shift,Rew.map]
  let J := I.shift.weaken (fun _ hp => List.mem_cons_of_mem P.free hp)
  have hi := J.inverse (x+1) 0 (ND.andLeft hx') (ND.andRight hp)
  change ND.Proof Δ (equalAt b a).shift
  rw [equalAt_shift]
  exact equalFromWitnesses (b+1) (a+1) 0 (x+1) (ND.andLeft hp) hx' hi

def equalSwap (a b : Nat) (I : Inputs Γ) (he : ND.Proof Γ (equalAt a b)) :
    ND.Proof Γ (equalAt b a) := by
  apply ND.exsElim he
  let P : Ordinal.Formula 1 := ∃⁰
    ((Ordinal.domain (.bvar 1) ⋏ eq (.bvar 1) (.fvar a)) ⋏
      ((Ordinal.domain (.bvar 0) ⋏ eq (.bvar 0) (.fvar b)) ⋏ orderIso (.bvar 1) (.bvar 0)))
  let Δ := P.free :: ND.shifted Γ
  have hp : ND.Proof Δ (∃⁰ ((Ordinal.domain (.fvar 0) ⋏ eq (.fvar 0) (.fvar (a+1))) ⋏
      ((Ordinal.domain (.bvar 0) ⋏ eq (.bvar 0) (.fvar (b+1))) ⋏ orderIso (.fvar 0) (.bvar 0)))) := by
    have h := ND.assumption (Γ := Δ) (p := P.free) (by simp [Δ])
    convert h using 1
    simp [P,Semiformula.free,Rewriting.free,Semiformula.rewAux,domain_rew,orderIso_rew,eq,Rew.free,Rew.q]
  let J := I.shift.weaken (fun _ hp => List.mem_cons_of_mem P.free hp)
  change ND.Proof Δ (equalAt b a).shift
  rw [equalAt_shift]
  apply ND.exsElim hp
  let Q : Ordinal.Formula 1 := ((Ordinal.domain (.fvar 0) ⋏ eq (.fvar 0) (.fvar (a+1))) ⋏
      ((Ordinal.domain (.bvar 0) ⋏ eq (.bvar 0) (.fvar (b+1))) ⋏ orderIso (.fvar 0) (.bvar 0)))
  let Ω := Q.free :: ND.shifted Δ
  have hq : ND.Proof Ω ((Ordinal.domain (.fvar 1) ⋏ eq (.fvar 1) (.fvar (a+1+1))) ⋏
      ((Ordinal.domain (.fvar 0) ⋏ eq (.fvar 0) (.fvar (b+1+1))) ⋏ orderIso (.fvar 1) (.fvar 0))) := by
    have h := ND.assumption (Γ := Ω) (p := Q.free) (by simp [Ω])
    convert h using 1
    simp [Q,Semiformula.free,Rewriting.free,Semiformula.rewAux,domain_rew,orderIso_rew,eq,Rew.free,Rew.q]
  let K := J.shift.weaken (fun _ hp => List.mem_cons_of_mem Q.free hp)
  have hi := K.inverse 1 0 (ND.andLeft (ND.andLeft hq)) (ND.andRight (ND.andRight hq))
  change ND.Proof Ω (equalAt (b+1) (a+1)).shift
  rw [equalAt_shift]
  exact equalFromWitnesses (b+1+1) (a+1+1) 0 1 (ND.andLeft (ND.andRight hq)) (ND.andLeft hq) hi
#print axioms equalSwapWithLeft
#print axioms equalSwap
end PA194InverseEqual
