import Absorb88MainBalance
import Mathlib.Tactic.LinearCombination

/-! Draft: signed rank divisibility from the oriented 88 main factor. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace Absorb88SignedRankDivisor
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open Absorb88MainBalance Absorb88MainEvaluation
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_signed_rank_divisor (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (FreeJAbsorb88.graph (Absorb88First.integerPorts p)).output v) :
    let b : V := v 0*(p 0:V)
    let q : V := 1+b
    let X : V := q*v 5
    let Y : V := (q*(q*q))*v 6
    let k : V := v 8+v 9
    let a : V := X*Y+Y
    let H : V := 3+4*a
    let A : V := (p 1:V)+v 5
    let Bp : V := q*A
    let Bn : V := (v 1+v 2)*A+v 1
    let G : DiffRing V := ι (v 2)+(ι b)*(ι q-ι (v 1))
    let rank : DiffRing V := ((ι q)*(ι q)-1)*G+ι (v 0)*(ι (p 2:V)+ι (p 3:V)*ι q)
    (ι Bp : DiffRing V)<ι Bn →
      (ι q : DiffRing V)^5 ∣ ι H*(ι k-rank-1) := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let X : V := q*v 5
  let Y : V := (q*(q*q))*v 6
  let k : V := v 8+v 9
  let a : V := X*Y+Y
  let W : V := Y*(q*q)
  let H : V := 3+4*a
  let A : V := (p 1:V)+v 5
  let Bp : V := q*A
  let Bn : V := (v 1+v 2)*A+v 1
  let G : DiffRing V := ι (v 2)+(ι b)*(ι q-ι (v 1))
  let rank : DiffRing V := ((ι q)*(ι q)-1)*G+ι (v 0)*(ι (p 2:V)+ι (p 3:V)*ι q)
  change (ι Bp : DiffRing V)<ι Bn → (ι q : DiffRing V)^5 ∣ ι H*(ι k-rank-1)
  intro hn
  obtain ⟨g,_,hD⟩ := graph_main_balance p v hb hv hz hn
  rw [main_expression] at hD
  change (ι W : DiffRing V)*(ι X+ι a*(ι (v 8)+ι Y*ι k))+
    ι H*(ι W*ι (v 11)-ι k+rank+1)=ι W*ι g at hD
  have hfactor : (ι H : DiffRing V)*(ι k-rank-1) =
      ι W*(ι X+ι a*(ι (v 8)+ι Y*ι k)+ι H*ι (v 11)-ι g) := by
    linear_combination -hD
  have hW : (ι W : DiffRing V)=(ι q)^5*ι (v 6) := by
    simp only [W,Y,map_mul]
    ring
  refine ⟨ι (v 6)*(ι X+ι a*(ι (v 8)+ι Y*ι k)+ι H*ι (v 11)-ι g),?_⟩
  rw [hfactor,hW]
  ring

#print axioms Absorb88SignedRankDivisor.graph_signed_rank_divisor
end Absorb88SignedRankDivisor
