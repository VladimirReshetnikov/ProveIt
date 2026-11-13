import Absorb88SignedRankDivisor
import Absorb88SignedCancel

/-! Draft: signed q⁴ rank congruence on the actual 88 negative branch. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace Absorb88SignedRankCongruence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open Absorb88SignedRankDivisor Absorb88SignedCancel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_signed_rank_congruence (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (FreeJAbsorb88.graph (Absorb88First.integerPorts p)).output v) :
    let b : V := v 0*(p 0:V)
    let q : V := 1+b
    let k : V := v 8+v 9
    let A : V := (p 1:V)+v 5
    let Bp : V := q*A
    let Bn : V := (v 1+v 2)*A+v 1
    let G : DiffRing V := ι (v 2)+(ι b)*(ι q-ι (v 1))
    let rank : DiffRing V := ((ι q)*(ι q)-1)*G+ι (v 0)*(ι (p 2:V)+ι (p 3:V)*ι q)
    (ι Bp : DiffRing V)<ι Bn → (ι q : DiffRing V)^4 ∣ ι k-rank-1 := by
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
  change (ι Bp : DiffRing V)<ι Bn → (ι q : DiffRing V)^4 ∣ ι k-rank-1
  intro hn
  have hq : 0<q := by dsimp [q]; simp
  have hy : q^3∣Y := ⟨v 6,by dsimp [Y]; ring⟩
  have hH : H=3+4*Y*(X+1) := by dsimp [H,a]; ring
  have hd := graph_signed_rank_divisor p v hb hv hz hn
  change (ι q : DiffRing V)^5 ∣ ι H*(ι k-rank-1) at hd
  have hd' : (ι (q^5) : DiffRing V) ∣ ι (3+4*Y*(X+1))*(ι k-rank-1) := by
    rw [←hH]
    simpa only [map_pow] using hd
  have hc := cancel_signed q Y X (ι k-rank-1) hq hy hd'
  simpa only [map_pow] using hc

#print axioms Absorb88SignedRankCongruence.graph_signed_rank_congruence
end Absorb88SignedRankCongruence
