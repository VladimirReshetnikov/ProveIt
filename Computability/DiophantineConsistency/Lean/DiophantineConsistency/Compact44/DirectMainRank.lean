import DiophantineConsistency.Compact44.DirectMainIndices
import DiophantineConsistency.ArithmeticAdaptiveRankCongruence2011

/-! Rank congruence from a direct-main balance; no index alignment yet. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DirectMainRank
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency FreeJDirectMainGraph
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticPellRecurrence
open ArithmeticAdaptiveFactorThree2011 ArithmeticAdaptiveFirstDivisibility2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem rank_of_balance (q Y X a c H G R k s main : V)
    (hq : 0<q) (hy : Y=q^3*s) (hH : H=3+4*Y*(X+1))
    (he : H*(R+1)+q^5*(s*(X+a*c+H*G)) = H*k+q^5*(s*main)) :
    q^4 ∣ magnitude (R+1,k) := by
  have hm5 : 0<q^5 := pow_pos hq _
  have hm4 : 0<q^4 := pow_pos hq _
  have hemod : (H*(R+1))%(q^5)=(H*k)%(q^5) := by
    have h := congrArg (fun z : V => z%(q^5)) he
    rw [mod_add_mul' _ _ hm5,mod_add_mul' _ _ hm5] at h
    exact h
  have hdiv : q^5∣H*magnitude (R+1,k) := by
    have h := dvd_magnitude_of_mod hm5 hemod
    have heq : magnitude (H*(R+1),H*k)=H*magnitude (R+1,k) := by
      dsimp [magnitude]
      rw [mul_add H ((R+1)-k) (k-(R+1)),mul_tsub H (R+1) k,mul_tsub H k (R+1)]
    rwa [heq] at h
  rw [hH] at hdiv
  have hY : q^3∣Y := ⟨s,hy⟩
  exact cancel_factor_three q Y X _ hq hY hdiv

theorem graph_rank (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (DirectMainFirst.integerPorts p)).output v) :
    let b : V := v 0*(p 0:V)
    let q : V := 1+b
    let k : V := v 8+v 9
    let R : V := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)
    q^4 ∣ magnitude (R+1,k) := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let X : V := q*v 5
  let Y : V := (q*(q*q))*v 6
  let U : V := Y*(q*q)
  let k : V := v 8+v 9
  let c : V := v 8+Y*k
  let a : V := X*Y+Y
  let H : V := 3+4*a
  let R : V := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)
  have hq : 0<q := by dsimp [q,b]; simp
  have hy : Y=q^3*v 6 := by dsimp [Y]; ring
  have hU : U=q^5*v 6 := by dsimp [U,Y]; ring
  have hH : H=3+4*Y*(X+1) := by dsimp [H,a]; ring
  obtain ⟨first,main,n,m,hfirst,hmain,hbalance,hn,hm,hnk,hmc,hnx,hny,hmx,hmy⟩ :=
    DirectMainIndices.graph_indices p v hb hv hz
  have he : H*(R+1)+q^5*(v 6*(X+a*c+H*v 11)) = H*k+q^5*(v 6*main) := by
    calc
      H*(R+1)+q^5*(v 6*(X+a*c+H*v 11)) =
          U*(X+a*c)+H*(U*v 11+R+1) := by rw [hU]; ring
      _ = H*k+U*main := hbalance
      _ = H*k+q^5*(v 6*main) := by rw [hU]; ring
  exact rank_of_balance q Y X a c H (v 11) R k (v 6) main hq hy hH he

#print axioms DirectMainRank.rank_of_balance
#print axioms DirectMainRank.graph_rank
end DirectMainRank
