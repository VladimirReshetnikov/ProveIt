import DiophantineConsistency.BFS943.Direct80Parity
import DiophantineConsistency.BFS943.Direct80Coprime
import DiophantineConsistency.BFS943.Direct80RankExact

/-! Bind odd beta and exact rank to the 80 graph's even radix and unit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Direct80GraphParity
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ArithmeticGcdNormalization
open TenPositive80Graph TenPositive80Factors TenPositive80NaturalRank TenPositive80RankExact
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_even_and_unit (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v)
    (hbeta : ∃u : V, (p 0:V)=2*u+1) :
    (∃w : V, q p v=2*w) ∧ Bez (b p v) (mu p v*mu p v) 1 := by
  have hodd := (graph_rank_exact p v hb hl hh hv hz).2.2.1
  let G : V := b p v*(q p v-v 1)+v 2
  let T : V := (p 2:V)+q p v*(p 3:V)
  have hq : q p v=(p 0:V)*v 0+1 := by rfl
  have hR : rankNat p v=G*(q p v*q p v-1)+v 0*T := by
    dsimp [rankNat,G,T]
    ring
  have heven := Direct80Parity.odd_rank_even_radix (p 0:V) (v 0) (q p v) G T (rankNat p v)
    hbeta hq hR hodd
  exact ⟨heven,Direct80Coprime.square_unit_certificate (b p v) (q p v) (mu p v) rfl rfl heven⟩

#print axioms Direct80GraphParity.graph_even_and_unit
end Direct80GraphParity
