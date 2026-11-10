import DiophantineConsistency.BFS943.Direct80Factors
import DiophantineConsistency.ArithmeticAdaptiveRankWindow2011

/-! Rank window after a proved transport gap. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Direct80RankWindow
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticAdaptiveRankWindow2011
open TenPositive80Factors
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def rank (p : Fin 4 → ℕ) (v : Fin 10 → V) : V :=
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)

theorem window (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hgap : v 1+v 2<1+v 0*(p 0:V)) :
    let q : V := 1+v 0*(p 0:V)
    24≤rank p v ∧ rank p v+q^3+q+1≤q^4 := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let R : V := rank p v
  have hq : q=(p 0:V)*v 0+1 := by dsimp [q,b]; ring_nf
  have hw := scalar_rank_window q (p 0:V) (p 2:V) (p 3:V) (v 0) (v 1) (v 2)
    hb (hv 0) (hv 1) (hv 2) hl hh hq hgap
  have hqb : q-1=b := by dsimp [q]; rw [add_comm]; simp
  have hR : ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0 = R := by
    change ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0 =
      (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)
    rw [hqb]
    ring_nf
  rw [hR] at hw
  exact hw

#print axioms Direct80RankWindow.window
end Direct80RankWindow
