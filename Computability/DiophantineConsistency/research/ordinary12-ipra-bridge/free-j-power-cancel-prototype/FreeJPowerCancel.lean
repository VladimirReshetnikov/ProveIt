import DiophantineConsistency.FreeJPowerFinish
import DiophantineConsistency.ArithmeticAdaptiveMersenne2011
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FreeJPowerCancel
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.Ordinary12FreeJ
open DiophantineConsistency.ArithmeticAdaptiveMersenne2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_divides_power (p : Fin 4 → ℕ) (v : Fin 12 → V) (d : V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀ j,0<v j) (hz : InternalZero (literal (fun j => (p j:ℤ))) v)
    (hbeta : (46:V)≤(p 0:V)) (hd : 4≤d)
    (hport : (p 0:V)=Exp.exp d-1) :
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    q∣Exp.exp R := by
  let q : V := 1+v 0*(p 0:V)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  have hp : v 5=Exp.exp R := FreeJPowerFinish.graph_power p v hb hl hh hv hz hbeta
  have hq3 : q∣3*Exp.exp R := by
    have hx := (FreeJPowerProjection.graph_projection p v hb hl hh hv hz).1
    rw [hp] at hx
    exact hx
  have hq : q=(Exp.exp d-1)*v 0+1 := by dsimp [q]; rw [←hport]; ring
  exact cancel_three d R q (v 0) hd hq hq3
end FreeJPowerCancel
#print axioms FreeJPowerCancel.graph_divides_power
