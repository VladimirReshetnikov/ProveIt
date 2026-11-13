import DiophantineConsistency.Compact44.FreeJPowerCancel
import DiophantineConsistency.ArithmeticRadixAlignment
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FreeJRadixAlignment
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.Ordinary12FreeJ
open DiophantineConsistency.ArithmeticRadixAlignment
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_alignment (p : Fin 4 → ℕ) (v : Fin 12 → V) (d : V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀ j,0<v j) (hz : InternalZero (literal (fun j => (p j:ℤ))) v)
    (hbeta : (46:V)≤(p 0:V)) (hd : 4≤d)
    (hport : (p 0:V)=Exp.exp d-1) :
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    ∃ N w : V, 0<N ∧ q=Exp.exp (d*N) ∧ d*N≤R ∧
      w=Exp.exp (R-d*N) ∧ v 5=q*w := by
  let q : V := 1+v 0*(p 0:V)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  have hd2 : 2≤d := le_trans (by norm_num : (2:V)≤4) hd
  have hq : q=(Exp.exp d-1)*v 0+1 := by dsimp [q]; rw [←hport]; ring
  have hx : v 5=Exp.exp R := FreeJPowerFinish.graph_power p v hb hl hh hv hz hbeta
  obtain ⟨w,hw⟩ := FreeJPowerCancel.graph_divides_power p v d hb hl hh hv hz hbeta hd hport
  have hfact : Exp.exp R=w*((Exp.exp d-1)*v 0+1) := by rw [←hq,hw]; ring
  obtain ⟨_,N,hN,hqN,hNR,hwexp⟩ := factor_alignment d (v 0) R w hd2 (hv 0) hfact
  have hqn : q=Exp.exp (d*N) := hq.trans hqN
  have hXq : v 5=q*w := by rw [hx,hw]
  exact ⟨N,w,hN,hqn,hNR,hwexp,hXq⟩
end FreeJRadixAlignment
#print axioms FreeJRadixAlignment.graph_alignment
