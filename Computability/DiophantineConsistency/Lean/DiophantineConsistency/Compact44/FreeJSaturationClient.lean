import DiophantineConsistency.Compact44.FreeJPopulationClient
import DiophantineConsistency.ArithmeticSaturation
import DiophantineConsistency.ArithmeticMaskPopulation
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FreeJSaturationClient
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open ArithmeticBinaryPopulation ArithmeticBinaryCarry ArithmeticRepunit
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Conditional graph saturation; the port split, repeated-mask population
facts and radix identification remain explicit hypotheses. -/
theorem graph_saturation (p : Fin 4 → ℕ) (v : Fin 12 → V) (d N HP : V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀ j,0<v j) (hz : InternalZero (literal (fun j => (p j:ℤ))) v)
    (hbeta : (46:V)≤(p 0:V)) (hd : 3≤d) (hN : 0<N)
    (hq : 1+v 0*(p 0:V)=Exp.exp (d*N)) (hJ : v 0=rep d N)
    (hport : (p 3:V)=HP+(p 0:V))
    (hMC : (p 2:V)<Exp.exp d) (hHP : HP<Exp.exp d)
    (hMC2 : (p 2:V)%2=0) (hHP8 : HP%8=4)
    (hsum : population (p 2:V)+population HP=d) (hHPJ : 1≤HP*v 0) :
    let q : V := 1+v 0*(p 0:V)
    NoCarry (q-v 1-v 2-1) ((p 2:V)*v 0+1) ∧
      NoCarry (v 1) (HP*v 0-1) := by
  let q : V := 1+v 0*(p 0:V)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  let A : V := q-v 1-v 2-1
  let M : V := (p 2:V)*v 0+1
  let H : V := HP*v 0-1
  change NoCarry A M ∧ NoCarry (v 1) H
  have hgap : 0<q-v 1-v 2 := by
    simpa only [tsub_tsub] using (FreeJFirstTransport.freej_first_factor_transport p v hb hv hz).2
  have hlt : v 1+v 2<q := tsub_pos_iff_lt.mp (by simpa only [tsub_tsub] using hgap)
  have hF : v 1 < q := lt_of_le_of_lt (by simp : v 1 ≤ v 1+v 2) hlt
  have hqpos : 0<q := lt_of_lt_of_le (hv 1) (le_of_lt hF)
  have hA : A<Exp.exp (d*N) := by
    rw [←hq]
    dsimp [A]
    have h : q-v 1<q := tsub_lt_self hqpos (hv 1)
    exact lt_of_le_of_lt (le_trans tsub_le_self tsub_le_self) h
  have hFl : v 1<Exp.exp (d*N) := by rw [←hq]; exact hF
  have hqdef : q=(p 0:V)*v 0+1 := by dsimp [q]; ring
  have hfour := ArithmeticSaturation.four_block q (p 0:V) (v 0) (v 1) (v 2) (p 2:V) HP hqdef hgap hHPJ
  have hrank : R = A+M+Exp.exp (d*N)*(v 1+H)+
      Exp.exp (d*N)^2*(Exp.exp (d*N)-1-A)+Exp.exp (d*N)^3*(Exp.exp (d*N)-1-v 1) := by
    rw [←hq]
    dsimp only [R,A,M,H]
    rw [hport]
    exact hfour
  have hMH : population M+population H≤d*N+2 := by
    dsimp [M,H]
    rw [hJ, ArithmeticMaskPopulation.repeated_mask_population d N (p 2:V) HP hd hN hMC hHP hMC2 hHP8 hsum]
  have hpop : 3*(d*N)+2≤population R :=
    FreeJPopulationClient.graph_population p v (d*N) hb hl hh hv hz hbeta hq
  exact ArithmeticSaturation.saturation (d*N) A (v 1) M H R hA hFl hrank hMH hpop
end FreeJSaturationClient
#print axioms FreeJSaturationClient.graph_saturation
