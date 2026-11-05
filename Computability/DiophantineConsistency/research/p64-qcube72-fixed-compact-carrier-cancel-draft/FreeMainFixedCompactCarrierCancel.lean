import FreeMainSameFirstIndexResidue
import FreeMainCarrierCancel

/-! Unchecked draft: same-zero compact index window and free-carrier cancellation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMainFixedCompactCarrierCancel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ArithmeticPellRecurrence
open FreeMainActualRankWindowCompact
attribute [local irreducible] CompactFixedBeta.betaNat CompactSymbolicPorts.lowNat
  CompactSymbolicPorts.highNat Nat.ofDigits CompactListMask.digits
  CompactConcreteMask.support CompactHighPopulation.highDigits CompactConcreteIncrement.mask
  compactPorts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem fixed_data (K : ℕ) (v : Fin 14 → V) (hv : ∀ i,0<v i)
    (hz : InternalZero (P64QCube72Free.graph
      (fun j => (compactPorts K j:ℤ))).output v) :
    let p := compactPorts K
    let q : V := (p 0:V)*v 0+1
    let Y := q*q*q*v 7
    let X := v 8*q
    let P := (X*Y)*Y
    let k := v 10+v 11
    let R := FreeMainAuxNorm.rank p v
    ∃ n s e mu : V, n<R ∧ R<2*n ∧
      xcoord n (2*(P-1)+1)=v 9 ∧ 2*ycoord n (2*(P-1)+1)=k ∧
      k=2*n+4*P*s ∧ 0<e ∧ Y*Y=e*mu ∧ e∣9 ∧ 0<mu ∧
      q*(q*(q*q))≤mu ∧ mu∣v 13 := by
  let p := compactPorts K
  let q : V := (p 0:V)*v 0+1
  let Y : V := q*q*q*v 7
  let X : V := v 8*q
  let P : V := (X*Y)*Y
  let k : V := v 10+v 11
  let c : V := k*Y+v 10
  let R : V := FreeMainAuxNorm.rank p v
  have hb := CompactSymbolicMaskData.data (V:=V)
  have hq33 : 33≤q := by
    dsimp only [q,p]
    rw [compactPorts_zero]
    exact FreeMainSymbolicPortRankedMain.q_lower (CompactFixedBeta.betaNat:V) (v 0)
      hb.2.2.2 (hv 0)
  have hq3 : 3≤q := le_trans (by norm_num) hq33
  have hY : Y=q*(q*q)*v 7 := by dsimp [Y]; ring
  obtain ⟨g,_,hcar⟩ := FreeMainGraphMainRoot.main_root p v hv hz
  change (Y*Y)*g=(Y*Y)*(X+(X*Y+Y)*c)+(4*(X*Y+Y)+3)*v 13 at hcar
  obtain ⟨e,mu,he,hU,he9,hmu,hbound,hdiv⟩ :=
    FreeMainCarrierCancel.cancel q X Y (v 7) g c (v 13) hq3 (hv 7) hY hcar
  obtain ⟨n,s,hn1,hn2,hnx,hny,hks⟩ := FreeMainSameFirstIndexResidue.fixed_window_residue K v hv hz
  exact ⟨n,s,e,mu,hn1,hn2,hnx,hny,hks,he,hU,he9,hmu,hbound,hdiv⟩

#print axioms fixed_data
end FreeMainFixedCompactCarrierCancel
