import FreeMainGraphResiduals
import DiophantineConsistency.Compact44.P72Window

/-! Source-only draft: the actual 72 rank is positive and lies in the
compact-port window. No reverse implication is claimed here. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMainActualRankWindowGeneric
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open P64QCubeMap
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem one_le_cast {x : V} (h : 0 < x) : (1 : DiffRing V) ≤ ι x := by
  simpa using (ι_le_ι (V := V)).mpr (pos_iff_one_le.mp h)

/-- Ring-level form of the same rank, defined locally so the generic check
    does not import the much larger strict-auxiliary module. -/
def rankValue {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) : R :=
  let qm := (p 0:R)*v 0
  let q := qm+1
  let gap := qm*(q-v 1)+v 2
  gap*(q*q-1)+((p 2:R)+q*(p 3:R))*v 0

/-- The natural-model rank represented by the unchanged graph expression. -/
def rank (p : Fin 4 → ℕ) (v : Fin 14 → V) : V :=
  let q : V := (p 0:V)*v 0+1
  ((p 0:V)*v 0*(q-v 1)+v 2)*(q*q-1)+((p 2:V)+q*(p 3:V))*v 0

/-- Extract positivity and the quartic window from a positive actual zero,
assuming exactly the two port inequalities used by `P72Window`. -/
theorem actual_window (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hv : ∀ i, 0 < v i)
    (hz : InternalZero (P64QCube72Free.graph (fun j => (p j:ℤ))).output v)
    (hMC : (p 2:V) < (p 0:V)) (hMF : (p 3:V) < 2*(p 0:V)) :
    let q : V := (p 0:V)*v 0+1
    0 < rank p v ∧
      (ι (rank p v) : DiffRing V)+1 < (ι q)*(ι q*((ι q)*(ι q))) := by
  let pp : Fin 4 → ℤ := fun j => (p j:ℤ)
  let z : Fin 14 → DiffRing V := fun i => ι (v i)
  let w : Fin 14 → V := lift p v
  let q : V := (p 0:V)*v 0+1
  let R : V := rank p v
  obtain ⟨_,_,_,_,hlt⟩ := FreeMainGraphResiduals.residuals p v hv hz
  have hlt' : InternalZero (P64Graph.graph pp).Lt w := by
    rw [internalZero_iff]
    change (P64QCube72Free.graph pp).Lt.evalRing z=0 at hlt
    rw [FreeMainGraphResiduals.transport_same pp,P64QCube78GraphSplit.transport_same pp,
      ←P64QCubeBinding.transport pp z,←P64QCubeMap.lift_cast p v] at hlt
    exact hlt
  have hwp := P64QCubeMap.lift_pos p v hv
  have hgapW := (P64Root.transport p w hwp hlt').1
  have hgap : v 1+v 2<q := by simpa [w,lift,q] using hgapW
  have hF : w 1≤(p 0:V)*w 0+1 := le_trans (by simp) (le_of_lt hgapW)
  have hrank : rankValue pp z = ι R := by
    have he : rankValue pp z=(P64Graph.vals pp (P64QCubeMap.liftRing pp z)).RR := by
      simp [rankValue,P64Graph.vals,P64QCubeMap.liftRing]
    rw [he,←P64QCubeMap.lift_cast p v]
    simpa [w,lift,R,rank,q] using P64Root.c_RR p w hF
  let Q : DiffRing V := ι q
  let F : DiffRing V := ι (v 1)
  let A : DiffRing V := ι (v 2)
  let C : DiffRing V := ι (q-(v 1+v 2))
  let B : DiffRing V := ι (p 0:V)
  let J : DiffRing V := ι (v 0)
  let MC : DiffRing V := ι (p 2:V)
  let MF : DiffRing V := ι (p 3:V)
  have hCeq : C=Q-F-A := by
    dsimp [C,Q,F,A]
    rw [P72Root.ι_tsub (le_of_lt hgap)]
    simp only [map_add]
    ring
  have hQ : Q=F+(C+A) := by rw [hCeq]; ring
  have hC : 1≤C := one_le_cast (tsub_pos_of_lt hgap)
  have hF1 : 1≤F := one_le_cast (hv 1)
  have hA1 : 1≤A := one_le_cast (hv 2)
  have hJ1 : 1≤J := one_le_cast (hv 0)
  have hBJ : B*J=Q-1 := by
    dsimp [B,J,Q,q]
    simp only [map_add,map_mul,map_one]
    ring
  have hMC1 : MC+1≤B := by
    have h : (p 2:V)+1≤(p 0:V) := lt_iff_succ_le.mp hMC
    have hh := (ι_le_ι (V:=V)).mpr h
    simpa only [MC,B,map_add,map_one] using hh
  have hMF1 : MF+1≤2*B := by
    have h : (p 3:V)+1≤2*(p 0:V) := lt_iff_succ_le.mp hMF
    have hh := (ι_le_ι (V:=V)).mpr h
    simpa only [MF,B,map_add,map_mul,map_one,map_ofNat] using hh
  have hwin := P72Window.window_ring hQ hF1 hA1 hC hJ1 hBJ hMC1 hMF1
  have hshape : rankValue pp z = ((Q-1)*(Q-F)+A)*(Q*Q-1)+(MC+MF*Q)*J := by
    dsimp [rankValue,pp,z,Q,F,A,MC,MF,J,q]
    simp only [P64Root.cast_nat,map_add,map_mul,map_one]
    ring
  have hqr : (2:DiffRing V)<Q := by rw [hQ]; linarith
  have hgap0 : 0<(Q-1)*(Q-F)+A := by
    have h1 : 0≤Q-1 := by linarith
    have h2 : 0≤Q-F := by rw [hQ]; linarith
    have hA : 0<A := by linarith
    exact add_pos_of_nonneg_of_pos (mul_nonneg h1 h2) hA
  have hq2 : 0<Q*Q-1 := by
    have hs := mul_self_nonneg (Q-1)
    nlinarith
  have hmask : 0≤(MC+MF*Q)*J := by
    have hmc : 0≤MC := ι_nonneg _
    have hmf : 0≤MF := ι_nonneg _
    have hq : 0≤Q := by linarith
    have hj : 0≤J := by linarith
    exact mul_nonneg (add_nonneg hmc (mul_nonneg hmf hq)) hj
  have hRring : (0:DiffRing V)<ι R := by
    rw [←hrank,hshape]
    exact add_pos_of_pos_of_nonneg (mul_pos hgap0 hq2) hmask
  have hR : 0<R := (ι_lt_ι (V:=V)).mp (by simpa using hRring)
  have hwindow : (ι R:DiffRing V)+1<Q*(Q*(Q*Q)) := by
    rw [←hrank,hshape]
    exact hwin
  exact ⟨hR,hwindow⟩


#print axioms actual_window
end FreeMainActualRankWindowGeneric
