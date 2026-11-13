import DiophantineConsistency.BFS943.DirectBFSHaltRank
import DiophantineConsistency.Compact44.CompactOuterPellSeed
import DiophantineConsistency.Compact44.CompactCalibratedTransport
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace DirectBFSHaltPellSeed
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticBinaryCarry ArithmeticPow ArithmeticPacking ArithmeticRepunit
open ArithmeticPellRecurrence ArithmeticPellHalfIndex ArithmeticOuterSeed
open CompactSymbolicPorts CompactConstructedRank CompactRankResidueJoin CompactOuterPellSeed CompactCalibratedTransport
open DirectBFSConstructedWord DirectBFSFourFieldsPacking DirectBFSHaltCanonicalPacking
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] DirectBFSFourFieldsPacking.kernel DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho CompactSymbolicPorts.highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def SeedBundle (K N s : V) (X : V → V) [𝚺₁-Function₁ X] : Prop :=
  let u := (590069:V)*N
  let R := rank K N s X
  ∃ sY n eta zeta gamma : V,
    0<sY ∧ 0<n ∧ 0<eta ∧ 0<zeta ∧ 0<gamma ∧
    SeedRelations u R sY n eta zeta gamma ∧
    sY*Exp.exp u^3 ≤ power (Exp.exp R+1) R ∧
    (let Y := sY*Exp.exp u^3
    let a := Exp.exp R*Y+Y
    let c := ycoord R a
    ∃ f i T w y : V, 0 < f ∧ 0 < i ∧ 0 < T ∧ 0 < w ∧ 0 < y ∧
      f=xcoord (R*c) a ∧ ycoord (R*c) a=i*c*c ∧
      f*f=1+delta a*(i*c*c)*(i*c*c) ∧
      let I := delta a*i*c*c
      y=ycoord R (I-2) ∧ xcoord R (I-2)=I*w ∧
      w=oddQuotient ((R-1)/2) (I-2) ∧
      (w+c)%(f*f)=0 ∧ (w+R)%c=0 ∧
      f*f*c*T=w+c+f*f*R ∧ w=absdiff (f*f*c*T) (f*f*R+c) ∧
      I*I*w*w+y*y=1+I*I*y*y)


theorem halt_seeds_transport (T : V)
    (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T)=0) :
    ∃ δ : V → V, (𝚺₁-Function₁ δ) ∧ (∀ j, δ j≤1) ∧
      (∀ j, δ j≠0 → 0<j ∧ j+1<length T ∧ j+stride T<length T) ∧
      let X := cellWord (row T) δ
      PackingInput 590069 (kernel:V) CompactConcreteIncrement.mask (highNat:V) (length T) (stride T) X ∧
      (𝚺₁-Function₁ X) ∧
      (∀ [𝚺₁-Function₁ X],
        rank (kernel:V) (length T) (stride T) X % (590069*length T) =
          (590069*stride T) % (590069*length T) ∧
        SeedBundle (kernel:V) (length T) (stride T) X ∧
        let R := rank (kernel:V) (length T) (stride T) X
        let q := Exp.exp (590069*length T)
        let w := Exp.exp (R-590069*length T)
        let C := Cw 590069 (length T) X
        let F := Fw 590069 (kernel:V) (length T) (stride T) X
        ∃ z : V, 0<z ∧ q*w=Exp.exp R ∧ ((kernel:V)+w)*C=F+z*(q-1)) := by
  letI : 𝚺₁-Function₁ (fun _ : V => (0:V)) := by definability
  let N := length T
  let s := stride T
  let c : V := (low+Exp.exp (590069*N)*(high+(Exp.exp (590069:V)-1)))*rep 590069 N
  obtain ⟨δ,hd,hb,hs,hpack,hcal⟩ := DirectBFSHaltRank.halt_rank T c hT
  have hbase := DirectBFSHaltPacking.halt_pack T (fun _ => 0) hT (by simp)
  letI : 𝚺₁-Function₁ (row T) := hbase.1
  letI : 𝚺₁-Function₁ δ := hd
  have hx : 𝚺₁-Function₁ (cellWord (row T) δ) := cellWord_definable (row T) δ
  refine ⟨δ,hd,hb,hs,hpack,hx,?_⟩
  intro hX
  letI : 𝚺₁-Function₁ (cellWord (row T) δ) := hX
  have hp : PackingInput 590069 (kernel:V) low high N s (cellWord (row T) δ) := by
    simpa only [N,s,low,high,highNat] using hpack
  have hr := rank_eq_window (kernel:V) N s (cellWord (row T) δ)
  have hcal' : rank (kernel:V) N s (cellWord (row T) δ) % (590069*N) =
      (590069*s) % (590069*N) := by simpa only [N,s,c] using hr ▸ hcal
  have hseed : SeedBundle (kernel:V) N s (cellWord (row T) δ) := seeds hp
  have htr := calibrated_transport hp hbase.2.2.2.1 hbase.2.2.2.2.1 hcal'
  exact ⟨hcal',hseed,htr⟩
#print axioms DirectBFSHaltPellSeed.halt_seeds_transport
end DirectBFSHaltPellSeed
