import DiophantineConsistency.Mixed121.Mixed121Aligned
import DiophantineConsistency.Mixed121.Mixed121Rotation

/-! # The saturated, band-cut graph data at the 121x8801 ports

These are the next two links of the `LeafFacts` halting chain at the
121x8801 tuple.

* `saturated_aligned` is the counterpart of Compact44's
  `CompactSameWitnessSaturation.generic_graph_saturation_facts`. It gives
  `symbolic_aligned` together with the two saturation no-carry facts
  `NoCarry (C − 1) (MC·J + 1)` and `NoCarry F (MF·J − 1)`.
* `symbolic_bands` is the counterpart of
  `SymbolicGraphBand.symbolic_bands_facts`. Through `kernel_bands`, the
  first-pair congruence modulo `Jβ = 2^(121·8801N) − 1` becomes the congruence
  of the two rotated clause bands and the bare part of the native word `C`.
  `graph_congruence_to_bands` is Compact44's `ModelBandCut` step at width 121.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Mixed121Bands
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits Mixed121Rotation
attribute [local irreducible] Mixed121Ports.betaNat Mixed121Ports.lowNat Mixed121Ports.highNat
  Mixed121Kernel.paramKernel Mixed121Kernel.rho
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem ports_one (β K L H : ℕ) : CompactSymbolicPorts.ports β K L H 1 = K := rfl

theorem port_one :
    ((Mixed121Ports.ports 1 : ℕ) : V) =
      ((Mixed121Kernel.paramKernel Mixed121Kernel.rho : ℕ) : V) := by
  unfold Mixed121Ports.ports
  rw [ports_one]

theorem saturated_aligned (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Mixed121Ports.ports v) :
    let p := Mixed121Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    ∃ N w : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ v 0=rep (121*8801) N ∧
      (121*8801)*N≤R ∧ w=Exp.exp (R-(121*8801)*N) ∧ v 5=q*w ∧
      0<v 0*(p 0:V) ∧ v 1<v 0*(p 0:V) ∧
      (((p 1:V)+w)*C)%(v 0*(p 0:V))=v 1 ∧
      dig 121 C 0=1 ∧ (∀ k<8801*N, dig 121 C k≤3) ∧
      NoCarry (C-1) ((p 2:V)*v 0+1) ∧
      NoCarry (v 1) ((Mixed121Ports.highNat:V)*v 0-1) := by
  let p := Mixed121Ports.ports
  let d : V := 121*8801
  obtain ⟨N,w,hN,hq,hJ,hle,hw,hv5,hpos,hbound,hcongr,h0,hlim⟩ :=
    Mixed121Aligned.symbolic_aligned v hv hz
  obtain ⟨hb, hl, hh, hbeta⟩ := Mixed121Ports.leaf_bounds (V:=V)
  have hs := FreeJSaturationClient.graph_saturation_facts p v d N
    (Mixed121Ports.highNat : V) hb hl hh hv hz hbeta (by dsimp [d]; norm_num) hN hq hJ
    Mixed121Aligned.port_three
    (by rw [Mixed121Aligned.port_two]; exact Mixed121Masks.model_low_lt)
    Mixed121Masks.model_high_lt
    (by rw [Mixed121Aligned.port_two]; exact Mixed121Masks.model_low_even)
    Mixed121Masks.model_high_mod_eight
    (by rw [Mixed121Aligned.port_two]; exact Mixed121Masks.model_population_sum)
    (Mixed121Ports.high_mul_pos (v 0) (hv 0))
  exact ⟨N,w,hN,hq,hJ,hle,hw,hv5,hpos,hbound,hcongr,h0,hlim,hs.1,hs.2⟩

/-- Compact44's `ModelBandCut.graph_congruence_to_bands` at width `121`. -/
theorem graph_congruence_to_bands (K n q P C w F : V)
    (hn : 0<n) (hP : 0<P) (hqdef : q=1+P) (hqexp : q=Exp.exp (121*n))
    (hK : K=kernelBand 4393+kernelBand 5495+bareKernel)
    (hg : ((K+w)*C)%P=F) :
    ((rotatedBand 4393 n C+rotatedBand 5495 n C+bareRotated n C)+w*C)
      %(Exp.exp (121*n)-1)=F := by
  have hm : Exp.exp (121*n)-1=P := by
    rw [← hqexp, hqdef, add_comm, add_tsub_cancel_right]
  apply combined_congr K n C w F hn
  · rw [hm]; exact hP
  · exact hK
  · rw [hm]; exact hg

theorem symbolic_bands (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Mixed121Ports.ports v) :
    let p := Mixed121Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    ∃ N w : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ v 0=rep (121*8801) N ∧
      (121*8801)*N≤R ∧ w=Exp.exp (R-(121*8801)*N) ∧ v 5=q*w ∧
      0<v 0*(p 0:V) ∧ v 1<v 0*(p 0:V) ∧
      ((rotatedBand 4393 (8801*N) C + rotatedBand 5495 (8801*N) C +
        bareRotated (8801*N) C)+w*C) % (Exp.exp (121*(8801*N))-1)=v 1 ∧
      dig 121 C 0=1 ∧ ∀ k<8801*N, dig 121 C k≤3 := by
  obtain ⟨N,w,hN,hq,hJ,hle,hw,hv5,hpos,hbound,hgraph,h0,hlim⟩ :=
    Mixed121Aligned.symbolic_aligned v hv hz
  have hn : 0<(8801:V)*N := mul_pos (by norm_num) hN
  have hqexp : 1+v 0*(Mixed121Ports.ports 0:V)=Exp.exp (121*((8801:V)*N)) := by
    rw [← mul_assoc]; exact hq
  rw [port_one] at hgraph
  have hbands := graph_congruence_to_bands
    ((Mixed121Kernel.paramKernel Mixed121Kernel.rho : ℕ) : V) ((8801:V)*N)
    (1+v 0*(Mixed121Ports.ports 0:V)) (v 0*(Mixed121Ports.ports 0:V))
    (1+v 0*(Mixed121Ports.ports 0:V)-v 1-v 2) w (v 1)
    hn hpos rfl hqexp kernel_bands hgraph
  exact ⟨N,w,hN,hq,hJ,hle,hw,hv5,hpos,hbound,hbands,h0,hlim⟩
end Mixed121Bands
#print axioms Mixed121Bands.saturated_aligned
#print axioms Mixed121Bands.graph_congruence_to_bands
#print axioms Mixed121Bands.symbolic_bands
