import DiophantineConsistency.Source34.Source34Aligned
import DiophantineConsistency.Source34.Source34Rotation
import DiophantineConsistency.Mixed121.Mixed121Bands

/-! # The saturated, band-cut graph data at the source34 ports

`Mixed121Bands` at the source34 tuple. `Mixed121Bands.ports_one` is generic
and used directly. The rest is re-declared:

* `port_one` identifies the second port with `Source34Kernel.paramKernel rho`;
* `saturated_aligned` adds the two saturation no-carry facts to
  `Source34Aligned.symbolic_aligned`;
* `graph_congruence_to_bands` and `symbolic_bands` cut the first-pair
  congruence into the two rotated source34 clause bands and the source34 bare
  part (`Source34Rotation.kernel_bands`, bare offsets `40, 41, 1100, 2200,
  8802`). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Source34Bands
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits Source34Rotation
attribute [local irreducible] Source34Ports.betaNat Source34Ports.lowNat Source34Ports.highNat
  Source34Kernel.paramKernel Mixed121Kernel.rho
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem port_one :
    ((Source34Ports.ports 1 : ℕ) : V) =
      ((Source34Kernel.paramKernel Mixed121Kernel.rho : ℕ) : V) := by
  unfold Source34Ports.ports
  rw [Mixed121Bands.ports_one]

theorem saturated_aligned (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Source34Ports.ports v) :
    let p := Source34Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    ∃ N w : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ v 0=rep (121*8801) N ∧
      (121*8801)*N≤R ∧ w=Exp.exp (R-(121*8801)*N) ∧ v 5=q*w ∧
      0<v 0*(p 0:V) ∧ v 1<v 0*(p 0:V) ∧
      (((p 1:V)+w)*C)%(v 0*(p 0:V))=v 1 ∧
      dig 121 C 0=1 ∧ (∀ k<8801*N, dig 121 C k≤3) ∧
      NoCarry (C-1) ((p 2:V)*v 0+1) ∧
      NoCarry (v 1) ((Source34Ports.highNat:V)*v 0-1) := by
  let p := Source34Ports.ports
  let d : V := 121*8801
  obtain ⟨N,w,hN,hq,hJ,hle,hw,hv5,hpos,hbound,hcongr,h0,hlim⟩ :=
    Source34Aligned.symbolic_aligned v hv hz
  obtain ⟨hb, hl, hh, hbeta⟩ := Source34Ports.leaf_bounds (V:=V)
  have hs := FreeJSaturationClient.graph_saturation_facts p v d N
    (Source34Ports.highNat : V) hb hl hh hv hz hbeta (by dsimp [d]; norm_num) hN hq hJ
    Source34Aligned.port_three
    (by rw [Source34Aligned.port_two]; exact Source34Masks.model_low_lt)
    Source34Masks.model_high_lt
    (by rw [Source34Aligned.port_two]; exact Source34Masks.model_low_even)
    Source34Masks.model_high_mod_eight
    (by rw [Source34Aligned.port_two]; exact Source34Masks.model_population_sum)
    (Source34Ports.high_mul_pos (v 0) (hv 0))
  exact ⟨N,w,hN,hq,hJ,hle,hw,hv5,hpos,hbound,hcongr,h0,hlim,hs.1,hs.2⟩

/-- Compact44's `ModelBandCut.graph_congruence_to_bands` at width `121`, for
the source34 bands. -/
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
    (hz : CompactLeafFacts.LeafFacts Source34Ports.ports v) :
    let p := Source34Ports.ports
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
    Source34Aligned.symbolic_aligned v hv hz
  have hn : 0<(8801:V)*N := mul_pos (by norm_num) hN
  have hqexp : 1+v 0*(Source34Ports.ports 0:V)=Exp.exp (121*((8801:V)*N)) := by
    rw [← mul_assoc]; exact hq
  rw [port_one] at hgraph
  have hbands := graph_congruence_to_bands
    ((Source34Kernel.paramKernel Mixed121Kernel.rho : ℕ) : V) ((8801:V)*N)
    (1+v 0*(Source34Ports.ports 0:V)) (v 0*(Source34Ports.ports 0:V))
    (1+v 0*(Source34Ports.ports 0:V)-v 1-v 2) w (v 1)
    hn hpos rfl hqexp kernel_bands hgraph
  exact ⟨N,w,hN,hq,hJ,hle,hw,hv5,hpos,hbound,hbands,h0,hlim⟩
end Source34Bands
#print axioms Source34Bands.port_one
#print axioms Source34Bands.saturated_aligned
#print axioms Source34Bands.graph_congruence_to_bands
#print axioms Source34Bands.symbolic_bands
