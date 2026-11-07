import DiophantineConsistency.Source34.Source34Bands
import DiophantineConsistency.Mixed121.Mixed121Temporal

/-! # The temporal word and the position no-carry at the source34 ports

`Mixed121Temporal` at the source34 tuple. The width-121 bit rotation
(`Mixed121Temporal.temporalWord`, `temporal_mod`, `temporal_word_lt`,
`temporal_digit_lt`, `temporal_digit_le`, `replace_temporal`,
`source_word_bound`, `graph_temporal_word`) and the increment extraction
`Mixed121Temporal.increment_digits` are generic and used directly. The two
tuple-level links are re-declared at the source34 ports:

* `position_noCarry`: every native cell `k > 0` of `C` has no carry against
  the source34 low-mask digit at `k mod 8801`;
* `graph_temporal`: in the source34 band congruence, `w·C` becomes the bit
  rotation `Mixed121Temporal.temporalWord` of `C`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Source34Temporal
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord
open Source34Rotation
open Mixed121Temporal (temporalWord graph_temporal_word increment_digits)
attribute [local irreducible] Source34Ports.betaNat Source34Ports.lowNat Source34Ports.highNat
  Source34Kernel.paramKernel Mixed121Kernel.rho
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem position_noCarry (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Source34Ports.ports v) :
    let p := Source34Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let C : V := q-v 1-v 2
    ∃ N w : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ v 0=rep (121*8801) N ∧
      v 5=q*w ∧ (((p 1:V)+w)*C)%(v 0*(p 0:V))=v 1 ∧ dig 121 C 0=1 ∧
      (∀ k<8801*N, 0<k →
        NoCarry (dig 121 C k) (dig 121 ((Source34Ports.lowNat:ℕ):V) (k%8801))) ∧
      NoCarry (v 1) ((Source34Ports.highNat:V)*v 0-1) := by
  obtain ⟨N,w,hN,hq,hJ,_,_,hv5,_,_,hcongr,h0,_,hlow,hhigh⟩ :=
    Source34Bands.saturated_aligned v hv hz
  have hC : 1 ≤ 1+v 0*(Source34Ports.ports 0:V)-v 1-v 2 := by
    have h := mod_le (1+v 0*(Source34Ports.ports 0:V)-v 1-v 2) (Exp.exp (121:V))
    rw [←dig_zero_index 121 _, h0] at h
    exact h
  have hn : NoCarry ((1+v 0*(Source34Ports.ports 0:V)-v 1-v 2)-1)
      (((Source34Ports.lowNat:ℕ):V)*rep (121*8801) N+1) := by
    have e2 : (Source34Ports.ports 2:V)*v 0+1 =
        ((Source34Ports.lowNat : ℕ) : V) * rep (121*8801) N + 1 := by
      rw [Source34Aligned.port_two, hJ]
    rw [e2] at hlow
    exact hlow
  have hextract := increment_digits 8801 N _ ((Source34Ports.lowNat:ℕ):V) (by norm_num) hN
    Source34Masks.model_low_lt Source34Increment.low_origin hC hn
  exact ⟨N,w,hN,hq,hJ,hv5,hcongr,h0,hextract.2,hhigh⟩

theorem graph_temporal (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Source34Ports.ports v) :
    let p := Source34Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    ∃ N w : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ v 0=rep (121*8801) N ∧
      (121*8801)*N≤R ∧ w=Exp.exp (R-(121*8801)*N) ∧ v 5=q*w ∧
      0<v 0*(p 0:V) ∧ v 1<v 0*(p 0:V) ∧
      ((rotatedBand 4393 (8801*N) C + rotatedBand 5495 (8801*N) C +
        bareRotated (8801*N) C)+temporalWord (8801*N) (R-121*(8801*N)) C)
          % (Exp.exp (121*(8801*N))-1)=v 1 ∧
      temporalWord (8801*N) (R-121*(8801*N)) C < Exp.exp (121*(8801*N)) ∧
      (∀ k : V, dig 121 (temporalWord (8801*N) (R-121*(8801*N)) C) k ≤ Exp.exp 121-1) ∧
      dig 121 C 0=1 ∧ ∀ k<8801*N, dig 121 C k≤3 := by
  obtain ⟨N,w,hN,hq,hJ,hle,hw,hv5,hpos,hbound,hband,h0,hlim⟩ :=
    Source34Bands.symbolic_bands v hv hz
  dsimp only at *
  let p := Source34Ports.ports
  let q : V := 1+v 0*(p 0:V)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  let C : V := q-v 1-v 2
  let n : V := 8801*N
  let A : V := rotatedBand 4393 n C + rotatedBand 5495 n C + bareRotated n C
  have hn : 0<n := mul_pos (by norm_num) hN
  have hqexp : q=Exp.exp (121*n) := by dsimp [n]; rw [←mul_assoc]; exact hq
  have hmod : Exp.exp (121*n)-1=v 0*(p 0:V) := by
    rw [← hqexp]; dsimp [q]; rw [add_comm,add_tsub_cancel_right]
  have hM : 0<Exp.exp (121*n)-1 := by rw [hmod]; exact hpos
  have hwexp : w=Exp.exp (R-121*n) := by dsimp [n]; rw [←mul_assoc]; exact hw
  have ht := graph_temporal_word n q (v 1) (v 2) C R w A (v 1)
    hn hM hqexp (hv 1) rfl hwexp hband
  exact ⟨N,w,hN,hq,hJ,hle,hw,hv5,hpos,hbound,ht.1,ht.2.1,ht.2.2,h0,hlim⟩
end Source34Temporal
#print axioms Source34Temporal.position_noCarry
#print axioms Source34Temporal.graph_temporal
