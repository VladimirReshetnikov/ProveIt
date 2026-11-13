import DiophantineConsistency.Mixed121.Mixed121Bands

/-! # The temporal word and the position no-carry at the 121x8801 ports

This module ports, at width `121`, Compact44's `CompactBitRotation`,
`ActualTemporalBand`, `BandCarryInputs.source_word_bound` and
`CompactPositionIncrement`. They use their width only as a literal, so the
accepted proof bodies are kept and only `67/66` become `121/120`.

On top of them come two links of the `LeafFacts` halting chain:

* `position_noCarry` is the counterpart of
  `CompactPositionCarry.generic_position_noCarry_facts`. Every native cell
  `k > 0` of `C` has no carry against the low-mask digit at `k mod 8801`.
* `graph_temporal` is the counterpart of
  `FixedGraphTemporal.fixed_graph_temporal_facts`. In the band congruence,
  the term `w·C = 2^(R−dN)·C` becomes the bit rotation `temporalWord` of `C`,
  which is bounded and has digits below `2^121`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Mixed121Temporal
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord
open Mixed121Rotation
attribute [local irreducible] Mixed121Ports.betaNat Mixed121Ports.lowNat Mixed121Ports.highNat
  Mixed121Kernel.paramKernel Mixed121Kernel.rho
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The unrestricted exponent gives a bit rotation, without radix alignment. -/
noncomputable def temporalWord (n e C : V) : V := rot 1 (121*n) C (e % (121*n))

theorem temporal_mod (n e C : V) (hn : 0<n)
    (hM : 0<Exp.exp (121*n)-1) :
    (Exp.exp e*C) % (Exp.exp (121*n)-1) =
      temporalWord n e C % (Exp.exp (121*n)-1) := by
  have hlen : 0<121*n := mul_pos (by norm_num) hn
  have h := exp_mul_mod_rot (1:V) (121*n) e C hlen (by simpa only [one_mul] using hM)
  simpa only [temporalWord,one_mul] using h

theorem temporal_word_lt (n e C : V) (hn : 0<n)
    (hC : C<Exp.exp (121*n)) : temporalWord n e C<Exp.exp (121*n) := by
  have hlen : 0<121*n := mul_pos (by norm_num) hn
  have h := rot_lt (1:V) (121*n) C (e%(121*n)) (le_of_lt (mod_lt e hlen))
    (by simpa only [one_mul] using hC)
  simpa only [temporalWord,one_mul] using h

theorem temporal_digit_lt (n e C k : V) :
    dig 121 (temporalWord n e C) k < Exp.exp 121 := dig_lt 121 _ k

theorem temporal_digit_le (n e C k : V) :
    dig 121 (temporalWord n e C) k ≤ Exp.exp 121-1 := by
  apply le_tsub_of_add_le_left
  simpa only [add_comm] using lt_iff_succ_le.mp (temporal_digit_lt n e C k)

/-- Replace only the exponential term; all other contributions remain explicit. -/
theorem replace_temporal (n e C A F : V) (hn : 0<n)
    (hM : 0<Exp.exp (121*n)-1)
    (h : (A+Exp.exp e*C)%(Exp.exp (121*n)-1)=F) :
    (A+temporalWord n e C)%(Exp.exp (121*n)-1)=F := by
  have ht := temporal_mod n e C hn hM
  have heq : (A+Exp.exp e*C)%(Exp.exp (121*n)-1) =
      (A+temporalWord n e C)%(Exp.exp (121*n)-1) := by
    rw [mod_add hM,ht,←mod_add hM]
  exact heq.symm.trans h

theorem source_word_bound (q n u v : V) (hq : q=Exp.exp (121*n)) (hu : 0<u) :
    q-u-v < Exp.exp (121*n) := by
  rw [← hq]
  have hqpos : 0<q := by rw [hq]; exact exp_pos _
  exact lt_of_le_of_lt tsub_le_self (tsub_lt_self hqpos hu)


theorem graph_temporal_word (n q u v C R w A F : V)
    (hn : 0<n) (hM : 0<Exp.exp (121*n)-1)
    (hq : q=Exp.exp (121*n)) (hu : 0<u) (hC : C=q-u-v)
    (hw : w=Exp.exp (R-121*n))
    (hgraph : (A+w*C)%(Exp.exp (121*n)-1)=F) :
    (A+temporalWord n (R-121*n) C)%(Exp.exp (121*n)-1)=F ∧
      temporalWord n (R-121*n) C<Exp.exp (121*n) ∧
      ∀ k : V, dig 121 (temporalWord n (R-121*n) C) k ≤ Exp.exp 121-1 := by
  have hbound : C<Exp.exp (121*n) := by
    rw [hC]
    exact source_word_bound q n u v hq hu
  refine ⟨?_, temporal_word_lt n (R-121*n) C hn hbound, ?_⟩
  · apply replace_temporal n (R-121*n) C A F hn hM
    rw [← hw]
    exact hgraph
  · intro k
    exact temporal_digit_le n (R-121*n) C k

theorem increment_digits (m N C MC : V) (hm : 0 < m) (hN : 0 < N)
    (hMC : MC < Exp.exp (121*m))
    (hMC0 : dig 121 MC 0 = Exp.exp 121-2) (hC : 1 ≤ C)
    (hnc : NoCarry (C-1) (MC * rep (121*m) N + 1)) :
    dig 121 C 0 = 1 ∧ ∀ k < m*N, 0 < k → NoCarry (dig 121 C k) (dig 121 MC (k % m)) := by
  have h2 : (2:V) ≤ Exp.exp 121 := by
    simpa using exp_monotone_le.mpr (show (1:V) ≤ 121 by norm_num)
  set e := Exp.exp (121:V)-2
  have he : Exp.exp (121:V) = e+2 := (tsub_add_cancel_of_le h2).symm
  have hρ1 : Exp.exp (121:V)-1=e+1 := by
    rw [he, show e+2=(e+1)+1 by ring, add_tsub_cancel_right]
  have hmN : 0 < m*N := mul_pos hm hN
  have hJ : ∀ k < m*N, dig 121 (MC * rep (121*m) N) k = dig 121 MC (k % m) :=
    dig_mul_rep 121 m MC hMC N
  have h0 : dig 121 (MC * rep (121*m) N) 0 = e := by
    rw [hJ 0 hmN, zero_mod, hMC0]
  obtain ⟨hinc0, hinck⟩ := dig_add_one 121 (MC * rep (121*m) N)
    (by rw [h0, he]; exact (add_lt_add_iff_left e).mpr one_lt_two)
  have hz : dig 121 (C-1) 0 = 0 := by
    apply noCarry_ones 121 _ (dig_lt 121 _ 0)
    simpa only [hinc0, h0, ←hρ1] using noCarry_dig 121 _ _ 0 hnc
  have hC1 : C-1+1=C := tsub_add_cancel_of_le hC
  obtain ⟨hc0, hck⟩ := dig_add_one 121 (C-1)
    (by rw [hz, zero_add, he]; exact lt_of_lt_of_le one_lt_two (le_add_of_nonneg_left (by simp)))
  rw [hC1] at hc0 hck
  refine ⟨by rw [hc0,hz,zero_add], ?_⟩
  intro k hk hk0
  simpa only [hinck k hk0, hJ k hk, ←hck k hk0] using noCarry_dig 121 _ _ k hnc


/-! ## The 121x8801 links -/

theorem position_noCarry (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Mixed121Ports.ports v) :
    let p := Mixed121Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let C : V := q-v 1-v 2
    ∃ N w : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ v 0=rep (121*8801) N ∧
      v 5=q*w ∧ (((p 1:V)+w)*C)%(v 0*(p 0:V))=v 1 ∧ dig 121 C 0=1 ∧
      (∀ k<8801*N, 0<k →
        NoCarry (dig 121 C k) (dig 121 ((Mixed121Ports.lowNat:ℕ):V) (k%8801))) ∧
      NoCarry (v 1) ((Mixed121Ports.highNat:V)*v 0-1) := by
  obtain ⟨N,w,hN,hq,hJ,_,_,hv5,_,_,hcongr,h0,_,hlow,hhigh⟩ :=
    Mixed121Bands.saturated_aligned v hv hz
  have hC : 1 ≤ 1+v 0*(Mixed121Ports.ports 0:V)-v 1-v 2 := by
    have h := mod_le (1+v 0*(Mixed121Ports.ports 0:V)-v 1-v 2) (Exp.exp (121:V))
    rw [←dig_zero_index 121 _, h0] at h
    exact h
  have hn : NoCarry ((1+v 0*(Mixed121Ports.ports 0:V)-v 1-v 2)-1)
      (((Mixed121Ports.lowNat:ℕ):V)*rep (121*8801) N+1) := by
    have e2 : (Mixed121Ports.ports 2:V)*v 0+1 =
        ((Mixed121Ports.lowNat : ℕ) : V) * rep (121*8801) N + 1 := by
      rw [Mixed121Aligned.port_two, hJ]
    rw [e2] at hlow
    exact hlow
  have hextract := increment_digits 8801 N _ ((Mixed121Ports.lowNat:ℕ):V) (by norm_num) hN
    Mixed121Masks.model_low_lt Mixed121Increment.low_origin hC hn
  exact ⟨N,w,hN,hq,hJ,hv5,hcongr,h0,hextract.2,hhigh⟩

theorem graph_temporal (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Mixed121Ports.ports v) :
    let p := Mixed121Ports.ports
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
    Mixed121Bands.symbolic_bands v hv hz
  dsimp only at *
  let p := Mixed121Ports.ports
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
end Mixed121Temporal
#print axioms Mixed121Temporal.temporal_mod
#print axioms Mixed121Temporal.replace_temporal
#print axioms Mixed121Temporal.graph_temporal_word
#print axioms Mixed121Temporal.increment_digits
#print axioms Mixed121Temporal.position_noCarry
#print axioms Mixed121Temporal.graph_temporal
