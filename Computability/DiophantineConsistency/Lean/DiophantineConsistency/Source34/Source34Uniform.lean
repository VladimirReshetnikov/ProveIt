import DiophantineConsistency.Source34.Source34Shift
import DiophantineConsistency.Mixed121.Mixed121Uniform

/-! # Uniform decoding at every clause cell, at the source34 ports

`Mixed121Uniform` at the source34 tuple. The whole-period phase lemmas
(`Mixed121Uniform.decoder_safe`, `predecessor_safe`, `shift_phase`,
`zero_source`, `target_and_predecessor`, `source_phase`) depend only on the
hull and the temporal word, and are used directly. Re-declared at the source34
ports, because they read the source34 bands, bare offsets, copy positions or
`MF_native`: `foreign_at4393`, `foreign_at5495` (via
`Source34Single.foreign` / `bare`), `clean_column_at4393`,
`clean_column_at5495`, `inputs` (over `Source34Band.copyDigit`),
`local_nocarry`, `DecodedAt`, `decode_at` and the chain link
`graph_uniform_decoder`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Source34Uniform
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticWindowBits
open ArithmeticCyclicWord CompactHeterogeneousCarry CompactGenericAlignedMass
open Source34Rotation Source34Flatten ModelDigitTransfer
open Mixed121Rotation (selectorOffset coefficient word cap)
open Mixed121Flatten (selectors copies aligned_room)
open Mixed121Clean (Bad)
open Mixed121Uniform (shift_phase target_and_predecessor source_phase)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## A clause column at any cell of the right phase -/

theorem foreign_at4393 (N C k : V) (hN : 0<N) (hk : k<8801*N)
    (hC : C<Exp.exp (121*(8801*N)))
    (hzero : ∀ j<8801*N, ¬Bad (j%8801) → dig 121 C j=0)
    (hp : k%8801=4393) :
    columnBand 5495 (8801*N) C k=0 ∧ bareColumn (8801*N) C k=0 := by
  have hn : 0<(8801:V)*N := mul_pos (by norm_num) hN
  have hs (j : Fin 943) : dig 121 (rot 121 (8801*N) C (selectorOffset 5495 j%(8801*N))) k=0 := by
    rw [dig_rot 121 (8801*N) C _ k (mod_lt _ hn) hk hC,cyc_mod _ _ _ hn]
    apply Mixed121Parity.source_zero N C k (selectorOffset 5495 j) hN hzero
    rw [hp]
    exact (Source34Single.foreign j.val (Or.inl j.isLt)).1
  have hc (j : Fin 44) : dig 121 (rot 121 (8801*N) C (copyOffset 5495 j%(8801*N))) k=0 := by
    rw [dig_rot 121 (8801*N) C _ k (mod_lt _ hn) hk hC,cyc_mod _ _ _ hn]
    apply Mixed121Parity.source_zero N C k (copyOffset 5495 j) hN hzero
    rw [hp]
    exact (Source34Single.foreign (Source34Kernel.extraPos j) (Source34Single.copy_allowed j)).1
  have hb (j : Fin 5) : dig 121 (rot 121 (8801*N) C (bareOffset j%(8801*N))) k=0 := by
    rw [dig_rot 121 (8801*N) C _ k (mod_lt _ hn) hk hC,cyc_mod _ _ _ hn]
    apply Mixed121Parity.source_zero N C k (bareOffset j) hN hzero
    rw [hp]
    exact (Source34Single.bare j).1
  constructor
  · simp only [columnBand,hs,hc,mul_zero,Finset.sum_const_zero,add_zero]
  · simp only [bareColumn,hb,Finset.sum_const_zero]

theorem foreign_at5495 (N C k : V) (hN : 0<N) (hk : k<8801*N)
    (hC : C<Exp.exp (121*(8801*N)))
    (hzero : ∀ j<8801*N, ¬Bad (j%8801) → dig 121 C j=0)
    (hp : k%8801=5495) :
    columnBand 4393 (8801*N) C k=0 ∧ bareColumn (8801*N) C k=0 := by
  have hn : 0<(8801:V)*N := mul_pos (by norm_num) hN
  have hs (j : Fin 943) : dig 121 (rot 121 (8801*N) C (selectorOffset 4393 j%(8801*N))) k=0 := by
    rw [dig_rot 121 (8801*N) C _ k (mod_lt _ hn) hk hC,cyc_mod _ _ _ hn]
    apply Mixed121Parity.source_zero N C k (selectorOffset 4393 j) hN hzero
    rw [hp]
    exact (Source34Single.foreign j.val (Or.inl j.isLt)).2
  have hc (j : Fin 44) : dig 121 (rot 121 (8801*N) C (copyOffset 4393 j%(8801*N))) k=0 := by
    rw [dig_rot 121 (8801*N) C _ k (mod_lt _ hn) hk hC,cyc_mod _ _ _ hn]
    apply Mixed121Parity.source_zero N C k (copyOffset 4393 j) hN hzero
    rw [hp]
    exact (Source34Single.foreign (Source34Kernel.extraPos j) (Source34Single.copy_allowed j)).2
  have hb (j : Fin 5) : dig 121 (rot 121 (8801*N) C (bareOffset j%(8801*N))) k=0 := by
    rw [dig_rot 121 (8801*N) C _ k (mod_lt _ hn) hk hC,cyc_mod _ _ _ hn]
    apply Mixed121Parity.source_zero N C k (bareOffset j) hN hzero
    rw [hp]
    exact (Source34Single.bare j).2
  constructor
  · simp only [columnBand,hs,hc,mul_zero,Finset.sum_const_zero,add_zero]
  · simp only [bareColumn,hb,Finset.sum_const_zero]

attribute [local irreducible] Compact943Data.rows Mixed121Flatten.selectors Mixed121Flatten.copies

theorem clean_column_at4393 (N C T F k : V) (hN : 0<N) (hk : k<8801*N)
    (hC : C<Exp.exp (121*(8801*N)))
    (hzero : ∀ j<8801*N, ¬Bad (j%8801) → dig 121 C j=0)
    (hp : k%8801=4393)
    (h : CarryInput 121 (8801*N) F 1 (cap (ι:=Aligned (Fin 943) (Fin 44)) 121)
      (coefficient (fun j => (alignedCoeff selectors copies j:V)))
      (word 121 (8801*N) C bandOffsets T))
    (hT : dig 121 T k=0) (hpred : dig 121 T (cyc (8801*N) k 1)=0) :
    dig 121 F k=Source34Single.decoderBand 4393 (8801*N) C k := by
  have hn : 0<(8801:V)*N := mul_pos (by norm_num) hN
  have hexact := (W121.TemporalCarryExact.clean_exact (8801*N) C T F
    (fun j : Aligned (Fin 943) (Fin 44) => (alignedCoeff selectors copies j:V))
    bandOffsets h k hk aligned_room hT (by rw [hpred]; simp)).2
  have hflat := column_flatten (8801*N) C T k
  obtain ⟨hforeign,hbare⟩ := foreign_at4393 N C k hN hk hC hzero hp
  rw [hforeign,hbare,hT] at hflat
  simp only [add_zero] at hflat
  have hband := band_column 4393 (8801*N) C k hn hk hC
  change columnBand 4393 (8801*N) C k = Source34Single.decoderBand 4393 (8801*N) C k at hband
  exact hexact.trans (hflat.trans hband)

theorem clean_column_at5495 (N C T F k : V) (hN : 0<N) (hk : k<8801*N)
    (hC : C<Exp.exp (121*(8801*N)))
    (hzero : ∀ j<8801*N, ¬Bad (j%8801) → dig 121 C j=0)
    (hp : k%8801=5495)
    (h : CarryInput 121 (8801*N) F 1 (cap (ι:=Aligned (Fin 943) (Fin 44)) 121)
      (coefficient (fun j => (alignedCoeff selectors copies j:V)))
      (word 121 (8801*N) C bandOffsets T))
    (hT : dig 121 T k=0) (hpred : dig 121 T (cyc (8801*N) k 1)=0) :
    dig 121 F k=Source34Single.decoderBand 5495 (8801*N) C k := by
  have hn : 0<(8801:V)*N := mul_pos (by norm_num) hN
  have hexact := (W121.TemporalCarryExact.clean_exact (8801*N) C T F
    (fun j : Aligned (Fin 943) (Fin 44) => (alignedCoeff selectors copies j:V))
    bandOffsets h k hk aligned_room hT (by rw [hpred]; simp)).2
  have hflat := column_flatten (8801*N) C T k
  obtain ⟨hforeign,hbare⟩ := foreign_at5495 N C k hN hk hC hzero hp
  rw [hforeign,hbare,hT] at hflat
  simp only [zero_add,add_zero] at hflat
  have hband := band_column 5495 (8801*N) C k hn hk hC
  change columnBand 5495 (8801*N) C k = Source34Single.decoderBand 5495 (8801*N) C k at hband
  exact hexact.trans (hflat.trans hband)

/-! ## Inputs and decoding at any cell -/

theorem inputs (N C k : V) (T : ℕ) (hN : 0<N) (hT : 3296≤T) (hTmax : T<8801)
    (hp : k%8801=(T:V))
    (hbool : ∀ j<8801*N, j%8801≠1063 → dig 121 C j≤1) :
    (∀ i : Fin 943, Mixed121Band.selDigit (8801*N) C k T i≤1) ∧
    (∀ j < 44, Source34Band.copyDigit (8801*N) C k T j≤1) := by
  have hn : 0<(8801:V)*N := mul_pos (by norm_num) hN
  constructor
  · intro i
    have hiT : i.val≤T := le_trans (by have := i.isLt; omega) hT
    unfold Mixed121Band.selDigit
    apply hbool _ (cyc_lt hn _ _)
    rw [source_phase N k T i.val hN hTmax hiT hp]
    intro he
    have he' : i.val=1063 := by exact_mod_cast he
    have := i.isLt
    omega
  · intro j hj
    have hmem : Source34Band.extraPosN j ∈ Source34Kernel.extraPositions := by
      unfold Source34Band.extraPosN
      rw [dif_pos hj]
      exact List.get_mem _ _
    have hall := Source34Single.extra_allowed _ hmem
    have hne := Source34Selected.extra_ne_dummy _ hmem
    have hjT : Source34Band.extraPosN j≤T := by
      unfold Source34Single.Allowed at hall
      omega
    unfold Source34Band.copyDigit
    apply hbool _ (cyc_lt hn _ _)
    rw [source_phase N k T _ hN hTmax hjT hp]
    intro he
    exact hne (by exact_mod_cast he)

theorem local_nocarry (N F k : V) (hN : 0<N) (hk : k<8801*N) (hk0 : 0<k)
    (hphase : k%8801=4393 ∨ k%8801=5495)
    (hhigh : NoCarry F (((Source34Ports.highNat:ℕ):V)*rep (121*8801) N-1)) :
    NoCarry (dig 121 F k) ((Exp.exp 10 - 2) + Exp.exp 10 * dsum (Exp.exp 2) (fun _ => 1) 44) := by
  have hd0 : 1≤dig 121 ((Source34Ports.highNat:ℕ):V) 0 := by
    rw [Source34Selected.model_origin]; norm_num
  have hh := high_mask_digits 121 8801 N F ((Source34Ports.highNat:ℕ):V) (by norm_num) hN
    Source34Masks.model_high_lt hd0 hhigh
  have h := hh.2 k hk hk0
  have e1 := Source34Selected.model_target (V:=V) 4393 Source34Selected.high_target4393
  have e2 := Source34Selected.model_target (V:=V) 5495 Source34Selected.high_target5495
  simp only [Nat.cast_ofNat] at e1 e2
  rcases hphase with hp | hp
  · rw [hp,e1] at h
    exact h
  · rw [hp,e2] at h
    exact h

/-- The decoded selection of the band reflected at `T`, read at cell `k`. -/
def DecodedAt (n C k : V) (T : ℕ) : Prop :=
  ((∀ i, Mixed121Band.selDigit n C k T i = 0) ∧
      ∀ j < 44, Source34Band.copyDigit n C k T j = 0) ∨
    ∃ i, CompactSelectorSum.Selected (Mixed121Band.selDigit n C k T) i ∧
      ∀ j < 44, Source34Band.copyDigit n C k T j =
        (Mixed121Digits.digit (Compact943Data.row i) j : V)

theorem decode_at (N C F k : V) (T : ℕ) (hN : 0<N) (hT : 3296≤T) (hTmax : T<8801)
    (hp : k%8801=(T:V))
    (hbool : ∀ j<8801*N, j%8801≠1063 → dig 121 C j≤1)
    (hcol : dig 121 F k = Source34Single.decoderBand T (8801*N) C k)
    (hnc : NoCarry (dig 121 F k)
      ((Exp.exp 10 - 2) + Exp.exp 10 * dsum (Exp.exp 2) (fun _ => 1) 44)) :
    DecodedAt (8801*N) C k T := by
  obtain ⟨hs, hcp⟩ := inputs N C k T hN hT hTmax hp hbool
  rw [hcol] at hnc
  exact Mixed121Decoder.decode _ (fun i d => (Mixed121Digits.digit (Compact943Data.row i) d : V))
    _ 44 (Compact943Decoder.count_bound _ hs)
    (fun i d _ => by exact_mod_cast Mixed121Digits.digit_le_one _ d) hcp hnc

attribute [local irreducible] Source34Ports.betaNat Source34Ports.lowNat Source34Ports.highNat
  Source34Kernel.paramKernel Mixed121Kernel.rho

theorem graph_uniform_decoder (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Source34Ports.ports v) :
    let p := Source34Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    ∃ N s : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ v 0=rep (121*8801) N ∧
      let E := R-121*(8801*N)
      E%121=0 ∧ s<N ∧ (E/121)%(8801*N)=8801*s ∧
      (∀ k<8801*N, k%8801=4393 → DecodedAt (8801*N) C k 4393) ∧
      (∀ k<8801*N, k%8801=5495 → DecodedAt (8801*N) C k 5495) := by
  obtain ⟨N,w,s,hN,hq,hJ,hle,hw,hv5,hcarry,haligned,hs,hshift⟩ :=
    Source34Shift.graph_cell_shift v hv hz
  obtain ⟨N',w',hN',hq',hJ',hle',hw',hv5',hcarry',h0',hzero,hbool⟩ :=
    Source34Clean.graph_support_carry v hv hz
  obtain ⟨N'',w'',hN'',hq'',hJ'',hv5'',hcongr'',h0'',hslots,hhigh⟩ :=
    Source34Temporal.position_noCarry v hv hz
  dsimp only at *
  have hNN : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((121*8801):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  have hNN' : N''=N := by
    apply mul_left_cancel₀ (by norm_num : ((121*8801):V)≠0)
    exact exp_inj (hq''.symm.trans hq)
  subst N' N''
  let p := Source34Ports.ports
  let q : V := 1+v 0*(p 0:V)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  let C : V := q-v 1-v 2
  let n : V := 8801*N
  let E : V := R-121*n
  let T : V := Mixed121Temporal.temporalWord n E C
  have hqexp : q=Exp.exp (121*n) := by dsimp [n]; rw [←mul_assoc]; exact hq
  have hC : C<Exp.exp (121*n) := by
    dsimp [C]
    exact Mixed121Temporal.source_word_bound q n (v 1) (v 2) hqexp (hv 1)
  have hcell : ((E/121)%n)%8801=0 := by rw [hshift,mod_mul_self_right]
  have hhigh' : NoCarry (v 1) (((Source34Ports.highNat:ℕ):V)*rep (121*8801) N-1) := by
    rw [←hJ]; exact hhigh
  refine ⟨N,s,hN,hq,hJ,haligned,hs,hshift,?_,?_⟩
  · intro k hk hp
    have hk0 : 0<k := by
      by_contra hh
      have hz0 : k=0 := nonpos_iff_eq_zero.mp (not_lt.mp hh)
      subst k
      norm_num at hp
    obtain ⟨hpred,htarget⟩ := target_and_predecessor N C E k hN hk hC haligned hcell hzero
      (Or.inr (Or.inr (Or.inl hp)))
    have hT0 := htarget (Or.inl hp)
    have hcol := clean_column_at4393 N C T (v 1) k hN hk hC hzero hp hcarry hT0 hpred
    have hnc := local_nocarry N (v 1) k hN hk hk0 (Or.inl hp) hhigh'
    exact decode_at N C (v 1) k 4393 hN (by norm_num) (by norm_num) (by simpa using hp) hbool
      hcol hnc
  · intro k hk hp
    have hk0 : 0<k := by
      by_contra hh
      have hz0 : k=0 := nonpos_iff_eq_zero.mp (not_lt.mp hh)
      subst k
      norm_num at hp
    obtain ⟨hpred,htarget⟩ := target_and_predecessor N C E k hN hk hC haligned hcell hzero
      (Or.inr (Or.inr (Or.inr hp)))
    have hT0 := htarget (Or.inr hp)
    have hcol := clean_column_at5495 N C T (v 1) k hN hk hC hzero hp hcarry hT0 hpred
    have hnc := local_nocarry N (v 1) k hN hk hk0 (Or.inr hp) hhigh'
    exact decode_at N C (v 1) k 5495 hN (by norm_num) (by norm_num) (by simpa using hp) hbool
      hcol hnc
end Source34Uniform
#print axioms Source34Uniform.clean_column_at4393
#print axioms Source34Uniform.inputs
#print axioms Source34Uniform.decode_at
#print axioms Source34Uniform.graph_uniform_decoder
