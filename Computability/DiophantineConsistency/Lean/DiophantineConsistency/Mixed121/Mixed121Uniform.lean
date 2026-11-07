import DiophantineConsistency.Mixed121.Mixed121Shift

/-! # Uniform decoding at every clause cell, at the 121x8801 ports

These are the 121x8801 counterparts of Compact44's `WholeBlockPhase`,
`WholeBlockTemporal`, `UniformForeignZero`, `UniformCleanColumn`,
`UniformBandInputs` and the chain links `graph_uniform_reset_facts` and
`graph_uniform_decoder_facts`.

The temporal rotation is a whole number of periods (`Mixed121Shift`). So at
every cell `k ≡ 4393` or `5495 (mod 8801)`:

* the temporal digit and its predecessor vanish, and the incoming carry is
  zero (`graph_uniform_reset`);
* the other band's sources and the bare sources are outside `Bad`, so the
  graph digit `F_k` is that band's decoder input (`clean_column_*`);
* the band's inputs are Boolean, because a source's phase is its support
  position, and `F_k` has no carry against `μ`.

`graph_uniform_decoder` therefore gives the decoded selection of
`Mixed121Decoder.decode` at every clause cell of every period. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Mixed121Uniform
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticWindowBits
open ArithmeticCyclicWord CompactHeterogeneousCarry CompactGenericAlignedMass
open Mixed121Rotation Mixed121Flatten Mixed121Clean ModelDigitTransfer
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Whole-period phases -/

theorem decoder_safe (p : V) (hp : p=4393 ∨ p=5495) : ¬Bad p := by
  rcases hp with rfl | rfl <;> norm_num [Bad]

theorem predecessor_safe (p : V) (hp : p=2195 ∨ p=3296 ∨ p=4393 ∨ p=5495) :
    ¬Bad (cyc 8801 p 1) := by
  have h1 : cyc (8801:V) 2195 1=2194 := by
    rw [cyc_of_le (by norm_num) (by norm_num) (by norm_num)]
    exact (eq_tsub_of_add_eq (show (2194:V)+1=2195 by norm_num)).symm
  have h2 : cyc (8801:V) 3296 1=3295 := by
    rw [cyc_of_le (by norm_num) (by norm_num) (by norm_num)]
    exact (eq_tsub_of_add_eq (show (3295:V)+1=3296 by norm_num)).symm
  have h3 : cyc (8801:V) 4393 1=4392 := by
    rw [cyc_of_le (by norm_num) (by norm_num) (by norm_num)]
    exact (eq_tsub_of_add_eq (show (4392:V)+1=4393 by norm_num)).symm
  have h4 : cyc (8801:V) 5495 1=5494 := by
    rw [cyc_of_le (by norm_num) (by norm_num) (by norm_num)]
    exact (eq_tsub_of_add_eq (show (5494:V)+1=5495 by norm_num)).symm
  rcases hp with rfl | rfl | rfl | rfl <;> simp only [h1,h2,h3,h4] <;> norm_num [Bad]

theorem shift_phase (N k D : V) (hN : 0<N) (hD : D%8801=0) :
    (cyc (8801*N) k D)%8801=k%8801 := by
  rw [CyclicAnyPhase.cyc_period 8801 N k D (by norm_num) hN]
  unfold cyc
  rw [hD,tsub_zero,mod_add_remove_right (by norm_num : (0:V)<8801),
    mod_eq_self_of_lt (mod_lt k (by norm_num : (0:V)<8801))]

theorem zero_source (N C E k : V) (hN : 0<N) (hk : k<8801*N)
    (hC : C<Exp.exp (121*(8801*N))) (haligned : E%121=0)
    (hcell : ((E/121)%(8801*N))%8801=0)
    (hzero : ∀ j<8801*N, ¬Bad (j%8801) → dig 121 C j=0)
    (hsafe : ¬Bad (k%8801)) :
    dig 121 (Mixed121Temporal.temporalWord (8801*N) E C) k=0 := by
  have hn : 0<(8801:V)*N := mul_pos (by norm_num) hN
  rw [Mixed121Shift.aligned_digit C (8801*N) E k hn hk hC haligned]
  apply hzero _ (cyc_lt hn _ _)
  rw [shift_phase N k ((E/121)%(8801*N)) hN hcell]
  exact hsafe

theorem target_and_predecessor (N C E k : V) (hN : 0<N) (hk : k<8801*N)
    (hC : C<Exp.exp (121*(8801*N))) (haligned : E%121=0)
    (hcell : ((E/121)%(8801*N))%8801=0)
    (hzero : ∀ j<8801*N, ¬Bad (j%8801) → dig 121 C j=0)
    (hp : k%8801=2195 ∨ k%8801=3296 ∨ k%8801=4393 ∨ k%8801=5495) :
    dig 121 (Mixed121Temporal.temporalWord (8801*N) E C) (cyc (8801*N) k 1)=0 ∧
    ((k%8801=4393 ∨ k%8801=5495) → dig 121 (Mixed121Temporal.temporalWord (8801*N) E C) k=0) := by
  have hn : 0<(8801:V)*N := mul_pos (by norm_num) hN
  constructor
  · apply zero_source N C E (cyc (8801*N) k 1) hN (cyc_lt hn _ _) hC haligned hcell hzero
    rw [CyclicAnyPhase.cyc_period 8801 N k 1 (by norm_num) hN]
    exact predecessor_safe _ hp
  · intro hdec
    exact zero_source N C E k hN hk hC haligned hcell hzero (decoder_safe _ hdec)

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
    exact (Mixed121Single.foreign j.val (Or.inl j.isLt)).1
  have hc (j : Fin 44) : dig 121 (rot 121 (8801*N) C (copyOffset 5495 j%(8801*N))) k=0 := by
    rw [dig_rot 121 (8801*N) C _ k (mod_lt _ hn) hk hC,cyc_mod _ _ _ hn]
    apply Mixed121Parity.source_zero N C k (copyOffset 5495 j) hN hzero
    rw [hp]
    exact (Mixed121Single.foreign (Mixed121Kernel.extraPos j) (Mixed121Single.copy_allowed j)).1
  have hb (j : Fin 5) : dig 121 (rot 121 (8801*N) C (bareOffset j%(8801*N))) k=0 := by
    rw [dig_rot 121 (8801*N) C _ k (mod_lt _ hn) hk hC,cyc_mod _ _ _ hn]
    apply Mixed121Parity.source_zero N C k (bareOffset j) hN hzero
    rw [hp]
    exact (Mixed121Single.bare j).1
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
    exact (Mixed121Single.foreign j.val (Or.inl j.isLt)).2
  have hc (j : Fin 44) : dig 121 (rot 121 (8801*N) C (copyOffset 4393 j%(8801*N))) k=0 := by
    rw [dig_rot 121 (8801*N) C _ k (mod_lt _ hn) hk hC,cyc_mod _ _ _ hn]
    apply Mixed121Parity.source_zero N C k (copyOffset 4393 j) hN hzero
    rw [hp]
    exact (Mixed121Single.foreign (Mixed121Kernel.extraPos j) (Mixed121Single.copy_allowed j)).2
  have hb (j : Fin 5) : dig 121 (rot 121 (8801*N) C (bareOffset j%(8801*N))) k=0 := by
    rw [dig_rot 121 (8801*N) C _ k (mod_lt _ hn) hk hC,cyc_mod _ _ _ hn]
    apply Mixed121Parity.source_zero N C k (bareOffset j) hN hzero
    rw [hp]
    exact (Mixed121Single.bare j).2
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
    dig 121 F k=Mixed121Single.decoderBand 4393 (8801*N) C k := by
  have hn : 0<(8801:V)*N := mul_pos (by norm_num) hN
  have hexact := (W121.TemporalCarryExact.clean_exact (8801*N) C T F
    (fun j : Aligned (Fin 943) (Fin 44) => (alignedCoeff selectors copies j:V))
    bandOffsets h k hk aligned_room hT (by rw [hpred]; simp)).2
  have hflat := column_flatten (8801*N) C T k
  obtain ⟨hforeign,hbare⟩ := foreign_at4393 N C k hN hk hC hzero hp
  rw [hforeign,hbare,hT] at hflat
  simp only [add_zero] at hflat
  have hband := band_column 4393 (8801*N) C k hn hk hC
  change columnBand 4393 (8801*N) C k = Mixed121Single.decoderBand 4393 (8801*N) C k at hband
  exact hexact.trans (hflat.trans hband)

theorem clean_column_at5495 (N C T F k : V) (hN : 0<N) (hk : k<8801*N)
    (hC : C<Exp.exp (121*(8801*N)))
    (hzero : ∀ j<8801*N, ¬Bad (j%8801) → dig 121 C j=0)
    (hp : k%8801=5495)
    (h : CarryInput 121 (8801*N) F 1 (cap (ι:=Aligned (Fin 943) (Fin 44)) 121)
      (coefficient (fun j => (alignedCoeff selectors copies j:V)))
      (word 121 (8801*N) C bandOffsets T))
    (hT : dig 121 T k=0) (hpred : dig 121 T (cyc (8801*N) k 1)=0) :
    dig 121 F k=Mixed121Single.decoderBand 5495 (8801*N) C k := by
  have hn : 0<(8801:V)*N := mul_pos (by norm_num) hN
  have hexact := (W121.TemporalCarryExact.clean_exact (8801*N) C T F
    (fun j : Aligned (Fin 943) (Fin 44) => (alignedCoeff selectors copies j:V))
    bandOffsets h k hk aligned_room hT (by rw [hpred]; simp)).2
  have hflat := column_flatten (8801*N) C T k
  obtain ⟨hforeign,hbare⟩ := foreign_at5495 N C k hN hk hC hzero hp
  rw [hforeign,hbare,hT] at hflat
  simp only [zero_add,add_zero] at hflat
  have hband := band_column 5495 (8801*N) C k hn hk hC
  change columnBand 5495 (8801*N) C k = Mixed121Single.decoderBand 5495 (8801*N) C k at hband
  exact hexact.trans (hflat.trans hband)

/-! ## Inputs and decoding at any cell -/

theorem source_phase (N k : V) (T j : ℕ) (hN : 0<N) (hT : T<8801) (hj : j≤T)
    (hp : k%8801=(T:V)) :
    (cyc (8801*N) k (((T-j):ℕ):V))%8801=(j:V) := by
  rw [CyclicAnyPhase.cyc_period 8801 N k (((T-j):ℕ):V) (by norm_num) hN,hp]
  exact Mixed121Selected.source_cell (8801:V) T j (by exact_mod_cast hT) hj

theorem inputs (N C k : V) (T : ℕ) (hN : 0<N) (hT : 3296≤T) (hTmax : T<8801)
    (hp : k%8801=(T:V))
    (hbool : ∀ j<8801*N, j%8801≠1063 → dig 121 C j≤1) :
    (∀ i : Fin 943, Mixed121Band.selDigit (8801*N) C k T i≤1) ∧
    (∀ j < 44, Mixed121Band.copyDigit (8801*N) C k T j≤1) := by
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
    have hmem : Mixed121Band.extraPosN j ∈ Mixed121Kernel.extraPositions := by
      unfold Mixed121Band.extraPosN
      rw [dif_pos hj]
      exact List.get_mem _ _
    have hall := Mixed121Single.extra_allowed _ hmem
    have hne := Mixed121Selected.extra_ne_dummy _ hmem
    have hjT : Mixed121Band.extraPosN j≤T := by
      unfold Mixed121Single.Allowed at hall
      omega
    unfold Mixed121Band.copyDigit
    apply hbool _ (cyc_lt hn _ _)
    rw [source_phase N k T _ hN hTmax hjT hp]
    intro he
    exact hne (by exact_mod_cast he)

theorem local_nocarry (N F k : V) (hN : 0<N) (hk : k<8801*N) (hk0 : 0<k)
    (hphase : k%8801=4393 ∨ k%8801=5495)
    (hhigh : NoCarry F (((Mixed121Ports.highNat:ℕ):V)*rep (121*8801) N-1)) :
    NoCarry (dig 121 F k) ((Exp.exp 10 - 2) + Exp.exp 10 * dsum (Exp.exp 2) (fun _ => 1) 44) := by
  have hd0 : 1≤dig 121 ((Mixed121Ports.highNat:ℕ):V) 0 := by
    rw [Mixed121Selected.model_origin]; norm_num
  have hh := high_mask_digits 121 8801 N F ((Mixed121Ports.highNat:ℕ):V) (by norm_num) hN
    Mixed121Masks.model_high_lt hd0 hhigh
  have h := hh.2 k hk hk0
  have e1 := Mixed121Selected.model_target (V:=V) 4393 Mixed121Selected.high_target4393
  have e2 := Mixed121Selected.model_target (V:=V) 5495 Mixed121Selected.high_target5495
  simp only [Nat.cast_ofNat] at e1 e2
  rcases hphase with hp | hp
  · rw [hp,e1] at h
    exact h
  · rw [hp,e2] at h
    exact h

/-- The decoded selection of the band reflected at `T`, read at cell `k`. -/
def DecodedAt (n C k : V) (T : ℕ) : Prop :=
  ((∀ i, Mixed121Band.selDigit n C k T i = 0) ∧
      ∀ j < 44, Mixed121Band.copyDigit n C k T j = 0) ∨
    ∃ i, CompactSelectorSum.Selected (Mixed121Band.selDigit n C k T) i ∧
      ∀ j < 44, Mixed121Band.copyDigit n C k T j =
        (Mixed121Digits.digit (Compact943Data.row i) j : V)

theorem decode_at (N C F k : V) (T : ℕ) (hN : 0<N) (hT : 3296≤T) (hTmax : T<8801)
    (hp : k%8801=(T:V))
    (hbool : ∀ j<8801*N, j%8801≠1063 → dig 121 C j≤1)
    (hcol : dig 121 F k = Mixed121Single.decoderBand T (8801*N) C k)
    (hnc : NoCarry (dig 121 F k)
      ((Exp.exp 10 - 2) + Exp.exp 10 * dsum (Exp.exp 2) (fun _ => 1) 44)) :
    DecodedAt (8801*N) C k T := by
  obtain ⟨hs, hcp⟩ := inputs N C k T hN hT hTmax hp hbool
  rw [hcol] at hnc
  exact Mixed121Decoder.decode _ (fun i d => (Mixed121Digits.digit (Compact943Data.row i) d : V))
    _ 44 (Compact943Decoder.count_bound _ hs)
    (fun i d _ => by exact_mod_cast Mixed121Digits.digit_le_one _ d) hcp hnc

attribute [local irreducible] Mixed121Ports.betaNat Mixed121Ports.lowNat Mixed121Ports.highNat
  Mixed121Kernel.paramKernel Mixed121Kernel.rho

theorem graph_uniform_decoder (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Mixed121Ports.ports v) :
    let p := Mixed121Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    ∃ N s : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ v 0=rep (121*8801) N ∧
      let E := R-121*(8801*N)
      E%121=0 ∧ s<N ∧ (E/121)%(8801*N)=8801*s ∧
      (∀ k<8801*N, k%8801=4393 → DecodedAt (8801*N) C k 4393) ∧
      (∀ k<8801*N, k%8801=5495 → DecodedAt (8801*N) C k 5495) := by
  obtain ⟨N,w,s,hN,hq,hJ,hle,hw,hv5,hcarry,haligned,hs,hshift⟩ :=
    Mixed121Shift.graph_cell_shift v hv hz
  obtain ⟨N',w',hN',hq',hJ',hle',hw',hv5',hcarry',h0',hzero,hbool⟩ :=
    Mixed121Clean.graph_support_carry v hv hz
  obtain ⟨N'',w'',hN'',hq'',hJ'',hv5'',hcongr'',h0'',hslots,hhigh⟩ :=
    Mixed121Temporal.position_noCarry v hv hz
  dsimp only at *
  have hNN : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((121*8801):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  have hNN' : N''=N := by
    apply mul_left_cancel₀ (by norm_num : ((121*8801):V)≠0)
    exact exp_inj (hq''.symm.trans hq)
  subst N' N''
  let p := Mixed121Ports.ports
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
  have hhigh' : NoCarry (v 1) (((Mixed121Ports.highNat:ℕ):V)*rep (121*8801) N-1) := by
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
end Mixed121Uniform
#print axioms Mixed121Uniform.predecessor_safe
#print axioms Mixed121Uniform.target_and_predecessor
#print axioms Mixed121Uniform.clean_column_at4393
#print axioms Mixed121Uniform.inputs
#print axioms Mixed121Uniform.decode_at
#print axioms Mixed121Uniform.graph_uniform_decoder
