import DiophantineConsistency.Mixed121.Mixed121Uniform

/-! # The field transport identities at the 121x8801 ports

These are the 121x8801 counterpart of Compact44's field-window layer
(`FieldWindowGeometry`, `FieldHighModel`, `FieldWindowReset`,
`FieldWindowColumns`, `FieldWindowParity`, `FieldMarkerParity`) and of the
chain link `graph_field_markers_facts`. They are the recipe's §2 overlap table
for `j < 10`:

| target   | DC source   | DR source   | temporal source |
|----------|-------------|-------------|-----------------|
| 1013 + j | 983 + j     | absent      | 1013 + j        |
| 1065 + j | 1003 + j    | 1023 + j    | absent          |

At a cell of phase `1013 + u`, every other source is a cell outside the
support. Such a cell has low-mask digit `B − 1`, so it is zero
(`zero_absent`). `MF_native` has digit `1` there, the incoming carry resets,
and both surviving digits are Boolean. Parity then forces
`C(k − 30) = C(k − D)`, the vertical transport (`vertical`). Likewise, at
phase `1065 + u` it forces `C(k − 62) = C(k − 8843)`, the horizontal
transport (`horizontal`). Both windows hold for all ten cells. Compact44
treats the last cell of each window as a separate marker case. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Mixed121Field
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticWindowBits
open ArithmeticCyclicWord CompactHeterogeneousCarry CompactGenericAlignedMass
open Mixed121Rotation Mixed121Flatten

/-- Membership in the support `E`, as arithmetic. -/
def InSupp (j : ℕ) : Prop :=
  j<943 ∨ (983≤j ∧ j≤992) ∨ (1003≤j ∧ j≤1032) ∨ j=1063 ∨ j=1064 ∨
    j=1095 ∨ j=1096 ∨ j=2195 ∨ j=3296

theorem insupp_of_mem (j : ℕ) (hj : j ∈ Mixed121Ports.maskSupport) : InSupp j := by
  unfold Mixed121Ports.maskSupport at hj
  rw [List.mem_toFinset, List.mem_filter] at hj
  have h := hj.1
  unfold Mixed121Kernel.support at h
  simp only [List.mem_append, List.mem_range, List.mem_map, List.mem_cons,
    List.not_mem_nil, or_false] at h
  unfold InSupp
  rcases h with ((h | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩) | h <;> omega

def phase (t e : ℕ) : ℕ := (t+8801-e%8801)%8801

theorem high_vertical : ∀ u < 10, Mixed121Ports.highDigits.getD (1013+u) 0 = 1 := by
  decide +kernel
theorem high_horizontal : ∀ u < 10, Mixed121Ports.highDigits.getD (1065+u) 0 = 1 := by
  decide +kernel

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem eq_of_even (x y : V) (hx : x≤1) (hy : y≤1) (hp : (x+y)%2=0) : x=y := by
  rcases le_one_iff_eq_zero_or_one.mp hx with rfl | rfl <;>
    rcases le_one_iff_eq_zero_or_one.mp hy with rfl | rfl <;> norm_num at *

private theorem cast_sub (a b : ℕ) (h : b≤a) : ((a-b:ℕ):V)=(a:V)-(b:V) := by
  apply eq_tsub_of_add_eq
  exact_mod_cast (Nat.sub_add_cancel h)

private theorem cyc_cast (t q : ℕ) :
    cyc (8801:V) (t:V) (q:V) = ((phase t q:ℕ):V) := by
  have hle : q%8801≤t+8801 := by have := Nat.mod_lt q (by omega : 0<8801); omega
  have hc : ((t+8801-q%8801:ℕ):V)=(t:V)+8801-((q%8801:ℕ):V) := by
    rw [cast_sub _ _ hle, Nat.cast_add]; simp only [Nat.cast_ofNat]
  have hm : (q:V)%8801 = ((q%8801:ℕ):V) := by
    simpa only [Nat.cast_ofNat] using (ArithmeticStandardCasts.cast_mod (V:=V) q 8801).symm
  unfold cyc phase
  rw [hm, ←hc]
  simpa only [Nat.cast_ofNat] using
    (ArithmeticStandardCasts.cast_mod (V:=V) (t+8801-q%8801) 8801).symm

/-- The phase of a source cell. -/
theorem cyc_phase (N k : V) (t e : ℕ) (hN : 0<N) (hp : k%8801=(t:V)) :
    (cyc (8801*N) k (e:V))%8801 = ((phase t e:ℕ):V) := by
  rw [CyclicAnyPhase.cyc_period 8801 N k (e:V) (by norm_num) hN, hp, cyc_cast]

/-- A cell whose phase is outside the support is zero. -/
theorem zero_absent (N C x : V) (j : ℕ) (hj : j<8801) (hx : x<8801*N)
    (hph : x%8801=(j:V)) (habs : ¬InSupp j)
    (hslots : ∀ y<8801*N, 0<y →
      NoCarry (dig 121 C y) (dig 121 ((Mixed121Ports.lowNat:ℕ):V) (y%8801))) :
    dig 121 C x=0 := by
  have hx0 : 0<x := by
    by_contra hz
    have he : x=0 := nonpos_iff_eq_zero.mp (not_lt.mp hz)
    rw [he, zero_mod] at hph
    have : j=0 := by exact_mod_cast hph.symm
    exact habs (Or.inl (by omega))
  have hmem : j ∉ Mixed121Ports.maskSupport := fun hm => habs (insupp_of_mem j hm)
  have hspecial : j≠1063 := by intro he; exact habs (by unfold InSupp; omega)
  have hn := hslots x hx hx0
  rw [hph, Mixed121Clean.absent_mask_digit j hj hmem hspecial] at hn
  exact Mixed121Increment.forbidden_zero _ (dig_lt 121 C x) hn

theorem phase_lt (t e : ℕ) : phase t e < 8801 := Nat.mod_lt _ (by norm_num)

/-- A source cell with phase outside the support is zero. -/
theorem source_absent (N C k : V) (t e : ℕ) (hN : 0<N) (hp : k%8801=(t:V))
    (habs : ¬InSupp (phase t e))
    (hslots : ∀ y<8801*N, 0<y →
      NoCarry (dig 121 C y) (dig 121 ((Mixed121Ports.lowNat:ℕ):V) (y%8801))) :
    dig 121 C (cyc (8801*N) k (e:V))=0 := by
  have hn : 0<(8801:V)*N := mul_pos (by norm_num) hN
  exact zero_absent N C _ (phase t e) (phase_lt t e) (cyc_lt hn _ _) (cyc_phase N k t e hN hp)
    habs hslots

/-! ## The column at a field cell -/

attribute [local irreducible] Compact943Data.rows Mixed121Flatten.selectors Mixed121Flatten.copies

/-- The predecessor of a field cell resets the carry. -/
theorem reset (N C E F k : V) (t : ℕ) (hN : 0<N) (hk : k<8801*N)
    (hC : C<Exp.exp (121*(8801*N))) (haligned : E%121=0) (hcell : ((E/121)%(8801*N))%8801=0)
    (ht0 : 1≤t) (htmax : t<8801) (htspecial : t-1≠1063) (hp : k%8801=(t:V))
    (hbool : ∀ j<8801*N, j%8801≠1063 → dig 121 C j≤1)
    (hcarry : CarryInput 121 (8801*N) F 1 (cap (ι:=Aligned (Fin 943) (Fin 44)) 121)
      (coefficient (fun j => (alignedCoeff selectors copies j:V)))
      (word 121 (8801*N) C bandOffsets (Mixed121Temporal.temporalWord (8801*N) E C))) :
    carry 121 (8801*N) (coefficient (fun j => (alignedCoeff selectors copies j:V)))
      (word 121 (8801*N) C bandOffsets (Mixed121Temporal.temporalWord (8801*N) E C))
      (cyc (8801*N) k 1)=0 := by
  let n : V := 8801*N
  let D : V := (E/121)%n
  let kp : V := cyc n k 1
  have hn : 0<n := mul_pos (by norm_num) hN
  have hkpl : kp<n := cyc_lt hn _ _
  have hpredphase : kp%8801=((t-1:ℕ):V) := by
    dsimp only [kp]
    rw [CyclicAnyPhase.cyc_period 8801 N k 1 (by norm_num) hN,hp]
    have htv : (t:V)<8801 := by exact_mod_cast htmax
    have htone : (1:V)≤(t:V) := by exact_mod_cast ht0
    rw [cyc_of_le htv (by norm_num) htone]
    have hs : (((t-1:ℕ):V)+1)=(t:V) := by exact_mod_cast (Nat.sub_add_cancel ht0)
    exact (eq_tsub_of_add_eq hs).symm
  have hsrcphase : (cyc n kp D)%8801=((t-1:ℕ):V) := by
    rw [Mixed121Uniform.shift_phase N kp D hN hcell,hpredphase]
  have hpred : dig 121 (Mixed121Temporal.temporalWord n E C) kp≤1 := by
    rw [Mixed121Shift.aligned_digit C n E kp hn hkpl hC haligned]
    apply hbool _ (cyc_lt hn _ _)
    rw [hsrcphase]
    intro he
    exact htspecial (by exact_mod_cast he)
  have h1 : (1:V)≤Exp.exp 120 := one_le_exp _
  exact (W121.TemporalCarryReset.clean n C (Mixed121Temporal.temporalWord n E C) F
    (fun j : Aligned (Fin 943) (Fin 44) => (alignedCoeff selectors copies j:V))
    bandOffsets hcarry k hk aligned_room (le_trans hpred h1)).1

/-- At a cell where `MF_native` has digit `1` and the carry resets, the
selector sums, the bare column and the temporal digit have even sum. -/
theorem field_parity (N C E F k : V) (t : ℕ) (hN : 0<N) (hk : k<8801*N)
    (hC : C<Exp.exp (121*(8801*N))) (haligned : E%121=0) (hcell : ((E/121)%(8801*N))%8801=0)
    (ht0 : 1≤t) (htmax : t<8801) (htspecial : t-1≠1063) (hp : k%8801=(t:V))
    (hhighd : Mixed121Ports.highDigits.getD t 0 = 1)
    (hbool : ∀ j<8801*N, j%8801≠1063 → dig 121 C j≤1)
    (hhigh : NoCarry F (((Mixed121Ports.highNat:ℕ):V)*rep (121*8801) N-1))
    (hcarry : CarryInput 121 (8801*N) F 1 (cap (ι:=Aligned (Fin 943) (Fin 44)) 121)
      (coefficient (fun j => (alignedCoeff selectors copies j:V)))
      (word 121 (8801*N) C bandOffsets (Mixed121Temporal.temporalWord (8801*N) E C))) :
    (Mixed121Parity.selectorsAt (8801*N) C k 4393 + Mixed121Parity.selectorsAt (8801*N) C k 5495 +
      bareColumn (8801*N) C k + dig 121 (Mixed121Temporal.temporalWord (8801*N) E C) k)%2=0 := by
  let n : V := 8801*N
  have hn : 0<n := mul_pos (by norm_num) hN
  have hk0 : 0<k := by
    by_contra hz
    have he : k=0 := nonpos_iff_eq_zero.mp (not_lt.mp hz)
    rw [he, zero_mod] at hp
    have : t=0 := by exact_mod_cast hp.symm
    omega
  have heven : dig 121 F k%2=0 := by
    have hd0 : 1≤dig 121 ((Mixed121Ports.highNat:ℕ):V) 0 := by
      rw [Mixed121Selected.model_origin]; norm_num
    have hh := high_mask_digits 121 8801 N F ((Mixed121Ports.highNat:ℕ):V) (by norm_num) hN
      Mixed121Masks.model_high_lt hd0 hhigh
    have h := hh.2 k hk hk0
    rw [hp, Mixed121Parity.model_high t hhighd] at h
    exact Mixed121Parity.noCarry_one_even _ h
  have hraw := (Mixed121Parity.raw_plus_incoming_even n F _ _ _ hcarry k hk heven).2
  have hpar := Mixed121Parity.expand n C _ k _ hn hk hC hraw
  rw [reset N C E F k t hN hk hC haligned hcell ht0 htmax htspecial hp hbool hcarry,
    add_zero] at hpar
  exact hpar

/-- Both band selector sums vanish at a field cell whose selector phases are absent. -/
theorem selectors_zero (N C k : V) (t : ℕ) (hN : 0<N) (hp : k%8801=(t:V))
    (hsel : ∀ j<943, ¬InSupp (phase t (4393-j)) ∧ ¬InSupp (phase t (5495-j)))
    (hslots : ∀ y<8801*N, 0<y →
      NoCarry (dig 121 C y) (dig 121 ((Mixed121Ports.lowNat:ℕ):V) (y%8801))) :
    Mixed121Parity.selectorsAt (8801*N) C k 4393=0 ∧
      Mixed121Parity.selectorsAt (8801*N) C k 5495=0 := by
  constructor
  · unfold Mixed121Parity.selectorsAt
    apply Finset.sum_eq_zero
    intro j _
    unfold Mixed121Band.selDigit
    exact source_absent N C k t (4393-j.val) hN hp (hsel j.val j.isLt).1 hslots
  · unfold Mixed121Parity.selectorsAt
    apply Finset.sum_eq_zero
    intro j _
    unfold Mixed121Band.selDigit
    exact source_absent N C k t (5495-j.val) hN hp (hsel j.val j.isLt).2 hslots

/-- The bare column, as the sum of its five source cells. -/
theorem bare_expand (n C k : V) (hn : 0<n) (hk : k<n) (hC : C<Exp.exp (121*n)) :
    bareColumn n C k = dig 121 C (cyc n k ((30:ℕ):V)) + dig 121 C (cyc n k ((62:ℕ):V)) +
      dig 121 C (cyc n k ((1100:ℕ):V)) + dig 121 C (cyc n k ((2200:ℕ):V)) +
      dig 121 C (cyc n k ((8843:ℕ):V)) := by
  unfold bareColumn
  rw [Fin.sum_univ_five]
  simp only [dig_rot 121 n C _ k (mod_lt _ hn) hk hC, cyc_mod _ _ _ hn]
  simp [bareOffset]

/-! ## The two transports -/

theorem vertical (N C E F k : V) (u : ℕ) (hu : u<10) (hN : 0<N) (hk : k<8801*N)
    (hC : C<Exp.exp (121*(8801*N))) (haligned : E%121=0)
    (hcell : ((E/121)%(8801*N))%8801=0) (hp : k%8801=((1013+u:ℕ):V))
    (hslots : ∀ y<8801*N, 0<y →
      NoCarry (dig 121 C y) (dig 121 ((Mixed121Ports.lowNat:ℕ):V) (y%8801)))
    (hbool : ∀ j<8801*N, j%8801≠1063 → dig 121 C j≤1)
    (hhigh : NoCarry F (((Mixed121Ports.highNat:ℕ):V)*rep (121*8801) N-1))
    (hcarry : CarryInput 121 (8801*N) F 1 (cap (ι:=Aligned (Fin 943) (Fin 44)) 121)
      (coefficient (fun j => (alignedCoeff selectors copies j:V)))
      (word 121 (8801*N) C bandOffsets (Mixed121Temporal.temporalWord (8801*N) E C))) :
    dig 121 C (cyc (8801*N) k 30)=dig 121 C (cyc (8801*N) k ((E/121)%(8801*N))) := by
  let n : V := 8801*N
  have hn : 0<n := mul_pos (by norm_num) hN
  have hpar := field_parity N C E F k (1013+u) hN hk hC haligned hcell (by omega) (by omega)
    (by omega) hp (high_vertical u hu) hbool hhigh hcarry
  obtain ⟨hs1, hs2⟩ := selectors_zero N C k (1013+u) hN hp
    (fun j hj => by constructor <;> (unfold phase InSupp; omega)) hslots
  have hb62 := source_absent N C k (1013+u) 62 hN hp (by unfold phase InSupp; omega) hslots
  have hb1100 := source_absent N C k (1013+u) 1100 hN hp (by unfold phase InSupp; omega) hslots
  have hb2200 := source_absent N C k (1013+u) 2200 hN hp (by unfold phase InSupp; omega) hslots
  have hb8843 := source_absent N C k (1013+u) 8843 hN hp (by unfold phase InSupp; omega) hslots
  rw [hs1, hs2, bare_expand n C k hn hk hC, hb62, hb1100, hb2200, hb8843,
    Mixed121Shift.aligned_digit C n E k hn hk hC haligned] at hpar
  simp only [zero_add, add_zero] at hpar
  have hleft : dig 121 C (cyc n k ((30:ℕ):V))≤1 := by
    apply hbool _ (cyc_lt hn _ _)
    rw [cyc_phase N k (1013+u) 30 hN hp]
    intro he
    have : phase (1013+u) 30 = 1063 := by exact_mod_cast he
    unfold phase at this; omega
  have hright : dig 121 C (cyc n k ((E/121)%n))≤1 := by
    apply hbool _ (cyc_lt hn _ _)
    rw [Mixed121Uniform.shift_phase N k _ hN hcell, hp]
    intro he
    have : 1013+u = 1063 := by exact_mod_cast he
    omega
  have h := eq_of_even _ _ hleft hright hpar
  simpa only [Nat.cast_ofNat] using h

theorem horizontal (N C E F k : V) (u : ℕ) (hu : u<10) (hN : 0<N) (hk : k<8801*N)
    (hC : C<Exp.exp (121*(8801*N))) (haligned : E%121=0)
    (hcell : ((E/121)%(8801*N))%8801=0) (hp : k%8801=((1065+u:ℕ):V))
    (hslots : ∀ y<8801*N, 0<y →
      NoCarry (dig 121 C y) (dig 121 ((Mixed121Ports.lowNat:ℕ):V) (y%8801)))
    (hbool : ∀ j<8801*N, j%8801≠1063 → dig 121 C j≤1)
    (hhigh : NoCarry F (((Mixed121Ports.highNat:ℕ):V)*rep (121*8801) N-1))
    (hcarry : CarryInput 121 (8801*N) F 1 (cap (ι:=Aligned (Fin 943) (Fin 44)) 121)
      (coefficient (fun j => (alignedCoeff selectors copies j:V)))
      (word 121 (8801*N) C bandOffsets (Mixed121Temporal.temporalWord (8801*N) E C))) :
    dig 121 C (cyc (8801*N) k 62)=dig 121 C (cyc (8801*N) k 8843) := by
  let n : V := 8801*N
  have hn : 0<n := mul_pos (by norm_num) hN
  have hpar := field_parity N C E F k (1065+u) hN hk hC haligned hcell (by omega) (by omega)
    (by omega) hp (high_horizontal u hu) hbool hhigh hcarry
  obtain ⟨hs1, hs2⟩ := selectors_zero N C k (1065+u) hN hp
    (fun j hj => by constructor <;> (unfold phase InSupp; omega)) hslots
  have hb30 := source_absent N C k (1065+u) 30 hN hp (by unfold phase InSupp; omega) hslots
  have hb1100 := source_absent N C k (1065+u) 1100 hN hp (by unfold phase InSupp; omega) hslots
  have hb2200 := source_absent N C k (1065+u) 2200 hN hp (by unfold phase InSupp; omega) hslots
  have htemp : dig 121 (Mixed121Temporal.temporalWord n E C) k = 0 := by
    rw [Mixed121Shift.aligned_digit C n E k hn hk hC haligned]
    have hph : (cyc n k ((E/121)%n))%8801 = ((1065+u:ℕ):V) := by
      rw [Mixed121Uniform.shift_phase N k _ hN hcell, hp]
    exact zero_absent N C _ (1065+u) (by omega) (cyc_lt hn _ _) hph
      (by unfold InSupp; omega) hslots
  rw [hs1, hs2, bare_expand n C k hn hk hC, hb30, hb1100, hb2200, htemp] at hpar
  simp only [zero_add, add_zero] at hpar
  have hleft : dig 121 C (cyc n k ((62:ℕ):V))≤1 := by
    apply hbool _ (cyc_lt hn _ _)
    rw [cyc_phase N k (1065+u) 62 hN hp]
    intro he
    have : phase (1065+u) 62 = 1063 := by exact_mod_cast he
    unfold phase at this; omega
  have hright : dig 121 C (cyc n k ((8843:ℕ):V))≤1 := by
    apply hbool _ (cyc_lt hn _ _)
    rw [cyc_phase N k (1065+u) 8843 hN hp]
    intro he
    have : phase (1065+u) 8843 = 1063 := by exact_mod_cast he
    unfold phase at this; omega
  have h := eq_of_even _ _ hleft hright hpar
  simpa only [Nat.cast_ofNat] using h

/-! ## The chain link -/

attribute [local irreducible] Mixed121Ports.betaNat Mixed121Ports.lowNat Mixed121Ports.highNat
  Mixed121Kernel.paramKernel Mixed121Kernel.rho

theorem graph_field_markers (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Mixed121Ports.ports v) :
    let p := Mixed121Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    ∃ N s : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ v 0=rep (121*8801) N ∧
      let E := R-121*(8801*N)
      E%121=0 ∧ s<N ∧ (E/121)%(8801*N)=8801*s ∧
      (∀ u : ℕ, u<10 → ∀ k<8801*N, k%8801=((1013+u:ℕ):V) →
        dig 121 C (cyc (8801*N) k 30)=dig 121 C (cyc (8801*N) k ((E/121)%(8801*N)))) ∧
      (∀ u : ℕ, u<10 → ∀ k<8801*N, k%8801=((1065+u:ℕ):V) →
        dig 121 C (cyc (8801*N) k 62)=dig 121 C (cyc (8801*N) k 8843)) := by
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
  have hqexp : q=Exp.exp (121*n) := by dsimp [n]; rw [←mul_assoc]; exact hq
  have hC : C<Exp.exp (121*n) := by
    dsimp [C]
    exact Mixed121Temporal.source_word_bound q n (v 1) (v 2) hqexp (hv 1)
  have hcell : ((E/121)%n)%8801=0 := by rw [hshift,mod_mul_self_right]
  have hhigh' : NoCarry (v 1) (((Mixed121Ports.highNat:ℕ):V)*rep (121*8801) N-1) := by
    rw [←hJ]; exact hhigh
  refine ⟨N,s,hN,hq,hJ,haligned,hs,hshift,?_,?_⟩
  · intro u hu k hk hp
    exact vertical N C E (v 1) k u hu hN hk hC haligned hcell hp hslots hbool hhigh' hcarry
  · intro u hu k hk hp
    exact horizontal N C E (v 1) k u hu hN hk hC haligned hcell hp hslots hbool hhigh' hcarry
end Mixed121Field
#print axioms Mixed121Field.insupp_of_mem
#print axioms Mixed121Field.high_vertical
#print axioms Mixed121Field.zero_absent
#print axioms Mixed121Field.field_parity
#print axioms Mixed121Field.vertical
#print axioms Mixed121Field.horizontal
#print axioms Mixed121Field.graph_field_markers
