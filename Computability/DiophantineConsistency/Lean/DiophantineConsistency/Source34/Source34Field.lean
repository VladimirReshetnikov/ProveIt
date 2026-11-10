import DiophantineConsistency.Source34.Source34Uniform
import DiophantineConsistency.Mixed121.Mixed121Field
import Mathlib.Tactic.IntervalCases

/-! # The field transport identities at the source34 ports

`Mixed121Field` at the source34 tuple. This is where the stride-two copy
geometry changes the mathematics. The recipe's overlap table for `u < 10` is
now

| target       | DC source        | DR source         | temporal source |
|--------------|------------------|-------------------|-----------------|
| 1000 + 2u    | 960 + 2u (`ρ^40`) | absent            | 1000 + 2u       |
| 1021 + 2u    | 980 + 2u (`ρ^41`) | 1020 + 2u (`ρ^8802`) | absent      |

(121x8801: targets `1013 + u` and `1065 + u`, shifts `30`, `62`, `8843`.)
The support is `0..942`, the even cells `960..1038`, the dummies and the
anchors (`InSupp`). At a cell of phase `1000 + 2u` the other bare sources
`959 + 2u`, `8701 + 2u`, `7601 + 2u`, `999 + 2u` and every selector source
are outside it; at phase `1021 + 2u` the sources `981 + 2u`, `8722 + 2u`,
`7622 + 2u` and the odd temporal phase `1021 + 2u` are outside it. Temporal
targets are even and spatial targets odd, so each window sees exactly its two
Boolean sources. `MF_native` has digit `1` at both windows (`high_vertical`,
`high_horizontal`), and parity gives

* `vertical`: `C(k − 40) = C(k − D)` at phase `1000 + 2u`;
* `horizontal`: `C(k − 41) = C(k − 8802)` at phase `1021 + 2u`.

Generic and used directly: `Mixed121Field.phase`, `eq_of_even`, `cyc_phase`,
`phase_lt`. Everything else is re-declared. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Source34Field
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticWindowBits
open ArithmeticCyclicWord CompactHeterogeneousCarry CompactGenericAlignedMass
open Source34Rotation Source34Flatten
open Mixed121Rotation (selectorOffset coefficient word cap)
open Mixed121Flatten (selectors copies aligned_room)
open Mixed121Field (phase eq_of_even cyc_phase phase_lt)

/-- Membership in the source34 support `E`, as arithmetic. -/
def InSupp (j : ℕ) : Prop :=
  j<943 ∨ (960≤j ∧ j≤1038 ∧ j%2=0) ∨ j=1063 ∨ j=1064 ∨
    j=1095 ∨ j=1096 ∨ j=2195 ∨ j=3296

theorem insupp_of_mem (j : ℕ) (hj : j ∈ Source34Ports.maskSupport) : InSupp j := by
  unfold Source34Ports.maskSupport at hj
  rw [List.mem_toFinset, List.mem_filter] at hj
  have h := hj.1
  unfold Source34Kernel.support at h
  simp only [List.mem_append, List.mem_range, List.mem_map, List.mem_cons,
    List.not_mem_nil, or_false] at h
  unfold InSupp
  rcases h with (h | ⟨a, ha, rfl⟩) | h <;> omega

theorem high_vertical : ∀ u < 10, Source34Ports.highDigits.getD (1000+2*u) 0 = 1 := by
  decide +kernel
theorem high_horizontal : ∀ u < 10, Source34Ports.highDigits.getD (1021+2*u) 0 = 1 := by
  decide +kernel

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A cell whose phase is outside the support is zero. -/
theorem zero_absent (N C x : V) (j : ℕ) (hj : j<8801) (hx : x<8801*N)
    (hph : x%8801=(j:V)) (habs : ¬InSupp j)
    (hslots : ∀ y<8801*N, 0<y →
      NoCarry (dig 121 C y) (dig 121 ((Source34Ports.lowNat:ℕ):V) (y%8801))) :
    dig 121 C x=0 := by
  have hx0 : 0<x := by
    by_contra hz
    have he : x=0 := nonpos_iff_eq_zero.mp (not_lt.mp hz)
    rw [he, zero_mod] at hph
    have : j=0 := by exact_mod_cast hph.symm
    exact habs (Or.inl (by omega))
  have hmem : j ∉ Source34Ports.maskSupport := fun hm => habs (insupp_of_mem j hm)
  have hspecial : j≠1063 := by intro he; exact habs (by unfold InSupp; omega)
  have hn := hslots x hx hx0
  rw [hph, Source34Clean.absent_mask_digit j hj hmem hspecial] at hn
  exact Mixed121Increment.forbidden_zero _ (dig_lt 121 C x) hn


/-- A source cell with phase outside the support is zero. -/
theorem source_absent (N C k : V) (t e : ℕ) (hN : 0<N) (hp : k%8801=(t:V))
    (habs : ¬InSupp (phase t e))
    (hslots : ∀ y<8801*N, 0<y →
      NoCarry (dig 121 C y) (dig 121 ((Source34Ports.lowNat:ℕ):V) (y%8801))) :
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
    (hhighd : Source34Ports.highDigits.getD t 0 = 1)
    (hbool : ∀ j<8801*N, j%8801≠1063 → dig 121 C j≤1)
    (hhigh : NoCarry F (((Source34Ports.highNat:ℕ):V)*rep (121*8801) N-1))
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
    have hd0 : 1≤dig 121 ((Source34Ports.highNat:ℕ):V) 0 := by
      rw [Source34Selected.model_origin]; norm_num
    have hh := high_mask_digits 121 8801 N F ((Source34Ports.highNat:ℕ):V) (by norm_num) hN
      Source34Masks.model_high_lt hd0 hhigh
    have h := hh.2 k hk hk0
    rw [hp, Source34Parity.model_high t hhighd] at h
    exact Mixed121Parity.noCarry_one_even _ h
  have hraw := (Mixed121Parity.raw_plus_incoming_even n F _ _ _ hcarry k hk heven).2
  have hpar := Source34Parity.expand n C _ k _ hn hk hC hraw
  rw [reset N C E F k t hN hk hC haligned hcell ht0 htmax htspecial hp hbool hcarry,
    add_zero] at hpar
  exact hpar

/-- Both band selector sums vanish at a field cell whose selector phases are absent. -/
theorem selectors_zero (N C k : V) (t : ℕ) (hN : 0<N) (hp : k%8801=(t:V))
    (hsel : ∀ j<943, ¬InSupp (phase t (4393-j)) ∧ ¬InSupp (phase t (5495-j)))
    (hslots : ∀ y<8801*N, 0<y →
      NoCarry (dig 121 C y) (dig 121 ((Source34Ports.lowNat:ℕ):V) (y%8801))) :
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
    bareColumn n C k = dig 121 C (cyc n k ((40:ℕ):V)) + dig 121 C (cyc n k ((41:ℕ):V)) +
      dig 121 C (cyc n k ((1100:ℕ):V)) + dig 121 C (cyc n k ((2200:ℕ):V)) +
      dig 121 C (cyc n k ((8802:ℕ):V)) := by
  unfold bareColumn
  rw [Fin.sum_univ_five]
  simp only [dig_rot 121 n C _ k (mod_lt _ hn) hk hC, cyc_mod _ _ _ hn]
  simp [bareOffset]

/-! ## Finite window geometry

`omega` alone does not close these facts for a symbolic `u`, nor the parity
test of `InSupp` under the outer `mod 8801`: both need the dark-shadow step
that Lean's `omega` omits. So `u < 10` is split into its ten values, the
selector phases (which avoid `960..1038` altogether) go through the coarse
`not_insupp`, and the remaining closed phases are evaluated by `norm_num`. The same facts are
checked by `s34_geometry_check2.py` outside Lean. -/

theorem not_insupp (j : ℕ)
    (h : ¬(j<943 ∨ (960≤j ∧ j≤1038) ∨ j=1063 ∨ j=1064 ∨ j=1095 ∨ j=1096 ∨ j=2195 ∨ j=3296)) :
    ¬InSupp j := by
  unfold InSupp; omega

theorem vertical_geometry (u : ℕ) (hu : u<10) :
    (∀ j<943, ¬InSupp (phase (1000+2*u) (4393-j)) ∧ ¬InSupp (phase (1000+2*u) (5495-j))) ∧
    ¬InSupp (phase (1000+2*u) 41) ∧ ¬InSupp (phase (1000+2*u) 1100) ∧
    ¬InSupp (phase (1000+2*u) 2200) ∧ ¬InSupp (phase (1000+2*u) 8802) ∧
    phase (1000+2*u) 40 ≠ 1063 := by
  interval_cases u <;>
    refine ⟨fun j hj => ⟨not_insupp _ ?_, not_insupp _ ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | (unfold phase; omega) | norm_num [phase, InSupp]

theorem horizontal_geometry (u : ℕ) (hu : u<10) :
    (∀ j<943, ¬InSupp (phase (1021+2*u) (4393-j)) ∧ ¬InSupp (phase (1021+2*u) (5495-j))) ∧
    ¬InSupp (phase (1021+2*u) 40) ∧ ¬InSupp (phase (1021+2*u) 1100) ∧
    ¬InSupp (phase (1021+2*u) 2200) ∧ ¬InSupp (1021+2*u) ∧
    phase (1021+2*u) 41 ≠ 1063 ∧ phase (1021+2*u) 8802 ≠ 1063 := by
  interval_cases u <;>
    refine ⟨fun j hj => ⟨not_insupp _ ?_, not_insupp _ ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | (unfold phase; omega) | norm_num [phase, InSupp]

/-! ## The two transports -/

theorem vertical (N C E F k : V) (u : ℕ) (hu : u<10) (hN : 0<N) (hk : k<8801*N)
    (hC : C<Exp.exp (121*(8801*N))) (haligned : E%121=0)
    (hcell : ((E/121)%(8801*N))%8801=0) (hp : k%8801=((1000+2*u:ℕ):V))
    (hslots : ∀ y<8801*N, 0<y →
      NoCarry (dig 121 C y) (dig 121 ((Source34Ports.lowNat:ℕ):V) (y%8801)))
    (hbool : ∀ j<8801*N, j%8801≠1063 → dig 121 C j≤1)
    (hhigh : NoCarry F (((Source34Ports.highNat:ℕ):V)*rep (121*8801) N-1))
    (hcarry : CarryInput 121 (8801*N) F 1 (cap (ι:=Aligned (Fin 943) (Fin 44)) 121)
      (coefficient (fun j => (alignedCoeff selectors copies j:V)))
      (word 121 (8801*N) C bandOffsets (Mixed121Temporal.temporalWord (8801*N) E C))) :
    dig 121 C (cyc (8801*N) k 40)=dig 121 C (cyc (8801*N) k ((E/121)%(8801*N))) := by
  let n : V := 8801*N
  have hn : 0<n := mul_pos (by norm_num) hN
  obtain ⟨gsel, g41, g1100, g2200, g8802, g40⟩ := vertical_geometry u hu
  have hpar := field_parity N C E F k (1000+2*u) hN hk hC haligned hcell (by omega) (by omega)
    (by omega) hp (high_vertical u hu) hbool hhigh hcarry
  obtain ⟨hs1, hs2⟩ := selectors_zero N C k (1000+2*u) hN hp
    gsel hslots
  have hb41 := source_absent N C k (1000+2*u) 41 hN hp g41 hslots
  have hb1100 := source_absent N C k (1000+2*u) 1100 hN hp g1100 hslots
  have hb2200 := source_absent N C k (1000+2*u) 2200 hN hp g2200 hslots
  have hb8802 := source_absent N C k (1000+2*u) 8802 hN hp g8802 hslots
  rw [hs1, hs2, bare_expand n C k hn hk hC, hb41, hb1100, hb2200, hb8802,
    Mixed121Shift.aligned_digit C n E k hn hk hC haligned] at hpar
  simp only [zero_add, add_zero] at hpar
  have hleft : dig 121 C (cyc n k ((40:ℕ):V))≤1 := by
    apply hbool _ (cyc_lt hn _ _)
    rw [cyc_phase N k (1000+2*u) 40 hN hp]
    intro he
    exact g40 (by exact_mod_cast he)
  have hright : dig 121 C (cyc n k ((E/121)%n))≤1 := by
    apply hbool _ (cyc_lt hn _ _)
    rw [Mixed121Uniform.shift_phase N k _ hN hcell, hp]
    intro he
    have : 1000+2*u = 1063 := by exact_mod_cast he
    omega
  have h := eq_of_even _ _ hleft hright hpar
  simpa only [Nat.cast_ofNat] using h

theorem horizontal (N C E F k : V) (u : ℕ) (hu : u<10) (hN : 0<N) (hk : k<8801*N)
    (hC : C<Exp.exp (121*(8801*N))) (haligned : E%121=0)
    (hcell : ((E/121)%(8801*N))%8801=0) (hp : k%8801=((1021+2*u:ℕ):V))
    (hslots : ∀ y<8801*N, 0<y →
      NoCarry (dig 121 C y) (dig 121 ((Source34Ports.lowNat:ℕ):V) (y%8801)))
    (hbool : ∀ j<8801*N, j%8801≠1063 → dig 121 C j≤1)
    (hhigh : NoCarry F (((Source34Ports.highNat:ℕ):V)*rep (121*8801) N-1))
    (hcarry : CarryInput 121 (8801*N) F 1 (cap (ι:=Aligned (Fin 943) (Fin 44)) 121)
      (coefficient (fun j => (alignedCoeff selectors copies j:V)))
      (word 121 (8801*N) C bandOffsets (Mixed121Temporal.temporalWord (8801*N) E C))) :
    dig 121 C (cyc (8801*N) k 41)=dig 121 C (cyc (8801*N) k 8802) := by
  let n : V := 8801*N
  have hn : 0<n := mul_pos (by norm_num) hN
  obtain ⟨gsel, g40, g1100, g2200, gtemp, g41, g8802⟩ := horizontal_geometry u hu
  have hpar := field_parity N C E F k (1021+2*u) hN hk hC haligned hcell (by omega) (by omega)
    (by omega) hp (high_horizontal u hu) hbool hhigh hcarry
  obtain ⟨hs1, hs2⟩ := selectors_zero N C k (1021+2*u) hN hp
    gsel hslots
  have hb40 := source_absent N C k (1021+2*u) 40 hN hp g40 hslots
  have hb1100 := source_absent N C k (1021+2*u) 1100 hN hp g1100 hslots
  have hb2200 := source_absent N C k (1021+2*u) 2200 hN hp g2200 hslots
  have htemp : dig 121 (Mixed121Temporal.temporalWord n E C) k = 0 := by
    rw [Mixed121Shift.aligned_digit C n E k hn hk hC haligned]
    have hph : (cyc n k ((E/121)%n))%8801 = ((1021+2*u:ℕ):V) := by
      rw [Mixed121Uniform.shift_phase N k _ hN hcell, hp]
    exact zero_absent N C _ (1021+2*u) (by omega) (cyc_lt hn _ _) hph
      gtemp hslots
  rw [hs1, hs2, bare_expand n C k hn hk hC, hb40, hb1100, hb2200, htemp] at hpar
  simp only [zero_add, add_zero] at hpar
  have hleft : dig 121 C (cyc n k ((41:ℕ):V))≤1 := by
    apply hbool _ (cyc_lt hn _ _)
    rw [cyc_phase N k (1021+2*u) 41 hN hp]
    intro he
    exact g41 (by exact_mod_cast he)
  have hright : dig 121 C (cyc n k ((8802:ℕ):V))≤1 := by
    apply hbool _ (cyc_lt hn _ _)
    rw [cyc_phase N k (1021+2*u) 8802 hN hp]
    intro he
    exact g8802 (by exact_mod_cast he)
  have h := eq_of_even _ _ hleft hright hpar
  simpa only [Nat.cast_ofNat] using h

/-! ## The chain link -/

attribute [local irreducible] Source34Ports.betaNat Source34Ports.lowNat Source34Ports.highNat
  Source34Kernel.paramKernel Mixed121Kernel.rho

theorem graph_field_markers (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Source34Ports.ports v) :
    let p := Source34Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    ∃ N s : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ v 0=rep (121*8801) N ∧
      let E := R-121*(8801*N)
      E%121=0 ∧ s<N ∧ (E/121)%(8801*N)=8801*s ∧
      (∀ u : ℕ, u<10 → ∀ k<8801*N, k%8801=((1000+2*u:ℕ):V) →
        dig 121 C (cyc (8801*N) k 40)=dig 121 C (cyc (8801*N) k ((E/121)%(8801*N)))) ∧
      (∀ u : ℕ, u<10 → ∀ k<8801*N, k%8801=((1021+2*u:ℕ):V) →
        dig 121 C (cyc (8801*N) k 41)=dig 121 C (cyc (8801*N) k 8802)) := by
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
  have hqexp : q=Exp.exp (121*n) := by dsimp [n]; rw [←mul_assoc]; exact hq
  have hC : C<Exp.exp (121*n) := by
    dsimp [C]
    exact Mixed121Temporal.source_word_bound q n (v 1) (v 2) hqexp (hv 1)
  have hcell : ((E/121)%n)%8801=0 := by rw [hshift,mod_mul_self_right]
  have hhigh' : NoCarry (v 1) (((Source34Ports.highNat:ℕ):V)*rep (121*8801) N-1) := by
    rw [←hJ]; exact hhigh
  refine ⟨N,s,hN,hq,hJ,haligned,hs,hshift,?_,?_⟩
  · intro u hu k hk hp
    exact vertical N C E (v 1) k u hu hN hk hC haligned hcell hp hslots hbool hhigh' hcarry
  · intro u hu k hk hp
    exact horizontal N C E (v 1) k u hu hN hk hC haligned hcell hp hslots hbool hhigh' hcarry
end Source34Field
#print axioms Source34Field.insupp_of_mem
#print axioms Source34Field.high_vertical
#print axioms Source34Field.not_insupp
#print axioms Source34Field.vertical_geometry
#print axioms Source34Field.horizontal_geometry
#print axioms Source34Field.zero_absent
#print axioms Source34Field.field_parity
#print axioms Source34Field.vertical
#print axioms Source34Field.horizontal
#print axioms Source34Field.graph_field_markers
