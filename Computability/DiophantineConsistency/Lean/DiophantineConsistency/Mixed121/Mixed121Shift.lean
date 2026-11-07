import DiophantineConsistency.Mixed121.Mixed121AnchorParity
import DiophantineConsistency.Mixed121.W121.FractionalBooleanWindows
import DiophantineConsistency.Compact44.TemporalEvenCarry

/-! # The temporal rotation is a whole number of native periods

These are the 121x8801 counterparts of Compact44's `ParityPreviousPhase`,
`ParityAdjacentPhase`, `FractionalAnchorConflict`, `AlignedTemporalAnchor`,
`AlignedAnchorPhase`, `AlignedAnchorModel` and the chain links
`graph_aligned_shift_facts` and `graph_cell_shift_facts`. This is the
recipe's binary-alignment argument for `b = 121`.

* `graph_aligned_shift`: the bit rotation `E = R − 121·8801N` of the temporal
  word is a multiple of `121`. A fractional rotation contradicts the anchor
  parity at one of the cells `2195`, `3296`. That cell is the one whose source
  avoids the dummies (`choose_two_ordinary`; its two candidate phases differ by
  `1101`).
* `graph_cell_shift`: the cell rotation `E/121` is a multiple of `8801`. At
  both anchors the aligned temporal digit is nonzero, so both sources lie in
  `Bad`. `1101` occurs in `Bad − Bad` only as `3296 − 2195`, so the shift is
  `0` modulo `8801` (`model_zero`, by `omega`). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Mixed121Shift
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticCyclicWord
open CompactHeterogeneousCarry CompactGenericAlignedMass Mixed121Rotation Mixed121Flatten
open Mixed121Clean

/-! ## Finite phase facts -/

def badDummy (x : ℕ) : Prop := x=1063 ∨ x=1064

theorem nat_choice (d : ℕ) (hd : d<8801) :
    ¬badDummy ((2194+8801-d)%8801) ∨ ¬badDummy ((3295+8801-d)%8801) := by
  unfold badDummy
  omega

theorem nat_zero (d : ℕ) (hd : d<8801)
    (h1 : BadNat ((2195+8801-d)%8801)) (h2 : BadNat ((3296+8801-d)%8801)) : d=0 := by
  unfold BadNat at h1 h2
  omega

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem cast_sub (a b : ℕ) (h : b≤a) : ((a-b:ℕ):V)=(a:V)-(b:V) := by
  apply eq_tsub_of_add_eq
  exact_mod_cast (Nat.sub_add_cancel h)

private theorem cyc_cast (t q : ℕ) :
    cyc (8801:V) (t:V) (q:V) = (((t+8801-q%8801)%8801:ℕ):V) := by
  have hle : q%8801≤t+8801 := by have := Nat.mod_lt q (by omega : 0<8801); omega
  have hc : ((t+8801-q%8801:ℕ):V)=(t:V)+8801-((q%8801:ℕ):V) := by
    rw [cast_sub _ _ hle, Nat.cast_add]; simp only [Nat.cast_ofNat]
  have hm : (q:V)%8801 = ((q%8801:ℕ):V) := by
    simpa only [Nat.cast_ofNat] using (ArithmeticStandardCasts.cast_mod (V:=V) q 8801).symm
  unfold cyc
  rw [hm, ←hc]
  simpa only [Nat.cast_ofNat] using
    (ArithmeticStandardCasts.cast_mod (V:=V) (t+8801-q%8801) 8801).symm

private theorem mod_add_mod' {n : V} (hn : 0<n) (x y : V) : (x%n+y)%n=(x+y)%n := by
  rw [mod_add hn,mod_eq_self_of_lt (mod_lt x hn),←mod_add hn]

private theorem cyc_add_mod {n : V} (hn : 0<n) (k e : V) : (cyc n k e+e)%n=k%n := by
  unfold cyc
  rw [mod_add_mod' hn]
  have hle : e%n≤k+n := le_trans (le_of_lt (mod_lt e hn)) le_add_self
  have he : k+n-e%n+e=(k+n)+n*(e/n) := by
    calc
      _ = k+n-e%n+(n*(e/n)+e%n) := by rw [div_add_mod]
      _ = (k+n-e%n+e%n)+n*(e/n) := by ring
      _ = _ := by rw [tsub_add_cancel_of_le hle]
  rw [he,mod_add_mul' _ _ hn,mod_add_remove_right hn]

theorem previous_ordinary (N j : V) (hN : 0<N) (hphase : j%8801≠1064) :
    (cyc (8801*N) j 1)%8801≠1063 := by
  intro hprev
  have hp := CyclicAnyPhase.cyc_period 8801 N j 1 (by norm_num) hN
  rw [hprev] at hp
  have h := cyc_add_mod (by norm_num : (0:V)<8801) (j%8801) 1
  rw [←hp] at h
  have hleft : ((1063:V)+1)%8801=1064 := by
    rw [show (1063:V)+1=1064 by norm_num,mod_eq_self_of_lt (by norm_num)]
  rw [hleft, mod_eq_self_of_lt (mod_lt _ (by norm_num : (0:V)<8801))] at h
  exact hphase h.symm

theorem choose_two_ordinary (N D : V) (hN : 0<N) :
    let a := (cyc (8801*N) 2194 D)%8801
    let b := (cyc (8801*N) 3295 D)%8801
    (a≠1063 ∧ a≠1064) ∨ (b≠1063 ∧ b≠1064) := by
  have hdlt : D%8801<8801 := mod_lt _ (by norm_num)
  obtain ⟨d,hd,hdv⟩ := CleanGeometry.bounded_standard 8801 (D%8801) hdlt
  have h1 := CyclicAnyPhase.cyc_period 8801 N 2194 D (by norm_num) hN
  have h2 := CyclicAnyPhase.cyc_period 8801 N 3295 D (by norm_num) hN
  rw [mod_eq_self_of_lt (by norm_num : (2194:V)<8801)] at h1
  rw [mod_eq_self_of_lt (by norm_num : (3295:V)<8801)] at h2
  rw [←cyc_mod 8801 2194 D (by norm_num), hdv] at h1
  rw [←cyc_mod 8801 3295 D (by norm_num), hdv] at h2
  have hc1 : cyc (8801:V) 2194 (d:V)=(((2194+8801-d)%8801:ℕ):V) := by
    simpa only [Nat.cast_ofNat,Nat.mod_eq_of_lt hd] using (cyc_cast (V:=V) 2194 d)
  have hc2 : cyc (8801:V) 3295 (d:V)=(((3295+8801-d)%8801:ℕ):V) := by
    simpa only [Nat.cast_ofNat,Nat.mod_eq_of_lt hd] using (cyc_cast (V:=V) 3295 d)
  rw [hc1] at h1
  rw [hc2] at h2
  have h := nat_choice d hd
  rcases h with h | h
  · left
    constructor <;> intro he <;> apply h <;> unfold badDummy
    · left; exact_mod_cast (h1.symm.trans he)
    · right; exact_mod_cast (h1.symm.trans he)
  · right
    constructor <;> intro he <;> apply h <;> unfold badDummy
    · left; exact_mod_cast (h2.symm.trans he)
    · right; exact_mod_cast (h2.symm.trans he)

theorem model_zero (D : V) (h1 : Bad (cyc 8801 2195 D)) (h2 : Bad (cyc 8801 3296 D)) :
    D%8801=0 := by
  have hdlt : D%8801<8801 := mod_lt _ (by norm_num)
  obtain ⟨d,hd,hdv⟩ := CleanGeometry.bounded_standard 8801 (D%8801) hdlt
  rw [←cyc_mod 8801 2195 D (by norm_num), hdv] at h1
  rw [←cyc_mod 8801 3296 D (by norm_num), hdv] at h2
  have hc1 : cyc (8801:V) 2195 (d:V)=(((2195+8801-d)%8801:ℕ):V) := by
    simpa only [Nat.cast_ofNat,Nat.mod_eq_of_lt hd] using (cyc_cast (V:=V) 2195 d)
  have hc2 : cyc (8801:V) 3296 (d:V)=(((3296+8801-d)%8801:ℕ):V) := by
    simpa only [Nat.cast_ofNat,Nat.mod_eq_of_lt hd] using (cyc_cast (V:=V) 3296 d)
  rw [hc1,bad_cast] at h1
  rw [hc2,bad_cast] at h2
  have hz := nat_zero d hd h1 h2
  simpa only [hz,Nat.cast_zero] using hdv

/-! ## Width-121 temporal lemmas over the carry family -/

section family
variable {ι : Type*} [Fintype ι]

theorem conflict (n C E F : V) (a e : ι→V) (hn : 0<n) (hC : C<Exp.exp (121*n))
    (h : CarryInput 121 n F 1 (cap (ι:=ι) 121)
      (coefficient a) (word 121 n C e (Mixed121Temporal.temporalWord n E C)))
    (t : V) (ht : t<n) (hroom : (∑ j, a j*3)+1<Exp.exp 120) (hr0 : 0<E%121)
    (hpar : (1 + dig 121 (Mixed121Temporal.temporalWord n E C) t +
      carry 121 n (coefficient a) (word 121 n C e (Mixed121Temporal.temporalWord n E C))
        (cyc n t 1))%2=0)
    (hb : dig 121 C (cyc n (cyc n t 1) ((E/121)%n))≤1)
    (hbprev : dig 121 C (cyc n (cyc n (cyc n t 1) ((E/121)%n)) 1)≤1) : False := by
  have hprev : dig 121 C (cyc n (cyc n t ((E/121)%n)) 1)≤1 := by
    rw [W121.TemporalSourcePredecessor.cyclic_commute n t ((E/121)%n) 1 hn]
    exact hb
  have he := W121.FractionalBooleanWindows.even_if_previous_boolean C n E t hn ht hC hr0 hprev
  have hcb := carry_le h (cyc_lt hn t 1)
  have hc1 := TemporalEvenCarry.carry_one _ _ hcb he hpar
  have hhalf := W121.FractionalBooleanWindows.half_if_both_boolean C n E (cyc n t 1)
    hn (cyc_lt hn t 1) hC hb hbprev
  have hc0 := (W121.TemporalCarryReset.clean n C (Mixed121Temporal.temporalWord n E C) F a e h t
    ht hroom hhalf).1
  rw [hc1] at hc0
  exact _root_.one_ne_zero hc0

theorem aligned_digit (C n E t : V) (hn : 0<n) (ht : t<n) (hC : C<Exp.exp (121*n))
    (haligned : E%121=0) :
    dig 121 (Mixed121Temporal.temporalWord n E C) t = dig 121 C (cyc n t ((E/121)%n)) := by
  have h := W121.TemporalSourceUnified.digit C n E t hn ht hC
  dsimp only at h
  rw [haligned] at h
  have hd := dig_lt 121 C (cyc n t ((E/121)%n))
  have hp := dig_lt 121 C (cyc n (cyc n t ((E/121)%n)) 1)
  simp only [exp_zero,mul_one,tsub_zero,mod_eq_self_of_lt hd,
    div_eq_zero_of_lt _ hp,add_zero] at h
  exact h

theorem anchor_nonzero (n C E F : V) (a e : ι→V)
    (hn : 0<n) (hC : C<Exp.exp (121*n)) (hcap : ∀ j<n, dig 121 C j≤3)
    (h : CarryInput 121 n F 1 (cap (ι:=ι) 121)
      (coefficient a) (word 121 n C e (Mixed121Temporal.temporalWord n E C)))
    (t : V) (ht : t<n) (hroom : (∑ j, a j*3)+1<Exp.exp 120) (haligned : E%121=0)
    (hpar : (1 + dig 121 (Mixed121Temporal.temporalWord n E C) t +
      carry 121 n (coefficient a) (word 121 n C e (Mixed121Temporal.temporalWord n E C))
        (cyc n t 1))%2=0) :
    dig 121 C (cyc n t ((E/121)%n))≠0 := by
  have hthree : (3:V)≤Exp.exp 120 := by
    have h4 : Exp.exp (2:V)=4 := by
      rw [show (2:V)=1+1 by norm_num,exp_succ,exp_one]
      norm_num
    have h := exp_monotone_le.mpr (show (2:V)≤120 by norm_num)
    rw [h4] at h
    exact le_trans (by norm_num) h
  have hpred : dig 121 (Mixed121Temporal.temporalWord n E C) (cyc n t 1)≤3 := by
    rw [aligned_digit C n E (cyc n t 1) hn (cyc_lt hn _ _) hC haligned]
    exact hcap _ (cyc_lt hn _ _)
  have hc0 := (W121.TemporalCarryReset.clean n C (Mixed121Temporal.temporalWord n E C) F a e h t
    ht hroom (le_trans hpred hthree)).1
  have hsource := aligned_digit C n E t hn ht hC haligned
  intro hz
  rw [hc0,hsource,hz] at hpar
  norm_num at hpar
end family

/-! ## The chain links -/

attribute [local irreducible] Compact943Data.rows Mixed121Flatten.selectors Mixed121Flatten.copies
attribute [local irreducible] Mixed121Ports.betaNat Mixed121Ports.lowNat Mixed121Ports.highNat
  Mixed121Kernel.paramKernel Mixed121Kernel.rho

theorem graph_aligned_shift (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Mixed121Ports.ports v) :
    let p := Mixed121Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    let a := coefficient (fun j : Aligned (Fin 943) (Fin 44) => (alignedCoeff selectors copies j:V))
    ∃ N w : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ v 0=rep (121*8801) N ∧
      (121*8801)*N≤R ∧ w=Exp.exp (R-(121*8801)*N) ∧ v 5=q*w ∧
      let E := R-121*(8801*N)
      let T := Mixed121Temporal.temporalWord (8801*N) E C
      let X := word 121 (8801*N) C bandOffsets T
      CarryInput 121 (8801*N) (v 1) 1 (cap (ι:=Aligned (Fin 943) (Fin 44)) 121) a X ∧
      E%121=0 := by
  obtain ⟨N,w,hN,hq,hJ,hle,hw,hv5,hcarry,h1095,h1096,hpar1,hpar2⟩ :=
    Mixed121AnchorParity.graph_anchor_parity v hv hz
  obtain ⟨N',w',hN',hq',hJ',hle',hw',hv5',hcarry',h0',hzero,hbool⟩ :=
    Mixed121Clean.graph_support_carry v hv hz
  dsimp only at *
  have hNN : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((121*8801):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
  let p := Mixed121Ports.ports
  let q : V := 1+v 0*(p 0:V)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  let C : V := q-v 1-v 2
  let n : V := 8801*N
  let E : V := R-121*n
  have hn : 0<n := mul_pos (by norm_num) hN
  have hnge : (8801:V)≤n := by
    have h := mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hN) (by norm_num : (0:V)≤8801)
    simpa only [n,mul_one] using h
  have ht1 : (2195:V)<n := lt_of_lt_of_le (by norm_num) hnge
  have ht2 : (3296:V)<n := lt_of_lt_of_le (by norm_num) hnge
  have hp1 : cyc n 2195 1=2194 := by
    rw [cyc_of_le ht1 (lt_trans (by norm_num : (1:V)<2195) ht1) (by norm_num)]
    exact (eq_tsub_of_add_eq (show (2194:V)+1=2195 by norm_num)).symm
  have hp2 : cyc n 3296 1=3295 := by
    rw [cyc_of_le ht2 (lt_trans (by norm_num : (1:V)<3296) ht2) (by norm_num)]
    exact (eq_tsub_of_add_eq (show (3295:V)+1=3296 by norm_num)).symm
  have hqexp : q=Exp.exp (121*n) := by dsimp [n]; rw [←mul_assoc]; exact hq
  have hC : C<Exp.exp (121*n) := by
    dsimp [C]
    exact Mixed121Temporal.source_word_bound q n (v 1) (v 2) hqexp (hv 1)
  refine ⟨N,w,hN,hq,hJ,hle,hw,hv5,hcarry,?_⟩
  by_contra hr
  have hr0 : 0<E%121 := pos_iff_ne_zero.mpr hr
  have hchoose := choose_two_ordinary N ((E/121)%n) hN
  change ((cyc n 2194 ((E/121)%n))%8801≠1063 ∧ (cyc n 2194 ((E/121)%n))%8801≠1064) ∨
    ((cyc n 3295 ((E/121)%n))%8801≠1063 ∧ (cyc n 3295 ((E/121)%n))%8801≠1064) at hchoose
  rw [←hp1,←hp2] at hchoose
  rcases hchoose with hp | hp
  · let j := cyc n (cyc n 2195 1) ((E/121)%n)
    have hb : dig 121 C j≤1 := hbool j (cyc_lt hn _ _) hp.1
    have hp' : (cyc n j 1)%8801≠1063 := previous_ordinary N j hN hp.2
    have hbprev : dig 121 C (cyc n j 1)≤1 := hbool _ (cyc_lt hn _ _) hp'
    exact conflict n C E (v 1)
      (fun j : Aligned (Fin 943) (Fin 44) => (alignedCoeff selectors copies j:V))
      bandOffsets hn hC hcarry 2195 ht1 aligned_room hr0 hpar1 hb hbprev
  · let j := cyc n (cyc n 3296 1) ((E/121)%n)
    have hb : dig 121 C j≤1 := hbool j (cyc_lt hn _ _) hp.1
    have hp' : (cyc n j 1)%8801≠1063 := previous_ordinary N j hN hp.2
    have hbprev : dig 121 C (cyc n j 1)≤1 := hbool _ (cyc_lt hn _ _) hp'
    exact conflict n C E (v 1)
      (fun j : Aligned (Fin 943) (Fin 44) => (alignedCoeff selectors copies j:V))
      bandOffsets hn hC hcarry 3296 ht2 aligned_room hr0 hpar2 hb hbprev

theorem graph_cell_shift (v : Fin 12 → V) (hv : ∀ j, 0 < v j)
    (hz : CompactLeafFacts.LeafFacts Mixed121Ports.ports v) :
    let p := Mixed121Ports.ports
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let C : V := q-v 1-v 2
    let a := coefficient (fun j : Aligned (Fin 943) (Fin 44) => (alignedCoeff selectors copies j:V))
    ∃ N w s : V, 0<N ∧ q=Exp.exp ((121*8801)*N) ∧ v 0=rep (121*8801) N ∧
      (121*8801)*N≤R ∧ w=Exp.exp (R-(121*8801)*N) ∧ v 5=q*w ∧
      let E := R-121*(8801*N)
      let T := Mixed121Temporal.temporalWord (8801*N) E C
      let X := word 121 (8801*N) C bandOffsets T
      CarryInput 121 (8801*N) (v 1) 1 (cap (ι:=Aligned (Fin 943) (Fin 44)) 121) a X ∧
      E%121=0 ∧ s<N ∧ (E/121)%(8801*N)=8801*s := by
  obtain ⟨N,w,hN,hq,hJ,hle,hw,hv5,hcarry,haligned⟩ := graph_aligned_shift v hv hz
  obtain ⟨N',w',hN',hq',hJ',hle',hw',hv5',hcarry',h1095,h1096,hpar1,hpar2⟩ :=
    Mixed121AnchorParity.graph_anchor_parity v hv hz
  obtain ⟨N'',w'',hN'',hq'',hJ'',hle'',hw'',hv5'',hcarry'',h0'',hzero,hbool⟩ :=
    Mixed121Clean.graph_support_carry v hv hz
  obtain ⟨N''',w''',hN''',hq''',hJ''',hle''',hw''',hv5''',hpos''',hbound''',hband''',hTlt''',
    hTcap''',h0''',hcap⟩ := Mixed121Temporal.graph_temporal v hv hz
  dsimp only at *
  have hNN1 : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((121*8801):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
  have hNN2 : N''=N := by
    apply mul_left_cancel₀ (by norm_num : ((121*8801):V)≠0)
    exact exp_inj (hq''.symm.trans hq)
  subst N''
  have hNN3 : N'''=N := by
    apply mul_left_cancel₀ (by norm_num : ((121*8801):V)≠0)
    exact exp_inj (hq'''.symm.trans hq)
  subst N'''
  let p := Mixed121Ports.ports
  let q : V := 1+v 0*(p 0:V)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  let C : V := q-v 1-v 2
  let n : V := 8801*N
  let E : V := R-121*n
  let D : V := (E/121)%n
  have hn : 0<n := mul_pos (by norm_num) hN
  have hnge : (8801:V)≤n := by
    have h := mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hN) (by norm_num : (0:V)≤8801)
    simpa only [n,mul_one] using h
  have ht1 : (2195:V)<n := lt_of_lt_of_le (by norm_num) hnge
  have ht2 : (3296:V)<n := lt_of_lt_of_le (by norm_num) hnge
  have hqexp : q=Exp.exp (121*n) := by dsimp [n]; rw [←mul_assoc]; exact hq
  have hC : C<Exp.exp (121*n) := by
    dsimp [C]
    exact Mixed121Temporal.source_word_bound q n (v 1) (v 2) hqexp (hv 1)
  have hnz1 := anchor_nonzero n C E (v 1)
    (fun j : Aligned (Fin 943) (Fin 44) => (alignedCoeff selectors copies j:V))
    bandOffsets hn hC hcap hcarry 2195 ht1 aligned_room haligned hpar1
  have hnz2 := anchor_nonzero n C E (v 1)
    (fun j : Aligned (Fin 943) (Fin 44) => (alignedCoeff selectors copies j:V))
    bandOffsets hn hC hcap hcarry 3296 ht2 aligned_room haligned hpar2
  have hb1 : Bad ((cyc n 2195 D)%8801) := by
    by_contra hb
    exact hnz1 (hzero _ (cyc_lt hn _ _) hb)
  have hb2 : Bad ((cyc n 3296 D)%8801) := by
    by_contra hb
    exact hnz2 (hzero _ (cyc_lt hn _ _) hb)
  have hp1 := CyclicAnyPhase.cyc_period 8801 N 2195 D (by norm_num) hN
  have hp2 := CyclicAnyPhase.cyc_period 8801 N 3296 D (by norm_num) hN
  rw [mod_eq_self_of_lt (by norm_num : (2195:V)<8801)] at hp1
  rw [mod_eq_self_of_lt (by norm_num : (3296:V)<8801)] at hp2
  rw [hp1] at hb1
  rw [hp2] at hb2
  have hd0 : D%8801=0 := model_zero D hb1 hb2
  have hdlt : D<n := mod_lt _ hn
  have hslt : D/8801<N := by
    apply div_lt_of_lt_mul
    simpa only [n,mul_comm] using hdlt
  have hD : D=8801*(D/8801) := by
    have h := div_add_mod D 8801
    rw [hd0,add_zero] at h
    exact h.symm
  exact ⟨N,w,D/8801,hN,hq,hJ,hle,hw,hv5,hcarry,haligned,hslt,hD⟩
end Mixed121Shift
#print axioms Mixed121Shift.nat_choice
#print axioms Mixed121Shift.nat_zero
#print axioms Mixed121Shift.choose_two_ordinary
#print axioms Mixed121Shift.model_zero
#print axioms Mixed121Shift.conflict
#print axioms Mixed121Shift.anchor_nonzero
#print axioms Mixed121Shift.graph_aligned_shift
#print axioms Mixed121Shift.graph_cell_shift
