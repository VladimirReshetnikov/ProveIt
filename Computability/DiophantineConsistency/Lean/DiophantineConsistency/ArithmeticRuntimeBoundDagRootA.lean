import DiophantineConsistency.ArithmeticRuntimeBoundDagMacrosD

/-! # Bounded DagPerm root, part A: equality test and command branches

Bounded twins of the equality test (`eqU_pos`, `eqU_zero`, `cancel463`, `eqA_le`,
`eqA_lt`, `eqZ`, `eqR_zero`, `eqR`, `ifeq_eq`, `ifeq_ne`), of `loop214`,
`ifeq_par1`, `ifeq_clear`, `mp_branch`, `nip_branch` and `nip_halt` of
`ArithmeticDagRootPerm222`, mirroring the accepted proof bodies.
No existing statement is changed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.ArithmeticRuntimeBoundDagMacros
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC ArithmeticCantor ArithmeticDagRun RMDag
open ArithmeticDagMacrosPerm222
open ArithmeticControlFile (writeValue)
open ArithmeticDagLoops (one_le_of_pos)
open ArithmeticRuntimeBoundDagRun ArithmeticEnumBoundTower
open ArithmeticCode254 (wim wel wal weq tagged)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local instance write_definable4 : 𝚺₁-Function₃[V] writeValue :=
  ArithmeticControlFile.write_defined.to_definable

theorem sz_mono {a b : AS V} (h0 : a.np ≤ b.np) (h1 : a.tw ≤ b.tw) (h2 : a.ws ≤ b.ws)
    (h3 : a.ac ≤ b.ac) (h4 : a.p1 ≤ b.p1) (h5 : a.p2 ≤ b.p2) (h6 : a.s1 ≤ b.s1) (h7 : a.s2 ≤ b.s2)
    (h8 : a.pl ≤ b.pl) : sz a ≤ sz b := by
  unfold sz
  exact _root_.add_le_add h0 (_root_.add_le_add h1 (_root_.add_le_add h2 (_root_.add_le_add h3
    (_root_.add_le_add h4 (_root_.add_le_add h5 (_root_.add_le_add h6 (_root_.add_le_add h7 h8)))))))

theorem eqU_posB (st : AS V) (b : V) (hb : st.s1 = b+1) :
    IRB (.node 462) (enc st) (.cont 1) (enc {st with s1 := b}) (1 + 1) :=
  RB.cont_car (n := 462) rfl (RB.cont_cdr (n := 461) (k := 0) rfl
    (decPos_ASB 6 (by omega) st b hb) (RB.contS 1 _))

theorem eqU_zeroB (st : AS V) (hb : st.s1 = 0) :
    IRB (.node 462) (enc st) (.brk 1) (enc st) (1 + 1) :=
  RB.brk_cdr (n := 462) (k := 0) rfl
    (RB.skip (n := 461) rfl (decZero_ASB 6 (by omega) st hb)) (RB.brkS 0 _)

theorem cancel463B (st : AS V) (N : V) (hN1 : N ≤ st.s1) (hN2 : N ≤ st.p2)
    {X : Exit} {y C : V}
    (hfin : IRB (.node 463) (enc {st with s1 := st.s1-N, p2 := st.p2-N}) X y C) :
    IRB (.node 463) (enc st) X y (N * (1 + (1 + 1)) + C) := by
  let Gr : V → AS V := fun t => {st with s1 := st.s1-t, p2 := st.p2-t}
  let Hr : V → AS V := fun t => {st with s1 := st.s1-t, p2 := st.p2-t-1}
  let G : V → V := fun t => writeValue 7 (st.p2-t) (writeValue 8 (st.s1-t) (enc st))
  have hG : ∀ t, G t = enc (Gr t) := by
    intro t
    show lupd (lupd (enc st) 6 (st.s1-t)) 5 (st.p2-t) = enc (Gr t)
    rw [lupd_enc _ 6 (by omega), lupd_enc _ 5 (by omega)]; rfl
  haveI : 𝚺₁-Function₁[V] G := write2_definable _ _ _ _ _ (sub_definable _) (sub_definable _)
  have hpass : ∀ t, t < N → IRB (.decnz 5) (G t) .normal (enc (Hr t)) 1 ∧
      IRB (.node 462) (enc (Hr t)) (.cont 1) (G (t+1)) (1 + 1) := by
    intro t ht
    have h1 := tsub_pos_of_lt (lt_of_lt_of_le ht hN1)
    have h2 := tsub_pos_of_lt (lt_of_lt_of_le ht hN2)
    constructor
    · rw [hG]
      exact decPos_ASB 5 (by omega) (Gr t) (st.p2-t-1)
        (tsub_add_cancel_of_le (one_le_of_pos h2)).symm
    · rw [hG]
      have hh := eqU_posB (Hr t) (st.s1-t-1)
        (tsub_add_cancel_of_le (one_le_of_pos h1)).symm
      simpa only [Hr, Gr, tsub_tsub] using hh
  have hh := RB.iterate (n := 463) rfl G (fun t => enc (Hr t)) N _ _ hpass (by rw [hG]; exact hfin)
  simpa only [hG, Gr, tsub_zero] using hh

variable {j : V} {L : ℕ} (hL : 2 ≤ L)
include hL

theorem eqA_leT (st : AS V) (h : st.p2 ≤ st.s1) (hs : sz st ≤ tower j L) :
    RnB (.node 463) st {st with s1 := st.s1-st.p2, p2 := 0} (tower j (L+1)) := by
  have hh := cancel463B st st.p2 h le_rfl (by
    simpa only [tsub_self] using RB.skip (n := 463) rfl
      (decZero_ASB 5 (by omega) {st with s1 := st.s1-st.p2, p2 := 0} rfl))
  exact irunB_mono hh (lin_le hL (le_trans (field_le_sz st 5) hs) (by norm_num))

theorem eqA_ltT (st : AS V) (h : st.s1 < st.p2) (hs : sz st ≤ tower j L) :
    IRB (.node 463) (enc st) (.brk 1) (enc {st with s1 := 0, p2 := st.p2-st.s1-1})
      (tower j (L+1)) := by
  have hh := cancel463B st st.s1 le_rfl (le_of_lt h) (by
    simp only [tsub_self]
    exact RB.brk_cdr (n := 463) (k := 0) rfl
      (decPos_ASB 5 (by omega) {st with s1 := 0, p2 := st.p2-st.s1} (st.p2-st.s1-1)
        (tsub_add_cancel_of_le (one_le_of_pos (tsub_pos_of_lt h))).symm)
      (eqU_zeroB _ rfl))
  exact irunB_mono hh (lin_le' hL (le_trans (field_le_sz st 6) hs) (by norm_num) (by norm_num))

theorem eqZT (st : AS V) (hs : sz st ≤ tower j L) :
    RnB (.node 465) st {st with p2 := 0} (tower j (L+1)) := by
  have h := clearB (p := DagPerm.dagPerm) R.run_zero R.run_add R.run_one
    ArithmeticDagControlPerm222.spec (n := 465) (r := 5) rfl (enc st)
  rw [lupd_enc _ 5 (by omega), lreg_enc _ 5 (by omega)] at h
  exact irunB_mono h (lin_le hL (le_trans (field_le_sz st 5) hs) (by norm_num))

theorem eqR_zeroT (st : AS V) (hp : st.p2 = 0) (hs : sz st ≤ tower j L) :
    IRB (.node 466) (enc st) (.brk 1) (enc {st with s1 := 0, p2 := 0}) (tower j (L+1)) := by
  let Gr : V → AS V := fun t => {st with s1 := st.s1-t, p2 := 0}
  let G : V → V := fun t => writeValue 7 0 (writeValue 8 (st.s1-t) (enc st))
  have hG : ∀ t, G t = enc (Gr t) := by
    intro t
    show lupd (lupd (enc st) 6 (st.s1-t)) 5 0 = enc (Gr t)
    rw [lupd_enc _ 6 (by omega), lupd_enc _ 5 (by omega)]; rfl
  haveI : 𝚺₁-Function₁[V] G := write2_definable _ _ _ _ _ (by definability) (sub_definable _)
  have hZ : ∀ u : AS V, u.p2 = 0 → RnB (.node 465) u {u with p2 := 0} (0 * (1 + 1) + 1) := by
    intro u hu
    have he : ({u with p2 := 0} : AS V) = u := by cases u; simp_all
    simpa only [zero_mul, zero_add, he] using
      RB.skip (n := 465) rfl (decZero_ASB 5 (by omega) u hu)
  have hpass : ∀ t, t < st.s1 → IRB (.node 465) (G t) .normal (G t) (0 * (1 + 1) + 1) ∧
      IRB (.node 462) (G t) (.cont 1) (G (t+1)) (1 + 1) := by
    intro t ht
    simp only [hG]
    refine ⟨hZ (Gr t) rfl, ?_⟩
    have hh := eqU_posB (Gr t) (st.s1-t-1)
      (tsub_add_cancel_of_le (one_le_of_pos (tsub_pos_of_lt ht))).symm
    simpa only [Gr, tsub_tsub] using hh
  have hfin : IRB (.node 466) (G st.s1) (.brk 1) (enc {st with s1 := 0, p2 := 0})
      (0 * (1 + 1) + 1 + (1 + 1)) := by
    rw [hG]; simp only [Gr, tsub_self]
    exact RB.brk_cdr (n := 466) (k := 0) rfl (hZ _ rfl) (eqU_zeroB _ rfl)
  have hh := RB.iterate (n := 466) rfl G G st.s1 _ _ hpass hfin
  have he : G 0 = enc st := by
    rw [hG]; congr 1; cases st; simp_all [Gr]
  rw [he] at hh
  exact irunB_mono hh (lin_le' hL (le_trans (field_le_sz st 6) hs) (by norm_num) (by norm_num))

theorem eqRT (st : AS V) (hs : sz st ≤ tower j L) :
    IRB (.node 466) (enc st) (.brk 1) (enc {st with s1 := 0, p2 := 0}) (tower j (L+3)) := by
  have h1 : tower j (L+1) + (1 + 1) ≤ tower j (L+2) :=
    add_le_tower_of (c := L+1) (by omega) le_rfl (by omega) le_rfl
      (numeral_le_tower j hL (by norm_num))
  by_cases hz : st.s1 = 0
  · have hh := RB.brk_cdr (n := 466) (k := 0) rfl (eqZT hL st hs) (eqU_zeroB _ hz)
    have hh' : IRB (.node 466) (enc st) (.brk 1) (enc {st with s1 := 0, p2 := 0})
        (tower j (L+1) + (1 + 1)) := by simpa only [← hz] using hh
    exact irunB_mono hh' (le_tower_of h1 (by omega))
  · have hp := one_le_of_pos (lt_of_le_of_ne (Arithmetic.zero_le _) (Ne.symm hz))
    have hs' : sz ({ ({st with p2 := 0} : AS V) with s1 := st.s1 - 1 } : AS V) ≤ tower j L :=
      le_trans (sz_mono (b := st) le_rfl le_rfl le_rfl le_rfl le_rfl (Arithmetic.zero_le _) tsub_le_self
        le_rfl le_rfl) hs
    have hh := RB.restart (n := 466) rfl (eqZT hL st hs)
      (eqU_posB _ (st.s1-1) (tsub_add_cancel_of_le hp).symm) (eqR_zeroT hL _ rfl hs')
    exact irunB_mono hh (add_le_tower_of (c := L+2) (by omega) le_rfl (by omega) h1 le_rfl)

theorem ifeq_eqT (st : AS V) (h : st.s1 = st.p2) (hs : sz st ≤ tower j L) :
    RnB (.node 123) st {st with s1 := 0, p2 := 0} (tower j (L+2)) := by
  have ha := eqA_leT hL st (le_of_eq h.symm) hs
  rw [h, tsub_self] at ha
  exact irunB_mono (RB.skip (n := 123) rfl (RB.brk_cdr (n := 464) (k := 0) rfl ha
    (decZero_ASB 6 (by omega) _ rfl))) (succ_le_tower (by omega) le_rfl)

theorem ifeq_neT (st : AS V) (h : st.s1 ≠ st.p2) (hs : sz st ≤ tower j L) :
    IRB (.node 123) (enc st) (.brk 1) (enc {st with s1 := 0, p2 := 0}) (tower j (L+4)) := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have hs' : sz ({st with s1 := 0, p2 := st.p2 - st.s1 - 1} : AS V) ≤ tower j L :=
      le_trans (sz_mono (b := st) le_rfl le_rfl le_rfl le_rfl le_rfl (le_trans tsub_le_self tsub_le_self)
        (Arithmetic.zero_le _) le_rfl le_rfl) hs
    have hh := RB.brk_cdr (n := 123) (k := 0) rfl
      (RB.skip (n := 464) rfl (eqA_ltT hL st hlt hs)) (eqRT hL _ hs')
    exact irunB_mono hh (add_le_tower_of (c := L+3) (by omega) (by omega) le_rfl le_rfl le_rfl)
  · have hdec := decPos_ASB 6 (by omega) {st with s1 := st.s1-st.p2, p2 := 0}
      (st.s1-st.p2-1) (tsub_add_cancel_of_le (one_le_of_pos (tsub_pos_of_lt hgt))).symm
    have hs' : sz (updAS ({st with s1 := st.s1-st.p2, p2 := 0} : AS V) 6 (st.s1-st.p2-1)) ≤
        tower j L :=
      le_trans (sz_mono (b := st) le_rfl le_rfl le_rfl le_rfl le_rfl (Arithmetic.zero_le _)
        (le_trans tsub_le_self tsub_le_self) le_rfl le_rfl) hs
    have hh := RB.brk_cdr (n := 123) (k := 0) rfl
      (RB.seq (n := 464) rfl (eqA_leT hL st (le_of_lt hgt) hs) hdec) (eqRT hL _ hs')
    refine irunB_mono hh ?_
    have h1 : tower j (L+1) + 1 ≤ tower j (L+2) := succ_le_tower (by omega) le_rfl
    exact add_le_tower_of (c := L+3) (by omega) (by omega) le_rfl h1 le_rfl

theorem loop214M (st : AS V) (hs : sz st ≤ tower j L) : Mac (.node 214) st {st with tw := 0} j L 1 := by
  have h := clearB (p := DagPerm.dagPerm) R.run_zero R.run_add R.run_one
    ArithmeticDagControlPerm222.spec (n := 214) (r := 1) rfl (enc st)
  rw [lupd_enc _ 1 (by omega), lreg_enc _ 1 (by omega)] at h
  exact ⟨irunB_mono h (lin_le hL (le_trans (field_le_sz st 1) hs) (by norm_num)),
    le_tower_of (le_trans (sz_mono (b := st) le_rfl (Arithmetic.zero_le _) le_rfl le_rfl le_rfl le_rfl
      le_rfl le_rfl le_rfl) hs) (by omega)⟩

theorem ifeq_eqM (st : AS V) (h : st.s1 = st.p2) (hs : sz st ≤ tower j L) :
    Mac (.node 123) st {st with s1 := 0, p2 := 0} j L 2 :=
  ⟨ifeq_eqT hL st h hs, le_tower_of (le_trans (sz_mono (b := st) le_rfl le_rfl le_rfl le_rfl le_rfl
    (Arithmetic.zero_le _) (Arithmetic.zero_le _) le_rfl le_rfl) hs) (by omega)⟩

theorem ifeq_skipM {n : Nat} {e : RMDag.Edge}
    (hne : DagPerm.dagPerm.nodes n = (.node 123, e)) (st : AS V) (h : st.s1 ≠ st.p2)
    (hs : sz st ≤ tower j L) : Mac (.node n) st {st with s1 := 0, p2 := 0} j L 4 :=
  ⟨RB.skip hne (ifeq_neT hL st h hs), le_tower_of (le_trans (sz_mono (b := st) le_rfl le_rfl le_rfl le_rfl
    le_rfl (Arithmetic.zero_le _) (Arithmetic.zero_le _) le_rfl le_rfl) hs) (by omega)⟩

/-- `ifeq_par1` (node 130). -/
theorem ifeq_par1M (st : AS V) (h2 : st.s2 = 0) (hs : sz st ≤ tower j L) :
    Mac (.node 130) st (if st.s1 = st.p2
      then { st with s1 := 0, p2 := 0, tw := st.p1, ws := cantor st.tw st.ws }
      else { st with s1 := 0, p2 := 0 }) j L 27 := by
  by_cases h : st.s1 = st.p2
  · rw [if_pos h]
    have m1 := ifeq_eqM hL st h hs
    have m2 := par1M (L := L+2) (by omega) _ (by exact ⟨rfl, h2⟩) m1.2
    exact (Mac.seq (n := 130) rfl hL m1 m2).mono (by omega)
  · rw [if_neg h]
    exact (ifeq_skipM hL rfl st h hs).mono (by omega)

/-- `ifeq_clear` (node 131). -/
theorem ifeq_clearM (st : AS V) (hs : sz st ≤ tower j L) :
    Mac (.node 131) st (if st.s1 = st.p2
      then { st with s1 := 0, p2 := 0, tw := 0 } else { st with s1 := 0, p2 := 0 }) j L 5 := by
  by_cases h : st.s1 = st.p2
  · rw [if_pos h]
    have m1 := ifeq_eqM hL st h hs
    have m2 := loop214M (L := L+2) (by omega) _ m1.2
    exact (Mac.seq (n := 131) rfl hL m1 m2).mono (by omega)
  · rw [if_neg h]
    exact (ifeq_skipM hL rfl st h hs).mono (by omega)

/-- The MP branch (node 150). -/
theorem mp_branchM (st : AS V) (hc : Clean st) (hs : sz st ≤ tower j L) :
    Mac (.node 150) st (if wim st.tw st.p1 = st.p2
      then { st with tw := st.p1, ws := cantor 0 st.ws, p2 := 0 }
      else { st with tw := 0, p2 := 0 }) j L 87 := by
  have m1 := par1M hL st hc hs
  have m2 := consM (L := L+24) (by omega) _ (by exact hc) m1.2
  have m3 := loop216M (L := L+(24+32+1)) (by omega) _ (le_tower_of m2.2 (by omega))
  have m4 := ifeq_par1M (L := L+(24+32+1)+1) (by omega) _ (by exact hc.2) m3.2
  have := Mac.seq (n := 150) rfl hL (Mac.seq (n := 161) rfl hL m1 m2)
    (Mac.seq (n := 151) rfl (by omega) m3 m4)
  refine (this.eq ?_).mono (by omega)
  clear this m1 m2 m3 m4 hs
  obtain ⟨c1, c2⟩ := hc
  cases st; simp only at c1 c2; subst c1; subst c2
  simp only [first_cantor, second_cantor, zero_add]

/-- The NIP branch (node 152) when the cache is not the falsity code. -/
theorem nip_branchM (st : AS V) (hc : Clean st) (hh : st.p2 ≠ 1) (hs : sz st ≤ tower j L) :
    Mac (.node 152) st { st with p2 := first st.ws, ws := second st.ws } j L 25 := by
  have m1 := incM hL 6 (by omega) st hs (by simp only [sz, updAS, field]; ring)
  have hne : (updAS st 6 (field st 6 + 1)).s1 ≠ (updAS st 6 (field st 6 + 1)).p2 := by
    show st.s1 + 1 ≠ st.p2
    rw [hc.1, zero_add]
    exact fun h => hh h.symm
  have m2 := ifeq_skipM (n := 132) (L := L+1) (by omega) rfl _ hne m1.2
  have m3 := pop_p2M (L := L+1+4) (by omega) _ (by exact ⟨rfl, hc.2⟩) m2.2
  have := Mac.seq (n := 152) rfl hL m1 (Mac.seq (n := 153) rfl (by omega) m2 m3)
  refine (this.eq ?_).mono (by omega)
  clear this m1 m2 m3 hs hne
  obtain ⟨c1, c2⟩ := hc
  cases st; simp only at c1 c2; subst c1; subst c2; simp [updAS, field]

/-- The NIP branch halts on the falsity code. -/
theorem nip_haltB (st : AS V) (hc : Clean st) (hh : st.p2 = 1) (hs : sz st ≤ tower j L) :
    ∃ y, IRB (.node 152) (enc st) .halt y (tower j (L+4)) := by
  have hinc := inc_ASB 6 (by omega) st
  have hs1 : sz (updAS st 6 (field st 6 + 1)) ≤ tower j (L+1) :=
    le_trans (le_of_eq (by simp only [sz, updAS, field]; ring : _ = sz st + 1)) (succ_le_tower hL hs)
  have heq : (updAS st 6 (field st 6 + 1)).s1 = (updAS st 6 (field st 6 + 1)).p2 := by
    show st.s1 + 1 = st.p2
    rw [hc.1, zero_add, hh]
  have h132 := RB.halt_cdr (n := 132) rfl (ifeq_eqT (L := L+1) (by omega) _ heq hs1) (RB.halt _)
  have h153 := RB.halt_car (n := 153) rfl h132
  refine ⟨_, irunB_mono (RB.halt_cdr (n := 152) rfl hinc h153) ?_⟩
  calc (1 : V) + (tower j (L+1+2) + 1) = 2 + tower j (L+3) := by ring
    _ ≤ tower j (L+4) := const_add_le (by omega) le_rfl (by norm_num)

end DiophantineConsistency.ArithmeticRuntimeBoundDagMacros
