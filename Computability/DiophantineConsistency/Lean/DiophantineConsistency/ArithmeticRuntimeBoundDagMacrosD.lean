import DiophantineConsistency.ArithmeticRuntimeBoundDagMacrosC

/-! # Bounded DagPerm macros, part D: counters, fetch, stack and formula macros

Bounded twins of `add2..add4`, `loop117`, `loop136`, `fetch_pos`, `fetch_zero`,
the pushes `pushwff`, `v1`, `par1..par3`, the constructors `cons`, `wel_m`,
`wal_m`, `weq_m`, `wn_m`, `wa_m`, `wex_m`, and the reads `read108`, `read_ac`,
`read_p1`, `read_p2`, `pop_p2`, `pop110` of `ArithmeticDagMacrosPerm222`. The
compositions are the accepted ones; `Mac.seq` adds the tower offsets.
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

local instance write_definable''' : 𝚺₁-Function₃[V] writeValue :=
  ArithmeticControlFile.write_defined.to_definable

theorem irb_eq {e : RMDag.Edge} {x : V} {X : Exit} {s1 s2 : AS V} {B : V}
    (h : IRB e x X (enc s1) B) (he : s1 = s2) : IRB e x X (enc s2) B := he ▸ h

/-! ## Counter increments -/

theorem add2B (st : AS V) : IRB (.node 159) (enc st) .normal (enc { st with tw := st.tw + 2 }) (1 + 1) :=
  irb_eq (RB.seq (n := 159) rfl (inc_ASB 1 (by omega) st) (inc_ASB 1 (by omega) _)) (by
    cases st; simp only [updAS, field]; congr 1; ring)

theorem add3B (st : AS V) :
    IRB (.node 157) (enc st) .normal (enc { st with tw := st.tw + 3 }) (1 + 1 + 1) :=
  irb_eq (RB.seq (n := 157) rfl (add2B st) (inc_ASB 1 (by omega) _)) (by
    cases st; simp only [updAS, field]; congr 1; ring)

theorem add4B (st : AS V) :
    IRB (.node 156) (enc st) .normal (enc { st with tw := st.tw + 4 }) (1 + 1 + 1 + 1) :=
  irb_eq (RB.seq (n := 156) rfl (add3B st) (inc_ASB 1 (by omega) _)) (by
    cases st; simp only [updAS, field]; congr 1; ring)

variable {j : V} {L : ℕ} (hL : 2 ≤ L)
include hL

theorem sz_add_const_le {st st' : AS V} {c : V} (hs : sz st ≤ tower j L)
    (h : sz st' = sz st + c) (hc : c ≤ 16) : sz st' ≤ tower j (L+1) := by
  rw [h]; exact add_le_tower' hL hs (le_trans hc (sixteen_le_tower_of j hL))

theorem add2M (st : AS V) (hs : sz st ≤ tower j L) : Mac (.node 159) st { st with tw := st.tw + 2 } j L 1 :=
  ⟨irunB_mono (add2B st) (numeral_le_tower j (by omega) (by norm_num)),
    sz_add_const_le hL hs (c := 2) (by simp only [sz]; ring) (by norm_num)⟩

theorem add3M (st : AS V) (hs : sz st ≤ tower j L) : Mac (.node 157) st { st with tw := st.tw + 3 } j L 1 :=
  ⟨irunB_mono (add3B st) (numeral_le_tower j (by omega) (by norm_num)),
    sz_add_const_le hL hs (c := 3) (by simp only [sz]; ring) (by norm_num)⟩

theorem incM (r : Nat) (hr : r < 9) (st : AS V) (hs : sz st ≤ tower j L)
    (hsz : sz (updAS st r (field st r + 1)) = sz st + 1) :
    Mac (.inc r) st (updAS st r (field st r + 1)) j L 1 :=
  Mac.inc r hr hL hs (le_of_eq hsz)

/-- `loop117` (`tw += 4·s2`). -/
theorem loop117M (st : AS V) (hs : sz st ≤ tower j L) :
    Mac (.node 117) st { st with tw := st.tw + 4 * st.s2, s2 := 0 } j L 1 := by
  let Gr : V → AS V := fun t => { st with tw := st.tw + 4 * t, s2 := st.s2 - t }
  let x0 : V := enc st
  let G : V → V := fun t =>
    writeValue ((5 : Nat) : V) (st.s2 - t) (writeValue ((2 : Nat) : V) (st.tw + 4 * t) x0)
  have hG : ∀ t, G t = enc (Gr t) := by
    intro t
    show lupd (lupd (enc st) 1 (st.tw + 4 * t)) 7 (st.s2 - t) = enc (Gr t)
    rw [lupd_enc _ 1 (by omega), lupd_enc _ 7 (by omega)]
    rfl
  haveI : 𝚺₁-Function₁[V] G :=
    write2_definable _ _ (fun t => st.s2 - t) (fun t => st.tw + 4 * t) x0
      (sub_definable st.s2) (lin_definable st.tw 4)
  have hpass : ∀ t, t < st.s2 →
      IRB (.decnz 7) (G t) .normal (enc { (Gr t) with s2 := st.s2 - t - 1 }) 1 ∧
      IRB (.node 118) (enc { (Gr t) with s2 := st.s2 - t - 1 }) (.cont 1) (G (t+1))
        (1 + 1 + 1 + 1 + 1) := by
    intro t ht
    refine ⟨?_, ?_⟩
    · rw [hG]
      exact decPos_ASB 7 (by omega) (Gr t) (st.s2 - t - 1)
        (tsub_add_cancel_of_le (one_le_of_pos (tsub_pos_of_lt ht))).symm
    · rw [hG]
      have h := RB.cont_cdr (n := 118) (k := 0) rfl (add4B { (Gr t) with s2 := st.s2 - t - 1 })
        (RB.contS 1 _)
      have e : ({ ({ (Gr t) with s2 := st.s2 - t - 1 } : AS V) with
          tw := ({ (Gr t) with s2 := st.s2 - t - 1 } : AS V).tw + 4 } : AS V) = Gr (t+1) := by
        simp only [Gr, tsub_tsub]
        congr 1
        ring
      rwa [e] at h
  have hfin : IRB (.node 117) (G st.s2) .normal (G st.s2) 1 := by
    rw [hG]
    exact RB.skip (n := 117) rfl (decZero_ASB 7 (by omega) (Gr st.s2) (by simp only [Gr, tsub_self]; rfl))
  have hit := RB.iterate (n := 117) rfl G (fun t => enc { (Gr t) with s2 := st.s2 - t - 1 }) st.s2
    _ _ hpass hfin
  have hG0 : G 0 = enc st := by
    rw [hG]
    congr 1
    simp only [Gr, mul_zero, add_zero, tsub_zero]
  rw [hG0, hG] at hit
  have hres : RnB (.node 117) st { st with tw := st.tw + 4 * st.s2, s2 := 0 }
      (st.s2 * (1 + (1 + 1 + 1 + 1 + 1)) + 1) := by
    simpa only [Gr, tsub_self] using hit
  exact ⟨irunB_mono hres (lin_le hL (le_trans (field_le_sz st 7) hs) (by norm_num)),
    sz_add_mul_le hL hs (c := 3) (x := st.s2) (by simp only [sz]; ring) (field_le_sz st 7)
      (by norm_num)⟩

/-- `loop136` (`np += s1 + 1`). -/
theorem loop136M (st : AS V) (hs : sz st ≤ tower j L) :
    Mac (.node 136) st { st with np := st.np + st.s1 + 1, s1 := 0 } j L 1 := by
  let Gr : V → AS V := fun t => { st with np := st.np + t, s1 := st.s1 - t }
  let Hr : V → AS V := fun t => { st with np := st.np + t + 1, s1 := st.s1 - t }
  let G : V → V := fun t =>
    writeValue ((6 : Nat) : V) (st.np + t)
      (writeValue ((8 : Nat) : V) (st.s1 - t) (enc st))
  have hG : ∀ t, G t = enc (Gr t) := by
    intro t
    show lupd (lupd (enc st) 6 (st.s1 - t)) 0 (st.np + t) = enc (Gr t)
    rw [lupd_enc _ 6 (by omega), lupd_enc _ 0 (by omega)]
    rfl
  have hadd : 𝚺₁-Function₁[V] (fun t => st.np + t) := by definability
  haveI : 𝚺₁-Function₁[V] G :=
    write2_definable _ _ _ _ (enc st) hadd (sub_definable st.s1)
  have hpass : ∀ t, t < st.s1 → IRB (.inc 0) (G t) .normal (enc (Hr t)) 1 ∧
      IRB (.node 300) (enc (Hr t)) (.cont 1) (G (t + 1)) (1 + 1) := by
    intro t ht
    rw [hG, hG]
    refine ⟨inc_ASB 0 (by omega) (Gr t), ?_⟩
    have hsub : st.s1 - t = (st.s1 - t - 1) + 1 :=
      (tsub_add_cancel_of_le (one_le_of_pos (tsub_pos_of_lt ht))).symm
    have hd := decPos_ASB 6 (by omega) (Hr t) (st.s1 - t - 1) hsub
    have h := RB.cont_cdr (n := 300) (k := 0) rfl hd (RB.contS 1 _)
    have he : updAS (Hr t) 6 (st.s1 - t - 1) = Gr (t + 1) := by
      simp only [updAS, Gr, Hr, add_assoc, tsub_tsub]
    rwa [he] at h
  have hfin : IRB (.node 136) (G st.s1) .normal
      (enc { st with np := st.np + st.s1 + 1, s1 := 0 }) (1 + 1) := by
    rw [hG]
    have hi := inc_ASB 0 (by omega) (Gr st.s1)
    have hz := decZero_ASB 6 (by omega) (Hr st.s1) (by simp [Hr, field])
    have h := RB.seq (n := 136) rfl hi (RB.skip (n := 300) rfl hz)
    simpa only [Hr, tsub_self] using h
  have h := RB.iterate (n := 136) rfl G (fun t => enc (Hr t)) st.s1 _ _ hpass hfin
  rw [hG] at h
  have hres : RnB (.node 136) st { st with np := st.np + st.s1 + 1, s1 := 0 }
      (st.s1 * (1 + (1 + 1)) + (1 + 1)) := by
    simpa only [Gr, add_zero, tsub_zero] using h
  exact ⟨irunB_mono hres (lin_le' hL (le_trans (field_le_sz st 6) hs) (by norm_num) (by norm_num)),
    sz_add_const_le hL hs (c := 1) (by simp only [sz]; ring) (by norm_num)⟩

theorem fetch_posM (st : AS V) (v : V) (hv : st.pl = v + 1) (hs : sz st ≤ tower j L) :
    Mac (.node 133) st { st with pl := v } j L 1 := by
  have hdec := decPos_ASB 8 (by omega) st v hv
  have h134 := RB.brk_cdr (n := 134) (k := 0) rfl hdec (RB.brkS 0 _)
  refine ⟨irunB_mono (RB.skip (n := 133) rfl h134) (numeral_le_tower j (by omega) (by norm_num)), ?_⟩
  refine le_trans (sz_le_of_split (st.np + st.tw + st.ws + st.ac + st.p1 + st.p2 + st.s1 + st.s2)
    v st.pl (sz st) (by simp only [sz]; ring) (by simp only [sz]; ring) ?_) (add_le_tower' hL hs hs)
  exact le_trans (show v ≤ st.pl by rw [hv]; exact le_self_add) (field_le_sz st 8)

theorem fetch_zeroM (st : AS V) (hpl : st.pl = 0) (h1 : st.s1 = 0) (hs : sz st ≤ tower j L) :
    Mac (.node 133) st { st with pl := st.np, np := st.np + 1 } j L 5 := by
  have h134 : Mac (.node 134) st st j L 1 :=
    ⟨irunB_mono (RB.skip (n := 134) rfl (decZero_ASB 8 (by omega) st hpl)) (one_le_tower j _),
      le_tower_of hs (by omega)⟩
  have h194 := loop194M (L := L+1) (by omega) st h134.2
  have h136 := loop136M (L := L+1+1) (by omega) _ h194.2
  have h135 := Mac.seq (n := 135) rfl (by omega) h194 h136
  have h := Mac.seq (n := 133) rfl hL h134 h135
  refine (h.eq ?_).mono (by omega)
  cases st; simp only at hpl h1; subst hpl; subst h1; simp

/-! ## Pushes -/

theorem pushwffM (st : AS V) (hc : Clean st) (hs : sz st ≤ tower j L) :
    Mac (.node 171) st { st with tw := 0, ws := cantor st.tw st.ws } j L 20 := by
  have h1 := loop216M hL st hs
  have h2 := loop217M (by omega) _ h1.2
  have h3 := pair162M (by omega) _ h2.2
  have h4 := loop212M (by omega) _ h3.2
  have h := Mac.seq (n := 171) rfl hL h1 (Mac.seq (n := 172) rfl (by omega) h2
    (Mac.seq (n := 173) rfl (by omega) h3 h4))
  refine (h.eq ?_).mono (by omega)
  obtain ⟨c1, c2⟩ := hc; cases st; simp only at c1 c2; subst c1; subst c2; simp

theorem v1M (st : AS V) (hc : Clean st) (hs : sz st ≤ tower j L) :
    Mac (.node 177) st { st with tw := 1, ws := cantor st.tw st.ws } j L 22 := by
  have h1 := pushwffM hL st hc hs
  have h2 := incM (L := L+20) (by omega) 1 (by omega) _ h1.2 (by simp only [sz, updAS, field]; ring)
  exact ((Mac.seq (n := 177) rfl hL h1 h2).eq (by simp [updAS, field])).mono (by omega)

theorem par1M (st : AS V) (hc : Clean st) (hs : sz st ≤ tower j L) :
    Mac (.node 166) st { st with tw := st.p1, ws := cantor st.tw st.ws } j L 24 := by
  have h1 := pushwffM hL st hc hs
  have h2 := loop198M (by omega) _ h1.2
  have h3 := loop205M (by omega) _ h2.2
  have h := Mac.seq (n := 166) rfl hL h1 (Mac.seq (n := 167) rfl (by omega) h2 h3)
  refine (h.eq ?_).mono (by omega)
  obtain ⟨c1, c2⟩ := hc; cases st; simp only at c1 c2; subst c1; subst c2; simp

theorem par2M (st : AS V) (hc : Clean st) (hs : sz st ≤ tower j L) :
    Mac (.node 121) st { st with tw := st.p2, ws := cantor st.tw st.ws } j L 24 := by
  have h1 := pushwffM hL st hc hs
  have h2 := loop200M (by omega) _ h1.2
  have h3 := loop207M (by omega) _ h2.2
  have h := Mac.seq (n := 121) rfl hL h1 (Mac.seq (n := 122) rfl (by omega) h2 h3)
  refine (h.eq ?_).mono (by omega)
  obtain ⟨c1, c2⟩ := hc; cases st; simp only at c1 c2; subst c1; subst c2; simp

theorem par3M (st : AS V) (hc : Clean st) (hs : sz st ≤ tower j L) :
    Mac (.node 168) st { st with tw := st.ac, ws := cantor st.tw st.ws } j L 24 := by
  have h1 := pushwffM hL st hc hs
  have h2 := loop193M (by omega) _ h1.2
  have h3 := loop201M (by omega) _ h2.2
  have h := Mac.seq (n := 168) rfl hL h1 (Mac.seq (n := 169) rfl (by omega) h2 h3)
  refine (h.eq ?_).mono (by omega)
  obtain ⟨c1, c2⟩ := hc; cases st; simp only at c1 c2; subst c1; subst c2; simp

/-! ## Constructors and reads -/

theorem pop110M (st : AS V) (hc : Clean st) (hs : sz st ≤ tower j L) :
    Mac (.node 160) st { st with ws := second st.ws, s1 := first st.ws } j L 15 := by
  have h1 := loop116M hL st hs
  have h2 := loop212M (by omega) _ h1.2
  refine ((Mac.seq (n := 160) rfl hL h1 h2).eq ?_).mono (by omega)
  obtain ⟨c1, c2⟩ := hc
  cases st; simp only at c1 c2; subst c1; subst c2
  simp [unpairAS, AS.withWSZero, cantor, triangle]

theorem consM (st : AS V) (hc : Clean st) (hs : sz st ≤ tower j L) :
    Mac (.node 119) st { st with tw := wim (first st.ws) st.tw, ws := second st.ws } j L 32 := by
  have h1 := pop110M hL st hc hs
  have h2 := pair162M (by omega) _ h1.2
  have h3 := loop117M (by omega) _ h2.2
  have h := Mac.seq (n := 119) rfl hL h1 (Mac.seq (n := 120) rfl (by omega) h2 h3)
  refine (h.eq ?_).mono (by omega)
  obtain ⟨c1, c2⟩ := hc; cases st; simp only at c1 c2; subst c1; subst c2
  simp [wim, tagged]

theorem wel_mM (st : AS V) (hc : Clean st) (hs : sz st ≤ tower j L) :
    Mac (.node 181) st { st with tw := wel (first st.ws) st.tw, ws := second st.ws } j L 34 := by
  have h1 := consM hL st hc hs
  have h2 := incM (L := L+32) (by omega) 1 (by omega) _ h1.2 (by simp only [sz, updAS, field]; ring)
  exact ((Mac.seq (n := 181) rfl hL h1 h2).eq (by simp [updAS, field, wel, wim, tagged])).mono
    (by omega)

theorem wal_mM (st : AS V) (hc : Clean st) (hs : sz st ≤ tower j L) :
    Mac (.node 180) st { st with tw := wal (first st.ws) st.tw, ws := second st.ws } j L 34 := by
  have h1 := consM hL st hc hs
  have h2 := add2M (L := L+32) (by omega) _ h1.2
  exact ((Mac.seq (n := 180) rfl hL h1 h2).eq (by simp [wal, wim, tagged])).mono (by omega)

theorem weq_mM (st : AS V) (hc : Clean st) (hs : sz st ≤ tower j L) :
    Mac (.node 182) st { st with tw := weq (first st.ws) st.tw, ws := second st.ws } j L 34 := by
  have h1 := consM hL st hc hs
  have h2 := add3M (L := L+32) (by omega) _ h1.2
  exact ((Mac.seq (n := 182) rfl hL h1 h2).eq (by simp [weq, wim, tagged])).mono (by omega)

theorem wn_mM (st : AS V) (hc : Clean st) (hs : sz st ≤ tower j L) :
    Mac (.node 218) st { st with tw := wn st.tw } j L 55 := by
  have h1 := v1M hL st hc hs
  have h2 := consM (L := L+22) (by omega) _ (by exact hc) h1.2
  exact ((Mac.seq (n := 218) rfl hL h1 h2).eq (by simp [wn])).mono (by omega)

theorem wa_mM (st : AS V) (hc : Clean st) (hs : sz st ≤ tower j L) :
    Mac (.node 178) st { st with tw := wa (first st.ws) st.tw, ws := second st.ws } j L 144 := by
  have h1 := wn_mM hL st hc hs
  have h2 := consM (L := L+55) (by omega) _ (by exact hc) h1.2
  have h3 := wn_mM (L := L+55+32) (by omega) _ (by exact hc) h2.2
  have h := Mac.seq (n := 178) rfl hL h1 (Mac.seq (n := 179) rfl (by omega) h2 h3)
  exact (h.eq (by simp [wa])).mono (by omega)

theorem wex_mM (st : AS V) (hc : Clean st) (hs : sz st ≤ tower j L) :
    Mac (.node 183) st { st with tw := wex (first st.ws) st.tw, ws := second st.ws } j L 146 := by
  have h1 := wn_mM hL st hc hs
  have h2 := wal_mM (L := L+55) (by omega) _ (by exact hc) h1.2
  have h3 := wn_mM (L := L+55+34) (by omega) _ (by exact hc) h2.2
  have h := Mac.seq (n := 183) rfl hL h1 (Mac.seq (n := 184) rfl (by omega) h2 h3)
  exact (h.eq (by simp [wex])).mono (by omega)

theorem read108M (st : AS V) (hc : Clean st) (hs : sz st ≤ tower j L) :
    Mac (.node 158) st { st with pl := second st.pl, s1 := first st.pl } j L 15 := by
  have h1 := loop115M hL st hs
  have h2 := loop209M (by omega) _ h1.2
  refine ((Mac.seq (n := 158) rfl hL h1 h2).eq ?_).mono (by omega)
  obtain ⟨c1, c2⟩ := hc
  cases st; simp only at c1 c2; subst c1; subst c2
  simp [unpairAS, AS.withPLZero, cantor, triangle]

theorem read_acM (st : AS V) (hc : Clean st) (hs : sz st ≤ tower j L) :
    Mac (.node 174) st { st with pl := second st.pl, ac := st.ac + first st.pl } j L 17 := by
  have h1 := read108M hL st hc hs
  have h2 := loop201M (by omega) _ h1.2
  refine ((Mac.seq (n := 174) rfl hL h1 h2).eq ?_).mono (by omega)
  obtain ⟨c1, c2⟩ := hc; cases st; simp only at c1 c2; subst c1; subst c2; simp

theorem read_p1M (st : AS V) (hc : Clean st) (hs : sz st ≤ tower j L) :
    Mac (.node 175) st { st with pl := second st.pl, p1 := st.p1 + first st.pl } j L 17 := by
  have h1 := read108M hL st hc hs
  have h2 := loop205M (by omega) _ h1.2
  refine ((Mac.seq (n := 175) rfl hL h1 h2).eq ?_).mono (by omega)
  obtain ⟨c1, c2⟩ := hc; cases st; simp only at c1 c2; subst c1; subst c2; simp

theorem read_p2M (st : AS V) (hc : Clean st) (hs : sz st ≤ tower j L) :
    Mac (.node 176) st { st with pl := second st.pl, p2 := st.p2 + first st.pl } j L 17 := by
  have h1 := read108M hL st hc hs
  have h2 := loop207M (by omega) _ h1.2
  refine ((Mac.seq (n := 176) rfl hL h1 h2).eq ?_).mono (by omega)
  obtain ⟨c1, c2⟩ := hc; cases st; simp only at c1 c2; subst c1; subst c2; simp

theorem pop_p2M (st : AS V) (hc : Clean st) (hs : sz st ≤ tower j L) :
    Mac (.node 170) st { st with ws := second st.ws, p2 := st.p2 + first st.ws } j L 17 := by
  have h1 := pop110M hL st hc hs
  have h2 := loop207M (by omega) _ h1.2
  refine ((Mac.seq (n := 170) rfl hL h1 h2).eq ?_).mono (by omega)
  obtain ⟨c1, c2⟩ := hc; cases st; simp only at c1 c2; subst c1; subst c2; simp

end DiophantineConsistency.ArithmeticRuntimeBoundDagMacros
