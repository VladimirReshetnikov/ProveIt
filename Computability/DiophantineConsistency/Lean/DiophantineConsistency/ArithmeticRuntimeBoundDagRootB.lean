import DiophantineConsistency.ArithmeticRuntimeBoundDagRootA

/-! # Bounded DagPerm root, part B: gate, AX word, dispatch, command and root step

Bounded twins of `l457`, `AXAtom.run`, `axWordRun`, `l236`, `ax_leaf`, `mp484`,
the dispatch lemmas, `read_run`, `command_step`, `fetch_run` and `root_step` of
`ArithmeticDagRootPerm222`, mirroring the accepted proof bodies. The AX word has
156 atoms; each atom costs at most `tower j (L+150)` on an input below
`tower j L`, so the word costs at most `tower j (L + KAX)`, `KAX = 151*156+17`.
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
open ArithmeticDagLoops (one_le_of_pos)
open ArithmeticRuntimeBoundDagRun ArithmeticEnumBoundTower
open ArithmeticCode254 (wim wel wal weq tagged)
open ArithmeticDagRootPerm222 (pushA popA gateF AXAtom axWordCheck axWordEval axWord axWord_checked
  f236 ax_eval mpOut boundary selector_cases)
open DiophantineConsistency.ArithmeticCommandStepPerm222
open DiophantineConsistency.ArithmeticCommandWordPerm222
open DiophantineConsistency.ArithmeticCommandFetchPerm222
open DiophantineConsistency.ArithmeticEnumStepPerm222 (enumValue execValue enum_live)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The tower offset of the AX word. -/
def KAX : ℕ := 151 * 156 + 17

theorem axWord_length : axWord.length = 156 := by decide

theorem dec_brkB {a b : Nat} (ha : DagPerm.dagPerm.nodes a = (.decnz 3, .node b)) {st : AS V}
    (k : V) (hk : st.ac = k + 1) {out B : V}
    (hb : IRB (.node b) (enc { st with ac := k }) (.brk 1) out B) :
    IRB (.node a) (enc st) (.brk 1) out (1 + B) :=
  RB.brk_cdr (k := 0) ha (decPos_ASB 3 (by omega) st k hk) hb

theorem passB {b c a' : Nat} {e : Edge} (hb : DagPerm.dagPerm.nodes b = (.node c, .brk 1))
    (hc : DagPerm.dagPerm.nodes c = (.node a', e)) {out out' B : V}
    (h : IRB (.node a') out (.brk 1) out' B) : IRB (.node b) out (.brk 1) out' (B + 1) :=
  RB.brk_cdr (k := 0) hb (RB.skip hc h) (RB.brkS 0 _)

theorem fallB {b c a' x : Nat} {e : Edge} (hb : DagPerm.dagPerm.nodes b = (.node c, .brk 1))
    (hc : DagPerm.dagPerm.nodes c = (.node a', e))
    (ha' : DagPerm.dagPerm.nodes a' = (.decnz 3, .node x))
    {st st' : AS V} (h0 : st.ac = 0) {B : V} (he : IRB e (enc st) .normal (enc st') B) :
    IRB (.node b) (enc st) (.brk 1) (enc st') (1 + B + 1) :=
  RB.brk_cdr (k := 0) hb (RB.seq hc (RB.skip ha' (decZero_ASB 3 (by omega) st h0)) he)
    (RB.brkS 0 _)

variable {j : V}

theorem l457M {L : ℕ} (hL : 2 ≤ L) (st : AS V) (hc : Clean st) (hs : sz st ≤ tower j L) :
    Mac (.node 457) st (gateF st) j L 17 := by
  have m1 := loop192M hL st hs
  have m2 := ifeq_clearM (L := L+1) (by omega) _ m1.2
  have m3 := loop211M (L := L+1+5) (by omega) _ m2.2
  have m4 := loop197M (L := L+1+5+1) (by omega) _ m3.2
  have m5 := ifeq_clearM (L := L+1+5+1+1) (by omega) _ m4.2
  have h := Mac.seq (n := 457) rfl hL m1 (Mac.seq (n := 458) rfl (by omega) m2
    (Mac.seq (n := 459) rfl (by omega) m3 (Mac.seq (n := 460) rfl (by omega) m4 m5)))
  refine (h.eq ?_).mono (by omega)
  clear h m1 m2 m3 m4 m5 hs
  obtain ⟨c1, c2⟩ := hc
  cases st
  simp only at c1 c2
  subst c1; subst c2
  simp only [gateF, zero_add]
  split <;> split <;> simp_all

theorem AXAtom.runM {L : ℕ} (hL : 2 ≤ L) (st : AS V) (hc : Clean st) (hs : sz st ≤ tower j L) :
    ∀ a : AXAtom, Mac (.node a.node) st (a.effect st) j L 150
  | .par1 => (par1M hL st hc hs).mono (by omega)
  | .par2 => (par2M hL st hc hs).mono (by omega)
  | .par3 => (par3M hL st hc hs).mono (by omega)
  | .push => (pushwffM hL st hc hs).mono (by omega)
  | .cons => (consM hL st hc hs).mono (by omega)
  | .wel => (wel_mM hL st hc hs).mono (by omega)
  | .wal => (wal_mM hL st hc hs).mono (by omega)
  | .weq => (weq_mM hL st hc hs).mono (by omega)
  | .wn => (wn_mM hL st hc hs).mono (by omega)
  | .wa => (wa_mM hL st hc hs).mono (by omega)
  | .wex => (wex_mM hL st hc hs).mono (by omega)
  | .readp2 => (read_p2M hL st hc hs).mono (by omega)
  | .readp1 => (read_p1M hL st hc hs).mono (by omega)

theorem axWordRunM (word : List AXAtom) : ∀ {n : Nat} {L : ℕ}, 2 ≤ L →
    axWordCheck n word = true → ∀ st : AS V, Clean st → sz st ≤ tower j L →
      Mac (.node n) st (axWordEval word st) j L (151 * word.length + 17) := by
  induction word with
  | nil =>
    intro n L hL h st hc hs
    simp only [axWordCheck, decide_eq_true_eq] at h
    subst n
    exact (l457M hL st hc hs).mono (by simp)
  | cons a rest ih =>
    intro n L hL h st hc hs
    simp only [axWordCheck] at h
    split at h
    · rename_i m next hn
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with ⟨hm, hr⟩
      subst m
      have m1 := AXAtom.runM hL st hc hs a
      have m2 := ih (L := L+150) (by omega) hr _ (by cases a <;> exact hc) m1.2
      exact (Mac.seq hn hL m1 m2).mono (by simp only [List.length_cons]; omega)
    · contradiction

theorem l236M {L : ℕ} (hL : 2 ≤ L) (st : AS V) (hc : Clean st) (hs : sz st ≤ tower j L) :
    Mac (.node 236) st (f236 st) j L KAX := by
  have h := axWordRunM axWord hL axWord_checked st hc hs
  rw [axWord_length] at h
  exact h

variable {L : ℕ} (hL : 2 ≤ L)
include hL

theorem mp484M (st : AS V) (hc : Clean st) (hs : sz st ≤ tower j L) :
    Mac (.node 484) st (mpOut { st with pl := second st.pl, p1 := st.p1 + first st.pl }) j L 105 := by
  have m1 := read_p1M hL st hc hs
  have m2 := mp_branchM (L := L+17) (by omega) _ (by exact hc) m1.2
  exact (Mac.seq (n := 484) rfl hL m1 m2).mono (by omega)

omit hL in
theorem skip142M (st : AS V) (h0 : st.ac = 0) (hs : sz st ≤ tower j L) :
    Mac (.node 142) st st j L 1 :=
  ⟨irunB_mono (RB.skip (n := 142) rfl (decZero_ASB 3 (by omega) st h0)) (one_le_tower _ _),
    le_tower_of hs (by omega)⟩

theorem dispatch_nipM (st : AS V) (hc : Clean st) (h0 : st.ac = 0) (hh : st.p2 ≠ 1)
    (hs : sz st ≤ tower j L) :
    Mac (.node 141) st { st with p2 := first st.ws, ws := second st.ws } j L 27 := by
  have m1 := skip142M st h0 hs
  have m2 := nip_branchM (L := L+1) (by omega) st hc hh m1.2
  exact (Mac.seq (n := 141) rfl hL m1 m2).mono (by omega)

theorem dispatch_nip_haltB (st : AS V) (hc : Clean st) (h0 : st.ac = 0) (hh : st.p2 = 1)
    (hs : sz st ≤ tower j L) : ∃ R', IRB (.node 141) (enc st) .halt R' (tower j (L+5)) := by
  obtain ⟨R', hR'⟩ := nip_haltB hL st hc hh hs
  exact ⟨R', irunB_mono (RB.halt_cdr (n := 141) rfl
    (RB.skip (n := 142) rfl (decZero_ASB 3 (by omega) st h0)) hR')
    (const_add_le (by omega) le_rfl (by norm_num))⟩

theorem dispatch_dropT (st : AS V) (hc : Clean st) (hs : sz { st with ac := 1 } ≤ tower j L) :
    RnB (.node 141) { st with ac := 1 } { st with ac := 0, tw := st.p2, ws := cantor st.tw st.ws }
      (tower j (L+25)) := by
  have hs0 : sz { st with ac := 0 } ≤ tower j L :=
    le_trans (sz_mono (b := { st with ac := 1 }) le_rfl le_rfl le_rfl (Arithmetic.zero_le _)
      le_rfl le_rfl le_rfl le_rfl le_rfl) hs
  have h := RB.skip (n := 141) rfl (dec_brkB (st := { st with ac := 1 }) rfl 0 (by simp)
    (fallB rfl rfl rfl rfl (par2M hL { st with ac := 0 } hc hs0).1))
  exact irunB_mono h (le_trans (le_of_eq (by ring : _ = (3 : V) + tower j (L+24)))
    (const_add_le (by omega) le_rfl (by norm_num)))

theorem dispatch_mpT (st : AS V) (hc : Clean st) (hs : sz { st with ac := 2 } ≤ tower j L) :
    RnB (.node 141) { st with ac := 2 }
      (mpOut { st with ac := 0, pl := second st.pl, p1 := st.p1 + first st.pl }) (tower j (L+106)) := by
  have hs0 : sz { st with ac := 0 } ≤ tower j L :=
    le_trans (sz_mono (b := { st with ac := 2 }) le_rfl le_rfl le_rfl (Arithmetic.zero_le _)
      le_rfl le_rfl le_rfl le_rfl le_rfl) hs
  have h := RB.skip (n := 141) rfl (dec_brkB (st := { st with ac := 2 }) rfl 1 (by dsimp; ring)
    (passB rfl rfl (dec_brkB (st := { ({ st with ac := 2 } : AS V) with ac := 1 }) rfl 0 (by simp)
      (fallB rfl rfl rfl rfl (mp484M hL { st with ac := 0 } hc hs0).1))))
  exact irunB_mono h (le_trans (le_of_eq (by ring : _ = (5 : V) + tower j (L+105)))
    (const_add_le (by omega) le_rfl (by norm_num)))

theorem dispatch_axT (st : AS V) (hc : Clean st) (c : V)
    (hs : sz { st with ac := c + 3 } ≤ tower j L) :
    RnB (.node 141) { st with ac := c + 3 } (f236 { st with ac := c }) (tower j (L+KAX+1)) := by
  have hsc : sz { st with ac := c } ≤ tower j L :=
    le_trans (sz_mono (b := { st with ac := c + 3 }) le_rfl le_rfl le_rfl le_self_add
      le_rfl le_rfl le_rfl le_rfl le_rfl) hs
  have hleaf := RB.brk_cdr (n := 149) (k := 0) rfl (l236M hL { st with ac := c } hc hsc).1
    (RB.brkS 0 _)
  have h := RB.skip (n := 141) rfl (dec_brkB (st := { st with ac := c + 3 }) rfl (c + 2)
    (by dsimp; ring) (passB rfl rfl
    (dec_brkB (st := { ({ st with ac := c + 3 } : AS V) with ac := c + 2 }) rfl (c + 1)
      (by dsimp; ring) (passB rfl rfl
      (dec_brkB (st := { ({ ({ st with ac := c + 3 } : AS V) with ac := c + 2 } : AS V) with
        ac := c + 1 }) rfl c rfl hleaf)))))
  exact irunB_mono h (le_trans (le_of_eq (by ring : _ = (6 : V) + tower j (L+KAX)))
    (const_add_le (by omega) le_rfl (by norm_num)))

/-- `read_run`: the selector read, then a dispatch bounded by `B`. -/
theorem read_runT (raw np t S d h : V) {X : AS V} {B : V}
    (hs : sz (boundary raw np t S d h) ≤ tower j L)
    (hd : RnB (.node 141) ⟨np,t,S,first raw,d,h,0,0,second raw⟩ X B) :
    RnB (.node 139) (boundary raw np t S d h) X (tower j (L+17) + B) := by
  have hr := read_acM hL (boundary raw np t S d h) ⟨rfl,rfl⟩ hs
  simp only [boundary, zero_add] at hr
  exact RB.seq (n := 139) rfl hr.1 hd

theorem read_sz (raw np t S d h : V) (hs : sz (boundary raw np t S d h) ≤ tower j L) :
    sz (⟨np,t,S,first raw,d,h,0,0,second raw⟩ : AS V) ≤ tower j (L+17) := by
  have hr := read_acM hL (boundary raw np t S d h) ⟨rfl,rfl⟩ hs
  simp only [boundary, zero_add] at hr
  exact hr.2

end DiophantineConsistency.ArithmeticRuntimeBoundDagMacros
