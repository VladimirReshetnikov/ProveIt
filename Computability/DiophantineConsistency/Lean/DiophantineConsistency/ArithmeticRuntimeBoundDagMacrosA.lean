import BusyBeaver.ZFC.ArithmeticDagRootPerm222
import DiophantineConsistency.ArithmeticRuntimeBoundDagRun
import DiophantineConsistency.ArithmeticEnumBoundTower

/-! # Bounded DagPerm macros, part A: setup and the transfer/copy loops

Bounded twins of `ArithmeticDagMacrosPerm222`. `IRB`/`RnB` are `IR`/`Rn` with an
explicit clock bound (`ArithmeticRuntimeBoundDagRun.IRunB`). `sz` is the sum of
the nine registers, and `Mac e st st' j L k` packages "within `tower j (L+k)` steps,
with output size at most `tower j (L+k)`" for inputs of size at most `tower j L`.
Each wrapper below mirrors the accepted proof body, with `transferB`/`copy2B` in
place of `transfer`/`copy2`. No existing statement is changed. -/
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
open ArithmeticRuntimeBoundDagRun ArithmeticEnumBoundTower

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `IR` with a clock bound. -/
abbrev IRB (e : RMDag.Edge) (x : V) (X : Exit) (y : V) (B : V) : Prop :=
  IRunB DagPerm.dagPerm ArithmeticDagControlPerm222.rowsLit
    (ArithmeticDagControlPerm222.run (V := V)) e x X y B

/-- `Rn` with a clock bound. -/
abbrev RnB (e : RMDag.Edge) (st st' : AS V) (B : V) : Prop := IRB e (enc st) .normal (enc st') B

/-- Total register mass of a record. -/
def sz (st : AS V) : V :=
  st.np + (st.tw + (st.ws + (st.ac + (st.p1 + (st.p2 + (st.s1 + (st.s2 + st.pl)))))))

theorem field_le_sz (st : AS V) : ∀ r, field st r ≤ sz st
  | 0 => show st.np ≤ sz st from le_self_add
  | 1 => show st.tw ≤ sz st from le_trans le_self_add le_add_self
  | 2 => show st.ws ≤ sz st from le_trans le_self_add (le_trans le_add_self le_add_self)
  | 3 => show st.ac ≤ sz st from
      le_trans le_self_add (le_trans le_add_self (le_trans le_add_self le_add_self))
  | 4 => show st.p1 ≤ sz st from le_trans le_self_add (le_trans le_add_self
      (le_trans le_add_self (le_trans le_add_self le_add_self)))
  | 5 => show st.p2 ≤ sz st from le_trans le_self_add (le_trans le_add_self
      (le_trans le_add_self (le_trans le_add_self (le_trans le_add_self le_add_self))))
  | 6 => show st.s1 ≤ sz st from le_trans le_self_add (le_trans le_add_self
      (le_trans le_add_self (le_trans le_add_self (le_trans le_add_self
        (le_trans le_add_self le_add_self)))))
  | 7 => show st.s2 ≤ sz st from le_trans le_self_add (le_trans le_add_self
      (le_trans le_add_self (le_trans le_add_self (le_trans le_add_self
        (le_trans le_add_self (le_trans le_add_self le_add_self))))))
  | 8 => show st.pl ≤ sz st from le_trans le_add_self (le_trans le_add_self
      (le_trans le_add_self (le_trans le_add_self (le_trans le_add_self
        (le_trans le_add_self (le_trans le_add_self le_add_self))))))
  | _+9 => show (0 : V) ≤ sz st from Arithmetic.zero_le _

/-! ## Tower arithmetic -/

theorem lin_le' {x c d j : V} {L : ℕ} (hL : 2 ≤ L) (hx : x ≤ tower j L) (hc : c ≤ 15)
    (hd : d ≤ 15) : x * c + d ≤ tower j (L+1) := by
  have h16 := sixteen_le_tower_of j hL
  rw [tower_succ]
  calc x * c + d ≤ tower j L * 15 + tower j L :=
        _root_.add_le_add (mul_le_mul hx hc (Arithmetic.zero_le _) (Arithmetic.zero_le _))
          (le_trans hd (le_trans (by norm_num) h16))
    _ = 16 * tower j L := by ring
    _ ≤ tower j L * tower j L := mul_le_sq h16

theorem lin_le {x c j : V} {L : ℕ} (hL : 2 ≤ L) (hx : x ≤ tower j L) (hc : c ≤ 15) :
    x * c + 1 ≤ tower j (L+1) :=
  lin_le' hL hx hc (by norm_num)

theorem mul_le_tower {x y j : V} {L : ℕ} (hx : x ≤ tower j L) (hy : y ≤ tower j L) :
    x * y ≤ tower j (L+1) := by
  rw [tower_succ]
  exact mul_le_mul hx hy (Arithmetic.zero_le _) (Arithmetic.zero_le _)

theorem add_le_tower_of {x y j : V} {a b c : ℕ} (hc : 2 ≤ c) (ha : a ≤ c) (hb : b ≤ c)
    (hx : x ≤ tower j a) (hy : y ≤ tower j b) : x + y ≤ tower j (c+1) :=
  add_le_tower' hc (le_tower_of hx ha) (le_tower_of hy hb)

/-! ## Instances of the generic bounded calculus -/

instance run_definable : 𝚺₁-Function₂[V] (ArithmeticDagControlPerm222.run (V := V)) :=
  ArithmeticControlTable.controlRun_definable ArithmeticDagControlPerm222.table

namespace RB
open ArithmeticDagControlPerm222 (spec)
theorem inc (r : Nat) (x : V) : IRB (.inc r) x .normal (lupd x r (lreg x r + 1)) 1 :=
  run_incB R.run_one spec r x
theorem decPos (r : Nat) (x v : V) (hv : lreg x r = v + 1) :
    IRB (.decnz r) x .normal (lupd x r v) 1 := run_decPosB R.run_one spec r x v hv
theorem decZero (r : Nat) (x : V) (hz : lreg x r = 0) : IRB (.decnz r) x (.brk 1) x 1 :=
  run_decZeroB R.run_one spec r x hz
theorem brkS (k : Nat) (x : V) : IRB (.brk (k+1)) x (.brk (k+1)) x 1 :=
  run_brkSB R.run_one spec k x
theorem contS (k : Nat) (x : V) : IRB (.cont (k+1)) x (.cont (k+1)) x 1 :=
  run_contSB R.run_one spec k x
theorem halt (x : V) : IRB .halt x .halt x 1 := run_haltB R.run_one spec x
variable {n : Nat} {a b : RMDag.Edge}
theorem seq (hn : DagPerm.dagPerm.nodes n = (a, b)) {x y z A B : V}
    (ha : IRB a x .normal y A) (hb : IRB b y .normal z B) : IRB (.node n) x .normal z (A + B) :=
  run_seqB R.run_add hn ha hb
theorem skip (hn : DagPerm.dagPerm.nodes n = (a, b)) {x y A : V}
    (ha : IRB a x (.brk 1) y A) : IRB (.node n) x .normal y A := run_skipB hn ha
theorem brk_cdr {k : Nat} (hn : DagPerm.dagPerm.nodes n = (a, b)) {x y z A B : V}
    (ha : IRB a x .normal y A) (hb : IRB b y (.brk (k+1)) z B) :
    IRB (.node n) x (.brk (k+1)) z (A + B) := run_brk_cdrB R.run_add hn ha hb
theorem cont_car {k : Nat} (hn : DagPerm.dagPerm.nodes n = (a, b)) {x y A : V}
    (ha : IRB a x (.cont (k+1)) y A) : IRB (.node n) x (.cont (k+1)) y A := run_cont_carB hn ha
theorem cont_cdr {k : Nat} (hn : DagPerm.dagPerm.nodes n = (a, b)) {x y z A B : V}
    (ha : IRB a x .normal y A) (hb : IRB b y (.cont (k+2)) z B) :
    IRB (.node n) x (.cont (k+1)) z (A + B) := run_cont_cdrB R.run_add hn ha hb
theorem restart (hn : DagPerm.dagPerm.nodes n = (a, b)) {x y z w A B C : V} {X : Exit}
    (ha : IRB a x .normal y A) (hb : IRB b y (.cont 1) z B) (hrest : IRB (.node n) z X w C) :
    IRB (.node n) x X w (A + B + C) := run_restartB R.run_add hn ha hb hrest
theorem halt_car (hn : DagPerm.dagPerm.nodes n = (a, b)) {x y A : V}
    (ha : IRB a x .halt y A) : IRB (.node n) x .halt y A := run_halt_carB hn ha
theorem halt_cdr (hn : DagPerm.dagPerm.nodes n = (a, b)) {x y z A B : V}
    (ha : IRB a x .normal y A) (hb : IRB b y .halt z B) : IRB (.node n) x .halt z (A + B) :=
  run_halt_cdrB R.run_add hn ha hb
theorem iterate (hn : DagPerm.dagPerm.nodes n = (a, b)) (G H : V → V) [𝚺₁-Function₁[V] G]
    (N A B : V)
    (hpass : ∀ t, t < N → IRB a (G t) .normal (H t) A ∧ IRB b (H t) (.cont 1) (G (t+1)) B)
    {X : Exit} {y C : V} (hfin : IRB (.node n) (G N) X y C) :
    IRB (.node n) (G 0) X y (N * (A + B) + C) :=
  run_iterateB R.run_zero R.run_add hn G H N A B hpass hfin
end RB

theorem decPos_ASB (r : Nat) (hr : r < 9) (st : AS V) (v : V) (hv : field st r = v + 1) :
    IRB (.decnz r) (enc st) .normal (enc (updAS st r v)) 1 := by
  have h := RB.decPos r (enc st) v (by rw [lreg_enc st r hr]; exact hv)
  rwa [lupd_enc st r hr] at h

theorem decZero_ASB (r : Nat) (hr : r < 9) (st : AS V) (hz : field st r = 0) :
    IRB (.decnz r) (enc st) (.brk 1) (enc st) 1 :=
  RB.decZero r (enc st) (by rw [lreg_enc st r hr]; exact hz)

theorem inc_ASB (r : Nat) (hr : r < 9) (st : AS V) :
    IRB (.inc r) (enc st) .normal (enc (updAS st r (field st r + 1))) 1 := by
  have h := RB.inc r (enc st)
  rwa [lreg_enc st r hr, lupd_enc st r hr] at h

/-! ## Packaged macro bounds -/

/-- Within `tower j (L+k)` steps, to an output of size at most `tower j (L+k)`. -/
def Mac (e : RMDag.Edge) (st st' : AS V) (j : V) (L k : ℕ) : Prop :=
  RnB e st st' (tower j (L+k)) ∧ sz st' ≤ tower j (L+k)

theorem Mac.mono {e : RMDag.Edge} {st st' : AS V} {j : V} {L k k' : ℕ}
    (h : Mac e st st' j L k) (hk : k ≤ k') : Mac e st st' j L k' :=
  ⟨irunB_mono h.1 (tower_mono j (by omega)), le_tower_of h.2 (by omega)⟩

theorem Mac.eq {e : RMDag.Edge} {st s1 s2 : AS V} {j : V} {L k : ℕ}
    (h : Mac e st s1 j L k) (he : s1 = s2) : Mac e st s2 j L k := he ▸ h

/-- Sequencing two packaged macros. -/
theorem Mac.seq {n : Nat} {a b : RMDag.Edge} (hn : DagPerm.dagPerm.nodes n = (a, b))
    {st s1 s2 : AS V} {j : V} {L k1 k2 : ℕ} (hL : 2 ≤ L)
    (ha : Mac a st s1 j L k1) (hb : Mac b s1 s2 j (L+k1) k2) :
    Mac (.node n) st s2 j L (k1+k2+1) := by
  refine ⟨irunB_mono (RB.seq hn ha.1 hb.1) ?_, le_tower_of hb.2 (by omega)⟩
  have := add_le_tower_of (j := j) (c := L+k1+k2) (by omega) (by omega) (by omega)
    (le_refl (tower j (L+k1))) (le_refl (tower j (L+k1+k2)))
  exact le_tower_of this (by omega)

theorem Mac.inc (r : Nat) (hr : r < 9) {st : AS V} {j : V} {L : ℕ} (hL : 2 ≤ L)
    (hs : sz st ≤ tower j L) (hsz : sz (updAS st r (field st r + 1)) ≤ sz st + 1) :
    Mac (.inc r) st (updAS st r (field st r + 1)) j L 1 :=
  ⟨irunB_mono (inc_ASB r hr st) (one_le_tower j _), le_trans hsz (succ_le_tower hL hs)⟩

variable {j : V} {L : ℕ} (hL : 2 ≤ L)
include hL

theorem mac_intro {e : RMDag.Edge} {st st' : AS V} {x c : V} (hs : sz st ≤ tower j L)
    (h : RnB e st st' (x * c + 1)) (hx : x ≤ sz st) (hc : c ≤ 15)
    (hsz : sz st' ≤ sz st + sz st) : Mac e st st' j L 1 :=
  ⟨irunB_mono h (lin_le hL (le_trans hx hs) hc),
    le_trans hsz (add_le_tower' hL hs hs)⟩

/-! ## The transfer and copy loops -/

/-- Package a two-register transfer after bounding its output size. -/
private theorem transferMacro {n m src dst : Nat}
    (hn : DagPerm.dagPerm.nodes n = (.decnz src, .node m))
    (hm : DagPerm.dagPerm.nodes m = (.inc dst, .cont 2))
    (hd : phys src ≠ phys dst) (hdr : dst < 9) (hsr : src < 9)
    (st : AS V) (hs : sz st ≤ tower j L)
    (hsz : sz (updAS (updAS st dst (field st dst + field st src)) src 0) ≤ sz st + sz st) :
    Mac (.node n) st (updAS (updAS st dst (field st dst + field st src)) src 0) j L 1 := by
  have h := transferB (p := DagPerm.dagPerm) R.run_zero R.run_add R.run_one
    ArithmeticDagControlPerm222.spec hn hm hd (enc st)
  rw [lreg_enc st dst hdr, lreg_enc st src hsr, lupd_enc st dst hdr,
    lupd_enc _ src hsr] at h
  exact mac_intro hL hs h (field_le_sz st src) (by norm_num) hsz

/-- Package a three-register copy after bounding its output size. -/
private theorem copyMacro {n m m' src d1 d2 : Nat}
    (hn : DagPerm.dagPerm.nodes n = (.decnz src, .node m))
    (hm : DagPerm.dagPerm.nodes m = (.node m', .cont 2))
    (hm' : DagPerm.dagPerm.nodes m' = (.inc d1, .inc d2))
    (h1 : phys src ≠ phys d1) (h2 : phys src ≠ phys d2) (h12 : phys d1 ≠ phys d2)
    (hd1 : d1 < 9) (hsr : src < 9) (hd2 : d2 < 9)
    (st : AS V) (hs : sz st ≤ tower j L)
    (hsz : sz (updAS (updAS (updAS st d1 (field st d1 + field st src)) d2
      (field st d2 + field st src)) src 0) ≤ sz st + sz st) :
    Mac (.node n) st (updAS (updAS (updAS st d1 (field st d1 + field st src)) d2
      (field st d2 + field st src)) src 0) j L 1 := by
  have h := copy2B (p := DagPerm.dagPerm) R.run_zero R.run_add R.run_one
    ArithmeticDagControlPerm222.spec hn hm hm' h1 h2 h12 (enc st)
  rw [lreg_enc st d1 hd1, lreg_enc st src hsr, lreg_enc st d2 hd2,
    lupd_enc st d1 hd1, lupd_enc _ d2 hd2, lupd_enc _ src hsr] at h
  exact mac_intro hL hs h (field_le_sz st src) (by norm_num) hsz


theorem loop201M (st : AS V) (hs : sz st ≤ tower j L) :
    Mac (.node 201) st { st with ac := st.ac + st.s1, s1 := 0 } j L 1 := by
  apply transferMacro hL (n := 201) (m := 202) (src := 6) (dst := 3) rfl rfl
    (by decide) (by omega) (by omega) st hs
  exact le_trans (le_of_eq (by simp only [sz, updAS, field]; ring)) le_self_add

theorem loop203M (st : AS V) (hs : sz st ≤ tower j L) :
    Mac (.node 203) st { st with np := st.np + st.s1, s1 := 0 } j L 1 := by
  apply transferMacro hL (n := 203) (m := 204) (src := 6) (dst := 0) rfl rfl
    (by decide) (by omega) (by omega) st hs
  exact le_trans (le_of_eq (by simp only [sz, updAS, field]; ring)) le_self_add

theorem loop205M (st : AS V) (hs : sz st ≤ tower j L) :
    Mac (.node 205) st { st with p1 := st.p1 + st.s1, s1 := 0 } j L 1 := by
  apply transferMacro hL (n := 205) (m := 206) (src := 6) (dst := 4) rfl rfl
    (by decide) (by omega) (by omega) st hs
  exact le_trans (le_of_eq (by simp only [sz, updAS, field]; ring)) le_self_add

theorem loop207M (st : AS V) (hs : sz st ≤ tower j L) :
    Mac (.node 207) st { st with p2 := st.p2 + st.s1, s1 := 0 } j L 1 := by
  apply transferMacro hL (n := 207) (m := 191) (src := 6) (dst := 5) rfl rfl
    (by decide) (by omega) (by omega) st hs
  exact le_trans (le_of_eq (by simp only [sz, updAS, field]; ring)) le_self_add

theorem loop208M (st : AS V) (hs : sz st ≤ tower j L) :
    Mac (.node 208) st { st with tw := st.tw + st.s1, s1 := 0 } j L 1 := by
  apply transferMacro hL (n := 208) (m := 186) (src := 6) (dst := 1) rfl rfl
    (by decide) (by omega) (by omega) st hs
  exact le_trans (le_of_eq (by simp only [sz, updAS, field]; ring)) le_self_add

theorem loop209M (st : AS V) (hs : sz st ≤ tower j L) :
    Mac (.node 209) st { st with pl := st.pl + st.s2, s2 := 0 } j L 1 := by
  apply transferMacro hL (n := 209) (m := 210) (src := 7) (dst := 8) rfl rfl
    (by decide) (by omega) (by omega) st hs
  exact le_trans (le_of_eq (by simp only [sz, updAS, field]; ring)) le_self_add

theorem loop211M (st : AS V) (hs : sz st ≤ tower j L) :
    Mac (.node 211) st { st with s1 := st.s1 + st.s2, s2 := 0 } j L 1 := by
  apply transferMacro hL (n := 211) (m := 185) (src := 7) (dst := 6) rfl rfl
    (by decide) (by omega) (by omega) st hs
  exact le_trans (le_of_eq (by simp only [sz, updAS, field]; ring)) le_self_add

theorem loop212M (st : AS V) (hs : sz st ≤ tower j L) :
    Mac (.node 212) st { st with ws := st.ws + st.s2, s2 := 0 } j L 1 := by
  apply transferMacro hL (n := 212) (m := 213) (src := 7) (dst := 2) rfl rfl
    (by decide) (by omega) (by omega) st hs
  exact le_trans (le_of_eq (by simp only [sz, updAS, field]; ring)) le_self_add

theorem loop216M (st : AS V) (hs : sz st ≤ tower j L) :
    Mac (.node 216) st { st with s1 := st.s1 + st.tw, tw := 0 } j L 1 := by
  apply transferMacro hL (n := 216) (m := 185) (src := 1) (dst := 6) rfl rfl
    (by decide) (by omega) (by omega) st hs
  exact le_trans (le_of_eq (by simp only [sz, updAS, field]; ring)) le_self_add

theorem loop217M (st : AS V) (hs : sz st ≤ tower j L) :
    Mac (.node 217) st { st with tw := st.tw + st.ws, ws := 0 } j L 1 := by
  apply transferMacro hL (n := 217) (m := 186) (src := 2) (dst := 1) rfl rfl
    (by decide) (by omega) (by omega) st hs
  exact le_trans (le_of_eq (by simp only [sz, updAS, field]; ring)) le_self_add

theorem loop197M (st : AS V) (hs : sz st ≤ tower j L) :
    Mac (.node 197) st { st with p2 := st.p2 + st.p1, p1 := 0 } j L 1 := by
  apply transferMacro hL (n := 197) (m := 191) (src := 4) (dst := 5) rfl rfl
    (by decide) (by omega) (by omega) st hs
  exact le_trans (le_of_eq (by simp only [sz, updAS, field]; ring)) le_self_add

theorem loop193M (st : AS V) (hs : sz st ≤ tower j L) :
    Mac (.node 193) st { st with s1 := st.s1 + st.ac, tw := st.tw + st.ac, ac := 0 } j L 1 := by
  apply copyMacro hL (n := 193) (m := 189) (m' := 190) (src := 3) (d1 := 6) (d2 := 1)
    rfl rfl rfl (by decide) (by decide) (by decide) (by omega) (by omega) (by omega) st hs
  exact le_trans (le_of_eq (by simp only [sz, updAS, field]; ring : _ = sz st + st.ac))
    (_root_.add_le_add le_rfl (field_le_sz st 3))

theorem loop194M (st : AS V) (hs : sz st ≤ tower j L) :
    Mac (.node 194) st { st with pl := st.pl + st.np, s1 := st.s1 + st.np, np := 0 } j L 1 := by
  apply copyMacro hL (n := 194) (m := 195) (m' := 196) (src := 0) (d1 := 8) (d2 := 6)
    rfl rfl rfl (by decide) (by decide) (by decide) (by omega) (by omega) (by omega) st hs
  exact le_trans (le_of_eq (by simp only [sz, updAS, field]; ring : _ = sz st + st.np))
    (_root_.add_le_add le_rfl (field_le_sz st 0))

theorem loop198M (st : AS V) (hs : sz st ≤ tower j L) :
    Mac (.node 198) st { st with s1 := st.s1 + st.p1, tw := st.tw + st.p1, p1 := 0 } j L 1 := by
  apply copyMacro hL (n := 198) (m := 189) (m' := 190) (src := 4) (d1 := 6) (d2 := 1)
    rfl rfl rfl (by decide) (by decide) (by decide) (by omega) (by omega) (by omega) st hs
  exact le_trans (le_of_eq (by simp only [sz, updAS, field]; ring : _ = sz st + st.p1))
    (_root_.add_le_add le_rfl (field_le_sz st 4))

theorem loop200M (st : AS V) (hs : sz st ≤ tower j L) :
    Mac (.node 200) st { st with s1 := st.s1 + st.p2, tw := st.tw + st.p2, p2 := 0 } j L 1 := by
  apply copyMacro hL (n := 200) (m := 189) (m' := 190) (src := 5) (d1 := 6) (d2 := 1)
    rfl rfl rfl (by decide) (by decide) (by decide) (by omega) (by omega) (by omega) st hs
  exact le_trans (le_of_eq (by simp only [sz, updAS, field]; ring : _ = sz st + st.p2))
    (_root_.add_le_add le_rfl (field_le_sz st 5))

theorem loop215M (st : AS V) (hs : sz st ≤ tower j L) :
    Mac (.node 215) st { st with s1 := st.s1 + st.tw, s2 := st.s2 + st.tw, tw := 0 } j L 1 := by
  apply copyMacro hL (n := 215) (m := 187) (m' := 188) (src := 1) (d1 := 6) (d2 := 7)
    rfl rfl rfl (by decide) (by decide) (by decide) (by omega) (by omega) (by omega) st hs
  exact le_trans (le_of_eq (by simp only [sz, updAS, field]; ring : _ = sz st + st.tw))
    (_root_.add_le_add le_rfl (field_le_sz st 1))

theorem loop192M (st : AS V) (hs : sz st ≤ tower j L) :
    Mac (.node 192) st { st with s1 := st.s1 + st.ac, s2 := st.s2 + st.ac, ac := 0 } j L 1 := by
  apply copyMacro hL (n := 192) (m := 187) (m' := 188) (src := 3) (d1 := 6) (d2 := 7)
    rfl rfl rfl (by decide) (by decide) (by decide) (by omega) (by omega) (by omega) st hs
  exact le_trans (le_of_eq (by simp only [sz, updAS, field]; ring : _ = sz st + st.ac))
    (_root_.add_le_add le_rfl (field_le_sz st 3))

end DiophantineConsistency.ArithmeticRuntimeBoundDagMacros
