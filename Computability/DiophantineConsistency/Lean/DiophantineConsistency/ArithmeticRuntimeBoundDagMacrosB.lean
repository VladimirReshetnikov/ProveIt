import DiophantineConsistency.ArithmeticRuntimeBoundDagMacrosA

/-! # Bounded DagPerm macros, part B: pairing, unpairing and counter loops

Bounded twins of `pass163`, `finish162`, `pair162`, `body154`, `loop115`,
`loop116`, `loop117`, `loop136`, `fetch_pos` and `fetch_zero` of
`ArithmeticDagMacrosPerm222`, mirroring the accepted proof bodies with the clock
threaded through `RB.iterate`. Per-pass clocks are weakened to one uniform tower
level. No existing statement is changed. -/
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

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem const_add_le {x c j : V} {a : ℕ} (ha : 2 ≤ a) (hx : x ≤ tower j a) (hc : c ≤ 16) :
    c + x ≤ tower j (a+1) :=
  add_le_tower' ha (le_trans hc (sixteen_le_tower_of j ha)) hx

theorem lin_le' {x c d j : V} {L : ℕ} (hL : 2 ≤ L) (hx : x ≤ tower j L) (hc : c ≤ 15)
    (hd : d ≤ 15) : x * c + d ≤ tower j (L+1) := by
  have h16 := sixteen_le_tower_of j hL
  rw [tower_succ]
  calc x * c + d ≤ tower j L * 15 + tower j L :=
        _root_.add_le_add (mul_le_mul hx hc (Arithmetic.zero_le _) (Arithmetic.zero_le _))
          (le_trans hd (le_trans (by norm_num) h16))
    _ = 16 * tower j L := by ring
    _ ≤ tower j L * tower j L := mul_le_sq h16

/-- The six registers untouched by the pairing and walk loops. -/
def rest6 (st : AS V) : V := st.np + st.ws + st.ac + st.p1 + st.p2 + st.pl

theorem sz_split (st : AS V) : sz st = rest6 st + (st.tw + st.s1 + st.s2) := by
  simp only [sz, rest6]; ring

theorem rest6_le (st : AS V) : rest6 st ≤ sz st := by
  rw [sz_split]; exact le_self_add

local instance write_definable' : 𝚺₁-Function₃[V] writeValue :=
  ArithmeticControlFile.write_defined.to_definable

variable {j : V} {L : ℕ} (hL : 2 ≤ L)
include hL

/-! ## Pairing -/

theorem pass163B (u : AS V) (k : V) (hk : u.s1 = k + 1) (hs : sz u ≤ tower j L) :
    IRB (.node 163) (enc u) (.cont 1) (enc { u with s1 := 0, s2 := u.s2 + 1, tw := u.tw + k })
      (tower j (L+2)) := by
  have hdec := decPos_ASB 6 (by omega) u k hk
  have hinc := inc_ASB 7 (by omega) (updAS u 6 k)
  have hsz : sz (updAS (updAS u 6 k) 7 (field (updAS u 6 k) 7 + 1)) ≤ tower j L := by
    refine le_trans (le_of_eq ?_) hs
    simp only [sz, updAS, field, hk]; ring
  have h208 := (loop208M hL _ hsz).1
  have h165 := RB.seq (n := 165) rfl hinc h208
  have h164 := RB.cont_cdr (n := 164) (k := 1) rfl h165 (RB.contS 2 _)
  have h163 := RB.cont_cdr (n := 163) (k := 0) rfl hdec h164
  have e : ({ updAS (updAS u 6 k) 7 (field (updAS u 6 k) 7 + 1) with
      tw := (updAS (updAS u 6 k) 7 (field (updAS u 6 k) 7 + 1)).tw +
        (updAS (updAS u 6 k) 7 (field (updAS u 6 k) 7 + 1)).s1, s1 := 0 } : AS V) =
      { u with s1 := 0, s2 := u.s2 + 1, tw := u.tw + k } := by
    cases u; rfl
  rw [e] at h163
  refine irunB_mono h163 ?_
  calc (1 : V) + ((1 + tower j (L+1)) + 1) = 3 + tower j (L+1) := by ring
    _ ≤ tower j (L+2) := const_add_le (by omega) le_rfl (by norm_num)

theorem finish162B (u : AS V) (h1 : u.s1 = 0) (h2 : u.tw = 0) (hs : sz u ≤ tower j L) :
    IRB (.node 162) (enc u) .normal (enc u) (tower j (L+2)) := by
  have h215 := (loop215M hL u hs).1
  have he : ({ u with s1 := u.s1 + u.tw, s2 := u.s2 + u.tw, tw := 0 } : AS V) = u := by
    cases u; simp only at h1 h2 ⊢; subst h1; subst h2; simp
  rw [he] at h215
  exact irunB_mono (RB.seq (n := 162) rfl h215
    (RB.skip (n := 163) rfl (decZero_ASB 6 (by omega) u h1))) (succ_le_tower (by omega) le_rfl)

/-- `pair162` within `tower j (L+14)` steps. -/
theorem pair162M (st : AS V) (hs : sz st ≤ tower j L) :
    Mac (.node 162) st { st with s2 := st.s2 + cantor st.s1 st.tw, s1 := 0, tw := 0 } j L 14 := by
  have hout : sz ({ st with s2 := st.s2 + cantor st.s1 st.tw, s1 := 0, tw := 0 } : AS V) ≤
      tower j (L+14) := by
    have e : sz ({ st with s2 := st.s2 + cantor st.s1 st.tw, s1 := 0, tw := 0 } : AS V) =
        (rest6 st + st.s2) + cantor st.s1 st.tw := by simp only [sz, rest6]; ring
    have h1 : rest6 st + st.s2 ≤ sz st := by
      rw [sz_split]; exact _root_.add_le_add le_rfl (le_add_self)
    have hc := cantor_le_tower hL (le_trans (field_le_sz st 6) hs) (le_trans (field_le_sz st 1) hs)
    rw [e]
    exact le_tower_of (add_le_tower_of (c := L+2) (by omega) (by omega) le_rfl
      (le_trans h1 hs) hc) (by omega)
  by_cases hz : st.s1 + st.tw = 0
  · have ha : st.s1 = 0 := le_of_add_eq_zero_left hz
    have hb : st.tw = 0 := le_of_add_eq_zero_left (by rwa [add_comm] at hz)
    have e : ({ st with s2 := st.s2 + cantor st.s1 st.tw, s1 := 0, tw := 0 } : AS V) = st := by
      cases st; simp only at ha hb ⊢; subst ha; subst hb; simp [cantor, triangle]
    refine ⟨?_, hout⟩
    rw [e]
    exact irunB_mono (finish162B hL st ha hb hs) (tower_mono j (by omega))
  set m := st.s1 + st.tw - 1 with hm
  have hn : st.s1 + st.tw = m + 1 :=
    (tsub_add_cancel_of_le (one_le_of_pos (lt_of_le_of_ne (Arithmetic.zero_le _) (Ne.symm hz)))).symm
  set K := st.s2 + st.tw + 1 + triangle (m + 1) with hK
  have hm1 : m + 1 ≤ tower j L := by
    rw [← hn]
    have h2 : st.s1 + st.tw ≤ sz st := by
      rw [sz_split, add_comm st.s1 st.tw]
      exact le_trans le_self_add le_add_self
    exact le_trans h2 hs
  have hmL : m ≤ tower j L := le_trans le_self_add hm1
  have hK3 : K ≤ tower j (L+3) := by
    have ht : triangle (m + 1) ≤ tower j (L+2) := by
      rw [triangle_eq_cantor]; exact cantor_le_tower hL hm1 (Arithmetic.zero_le _)
    have h21 : st.s2 + st.tw ≤ tower j (L+1) :=
      add_le_tower' hL (le_trans (field_le_sz st 7) hs) (le_trans (field_le_sz st 1) hs)
    exact add_le_tower_of (c := L+2) (by omega) (by omega) le_rfl
      (succ_le_tower (by omega) h21) ht
  set Lg := L + 6 with hLg
  have hmK : sz st + (m + (K + m)) ≤ tower j Lg := by
    have h1 : K + m ≤ tower j (L+4) := add_le_tower_of (c := L+3) (by omega) le_rfl (by omega) hK3 hmL
    have h2 : m + (K + m) ≤ tower j (L+5) := add_le_tower_of (c := L+4) (by omega) (by omega) le_rfl hmL h1
    exact le_tower_of (add_le_tower_of (c := L+5) (by omega) (by omega) le_rfl hs h2) (by omega)
  -- the first pass
  have h215 := loop215M hL st hs
  have hp0 := pass163B (L := L+1) (by omega)
    { st with s1 := st.s1 + st.tw, s2 := st.s2 + st.tw, tw := 0 } m hn h215.2
  let Gr : V → AS V := fun t => { st with s1 := 0, tw := m - t, s2 := K - triangle (m + 1 - t) }
  let Hr : V → AS V := fun t =>
    { st with s1 := m - t, tw := 0, s2 := K - triangle (m + 1 - t) + (m - t) }
  have hGr : ∀ t, sz (Gr t) ≤ tower j Lg := by
    intro t
    have e1 : sz (Gr t) = rest6 st + ((m - t) + (K - triangle (m + 1 - t))) := by
      simp only [sz, rest6, Gr]; ring
    refine le_trans ?_ hmK
    rw [e1]
    exact _root_.add_le_add (rest6_le st) (_root_.add_le_add tsub_le_self
      (le_trans tsub_le_self le_self_add))
  have hHr : ∀ t, sz (Hr t) ≤ tower j Lg := by
    intro t
    have e1 : sz (Hr t) = rest6 st + ((m - t) + (K - triangle (m + 1 - t) + (m - t))) := by
      simp only [sz, rest6, Hr]; ring
    refine le_trans ?_ hmK
    rw [e1]
    exact _root_.add_le_add (rest6_le st) (_root_.add_le_add tsub_le_self
      (_root_.add_le_add tsub_le_self tsub_le_self))
  let x0 : V := lupd (enc st) 6 0
  let G : V → V := fun t =>
    writeValue ((5 : Nat) : V) (K - triangle (m + 1 - t)) (writeValue ((2 : Nat) : V) (m - t) x0)
  have hG : ∀ t, G t = enc (Gr t) := by
    intro t
    show lupd (lupd (lupd (enc st) 6 0) 1 (m - t)) 7 (K - triangle (m + 1 - t)) = enc (Gr t)
    rw [lupd_enc _ 6 (by omega), lupd_enc _ 1 (by omega), lupd_enc _ 7 (by omega)]
    rfl
  haveI : 𝚺₁-Function₁[V] G :=
    write2_definable _ _ (fun t => K - triangle (m + 1 - t)) (fun t => m - t) x0
      (sub_triangle_definable K (m + 1)) (sub_definable m)
  have hpass : ∀ t, t < m → IRB (.node 215) (G t) .normal (enc (Hr t)) (tower j (Lg+2)) ∧
      IRB (.node 163) (enc (Hr t)) (.cont 1) (G (t+1)) (tower j (Lg+2)) := by
    intro t ht
    have hjm : m - t = (m - t - 1) + 1 :=
      (tsub_add_cancel_of_le (one_le_of_pos (tsub_pos_of_lt ht))).symm
    refine ⟨?_, ?_⟩
    · rw [hG]
      have h := (loop215M (L := Lg) (by omega) (Gr t) (hGr t)).1
      have e : ({ Gr t with s1 := (Gr t).s1 + (Gr t).tw, s2 := (Gr t).s2 + (Gr t).tw, tw := 0 } :
          AS V) = Hr t := by
        simp only [Gr, Hr, zero_add]
      rw [e] at h
      exact irunB_mono h (tower_mono j (by omega))
    · rw [hG]
      have h := pass163B (L := Lg) (by omega) (Hr t) (m - t - 1) hjm (hHr t)
      have e : ({ Hr t with s1 := 0, s2 := (Hr t).s2 + 1, tw := (Hr t).tw + (m - t - 1) } :
          AS V) = Gr (t+1) := by
        simp only [Hr, Gr, zero_add]
        congr 1
        · rw [tsub_tsub]
        · have hsub : m + 1 - (t + 1) = m - t := add_tsub_add_eq_tsub_right m 1 t
          have hT : triangle (m + 1 - t) = triangle (m - t) + (m - t + 1) := by
            rw [show m + 1 - t = (m - t) + 1 from by
              rw [add_comm m 1, add_tsub_assoc_of_le (le_of_lt ht), add_comm], triangle_succ,
              add_assoc]
          have hle : triangle (m - t) + (m - t + 1) ≤ K := by
            rw [← hT, hK]
            exact le_trans (triangle_mono tsub_le_self) le_add_self
          rw [hsub, hT, add_assoc, tsub_add_shift hle]
      rwa [e] at h
  have hfin : IRB (.node 162) (G m) .normal (G m) (tower j (Lg+2)) := by
    rw [hG]
    exact finish162B (L := Lg) (by omega) (Gr m) rfl (by simp only [Gr, tsub_self]) (hGr m)
  have hit := RB.iterate (n := 162) rfl G (fun t => enc (Hr t)) m _ _ hpass hfin
  have hG0 : G 0 = enc { st with s1 := 0, s2 := st.s2 + st.tw + 1, tw := 0 + m } := by
    rw [hG]
    congr 1
    have hs' : K - triangle (m + 1 - 0) = st.s2 + st.tw + 1 := by
      rw [tsub_zero, hK, add_tsub_cancel_right]
    simp only [Gr, tsub_zero, zero_add]
    rw [show K - triangle (m + 1) = st.s2 + st.tw + 1 by simpa using hs']
  rw [hG0] at hit
  have hres := RB.restart (n := 162) rfl h215.1 hp0 hit
  have h1 : triangle (1 : V) = 1 := by
    have h := triangle_succ (0 : V)
    have h0 : triangle (0 : V) = 0 := by simp [triangle]
    simpa [h0] using h
  have hs2 : K - triangle (m + 1 - m) = st.s2 + cantor st.s1 st.tw := by
    rw [add_tsub_cancel_left, h1, hK, cantor, hn, add_right_comm (st.s2 + st.tw) 1,
      add_tsub_cancel_right, add_assoc, add_comm st.tw]
  have e : Gr m = { st with s2 := st.s2 + cantor st.s1 st.tw, s1 := 0, tw := 0 } := by
    simp only [Gr, tsub_self]
    rw [hs2]
  rw [hG m, e] at hres
  refine ⟨irunB_mono hres ?_, hout⟩
  -- clock arithmetic
  have hAB : tower j (Lg+2) + tower j (Lg+2) ≤ tower j (Lg+3) := add_le_tower' (by omega) le_rfl le_rfl
  have hmAB : m * (tower j (Lg+2) + tower j (Lg+2)) ≤ tower j (Lg+4) :=
    mul_le_tower (le_tower_of hmL (by omega)) hAB
  have hit' : m * (tower j (Lg+2) + tower j (Lg+2)) + tower j (Lg+2) ≤ tower j (Lg+5) :=
    add_le_tower_of (c := Lg+4) (by omega) le_rfl (by omega) hmAB le_rfl
  have h12 : tower j (L+1) + tower j (L+1+2) ≤ tower j (L+4) :=
    add_le_tower_of (c := L+3) (by omega) (by omega) (by omega) le_rfl le_rfl
  exact le_tower_of (add_le_tower_of (c := Lg+5) (by omega) (by omega) le_rfl h12 hit') (by omega)

end DiophantineConsistency.ArithmeticRuntimeBoundDagMacros
