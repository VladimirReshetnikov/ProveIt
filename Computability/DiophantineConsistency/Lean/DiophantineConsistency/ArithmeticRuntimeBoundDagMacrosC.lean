import DiophantineConsistency.ArithmeticRuntimeBoundDagMacrosB

/-! # Bounded DagPerm macros, part C: unpair walks, `tw += 4·s2`, fetch

Bounded twins of `body154`, `loop115`, `loop116`, `add2..add4`, `loop117`,
`loop136`, `fetch_pos` and `fetch_zero`, mirroring the accepted proof bodies.
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
open DiophantineConsistency.ArithmeticCommandWordPerm222 (first_le second_le)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local instance write_definable'' : 𝚺₁-Function₃[V] writeValue :=
  ArithmeticControlFile.write_defined.to_definable

theorem sz_le_of_split {st st' : AS V} (R a b c : V) (h1 : sz st' = R + a) (h2 : sz st = R + b)
    (ha : a ≤ c) : sz st' ≤ sz st + c := by
  rw [h1, h2]
  exact le_trans (_root_.add_le_add le_rfl ha) (_root_.add_le_add le_self_add le_rfl)

variable {j : V} {L : ℕ} (hL : 2 ≤ L)
include hL

theorem sz_add_mul_le {st st' : AS V} {c x : V} (hs : sz st ≤ tower j L)
    (h : sz st' = sz st + c * x) (hx : x ≤ sz st) (hc : c ≤ 14) : sz st' ≤ tower j (L+1) := by
  have h16 := sixteen_le_tower_of j hL
  rw [h, tower_succ]
  calc sz st + c * x ≤ tower j L + 14 * tower j L :=
        _root_.add_le_add hs (mul_le_mul hc (le_trans hx hs) (Arithmetic.zero_le _)
          (by norm_num))
    _ = 15 * tower j L := by ring
    _ ≤ tower j L * tower j L := mul_le_sq (le_trans (by norm_num) h16)

/-! ## The unpair walk -/

omit hL in
theorem walkStep_sz (st : AS V) : sz (walkStep st) ≤ sz st + 1 := by
  unfold walkStep
  split_ifs with h
  · exact le_of_eq (by simp only [sz, h]; ring)
  · have hv : st.s1 = (st.s1 - 1) + 1 :=
      (tsub_add_cancel_of_le (one_le_of_pos (lt_of_le_of_ne (Arithmetic.zero_le _) (Ne.symm h)))).symm
    refine le_trans (le_of_eq ?_) le_self_add
    simp only [sz]
    conv_rhs => rw [hv]
    ring

theorem body154B (st : AS V) (hs : sz st ≤ tower j L) :
    IRB (.node 154) (enc st) (.cont 1) (enc (walkStep st)) (tower j (L+4)) := by
  have hinc := inc_ASB 7 (by omega) st
  have hs1 : sz (updAS st 7 (field st 7 + 1)) ≤ tower j (L+1) :=
    le_trans (le_of_eq (by simp only [sz, updAS, field]; ring : _ = sz st + 1)) (succ_le_tower hL hs)
  have h137 : RnB (.node 137) (updAS st 7 (field st 7 + 1)) (walkStep st) (tower j (L+3)) := by
    by_cases h0 : st.s1 = 0
    · have h138 := RB.skip (n := 138) rfl
        (decZero_ASB 6 (by omega) (updAS st 7 (field st 7 + 1)) h0)
      have h211 := (loop211M (by omega) (updAS st 7 (field st 7 + 1)) hs1).1
      have h := RB.seq (n := 137) rfl h138 h211
      have e : ({ updAS st 7 (field st 7 + 1) with
          s1 := (updAS st 7 (field st 7 + 1)).s1 + (updAS st 7 (field st 7 + 1)).s2, s2 := 0 } : AS V)
          = walkStep st := by
        cases st
        simp only at h0
        subst h0
        simp [walkStep, updAS, field]
      rw [e] at h
      exact irunB_mono h (const_add_le (by omega) le_rfl (by norm_num))
    · have hv : st.s1 = (st.s1 - 1) + 1 :=
        (tsub_add_cancel_of_le (one_le_of_pos (lt_of_le_of_ne (Arithmetic.zero_le _) (Ne.symm h0)))).symm
      have hdec := decPos_ASB 6 (by omega) (updAS st 7 (field st 7 + 1)) (st.s1 - 1) hv
      have h138 := RB.brk_cdr (n := 138) (k := 0) rfl hdec (RB.brkS 0 _)
      have h := RB.skip (n := 137) rfl h138
      have e : updAS (updAS st 7 (field st 7 + 1)) 6 (st.s1 - 1) = walkStep st := by
        simp only [walkStep, if_neg h0]
        rfl
      rw [e] at h
      exact irunB_mono h (numeral_le_tower j (by omega) (by norm_num))
  have h155 := RB.seq (n := 155) rfl hinc h137
  have h := RB.cont_cdr (n := 154) (k := 0) rfl h155 (RB.contS 1 _)
  refine irunB_mono h ?_
  calc (1 : V) + tower j (L+3) + 1 = 2 + tower j (L+3) := by ring
    _ ≤ tower j (L+4) := const_add_le (by omega) le_rfl (by norm_num)

/-- Both unpair loops have the same bounded walk; only the source register differs. -/
private theorem unpair_loopM (useWS : Bool) (st : AS V) (hs : sz st ≤ tower j L) :
    Mac (.node (if useWS then 116 else 115)) st
      (if useWS then (unpairAS st (cantor st.s1 st.s2 + st.ws)).withWSZero
       else (unpairAS st (cantor st.s1 st.s2 + st.pl)).withPLZero) j L 13 := by
  set M := cantor st.s1 st.s2
  set v := if useWS then st.ws else st.pl
  set r : Nat := if useWS then 2 else 8
  set n : Nat := if useWS then 116 else 115
  have hr : r < 9 := by cases useWS <;> decide
  have hn : DagPerm.dagPerm.nodes n = (.decnz r, .node 154) := by cases useWS <;> rfl
  have hv : v ≤ tower j L := by
    cases useWS with
    | false => exact le_trans (field_le_sz st 8) hs
    | true => exact le_trans (field_le_sz st 2) hs
  have hM : M ≤ tower j (L+2) :=
    cantor_le_tower hL (le_trans (field_le_sz st 6) hs) (le_trans (field_le_sz st 7) hs)
  have hMv : M + v ≤ tower j (L+3) := add_le_tower_of (c := L+2) (by omega) le_rfl (by omega) hM hv
  have hQ : sz st + (v + (M + v) + (M + v)) ≤ tower j (L+6) := by
    have h1 : v + (M + v) ≤ tower j (L+4) := add_le_tower_of (c := L+3) (by omega) (by omega) le_rfl hv hMv
    have h2 : v + (M + v) + (M + v) ≤ tower j (L+5) :=
      add_le_tower_of (c := L+4) (by omega) le_rfl (by omega) h1 hMv
    exact add_le_tower_of (c := L+5) (by omega) (by omega) le_rfl hs h2
  let Wr : V → AS V := fun t =>
    if useWS then { st with ws := v - t, s1 := first (M + t), s2 := second (M + t) }
    else { st with pl := v - t, s1 := first (M + t), s2 := second (M + t) }
  have hfield : ∀ t, field (Wr t) r = v-t := by intro t; cases useWS <;> rfl
  have hWr : ∀ t, t ≤ v → ∀ w, w ≤ v → sz (updAS (Wr t) r w) ≤ tower j (L+6) := by
    intro t ht w hw
    refine le_trans ?_ hQ
    have hspl : sz (updAS (Wr t) r w) ≤ sz st + (w + first (M+t) + second (M+t)) := by
      cases useWS with
      | false =>
        refine sz_le_of_split (st.np + st.tw + st.ws + st.ac + st.p1 + st.p2)
          (w + first (M+t) + second (M+t)) (st.s1 + st.s2 + st.pl) _
          (by simp [sz, Wr, updAS, r]; ring) (by simp only [sz]; ring) ?_
        exact le_rfl
      | true =>
        refine sz_le_of_split (st.np + st.tw + st.pl + st.ac + st.p1 + st.p2)
          (w + first (M+t) + second (M+t)) (st.ws + st.s1 + st.s2) _
          (by simp [sz, Wr, updAS, r]; ring) (by simp only [sz]; ring) ?_
        exact le_rfl
    refine le_trans hspl (_root_.add_le_add le_rfl ?_)
    exact _root_.add_le_add (_root_.add_le_add hw
      (le_trans (first_le _) (_root_.add_le_add le_rfl ht)))
      (le_trans (second_le _) (_root_.add_le_add le_rfl ht))
  let x0 : V := enc st
  let G : V → V := fun t => writeValue (((if useWS then 0 else 1) : Nat) : V) (v - t)
    (writeValue ((5 : Nat) : V) (second (M + t)) (writeValue ((8 : Nat) : V) (first (M + t)) x0))
  have hG : ∀ t, G t = enc (Wr t) := by
    intro t
    cases useWS with
    | false =>
      show lupd (lupd (lupd (enc st) 6 (first (M+t))) 7 (second (M+t))) 8 (v-t) = enc (Wr t)
      rw [lupd_enc _ 6 (by omega), lupd_enc _ 7 (by omega), lupd_enc _ 8 (by omega)]
      rfl
    | true =>
      show lupd (lupd (lupd (enc st) 6 (first (M+t))) 7 (second (M+t))) 2 (v-t) = enc (Wr t)
      rw [lupd_enc _ 6 (by omega), lupd_enc _ 7 (by omega), lupd_enc _ 2 (by omega)]
      rfl
  haveI : 𝚺₁-Function₁[V] G :=
    write3_definable _ _ _ (fun t => v - t) (fun t => second (M + t)) (fun t => first (M + t)) x0
      (sub_definable v) (second_add_definable M) (first_add_definable M)
  have hpass : ∀ t, t < v → IRB (.decnz r) (G t) .normal (enc (updAS (Wr t) r (v-t-1))) 1 ∧
      IRB (.node 154) (enc (updAS (Wr t) r (v-t-1))) (.cont 1) (G (t+1))
        (tower j (L+6+4)) := by
    intro t ht
    refine ⟨?_, ?_⟩
    · rw [hG]
      exact decPos_ASB r hr (Wr t) (v-t-1) (by rw [hfield]; exact
        (tsub_add_cancel_of_le (one_le_of_pos (tsub_pos_of_lt ht))).symm)
    · rw [hG]
      have h := body154B (L := L+6) (by omega) (updAS (Wr t) r (v-t-1))
        (hWr t (le_of_lt ht) _ (le_trans tsub_le_self tsub_le_self))
      have e : walkStep (updAS (Wr t) r (v-t-1)) = Wr (t+1) := by
        cases useWS <;> rw [walkStep_fields] <;>
          simp [Wr, updAS, r, cantor_projections, add_assoc, tsub_tsub]
      rwa [e] at h
  have hfin : IRB (.node n) (G v) .normal (G v) 1 := by
    rw [hG]
    exact RB.skip hn (decZero_ASB r hr (Wr v) (by rw [hfield, tsub_self]))
  have hit := RB.iterate hn G (fun t => enc (updAS (Wr t) r (v-t-1))) v _ _ hpass hfin
  have hG0 : G 0 = enc st := by
    rw [hG]
    congr 1
    cases useWS <;> simp [Wr, M, v, first_cantor, second_cantor]
  have hszv : sz (Wr v) ≤ tower j (L+6) := by
    have := hWr v le_rfl (v-v) tsub_le_self
    cases useWS <;> simpa [Wr, updAS, r] using this
  rw [hG0, hG v] at hit
  have hres : RnB (.node n) st (Wr v) (v * (1 + tower j (L+6+4)) + 1) := hit
  have e : Wr v = (if useWS then (unpairAS st (cantor st.s1 st.s2 + st.ws)).withWSZero
       else (unpairAS st (cantor st.s1 st.s2 + st.pl)).withPLZero) := by
    cases useWS <;> simp [Wr, unpairAS, AS.withPLZero, AS.withWSZero, M, v]
  rw [e] at hres hszv
  refine ⟨irunB_mono hres ?_, le_tower_of hszv (by omega)⟩
  have h1 : 1 + tower j (L+6+4) ≤ tower j (L+11) := const_add_le (by omega) le_rfl (by norm_num)
  have h2 : v * (1 + tower j (L+6+4)) ≤ tower j (L+12) :=
    mul_le_tower (le_tower_of hv (by omega)) h1
  exact le_trans (succ_le_tower (by omega) h2) le_rfl

/-- `loop115` (unpair `pl`) within `tower j (L+13)` steps. -/
theorem loop115M (st : AS V) (hs : sz st ≤ tower j L) :
    Mac (.node 115) st (unpairAS st (cantor st.s1 st.s2 + st.pl)).withPLZero j L 13 :=
  unpair_loopM hL false st hs

/-- `loop116` (unpair `ws`) within `tower j (L+13)` steps. -/
theorem loop116M (st : AS V) (hs : sz st ≤ tower j L) :
    Mac (.node 116) st (unpairAS st (cantor st.s1 st.s2 + st.ws)).withWSZero j L 13 :=
  unpair_loopM hL true st hs

end DiophantineConsistency.ArithmeticRuntimeBoundDagMacros
