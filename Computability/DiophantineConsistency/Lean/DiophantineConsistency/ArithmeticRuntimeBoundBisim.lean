import BusyBeaver.ZFC.ArithmeticControlBisimPerm215

/-! # Linear clock bounds for the certified offset-segment bisimulation

`ArithmeticControlBisim.entry_step` produces two positive clocks without an
upper bound. Its segment walk, however, is driven by the standard fuel, so each
certified entry costs at most `fuel+1` instructions on either side. This module
re-proves the segment and entry lemmas with that explicit upper bound and
derives a bounded halting transfer: if machine B halts at internal time `t`,
machine A halts at some time `≤ (fuel+1)*t`. It is instantiated for the actual
DagPerm/p215 certificate (fuel 6, hence factor 7). Proof bodies follow the
accepted originals; no existing statement is changed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.ArithmeticRuntimeBoundBisim
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC SetTheory.BusyBeaver.ZFC.ArithmeticControlBisim

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {reg : V → Fin 9 → V} {write : Fin 9 → V → V → V} {live : V → V → V}

section Segment
variable (step : V → V) (run : V → V → V) (rows : Nat → Option Row)
  (run_zero : ∀ x, run 0 x = x)
  (run_add : ∀ t u x, run (t+u) x = run u (run t x))
  (run_one : ∀ x, run 1 x = step x)
  (spec : ∀ (c : Nat) (row : Row) (x : V), rows c = some row →
    step (live (c : V) x) = sem reg write live row x)
  (reg_write_same : ∀ p v x, reg (write p v x) p = v)
  (reg_write_other : ∀ p q v x, p ≠ q → reg (write p v x) q = reg x q)

include run_zero run_add run_one spec reg_write_same reg_write_other

/-- `segment_sound` with its clock bounded by the standard fuel. -/
theorem segment_sound_le (fuel c : Nat) (u : Vec) (t : Nat) (u' : Vec)
    (hs : segment rows fuel c u = some (t, u')) (x y : V) (hy : Shifted reg x u y) :
    ∃ k y', k ≤ (fuel : V) ∧ run k (live (c : V) y) = live (t : V) y' ∧
      Shifted reg x u' y' := by
  induction fuel generalizing c u y with
  | zero => simp [segment] at hs
  | succ fuel ih =>
    rcases hr : rows c with _ | row
    · simp [segment, hr] at hs
    · simp only [segment, hr] at hs
      by_cases hstop : row.op = 2 ∨ row.op = 4
      · rw [if_pos hstop] at hs
        cases hs
        exact ⟨0, y, Arithmetic.zero_le _, run_zero _, hy⟩
      rw [if_neg hstop] at hs
      have h2 : row.op ≠ 2 := fun h => hstop (.inl h)
      have hsucc : ∀ k : V, k ≤ (fuel : V) → 1 + k ≤ ((fuel+1 : Nat) : V) := by
        intro k hk
        rw [Nat.cast_succ, add_comm (fuel : V) 1]
        exact _root_.add_le_add le_rfl hk
      by_cases h1 : row.op = 1
      · rw [if_pos h1] at hs
        obtain ⟨k, y', hkf, hk, hy'⟩ := ih row.next0 (bump u row.reg) hs
          (write row.reg (reg y row.reg + 1) y)
          (shifted_bump reg_write_same reg_write_other x y u row.reg hy)
        refine ⟨1+k, y', hsucc k hkf, ?_, hy'⟩
        rw [run_add, run_one, spec c row y hr, sem, if_pos h1, hk]
      · rw [if_neg h1] at hs
        by_cases h3 : row.op = 3
        · rw [if_pos h3] at hs
          obtain ⟨k, y', hkf, hk, hy'⟩ := ih row.next0 u hs y hy
          refine ⟨1+k, y', hsucc k hkf, ?_, hy'⟩
          rw [run_add, run_one, spec c row y hr, sem, if_neg h1, if_neg h2, if_pos h3, hk]
        · rw [if_neg h3] at hs
          cases hs

end Segment

section Entry

variable (fileOf : (Fin 9 → V) → V) (reg_fileOf : ∀ g p, reg (fileOf g) p = g p)
  (stepA stepB : V → V) (runA runB : V → V → V) (rowsA rowsB : Nat → Option Row)
  (cert : Nat → Option Entry) (fuel : Nat)
  (runA_zero : ∀ x, runA 0 x = x) (runB_zero : ∀ x, runB 0 x = x)
  (runA_add : ∀ t u x, runA (t+u) x = runA u (runA t x))
  (runB_add : ∀ t u x, runB (t+u) x = runB u (runB t x))
  (runA_one : ∀ x, runA 1 x = stepA x) (runB_one : ∀ x, runB 1 x = stepB x)
  (specA : ∀ (c : Nat) (row : Row) (x : V), rowsA c = some row →
    stepA (live (c : V) x) = sem reg write live row x)
  (specB : ∀ (c : Nat) (row : Row) (x : V), rowsB c = some row →
    stepB (live (c : V) x) = sem reg write live row x)
  (reg_write_same : ∀ p v x, reg (write p v x) p = v)
  (reg_write_other : ∀ p q v x, p ≠ q → reg (write p v x) q = reg x q)

include reg_fileOf runA_zero runB_zero runA_add runB_add runA_one runB_one specA specB
  reg_write_same reg_write_other in
/-- `entry_step` with both clocks at most `fuel+1`. -/
theorem entry_step_le (e : Entry) (hc : checkEntry rowsA rowsB cert fuel e = true)
    (x ya yb : V) (ha : Shifted reg x e.α ya) (hb : Shifted reg x e.β yb) :
    ∃ ka kb, 1 ≤ ka ∧ 1 ≤ kb ∧ ka ≤ (fuel : V) + 1 ∧ kb ≤ (fuel : V) + 1 ∧
      ((runA ka (live (e.a : V) ya) = 0 ∧ runB kb (live (e.b : V) yb) = 0) ∨
       ∃ s e', (s = e.s0 ∨ s = e.s1) ∧ cert s = some e' ∧
         Next (reg := reg) (live := live) e' (runA ka (live (e.a : V) ya))
           (runB kb (live (e.b : V) yb))) := by
  obtain ⟨ta, ua, tb, ub, ra, rb, hsa, hsb, hra, hrb, hcase⟩ :=
    checkEntry_spec rowsA rowsB cert fuel e hc
  obtain ⟨k1, ya1, hk1f, hk1, hya1⟩ := segment_sound_le stepA runA rowsA runA_zero runA_add
    runA_one specA reg_write_same reg_write_other fuel e.a e.α ta ua hsa x ya ha
  obtain ⟨k2, yb1, hk2f, hk2, hyb1⟩ := segment_sound_le stepB runB rowsB runB_zero runB_add
    runB_one specB reg_write_same reg_write_other fuel e.b e.β tb ub hsb x yb hb
  have hA : ∀ t, runA (k1+t) (live (e.a : V) ya) = runA t (live (ta : V) ya1) := by
    intro t; rw [runA_add, hk1]
  have hB : ∀ t, runB (k2+t) (live (e.b : V) yb) = runB t (live (tb : V) yb1) := by
    intro t; rw [runB_add, hk2]
  have hpos : ∀ k : V, 1 ≤ k + 1 := fun k => le_add_self
  have hka : k1 + 1 ≤ (fuel : V) + 1 := _root_.add_le_add hk1f le_rfl
  have hkb : k2 + 1 ≤ (fuel : V) + 1 := _root_.add_le_add hk2f le_rfl
  rcases hcase with ⟨ha4, hb4⟩ | ⟨ha2, hb2, hreg, hoff, ⟨e0, he0, hm0⟩, ⟨e1, he1, hm1⟩⟩
  · refine ⟨k1+1, k2+1, hpos _, hpos _, hka, hkb, .inl ⟨?_, ?_⟩⟩
    · rw [hA, runA_one, specA ta ra ya1 hra, sem]
      simp [ha4]
    · rw [hB, runB_one, specB tb rb yb1 hrb, sem]
      simp [hb4]
  set x' := fileOf (fun p => reg x p + ((min (vget ua p) (vget ub p) : Nat) : V)) with hx'
  have hx'p : ∀ p : Fin 9, reg x' p = reg x p + ((min (vget ua p) (vget ub p) : Nat) : V) :=
    fun p => by rw [hx', reg_fileOf]
  obtain ⟨hsa', hsb'⟩ := shifted_norm x ya1 yb1 ua ub hya1 hyb1 x' hx'p
  set r := ra.reg
  have hra0 : vget (vnorm ua ub) r = 0 := by
    rw [vget_vnorm]; omega
  have hrb0 : vget (vnorm ub ua) r = 0 := by
    rw [vget_vnorm]; omega
  have hva : reg ya1 r = reg x' r := by rw [hsa' r, hra0]; simp
  have hvb : reg yb1 r = reg x' r := by rw [hsb' r, hrb0]; simp
  have hvb' : reg yb1 rb.reg = reg x' r := by rw [← hreg]; exact hvb
  obtain ⟨h0a, h0b, h0α, h0β⟩ := entryIs_eq hm0
  obtain ⟨h1a, h1b, h1α, h1β⟩ := entryIs_eq hm1
  have ha1 : ra.op ≠ 1 := by omega
  have hb1 : rb.op ≠ 1 := by omega
  refine ⟨k1+1, k2+1, hpos _, hpos _, hka, hkb, .inr ?_⟩
  by_cases hz : reg x' r = 0
  · refine ⟨e.s0, e0, .inl rfl, he0, x', ya1, yb1, ?_, ?_, ?_, ?_⟩
    · rw [hA, runA_one, specA ta ra ya1 hra, sem, if_neg ha1, if_pos ha2, if_pos (hva.trans hz),
        h0a]
    · rw [hB, runB_one, specB tb rb yb1 hrb, sem, if_neg hb1, if_pos hb2,
        if_pos (hvb'.trans hz), h0b]
    · rw [h0α]; exact hsa'
    · rw [h0β]; exact hsb'
  · refine ⟨e.s1, e1, .inr rfl, he1, write r (reg x' r - 1) x',
      write r (reg ya1 r - 1) ya1, write r (reg yb1 r - 1) yb1, ?_, ?_, ?_, ?_⟩
    · rw [hA, runA_one, specA ta ra ya1 hra, sem, if_neg ha1, if_pos ha2,
        if_neg (fun h => hz (hva ▸ h)), h1a]
    · rw [hB, runB_one, specB tb rb yb1 hrb, sem, if_neg hb1, if_pos hb2,
        if_neg (fun h => hz (hvb' ▸ h)), h1b, ← hreg]
    · rw [h1α]
      exact shifted_decrement reg_write_same reg_write_other x' ya1 _ r hsa' hra0
    · rw [h1β]
      exact shifted_decrement reg_write_same reg_write_other x' yb1 _ r hsb' hrb0

end Entry

section Main

variable (fileOf : (Fin 9 → V) → V) (reg_fileOf : ∀ g p, reg (fileOf g) p = g p)
  (live_ne : ∀ c x, live c x ≠ 0)
  (liveDef : 𝚺₁.Semisentence 3) (regDef : Fin 9 → 𝚺₁.Semisentence 2)
  [hlive : 𝚺₁-Function₂[V] live via liveDef]
  [hreg : ∀ p, 𝚺₁-Function₁[V] (fun x => reg x p) via regDef p]
  (stepA stepB : V → V) (runA runB : V → V → V)
  [𝚺₁-Function₂[V] runA] [𝚺₁-Function₂[V] runB]
  (rowsA rowsB : Nat → Option Row) (cert : Nat → Option Entry) (fuel N : Nat)
  (runA_zero : ∀ x, runA 0 x = x) (runB_zero : ∀ x, runB 0 x = x)
  (runA_add : ∀ t u x, runA (t+u) x = runA u (runA t x))
  (runB_add : ∀ t u x, runB (t+u) x = runB u (runB t x))
  (runA_one : ∀ x, runA 1 x = stepA x) (runB_one : ∀ x, runB 1 x = stepB x)
  (runA_halted : ∀ t, runA t 0 = 0) (runB_halted : ∀ t, runB t 0 = 0)
  (specA : ∀ (c : Nat) (row : Row) (x : V), rowsA c = some row →
    stepA (live (c : V) x) = sem reg write live row x)
  (specB : ∀ (c : Nat) (row : Row) (x : V), rowsB c = some row →
    stepB (live (c : V) x) = sem reg write live row x)
  (reg_write_same : ∀ p v x, reg (write p v x) p = v)
  (reg_write_other : ∀ p q v x, p ≠ q → reg (write p v x) q = reg x q)
  (hcheck : ∀ i, i < N → entryOK rowsA rowsB cert fuel N i = true)

include reg_fileOf runA_zero runB_zero runA_add runB_add runA_one runB_one specA specB
  reg_write_same reg_write_other hcheck in
omit [𝚺₁-Function₂ runA] [𝚺₁-Function₂ runB] in
/-- A certified relation step bounds both clocks simultaneously. -/
theorem rel_step_both (a b : V) (h : Rel reg live cert N a b) :
    ∃ ka kb, 1 ≤ ka ∧ 1 ≤ kb ∧ ka ≤ (fuel : V) + 1 ∧ kb ≤ (fuel : V) + 1 ∧
      ((runA ka a = 0 ∧ runB kb b = 0) ∨ Rel reg live cert N (runA ka a) (runB kb b)) := by
    obtain ⟨i, hi, e, he, x, ya, yb, ha, hb, hsa, hsb⟩ := rel_entry a b h
    obtain ⟨_, he', hc, hs0, hs1, _⟩ := entryOK_spec rowsA rowsB cert fuel N i (hcheck i hi)
    rw [he] at he'
    cases he'
    obtain ⟨ka, kb, hka, hkb, hkaK, hkbK, hq⟩ := entry_step_le fileOf reg_fileOf stepA stepB runA
      runB rowsA rowsB cert fuel runA_zero runB_zero runA_add runB_add runA_one runB_one specA
      specB reg_write_same reg_write_other e hc x ya yb hsa hsb
    refine ⟨ka, kb, hka, hkb, hkaK, hkbK, ?_⟩
    rw [ha, hb]
    rcases hq with hz | ⟨s, e', hs, hes, x', ya', yb', ha', hb', hsa', hsb'⟩
    · exact .inl hz
    · have hsN : s < N := by rcases hs with rfl | rfl <;> assumption
      refine .inr ?_
      rw [ha', hb']
      obtain ⟨e'', he'', _, _, _, hpos⟩ := entryOK_spec rowsA rowsB cert fuel N s (hcheck s hsN)
      rw [hes] at he''
      cases he''
      exact rel_of_entry s hsN e' hes hpos x' ya' yb' hsa' hsb'

include reg_fileOf runA_zero runB_zero runA_add runB_add runA_one runB_one
  runA_halted runB_halted specA specB reg_write_same reg_write_other hcheck hlive hreg in
/-- Both clocks stay between the number of certified steps and its fuel bound. -/
theorem bounded_clocks (a b : V) (h0 : Rel reg live cert N a b) (n : V) :
    ∃ ta tb, ta ≤ ((fuel : V) + 1) * n ∧ n ≤ ta ∧
      tb ≤ ((fuel : V) + 1) * n ∧ n ≤ tb ∧
      ((runA ta a = 0 ∧ runB tb b = 0) ∨ Rel reg live cert N (runA ta a) (runB tb b)) := by
  haveI : 𝚺₁-Relation[V] (Rel reg live cert N) :=
    (rel_defined reg live cert N liveDef regDef).to_definable
  let K : V := (fuel : V) + 1
  have hK1 : (1 : V) ≤ K := le_add_self
  change ∃ ta tb, ta ≤ K * n ∧ n ≤ ta ∧ tb ≤ K * n ∧ n ≤ tb ∧ _
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    exact ⟨0, 0, by simp, le_rfl, by simp, le_rfl,
      .inr (by simpa only [runA_zero, runB_zero] using h0)⟩
  case succ n ih =>
    obtain ⟨ta, tb, hta, hta', htb, htb', hq⟩ := ih
    have hKn : K * (n+1) = K * n + K := by ring
    rcases hq with ⟨hza, hzb⟩ | hr
    · refine ⟨ta+1, tb+1, ?_, _root_.add_le_add hta' le_rfl, ?_,
        _root_.add_le_add htb' le_rfl, .inl ⟨?_, ?_⟩⟩
      · rw [hKn]; exact _root_.add_le_add hta hK1
      · rw [hKn]; exact _root_.add_le_add htb hK1
      · rw [runA_add, hza, runA_halted]
      · rw [runB_add, hzb, runB_halted]
    · obtain ⟨ka, kb, hka, hkb, hkaK, hkbK, hs⟩ :=
        rel_step_both fileOf reg_fileOf stepA stepB runA runB rowsA rowsB cert fuel N
          runA_zero runB_zero runA_add runB_add runA_one runB_one specA specB
          reg_write_same reg_write_other hcheck _ _ hr
      refine ⟨ta+ka, tb+kb, ?_, _root_.add_le_add hta' hka, ?_,
        _root_.add_le_add htb' hkb, ?_⟩
      · rw [hKn]; exact _root_.add_le_add hta hkaK
      · rw [hKn]; exact _root_.add_le_add htb hkbK
      · rw [runA_add, runB_add]; exact hs

include reg_fileOf live_ne runA_zero runB_zero runA_add runB_add runA_one runB_one
  runA_halted runB_halted specA specB reg_write_same reg_write_other hcheck hlive hreg in
/-- **Bounded certified transfer, B to A.** A halt of B at internal time `t`
gives a halt of A at some time at most `(fuel+1)*t`. -/
theorem halts_le_of_check (e : Entry) (he : cert 0 = some e) (hN : 0 < N)
    (hα : ∀ p : Fin 9, vget e.α p = 0) (hβ : ∀ p : Fin 9, vget e.β p = 0) (x t : V)
    (ht : runB t (live (e.b : V) x) = 0) :
    ∃ ta ≤ ((fuel : V) + 1) * t, runA ta (live (e.a : V) x) = 0 := by
  have h0 : Rel reg live cert N (live (e.a : V) x) (live (e.b : V) x) := by
    obtain ⟨e', he', _, _, _, hpos⟩ := entryOK_spec rowsA rowsB cert fuel N 0 (hcheck 0 hN)
    rw [he] at he'
    cases he'
    exact rel_of_entry 0 hN e he hpos x x x
      (fun p => by rw [hα p]; simp) (fun p => by rw [hβ p]; simp)
  obtain ⟨ta, tb, hta, hta', htb, htb', hq⟩ := bounded_clocks
    fileOf reg_fileOf liveDef regDef stepA stepB runA runB rowsA rowsB cert fuel N
    runA_zero runB_zero runA_add runB_add runA_one runB_one runA_halted runB_halted
    specA specB reg_write_same reg_write_other hcheck _ _ h0 t
  have hz : runB tb (live (e.b : V) x) = 0 := by
    rw [← add_tsub_cancel_of_le htb', runB_add, ht, runB_halted]
  rcases hq with ⟨hza, _⟩ | hr
  · exact ⟨ta, hta, hza⟩
  · obtain ⟨_, _, _, _, _, _, _, _, hb, _, _⟩ := rel_entry _ _ hr
    exact absurd hz (hb ▸ live_ne _ _)

end Main
end Model

/-! ## The actual DagPerm/p215 certificate -/

section Actual
open ArithmeticControlTable
open ArithmeticControlFile (regValue fileValue liveValue reg_file live_ne_zero
  liveDef projectionDef projection_defined)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local instance proj_defined (p : Fin 9) :
    𝚺₁-Function₁[V] (fun x => regValue x p) via projectionDef 8 p :=
  projection_defined 8 p

/-- A p215 control halt at time `t` from control 1 gives a DagPerm halt from
the same file at some time at most `7*t`. -/
theorem dag_halts_le_of_215 (x t : V)
    (ht : ArithmeticControl215Table.run215 t (liveValue 1 x) = 0) :
    ∃ ta ≤ 7 * t, ArithmeticDagControlPerm222.run ta (liveValue 1 x) = 0 := by
  have h := halts_le_of_check (reg := regValue) (write := write) (live := liveValue)
    fileValue reg_file live_ne_zero liveDef (fun p => projectionDef 8 p)
    (stepValue ArithmeticDagControlPerm222.table) (stepValue ArithmeticControl215Table.table215)
    ArithmeticDagControlPerm222.run ArithmeticControl215Table.run215
    ArithmeticDagControlPerm222.rowsLit ArithmeticControl215Table.rows215
    ArithmeticControlBisimPerm215.cert ArithmeticControlBisimPerm215.fuel
    ArithmeticControlBisimPerm215.certSize
    ArithmeticDagControlPerm222.run_zero ArithmeticControl215Table.run215_zero
    ArithmeticDagControlPerm222.run_add ArithmeticControl215Table.run215_add
    ArithmeticDagControlPerm222.run_one ArithmeticControl215Table.run215_one
    ArithmeticDagControlPerm222.run_halted ArithmeticControl215Table.run215_halted
    ArithmeticDagControlPerm222.spec ArithmeticControl215Table.spec215
    reg_write_same reg_write_other ArithmeticControlBisimPerm215.check_all
    ArithmeticControlBisimPerm215.rootEntry ArithmeticControlBisimPerm215.cert_zero (by decide)
    ArithmeticControlBisimPerm215.root_offsets.1 ArithmeticControlBisimPerm215.root_offsets.2
    x t (by simpa only [ArithmeticControlBisimPerm215.rootEntry, Nat.cast_one] using ht)
  have h7 : ((ArithmeticControlBisimPerm215.fuel : Nat) : V) + 1 = 7 := by
    simp only [ArithmeticControlBisimPerm215.fuel]
    norm_num
  rw [h7] at h
  simpa only [ArithmeticControlBisimPerm215.rootEntry, Nat.cast_one] using h

end Actual
end DiophantineConsistency.ArithmeticRuntimeBoundBisim
