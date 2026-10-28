import DiophantineConsistency.ArithmeticRuntimeBoundBisim

/-! # Reverse bounded bisimulation hop: DagPerm halt ⇒ p215 control halt

The A-to-B counterpart of `halts_le_of_check` (`ArithmeticRuntimeBoundBisim`), using its
`entry_step_le` clock bound on the B side. The conclusion uses the p215 halting predicate
of `ArithmeticControlBisimPerm215.halts_iff` (`run215 t (liveValue 1 x) = 0`), so it
composes with the tape lane. Instantiated for the actual DagPerm/p215 certificate (fuel 6,
factor 7). Proof bodies follow the accepted forward ones; no existing statement is changed. -/
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

include reg_fileOf live_ne runA_zero runB_zero runA_add runB_add runA_one runB_one
  runA_halted runB_halted specA specB reg_write_same reg_write_other hcheck hlive hreg in
/-- **Bounded certified transfer, A to B.** A halt of A at internal time `t`
gives a halt of B at some time at most `(fuel+1)*t`. -/
theorem halts_le_of_check_rev (e : Entry) (he : cert 0 = some e) (hN : 0 < N)
    (hα : ∀ p : Fin 9, vget e.α p = 0) (hβ : ∀ p : Fin 9, vget e.β p = 0) (x t : V)
    (ht : runA t (live (e.a : V) x) = 0) :
    ∃ tb ≤ ((fuel : V) + 1) * t, runB tb (live (e.b : V) x) = 0 := by
  haveI : 𝚺₁-Relation[V] (Rel reg live cert N) :=
    (rel_defined reg live cert N liveDef regDef).to_definable
  obtain ⟨K, hK⟩ : ∃ K : V, K = (fuel : V) + 1 := ⟨_, rfl⟩
  rw [← hK]
  have hK1 : (1 : V) ≤ K := by rw [hK]; exact le_add_self
  have rel_live : ∀ a b, Rel reg live cert N a b → a ≠ 0 ∧ b ≠ 0 := by
    intro a b h
    obtain ⟨_, _, _, _, _, _, _, ha, hb, _, _⟩ := rel_entry a b h
    exact ⟨ha ▸ live_ne _ _, hb ▸ live_ne _ _⟩
  have rel_step : ∀ a b, Rel reg live cert N a b → ∃ ka kb, 1 ≤ ka ∧ 1 ≤ kb ∧ kb ≤ K ∧
      ((runA ka a = 0 ∧ runB kb b = 0) ∨ Rel reg live cert N (runA ka a) (runB kb b)) := by
    intro a b h
    obtain ⟨i, hi, e, he, x, ya, yb, ha, hb, hsa, hsb⟩ := rel_entry a b h
    obtain ⟨_, he', hc, hs0, hs1, _⟩ := entryOK_spec rowsA rowsB cert fuel N i (hcheck i hi)
    rw [he] at he'
    cases he'
    obtain ⟨ka, kb, hka, hkb, _, hkaK, hq⟩ := entry_step_le fileOf reg_fileOf stepA stepB runA
      runB rowsA rowsB cert fuel runA_zero runB_zero runA_add runB_add runA_one runB_one specA
      specB reg_write_same reg_write_other e hc x ya yb hsa hsb
    refine ⟨ka, kb, hka, hkb, by rw [hK]; exact hkaK, ?_⟩
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
  have h0 : Rel reg live cert N (live (e.a : V) x) (live (e.b : V) x) := by
    obtain ⟨e', he', _, _, _, hpos⟩ := entryOK_spec rowsA rowsB cert fuel N 0 (hcheck 0 hN)
    rw [he] at he'
    cases he'
    exact rel_of_entry 0 hN e he hpos x x x
      (fun p => by rw [hα p]; simp) (fun p => by rw [hβ p]; simp)
  have clocks : ∀ n : V, ∃ ta tb, tb ≤ K * n ∧ n ≤ ta ∧
      ((runA ta (live (e.a : V) x) = 0 ∧ runB tb (live (e.b : V) x) = 0) ∨
        Rel reg live cert N (runA ta (live (e.a : V) x)) (runB tb (live (e.b : V) x))) := by
    intro n
    induction n using ISigma1.sigma1_succ_induction
    · definability
    case zero =>
      exact ⟨0, 0, by simp, le_rfl, .inr (by simpa only [runA_zero, runB_zero] using h0)⟩
    case succ n ih =>
      obtain ⟨ta, tb, htb, hta, hq⟩ := ih
      have hKn : K * (n+1) = K * n + K := by ring
      rcases hq with ⟨hza, hzb⟩ | hr
      · refine ⟨ta+1, tb+1, ?_, _root_.add_le_add hta le_rfl, .inl ⟨?_, ?_⟩⟩
        · rw [hKn]; exact _root_.add_le_add htb hK1
        · rw [runA_add, hza, runA_halted]
        · rw [runB_add, hzb, runB_halted]
      · obtain ⟨ka, kb, hka, _, hkbK, hs⟩ := rel_step _ _ hr
        refine ⟨ta+ka, tb+kb, ?_, _root_.add_le_add hta hka, ?_⟩
        · rw [hKn]; exact _root_.add_le_add htb hkbK
        · rw [runA_add, runB_add]
          exact hs
  obtain ⟨ta, tb, htb, hta, hq⟩ := clocks t
  have hz : runA ta (live (e.a : V) x) = 0 := by
    rw [← add_tsub_cancel_of_le hta, runA_add, ht, runA_halted]
  rcases hq with ⟨_, hzb⟩ | hr
  · exact ⟨tb, htb, hzb⟩
  · exact absurd hz (rel_live _ _ hr).1

end Main
end Model

section Actual
open ArithmeticControlTable
open ArithmeticControlFile (regValue fileValue liveValue reg_file live_ne_zero
  liveDef projectionDef projection_defined)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local instance proj_defined_rev (p : Fin 9) :
    𝚺₁-Function₁[V] (fun x => regValue x p) via projectionDef 8 p :=
  projection_defined 8 p

/-- A DagPerm control halt at time `t` from control 1 gives a p215 control halt
from the same file at some time at most `7*t`. -/
theorem p215_halts_le_of_dag (x t : V)
    (ht : ArithmeticDagControlPerm222.run t (liveValue 1 x) = 0) :
    ∃ tp ≤ 7 * t, ArithmeticControl215Table.run215 tp (liveValue 1 x) = 0 := by
  have h := halts_le_of_check_rev (reg := regValue) (write := write) (live := liveValue)
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

/-- The literal seed file of the scheduler. -/
theorem p215_halts_le_of_dag_seed (t : V)
    (ht : ArithmeticDagControlPerm222.run t (ArithmeticControlFile.liveValue 1
      (ArithmeticControlFile.fileValue ![0,0,0,0,0,0,4,0,0])) = 0) :
    ∃ tp ≤ 7 * t, ArithmeticControl215Table.run215 tp (ArithmeticControlFile.liveValue 1
      (ArithmeticControlFile.fileValue ![0,0,0,0,0,0,4,0,0])) = 0 :=
  p215_halts_le_of_dag _ t ht

end Actual

end DiophantineConsistency.ArithmeticRuntimeBoundBisim
