import BusyBeaver.ZFC.ArithmeticDagRun
import BusyBeaver.ZFC.DagPerm

/-! Three internal loop shapes for any represented control interpreter, then
literal instances in the actual DagPerm program. The algebra adapts the loop
proofs of ArithmeticL2Lib254, but imports neither that module nor its fixed
254 interpreter. All counters and elapsed times remain internal to IΣ1.
The actual whole-program occurrence and 215-machine simulation are separate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SetTheory.BusyBeaver.ZFC.ArithmeticDagLoops
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticDagRun RMDag
open ArithmeticControlFile (regValue liveValue writeValue write_defined)
open ArithmeticControlTable (write reg_write_same reg_write_other file_ext)
open ArithmeticControlBisim (Row sem)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local instance write_definable : 𝚺₁-Function₃[V] writeValue := write_defined.to_definable

private theorem reg_write_cases (p q : Fin 9) (v x : V) :
    regValue (write p v x) q = if p=q then v else regValue x q := by
  by_cases h : p=q
  · subst h; rw [reg_write_same, if_pos rfl]
  · rw [reg_write_other p q v x h, if_neg h]

theorem lreg_lupd_same (x v : V) (r : Nat) : lreg (lupd x r v) r = v := by
  simp only [lreg, lupd, reg_write_same]

theorem lreg_lupd_other (x v : V) (r s : Nat) (h : phys r ≠ phys s) :
    lreg (lupd x r v) s = lreg x s := by
  simp only [lreg, lupd]; exact reg_write_other _ _ _ _ h

theorem lupd_lreg (x : V) (r : Nat) : lupd x r (lreg x r) = x :=
  ArithmeticControlTable.write_same _ x

theorem lupd_write (x v : V) (r : Nat) : lupd x r v = writeValue ((phys r).val : V) v x := rfl

theorem lupd_lupd (x v w : V) (r : Nat) : lupd (lupd x r v) r w = lupd x r w := by
  apply file_ext; intro q
  simp only [lupd, reg_write_cases]
  split_ifs <;> rfl

theorem lupd_comm (x v w : V) (r s : Nat) (h : phys r ≠ phys s) :
    lupd (lupd x r v) s w = lupd (lupd x s w) r v := by
  apply file_ext; intro q
  simp only [lupd, reg_write_cases]
  split_ifs with h1 h2 h2
  · exact absurd (h2.trans h1.symm) h
  all_goals rfl

theorem one_le_of_pos {a : V} (h : 0 < a) : 1 ≤ a := by simpa using lt_iff_succ_le.mp h

variable {p : Prog} {rows : Nat → Option Row} {step : V → V} {run : V → V → V}
variable [𝚺₁-Function₂[V] run]
variable (run_zero : ∀ x, run 0 x=x)
  (run_add : ∀ t u x, run (t+u) x=run u (run t x))
  (run_one : ∀ x, run 1 x=step x)
  (spec : ∀ (c : Nat) (row : Row) (x : V), rows c=some row →
    step (liveValue (c : V) x)=sem regValue write liveValue row x)
include run_zero run_add run_one spec

/-- `while src > 0: src -= 1; dst += 1` behind one node: transfer `src` into `dst`. -/
theorem transfer {n m src dst : Nat} (hn : p.nodes n = (.decnz src, .node m))
    (hm : p.nodes m = (.inc dst, .cont 2)) (hsd : phys src ≠ phys dst) (x : V) :
    IRun p rows run (.node n) x .normal (lupd (lupd x dst (lreg x dst + lreg x src)) src 0) := by
  have hds : phys dst ≠ phys src := fun h => hsd h.symm
  let G : V → V := fun t => lupd (lupd x dst (lreg x dst + t)) src (lreg x src - t)
  let H : V → V := fun t => lupd (G t) src (lreg x src - t - 1)
  haveI : 𝚺₁-Function₁[V] G := by
    simp only [G, lupd_write, lreg]
    definability
  have hG0 : G 0 = x := by
    simp only [G, add_zero, tsub_zero]
    rw [show lreg x src = lreg (lupd x dst (lreg x dst)) src from
      (lreg_lupd_other x _ dst src hds).symm, lupd_lreg, lupd_lreg]
  have hpass : ∀ t, t < lreg x src → IRun p rows run (.decnz src) (G t) .normal (H t) ∧
      IRun p rows run (.node m) (H t) (.cont 1) (G (t+1)) := by
    intro t ht
    refine ⟨run_decPos run_one spec src (G t) (lreg x src - t - 1) ?_, ?_⟩
    · simp only [G, lreg_lupd_same]
      exact (tsub_add_cancel_of_le (one_le_of_pos (tsub_pos_of_lt ht))).symm
    · have hc := run_cont_cdr run_add (k := 0) hm (run_inc run_one spec dst (H t)) (run_contS run_one spec 1 _)
      have key : lupd (H t) dst (lreg (H t) dst + 1) = G (t+1) := by
        simp only [H, G]
        rw [lreg_lupd_other _ _ _ _ hsd, lreg_lupd_other _ _ _ _ hsd, lreg_lupd_same, lupd_lupd,
          lupd_comm _ _ _ src dst hsd, lupd_lupd, add_assoc, tsub_tsub]
      rw [key] at hc
      exact hc
  have hfin : IRun p rows run (.node n) (G (lreg x src)) .normal (G (lreg x src)) :=
    run_skip hn (run_decZero run_one spec src _ (by simp only [G, lreg_lupd_same, tsub_self]))
  have h := run_iterate run_zero run_add hn G H (lreg x src) hpass hfin
  rw [hG0] at h
  simpa only [G, tsub_self] using h

/-- A loop body `((inc d₁, inc d₂), continue 2)`: copy `src` into two registers. -/
theorem copy2 {n m m' src d1 d2 : Nat} (hn : p.nodes n = (.decnz src, .node m))
    (hm : p.nodes m = (.node m', .cont 2))
    (hm' : p.nodes m' = (.inc d1, .inc d2))
    (h1 : phys src ≠ phys d1) (h2 : phys src ≠ phys d2) (h12 : phys d1 ≠ phys d2) (x : V) :
    IRun p rows run (.node n) x .normal
      (lupd (lupd (lupd x d1 (lreg x d1 + lreg x src)) d2 (lreg x d2 + lreg x src)) src 0) := by
  have h1' : phys d1 ≠ phys src := fun h => h1 h.symm
  have h2' : phys d2 ≠ phys src := fun h => h2 h.symm
  have h12' : phys d2 ≠ phys d1 := fun h => h12 h.symm
  let G : V → V := fun t =>
    lupd (lupd (lupd x d1 (lreg x d1 + t)) d2 (lreg x d2 + t)) src (lreg x src - t)
  let H : V → V := fun t => lupd (G t) src (lreg x src - t - 1)
  haveI : 𝚺₁-Function₁[V] G := by
    simp only [G, lupd_write, lreg]
    definability
  have hG0 : G 0 = x := by
    simp only [G, add_zero, tsub_zero]
    rw [show lreg x src = lreg (lupd (lupd x d1 (lreg x d1)) d2 (lreg x d2)) src by
        rw [lreg_lupd_other _ _ _ _ h2', lreg_lupd_other _ _ _ _ h1'],
      lupd_lreg, show lreg x d2 = lreg (lupd x d1 (lreg x d1)) d2 from
        (lreg_lupd_other x _ d1 d2 h12).symm, lupd_lreg, lupd_lreg]
  have hpass : ∀ t, t < lreg x src → IRun p rows run (.decnz src) (G t) .normal (H t) ∧
      IRun p rows run (.node m) (H t) (.cont 1) (G (t+1)) := by
    intro t ht
    refine ⟨run_decPos run_one spec src (G t) (lreg x src - t - 1) ?_, ?_⟩
    · simp only [G, lreg_lupd_same]
      exact (tsub_add_cancel_of_le (one_le_of_pos (tsub_pos_of_lt ht))).symm
    · have hin := run_seq run_add hm' (run_inc run_one spec d1 (H t)) (run_inc run_one spec d2 _)
      have hc := run_cont_cdr run_add (k := 0) hm hin (run_contS run_one spec 1 _)
      have key : lupd (lupd (H t) d1 (lreg (H t) d1 + 1)) d2
          (lreg (lupd (H t) d1 (lreg (H t) d1 + 1)) d2 + 1) = G (t+1) := by
        simp only [H, G]
        rw [lreg_lupd_other _ _ _ _ h12, lreg_lupd_other _ _ _ _ h2, lreg_lupd_other _ _ _ _ h2,
          lreg_lupd_same, lreg_lupd_other _ _ _ _ h1, lreg_lupd_other _ _ _ _ h1,
          lreg_lupd_other _ _ _ _ h12', lreg_lupd_same, lupd_lupd]
        rw [lupd_comm _ _ _ src d1 h1, lupd_comm _ _ _ d2 d1 h12', lupd_lupd,
          lupd_comm _ _ _ src d2 h2, lupd_lupd, add_assoc, add_assoc, tsub_tsub]
      rw [key] at hc
      exact hc
  have hfin : IRun p rows run (.node n) (G (lreg x src)) .normal (G (lreg x src)) :=
    run_skip hn (run_decZero run_one spec src _ (by simp only [G, lreg_lupd_same, tsub_self]))
  have h := run_iterate run_zero run_add hn G H (lreg x src) hpass hfin
  rw [hG0] at h
  simpa only [G, tsub_self] using h

/-- A loop `(decnz r, continue 1)` clears `r`. -/
theorem clear {n r : Nat} (hn : p.nodes n = (.decnz r, .cont 1)) (x : V) :
    IRun p rows run (.node n) x .normal (lupd x r 0) := by
  let G : V → V := fun t => lupd x r (lreg x r - t)
  haveI : 𝚺₁-Function₁[V] G := by
    simp only [G, lupd_write, lreg]
    definability
  have hG0 : G 0 = x := by simp only [G, tsub_zero]; exact lupd_lreg x r
  have hpass : ∀ t, t < lreg x r → IRun p rows run (.decnz r) (G t) .normal (G (t+1)) ∧
      IRun p rows run (.cont 1) (G (t+1)) (.cont 1) (G (t+1)) := by
    intro t ht
    refine ⟨?_, run_contS run_one spec 0 _⟩
    have hd := run_decPos (p := p) run_one spec r (G t) (lreg x r - t - 1) (by
      simp only [G, lreg_lupd_same]
      exact (tsub_add_cancel_of_le (one_le_of_pos (tsub_pos_of_lt ht))).symm)
    have key : lupd (G t) r (lreg x r - t - 1) = G (t+1) := by
      simp only [G, lupd_lupd, tsub_tsub]
    rw [key] at hd
    exact hd
  have hfin : IRun p rows run (.node n) (G (lreg x r)) .normal (G (lreg x r)) :=
    run_skip hn (run_decZero run_one spec r _ (by simp only [G, lreg_lupd_same, tsub_self]))
  have h := run_iterate run_zero run_add hn G (fun t => G (t+1)) (lreg x r) hpass hfin
  rw [hG0] at h
  simpa only [G, tsub_self] using h

/-- Literal current node 197 transfers p1 into p2. -/
theorem dagPerm_transfer197 (x : V) :
    IRun DagPerm.dagPerm rows run (.node 197) x .normal
      (lupd (lupd x 5 (lreg x 5+lreg x 4)) 4 0) :=
  transfer run_zero run_add run_one spec (m := 191) rfl rfl (by decide) x

/-- Literal current node 192 copies ac into s1 and s2 and clears ac. -/
theorem dagPerm_copy192 (x : V) :
    IRun DagPerm.dagPerm rows run (.node 192) x .normal
      (lupd (lupd (lupd x 6 (lreg x 6+lreg x 3)) 7 (lreg x 7+lreg x 3)) 3 0) :=
  copy2 run_zero run_add run_one spec (m := 187) (m' := 188)
    rfl rfl rfl (by decide) (by decide) (by decide) x

/-- Literal current node 214 clears tw, including an initially zero counter. -/
theorem dagPerm_clear214 (x : V) :
    IRun DagPerm.dagPerm rows run (.node 214) x .normal (lupd x 1 0) :=
  clear run_zero run_add run_one spec rfl x

end SetTheory.BusyBeaver.ZFC.ArithmeticDagLoops
