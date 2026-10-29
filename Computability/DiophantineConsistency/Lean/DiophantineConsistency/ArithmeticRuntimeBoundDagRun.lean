import BusyBeaver.ZFC.ArithmeticDagLoops

/-! # Clock-bounded structured runs of DAG register programs

`ArithmeticDagRun.IRun` states that every occurrence of an edge reaches an exit
at *some* internal time. Here `IRunB … B` additionally bounds that time by an
explicit internal `B`. Every composition lemma of `ArithmeticDagRun` gets a
bounded counterpart whose bound is the sum of the premises' bounds; the loop
lemma `run_iterate` gets one with a uniform per-pass bound, giving
`N * (Pa + Pb) + Bfin`. The three generic loop shapes of `ArithmeticDagLoops`
are re-proved with linear clocks. Proof bodies follow the accepted originals.
No existing statement is changed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.ArithmeticRuntimeBoundDagRun
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC SetTheory.BusyBeaver.ZFC.ArithmeticDagRun RMDag
open ArithmeticControlFile (regValue liveValue writeValue write_defined)
open ArithmeticControlBisim (Row sem)
open ArithmeticControlTable (write reg_write_same reg_write_other file_ext)
open ArithmeticDagLoops (lreg_lupd_same lreg_lupd_other lupd_lreg lupd_write lupd_lupd lupd_comm
  one_le_of_pos)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section Defs
variable (p : Prog) (rows : Nat → Option Row) (run : V → V → V)

/-- `Reach` with the clock bounded by `B`. -/
def ReachB (c : Nat) (E : Exit → Nat) (x : V) (X : Exit) (y : V) (B : V) : Prop :=
  match X with
  | .halt => ∃ t ≤ B, run t (liveValue (c : V) x) = 0
  | X => ∃ t ≤ B, run t (liveValue (c : V) x) = liveValue ((E X : Nat) : V) y

/-- `IRun` with the clock bounded by `B` at every occurrence. -/
def IRunB (e : RMDag.Edge) (x : V) (X : Exit) (y : V) (B : V) : Prop :=
  ∀ f c E, Occ p rows f e c E → ReachB run c E x X y B
end Defs

variable {p : Prog} {rows : Nat → Option Row} {step : V → V} {run : V → V → V}

theorem reachB_mono {c : Nat} {E : Exit → Nat} {x y B B' : V} {X : Exit}
    (h : ReachB run c E x X y B) (hB : B ≤ B') : ReachB run c E x X y B' := by
  cases X <;> obtain ⟨t, ht, h⟩ := h <;> exact ⟨t, le_trans ht hB, h⟩

theorem irunB_mono {e : RMDag.Edge} {x y B B' : V} {X : Exit}
    (h : IRunB p rows run e x X y B) (hB : B ≤ B') : IRunB p rows run e x X y B' :=
  fun f c E ho => reachB_mono (h f c E ho) hB

theorem reach_of_reachB {c : Nat} {E : Exit → Nat} {x y B : V} {X : Exit}
    (h : ReachB run c E x X y B) : Reach run c E x X y := by
  cases X <;> obtain ⟨t, _, h⟩ := h <;> exact ⟨t, h⟩

/-- Forgetting the bound recovers the accepted semantics. -/
theorem irun_of_irunB {e : RMDag.Edge} {x y B : V} {X : Exit}
    (h : IRunB p rows run e x X y B) : IRun p rows run e x X y :=
  fun f c E ho => reach_of_reachB (h f c E ho)

variable (run_zero : ∀ x, run 0 x = x)
  (run_add : ∀ t u x, run (t+u) x = run u (run t x))
  (run_one : ∀ x, run 1 x = step x)
  (spec : ∀ (c : Nat) (row : Row) (x : V), rows c = some row →
    step (liveValue (c : V) x) = sem regValue write liveValue row x)

include run_add run_one spec

/-! ## Leaves: one instruction each -/

omit run_add in
theorem run_incB (r : Nat) (x : V) :
    IRunB p rows run (.inc r) x .normal (lupd x r (lreg x r + 1)) 1 := by
  intro f c E h
  cases f with
  | zero => exact h.elim
  | succ f =>
    obtain ⟨_, hc⟩ := h
    refine ⟨1, le_rfl, ?_⟩
    rw [leaf_step run_one spec (.inc r) c E _ rfl hc]
    simp [sem, lupd, lreg]

omit run_add in
theorem run_decPosB (r : Nat) (x v : V) (hv : lreg x r = v + 1) :
    IRunB p rows run (.decnz r) x .normal (lupd x r v) 1 := by
  intro f c E h
  cases f with
  | zero => exact h.elim
  | succ f =>
    obtain ⟨_, hc⟩ := h
    refine ⟨1, le_rfl, ?_⟩
    rw [leaf_step run_one spec (.decnz r) c E _ rfl hc]
    have hne : regValue x (phys r) ≠ 0 := by
      change lreg x r ≠ 0; rw [hv]; exact Arithmetic.succ_ne_zero v
    simp only [sem, show (2 : Nat) ≠ 1 by decide, if_false, if_true, hne]
    simp only [lupd, lreg] at hv ⊢
    rw [hv, add_tsub_cancel_right]

omit run_add in
theorem run_decZeroB (r : Nat) (x : V) (hz : lreg x r = 0) :
    IRunB p rows run (.decnz r) x (.brk 1) x 1 := by
  intro f c E h
  cases f with
  | zero => exact h.elim
  | succ f =>
    obtain ⟨_, hc⟩ := h
    refine ⟨1, le_rfl, ?_⟩
    rw [leaf_step run_one spec (.decnz r) c E _ rfl hc]
    have hz' : regValue x (phys r) = 0 := hz
    simp [sem, hz']

omit run_add in
theorem run_brk0B (x : V) : IRunB p rows run (.brk 0) x .normal x 1 := by
  intro f c E h
  cases f with
  | zero => exact h.elim
  | succ f =>
    obtain ⟨_, hc⟩ := h
    exact ⟨1, le_rfl, by rw [leaf_step run_one spec (.brk 0) c E _ rfl hc]; simp [sem]⟩

omit run_add in
theorem run_brkSB (k : Nat) (x : V) : IRunB p rows run (.brk (k+1)) x (.brk (k+1)) x 1 := by
  intro f c E h
  cases f with
  | zero => exact h.elim
  | succ f =>
    obtain ⟨_, hc⟩ := h
    exact ⟨1, le_rfl, by rw [leaf_step run_one spec (.brk (k+1)) c E _ rfl hc]; simp [sem]⟩

omit run_add in
theorem run_contSB (k : Nat) (x : V) : IRunB p rows run (.cont (k+1)) x (.cont (k+1)) x 1 := by
  intro f c E h
  cases f with
  | zero => exact h.elim
  | succ f =>
    obtain ⟨_, hc⟩ := h
    exact ⟨1, le_rfl, by rw [leaf_step run_one spec (.cont (k+1)) c E _ rfl hc]; simp [sem]⟩

omit run_add in
theorem run_haltB (x : V) : IRunB p rows run .halt x .halt x 1 := by
  intro f c E h
  cases f with
  | zero => exact h.elim
  | succ f =>
    obtain ⟨_, hc⟩ := h
    exact ⟨1, le_rfl, by rw [leaf_step run_one spec .halt c E _ rfl hc]; simp [sem]⟩

/-! ## Composition -/

omit run_one spec in
theorem reachB_trans {c₁ c₂ : Nat} {x y : V} {t₁ B₁ : V} (ht : t₁ ≤ B₁)
    (h₁ : run t₁ (liveValue (c₁ : V) x) = liveValue (c₂ : V) y) {E : Exit → Nat} {X : Exit}
    {z B₂ : V} (h₂ : ReachB run c₂ E y X z B₂) : ReachB run c₁ E x X z (B₁ + B₂) := by
  cases X <;> obtain ⟨t, h, ht'⟩ := h₂ <;>
    exact ⟨t₁ + t, _root_.add_le_add ht h, by rw [run_add, h₁, ht']⟩

omit run_one spec in
private theorem run_cdrB_core {n : Nat} {a b : RMDag.Edge} (hn : p.nodes n = (a, b))
    {x y z A B : V} {X Y : Exit}
    (ha : IRunB p rows run a x .normal y A) (hb : IRunB p rows run b y X z B)
    (relabel : ∀ c d E, ReachB run d (cdrExit c E) y X z B → ReachB run d E y Y z B) :
    IRunB p rows run (.node n) x Y z (A + B) := by
  intro f c E h
  obtain ⟨f', rfl, hca, hcd⟩ := occ_node h
  simp only [hn] at hca hcd
  obtain ⟨t₁, ht₁, h₁⟩ := ha f' c (carExit c (size p f' a) E) hca
  exact reachB_trans run_add (c₂ := c + size p f' a) ht₁ h₁
    (relabel c _ E (hb f' (c + size p f' a) (cdrExit c E) hcd))

omit run_add run_one spec in
private theorem run_carB_core {n : Nat} {a b : RMDag.Edge} (hn : p.nodes n = (a, b))
    {x y A : V} {X Y : Exit} (ha : IRunB p rows run a x X y A)
    (relabel : ∀ c d E, ReachB run c (carExit c d E) x X y A → ReachB run c E x Y y A) :
    IRunB p rows run (.node n) x Y y A := by
  intro f c E h
  obtain ⟨f', rfl, hca, _⟩ := occ_node h
  simp only [hn] at hca
  exact relabel c (size p f' a) E (ha f' c (carExit c (size p f' a) E) hca)

omit run_one spec in
theorem run_seqB {n : Nat} {a b : RMDag.Edge} (hn : p.nodes n = (a, b)) {x y z A B : V}
    (ha : IRunB p rows run a x .normal y A) (hb : IRunB p rows run b y .normal z B) :
    IRunB p rows run (.node n) x .normal z (A + B) := by
  exact run_cdrB_core run_add hn ha hb (fun _ _ _ h => h)

omit run_add run_one spec in
theorem run_skipB {n : Nat} {a b : RMDag.Edge} (hn : p.nodes n = (a, b)) {x y A : V}
    (ha : IRunB p rows run a x (.brk 1) y A) : IRunB p rows run (.node n) x .normal y A := by
  exact run_carB_core hn ha (fun _ _ _ h => h)

omit run_add run_one spec in
theorem run_halt_carB {n : Nat} {a b : RMDag.Edge} (hn : p.nodes n = (a, b)) {x y A : V}
    (ha : IRunB p rows run a x .halt y A) : IRunB p rows run (.node n) x .halt y A := by
  exact run_carB_core hn ha (fun _ _ _ h => h)

omit run_one spec in
theorem run_halt_cdrB {n : Nat} {a b : RMDag.Edge} (hn : p.nodes n = (a, b)) {x y z A B : V}
    (ha : IRunB p rows run a x .normal y A) (hb : IRunB p rows run b y .halt z B) :
    IRunB p rows run (.node n) x .halt z (A + B) := by
  exact run_cdrB_core run_add hn ha hb (fun _ _ _ h => h)

omit run_one spec in
theorem run_brk_cdrB {n k : Nat} {a b : RMDag.Edge} (hn : p.nodes n = (a, b)) {x y z A B : V}
    (ha : IRunB p rows run a x .normal y A) (hb : IRunB p rows run b y (.brk (k+1)) z B) :
    IRunB p rows run (.node n) x (.brk (k+1)) z (A + B) := by
  exact run_cdrB_core run_add hn ha hb (fun _ _ _ h => h)

omit run_add run_one spec in
theorem run_brk_carB {n k : Nat} {a b : RMDag.Edge} (hn : p.nodes n = (a, b)) {x y A : V}
    (ha : IRunB p rows run a x (.brk (k+2)) y A) :
    IRunB p rows run (.node n) x (.brk (k+1)) y A := by
  exact run_carB_core hn ha (fun _ _ _ h => h)

omit run_add run_one spec in
theorem run_cont_carB {n k : Nat} {a b : RMDag.Edge} (hn : p.nodes n = (a, b)) {x y A : V}
    (ha : IRunB p rows run a x (.cont (k+1)) y A) :
    IRunB p rows run (.node n) x (.cont (k+1)) y A := by
  exact run_carB_core hn ha (fun _ _ _ h => h)

omit run_one spec in
theorem run_cont_cdrB {n k : Nat} {a b : RMDag.Edge} (hn : p.nodes n = (a, b)) {x y z A B : V}
    (ha : IRunB p rows run a x .normal y A) (hb : IRunB p rows run b y (.cont (k+2)) z B) :
    IRunB p rows run (.node n) x (.cont (k+1)) z (A + B) := by
  exact run_cdrB_core run_add hn ha hb (fun _ _ _ h => h)

omit run_one spec in
theorem run_restartB {n : Nat} {a b : RMDag.Edge} (hn : p.nodes n = (a, b)) {x y z w A B C : V}
    {X : Exit} (ha : IRunB p rows run a x .normal y A) (hb : IRunB p rows run b y (.cont 1) z B)
    (hrest : IRunB p rows run (.node n) z X w C) :
    IRunB p rows run (.node n) x X w (A + B + C) := by
  intro f c E h
  obtain ⟨f', hf, hca, hcd⟩ := occ_node h
  have h' := h
  subst hf
  simp only [hn] at hca hcd
  obtain ⟨t₁, ht₁, h₁⟩ := ha f' c (carExit c (size p f' a) E) hca
  obtain ⟨t₂, ht₂, h₂⟩ := hb f' (c + size p f' a) (cdrExit c E) hcd
  have h₁' : run t₁ (liveValue (c : V) x) = liveValue ((c + size p f' a : Nat) : V) y := h₁
  have h₂' : run t₂ (liveValue ((c + size p f' a : Nat) : V) y) = liveValue (c : V) z := h₂
  exact reachB_trans run_add (t₁ := t₁ + t₂) (_root_.add_le_add ht₁ ht₂)
    (by rw [run_add, h₁', h₂']) (hrest (f'+1) c E h')

section Iterate

variable [𝚺₁-Function₂[V] run]

omit run_one spec in
include run_zero in
/-- `run_iterate` with uniform per-pass bounds: `N` passes cost at most
`N * (A + B)`, followed by the final run. -/
theorem run_iterateB {n : Nat} {a b : RMDag.Edge} (hn : p.nodes n = (a, b))
    (G H : V → V) [𝚺₁-Function₁[V] G] (N A B : V)
    (hpass : ∀ t, t < N → IRunB p rows run a (G t) .normal (H t) A ∧
      IRunB p rows run b (H t) (.cont 1) (G (t+1)) B)
    {X : Exit} {y C : V} (hfin : IRunB p rows run (.node n) (G N) X y C) :
    IRunB p rows run (.node n) (G 0) X y (N * (A + B) + C) := by
  intro f c E h
  have hlive : 𝚺₁-Function₂[V] liveValue := ArithmeticControlFile.live_defined.to_definable
  have key : ∀ t, t ≤ N → ∃ s ≤ t * (A + B),
      run s (liveValue (c : V) (G 0)) = liveValue (c : V) (G t) := by
    intro t
    induction t using ISigma1.sigma1_succ_induction
    · definability
    case zero => intro _; exact ⟨0, by simp, run_zero _⟩
    case succ t ih =>
      intro ht
      have htN : t < N := lt_of_lt_of_le (lt_add_one t) ht
      obtain ⟨s, hs, hrs⟩ := ih (le_of_lt htN)
      obtain ⟨ha, hb⟩ := hpass t htN
      obtain ⟨f', hf, hca, hcd⟩ := occ_node h
      subst hf
      simp only [hn] at hca hcd
      obtain ⟨t₁, ht₁, h₁⟩ := ha f' c (carExit c (size p f' a) E) hca
      obtain ⟨t₂, ht₂, h₂⟩ := hb f' (c + size p f' a) (cdrExit c E) hcd
      have h₁' : run t₁ (liveValue (c : V) (G t)) =
          liveValue ((c + size p f' a : Nat) : V) (H t) := h₁
      have h₂' : run t₂ (liveValue ((c + size p f' a : Nat) : V) (H t)) =
          liveValue (c : V) (G (t+1)) := h₂
      refine ⟨s + t₁ + t₂, ?_, by rw [run_add, run_add, hrs, h₁', h₂']⟩
      calc s + t₁ + t₂ ≤ t * (A + B) + A + B :=
            _root_.add_le_add (_root_.add_le_add hs ht₁) ht₂
        _ = (t + 1) * (A + B) := by ring
  obtain ⟨s, hs, hrs⟩ := key N le_rfl
  exact reachB_trans run_add hs hrs (hfin f c E h)

/-! ## The three generic loop shapes with linear clocks -/

local instance write_definable : 𝚺₁-Function₃[V] writeValue := write_defined.to_definable

include run_zero in
/-- `transfer`: `src` passes of three instructions, plus the final test. -/
theorem transferB {n m src dst : Nat} (hn : p.nodes n = (.decnz src, .node m))
    (hm : p.nodes m = (.inc dst, .cont 2)) (hsd : phys src ≠ phys dst) (x : V) :
    IRunB p rows run (.node n) x .normal (lupd (lupd x dst (lreg x dst + lreg x src)) src 0)
      (lreg x src * (1 + (1 + 1)) + 1) := by
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
  have hpass : ∀ t, t < lreg x src → IRunB p rows run (.decnz src) (G t) .normal (H t) 1 ∧
      IRunB p rows run (.node m) (H t) (.cont 1) (G (t+1)) (1 + 1) := by
    intro t ht
    refine ⟨run_decPosB run_one spec src (G t) (lreg x src - t - 1) ?_, ?_⟩
    · simp only [G, lreg_lupd_same]
      exact (tsub_add_cancel_of_le (one_le_of_pos (tsub_pos_of_lt ht))).symm
    · have hc := run_cont_cdrB run_add (k := 0) hm (run_incB run_one spec dst (H t))
        (run_contSB run_one spec 1 _)
      have key : lupd (H t) dst (lreg (H t) dst + 1) = G (t+1) := by
        simp only [H, G]
        rw [lreg_lupd_other _ _ _ _ hsd, lreg_lupd_other _ _ _ _ hsd, lreg_lupd_same, lupd_lupd,
          lupd_comm _ _ _ src dst hsd, lupd_lupd, add_assoc, tsub_tsub]
      rw [key] at hc
      exact hc
  have hfin : IRunB p rows run (.node n) (G (lreg x src)) .normal (G (lreg x src)) 1 :=
    run_skipB hn (run_decZeroB run_one spec src _ (by simp only [G, lreg_lupd_same, tsub_self]))
  have h := run_iterateB run_zero run_add hn G H (lreg x src) 1 (1 + 1) hpass hfin
  rw [hG0] at h
  simpa only [G, tsub_self] using h

include run_zero in
/-- `copy2`: `src` passes of four instructions, plus the final test. -/
theorem copy2B {n m m' src d1 d2 : Nat} (hn : p.nodes n = (.decnz src, .node m))
    (hm : p.nodes m = (.node m', .cont 2))
    (hm' : p.nodes m' = (.inc d1, .inc d2))
    (h1 : phys src ≠ phys d1) (h2 : phys src ≠ phys d2) (h12 : phys d1 ≠ phys d2) (x : V) :
    IRunB p rows run (.node n) x .normal
      (lupd (lupd (lupd x d1 (lreg x d1 + lreg x src)) d2 (lreg x d2 + lreg x src)) src 0)
      (lreg x src * (1 + (1 + 1 + 1)) + 1) := by
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
  have hpass : ∀ t, t < lreg x src → IRunB p rows run (.decnz src) (G t) .normal (H t) 1 ∧
      IRunB p rows run (.node m) (H t) (.cont 1) (G (t+1)) (1 + 1 + 1) := by
    intro t ht
    refine ⟨run_decPosB run_one spec src (G t) (lreg x src - t - 1) ?_, ?_⟩
    · simp only [G, lreg_lupd_same]
      exact (tsub_add_cancel_of_le (one_le_of_pos (tsub_pos_of_lt ht))).symm
    · have hin := run_seqB run_add hm' (run_incB run_one spec d1 (H t))
        (run_incB run_one spec d2 _)
      have hc := run_cont_cdrB run_add (k := 0) hm hin (run_contSB run_one spec 1 _)
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
  have hfin : IRunB p rows run (.node n) (G (lreg x src)) .normal (G (lreg x src)) 1 :=
    run_skipB hn (run_decZeroB run_one spec src _ (by simp only [G, lreg_lupd_same, tsub_self]))
  have h := run_iterateB run_zero run_add hn G H (lreg x src) 1 (1 + 1 + 1) hpass hfin
  rw [hG0] at h
  simpa only [G, tsub_self] using h

include run_zero in
/-- `clear`: `r` passes of two instructions, plus the final test. -/
theorem clearB {n r : Nat} (hn : p.nodes n = (.decnz r, .cont 1)) (x : V) :
    IRunB p rows run (.node n) x .normal (lupd x r 0) (lreg x r * (1 + 1) + 1) := by
  let G : V → V := fun t => lupd x r (lreg x r - t)
  haveI : 𝚺₁-Function₁[V] G := by
    simp only [G, lupd_write, lreg]
    definability
  have hG0 : G 0 = x := by simp only [G, tsub_zero]; exact lupd_lreg x r
  have hpass : ∀ t, t < lreg x r → IRunB p rows run (.decnz r) (G t) .normal (G (t+1)) 1 ∧
      IRunB p rows run (.cont 1) (G (t+1)) (.cont 1) (G (t+1)) 1 := by
    intro t ht
    refine ⟨?_, run_contSB run_one spec 0 _⟩
    have hd := run_decPosB (p := p) run_one spec r (G t) (lreg x r - t - 1) (by
      simp only [G, lreg_lupd_same]
      exact (tsub_add_cancel_of_le (one_le_of_pos (tsub_pos_of_lt ht))).symm)
    have key : lupd (G t) r (lreg x r - t - 1) = G (t+1) := by
      simp only [G, lupd_lupd, tsub_tsub]
    rw [key] at hd
    exact hd
  have hfin : IRunB p rows run (.node n) (G (lreg x r)) .normal (G (lreg x r)) 1 :=
    run_skipB hn (run_decZeroB run_one spec r _ (by simp only [G, lreg_lupd_same, tsub_self]))
  have h := run_iterateB run_zero run_add hn G (fun t => G (t+1)) (lreg x r) 1 1 hpass hfin
  rw [hG0] at h
  simpa only [G, tsub_self] using h

end Iterate

end DiophantineConsistency.ArithmeticRuntimeBoundDagRun
