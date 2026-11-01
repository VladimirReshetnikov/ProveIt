import DiophantineConsistency.ArithmeticUnaryRecursion
import DiophantineConsistency.ArithmeticWangPlane

/-! **K1 — the represented run with its absolute head** (construction spec §3,
Stage M), in every model of IΣ1.

`ArithmeticMachineRun215.run τ` codes the configuration `P(state, P(left, right))`
but not the absolute head column. Here a second primitive recursion
`hd o τ` carries it, starting at an arbitrary internal origin column `o`:
`hd o 0 = o` and `hd o (τ+1) = hstep (run τ) (hd o τ)`, where `hstep` moves the
column by the direction bit of the action looked up from `run τ` (unchanged when
the lookup is absent, i.e. after halting).

Exported facts (all internal, `τ, T, o` arbitrary and possibly nonstandard):
* `state_le` — every reached state code is at most `215`;
* `live_step` — an operating configuration steps by an explicit action
  `1+4·st'+2·d+w` with `st' ≤ 215`, `d, w ≤ 1`; the represented next
  configuration and the next head column are given in closed form;
* `halted_stable` — after a halt at `T`, configuration and head are frozen;
* `head_bounds`, `trace_head` — `|hd o τ - o| ≤ τ`, and after a halt at `T`
  every head column lies in `[o-T, o+T]` at every time;
* `run_one`, `hd_one` — the first blank step (state code 2, left half 1).

**Interface for K2.** The tiling word reads row `k` from `run k` and `hd L k`
with `L = T+2`; `live_step` together with `ArithmeticWangPlane.step_apply` and
the `tb_*` tape-reading lemmas give the row-to-row colour law, and `trace_head`
keeps the head columns inside `[2, 2T+2]`. The tape-half length bounds of the
classical trace box are not needed: band boundary columns only need the head
bounds, because pass tiles have blank side colours whatever their bit. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.ArithmeticRunTrace
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticWangTable ArithmeticWangPlane
open ArithmeticMachineRun215 (run run_succ run_zero runDef run_defined)
open ArithmeticMachinePerm252 ArithmeticMachineGraphPerm252

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The action read by a configuration and the head step -/

/-- The action code looked up for the scanned bit of configuration `c`
(`0` when the state code is `0` or invalid). -/
def act (c : V) : V :=
  ArithmeticMachineGraph215.actionLookup (first c) (second (second c) % 2)

/-- The head column after one step from configuration `c` at column `h`. -/
def hstep (c h : V) : V :=
  if act c = 0 then h else if (act c - 1) / 2 % 2 = 0 then h - 1 else h + 1

def hstepDef : 𝚺₁.Semisentence 3 := .mkSigma
  “out c h. ∃ s, !ArithmeticCantor.firstDef s c ∧ ∃ t, !ArithmeticCantor.secondDef t c ∧
    ∃ r, !ArithmeticCantor.secondDef r t ∧ ∃ b, !remDef b r 2 ∧
    ∃ A, !ArithmeticMachineGraph215.actionLookupDef A s b ∧
    ∃ z, !subDef z A 1 ∧ ∃ y, !divDef y z 2 ∧ ∃ m, !remDef m y 2 ∧ ∃ hm, !subDef hm h 1 ∧
    ((A = 0 ∧ out = h) ∨ (A ≠ 0 ∧ m = 0 ∧ out = hm) ∨ (A ≠ 0 ∧ m ≠ 0 ∧ out = h + 1))”

instance hstep_defined : 𝚺₁-Function₂[V] hstep via hstepDef := .mk fun e => by
  simp only [hstepDef, hstep, act]
  by_cases hA : ArithmeticMachineGraph215.actionLookup (first (e 1)) (second (second (e 1)) % 2) = 0
  · simp [hA]
  · by_cases hm : (ArithmeticMachineGraph215.actionLookup (first (e 1))
        (second (second (e 1)) % 2) - 1) / 2 % 2 = 0
    · simp [hA, hm]
    · have h1 := (mod_two _).resolve_left hm
      simp [hA, hm, h1]

instance hstep_definable : 𝚺₁-Function₂[V] hstep := hstep_defined.to_definable

theorem hstep_le (c h : V) : hstep c h ≤ h + 1 := by
  unfold hstep
  split_ifs <;> simp

theorem le_hstep (c h : V) : h ≤ hstep c h + 1 := by
  unfold hstep
  split_ifs <;> first | exact le_tsub_add | simp

/-! ## The head recursion -/

def zeroDef : 𝚺₁.Semisentence 2 := .mkSigma “out o. out = o”
def succDef : 𝚺₁.Semisentence 4 := .mkSigma
  “out previous index o. ∃ c, !runDef c index ∧ !hstepDef out c previous”
def blueprint : PR.Blueprint 1 where
  zero := zeroDef
  succ := succDef

noncomputable def construction : PR.Construction V blueprint where
  zero p := p 0
  succ _ index previous := hstep (run index) previous
  zero_defined := .mk fun e => by simp [blueprint, zeroDef]
  succ_defined := .mk fun e => by simp [blueprint, succDef]

/-- The absolute head column at time `τ`, from origin column `o`. -/
noncomputable def hd (o τ : V) : V := construction.result ![o] τ
def hdResultDef : 𝚺₁.Semisentence 3 := blueprint.resultDef
def hdDef : 𝚺₁.Semisentence 3 := .mkSigma “out o τ. !hdResultDef out τ o”

private theorem hd_result_defined :
    𝚺₁-Function₂[V] (fun τ o => hd o τ) via hdResultDef :=
  ArithmeticUnaryRecursion.result_defined blueprint construction

instance hd_defined : 𝚺₁-Function₂[V] hd via hdDef := .mk fun e => by
  have h := (hd_result_defined (V := V)).df ![e 0, e 2, e 1]
  simp [hdDef, h]
instance hd_definable : 𝚺₁-Function₂[V] hd := hd_defined.to_definable

@[simp] theorem hd_zero (o : V) : hd o 0 = o := by simp [hd, construction]
theorem hd_succ (o τ : V) : hd o (τ + 1) = hstep (run τ) (hd o τ) := by
  simp [hd, PR.Construction.result_succ, construction]

/-! ## Actions of reachable configurations -/

theorem bit_le (r : V) : r % 2 ≤ 1 :=
  le_one_iff_eq_zero_or_one.mpr (mod_two r)

/-- The looked-up action of an operating state code is a genuine action. -/
theorem act_spec {st b : V} (hst0 : st ≠ 0) (hst : st ≤ 215) (hb : b ≤ 1) :
    ∃ st' d w : V, st' ≤ 215 ∧ d ≤ 1 ∧ w ≤ 1 ∧
      ArithmeticMachineGraph215.actionLookup st b = 1 + 4 * st' + 2 * d + w := by
  obtain ⟨p, hp, rfl⟩ := standard_of_lt (n := 216) (i := st)
    (lt_of_le_of_lt hst (by simpa using (Nat.cast_lt (α := V)).mpr (by decide : (215 : ℕ) < 216)))
  obtain ⟨β, hβ, rfl⟩ := standard_of_lt (n := 2) (i := b)
    (lt_of_le_of_lt hb (by simpa using (Nat.cast_lt (α := V)).mpr (by decide : (1 : ℕ) < 2)))
  have hp0 : p ≠ 0 := by rintro rfl; exact hst0 (by simp)
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  obtain ⟨c, d, w, hc, hd, hw, hA⟩ := actCode_spec (2 * q + β)
  refine ⟨(c : V), (d : V), (w : V), by exact_mod_cast hc, by exact_mod_cast hd,
    by exact_mod_cast hw, ?_⟩
  have h := lookupValue_cast (V := V) ArithmeticMachineGraph215.literalRows 0 (q + 1) β
  rw [lookup_eq_actCode q β (by omega) (by omega), hA] at h
  simp only [ArithmeticMachineGraph215.actionLookup]
  rw [h]; push_cast; ring

/-- The lookup at the halt code is absent. -/
theorem act_halted {c : V} (h : first c = 0) : act c = 0 := by
  obtain ⟨β, -, hβ⟩ := standard_of_lt (n := 2) (i := second (second c) % 2)
    (lt_of_le_of_lt (bit_le _) (by simpa using (Nat.cast_lt (α := V)).mpr (by decide : (1 : ℕ) < 2)))
  have hl := lookupValue_cast (V := V) ArithmeticMachineGraph215.literalRows 0 0 β
  rw [ArithmeticMachineStep215.lookup_zero] at hl
  simp only [act, ArithmeticMachineGraph215.actionLookup, h, hβ]
  simpa using hl

/-- Decoding the action fields of `1+4st'+2d+w`. -/
theorem action_fields {st' d w : V} (hd : d ≤ 1) (hw : w ≤ 1) :
    (1 + 4 * st' + 2 * d + w - 1) / 2 % 2 = d := by
  have hz : 1 + 4 * st' + 2 * d + w - 1 = 2 * (2 * st' + d) + w := by
    rw [show 1 + 4 * st' + 2 * d + w = (2 * (2 * st' + d) + w) + 1 by ring, add_tsub_cancel_right]
  have hw2 : w < 2 := lt_of_le_of_lt hw (by norm_num)
  have hd2 : d < 2 := lt_of_le_of_lt hd (by norm_num)
  rw [hz, div_mul_add' _ 2 hw2, mod_mul_add' _ _ (by norm_num : (0:V) < 2), mod_eq_self_of_lt hd2]

/-- One operating step of the represented run, with its head column. -/
theorem live_step (o τ : V) (hst0 : first (run τ) ≠ 0) (hst : first (run τ) ≤ 215) :
    ∃ st' d w : V, st' ≤ 215 ∧ d ≤ 1 ∧ w ≤ 1 ∧
      act (run τ) = 1 + 4 * st' + 2 * d + w ∧
      run (τ + 1) =
        (if d = 0 then
          cantor st' (cantor (first (second (run τ)) / 2)
            (first (second (run τ)) % 2 + 2 * (w + 2 * (second (second (run τ)) / 2))))
        else cantor st' (cantor (2 * first (second (run τ)) + w) (second (second (run τ)) / 2))) ∧
      hd o (τ + 1) = (if d = 0 then hd o τ - 1 else hd o τ + 1) := by
  obtain ⟨st', d, w, hst', hd1, hw1, hA⟩ := act_spec hst0 hst (bit_le (second (second (run τ))))
  refine ⟨st', d, w, hst', hd1, hw1, hA, ?_, ?_⟩
  · rw [run_succ]; exact step_apply _ st' d w hd1 hw1 hA
  · have hpos : (0 : V) < 1 + 4 * st' + 2 * d + w := by positivity
    have hA' : act (run τ) = 1 + 4 * st' + 2 * d + w := hA
    rw [hd_succ, hstep, hA', if_neg (ne_of_gt hpos), action_fields hd1 hw1]

/-- An absent action leaves the configuration unchanged. -/
theorem step_of_act_zero {c : V} (h : act c = 0) : ArithmeticMachineStep215.stepValue c = c := by
  unfold ArithmeticMachineStep215.stepValue ArithmeticMachineStepPerm252.genericStepValue
  exact if_pos h

theorem step_halted' {c : V} (h : first c = 0) : ArithmeticMachineStep215.stepValue c = c :=
  step_of_act_zero (act_halted h)

/-- Every reached state code is at most `215`. -/
theorem state_le (τ : V) : first (run τ) ≤ 215 := by
  induction τ using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    have h1 : (1 : V) = cantor 1 (cantor 0 0) := by
      simp [cantor, triangle, one_add_one_eq_two, Arithmetic.div_self (by norm_num : (0:V) < 2)]
    rw [run_zero, h1, first_cantor]; norm_num
  case succ τ ih =>
    by_cases h0 : first (run τ) = 0
    · rw [run_succ, step_halted' h0]; exact ih
    · obtain ⟨st', d, w, hst', -, -, -, hr, -⟩ := live_step 0 τ h0 ih
      rw [hr]; split <;> simpa using hst'

/-- A halted configuration and its head are frozen. -/
theorem halted_step (o τ : V) (h : first (run τ) = 0) :
    run (τ + 1) = run τ ∧ hd o (τ + 1) = hd o τ := by
  refine ⟨by rw [run_succ, step_halted' h], ?_⟩
  rw [hd_succ, hstep, if_pos (act_halted h)]

theorem halted_stable (o T : V) (hT : first (run T) = 0) (i : V) :
    run (T + i) = run T ∧ hd o (T + i) = hd o T := by
  induction i using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ i ih =>
    have h' : first (run (T + i)) = 0 := by rw [ih.1]; exact hT
    obtain ⟨e1, e2⟩ := halted_step o (T + i) h'
    simpa only [← add_assoc, e1, e2] using ih

theorem halted_stable_le (o T τ : V) (hT : first (run T) = 0) (hτ : T ≤ τ) :
    run τ = run T ∧ hd o τ = hd o T := by
  obtain ⟨i, rfl⟩ : ∃ i, τ = T + i := ⟨τ - T, (add_tsub_cancel_of_le hτ).symm⟩
  exact halted_stable o T hT i

/-! ## Head bounds -/

/-- `o - τ ≤ hd o τ ≤ o + τ`. -/
theorem head_bounds (o τ : V) : o ≤ hd o τ + τ ∧ hd o τ ≤ o + τ := by
  induction τ using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ τ ih =>
    rw [hd_succ]
    refine ⟨?_, ?_⟩
    · exact le_trans ih.1 (by simpa only [add_assoc, add_comm, add_left_comm] using
        (add_le_add (le_hstep (run τ) (hd o τ)) (le_refl τ)))
    · exact le_trans (hstep_le _ _) (by simpa only [add_assoc, add_comm, add_left_comm] using add_le_add_right ih.2 1)

/-- **Trace box of the head.** After a halt at `T`, every head column at every
time lies in `[o-T, o+T]`. -/
theorem trace_head (o T : V) (hT : first (run T) = 0) (τ : V) :
    o ≤ hd o τ + T ∧ hd o τ ≤ o + T := by
  rcases le_total τ T with h | h
  · obtain ⟨b1, b2⟩ := head_bounds o τ
    exact ⟨le_trans b1 (add_le_add le_rfl h), le_trans b2 (add_le_add le_rfl h)⟩
  · rw [(halted_stable_le o T τ hT h).2]
    exact head_bounds o T

/-! ## The first blank step -/

theorem cantor_zero_zero' : cantor (0 : V) 0 = 0 := by
  simp [cantor, triangle]

theorem cantor_one_zero' : cantor (1 : V) 0 = 1 := by
  have h2 : (2 : V) / 2 = 1 := Arithmetic.div_self (by norm_num)
  simp [cantor, triangle, one_add_one_eq_two, h2]

theorem actCode_zero' : actCode 0 = 12 := by decide +kernel

/-- The first action from the blank tape: write 1, move right, state code 2. -/
theorem act_zero : act (run (0 : V)) = 1 + 4 * 2 + 2 * 1 + 1 := by
  simpa only [run_zero, act] using (ArithmeticWangPlane.initial_action (V := V))

/-- The configuration after the first blank step: state code 2, left half 1,
right half 0. -/
theorem run_one : run (1 : V) = cantor 2 (cantor 1 0) :=
  ArithmeticWangPlane.initial_run_one

theorem hd_one (o : V) : hd o 1 = o + 1 := by
  have h := hd_succ o 0
  rw [zero_add, hd_zero, hstep, act_zero, if_neg (by positivity),
    action_fields (by norm_num) (by norm_num), if_neg _root_.one_ne_zero] at h
  exact h

end DiophantineConsistency.ArithmeticRunTrace
