import PA195ZipTable
import PA195DenseBinding
import PA195Bounded
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA195ZipBridge
open PA195LocalQuotient
open List.Vector

theorem lookup_outside (q : Nat) (b : Bool) (h : 195 ≤ q) : lookup dense q b = none := by
  cases hr : lookup dense q b with
  | none => rfl
  | some r =>
    have hm : r ∈ dense := List.mem_of_find?_eq_some hr
    have hrq : r.state = q := by
      have hmatch := List.find?_some hr
      have hh : r.state = q ∧ r.read = b := by
        simpa [lookup, Bool.and_eq_true, beq_iff_eq] using hmatch
      exact hh.1
    have hg := (List.all_eq_true.mp dense_control_certificate.1) r hm
    have hbound : r.state < 195 ∧ r.target ≤ 195 := by
      simpa [denseRowGood, Bool.and_eq_true] using hg
    omega

/-- The table used by the quotient is exactly the generated literal machine. -/
theorem lookup_literal (q : Nat) (b : Bool) :
    (lookup dense q b).map rowTriple = PA195.Literal.machine q b := by
  by_cases hq : q < 195
  · simpa [PA195.Literal.machine, hq] using all_literal_rows ⟨q, hq⟩ b
  · have hn : 195 ≤ q := by omega
    simp [PA195.Literal.machine, hq, lookup_outside q b hn]

theorem read_head (a : Configuration) (z : M6.Zip.Conf) (h : Related a z) :
    a.tape a.pos = z.r.headD false := by
  have h0 := h.2 0
  have heq : z.r.getD 0 false = z.r.headD false := by cases z.r <;> rfl
  change a.tape (a.pos + 0) = z.r.getD 0 false at h0
  have h0' : a.tape a.pos = z.r.getD 0 false := by simpa using h0
  exact h0'.trans heq

def Sync (a : Option Configuration) (z : Option M6.Zip.Conf) : Prop :=
  match a, z with
  | none, none => True
  | some a, some z => Related a z
  | _, _ => False

/-- A zipper step and a full-tape step either both stop or both move to
related full configurations. -/
theorem step_sync (a : Configuration) (z : M6.Zip.Conf) (h : Related a z) :
    Sync (fullStep dense a) (M6.Zip.step PA195.Literal.machine z) := by
  have he : a.state = z.q := h.1
  have hb : a.tape a.pos = z.r.headD false := read_head a z h
  have ht := lookup_literal a.state (a.tape a.pos)
  cases hr : lookup dense a.state (a.tape a.pos) with
  | none =>
    have hm : PA195.Literal.machine z.q (z.r.headD false) = none := by
      rw [hr] at ht
      rw [he, hb] at ht
      simpa only [Option.map_none] using ht.symm
    simp only [Sync, fullStep, hr, M6.Zip.step, hm]
    trivial
  | some r =>
    have hm : PA195.Literal.machine z.q (z.r.headD false) = some (rowTriple r) := by
      rw [hr] at ht
      rw [he, hb] at ht
      simpa only [Option.map_some] using ht.symm
    cases r with
    | mk state read write right target =>
      cases right <;>
        simp only [Sync, fullStep, hr, M6.Zip.step, hm, rowTriple] <;>
        exact related_advance a z h write _ target

/-- Finite full-tape and zipper executions agree for every standard clock. -/
theorem run_sync (n : Nat) (a : Configuration) (z : M6.Zip.Conf) (h : Related a z) :
    Sync (fullRun dense n a) (M6.Zip.run PA195.Literal.machine n z) := by
  induction n generalizing a z with
  | zero => exact h
  | succ n ih =>
    have hs := step_sync a z h
    cases ha : fullStep dense a with
    | none =>
      cases hz : M6.Zip.step PA195.Literal.machine z with
      | none => simp [fullRun, M6.Zip.run, ha, hz, Sync]
      | some z' => simp [ha, hz, Sync] at hs
    | some a' =>
      cases hz : M6.Zip.step PA195.Literal.machine z with
      | none => simp [ha, hz, Sync] at hs
      | some z' =>
        have hrel : Related a' z' := by simpa [ha, hz, Sync] using hs
        simpa [fullRun, M6.Zip.run, ha, hz] using ih a' z' hrel

theorem generic_eq_fullRun (rows : List Row) (n : Nat) (c : Configuration) :
    PA195GenericTrace.run (fullStep rows) n c = fullRun rows n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [PA195GenericTrace.run, fullRun]
    cases hs : fullStep rows c with
    | none => rfl
    | some d => simpa [hs] using ih d

/-- A generated literal zipper is stuck exactly outside its 195 working labels. -/
theorem literal_stuck_iff (z : M6.Zip.Conf) :
    M6.Zip.step PA195.Literal.machine z = none ↔ 195 ≤ z.q := by
  by_cases hq : z.q < 195
  · have hm : PA195.Literal.machine z.q (z.r.headD false) =
        some (PA195.Literal.transition z.q (z.r.headD false)) := by
      simp [PA195.Literal.machine, hq]
    have hne : M6.Zip.step PA195.Literal.machine z ≠ none := by
      simp only [M6.Zip.step, hm]
      rcases ht : PA195.Literal.transition z.q (z.r.headD false) with ⟨w,d,q⟩
      cases d <;> simp
    constructor
    · exact fun h => False.elim (hne h)
    · intro h; omega
  · have hn : 195 ≤ z.q := by omega
    have hm : PA195.Literal.machine z.q (z.r.headD false) = none := by
      simp [PA195.Literal.machine, hq]
    simp only [M6.Zip.step, hm]
    simp [hn]

/-- Every defined dense run starting at a valid control ends at a valid control. -/
theorem dense_run_valid (n : Nat) (a b : Configuration) (hv : denseValid a)
    (h : fullRun dense n a = some b) : denseValid b := by
  induction n generalizing a with
  | zero =>
    simp only [fullRun, Option.some.injEq] at h
    subst b
    exact hv
  | succ n ih =>
    cases hs : fullStep dense a with
    | none => simp [fullRun, hs] at h
    | some c =>
      have hc : denseValid c := dense_step_valid a c hs
      have hr : fullRun dense n c = some b := by simpa [fullRun, hs] using h
      exact ih c hc hr

/-- Synchronized finite runs and the valid-control invariant identify
halting in the two full-tape and finite-support zipper representations. -/
theorem halts_full_iff_zip (a : Configuration) (z : M6.Zip.Conf)
    (hrel : Related a z) (hv : denseValid a) :
    PA195GenericTrace.Halts (fullStep dense) (fun c => c.state = 195) a ↔
      M6.Zip.Halts PA195.Literal.machine z := by
  constructor
  · rintro ⟨n, b, hb, hhalt⟩
    rw [generic_eq_fullRun] at hb
    have hs := run_sync n a z hrel
    cases hz : M6.Zip.run PA195.Literal.machine n z with
    | none => simp [hb, hz, Sync] at hs
    | some z' =>
      have hrel' : Related b z' := by simpa [hb, hz, Sync] using hs
      have heq : b.state = z'.q := hrel'.1
      have hzstate : z'.q = 195 := by omega
      exact ⟨z', ⟨n, hz⟩, (literal_stuck_iff z').2 (by omega)⟩
  · rintro ⟨z', ⟨n, hz⟩, hhalt⟩
    have hs := run_sync n a z hrel
    cases hb : fullRun dense n a with
    | none => simp [hb, hz, Sync] at hs
    | some b =>
      have hrel' : Related b z' := by simpa [hb, hz, Sync] using hs
      have hv' := dense_run_valid n a b hv hb
      have hge := (literal_stuck_iff z').1 hhalt
      have heq : b.state = z'.q := hrel'.1
      have hstate : b.state = 195 := by unfold denseValid at hv'; omega
      exact ⟨n, b, by rw [generic_eq_fullRun]; exact hb, hstate⟩

def blankFull : Configuration := ⟨0, 0, fun _ => false⟩

theorem blank_related : Related blankFull PA195Bounded.blankZip := by
  refine ⟨rfl, ?_⟩
  intro i
  cases i <;> rfl

/-- The quotient's dense full-tape run has exactly the literal blank-tape
halting meaning used by PA195Bounded. -/
theorem blank_full_iff_zip :
    PA195GenericTrace.Halts (fullStep dense) (fun c => c.state = 195) blankFull ↔
      M6.Zip.Halts PA195.Literal.machine PA195Bounded.blankZip :=
  halts_full_iff_zip blankFull PA195Bounded.blankZip blank_related (by change 0 ≤ 195; decide)

/-- This is only the standard-natural-number meaning of the selected bounded
function code, not an iPRA or all-model equivalence. -/
theorem bounded_code_iff_full :
    (∃ n, DiophantineConsistency.PRAFiniteFunctionCodes.eval PA195Bounded.boundedCode
      (n ::ᵥ List.Vector.nil) = 1) ↔
    PA195GenericTrace.Halts (fullStep dense) (fun c => c.state = 195) blankFull := by
  exact PA195Bounded.code_halts_iff_literal.trans blank_full_iff_zip.symm

#print axioms bounded_code_iff_full
#print axioms blank_full_iff_zip
#print axioms lookup_literal
#print axioms run_sync
end PA195ZipBridge
