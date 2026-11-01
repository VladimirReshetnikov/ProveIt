import BusyBeaver.ZFC.ArithmeticCantor
import Foundation.FirstOrder.Arithmetic.HFS.PRF

/-!
Represented iteration of the actual Cantor stream tail. Every stream and
iteration index may be internal to an IΣ1 model. Positive tails strictly
decrease, so all positions beyond the stream's numeric code read zero.
This supplies a finite bound for theorem-stack certification; no proof-stack
invariant, scheduler soundness or consistency endpoint is assumed or claimed.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticStackTail254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def zeroDef : 𝚺₁.Semisentence 2 := .mkSigma “out initial. out = initial”
def succDef : 𝚺₁.Semisentence 4 := .mkSigma
  “out previous index initial. !ArithmeticCantor.secondDef out previous”
def blueprint : PR.Blueprint 1 where
  zero := zeroDef
  succ := succDef
noncomputable def construction : PR.Construction V blueprint where
  zero parameters := parameters 0
  succ _ _ previous := second previous
  zero_defined := .mk fun e => by simp [blueprint, zeroDef]
  succ_defined := .mk fun e => by simp [blueprint, succDef]

/-- Arguments are number of tails first, initial stream second. -/
noncomputable def tailIter (time initial : V) : V := construction.result ![initial] time

def tailDef : 𝚺₁.Semisentence 3 := blueprint.resultDef
def tailDeltaDef : 𝚫₁.Semisentence 3 := blueprint.resultDeltaDef
instance tail_defined : 𝚺₁-Function₂[V] tailIter via tailDef := .mk fun e => by
  have he : (fun i : Fin 1 => e i.succ.succ) = ![e 2] := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  have h := (construction (V := V)).result_defined.df e
  change blueprint.resultDef.val.Evalb e ↔
    e 0 = construction.result (fun i : Fin 1 => e i.succ.succ) (e 1) at h
  rw [he] at h
  change blueprint.resultDef.val.Evalb e ↔ e 0 = construction.result ![e 2] (e 1)
  exact h
instance tail_defined_delta : 𝚫₁-Function₂[V] tailIter via tailDeltaDef :=
  tail_defined.graph_delta
instance tail_definable : 𝚺₁-Function₂[V] tailIter := tail_defined.to_definable
instance tail_definable_delta : 𝚫₁-Function₂[V] tailIter := tail_defined_delta.to_definable

@[simp] theorem tail_zero (initial : V) : tailIter 0 initial = initial := by
  simp [tailIter, construction]
@[simp] theorem tail_succ (time initial : V) :
    tailIter (time + 1) initial = second (tailIter time initial) := by
  simp [tailIter, PR.Construction.result_succ, construction]

@[simp] theorem first_zero : first (0 : V) = 0 := by
  simpa [cantor, triangle] using first_cantor (0 : V) 0
@[simp] theorem second_zero : second (0 : V) = 0 := by
  simpa [cantor, triangle] using second_cantor (0 : V) 0

/-- A positive Cantor stream cannot retain its numeric code after a tail. -/
theorem second_lt (z : V) (hz : z ≠ 0) : second z < z := by
  have hne : first z + second z ≠ 0 := by
    intro hs
    have ha := (add_eq_zero.mp hs).1
    have hb := (add_eq_zero.mp hs).2
    apply hz
    calc
      z = cantor (first z) (second z) := (cantor_projections z).symm
      _ = 0 := by simp [ha, hb, cantor, triangle]
  have hs : 0 < first z + second z :=
    lt_of_le_of_ne (Arithmetic.zero_le _) (Ne.symm hne)
  have ht : 0 < triangle (first z + second z) := lt_of_lt_of_le hs (le_triangle _)
  calc
    second z < triangle (first z + second z) + second z := by
      simpa only [zero_add, add_zero, add_comm] using _root_.add_lt_add_right ht (second z)
    _ = z := cantor_projections z

@[simp] theorem tail_zero_stream (time : V) : tailIter time 0 = 0 := by
  induction time using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ time ih => rw [tail_succ, ih, second_zero]

/-- All parameters other than the induction time are fixed. -/
theorem tail_add (first second initial : V) :
    tailIter (first + second) initial = tailIter second (tailIter first initial) := by
  induction second using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ second ih => rw [← add_assoc, tail_succ, tail_succ, ih]

theorem tail_shift (time initial : V) :
    tailIter (time + 1) initial = tailIter time (second initial) := by
  have h1 : tailIter (1 : V) initial = second initial := by
    simpa only [zero_add, tail_zero] using tail_succ (0 : V) initial
  calc
    tailIter (time + 1) initial = tailIter (1 + time) initial := by rw [add_comm]
    _ = tailIter time (tailIter 1 initial) := tail_add 1 time initial
    _ = tailIter time (second initial) := by rw [h1]

@[simp] theorem tail_cantor (time x z : V) :
    tailIter (time + 1) (cantor x z) = tailIter time z := by
  rw [tail_shift, second_cantor]

/-- Pointwise Sigma1 induction; the initial stream stays fixed. -/
theorem tail_bound (time initial : V) :
    tailIter time initial = 0 ∨ tailIter time initial + time ≤ initial := by
  induction time using ISigma1.sigma1_succ_induction
  · definability
  case zero => right; simp
  case succ time ih =>
    rcases ih with hz | hb
    · left; rw [tail_succ, hz, second_zero]
    · by_cases hz : tailIter time initial = 0
      · left; rw [tail_succ, hz, second_zero]
      · right
        have hdec : second (tailIter time initial) + 1 ≤ tailIter time initial :=
          lt_iff_succ_le.mp (second_lt _ hz)
        calc
          tailIter (time + 1) initial + (time + 1) =
              (second (tailIter time initial) + 1) + time := by
                rw [tail_succ]
                simp only [add_assoc, add_comm]
          _ ≤ tailIter time initial + time := _root_.add_le_add hdec le_rfl
          _ ≤ initial := hb

/-- Every internal offset at or beyond the numeric stream code is zero. -/
theorem tail_eq_zero_of_le (time initial : V) (hle : initial ≤ time) :
    tailIter time initial = 0 := by
  rcases tail_bound time initial with hz | hb
  · exact hz
  · have hh : tailIter time initial + time ≤ 0 + time := by
      simpa only [zero_add] using le_trans hb hle
    exact le_antisymm ((add_le_add_iff_right time).mp hh) (Arithmetic.zero_le _)

theorem tail_total (time initial : V) : ∃! out, tailDef.val.Evalb ![out,time,initial] := by simp

end SetTheory.BusyBeaver.ZFC.ArithmeticStackTail254
