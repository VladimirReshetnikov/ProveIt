/- DESIGN PROTOTYPE: not certified as compiling in this packet.
   See ../../validation/manifest.json and report.pdf for exact scope. -/
import DiophantineConsistency.WangTiles942RowStep
import DiophantineConsistency.WangTiles942StepConstruction

/-!
# Canonical realization of an operating row

UNVALIDATED CANDIDATE: this file has not been compiled in the project environment.
Shared-edge construction is assumed installed prior work and is not proposed here.

Candidate against commit 553a5f7a463cbaab8800ff8148fef0bc5a9e1b22.
The receiver lemma retains the entire tile equality already obtained in the
original proof. The canonical-row theorem then shares StepConstruction's
operational semantics with the soundness direction. This file is additive;
production integration would replace receiver_south/south_step bodies.
-/
namespace DiophantineConsistency.CanonicalOperatingRow
open SetTheory.BusyBeaver
open WangTiles942 WangTiles942Language WangTiles942Signals WangTiles942RowEncoding
  WangTiles942StripGeometry WangTiles942OperatingRow WangTiles942HeadBounds
  WangTiles942RowStep WangTiles942StepConstruction
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
variable {T : ℤ → ℤ → Tile} {N L R : ℕ} {t : ℤ} {cfg : Config 215}

theorem receiver_tile
    (hA : ∀ x τ, Allowed (T x τ))
    (hH : ∀ x τ, (T (x+1) τ).west = (T x τ).east)
    (hrow : RowEncodes T (-(L : ℤ)) (R : ℤ) t cfg)
    (q : Fin 215) (hq : cfg.state = some q)
    (x : ℤ) (hl : -(L : ℤ) < x) (hr : x < (R : ℤ))
    (hx : x = (DecimalMachine215.machine.transition q
      (Tape.read cfg.tape cfg.head)).move.apply cfg.head) :
    T x t = receiveTile cfg q x := by
  have ho : x ≠ cfg.head := hx ▸ WangMachineStep.moved_head_ne _ _
  have hp : (T x t).north = (symbol cfg x).val := hrow.plain x hl hr ho
  have hh := head_transition hA hrow q hq
  have hmove := WangMachineAction.transition_moved_head q
    (Tape.read cfg.tape cfg.head) cfg.head
  cases hd : (action (WangMachineAction.inputIndex q
      (Tape.read cfg.tape cfg.head))).2.1 with
  | false =>
      simp only [hd, Bool.false_eq_true, if_false] at hmove
      have he : x+1 = cfg.head := by omega
      have hm := hH x t
      rw [he, hh] at hm
      have hrx := left_transition_receiver
        (WangMachineAction.inputIndex q (Tape.read cfg.tape cfg.head)) hd
        (hA x t) (symbol cfg x) hp hm.symm
      simpa only [receiveTile, sourceIndex, hd, Bool.toNat_false, Bool.toNat_true,
        Nat.zero_mul, Nat.one_mul, Nat.sub_zero, Nat.sub_self] using hrx
  | true =>
      simp only [hd, if_true] at hmove
      have he : cfg.head+1 = x := by omega
      have hm := hH cfg.head t
      rw [he, hh] at hm
      have hrx := right_transition_receiver
        (WangMachineAction.inputIndex q (Tape.read cfg.tape cfg.head)) hd
        (hA x t) (symbol cfg x) hp hm.symm
      simpa only [receiveTile, sourceIndex, hd, Bool.toNat_false, Bool.toNat_true,
        Nat.zero_mul, Nat.one_mul, Nat.sub_zero, Nat.sub_self] using hrx

/-- Inside the persistent strip, the actual row is the supplied canonical
operating row. This is exact tile equality, not merely a south-color equation. -/
theorem row_eq_stepTile
    (hA : ∀ x τ, Allowed (T x τ))
    (hH : ∀ x τ, (T (x+1) τ).west = (T x τ).east)
    (hTime : ∀ x τ, (T x (τ+1)).north = (T x τ).south)
    (hs : PersistentStrip T N L R)
    (hrow : RowEncodes T (-(L : ℤ)) (R : ℤ) t cfg)
    (q : Fin 215) (hq : cfg.state = some q)
    (x : ℤ) (hl : -(L : ℤ) < x) (hr : x < (R : ℤ)) :
    T x t = stepTile cfg q x := by
  by_cases ho : x = cfg.head
  · subst x
    rw [stepTile_old_head]
    exact head_transition hA hrow q hq
  · by_cases hn : x = nextHead cfg q
    · rw [stepTile, if_neg ho, if_pos hn]
      exact receiver_tile hA hH hrow q hq x hl hr hn
    · rw [stepTile_elsewhere cfg q x ho hn]
      exact far_pass hA hH hTime hs hrow q hq x hl hr ho hn

/-- The previous south_step statement becomes a projection of canonical
realization followed by the already proved construction theorem. -/
theorem south_step_via_canonical
    (hA : ∀ x τ, Allowed (T x τ))
    (hH : ∀ x τ, (T (x+1) τ).west = (T x τ).east)
    (hTime : ∀ x τ, (T x (τ+1)).north = (T x τ).south)
    (hs : PersistentStrip T N L R)
    (hrow : RowEncodes T (-(L : ℤ)) (R : ℤ) t cfg)
    (q : Fin 215) (hq : cfg.state = some q)
    (x : ℤ) (hl : -(L : ℤ) < x) (hr : x < (R : ℤ)) :
    (T x t).south = WangMachineEncoding.color (DecimalMachine215.machine.step cfg) x := by
  rw [row_eq_stepTile hA hH hTime hs hrow q hq x hl hr]
  exact stepTile_south cfg q hq x

/-- Exact row uniqueness follows without a second machine-step analysis. -/
theorem row_unique (q : Fin 215) {U : ℤ → ℤ → Tile}
    (hT : ∀ x, -(L : ℤ) < x → x < (R : ℤ) → T x t = stepTile cfg q x)
    (hU : ∀ x, -(L : ℤ) < x → x < (R : ℤ) → U x t = stepTile cfg q x)
    (x : ℤ) (hl : -(L : ℤ) < x) (hr : x < (R : ℤ)) :
    T x t = U x t :=
  (hT x hl hr).trans (hU x hl hr).symm

#print axioms receiver_tile
#print axioms row_eq_stepTile
#print axioms south_step_via_canonical
end DiophantineConsistency.CanonicalOperatingRow
