import DiophantineConsistency.WangTiles942Boundary

/-!
# Exact local input grammar of the actual 942 Wang tiles

An operating head input selects exactly its indexed transition. Halt
inputs admit pass and finish, and plain inputs admit pass, finish, or a
receive tile with an actual directional target. These are finite-language
statements, not machine-step or unique-head semantics for a whole row.
-/

namespace DiophantineConsistency.WangTiles942InputLanguage

open WangTiles942 WangTiles942Language WangTiles942Boundary

set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- The actual source-action index, with the read bit as the low bit. -/
def inputIndex (q : Fin 215) (b : Fin 2) : Fin 430 :=
  ⟨2*q.val+b.val, by have hq := q.isLt; have hb := b.isLt; omega⟩

theorem inputIndex_val (q : Fin 215) (b : Fin 2) :
    (inputIndex q b).val = 2*q.val+b.val := rfl

theorem inputIndex_components (q : Fin 215) (b : Fin 2) :
    (inputIndex q b).val / 2 = q.val ∧ (inputIndex q b).val % 2 = b.val := by
  have hb := b.isLt
  rw [inputIndex_val]
  omega

theorem transition_north_eq_index (j : Fin 430) : (transitionRow j).2.north = j.val+2 := by
  change 2*(j.val/2)+j.val%2+2 = j.val+2
  omega

theorem operating_head_bounds (q : Fin 215) (b : Fin 2) :
    2 ≤ headColor q.val b.val ∧ headColor q.val b.val ≤ 431 := by
  have hq := q.isLt
  have hb := b.isLt
  unfold headColor
  omega

theorem indexed_transition_input (q : Fin 215) (b : Fin 2) :
    (transitionRow (inputIndex q b)).2.north = headColor q.val b.val := by
  rw [transition_north_eq_index, inputIndex_val]
  rfl

/-- An operating encoded input determines exactly its actual transition row. -/
theorem north_operating_iff_transition {t : Tile} (ht : Allowed t)
    (q : Fin 215) (b : Fin 2) :
    t.north = headColor q.val b.val ↔ t = (transitionRow (inputIndex q b)).2 := by
  have hb := operating_head_bounds q b
  constructor
  · intro hn
    cases ht with
    | start => simp only [start] at hn; omega
    | transition j =>
        have hj : j = inputIndex q b := by
          apply Fin.ext
          rw [inputIndex_val]
          rw [transition_north_eq_index] at hn
          unfold headColor at hn
          omega
        subst j
        rfl
    | pass a c =>
        have ha := a.isLt
        have hc := c.isLt
        simp only at hn
        omega
    | receive d p hp c => have hc := c.isLt; simp only at hn; omega
    | finish a c =>
        have ha := a.isLt
        have hc := c.isLt
        simp only at hn
        omega
    | initLeft => simp only at hn; omega
    | initHead => simp only at hn; omega
    | initRight => simp only at hn; omega
    | reset p hp => simp only at hn; omega
    | seam a c => simp only at hn; omega
  · rintro rfl
    exact indexed_transition_input q b

theorem halt_head_eq (b : Fin 2) : headColor 215 b.val = 432+b.val := by
  unfold headColor
  omega

/-- A halt head can pass unchanged or finish; both alternatives are retained. -/
theorem north_halt_iff_pass_or_finish {t : Tile} (ht : Allowed t) (b : Fin 2) :
    t.north = headColor 215 b.val ↔
      t = ⟨0,432+b.val,0,432+b.val⟩ ∨ t = ⟨0,432+b.val,0,438⟩ := by
  have hb := b.isLt
  constructor
  · intro hn
    rw [halt_head_eq] at hn
    cases ht with
    | start => simp only [start] at hn; omega
    | transition j => have hj := transition_north_bound j; omega
    | pass a c => exact Or.inl (congrArg (fun n : ℕ => (⟨0,n,0,n⟩ : Tile)) hn)
    | receive d p hp c => have hc := c.isLt; simp only at hn; omega
    | finish a c => exact Or.inr (congrArg (fun n : ℕ => (⟨0,n,0,438⟩ : Tile)) hn)
    | initLeft => simp only at hn; omega
    | initHead => simp only at hn; omega
    | initRight => simp only at hn; omega
    | reset p hp => simp only at hn; omega
    | seam a c => simp only at hn; omega
  · rintro (rfl | rfl) <;> exact (halt_head_eq b).symm

/-- A plain-symbol input may pass, finish, or receive a head from an actual
transition target; the target may be the halt state 215. -/
theorem north_plain_iff {t : Tile} (ht : Allowed t) (b : Fin 2) :
    t.north = b.val ↔ t = ⟨0,b.val,0,b.val⟩ ∨ t = ⟨0,b.val,0,438⟩ ∨
      ∃ (d : Bool) (q : ℕ), q ∈ targets d ∧
        t = ⟨d.toNat*rail d q,b.val,(1-d.toNat)*rail d q,headColor q b.val⟩ := by
  have hb := b.isLt
  constructor
  · intro hn
    cases ht with
    | start => simp only [start] at hn; omega
    | transition j => rw [transition_north_eq_index] at hn; omega
    | pass a c => exact Or.inl (congrArg (fun n : ℕ => (⟨0,n,0,n⟩ : Tile)) hn)
    | receive d q hq c =>
        have hc : c = b := Fin.ext hn
        subst c
        exact Or.inr (Or.inr ⟨d,q,hq,rfl⟩)
    | finish a c => exact Or.inr (Or.inl
        (congrArg (fun n : ℕ => (⟨0,n,0,438⟩ : Tile)) hn))
    | initLeft => simp only at hn; omega
    | initHead => simp only at hn; omega
    | initRight => simp only at hn; omega
    | reset p hp => simp only at hn; omega
    | seam a c => simp only at hn; omega
  · rintro (rfl | rfl | ⟨d,q,hq,rfl⟩) <;> rfl

end DiophantineConsistency.WangTiles942InputLanguage
