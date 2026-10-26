import DiophantineConsistency.WangTiles942RowEncoding
import DiophantineConsistency.WangTiles942ResetRows
import DiophantineConsistency.WangTiles942InputLanguage

/-!
# An operating encoded row cannot finish anywhere inside its strip

The unique head input forces its actual transition tile. A finish at any
interior position would force finish at the head through the next reset
row, contradicting the transition's Boolean South output. Absence of
finishes is a conclusion, never an added row-encoding premise.
-/

namespace DiophantineConsistency.WangTiles942OperatingRow

open SetTheory.BusyBeaver
open WangTiles942 WangTiles942Language WangTiles942InputLanguage
  WangTiles942RowEncoding WangTiles942StripGeometry WangTiles942ResetRows

set_option Elab.async false
set_option maxRecDepth 10000

/-- The actual tape read, as the finite bit used by the tile language. -/
def symbol (cfg : Config 215) (x : ℤ) : Fin 2 :=
  ⟨(Tape.read cfg.tape x).toNat, by cases Tape.read cfg.tape x <;> decide⟩

theorem operating_head_tile {T : ℤ → ℤ → Tile} {l r t : ℤ} {cfg : Config 215}
    (hA : ∀ x τ, Allowed (T x τ)) (h : RowEncodes T l r t cfg)
    (q : Fin 215) (hq : cfg.state = some q) :
    T cfg.head t = (transitionRow (inputIndex q (symbol cfg cfg.head))).2 := by
  apply (north_operating_iff_transition (hA cfg.head t) q (symbol cfg cfg.head)).mp
  exact h.operating_head q hq

theorem operating_head_south_le_one {T : ℤ → ℤ → Tile} {l r t : ℤ} {cfg : Config 215}
    (hA : ∀ x τ, Allowed (T x τ)) (h : RowEncodes T l r t cfg)
    (q : Fin 215) (hq : cfg.state = some q) : (T cfg.head t).south ≤ 1 := by
  rw [operating_head_tile hA h q hq]
  change (action (inputIndex q (symbol cfg cfg.head))).1.toNat ≤ 1
  exact Bool.toNat_le _

/-- One alleged finish would propagate to the actual operating head,
whose forced transition has South0 or1, not438. -/
theorem no_south438 {T : ℤ → ℤ → Tile} {N L R : ℕ} {t : ℤ} {cfg : Config 215}
    (hA : ∀ x τ, Allowed (T x τ))
    (hH : ∀ x τ, (T (x+1) τ).west = (T x τ).east)
    (hTime : ∀ x τ, (T x (τ+1)).north = (T x τ).south)
    (hs : PersistentStrip T N L R)
    (h : RowEncodes T (-(L : ℤ)) (R : ℤ) t cfg)
    (q : Fin 215) (hq : cfg.state = some q)
    (x : ℤ) (hl : -(L : ℤ) < x) (hr : x < (R : ℤ)) : (T x t).south ≠ 438 := by
  intro hf
  have hrow := strip_finish_and_reset_of_south438 T (-(L : ℤ)) (R : ℤ) x t
    (fun x τ _ _ => hA x τ) (fun x τ _ _ => hH x τ)
    (fun x τ _ _ => hTime x τ)
    (fun x τ hxl hxr => (hs.interior x hxl hxr τ).1) hl hr hf
  have hh := (hrow cfg.head h.head_left h.head_right).2.1
  have hb := operating_head_south_le_one hA h q hq
  omega

theorem no_finish {T : ℤ → ℤ → Tile} {N L R : ℕ} {t : ℤ} {cfg : Config 215}
    (hA : ∀ x τ, Allowed (T x τ))
    (hH : ∀ x τ, (T (x+1) τ).west = (T x τ).east)
    (hTime : ∀ x τ, (T x (τ+1)).north = (T x τ).south)
    (hs : PersistentStrip T N L R)
    (h : RowEncodes T (-(L : ℤ)) (R : ℤ) t cfg)
    (q : Fin 215) (hq : cfg.state = some q)
    (x : ℤ) (hl : -(L : ℤ) < x) (hr : x < (R : ℤ)) : ¬ FinishTile (T x t) := by
  intro hf
  exact no_south438 hA hH hTime hs h q hq x hl hr hf.south

end DiophantineConsistency.WangTiles942OperatingRow
