import DiophantineConsistency.WangTiles942RowStep

/-! Source-only checks; requires canonical-row.patch, no Lean run claimed. -/
namespace DiophantineConsistency.Round3CanonicalRowChecks

open SetTheory.BusyBeaver WangTiles942 WangTiles942Language
open WangTiles942RowEncoding WangTiles942StripGeometry
open WangTiles942StepConstruction WangTiles942RowStep

-- Function equality is restricted to the actual open strip subtype.
example {T : ℤ → ℤ → Tile} {N L R : ℕ} {t : ℤ} {cfg : Config 215}
    (hA : ∀ x τ, Allowed (T x τ))
    (hH : ∀ x τ, (T (x+1) τ).west = (T x τ).east)
    (hTime : ∀ x τ, (T x (τ+1)).north = (T x τ).south)
    (hs : PersistentStrip T N L R)
    (hrow : RowEncodes T (-(L : ℤ)) (R : ℤ) t cfg)
    (q : Fin 215) (hq : cfg.state = some q) :
    (fun x : {x : ℤ // -(L : ℤ) < x ∧ x < (R : ℤ)} => T x.val t) =
      (fun x => stepTile cfg q x.val) := by
  funext x
  exact row_tile_eq_stepTile hA hH hTime hs hrow q hq x.val x.property.1 x.property.2

-- All old endpoint premises remain visible, including time matching.
example {T : ℤ → ℤ → Tile} {N L R : ℕ} {t : ℤ} {cfg : Config 215}
    (hA : ∀ x τ, Allowed (T x τ))
    (hH : ∀ x τ, (T (x+1) τ).west = (T x τ).east)
    (hTime : ∀ x τ, (T x (τ+1)).north = (T x τ).south)
    (hs : PersistentStrip T N L R)
    (hrow : RowEncodes T (-(L : ℤ)) (R : ℤ) t cfg)
    (q : Fin 215) (hq : cfg.state = some q) :
    RowEncodes T (-(L : ℤ)) (R : ℤ) (t+1) (DecimalMachine215.machine.step cfg) :=
  row_step hA hH hTime hs hrow q hq

#print axioms receiver_tile
#print axioms receiver_south
#print axioms row_tile_eq_stepTile
#print axioms south_step
#print axioms row_step

end DiophantineConsistency.Round3CanonicalRowChecks
