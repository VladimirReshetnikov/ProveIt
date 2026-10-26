import DiophantineConsistency.WangTiles942OperatingRow

namespace DiophantineConsistency.WangTiles942OperatingRowChecks

open SetTheory.BusyBeaver
open WangTiles942 WangTiles942Language WangTiles942RowEncoding
  WangTiles942StripGeometry WangTiles942OperatingRow

set_option Elab.async false
set_option maxRecDepth 10000

/-- A halted head input really can finish in the finite language. The
operating-state hypothesis in the whole-row exclusion is material. -/
private def halted : Config 215 := { state := none, head := 0, tape := [] }

example : Allowed (⟨0,WangMachineEncoding.color halted 0,0,438⟩ : Tile) :=
  Allowed.finish (1 : Fin 2) (0 : Fin 2)

/-- Plain finish is locally allowed too: its global exclusion requires
the actual operating head and propagation through the following reset. -/
example (b : Fin 2) : Allowed (⟨0,b.val,0,438⟩ : Tile) := by
  simpa only [Fin.val_zero, Nat.mul_zero, zero_add] using Allowed.finish (0 : Fin 2) b

example {T : ℤ → ℤ → Tile} {N L R : ℕ} {t : ℤ} {cfg : Config 215}
    (hA : ∀ x τ, Allowed (T x τ))
    (hH : ∀ x τ, (T (x+1) τ).west = (T x τ).east)
    (hTime : ∀ x τ, (T x (τ+1)).north = (T x τ).south)
    (hs : PersistentStrip T N L R)
    (h : RowEncodes T (-(L : ℤ)) (R : ℤ) t cfg)
    (q : Fin 215) (hq : cfg.state = some q) :
    ∀ x, -(L : ℤ) < x → x < (R : ℤ) → (T x t).south ≠ 438 :=
  no_south438 hA hH hTime hs h q hq

#print axioms operating_head_tile
#print axioms operating_head_south_le_one
#print axioms no_south438
#print axioms no_finish

end DiophantineConsistency.WangTiles942OperatingRowChecks
