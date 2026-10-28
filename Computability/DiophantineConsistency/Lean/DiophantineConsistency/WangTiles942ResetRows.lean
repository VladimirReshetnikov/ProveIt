import DiophantineConsistency.WangTiles942ResetHorizontal
import DiophantineConsistency.WangTiles942Boundary

/-!
# Propagating one actual reset across a seam-free integer interval

Color1 propagates in both horizontal directions. The exact local tile
classification then forces a reset at each interior position. The only
geometry input is explicit absence of seams in that interval; periodicity,
unique Start, an assumed reset row and machine semantics are not used.
-/

namespace DiophantineConsistency.WangTiles942ResetRows

open WangTiles942 WangTiles942Language WangTiles942ResetHorizontal WangTiles942Boundary

set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Exact membership in the three reset tiles, retaining the south color. -/
def ResetTile (t : Tile) : Prop := ∃ p ∈ [434,435,436], t = ⟨1,438,1,p⟩

theorem ResetTile.horizontal {t : Tile} (h : ResetTile t) : t.west = 1 ∧ t.east = 1 := by
  obtain ⟨p,hp,rfl⟩ := h
  exact ⟨rfl,rfl⟩

theorem ResetTile.north {t : Tile} (h : ResetTile t) : t.north = 438 := by
  obtain ⟨p,hp,rfl⟩ := h
  rfl

/-- Exact membership in the four finish tiles; their north colors remain
the two-bit plain/head alternatives rather than an assumed run state. -/
def FinishTile (t : Tile) : Prop :=
  ∃ a b : Fin 2, t = ⟨0,432*a.val+b.val,0,438⟩

theorem FinishTile.south {t : Tile} (h : FinishTile t) : t.south = 438 := by
  obtain ⟨a,b,rfl⟩ := h
  rfl

/-- Generic connectivity of an open integer interval, with both step
directions explicit. The predicate need not concern tiles. -/
theorem interval_propagate (P : ℤ → Prop) (l r x₀ : ℤ)
    (hl₀ : l < x₀) (hr₀ : x₀ < r) (h₀ : P x₀)
    (hnext : ∀ x, l < x → x+1 < r → P x → P (x+1))
    (hprev : ∀ x, l < x-1 → x < r → P x → P (x-1)) :
    ∀ x, l < x → x < r → P x := by
  have shifted (z : ℤ) : l < x₀ + z → x₀ + z < r → P (x₀ + z) := by
    induction z using Int.induction_on with
    | zero => exact fun _ _ => (show P (x₀ + 0) from (by simpa only [add_zero] using h₀))
    | succ n ih =>
        intro hl hr
        simpa only [add_assoc] using
          hnext (x₀ + (n : ℤ)) (by omega) (by omega) (ih (by omega) (by omega))
    | pred n ih =>
        intro hl hr
        simpa only [add_sub_assoc] using
          hprev (x₀ + -(n : ℤ)) (by omega) (by omega) (ih (by omega) (by omega))
  intro x hl hr
  have he : x₀ + (x - x₀) = x := by omega
  simpa only [he] using shifted (x-x₀) (by omega) (by omega)

/-- A reset's east1 forces the next tile to reset when that tile is not a seam. -/
theorem reset_next (T : ℤ → Tile) (x : ℤ)
    (ha : Allowed (T (x+1))) (hH : (T (x+1)).west = (T x).east)
    (hn : (T (x+1)).north ≠ 437) (hr : ResetTile (T x)) : ResetTile (T (x+1)) :=
  west_1_nonseam ha (hH.trans hr.horizontal.2) hn

/-- A reset's west1 forces the previous tile to reset when that tile is not a seam. -/
theorem reset_previous (T : ℤ → Tile) (x : ℤ)
    (ha : Allowed (T (x-1))) (hH : (T x).west = (T (x-1)).east)
    (hn : (T (x-1)).north ≠ 437) (hr : ResetTile (T x)) : ResetTile (T (x-1)) :=
  east_1_nonseam ha (hH.symm.trans hr.horizontal.1) hn

/-- A single actual reset determines every tile in a connected seam-free
row segment. Only local interval memberships and matching are needed. -/
theorem row_reset (T : ℤ → Tile) (l r x₀ : ℤ)
    (hallowed : ∀ x, l < x → x < r → Allowed (T x))
    (hH : ∀ x, l < x → x+1 < r → (T (x+1)).west = (T x).east)
    (hnonseam : ∀ x, l < x → x < r → (T x).north ≠ 437)
    (hl₀ : l < x₀) (hr₀ : x₀ < r) (hreset : ResetTile (T x₀)) :
    ∀ x, l < x → x < r → ResetTile (T x) := by
  apply interval_propagate (fun x => ResetTile (T x)) l r x₀ hl₀ hr₀ hreset
  · intro x hl hr hx
    exact reset_next T x (hallowed (x+1) (by omega) hr) (hH x hl hr)
      (hnonseam (x+1) (by omega) hr) hx
  · intro x hl hr hx
    have hh := hH (x-1) hl (by omega)
    rw [sub_add_cancel] at hh
    exact reset_previous T x (hallowed (x-1) hl (by omega)) hh
      (hnonseam (x-1) hl (by omega)) hx

/-- A lone north438 edge suffices because the actual local language first
identifies its reset tile; an entire reset row is not supplied. -/
theorem row_reset_of_north438 (T : ℤ → Tile) (l r x₀ : ℤ)
    (hallowed : ∀ x, l < x → x < r → Allowed (T x))
    (hH : ∀ x, l < x → x+1 < r → (T (x+1)).west = (T x).east)
    (hnonseam : ∀ x, l < x → x < r → (T x).north ≠ 437)
    (hl₀ : l < x₀) (hr₀ : x₀ < r) (hnorth : (T x₀).north = 438) :
    ∀ x, l < x → x < r → ResetTile (T x) := by
  exact row_reset T l r x₀ hallowed hH hnonseam hl₀ hr₀
    ((north_438_iff_reset (hallowed x₀ hl₀ hr₀)).mp hnorth)

/-- Two-dimensional specialization retains the original time and row.
Vertical matching is unnecessary for this horizontal propagation theorem. -/
theorem strip_reset_row (T : ℤ → ℤ → Tile) (l r x₀ t : ℤ)
    (hallowed : ∀ x τ, l < x → x < r → Allowed (T x τ))
    (hH : ∀ x τ, l < x → x+1 < r → (T (x+1) τ).west = (T x τ).east)
    (hnonseam : ∀ x τ, l < x → x < r → (T x τ).north ≠ 437)
    (hl₀ : l < x₀) (hr₀ : x₀ < r) (hreset : ResetTile (T x₀ t)) :
    ∀ x, l < x → x < r → ResetTile (T x t) := by
  exact row_reset (fun x => T x t) l r x₀
    (fun x => hallowed x t) (fun x => hH x t) (fun x => hnonseam x t) hl₀ hr₀ hreset

/-- One south438 edge gives a reset in the next row. Horizontal propagation
then fixes that entire next interior row, and time matching pulls south438
back to every tile of the original row. All those original tiles are actual
finish tiles by the finite language classification. No head, run, or uniform
finish/reset premise is supplied. -/
theorem strip_finish_and_reset_of_south438 (T : ℤ → ℤ → Tile) (l r x₀ t : ℤ)
    (hallowed : ∀ x τ, l < x → x < r → Allowed (T x τ))
    (hH : ∀ x τ, l < x → x+1 < r → (T (x+1) τ).west = (T x τ).east)
    (hTime : ∀ x τ, l < x → x < r → (T x (τ+1)).north = (T x τ).south)
    (hnonseam : ∀ x τ, l < x → x < r → (T x τ).north ≠ 437)
    (hl₀ : l < x₀) (hr₀ : x₀ < r) (hsouth : (T x₀ t).south = 438) :
    ∀ x, l < x → x < r →
      ResetTile (T x (t+1)) ∧ (T x t).south = 438 ∧ FinishTile (T x t) := by
  have hseed : ResetTile (T x₀ (t+1)) :=
    (north_438_iff_reset (hallowed x₀ (t+1) hl₀ hr₀)).mp
      ((hTime x₀ t hl₀ hr₀).trans hsouth)
  have hrow := strip_reset_row T l r x₀ (t+1) hallowed hH hnonseam hl₀ hr₀ hseed
  intro x hl hr
  have hreset := hrow x hl hr
  have hs : (T x t).south = 438 := (hTime x t hl hr).symm.trans hreset.north
  exact ⟨hreset, hs, (south_438_iff_finish (hallowed x t hl hr)).mp hs⟩

/-- The equivalent trigger may be one actual finish tile at an arbitrary
interior coordinate and integer time. -/
theorem strip_finish_and_reset_of_finish (T : ℤ → ℤ → Tile) (l r x₀ t : ℤ)
    (hallowed : ∀ x τ, l < x → x < r → Allowed (T x τ))
    (hH : ∀ x τ, l < x → x+1 < r → (T (x+1) τ).west = (T x τ).east)
    (hTime : ∀ x τ, l < x → x < r → (T x (τ+1)).north = (T x τ).south)
    (hnonseam : ∀ x τ, l < x → x < r → (T x τ).north ≠ 437)
    (hl₀ : l < x₀) (hr₀ : x₀ < r) (hfinish : FinishTile (T x₀ t)) :
    ∀ x, l < x → x < r →
      ResetTile (T x (t+1)) ∧ (T x t).south = 438 ∧ FinishTile (T x t) :=
  strip_finish_and_reset_of_south438 T l r x₀ t hallowed hH hTime hnonseam
    hl₀ hr₀ hfinish.south

end DiophantineConsistency.WangTiles942ResetRows
