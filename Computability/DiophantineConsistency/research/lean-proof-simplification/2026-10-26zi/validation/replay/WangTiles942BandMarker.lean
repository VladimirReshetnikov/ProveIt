import DiophantineConsistency.WangTiles942CycleBand
import DiophantineConsistency.WangTiles942CycleMarker
import DiophantineConsistency.WangTiles942HelicalMarker

/-!
# The actual computation band has one marker in its canonical quotient

The marker is unique for this explicit construction. No uniqueness is
assumed for an arbitrary marked word. The quotient below is the literal
quotientWord of the helical extension, not an unspecified existential word.
-/

namespace DiophantineConsistency.WangTiles942BandMarker

open WangTiles942 WangTiles942Language WangTiles942Periodic WangTiles942CycleBand
open WangTiles942CycleMarker WangTiles942HelicalExtension WangTiles942HelicalQuotient
open WangTiles942HelicalMarker

set_option Elab.async false
set_option maxRecDepth 10000

/-- Signed time is zero in the finite cycle precisely at multiples of H. -/
theorem timeIndex_val_zero_iff (H : ℕ) [NeZero H] (t : ℤ) :
    (timeIndex H t).val = 0 ↔ t % (H : ℤ) = 0 := by
  change (t : ZMod H).val = 0 ↔ _
  have he := ZMod.val_intCast (n := H) t
  constructor <;> intro h <;> omega

/-- The seam cannot introduce Start because its north color is437.
The local assertion requires no halt or lower height bound. -/
theorem band_eq_start_iff (L H : ℕ) [NeZero H] (hL : 0 < L) (x t : ℤ) :
    band L H x t = start ↔ x = 0 ∧ t % (H : ℤ) = 0 := by
  by_cases hx : x = -(L : ℤ)
  · rw [hx,band_seam]
    constructor
    · intro he
      have hn := congrArg Tile.north he
      change (437 : ℕ) = 435 at hn
      omega
    · rintro ⟨he,_⟩
      omega
  · rw [band_interior L H x t hx,cycleTile_eq_start_iff,timeIndex_val_zero_iff]
    exact and_comm

/-- The precise index word obtained from the actual extended band.
Allowedness is discharged from the actual halt and the chosen height. -/
noncomputable def canonicalWord (T L R H : ℕ) [NeZero H]
    (hh : (DecimalMachine215.machine.run T).state = none)
    (hTH : T+2 ≤ H) (hw : 0 < L+R) : ZMod ((L+R)*H) → Fin 942 :=
  quotientWord (extend (band L H) (L+R) (L : ℤ))
    (extend_allowed (band L H) (L+R) hw (L : ℤ)
      (fun x _ t => band_allowed T L H hh hTH x t)) (L+R) H

/-- The literal index zero, not just its tile value, is unique. This uses
the already proved injectivity of all942 actual tile tuples. -/
theorem canonicalWord_marker_iff (T L R H : ℕ) [NeZero H]
    [NeZero ((L+R)*H)]
    (hh : (DecimalMachine215.machine.run T).state = none)
    (hTH : T+2 ≤ H) (hL : 0 < L) (hR : 0 < R) (hw : 0 < L+R)
    (z : ZMod ((L+R)*H)) :
    canonicalWord T L R H hh hTH hw z = 0 ↔ z = 0 := by
  have hm := quotientWord_marker_iff (band L H) (L+R) H hw (NeZero.pos H)
    (L : ℤ) (by omega) (by exact_mod_cast (show L < L+R by omega))
    (fun x _ t => band_allowed T L H hh hTH x t)
    (fun x _ t => band_eq_start_iff L H hL x t) z
  change tile (canonicalWord T L R H hh hTH hw z) = start ↔ z = 0 at hm
  have hs : tile (0 : Fin 942) = start := start_zero
  constructor
  · intro he
    apply hm.mp
    rw [he,hs]
  · intro he
    apply tile_injective
    rw [hs]
    exact hm.mpr he

/-- All finite matching, every original-band tile, and unique Start are
proved for the same concrete quotient. Width and height are independent. -/
theorem canonicalWord_properties (T L R H : ℕ) [NeZero H]
    [NeZero ((L+R)*H)]
    (hh : (DecimalMachine215.machine.run T).state = none)
    (hL : T+2 ≤ L) (hR : T+2 ≤ R) (hTH : T+2 ≤ H) (hH : 3 ≤ H)
    (hw : 0 < L+R) :
    MarkedWord ((L+R)*H) (L+R : ℕ) (canonicalWord T L R H hh hTH hw) ∧
    (∀ z, canonicalWord T L R H hh hTH hw z = 0 ↔ z = 0) ∧
    (∀ x, -(L : ℤ) ≤ x → x < (R : ℤ) → ∀ t,
      tile (canonicalWord T L R H hh hTH hw (address ((L+R)*H) (L+R : ℕ) x t)) =
        band L H x t) := by
  have hp := band_quotient_properties T L R H hh hL hR hTH hH hw
  exact ⟨hp.1,canonicalWord_marker_iff T L R H hh hTH (by omega) (by omega) hw,hp.2⟩

/-- An actual halting time supplies a uniquely marked concrete word for
all sufficiently large independent left/right margins and heights. -/
theorem canonical_unique_word_of_halt (T L R H : ℕ)
    (hh : (DecimalMachine215.machine.run T).state = none)
    (hL : T+2 ≤ L) (hR : T+2 ≤ R) (hTH : T+2 ≤ H) (hH : 3 ≤ H) :
    letI : NeZero H := ⟨by omega⟩
    letI : NeZero ((L+R)*H) := ⟨Nat.ne_of_gt (Nat.mul_pos (by omega) (by omega))⟩
    let a := canonicalWord T L R H hh hTH (by omega)
    MarkedWord ((L+R)*H) (L+R : ℕ) a ∧
    (∀ z, a z = 0 ↔ z = 0) ∧
    (∀ x, -(L : ℤ) ≤ x → x < (R : ℤ) → ∀ t,
      tile (a (address ((L+R)*H) (L+R : ℕ) x t)) = band L H x t) := by
  letI : NeZero H := ⟨by omega⟩
  letI : NeZero ((L+R)*H) := ⟨Nat.ne_of_gt (Nat.mul_pos (by omega) (by omega))⟩
  exact canonicalWord_properties T L R H hh hL hR hTH hH (by omega)

end DiophantineConsistency.WangTiles942BandMarker

-- UNEXECUTED audit commands, excluded from every candidate size metric.
#print axioms DiophantineConsistency.WangTiles942BandMarker.timeIndex_val_zero_iff
#print axioms DiophantineConsistency.WangTiles942BandMarker.band_eq_start_iff
#print axioms DiophantineConsistency.WangTiles942BandMarker.canonicalWord_marker_iff
#print axioms DiophantineConsistency.WangTiles942BandMarker.canonicalWord_properties
#print axioms DiophantineConsistency.WangTiles942BandMarker.canonical_unique_word_of_halt
