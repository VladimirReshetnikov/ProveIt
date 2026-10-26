import DiophantineConsistency.WangTiles942CycleBoundary
import DiophantineConsistency.WangTiles942HelicalExtension

/-!
# A finite computation band with its actual twisted seam

The interior is the finite trace cycle lifted to integer time. The left
seam faces the current row on its right and the previous row on its left.
Independent actual trace margins prove all boundary colors; the final
marked-word theorem assumes no extra boundary-cleanliness premise.
-/

namespace DiophantineConsistency.WangTiles942CycleBand

open SetTheory.BusyBeaver WangTiles942 WangTiles942Language WangTiles942Periodic
open WangTiles942TraceCycle WangTiles942CycleBoundary WangTiles942FinishConstruction
open WangTiles942HelicalExtension WangTiles942HelicalQuotient

set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- The actual finite row index at arbitrary signed time. -/
def timeIndex (H : ℕ) [NeZero H] (t : ℤ) : Fin H :=
  ⟨(t : ZMod H).val,ZMod.val_lt _⟩

theorem timeIndex_zero (H : ℕ) [NeZero H] :
    timeIndex H 0 = (⟨0,NeZero.pos H⟩ : Fin H) := by
  apply Fin.ext
  simp [timeIndex]

theorem timeIndex_period (H : ℕ) [NeZero H] (t : ℤ) :
    timeIndex H (t+(H : ℤ)) = timeIndex H t := by
  apply Fin.ext
  simp [timeIndex]

theorem timeIndex_succ (H : ℕ) [NeZero H] (t : ℤ) :
    timeIndex H (t+1) = nextIndex (NeZero.pos H) (timeIndex H t) := by
  apply Fin.ext
  simp only [timeIndex,nextIndex,Int.cast_add,Int.cast_one,ZMod.val_add,
    ZMod.val_one_eq_one_mod,Nat.add_mod_mod]

/-- The finite seam codes are literally 0, 1, or 2. -/
def seamCode {H : ℕ} (k : Fin H) : Fin 3 := ⟨edgeCode k,by have h := edgeCode_le_two k; omega⟩

/-- Its west code is squared, as required by the actual seam constructor. -/
def seam (H : ℕ) [NeZero H] (t : ℤ) : Tile :=
  ⟨(edgeCode (timeIndex H (t-1)))^2,437,edgeCode (timeIndex H t),437⟩

theorem seam_allowed (H : ℕ) [NeZero H] (t : ℤ) : Allowed (seam H t) :=
  Allowed.seam (seamCode (timeIndex H (t-1))) (seamCode (timeIndex H t))

theorem seam_period (H : ℕ) [NeZero H] (t : ℤ) : seam H (t+H) = seam H t := by
  have he : t+(H : ℤ)-1 = (t-1)+(H : ℤ) := by ring
  simp only [seam,he,timeIndex_period]

/-- Only the left seam is inserted. The right seam is supplied by the
next helical copy, so the canonical band excludes x=R. -/
def band (L H : ℕ) [NeZero H] (x t : ℤ) : Tile :=
  if x = -(L : ℤ) then seam H t else cycleTile (timeIndex H t) x

theorem band_seam (L H : ℕ) [NeZero H] (t : ℤ) :
    band L H (-(L : ℤ)) t = seam H t := by simp [band]

theorem band_interior (L H : ℕ) [NeZero H] (x t : ℤ) (hx : x ≠ -(L : ℤ)) :
    band L H x t = cycleTile (timeIndex H t) x := by simp only [band,if_neg hx]

theorem band_allowed (T L H : ℕ) [NeZero H]
    (hh : (DecimalMachine215.machine.run T).state = none) (hTH : T+2 ≤ H)
    (x t : ℤ) : Allowed (band L H x t) := by
  unfold band
  split_ifs
  · exact seam_allowed H t
  · exact cycleTile_allowed T H hh hTH _ x

theorem band_temporal (L H : ℕ) [NeZero H] (hH : 3 ≤ H) (x t : ℤ) :
    (band L H x (t+1)).north = (band L H x t).south := by
  by_cases hx : x = -(L : ℤ)
  · subst x
    rw [band_seam,band_seam]
    rfl
  · rw [band_interior L H x _ hx,band_interior L H x _ hx,timeIndex_succ]
    exact cycleTile_temporal hH (timeIndex H t) x

theorem band_horizontal (T L H : ℕ) [NeZero H]
    (hh : (DecimalMachine215.machine.run T).state = none) (hL : T+2 ≤ L)
    (x t : ℤ) (hx : -(L : ℤ) ≤ x) :
    (band L H (x+1) t).west = (band L H x t).east := by
  have hn : x+1 ≠ -(L : ℤ) := by omega
  rw [band_interior L H (x+1) t hn]
  by_cases he : x = -(L : ℤ)
  · subst x
    rw [band_seam,cycleTile_left_west T L hh hL]
    rfl
  · rw [band_interior L H x t he]
    exact cycleTile_horizontal (timeIndex H t) x

/-- The right edge of row t matches the left-facing seam edge of row t+1. -/
theorem band_twisted (T L R H : ℕ) [NeZero H]
    (hh : (DecimalMachine215.machine.run T).state = none)
    (_hL : T+2 ≤ L) (hR : T+2 ≤ R) (t : ℤ) :
    (band L H (-(L : ℤ)) (t+1)).west = (band L H ((R : ℤ)-1) t).east := by
  have hn : (R : ℤ)-1 ≠ -(L : ℤ) := by omega
  rw [band_seam,band_interior L H _ t hn,cycleTile_right_east T R hh hR]
  simp only [seam,add_sub_cancel_right]

theorem band_period (L H : ℕ) [NeZero H] (x t : ℤ) :
    band L H x (t+(H : ℤ)) = band L H x t := by
  by_cases hx : x = -(L : ℤ)
  · subst x
    rw [band_seam,band_seam,seam_period]
  · rw [band_interior L H x _ hx,band_interior L H x _ hx,timeIndex_period]

theorem band_start (L H : ℕ) [NeZero H] (hL : 0 < L) : band L H 0 0 = start := by
  rw [band_interior L H 0 0 (by omega),timeIndex_zero,cycleTile_zero,initialTile_zero]

/-- A canonical computation band has all geometric properties at every
independently enlarged left margin, right margin, and cycle height. -/
theorem band_properties (T L R H : ℕ) [NeZero H]
    (hh : (DecimalMachine215.machine.run T).state = none)
    (hL : T+2 ≤ L) (hR : T+2 ≤ R) (hTH : T+2 ≤ H) (hH : 3 ≤ H) :
    (∀ x t, Allowed (band L H x t)) ∧
    (∀ x t, (band L H x (t+1)).north = (band L H x t).south) ∧
    (∀ x, -(L : ℤ) ≤ x → ∀ t,
      (band L H (x+1) t).west = (band L H x t).east) ∧
    (∀ t, (band L H (-(L : ℤ)) (t+1)).west = (band L H ((R : ℤ)-1) t).east) ∧
    (∀ x t, band L H x (t+(H : ℤ)) = band L H x t) ∧
    band L H 0 0 = start := by
  exact ⟨band_allowed T L H hh hTH,band_temporal L H hH,
    fun x hx t => band_horizontal T L H hh hL x t hx,
    band_twisted T L R H hh hL hR,band_period L H,band_start L H (by omega)⟩

/-- The concrete quotient of the extended band has matching and retains every
canonical-band tile. Both the existential and uniquely marked endpoints use this
same descent proof; marker uniqueness is deliberately not a premise. -/
theorem band_quotient_properties (T L R H : ℕ) [NeZero H]
    [NeZero ((L+R)*H)]
    (hh : (DecimalMachine215.machine.run T).state = none)
    (hL : T+2 ≤ L) (hR : T+2 ≤ R) (hTH : T+2 ≤ H) (hH : 3 ≤ H)
    (hw : 0 < L+R) :
    let a := quotientWord (extend (band L H) (L+R) (L : ℤ))
      (extend_allowed (band L H) (L+R) hw (L : ℤ)
        (fun x _ t => band_allowed T L H hh hTH x t)) (L+R) H
    MarkedWord ((L+R)*H) (L+R : ℕ) a ∧
      ∀ x, -(L : ℤ) ≤ x → x < (R : ℤ) → ∀ t,
        tile (a (address ((L+R)*H) (L+R : ℕ) x t)) = band L H x t := by
  have hleft : ((L+R : ℕ) : ℤ)-(L : ℤ)-1 = (R : ℤ)-1 := by push_cast; ring
  rcases extension_properties (band L H) (L+R) H hw (L : ℤ) (by omega) (by omega)
      (fun x _ t => band_allowed T L H hh hTH x t)
      (fun x _ t => band_temporal L H hH x t)
      (fun x hx _ t => band_horizontal T L H hh hL x t hx)
      (by simpa only [hleft] using band_twisted T L R H hh hL hR)
      (fun x _ t => band_period L H x t) (band_start L H (by omega)) with
    ⟨_,hhoriz,htime,hs,hhel,hvert⟩
  refine ⟨quotientWord_marked _ _ _ _ hhoriz htime hs hhel hvert,?_⟩
  intro x hx0 hxR t
  apply (quotientWord_binding _ _ _ _ hhel hvert x t).trans
  apply extend_on_band (band L H) (L+R) hw (L : ℤ) x t
  unfold InBand
  push_cast
  omega

/-- A halting actual blank run gives an actual finite marked word of
length (L+R)*H and stride L+R, retaining every canonical-band tile.
There is no additional premise about trace boundaries or clean runs. -/
theorem marked_word_of_halt (T L R H : ℕ)
    (hh : (DecimalMachine215.machine.run T).state = none)
    (hL : T+2 ≤ L) (hR : T+2 ≤ R) (hTH : T+2 ≤ H) (hH : 3 ≤ H) :
    letI : NeZero H := ⟨by omega⟩
    letI : NeZero ((L+R)*H) := ⟨Nat.ne_of_gt (Nat.mul_pos (by omega) (by omega))⟩
    ∃ a : ZMod ((L+R)*H) → Fin 942, MarkedWord ((L+R)*H) (L+R : ℕ) a ∧
      ∀ x, -(L : ℤ) ≤ x → x < (R : ℤ) → ∀ t,
        tile (a (address ((L+R)*H) (L+R : ℕ) x t)) = band L H x t := by
  letI : NeZero H := ⟨by omega⟩
  letI : NeZero ((L+R)*H) := ⟨Nat.ne_of_gt (Nat.mul_pos (by omega) (by omega))⟩
  have hp := band_quotient_properties T L R H hh hL hR hTH hH (by omega)
  exact ⟨_,hp.1,hp.2⟩

end DiophantineConsistency.WangTiles942CycleBand
