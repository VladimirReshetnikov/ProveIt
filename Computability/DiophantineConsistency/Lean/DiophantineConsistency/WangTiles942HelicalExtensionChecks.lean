import DiophantineConsistency.WangTiles942HelicalExtension

/-! Signed representatives, the twisted horizontal seam, unit width,
and composition with the actual finite marked-word quotient. -/

namespace DiophantineConsistency.WangTiles942HelicalExtensionChecks

open WangTiles942 WangTiles942Language WangTiles942Periodic
open WangTiles942HelicalExtension WangTiles942HelicalQuotient

set_option Elab.async false
set_option maxRecDepth 10000

example : representative 3 1 (-2) = 1 ∧ quotient 3 1 (-2) = -1 := by decide
example : representative 3 1 2 = -1 ∧ quotient 3 1 2 = 1 := by decide

/-- Negative coordinates use the Euclidean quotient, not truncation to zero. -/
example : extend (fun x t : ℤ => (x,t)) 3 1 (-2) 7 = (1,6) := by decide
example : extend (fun x t : ℤ => (x,t)) 3 1 (-2) 7 ≠ (1,7) := by decide

/-- Crossing from the rightmost band site increases the time by one. -/
example : extend (fun x t : ℤ => (x,t)) 3 1 2 7 = (-1,8) := by decide
example : extend (fun x t : ℤ => (x,t)) 3 1 2 7 ≠ (-1,6) := by decide

example {α : Type*} (C : ℤ → ℤ → α) (x t : ℤ) :
    extend C 1 0 x t = C 0 (t+x) := by simp [extend, representative, quotient]

example {α : Type*} (C : ℤ → ℤ → α) (x t : ℤ) :
    extend C 1 0 (x+1) (t-1) = extend C 1 0 x t :=
  extend_helical C 1 (by decide) 0 x t

example {α : Type*} (C : ℤ → ℤ → α) (t : ℤ) :
    extend C 3 1 (-1) t = C (-1) t :=
  extend_on_band C 3 (by decide) 1 (-1) t (by constructor <;> omega)

example {α : Type*} (C : ℤ → ℤ → α) (t : ℤ) :
    extend C 3 1 1 t = C 1 t :=
  extend_on_band C 3 (by decide) 1 1 t (by constructor <;> omega)

/-- Origin preservation would be false if the upper bound on L were omitted. -/
example : extend (fun x _ : ℤ => x) 3 3 0 0 = -3 := by decide
example : extend (fun x _ : ℤ => x) 3 3 0 0 ≠ 0 := by decide

/-- At width one all horizontal edges use the twisted boundary condition;
there are no strict interior neighbor pairs. -/
example (C : ℤ → ℤ → Tile)
    (ht : ∀ t, (C 0 (t+1)).west = (C 0 t).east) (x t : ℤ) :
    (extend C 1 0 (x+1) t).west = (extend C 1 0 x t).east := by
  apply extend_horizontal_matching C 1 (by decide) 0
  · intro y hy hy'
    omega
  · simpa using ht

/-- The two geometry modules compose to a real indexed marked word, with
the original canonical-band tiles retained pointwise. -/
example (C : ℤ → ℤ → Tile) (w H : ℕ) (hw : 0 < w) (hHp : 0 < H)
    (L : ℤ) (hL0 : 0 ≤ L) (hLw : L < (w : ℤ))
    (hA : ∀ x, InBand w L x → ∀ t, Allowed (C x t))
    (hTime : ∀ x, InBand w L x → ∀ t, (C x (t+1)).north = (C x t).south)
    (hH : ∀ x, -L ≤ x → x+1 < (w : ℤ)-L →
      ∀ t, (C (x+1) t).west = (C x t).east)
    (hTwist : ∀ t, (C (-L) (t+1)).west = (C ((w : ℤ)-L-1) t).east)
    (hPeriod : ∀ x, InBand w L x → ∀ t, C x (t+(H : ℤ)) = C x t)
    (hStart : C 0 0 = start) :
    letI : NeZero (w*H) := ⟨Nat.ne_of_gt (Nat.mul_pos hw hHp)⟩
    ∃ a : ZMod (w*H) → Fin 942, MarkedWord (w*H) (w : ℤ) a ∧
      ∀ x, InBand w L x → ∀ t, tile (a (address (w*H) w x t)) = C x t := by
  letI : NeZero (w*H) := ⟨Nat.ne_of_gt (Nat.mul_pos hw hHp)⟩
  rcases extension_properties C w H hw L hL0 hLw hA hTime hH hTwist hPeriod hStart with
    ⟨ha,hh,ht,hs,hhel,hv⟩
  rcases exists_marked_word (extend C w L) ha w H hw hHp hh ht hs hhel hv with
    ⟨a,hm,hbind⟩
  refine ⟨a,hm,?_⟩
  intro x hx t
  exact (hbind x t).trans (extend_on_band C w hw L x t hx)

#print axioms representative_in_band
#print axioms coordinates_of_decomposition
#print axioms coordinates_in_band
#print axioms extend_on_band
#print axioms coordinates_add_width
#print axioms coordinates_succ_inside
#print axioms coordinates_succ_wrap
#print axioms extend_helical
#print axioms extend_vertical
#print axioms extend_allowed
#print axioms extend_time_matching
#print axioms extend_horizontal_matching
#print axioms extend_start
#print axioms extension_properties

end DiophantineConsistency.WangTiles942HelicalExtensionChecks
