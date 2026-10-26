import DiophantineConsistency.WangTiles942HelicalQuotient

/-! Full signed-address and quotient checks, including negative time,
noncoprime dimensions and modulus1. No unique-Start premise is introduced. -/

namespace DiophantineConsistency.WangTiles942HelicalQuotientChecks

open WangTiles942 WangTiles942Language WangTiles942Periodic WangTiles942HelicalQuotient

set_option Elab.async false
set_option maxRecDepth 10000

/-- The integer-time normalization works in both directions for arbitrary
values, even without a finite vertical period. -/
example (x t : ℤ) :
    (fun x t : ℤ => x+2*t) x t = (fun x t : ℤ => x+2*t) (x+2*t) 0 :=
  row_zero_of_helix (fun x t : ℤ => x+2*t) 2 (by intro x t; ring) x t

example {α : Type*} (f : ℤ → α) (hp : Function.Periodic f 12) : f (-37 % 12) = f (-37) :=
  periodic_emod hp (-37)

example {α : Type*} (f : ℤ → α) (hp : Function.Periodic f 12) (z : ℤ) :
    f ((z : ZMod 12).val : ℤ) = f z := periodic_zmod_val hp z

/-- Reversing the temporal sign would give the wrong address. -/
example : address 6 2 0 1 = (4 : ZMod 6) := by decide
example : address 6 2 0 1 ≠ (2 : ZMod 6) := by decide

private def plain : Tile := ⟨0,0,0,0⟩
private def constantPlane (_ _ : ℤ) : Tile := plain

private theorem constant_allowed : ∀ x t, Allowed (constantPlane x t) := by
  intro x t
  exact Allowed.pass (0 : Fin 2) (0 : Fin 2)

/-- These dimensions share a factor. The full tile factorization still
holds; the constant plain plane is not falsely claimed to contain Start. -/
example : Nat.gcd 2 2 = 2 := by decide

example (x t : ℤ) :
    tile (quotientWord constantPlane constant_allowed 2 2 (address 4 2 x t)) = plain :=
  quotientWord_binding constantPlane constant_allowed 2 2
    (by intro x t; rfl) (by intro x t; rfl) x t

/-- The quotient itself remains valid at modulus1. Actual Start plus
matching is separately required for a marked word, and is not assumed here. -/
example (x t : ℤ) :
    tile (quotientWord constantPlane constant_allowed 1 1 (address 1 1 x t)) = plain :=
  quotientWord_binding constantPlane constant_allowed 1 1
    (by intro x t; rfl) (by intro x t; rfl) x t

example (n : ℕ) [NeZero n] (w : ℤ) (j : ZMod n) :
    address n w (-(j.val : ℤ)) 0 = j := address_row_zero n w j

example (T : ℤ → ℤ → Tile) (hA : ∀ x t, Allowed (T x t))
    (w H : ℕ) [NeZero (w*H)]
    (hH : ∀ x t, (T (x+1) t).west = (T x t).east)
    (hTime : ∀ x t, (T x (t+1)).north = (T x t).south)
    (hStart : T 0 0 = start)
    (hhelix : ∀ x t, T (x+(w : ℤ)) (t-1) = T x t)
    (hvertical : ∀ x t, T x (t+(H : ℤ)) = T x t) :
    MarkedWord (w*H) (w : ℤ) (quotientWord T hA w H) ∧
      ∀ x t, plane (w*H) w (quotientWord T hA w H) x t = T x t := by
  exact ⟨quotientWord_marked T hA w H hH hTime hStart hhelix hvertical,
    quotientWord_binding T hA w H hhelix hvertical⟩

example (T : ℤ → ℤ → Tile) (hA : ∀ x t, Allowed (T x t))
    (w H : ℕ) (hw : 0 < w) (hHpos : 0 < H)
    (hH : ∀ x t, (T (x+1) t).west = (T x t).east)
    (hTime : ∀ x t, (T x (t+1)).north = (T x t).south)
    (hStart : T 0 0 = start)
    (hhelix : ∀ x t, T (x+(w : ℤ)) (t-1) = T x t)
    (hvertical : ∀ x t, T x (t+(H : ℤ)) = T x t) :
    letI : NeZero (w*H) := ⟨Nat.ne_of_gt (Nat.mul_pos hw hHpos)⟩
    ∃ a : ZMod (w*H) → Fin 942, MarkedWord (w*H) (w : ℤ) a ∧
      ∀ x t, tile (a (address (w*H) w x t)) = T x t :=
  exists_marked_word T hA w H hw hHpos hH hTime hStart hhelix hvertical

#print axioms row_zero_of_helix
#print axioms periodic_emod
#print axioms periodic_zmod_val
#print axioms row_zero_period
#print axioms signed_row_period
#print axioms quotientWord_tile
#print axioms quotientWord_cast
#print axioms quotientWord_binding
#print axioms address_row_zero
#print axioms quotientWord_marked
#print axioms exists_marked_word

end DiophantineConsistency.WangTiles942HelicalQuotientChecks
