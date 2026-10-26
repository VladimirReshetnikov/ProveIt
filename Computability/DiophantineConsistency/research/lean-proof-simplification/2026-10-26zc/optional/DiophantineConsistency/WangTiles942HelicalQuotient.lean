import DiophantineConsistency.WangTiles942Periodic
import DiophantineConsistency.WangTiles942Permutation

/-!
# A helical plane descends to the actual finite marked word

The periods (w,-1) and (0,H) imply a row-zero period w*H. Integer
periodicity then gives the full signed-address factorization through
ZMod(w*H), retaining every actual tile. No coprimality, unique Start,
computation, or assumed quotient factorization is used.
-/

namespace DiophantineConsistency.WangTiles942HelicalQuotient

open WangTiles942 WangTiles942Language WangTiles942Periodic

set_option Elab.async false
set_option maxRecDepth 10000

/-- Move any integer time to zero using the given helical period.
The equality is proved in both integer time directions. -/
theorem row_zero_of_helix {α : Type*} (T : ℤ → ℤ → α) (w : ℤ)
    (hhelix : ∀ x t, T (x+w) (t-1) = T x t) (x t : ℤ) :
    T x t = T (x+w*t) 0 := by
  induction t using Int.induction_on generalizing x with
  | zero => simp
  | succ n ih =>
      have hh := hhelix x ((n : ℤ)+1)
      rw [add_sub_cancel_right] at hh
      calc
        T x ((n : ℤ)+1) = T (x+w) n := hh.symm
        _ = T ((x+w)+w*n) 0 := ih _
        _ = T (x+w*((n : ℤ)+1)) 0 := by congr 1; ring
  | pred n ih =>
      have hh := hhelix (x-w) (-(n : ℤ))
      rw [sub_add_cancel] at hh
      calc
        T x (-(n : ℤ)-1) = T (x-w) (-(n : ℤ)) := hh
        _ = T ((x-w)+w*(-(n : ℤ))) 0 := ih _
        _ = T (x+w*(-(n : ℤ)-1)) 0 := by congr 1; ring

/-- A generic integer periodic function agrees with its remainder values. -/
theorem periodic_emod {α : Type*} {f : ℤ → α} {n : ℤ}
    (hp : Function.Periodic f n) (z : ℤ) : f (z % n) = f z := by
  simpa [Int.emod_def, mul_comm] using hp.sub_int_mul_eq (x := z) (z/n)

theorem periodic_zmod_val {α : Type*} {f : ℤ → α} {n : ℕ} [NeZero n]
    (hp : Function.Periodic f (n : ℤ)) (z : ℤ) :
    f ((z : ZMod n).val : ℤ) = f z := by
  rw [ZMod.val_intCast]
  exact periodic_emod hp z

theorem row_zero_period {α : Type*} (T : ℤ → ℤ → α) (w H : ℕ)
    (hhelix : ∀ x t, T (x+(w : ℤ)) (t-1) = T x t)
    (hvertical : ∀ x t, T x (t+(H : ℤ)) = T x t) :
    Function.Periodic (fun x => T x 0) ((w*H : ℕ) : ℤ) := by
  intro x
  rw [Nat.cast_mul]
  exact (row_zero_of_helix T w hhelix x H).symm.trans (by simpa using hvertical x 0)

theorem signed_row_period {α : Type*} (T : ℤ → ℤ → α) (w H : ℕ)
    (hhelix : ∀ x t, T (x+(w : ℤ)) (t-1) = T x t)
    (hvertical : ∀ x t, T x (t+(H : ℤ)) = T x t) :
    Function.Periodic (fun z => T (-z) 0) ((w*H : ℕ) : ℤ) := by
  simpa only [zero_sub] using (row_zero_period T w H hhelix hvertical).const_sub 0

/-- The literal decoder supplies the value; allowedness supplies only the bound. -/
theorem recoveredIndex_lt_of_allowed {t : Tile} (ht : Allowed t) :
    recoveredIndex t < 942 := by
  obtain ⟨i, rfl⟩ := (allowed_iff_tile t).mp ht
  simpa only [recovered_tile] using i.isLt

def indexOfAllowed (t : Tile) (ht : Allowed t) : Fin 942 :=
  ⟨recoveredIndex t, recoveredIndex_lt_of_allowed ht⟩

theorem tile_indexOfAllowed (t : Tile) (ht : Allowed t) :
    tile (indexOfAllowed t ht) = t := by
  obtain ⟨i, rfl⟩ := (allowed_iff_tile t).mp ht
  exact congrArg tile (Fin.ext (recovered_tile i))

/-- Compute actual literal indices from canonical representative tiles. -/
def quotientWord (T : ℤ → ℤ → Tile) (hA : ∀ x t, Allowed (T x t))
    (w H : ℕ) (z : ZMod (w*H)) : Fin 942 :=
  indexOfAllowed (T (-(z.val : ℤ)) 0) (hA _ _)

theorem quotientWord_tile (T : ℤ → ℤ → Tile) (hA : ∀ x t, Allowed (T x t))
    (w H : ℕ) (z : ZMod (w*H)) :
    tile (quotientWord T hA w H z) = T (-(z.val : ℤ)) 0 :=
  tile_indexOfAllowed _ _

theorem quotientWord_cast (T : ℤ → ℤ → Tile) (hA : ∀ x t, Allowed (T x t))
    (w H : ℕ) [NeZero (w*H)]
    (hhelix : ∀ x t, T (x+(w : ℤ)) (t-1) = T x t)
    (hvertical : ∀ x t, T x (t+(H : ℤ)) = T x t) (z : ℤ) :
    tile (quotientWord T hA w H (z : ZMod (w*H))) = T (-z) 0 := by
  rw [quotientWord_tile]
  exact periodic_zmod_val (signed_row_period T w H hhelix hvertical) z

/-- Full pointwise binding at the same signed address used by MarkedWord. -/
theorem quotientWord_binding (T : ℤ → ℤ → Tile) (hA : ∀ x t, Allowed (T x t))
    (w H : ℕ) [NeZero (w*H)]
    (hhelix : ∀ x t, T (x+(w : ℤ)) (t-1) = T x t)
    (hvertical : ∀ x t, T x (t+(H : ℤ)) = T x t) (x t : ℤ) :
    tile (quotientWord T hA w H (address (w*H) w x t)) = T x t := by
  rw [address, quotientWord_cast T hA w H hhelix hvertical]
  have he : -(-x-(w : ℤ)*t) = x+(w : ℤ)*t := by ring
  rw [he]
  exact (row_zero_of_helix T w hhelix x t).symm

/-- Every quotient position can be addressed at time zero. -/
theorem address_row_zero (n : ℕ) [NeZero n] (w : ℤ) (j : ZMod n) :
    address n w (-(j.val : ℤ)) 0 = j := by
  simp [address]

theorem quotientWord_marked (T : ℤ → ℤ → Tile) (hA : ∀ x t, Allowed (T x t))
    (w H : ℕ) [NeZero (w*H)]
    (hH : ∀ x t, (T (x+1) t).west = (T x t).east)
    (hTime : ∀ x t, (T x (t+1)).north = (T x t).south)
    (hStart : T 0 0 = start)
    (hhelix : ∀ x t, T (x+(w : ℤ)) (t-1) = T x t)
    (hvertical : ∀ x t, T x (t+(H : ℤ)) = T x t) :
    MarkedWord (w*H) (w : ℤ) (quotientWord T hA w H) := by
  have hb := quotientWord_binding T hA w H hhelix hvertical
  constructor
  · apply tile_injective
    have hzero := hb 0 0
    simpa only [address_origin, hStart, start_zero, start] using hzero
  · intro j
    have h0 := hb (-(j.val : ℤ)) 0
    have h1 := hb (-(j.val : ℤ)+1) 0
    rw [address_row_zero] at h0
    rw [address_east, address_row_zero] at h1
    rw [h0, h1]
    exact (hH _ _).symm
  · intro j
    have h0 := hb (-(j.val : ℤ)) 0
    have h1 := hb (-(j.val : ℤ)) (0+1)
    rw [address_row_zero] at h0
    rw [address_next_row, address_row_zero] at h1
    rw [h0, h1]
    exact (hTime _ _).symm

/-- Positive geometric dimensions supply the nonzero finite modulus.
All actual tiles, including the original Start, are retained pointwise. -/
theorem exists_marked_word (T : ℤ → ℤ → Tile) (hA : ∀ x t, Allowed (T x t))
    (w H : ℕ) (hw : 0 < w) (hHpos : 0 < H)
    (hH : ∀ x t, (T (x+1) t).west = (T x t).east)
    (hTime : ∀ x t, (T x (t+1)).north = (T x t).south)
    (hStart : T 0 0 = start)
    (hhelix : ∀ x t, T (x+(w : ℤ)) (t-1) = T x t)
    (hvertical : ∀ x t, T x (t+(H : ℤ)) = T x t) :
    letI : NeZero (w*H) := ⟨Nat.ne_of_gt (Nat.mul_pos hw hHpos)⟩
    ∃ a : ZMod (w*H) → Fin 942, MarkedWord (w*H) (w : ℤ) a ∧
      ∀ x t, tile (a (address (w*H) w x t)) = T x t := by
  letI : NeZero (w*H) := ⟨Nat.ne_of_gt (Nat.mul_pos hw hHpos)⟩
  exact ⟨quotientWord T hA w H,
    quotientWord_marked T hA w H hH hTime hStart hhelix hvertical,
    quotientWord_binding T hA w H hhelix hvertical⟩

end DiophantineConsistency.WangTiles942HelicalQuotient
