import DiophantineConsistency.CurrentControllerData2011

/-! Safe physical positions for the actual controller power subset.
These are ordinary natural bounds and exact cyclic embeddings. No dummy
value, rank identity, or controller unit is a premise or conclusion. -/
namespace DiophantineConsistency.CurrentControllerPositions2011

open CurrentControllerData2011
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def position (k : ℕ) (j : ZMod (auxiliary^k)) : ℕ :=
  2+(auxiliary-1)*j.val

def cell (k : ℕ) (j : ZMod (auxiliary^k)) : ZMod (auxiliary^(k+1)) :=
  (position k j : ℕ)

theorem position_pos (k : ℕ) (j : ZMod (auxiliary^k)) : 0 < position k j := by
  unfold position
  omega

/-- A subtraction-free form of the sharp endpoint estimate. -/
theorem position_budget (k : ℕ) (j : ZMod (auxiliary^k)) :
    position k j+auxiliary^k+auxiliary ≤ auxiliary^(k+1)+3 := by
  have hv : j.val+1 ≤ auxiliary^k := ZMod.val_lt j
  have hm := Nat.mul_le_mul_left (auxiliary-1) hv
  have hp : auxiliary^(k+1) = auxiliary^k*auxiliary := pow_succ _ _
  have ha : auxiliary-1+1 = auxiliary := by decide
  unfold position
  nlinarith

theorem position_max (k : ℕ) (j : ZMod (auxiliary^k)) :
    position k j ≤ auxiliary^(k+1)-auxiliary^k-auxiliary+3 := by
  have h := position_budget k j
  omega

theorem position_next_lt (k : ℕ) (j : ZMod (auxiliary^k)) :
    position k j+1 < auxiliary^(k+1) := by
  have h := position_budget k j
  have ha : 4 ≤ auxiliary := by decide
  have hp : 0 < auxiliary^k := pow_pos (NeZero.pos auxiliary) k
  omega

theorem position_lt (k : ℕ) (j : ZMod (auxiliary^k)) :
    position k j < auxiliary^(k+1) := by
  have h := position_next_lt k j
  omega

theorem stride_lt_orbit {rw k : ℕ} (hrw : rw < k) : auxiliary^rw < auxiliary^k :=
  Nat.pow_lt_pow_right (by decide : 1 < auxiliary) hrw

theorem position_stride_lt {rw k : ℕ} (hrw : rw < k) (j : ZMod (auxiliary^k)) :
    position k j+auxiliary^rw < auxiliary^(k+1) := by
  have h := position_budget k j
  have hs := stride_lt_orbit hrw
  have ha : 4 ≤ auxiliary := by decide
  omega

theorem optional_next_lt (k : ℕ) : 3+1 < auxiliary^(k+1) := by
  have h : auxiliary ≤ auxiliary^(k+1) := by
    simpa only [pow_one] using pow_le_pow_right'
      (by decide : 1 ≤ auxiliary) (Nat.succ_le_succ (Nat.zero_le k))
  have ha : 4 < auxiliary := by decide
  omega

theorem optional_lt (k : ℕ) : 3 < auxiliary^(k+1) := by
  have h := optional_next_lt k
  omega

theorem optional_stride_lt {rw k : ℕ} (hrw : rw < k) :
    3+auxiliary^rw < auxiliary^(k+1) := by
  have hs := stride_lt_orbit hrw
  have hp : 0 < auxiliary^k := pow_pos (NeZero.pos auxiliary) k
  have ha : 4 < auxiliary := by decide
  rw [pow_succ]
  nlinarith

theorem position_injective (k : ℕ) : Function.Injective (position k) := by
  intro i j hij
  apply ZMod.val_injective
  have hp : 0 < auxiliary-1 := by decide
  unfold position at hij
  nlinarith

theorem position_ne_three (k : ℕ) (j : ZMod (auxiliary^k)) : position k j ≠ 3 := by
  intro h
  have hp : 2 ≤ auxiliary-1 := by decide
  unfold position at h
  by_cases hz : j.val = 0
  · simp [hz] at h
  · have hj : 1 ≤ j.val := by omega
    nlinarith

theorem cell_val (k : ℕ) (j : ZMod (auxiliary^k)) : (cell k j).val = position k j :=
  ZMod.val_natCast_of_lt (position_lt k j)

theorem cell_injective (k : ℕ) : Function.Injective (cell k) := by
  intro i j hij
  apply position_injective k
  simpa only [cell_val] using congrArg ZMod.val hij

theorem cell_ne_three (k : ℕ) (j : ZMod (auxiliary^k)) : cell k j ≠ 3 := by
  intro h
  apply position_ne_three k j
  calc
    position k j = (cell k j).val := (cell_val k j).symm
    _ = ((3 : ℕ) : ZMod (auxiliary^(k+1))).val := congrArg ZMod.val h
    _ = 3 := ZMod.val_natCast_of_lt (optional_lt k)

/-- The actual finite support, with the optional cell selected iff ε≠0. -/
def support (k : ℕ) (s : Finset (ZMod (auxiliary^k))) (ε : ℕ) : Finset ℕ :=
  if ε = 0 then s.image (position k) else insert 3 (s.image (position k))

theorem three_not_mem_image (k : ℕ) (s : Finset (ZMod (auxiliary^k))) :
    3 ∉ s.image (position k) := by
  intro h
  obtain ⟨j,hj,he⟩ := Finset.mem_image.mp h
  exact position_ne_three k j he

theorem support_card (k : ℕ) (s : Finset (ZMod (auxiliary^k)))
    (ε : ℕ) (hε : ε ≤ 1) : (support k s ε).card = s.card+ε := by
  unfold support
  split_ifs with h
  · rw [Finset.card_image_of_injective s (position_injective k),h,Nat.add_zero]
  · have he : ε = 1 := by omega
    rw [Finset.card_insert_of_notMem (three_not_mem_image k s),
      Finset.card_image_of_injective s (position_injective k),he]

theorem support_mem (k : ℕ) (s : Finset (ZMod (auxiliary^k))) (ε n : ℕ) :
    n ∈ support k s ε ↔ (∃ j ∈ s, position k j = n) ∨ (ε ≠ 0 ∧ n = 3) := by
  by_cases h : ε = 0 <;> simp [support,h,or_comm]

theorem support_basic (k : ℕ) (s : Finset (ZMod (auxiliary^k))) (ε n : ℕ)
    (hn : n ∈ support k s ε) : 0 < n ∧ n+1 < auxiliary^(k+1) := by
  rcases (support_mem k s ε n).mp hn with ⟨j,hj,rfl⟩ | ⟨hε,rfl⟩
  · exact ⟨position_pos k j,position_next_lt k j⟩
  · exact ⟨by decide,optional_next_lt k⟩

/-- These safety bounds need only rw<k; the subset construction's stronger
condition auxiliary^k>d*auxiliary is not required for position geometry. -/
theorem support_safe {rw k : ℕ} (hrw : rw < k)
    (s : Finset (ZMod (auxiliary^k))) (ε n : ℕ) (hn : n ∈ support k s ε) :
    0 < n ∧ n+1 < auxiliary^(k+1) ∧ n+auxiliary^rw < auxiliary^(k+1) := by
  obtain ⟨hpos,hnext⟩ := support_basic k s ε n hn
  refine ⟨hpos,hnext,?_⟩
  rcases (support_mem k s ε n).mp hn with ⟨j,hj,rfl⟩ | ⟨hε,rfl⟩
  · exact position_stride_lt hrw j
  · exact optional_stride_lt hrw

def cyclicSupport (k : ℕ) (s : Finset (ZMod (auxiliary^k))) (ε : ℕ) :
    Finset (ZMod (auxiliary^(k+1))) :=
  (support k s ε).image (fun n : ℕ => (n : ZMod (auxiliary^(k+1))))

theorem support_cast_injective (k : ℕ) (s : Finset (ZMod (auxiliary^k))) (ε : ℕ) :
    Set.InjOn (fun n : ℕ => (n : ZMod (auxiliary^(k+1)))) (support k s ε) := by
  intro a ha b hb he
  have hla : a < auxiliary^(k+1) := by have h := (support_basic k s ε a ha).2; omega
  have hlb : b < auxiliary^(k+1) := by have h := (support_basic k s ε b hb).2; omega
  simpa only [ZMod.val_natCast_of_lt hla,ZMod.val_natCast_of_lt hlb] using
    congrArg ZMod.val he

theorem cyclicSupport_card (k : ℕ) (s : Finset (ZMod (auxiliary^k)))
    (ε : ℕ) (hε : ε ≤ 1) : (cyclicSupport k s ε).card = s.card+ε := by
  rw [cyclicSupport,Finset.card_image_of_injOn (support_cast_injective k s ε)]
  exact support_card k s ε hε

/-- This is directly in the value form consumed by the dummy safety API. -/
theorem cyclicSupport_safe {rw k : ℕ} (hrw : rw < k)
    (s : Finset (ZMod (auxiliary^k))) (ε : ℕ) (j : ZMod (auxiliary^(k+1)))
    (hj : j ∈ cyclicSupport k s ε) :
    0 < j.val ∧ j.val+1 < auxiliary^(k+1) ∧ j.val+auxiliary^rw < auxiliary^(k+1) := by
  obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hj
  have hb := support_safe hrw s ε n hn
  have hl : n < auxiliary^(k+1) := by omega
  simpa only [ZMod.val_natCast_of_lt hl] using hb

end DiophantineConsistency.CurrentControllerPositions2011
