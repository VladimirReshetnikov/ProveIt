import GowersSzemeredi.Definitions

/-!
# Rounding-safe consecutive chunks

Split an interval of length L into L/m chunks of length m or m+1 when
m*m ≤ L. These elementary facts are shared by Sections 5 and 16. Their
original BaseCase namespace is retained for compatibility with Section 16.
-/

set_option autoImplicit false

namespace LeanProofs.GowersSzemeredi.BaseCase

def coarseChunkStart (m b j : Nat) : Nat :=
  j * m + min j b

def coarseChunkLength (m b j : Nat) : Nat :=
  if j < b then m + 1 else m

lemma coarseChunk_end (m b j : Nat) :
    coarseChunkStart m b j + coarseChunkLength m b j =
      coarseChunkStart m b (j + 1) := by
  by_cases hjb : j < b
  · simp [coarseChunkStart, coarseChunkLength, hjb, min_eq_left hjb.le]
    ring
  · have hbj : b ≤ j := Nat.le_of_not_gt hjb
    have hsucc : b ≤ j + 1 := hbj.trans (Nat.le_succ _)
    simp [coarseChunkStart, coarseChunkLength, hjb, min_eq_right hbj,
      min_eq_right hsucc]
    ring

lemma coarse_remainder_le_quotient {L m : Nat} (hm : 0 < m)
    (hLm : m * m ≤ L) : L % m ≤ L / m := by
  have hmm : m ≤ L / m := (Nat.le_div_iff_mul_le hm).2 hLm
  exact (Nat.mod_lt L hm).le.trans hmm

lemma coarseChunk_total {L m : Nat} (hm : 0 < m)
    (hLm : m * m ≤ L) :
    coarseChunkStart m (L % m) (L / m) = L := by
  have hb := coarse_remainder_le_quotient hm hLm
  rw [coarseChunkStart, min_eq_right hb, Nat.mul_comm (L / m) m]
  exact Nat.div_add_mod L m

lemma coarseChunk_length_bounds {L m : Nat} (hm : 0 < m)
    (j : Fin (L / m)) :
    m ≤ coarseChunkLength m (L % m) j ∧
      coarseChunkLength m (L % m) j ≤ 2 * m := by
  unfold coarseChunkLength
  split_ifs <;> omega

lemma coarseChunkStart_mono {m b j k : Nat} (hjk : j ≤ k) :
    coarseChunkStart m b j ≤ coarseChunkStart m b k := by
  unfold coarseChunkStart
  exact Nat.add_le_add (Nat.mul_le_mul_right m hjk) (min_le_min hjk le_rfl)

lemma coarseChunk_index_lt {L m : Nat} (hm : 0 < m)
    (hLm : m * m ≤ L) (j : Fin (L / m)) {i : Nat}
    (hi : i < coarseChunkLength m (L % m) j) :
    coarseChunkStart m (L % m) j + i < L := by
  calc
    coarseChunkStart m (L % m) j + i <
        coarseChunkStart m (L % m) j +
          coarseChunkLength m (L % m) j := Nat.add_lt_add_left hi _
    _ = coarseChunkStart m (L % m) (j + 1) := coarseChunk_end _ _ _
    _ ≤ coarseChunkStart m (L % m) (L / m) := by
      apply coarseChunkStart_mono
      omega
    _ = L := coarseChunk_total hm hLm

lemma exists_coarseChunk {L m t : Nat} (hm : 0 < m)
    (hLm : m * m ≤ L) (ht : t < L) :
    ∃ j : Fin (L / m), ∃ i : Nat,
      i < coarseChunkLength m (L % m) j ∧
      t = coarseChunkStart m (L % m) j + i := by
  have hm1 : 0 < m + 1 := m.succ_pos
  by_cases hfront : t / (m + 1) < L % m
  · -- `t` lies in one of the first `L % m` chunks, of length `m + 1`
    refine ⟨⟨t / (m + 1), hfront.trans_le (coarse_remainder_le_quotient hm hLm)⟩,
      t % (m + 1), by simpa [coarseChunkLength, hfront] using Nat.mod_lt t hm1, ?_⟩
    simp only [coarseChunkStart, min_eq_left hfront.le]
    have := Nat.div_add_mod' t (m + 1)
    rw [Nat.mul_add_one] at this
    omega
  · -- otherwise `t - L % m` is split into chunks of length `m`
    have hb := (Nat.le_div_iff_mul_le hm1).1 (Nat.not_lt.1 hfront)
    rw [Nat.mul_add_one] at hb
    have hj : L % m ≤ (t - L % m) / m := (Nat.le_div_iff_mul_le hm).2 (by omega)
    have hq : (t - L % m) / m < L / m :=
      (Nat.div_lt_iff_lt_mul hm).2 (by have := Nat.div_add_mod' L m; omega)
    refine ⟨⟨_, hq⟩, (t - L % m) % m,
      by simpa [coarseChunkLength, Nat.not_lt.2 hj] using Nat.mod_lt (t - L % m) hm, ?_⟩
    simp only [coarseChunkStart, min_eq_right hj]
    have := Nat.div_add_mod' (t - L % m) m
    omega

lemma coarseChunk_unique {L m t : Nat}
    (j j' : Fin (L / m)) (i i' : Nat)
    (hi : i < coarseChunkLength m (L % m) j)
    (hi' : i' < coarseChunkLength m (L % m) j')
    (ht : t = coarseChunkStart m (L % m) j + i)
    (ht' : t = coarseChunkStart m (L % m) j' + i') : j = j' := by
  -- a chunk ends no later than every later chunk starts
  have key : ∀ {a b : Nat}, a < b → coarseChunkStart m (L % m) a +
      coarseChunkLength m (L % m) a ≤ coarseChunkStart m (L % m) b := fun h =>
    (coarseChunk_end _ _ _).trans_le (coarseChunkStart_mono (Nat.succ_le_of_lt h))
  apply Fin.ext
  rcases lt_trichotomy (j : Nat) j' with h | h | h
  · have := key h; omega
  · exact h
  · have := key h; omega

end LeanProofs.GowersSzemeredi.BaseCase
