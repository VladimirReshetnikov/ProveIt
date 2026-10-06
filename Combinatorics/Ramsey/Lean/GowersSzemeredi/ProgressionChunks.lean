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
  let n := L / m
  let b := L % m
  have hdecomp : L = n * m + b := by
    calc
      L = m * (L / m) + L % m := (Nat.div_add_mod L m).symm
      _ = (L / m) * m + L % m := by rw [Nat.mul_comm m (L / m)]
      _ = n * m + b := by rfl
  have hbn : b ≤ n := coarse_remainder_le_quotient hm hLm
  by_cases hfront : t < b * (m + 1)
  · let j : Fin n := ⟨t / (m + 1), by
      have hjb : t / (m + 1) < b :=
        (Nat.div_lt_iff_lt_mul (by omega : 0 < m + 1)).2 hfront
      exact hjb.trans_le hbn⟩
    let i := t % (m + 1)
    have hjb : (j : Nat) < b :=
      (Nat.div_lt_iff_lt_mul (by omega : 0 < m + 1)).2 hfront
    have hjb' : (j : Nat) < L % m := by simpa [b] using hjb
    refine ⟨j, i, ?_, ?_⟩
    · simpa [coarseChunkLength, hjb', i] using Nat.mod_lt t (by omega : 0 < m + 1)
    · have htdiv : t = t / (m + 1) * (m + 1) + t % (m + 1) := by
        calc
          t = (m + 1) * (t / (m + 1)) + t % (m + 1) :=
            (Nat.div_add_mod t (m + 1)).symm
          _ = t / (m + 1) * (m + 1) + t % (m + 1) := by
            rw [Nat.mul_comm (m + 1) (t / (m + 1))]
      rw [coarseChunkStart, min_eq_left hjb'.le]
      dsimp only [j, i]
      calc
        t = t / (m + 1) * (m + 1) + t % (m + 1) := htdiv
        _ = t / (m + 1) * m + t / (m + 1) + t % (m + 1) := by ring
  · have hback : b * (m + 1) ≤ t := Nat.le_of_not_gt hfront
    let u := t - b * (m + 1)
    have hu : u < (n - b) * m := by
      have hrewrite : L = b * (m + 1) + (n - b) * m := by
        calc
          L = n * m + b := hdecomp
          _ = ((n - b) + b) * m + b := by rw [Nat.sub_add_cancel hbn]
          _ = b * (m + 1) + (n - b) * m := by ring
      dsimp only [u]
      omega
    let j : Fin n := ⟨b + u / m, by
      have huq : u / m < n - b := (Nat.div_lt_iff_lt_mul hm).2 hu
      omega⟩
    let i := u % m
    have hbj : b ≤ (j : Nat) := by simp [j]
    have hbj' : L % m ≤ (j : Nat) := by simpa [b] using hbj
    refine ⟨j, i, ?_, ?_⟩
    · simpa [coarseChunkLength, Nat.not_lt.mpr hbj', i] using Nat.mod_lt u hm
    · have htu : t = b * (m + 1) + u := by dsimp only [u]; omega
      have hmod : u = u / m * m + u % m := by
        calc
          u = m * (u / m) + u % m := (Nat.div_add_mod u m).symm
          _ = u / m * m + u % m := by rw [Nat.mul_comm m (u / m)]
      rw [htu, hmod, coarseChunkStart, min_eq_right hbj']
      dsimp only [j, i]
      ring

lemma coarseChunk_unique {L m t : Nat}
    (j j' : Fin (L / m)) (i i' : Nat)
    (hi : i < coarseChunkLength m (L % m) j)
    (hi' : i' < coarseChunkLength m (L % m) j')
    (ht : t = coarseChunkStart m (L % m) j + i)
    (ht' : t = coarseChunkStart m (L % m) j' + i') : j = j' := by
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hj | hj
  · have hlt : t < coarseChunkStart m (L % m) j' := by
      calc
        t = coarseChunkStart m (L % m) j + i := ht
        _ < coarseChunkStart m (L % m) j +
            coarseChunkLength m (L % m) j := Nat.add_lt_add_left hi _
        _ = coarseChunkStart m (L % m) (j + 1) := coarseChunk_end _ _ _
        _ ≤ coarseChunkStart m (L % m) j' := by
          apply coarseChunkStart_mono
          omega
    rw [ht'] at hlt
    omega
  · have hlt : t < coarseChunkStart m (L % m) j := by
      calc
        t = coarseChunkStart m (L % m) j' + i' := ht'
        _ < coarseChunkStart m (L % m) j' +
            coarseChunkLength m (L % m) j' := Nat.add_lt_add_left hi' _
        _ = coarseChunkStart m (L % m) (j' + 1) := coarseChunk_end _ _ _
        _ ≤ coarseChunkStart m (L % m) j := by
          apply coarseChunkStart_mono
          omega
    rw [ht] at hlt
    omega

end LeanProofs.GowersSzemeredi.BaseCase
