theorem main_index_gt_first {A P c k p n : ℕ}
    (hA : 1 < A) (hP : 1 < P) (hc : 1 < c)
    (hp : 0 < p) (hn : 0 < n) (hAP : 2 * A < 2 * P - 1)
    (hcp : c = yn hA p) (hk : k = 2 * yn hP n) (hkc : k < c) : n < p := by
  have hmono := (coordinates_mono_base hA hP (by omega : A ≤ P) p).2
  rw [hcp, hk] at hkc
  exact (strictMono_y hP).lt_iff_lt.mp (by omega)
