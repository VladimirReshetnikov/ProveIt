import DiophantineConsistency.SplitSourceContract

open DiophantineConsistency SplitSourceContract SplitSourceWords

-- At b=1 the low digits must all be zero. This boundary remains part of
-- the exact binomial test; no unsupported b>=2 condition is introduced.
example {d : Parameters} {a : ℕ} (hd : Valid d a) :
    (SplitNineRatio.threshold a 1) ^ 2 ∣
      (2 * SplitNineRatio.rank a 1 (word d a 1 0) (mask d a 1)).choose
        (SplitNineRatio.rank a 1 (word d a 1 0) (mask d a 1)) ↔
      ∀ j, (sourcePolynomial d (fun _ => 0)).coeff (d.q j) = 0 := by
  have hB := (SplitNineRatio.base_bounds a (by decide : 0 < 1)).1
  have hcap : 0 < 4 * 1 * (SplitNineRatio.base a 1) ^ 116 := by positivity
  rw [binomial_iff_source hd (k := 0) (by decide) hcap]
  constructor
  · rintro ⟨z, hz, _, hcoeff⟩
    have he : z = fun _ => 0 := by funext i; have h := hz i; omega
    simpa only [he] using hcoeff
  · intro hcoeff
    refine ⟨fun _ => 0, fun _ => by norm_num, ?_, hcoeff⟩
    simp [LowMaskCoding.indexedCode]

#print axioms binomial_iff_source
#print axioms source_of_zero
#print axioms zero_of_source
