import DiophantineConsistency.NativePackingPopulation

namespace DiophantineConsistency.NativePackingPopulationChecks

open Jones1982 NativePackingPopulation
set_option Elab.async false

-- A zero-width lower window is retained; the unrestricted top block may be large.
example : σ 2 (0+2^0*0+(2^0)^2*0+(2^0)^3*37) = σ 2 37 := by
  simpa only [σ_two_zero,zero_add] using
    four_block_exact (u:=0) (A:=0) (B:=0) (C:=0) 37
      (by decide) (by decide) (by decide)

-- Independent lower masks and complement blocks, with a nonzero overlap-free sum.
example : σ 2 ((1+6)+8*(2+5)+8^2*(8-1-1)+8^3*(8-1-2)) = 10 := by
  have h := mask_population (u:=3) (A:=1) (F:=2) (M:=6) (H:=5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  convert h using 1 <;> decide

-- Carrying within one lower block invalidates the claimed population sum.
example : σ 2 ((1+1)+8*(2+5)+8^2*(8-1-1)+8^3*(8-1-2)) ≠
    2*3+σ 2 1+σ 2 5 := by decide

-- Two strict representatives alone do not make their sum strict.
example : (7:ℕ)<2^3 ∧ 7<2^3 ∧ ¬7+7<2^3 := by decide

#print axioms disjoint_add_lt
#print axioms four_block_exact
#print axioms mask_population
#print axioms calibrated_population

end DiophantineConsistency.NativePackingPopulationChecks
