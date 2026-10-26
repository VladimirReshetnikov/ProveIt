import DiophantineConsistency.NativeOuterSeedConstruction

namespace DiophantineConsistency.NativeOuterSeedConstructionChecks

open NativeOuterSeedConstruction Jones1982 Pell

set_option Elab.async false

-- The smallest binary width already has actual odd ranks of both mod-four
-- classes. Outer construction does not silently assume the auxiliary class3.
example : Nonempty (Seed 1 31) :=
  exists_outer_seed 1 31 15 (by decide) (by decide) (by decide)
example : Nonempty (Seed 1 61) :=
  exists_outer_seed 1 61 30 (by decide) (by decide) (by decide)
example : 31%4 = 3 ∧ 61%4 = 1 := by decide

-- Population, not an assumed binomial divisibility or Pell interval,
-- supplies the exact q-cubed common scale.
example {u R r : ℕ} (hu : 0<u) (hR : R=2*r+1) (hp : σ 2 R=3*u+2) :
    ∃ Y : ℕ, 0<Y ∧ (2^u)^3 ∣ Y := by
  obtain ⟨d⟩ := exists_outer_seed u R r hu hR hp
  exact ⟨d.Y,d.Y_pos,⟨d.s,by rw [d.scale,mul_comm]⟩⟩

-- All six independent outer witnesses are strictly positive and satisfy
-- the exact displayed definitions of both norm blocks and the index.
example {u R r : ℕ} (hu : 0<u) (hR : R=2*r+1) (hp : σ 2 R=3*u+2) :
    ∃ d : Seed u R,
      0<d.s ∧ 0<d.tau ∧ 0<d.eta ∧ 0<d.zeta ∧ 0<d.h ∧ 0<d.gamma ∧
      d.c = (d.eta+d.zeta)*d.Y+d.eta ∧
      d.eta+d.zeta = 1+R+(2^R*d.Y)*d.h ∧
      d.D = 2^R+d.a*d.c+d.gamma*(4*d.a+3) ∧
      d.tau^2 = 1+(2^R*d.Y^2)*(2^R*d.Y^2+1)*(d.eta+d.zeta)^2 := by
  obtain ⟨d⟩ := exists_outer_seed u R r hu hR hp
  refine ⟨d,d.s_pos,d.tau_pos,d.eta_pos,d.zeta_pos,d.h_pos,d.gamma_pos,?_,?_,d.root,?_⟩
  · simpa only [d.split] using d.interval
  · simpa only [d.split] using d.index
  · simpa only [d.split] using d.first_norm

-- The doubled first ordinate matters: the first fundamental example has
-- tau3,k2,Q1. Replacing k2 by the undoubled value1 breaks the norm.
example : (3:ℕ)^2 = 1+1*(1+1)*2^2 ∧ (3:ℕ)^2 ≠ 1+1*(1+1)*1^2 := by decide

-- Positive width is needed for the derived r>=4 bound: width0/rank3
-- satisfies the population identity but has half-index1.
example : σ 2 3 = 3*0+2 ∧ 3=2*1+1 ∧ ¬4≤(1:ℕ) := by decide

-- The actual main ordinate is retained at the specified rank.
example {u R : ℕ} (d : Seed u R) :
    d.c = yn (by omega : 1 < d.a+2) R ∧
      d.D^2 = 1+((d.a+2)^2-1)*d.c^2 := ⟨d.main_index,d.main_norm⟩

#print axioms population_sizes
#print axioms scaled_half_floor
#print axioms pell_interval
#print axioms exists_outer_seed

end DiophantineConsistency.NativeOuterSeedConstructionChecks
