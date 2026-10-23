import DiophantineConsistency.NativePellBootstrap

open DiophantineConsistency.NativePellBootstrap Diophantine Pell

-- The actual square first norm has tau=5,k=2 at Q=2.
-- This tests the factor-two classification rather than a tau*(tau+1) variant.
example : ∃ n, 0 < n ∧ (5 : ℕ) = xn (by decide : 1 < 5) n ∧
    (2 : ℕ) = 2 * yn (by decide : 1 < 5) n :=
  first_norm_classification (Q := 2) (by decide) (by decide) (by decide)

-- The generic box permits MF_source between beta and 2*beta.
example : PortBox (![10,0,3,19] : Fin 4 → ℤ) := by
  constructor <;> decide

#print axioms main_classification
#print axioms twice_index_lt
#print axioms source_main_classification
#print axioms source_c_bounds
#print axioms source_Y_ge_two
#print axioms source_rank_half_lt
#print axioms source_main_and_half_bounds
#print axioms firstUnit_fundamental
#print axioms first_norm_classification
#print axioms large_of_six_le
#print axioms firstQ_pos
#print axioms source_first_registers
#print axioms source_first_classification
#print axioms first_index_lower
#print axioms main_index_gt_first
#print axioms source_a_eq
#print axioms source_base_separation
#print axioms source_bootstrap
#print axioms source_rank_eq_target
#print axioms source_transport_positive
#print axioms source_native_rank_ge_twentyfour
#print axioms source_scale_eq
#print axioms source_window_bound
#print axioms source_bootstrap_of_portBox
#print axioms source_auxiliary_norms
#print axioms source_main_index_exact
