import DiophantineConsistency.GapSourceWords66
open DiophantineConsistency.GapSourceWords66
#print axioms sum_positions
#print axioms highInt_eq
#print axioms scale
#print axioms highInt_pos
#print axioms word_pos
#print axioms word_cast
#print axioms mask_eq_population
#print axioms mask_cast
#print axioms weak_cap_bounds
#print axioms rank_cast
#print axioms literal_valid_of_height
#print axioms literal_valid_pow

-- The sharp whole-tuple widths have exactly the even coefficient exponent.
example (ports : Fin 4 → ℤ)
    (hb : 0 ≤ ports 0 ∧ ports 0 < 2^429959)
    (hk : 0 ≤ ports 1 ∧ ports 1 < 2^434054)
    (hm : 0 ≤ ports 2 ∧ ports 2 < 2^429959)
    (hf : 0 ≤ ports 3 ∧ ports 3 < 2*2^429959) :
    Valid (literalParameters ports) 432007 :=
  literal_valid_pow ports 429959 434054 432007 (by decide) (by decide) (by decide) hb hk hm hf
