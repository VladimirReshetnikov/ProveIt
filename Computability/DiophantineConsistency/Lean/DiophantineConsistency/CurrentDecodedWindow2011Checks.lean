import DiophantineConsistency.CurrentDecodedWindow2011

namespace DiophantineConsistency.CurrentDecodedWindow2011Checks

open CurrentDecodedWindow2011 CurrentPolynomialWindow2011 CurrentWindowCarry2011

set_option Elab.async false

-- The decoded-cell endpoint adds no label, count, phase or occupation premise.
example (v : Fin 14 → ℤ) (hv : ∀ j, 0 < v j)
    (hz : MvPolynomial.eval v (Carrier65.polynomial ports) = 0) :
    ∃ N, ∃ hN : 0 < N, DecodedWindow v N hN :=
  polynomial_zero_decoded_window v hv hz

-- Start's actual South complement is a conclusion of the polynomial data.
example {N : ℕ} [NeZero (N * 2011)] (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c carry digits) :
    CurrentCellLabels2011.binaryWord
      (fun j => c (((942 + j : ℕ) : ZMod (N * 2011)))) 9 = 510 :=
  facts_start_south v x c carry digits h

#print axioms facts_decode_cell
#print axioms facts_start_south
#print axioms facts_terminal_south
#print axioms polynomial_zero_decoded_window

end DiophantineConsistency.CurrentDecodedWindow2011Checks
