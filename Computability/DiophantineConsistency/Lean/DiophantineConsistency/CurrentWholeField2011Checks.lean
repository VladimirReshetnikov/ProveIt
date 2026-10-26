import DiophantineConsistency.CurrentWholeField2011

/-! Focused composition checks. The native checks accept only the original
Facts, without a separate occupation, marker, Start or alignment premise. -/

namespace DiophantineConsistency.CurrentWholeField2011Checks

open CurrentPolynomialWindow2011 CurrentDecodedWindow2011 CurrentWholeField2011
  CurrentCellLabels2011 CurrentCellTranslation2011

set_option Elab.async false

example (f : ℕ → ℕ) (hf : ∀ j, j < 9 → f j ≤ 1)
    (hw : binaryWord f 9 = 510) : f 1 = 1 ∧ f 2 = 1 :=
  binaryWord_510_bits f hf hw

variable {N : ℕ} [NeZero (N * 2011)]

example (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c carry digits) :
    c 943 = 1 ∧ c 944 = 1 := facts_start_bits v x c carry digits h

example (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c carry digits) :
    (((Carrier65.core CurrentWindowCarry2011.ports v).rank.toNat -
      47 * (N * 2011)) / 47) % 2011 = 0 := facts_whole_field v x c carry digits h

/-- The full cell bit length divides the original rank shift, with no
upper bound or normalization assumption on that shift. -/
example (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c carry digits) :
    94517 ∣ (Carrier65.core CurrentWindowCarry2011.ports v).rank.toNat -
      47 * (N * 2011) :=
  Nat.dvd_of_mod_eq_zero (facts_cell_aligned v x c carry digits h)

/-- Every decoded cell remains on the original c/carry functions after
alignment; no fresh word or additional native premise is introduced. -/
example (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c carry digits)
    (b : Cell N) :
    CellDecoded c carry
      ((Carrier65.core CurrentWindowCarry2011.ports v).rank.toNat - 47 * (N * 2011)) b ∧
    (((Carrier65.core CurrentWindowCarry2011.ports v).rank.toNat -
      47 * (N * 2011)) / 47) % 2011 = 0 :=
  ⟨(facts_decode_cell v x c carry digits h b b.property).1,
    facts_whole_field v x c carry digits h⟩

example (v : Fin 14 → ℤ) (hv : ∀ j, 0 < v j)
    (hz : MvPolynomial.eval v CurrentPolynomialWindow2011.polynomial = 0) :
    ∃ N, ∃ hN : 0 < N, AlignedWindow v N hN :=
  polynomial_zero_aligned_window v hv hz

#print axioms binaryWord_510_bits
#print axioms facts_start_bits
#print axioms facts_copy_marker
#print axioms facts_whole_field
#print axioms facts_cell_aligned
#print axioms polynomial_zero_aligned_window

end DiophantineConsistency.CurrentWholeField2011Checks
