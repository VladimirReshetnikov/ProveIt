import DiophantineConsistency.CurrentOneHot2011
import DiophantineConsistency.CurrentCellLabels2011
import DiophantineConsistency.CurrentCellTranslation2011

/-!
ADD-ONLY PROPOSAL; not imported by upstream and not claimed compiled.
This packages existing hypotheses, not new native semantics. In particular,
empty cells remain possible and no machine or ConZFC conclusion is introduced.
-/

namespace SimplificationProposals.NativeWordFacts

open DiophantineConsistency
open NativeCyclicConvolution NativeCyclicRotation

variable {N : ℕ} [NeZero (N * 2011)]

/-- Minimal shared hypotheses for counting and local decoding.
The phase, origin, carry recurrence, and polynomial provenance are NOT fields:
they belong to later stages or stronger interfaces. -/
structure WordFacts (c carry digits : ZMod (N * 2011) → ℕ) (W : ℕ) : Prop where
  boolean : ∀ i, c i ≤ 1
  support : ∀ i, i.val % 2011 ∉ CurrentMasks2011.lowSupport → c i = 0
  carry_bound : ∀ i, carry i ≤ 57
  local_equation : ∀ i,
    convolution CurrentKernel2011.folded c i + binaryRotation 47 W c i +
      carry (i - 1) = digits i + CurrentMasks2011.radix * carry i
  mask_tests : ∀ i, digits i &&& CurrentHighDigits2011.maskDigits i = 0

def temporalExponent (v : Fin 14 → ℤ) (N : ℕ) : ℕ :=
  (Carrier65.core CurrentWindowCarry2011.ports v).rank.toNat - 47 * (N * 2011)

/-- Adapter leaves the original broad Facts structure and public API intact. -/
theorem of_polynomial_facts (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ)
    (h : CurrentPolynomialWindow2011.Facts v N x c carry digits) :
    WordFacts c carry digits (temporalExponent v N) :=
  ⟨h.boolean, h.support, h.carry_bound, h.carry_equation, h.mask_tests⟩

/-- Uses the already implemented Cell subtype rather than introducing a rival. -/
theorem WordFacts.count_le_one
    {c carry digits : ZMod (N * 2011) → ℕ} {W : ℕ}
    (h : WordFacts c carry digits W) (b : CurrentCellTranslation2011.Cell N) :
    CurrentClause2011.selectorCount c b.val ≤ 1 :=
  CurrentOneHot2011.literal_count_le_one c carry digits W
    h.boolean h.support h.carry_bound h.local_equation h.mask_tests b.val b.property

/-- Fractional phase remains an explicit prerequisite; one-hot is derived first. -/
theorem WordFacts.decode_cell
    {c carry digits : ZMod (N * 2011) → ℕ} {W : ℕ}
    (h : WordFacts c carry digits W) (hphase : W % 47 = 0)
    (b : CurrentCellTranslation2011.Cell N) :
    CurrentCellLabels2011.CellDecoded c carry W b.val ∧ carry (b.val + 1005) = 0 :=
  CurrentCellLabels2011.decode_cell c carry digits W
    h.boolean h.support h.carry_bound h.local_equation h.mask_tests hphase
    b.val b.property (h.count_le_one b)

#print axioms of_polynomial_facts
#print axioms WordFacts.count_le_one
#print axioms WordFacts.decode_cell

end SimplificationProposals.NativeWordFacts
