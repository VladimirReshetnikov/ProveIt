import DiophantineConsistency.CompactCoefficientDecoder
import DiophantineConsistency.ArithmeticCyclicWord
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactPartialBand
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open ArithmeticCyclicWord ArithmeticWindowDigits
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Source digit at the target column for a selector in one reflected band. -/
noncomputable def selectorDigit (n C k : V) (T : ℕ) (i : Fin 943) : V :=
  dig 67 C (cyc n k (((T-i.val):ℕ):V))

/-- Source digit at the target column for a copy position in one reflected band. -/
noncomputable def copyDigit (pos : Fin 41 → ℕ) (n C k : V) (T : ℕ) (j : Fin 41) : V :=
  dig 67 C (cyc n k (((T-pos j):ℕ):V))

/-- The weighted selector/copy contribution of one band equals the local
    decoder expression. This does not identify the full graph column. -/
theorem band_decomposition (pos : Fin 41 → ℕ) (T : ℕ) (n C k : V)
    (hn : 0<n) (hk : k<n) (hC : C<Exp.exp (67*n)) :
    (∑ i : Fin 943, ((CompactCoefficientMass.selector (Compact943Data.row i):ℕ):V) *
      dig 67 (rot 67 n C ((((T-i.val):ℕ):V)%n)) k) +
    (∑ j : Fin 41, ((2^(10+j.val):ℕ):V) *
      dig 67 (rot 67 n C ((((T-pos j):ℕ):V)%n)) k) =
    (∑ i, selectorDigit n C k T i) + Exp.exp 10 *
      ((∑ i, (Exp.exp 41-Compact943Decoder.tileValue (V:=V) i) * selectorDigit n C k T i) +
       ∑ j, (2:V)^j.val * copyDigit pos n C k T j) := by
  have hi : ∀ i : Fin 943,
      dig 67 (rot 67 n C ((((T-i.val):ℕ):V)%n)) k = selectorDigit n C k T i := by
    intro i
    unfold selectorDigit
    rw [dig_rot 67 n C _ k (mod_lt _ hn) hk hC, cyc_mod n k _ hn]
  have hj : ∀ j : Fin 41,
      dig 67 (rot 67 n C ((((T-pos j):ℕ):V)%n)) k = copyDigit pos n C k T j := by
    intro j
    unfold copyDigit
    rw [dig_rot 67 n C _ k (mod_lt _ hn) hk hC, cyc_mod n k _ hn]
  simp_rw [hi,hj]
  exact CompactCoefficientDecoder.finite_decomposition _ _
end CompactPartialBand
#print axioms CompactPartialBand.band_decomposition
