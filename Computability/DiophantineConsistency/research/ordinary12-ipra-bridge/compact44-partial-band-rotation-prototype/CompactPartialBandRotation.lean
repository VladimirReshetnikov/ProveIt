import DiophantineConsistency.CompactPartialBand
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactPartialBandRotation
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open ArithmeticCyclicWord ArithmeticWindowDigits
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def selectorCoeff (i : Fin 943) : V := (CompactCoefficientMass.selector (Compact943Data.row i):ℕ)
def copyCoeff (j : Fin 41) : V := ((2^(10+j.val):ℕ):V)
def selectorOffset (T : ℕ) (i : Fin 943) : V := (((T-i.val):ℕ):V)
def copyOffset (pos : Fin 41 → ℕ) (T : ℕ) (j : Fin 41) : V := (((T-pos j):ℕ):V)

def kernelBand (pos : Fin 41 → ℕ) (T : ℕ) : V :=
  (∑ i, selectorCoeff i * Exp.exp (67*selectorOffset T i)) +
  (∑ j, copyCoeff j * Exp.exp (67*copyOffset pos T j))
def rotatedBand (pos : Fin 41 → ℕ) (T : ℕ) (n C : V) : V :=
  (∑ i, selectorCoeff i * rot 67 n C (selectorOffset T i % n)) +
  (∑ j, copyCoeff j * rot 67 n C (copyOffset pos T j % n))
def columnBand (pos : Fin 41 → ℕ) (T : ℕ) (n C k : V) : V :=
  (∑ i, selectorCoeff i * dig 67 (rot 67 n C (selectorOffset T i % n)) k) +
  (∑ j, copyCoeff j * dig 67 (rot 67 n C (copyOffset pos T j % n)) k)

theorem band_rotation_congr (pos : Fin 41 → ℕ) (T : ℕ) (n C : V)
    (hn : 0<n) (hM : 0<Exp.exp (67*n)-1) :
    (kernelBand pos T * C) % (Exp.exp (67*n)-1) =
      rotatedBand pos T n C % (Exp.exp (67*n)-1) := by
  have hs := kernel_rotation_congr (67:V) n C selectorCoeff (selectorOffset T) hn hM
  have hc := kernel_rotation_congr (67:V) n C copyCoeff (copyOffset pos T) hn hM
  unfold kernelBand rotatedBand
  rw [add_mul, mod_add hM, hs, hc, ← mod_add hM]

theorem band_column (pos : Fin 41 → ℕ) (T : ℕ) (n C k : V)
    (hn : 0<n) (hk : k<n) (hC : C<Exp.exp (67*n)) :
    columnBand pos T n C k =
    (∑ i, CompactPartialBand.selectorDigit n C k T i) + Exp.exp 10 *
      ((∑ i, (Exp.exp 41-Compact943Decoder.tileValue (V:=V) i) * CompactPartialBand.selectorDigit n C k T i) +
       ∑ j, (2:V)^j.val * CompactPartialBand.copyDigit pos n C k T j) := by
  exact CompactPartialBand.band_decomposition pos T n C k hn hk hC
#print axioms CompactPartialBandRotation.band_rotation_congr
#print axioms CompactPartialBandRotation.band_column
end CompactPartialBandRotation
