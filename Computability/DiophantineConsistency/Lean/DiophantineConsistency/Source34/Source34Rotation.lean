import DiophantineConsistency.Source34.Source34Band
import DiophantineConsistency.Mixed121.Mixed121Rotation

/-! # The source34 kernel as two reflected bands and a bare part

`Mixed121Rotation` at the source34 tuple. The width-generic carry inputs
(`Mixed121Rotation.aligned_rotation_bounds`, `coefficient`, `word`, `cap`,
`carry_input`), the selector coefficients and offsets, `add_congr_mod` and
`cast_rho_pow` are shared and used from `Mixed121Rotation`. What changes:

* `copyOffset` reads the source34 positions `Source34Kernel.extraPos`, so the
  bands `kernelBand`, `rotatedBand`, `columnBand` and their lemmas
  `band_rotation_congr`, `band_column` are re-declared;
* the bare part is `ρ^40 + ρ^41 + ρ^1100 + ρ^2200 + ρ^8802`, where
  `ρ^8802 = ρ^L·ρ` (`bareOffset = ![40, 41, 1100, 2200, 8802]`);
* `kernel_bands` casts `Source34Kernel.paramKernel rho` into any model as
  `kernelBand 4393 + kernelBand 5495 + bareKernel`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace Source34Rotation
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open ArithmeticCyclicWord ArithmeticWindowDigits CompactHeterogeneousCarry
open Mixed121Rotation (selectorCoeff copyCoeff selectorOffset add_congr_mod cast_rho_pow)
attribute [local irreducible] Compact943Data.rows
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The 121-bit bands -/

def copyOffset (T : ℕ) (j : Fin 44) : V := (((T - Source34Kernel.extraPos j : ℕ)) : V)

def kernelBand (T : ℕ) : V :=
  (∑ i, selectorCoeff i * Exp.exp (121*selectorOffset T i)) +
  (∑ j, copyCoeff j * Exp.exp (121*copyOffset T j))
def rotatedBand (T : ℕ) (n C : V) : V :=
  (∑ i, selectorCoeff i * rot 121 n C (selectorOffset T i % n)) +
  (∑ j, copyCoeff j * rot 121 n C (copyOffset T j % n))
def columnBand (T : ℕ) (n C k : V) : V :=
  (∑ i, selectorCoeff i * dig 121 (rot 121 n C (selectorOffset T i % n)) k) +
  (∑ j, copyCoeff j * dig 121 (rot 121 n C (copyOffset T j % n)) k)

theorem band_rotation_congr (T : ℕ) (n C : V)
    (hn : 0<n) (hM : 0<Exp.exp (121*n)-1) :
    (kernelBand T * C) % (Exp.exp (121*n)-1) =
      rotatedBand T n C % (Exp.exp (121*n)-1) := by
  have hs := kernel_rotation_congr (121:V) n C selectorCoeff (selectorOffset T) hn hM
  have hc := kernel_rotation_congr (121:V) n C copyCoeff (copyOffset T) hn hM
  unfold kernelBand rotatedBand
  rw [add_mul, mod_add hM, hs, hc, ← mod_add hM]

theorem band_column (T : ℕ) (n C k : V)
    (hn : 0<n) (hk : k<n) (hC : C<Exp.exp (121*n)) :
    columnBand T n C k =
    (∑ i, Mixed121Band.selDigit n C k T i *
        (1 + Exp.exp 10 * ModelDigitTransfer.dsum (Exp.exp 2)
          (fun d => (Mixed121Digits.digit (Compact943Data.row i) d : V)) 44)) +
      Exp.exp 10 * ModelDigitTransfer.dsum (Exp.exp 2) (Source34Band.copyDigit n C k T) 44 :=
  Source34Band.band_decomposition T n C k hn hk hC

/-! ## The bare part and the kernel -/

def bareOffset (i : Fin 5) : V := ((![40, 41, 1100, 2200, 8802] i : ℕ) : V)
def bareKernel : V := ∑ i : Fin 5, Exp.exp (121 * bareOffset i)
def bareRotated (n C : V) : V := ∑ i : Fin 5, rot 121 n C (bareOffset i % n)

theorem bare_congr (n C : V) (hn : 0<n) (hM : 0<Exp.exp (121*n)-1) :
    (bareKernel * C) % (Exp.exp (121*n)-1) = bareRotated n C % (Exp.exp (121*n)-1) := by
  have h := kernel_rotation_congr (121:V) n C (fun _ : Fin 5 => (1:V)) bareOffset hn hM
  simpa [bareKernel, bareRotated] using h

/-- The full kernel product, reduced modulo `2^(121n) − 1`, is the sum of the
rotated bands. -/
theorem combined_congr (K n C w F : V)
    (hn : 0<n) (hM : 0<Exp.exp (121*n)-1)
    (hK : K = kernelBand 4393 + kernelBand 5495 + bareKernel)
    (hgraph : ((K+w)*C) % (Exp.exp (121*n)-1) = F) :
    ((rotatedBand 4393 n C + rotatedBand 5495 n C + bareRotated n C) + w*C)
      % (Exp.exp (121*n)-1) = F := by
  let M : V := Exp.exp (121*n)-1
  have h1 := band_rotation_congr 4393 n C hn hM
  have h2 := band_rotation_congr 5495 n C hn hM
  have h3 := bare_congr n C hn hM
  have hp : ((kernelBand 4393 + kernelBand 5495 + bareKernel) * C) % M =
      (rotatedBand 4393 n C + rotatedBand 5495 n C + bareRotated n C) % M := by
    rw [add_mul, add_mul]
    exact add_congr_mod M _ _ _ _ hM (add_congr_mod M _ _ _ _ hM h1 h2) h3
  have hr : (((kernelBand 4393 + kernelBand 5495 + bareKernel)*C) + w*C)%M =
      ((rotatedBand 4393 n C + rotatedBand 5495 n C + bareRotated n C) + w*C)%M :=
    add_congr_mod M _ _ _ _ hM hp rfl
  rw [hK, add_mul] at hgraph
  exact hr.symm.trans hgraph

attribute [local irreducible] Mixed121Kernel.rho

theorem bare_formula :
    bareKernel (V:=V) =
      Exp.exp (121*(40:V)) + Exp.exp (121*(41:V)) + Exp.exp (121*(1100:V)) +
      Exp.exp (121*(2200:V)) + Exp.exp (121*(8802:V)) := by
  unfold bareKernel bareOffset
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Nat.cast_ofNat, add_zero]
  ring

/-- The concrete source34 kernel in a model: two reflected clause bands and
the bare part. -/
theorem kernel_bands :
    ((Source34Kernel.paramKernel Mixed121Kernel.rho : ℕ) : V) =
      kernelBand 4393 + kernelBand 5495 + bareKernel := by
  rw [Source34Kernel.cast_paramKernel, bare_formula]
  have h8802 : ((Mixed121Kernel.rho : ℕ) : V)^8801 * ((Mixed121Kernel.rho : ℕ) : V)^1 =
      ((Mixed121Kernel.rho : ℕ) : V)^8802 := by rw [← pow_add]
  rw [h8802]
  simp only [cast_rho_pow, Nat.cast_ofNat]
  unfold kernelBand selectorCoeff copyCoeff selectorOffset copyOffset
  simp only [mul_add, Finset.sum_add_distrib]
  ring
end Source34Rotation
#print axioms Source34Rotation.band_rotation_congr
#print axioms Source34Rotation.band_column
#print axioms Source34Rotation.bare_congr
#print axioms Source34Rotation.combined_congr
#print axioms Source34Rotation.kernel_bands
