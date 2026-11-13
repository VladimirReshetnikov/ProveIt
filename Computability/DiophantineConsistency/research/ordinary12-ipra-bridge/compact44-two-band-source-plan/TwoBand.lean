import DiophantineConsistency.CompactPartialBandRotation
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TwoBand
open DiophantineConsistency CompactPartialBandRotation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def bareOffset (i : Fin 5) : V := ((![30, 62, 1100, 2201, 8849] i : ℕ) : V)
def bareKernel : V := ∑ i : Fin 5, Exp.exp (67 * bareOffset i)
def bareRotated (n C : V) : V := ∑ i : Fin 5, rot 67 n C (bareOffset i % n)

theorem bare_congr (n C : V) (hn : 0<n) (hM : 0<Exp.exp (67*n)-1) :
    (bareKernel * C) % (Exp.exp (67*n)-1) = bareRotated n C % (Exp.exp (67*n)-1) := by
  have h := kernel_rotation_congr (67:V) n C (fun _ : Fin 5 => (1:V)) bareOffset hn hM
  simpa [bareKernel, bareRotated] using h

theorem combined_congr (pos : Fin 41 → ℕ) (K n C w F : V)
    (hn : 0<n) (hM : 0<Exp.exp (67*n)-1)
    (hK : K = kernelBand pos 4393 + kernelBand pos 5495 + bareKernel)
    (hgraph : ((K+w)*C) % (Exp.exp (67*n)-1) = F) :
    ((rotatedBand pos 4393 n C + rotatedBand pos 5495 n C + bareRotated n C) + w*C)
      % (Exp.exp (67*n)-1) = F := by
  let M : V := Exp.exp (67*n)-1
  have h1 := band_rotation_congr pos 4393 n C hn hM
  have h2 := band_rotation_congr pos 5495 n C hn hM
  have h3 := bare_congr n C hn hM
  have hp : ((kernelBand pos 4393 + kernelBand pos 5495 + bareKernel) * C) % M =
      (rotatedBand pos 4393 n C + rotatedBand pos 5495 n C + bareRotated n C) % M := by
    calc
      _ = (((kernelBand pos 4393*C + kernelBand pos 5495*C) % M) +
          (bareKernel*C)%M)%M := by rw [add_mul, add_mul, mod_add hM]
      _ = ((((kernelBand pos 4393*C)%M + (kernelBand pos 5495*C)%M)%M) +
          (bareKernel*C)%M)%M := by rw [mod_add hM]
      _ = (((rotatedBand pos 4393 n C)%M + (rotatedBand pos 5495 n C)%M)%M +
          (bareRotated n C)%M)%M := by rw [h1, h2, h3]
      _ = _ := by rw [← mod_add hM, ← mod_add hM]
  rw [hK, add_mul, mod_add hM, hp, ← mod_add hM] at hgraph
  exact hgraph
#print axioms TwoBand.bare_congr
#print axioms TwoBand.combined_congr
end TwoBand
