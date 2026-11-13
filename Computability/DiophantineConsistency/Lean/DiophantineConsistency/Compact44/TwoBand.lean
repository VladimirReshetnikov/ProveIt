import DiophantineConsistency.Compact44.CompactPartialBandRotation
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

theorem add_congr_mod (M a b c d : V) (hM : 0<M)
    (ha : a%M=b%M) (hb : c%M=d%M) : (a+c)%M=(b+d)%M := by
  rw [mod_add hM, ha, hb, ← mod_add hM]

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
    rw [add_mul, add_mul]
    exact add_congr_mod M _ _ _ _ hM (add_congr_mod M _ _ _ _ hM h1 h2) h3
  have hr : (((kernelBand pos 4393 + kernelBand pos 5495 + bareKernel)*C) + w*C)%M =
      ((rotatedBand pos 4393 n C + rotatedBand pos 5495 n C + bareRotated n C) + w*C)%M :=
    add_congr_mod M _ _ _ _ hM hp rfl
  rw [hK, add_mul] at hgraph
  exact hr.symm.trans hgraph
#print axioms TwoBand.bare_congr
#print axioms TwoBand.add_congr_mod
#print axioms TwoBand.combined_congr
end TwoBand
