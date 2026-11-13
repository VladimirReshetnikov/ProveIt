import DiophantineConsistency.Mixed121.Mixed121Band
import DiophantineConsistency.Compact44.CompactHeterogeneousCarry
import DiophantineConsistency.ArithmeticStandardCasts
import Mathlib.Data.Fintype.BigOperators

/-! # The 121x8801 kernel as two reflected bands and a bare part

There are three groups of results.

* A width-generic copy of Compact44's `BandCarryInputs` and
  `GenericBandCarryFamily`. Their proofs never used the literal `67` except
  as the width, so here the width is a parameter `w`.
* The 121-bit band rotation. Modulo `2^(121n) − 1`, the product of a reflected
  clause band with a native word `C` is the corresponding sum of rotations of
  `C` (`band_rotation_congr`), and its column `k` is the decoder input of
  `Mixed121Band` (`band_column`).
* `kernel_bands`, which casts the concrete kernel `paramKernel rho` into any
  model as `kernelBand 4393 + kernelBand 5495 + bareKernel`. The bare part is
  `ρ^30 + ρ^62 + ρ^1100 + ρ^2200 + ρ^8843`, where `ρ^8843 = ρ^L·ρ^42`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace Mixed121Rotation
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open ArithmeticCyclicWord ArithmeticWindowDigits CompactHeterogeneousCarry
attribute [local irreducible] Compact943Data.rows
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Width-generic carry inputs -/

theorem aligned_rotation_bounds (w n C e D : V) (hn : 0<n)
    (hC : C<Exp.exp (w*n)) (hcap : ∀ k<n, dig w C k≤D) :
    rot w n C (e%n) < Exp.exp (w*n) ∧
      ∀ k<n, dig w (rot w n C (e%n)) k≤D := by
  have he : e%n<n := mod_lt _ hn
  refine ⟨rot_lt w n C _ (le_of_lt he) hC, ?_⟩
  intro k hk
  rw [dig_rot w n C _ k he hk hC]
  exact hcap _ (cyc_lt hn k (e%n))

section family
variable {ι : Type*} [Fintype ι]

def coefficient (a : ι → V) : ι ⊕ Unit → V
  | .inl i => a i
  | .inr _ => 1

def word (w n C : V) (e : ι → V) (T : V) : ι ⊕ Unit → V
  | .inl i => rot w n C (e i%n)
  | .inr _ => T

def cap (w : V) : ι ⊕ Unit → V
  | .inl _ => 3
  | .inr _ => Exp.exp w-1

theorem carry_input (w n C T F b : V) (a e : ι → V)
    (hn : 0<n) (hM : 0<Exp.exp (w*n)-1)
    (hC : C<Exp.exp (w*n)) (hCcap : ∀ k<n, dig w C k≤3)
    (hT : T<Exp.exp (w*n)) (hTcap : ∀ k<n, dig w T k≤Exp.exp w-1)
    (hF : F<Exp.exp (w*n)-1)
    (hgraph : ((∑ i, a i*rot w n C (e i%n)) + T) % (Exp.exp (w*n)-1)=F)
    (hmass : ((∑ i, a i*3)+(Exp.exp w-1))+1 ≤ (b+1)*(Exp.exp w-1)) :
    CarryInput w n F b (cap (ι:=ι) w) (coefficient a) (word w n C e T) := by
  refine ⟨hn,hM,?_,?_,hF,?_,?_⟩
  · intro i
    cases i with
    | inl i => exact (aligned_rotation_bounds w n C (e i) 3 hn hC hCcap).1
    | inr i => exact hT
  · intro i k hk
    cases i with
    | inl i => exact (aligned_rotation_bounds w n C (e i) 3 hn hC hCcap).2 k hk
    | inr i => exact hTcap k hk
  · simp only [Fintype.sum_sum_type, Fintype.sum_unique, coefficient, word, one_mul]
    rw [hgraph, mod_eq_self_of_lt hF]
  · simpa only [Fintype.sum_sum_type, Fintype.sum_unique, coefficient, cap, one_mul] using hmass
end family

/-! ## The 121-bit bands -/

def selectorCoeff (i : Fin 943) : V := ((Mixed121Kernel.clause (Compact943Data.row i) : ℕ) : V)
def copyCoeff (j : Fin 44) : V := ((Mixed121Kernel.W j.val : ℕ) : V)
def selectorOffset (T : ℕ) (i : Fin 943) : V := (((T - i.val : ℕ)) : V)
def copyOffset (T : ℕ) (j : Fin 44) : V := (((T - Mixed121Kernel.extraPos j : ℕ)) : V)

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
      Exp.exp 10 * ModelDigitTransfer.dsum (Exp.exp 2) (Mixed121Band.copyDigit n C k T) 44 :=
  Mixed121Band.band_decomposition T n C k hn hk hC

/-! ## The bare part and the kernel -/

def bareOffset (i : Fin 5) : V := ((![30, 62, 1100, 2200, 8843] i : ℕ) : V)
def bareKernel : V := ∑ i : Fin 5, Exp.exp (121 * bareOffset i)
def bareRotated (n C : V) : V := ∑ i : Fin 5, rot 121 n C (bareOffset i % n)

theorem bare_congr (n C : V) (hn : 0<n) (hM : 0<Exp.exp (121*n)-1) :
    (bareKernel * C) % (Exp.exp (121*n)-1) = bareRotated n C % (Exp.exp (121*n)-1) := by
  have h := kernel_rotation_congr (121:V) n C (fun _ : Fin 5 => (1:V)) bareOffset hn hM
  simpa [bareKernel, bareRotated] using h

theorem add_congr_mod (M a b c d : V) (hM : 0<M)
    (ha : a%M=b%M) (hb : c%M=d%M) : (a+c)%M=(b+d)%M := by
  rw [mod_add hM, ha, hb, ← mod_add hM]

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

theorem cast_rho_pow (e : ℕ) :
    ((Mixed121Kernel.rho : ℕ) : V)^e = Exp.exp ((121 : V) * (e : V)) := by
  calc
    ((Mixed121Kernel.rho : ℕ) : V)^e = (((2^121 : ℕ)^e : ℕ) : V) := by
      rw [← Nat.cast_pow, Mixed121Kernel.rho]
    _ = ((2^(121*e) : ℕ) : V) := by rw [pow_mul]
    _ = Exp.exp ((121 : V) * (e : V)) := by
      rw [← ArithmeticStandardCasts.cast_exp (V:=V) (121*e)]
      simp only [Nat.cast_mul, Nat.cast_ofNat]

theorem bare_formula :
    bareKernel (V:=V) =
      Exp.exp (121*(30:V)) + Exp.exp (121*(62:V)) + Exp.exp (121*(1100:V)) +
      Exp.exp (121*(2200:V)) + Exp.exp (121*(8843:V)) := by
  unfold bareKernel bareOffset
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Nat.cast_ofNat, add_zero]
  ring

/-- The concrete kernel in a model: two reflected clause bands and the bare
part. -/
theorem kernel_bands :
    ((Mixed121Kernel.paramKernel Mixed121Kernel.rho : ℕ) : V) =
      kernelBand 4393 + kernelBand 5495 + bareKernel := by
  rw [Mixed121Kernel.cast_paramKernel, bare_formula]
  have h8843 : ((Mixed121Kernel.rho : ℕ) : V)^8801 * ((Mixed121Kernel.rho : ℕ) : V)^42 =
      ((Mixed121Kernel.rho : ℕ) : V)^8843 := by rw [← pow_add]
  rw [h8843]
  simp only [cast_rho_pow, Nat.cast_ofNat]
  unfold kernelBand selectorCoeff copyCoeff selectorOffset copyOffset
  simp only [mul_add, Finset.sum_add_distrib]
  ring
end Mixed121Rotation
#print axioms Mixed121Rotation.aligned_rotation_bounds
#print axioms Mixed121Rotation.carry_input
#print axioms Mixed121Rotation.band_rotation_congr
#print axioms Mixed121Rotation.band_column
#print axioms Mixed121Rotation.bare_congr
#print axioms Mixed121Rotation.combined_congr
#print axioms Mixed121Rotation.cast_rho_pow
#print axioms Mixed121Rotation.kernel_bands
