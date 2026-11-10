import DiophantineConsistency.LinCof.LCBootstrap
import DiophantineConsistency.P138.P138NoRoot

/-! # The quintic has no rational root; `s` and `r` vanish at no zero

For the linear-cofactor registers `LCValue.regsK p x κ ω Λ ψ wt` (any slots), with the carrier
modulus `Dc = H · M`, `M = 2q³`:

* `Ac_ne`: `Ac = (zc² + 3Dc²)(zc³ − 19Dc³) ≠ 0`, since `Dc ≠ 0` and `19` is not a rational cube
  (`P138NoRoot.no_cube_19`);
* `S_ne`, `s_r_ne`: at a zero of the output, `S = s r H M⁵ ≠ 0`, because at `S = 0` the output
  is `(δ Ac²)²` and `δ ≠ 0` (`LCBootstrap.nonzero`); hence `s ≠ 0` and `r ≠ 0`;
* `B_ne`: at a zero the linear cofactor `B = r A Dm` is nonzero.

No slot law is needed here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.LCNoRoot
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing LCValue P138Ports LCBootstrap
open P138NoRoot (no_cube_19)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section Regs
variable (p : Fin 6 → DiffRing V) (x : Fin 11 → DiffRing V) (κ ω Λ ψ wt : DiffRing V)
local notation "𝓡" => regsK p x κ ω Λ ψ wt

/-- **`Ac ≠ 0`** (`Dc = H · 2q³` is nonzero). -/
theorem Ac_ne (hp : PortFacts p) : (𝓡).Ac ≠ 0 := by
  rw [Ac_eq]
  have hD := Dc_ne p x κ ω Λ ψ wt hp
  refine mul_ne_zero ?_ (sub_ne_zero.mpr (no_cube_19 hD))
  have h1 : 0 < (𝓡).Dc ^ 2 := by positivity
  have := sq_nonneg (𝓡).zc
  exact (show (0 : DiffRing V) < (𝓡).zc ^ 2 + 3 * (𝓡).Dc ^ 2 by linarith).ne'

/-- **At a zero, `S = s r H M⁵ ≠ 0`.** -/
theorem S_ne (hp : PortFacts p) (hz : valueK p x κ ω Λ ψ wt = 0) : (𝓡).S ≠ 0 := by
  intro hS
  rw [value_eq_product, hS, Z_eq, hS] at hz
  have h : ((𝓡).delta * (𝓡).Ac ^ 2) ^ 2 = 0 := by linear_combination hz
  rcases mul_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h) with h | h
  · exact (nonzero p x κ ω Λ ψ wt).2.1 h
  · exact Ac_ne p x κ ω Λ ψ wt hp (pow_eq_zero_iff (by norm_num) |>.mp h)

/-- **At a zero, `s ≠ 0` and `r ≠ 0`.** -/
theorem s_r_ne (hp : PortFacts p) (hz : valueK p x κ ω Λ ψ wt = 0) : x 10 ≠ 0 ∧ x 4 ≠ 0 := by
  have h := S_ne p x κ ω Λ ψ wt hp hz
  rw [S_eq] at h
  exact ⟨fun h0 => h (by rw [h0]; ring), fun h0 => h (by rw [h0]; ring)⟩

/-- **At a zero the linear cofactor `B = r A Dm` is nonzero.** -/
theorem B_ne (hp : PortFacts p) (hz : valueK p x κ ω Λ ψ wt = 0) : (𝓡).B ≠ 0 := by
  rw [B_eq]
  have hDm := Dm_ge p x κ ω Λ ψ wt hp
  exact mul_ne_zero (mul_ne_zero (s_r_ne p x κ ω Λ ψ wt hp hz).2 (A_ne p x κ ω Λ ψ wt hp))
    (show (0:DiffRing V) < (𝓡).Dm by linarith).ne'

end Regs

#print axioms Ac_ne
#print axioms S_ne
#print axioms s_r_ne
#print axioms B_ne

end DiophantineConsistency.LCNoRoot
