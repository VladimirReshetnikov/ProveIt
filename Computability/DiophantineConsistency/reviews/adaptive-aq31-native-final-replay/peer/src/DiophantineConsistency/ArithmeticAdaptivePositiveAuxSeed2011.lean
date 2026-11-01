import DiophantineConsistency.ArithmeticConstructionAssembly
import DiophantineConsistency.ArithmeticAdaptiveConstructionAuxClient2011
import DiophantineConsistency.ArithmeticAdaptiveConstructionAuxPhase2011
/-! Strict orientation of the auxiliary seed under the explicit carrier and orientation hypotheses. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptivePositiveAuxSeed2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem norm_positive (I z y : V) (hI : 1 ≤ I)
    (hn : I*I*z*z+y*y=1+I*I*y*y) : 0<z := by
  apply pos_iff_ne_zero.mpr
  intro hz
  have hle : y*y ≤ (I*I)*(y*y) :=
    le_mul_of_one_le_left (by simp) (one_le_mul hI hI)
  have hbad : y*y+1 ≤ y*y := calc
    y*y+1 ≤ 1+(I*I)*(y*y) := by simpa only [add_comm] using add_le_add_left hle (1:V)
    _ = y*y := by simpa only [hz, mul_zero, zero_mul, zero_add, mul_assoc] using hn.symm
  exact (not_le_of_gt (lt_add_one (y*y))) hbad
open DiophantineConsistency
open ArithmeticCarrierSoundness2011 ArithmeticCarrierRadix2011

theorem exact_orientation_strict (v : Fin 14 → V)
    (hv : ∀ j, 0<v j)
    (he : Equations (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V)
      (CurrentMasks2011.lowPort:V) ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V) v)
    (horient : let q := ArithmeticCarrierRadix2011.q v
      let Y := v 7*q^3
      let c := (v 10+v 11)*Y+v 10
      let L := v 4*v 4*c*v 6
      let M := v 4*v 4*rank v+c
      L=(L-M)+(M-L)+c+v 4*v 4*rank v) :
    let q := ArithmeticCarrierRadix2011.q v
    let Y := v 7*q^3
    let c := (v 10+v 11)*Y+v 10
    v 4*v 4*rank v+c < v 4*v 4*c*v 6 := by
  let q := ArithmeticCarrierRadix2011.q v
  let Y := v 7*q^3
  let c := (v 10+v 11)*Y+v 10
  let X := v 8*q
  let a := X*Y+Y
  let delta := (a+1)*(a+3)
  let I := delta*v 5*c*c
  let L := v 4*v 4*c*v 6
  let M := v 4*v 4*rank v+c
  let z := (L-M)+(M-L)
  have hq : 0<q := by
    change 0<(CurrentMasks2011.beta:V)*v 0+1
    exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  have hY : 0<Y := mul_pos (hv 7) (pow_pos hq _)
  have hc : 0<c := add_pos (mul_pos (add_pos (hv 10) (hv 11)) hY) (hv 10)
  have hd : 0<delta := mul_pos (by dsimp [a]; simp) (by dsimp [a]; simp)
  have hI : 1≤I := one_le_mul (one_le_mul (one_le_mul (pos_iff_one_le.mp hd)
    (pos_iff_one_le.mp (hv 5))) (pos_iff_one_le.mp hc)) (pos_iff_one_le.mp hc)
  have hn : I*I*z*z+v 12*v 12=1+I*I*v 12*v 12 := by
    have hh := he.2.2.2.2
    change I*I*z*z+v 12*v 12=1+I*I*v 12*v 12 at hh
    exact hh
  have hz : 0<z := norm_positive I z (v 12) hI hn
  have hL : L=z+M := by
    change L=z+c+v 4*v 4*rank v at horient
    rw [horient]
    dsimp [M]
    ring
  have hle : M≤L := by rw [hL]; simp
  change M<L
  by_contra hnot
  have hLM : L=M := le_antisymm (le_of_not_gt hnot) hle
  have hz0 : z=0 := by simp [z,hLM]
  exact (ne_of_gt hz) hz0

end DiophantineConsistency.ArithmeticAdaptivePositiveAuxSeed2011
