import DiophantineConsistency.ArithmeticAdaptiveConstructionFirstSeed2011
import DiophantineConsistency.ArithmeticAdaptiveConstructionTransportActual2011

/-! The actual equation vector and seed jointly provide the first carrier. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionFirstActual2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCarrierSoundness2011 ArithmeticCarrierRadix2011 ArithmeticOuterSeed
  ArithmeticAdaptiveConstructionTransportActual2011 ArithmeticAdaptiveConstructionFirstSeed2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The actual old vector, outer seed, rank phase, and exact radix/multiplier
facts produce a positive first carrier; no independent quotient positivity
or size hypothesis is required. -/
theorem positive_first_of_actual (v : Fin 14 → V) (u : V)
    (hv : ∀ j, 0<v j)
    (he : Equations (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V)
      (CurrentMasks2011.lowPort:V) ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V) v)
    (hphase : rank v%4=3)
    (hq : ArithmeticCarrierRadix2011.q v=Exp.exp u)
    (hX : Exp.exp (rank v)=ArithmeticCarrierRadix2011.q v*v 8)
    (hR : 2*u≤rank v)
    (hseed : SeedRelations u (rank v) (v 7) (v 9) (v 10) (v 11) (v 13)) :
    let q := Exp.exp u
    let X := Exp.exp (rank v)
    let Y := v 7*q^3
    let Q := X*Y*Y
    let k := v 10+v 11
    let ell := Q*k
    let tau := X*Y*v 9+k-rank v
    let b := ArithmeticCarrierRadix2011.q v*(v 3-1)
    ∃ r : V, 0<r ∧ ell+k+r+v 7=(1+(q-1)*k)*b+tau ∧
      (q^3*(q-1))*(ell+k+r)+(q^3*v 7)*(q-1) =
        (q^3*(q-1))*tau+(1+(q-1)*k)*q^3*((q-1)*b) := by
  have hb := actual_transport_quotient_positive v u hv he hq hX hR
  have hq2 : (2:V)≤Exp.exp u-1 := by
    rw [← hq]
    change (2:V)≤((CurrentMasks2011.beta:V)*v 0+1)-1
    simp only [add_tsub_cancel_right]
    have hβ := (current_bounds (V:=V)).1
    have hβv : (CurrentMasks2011.beta:V)≤(CurrentMasks2011.beta:V)*v 0 :=
      le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp (hv 0))
    exact le_trans (by norm_num : (2:V)≤15) (le_trans hβ hβv)
  exact positive_first_of_seed u (rank v) (v 7) (v 9) (v 10) (v 11) (v 13)
    (ArithmeticCarrierRadix2011.q v*(v 3-1)) (hv 7) hphase hq2 hb hseed
end DiophantineConsistency.ArithmeticAdaptiveConstructionFirstActual2011
