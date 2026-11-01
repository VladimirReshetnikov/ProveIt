import DiophantineConsistency.AdaptiveGap85ShiftModel
import DiophantineConsistency.AdaptiveGap85ThresholdFullSeed

/-! Apply the actual seed equations to the all-model pointwise shift. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85ShiftSeedClient
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence AdaptiveEquationSyntax2011 AdaptiveGap85Literal
open AdaptiveGap85ShiftModel AdaptiveGap85ThresholdFullSeed
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A positive literal zero satisfying the actual seed equations has a shifted
    positive zero that violates the pointwise gap. Existence is not asserted. -/
theorem shifted_seed_zero_breaks_gap (p : Fin 4 → ℕ) (v : Fin 13 → V) (a R s u : V)
    (hb : 0<(p 0:V)) (hv : ∀ i,0<v i) (hs : 0<s) (hR : 5≤R)
    (hY : let b := v 0*(p 0:V); let q := 1+b; v 7=s*q^3)
    (hc : v 9+v 7*(v 9+v 10)=ycoord R a)
    (hn : let c := v 9+v 7*(v 9+v 10);
      v 3*v 3=1+delta a*(v 4*c*c)*(v 4*c*c))
    (hux : let c := v 9+v 7*(v 9+v 10); let I := delta a*v 4*c*c;
      xcoord R (I-2)=I*u)
    (he : let c := v 9+v 7*(v 9+v 10);
      v 3*v 3*c*v 5=u+c+v 3*v 3*R)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v) :
    (∀ i,0<shift p v i) ∧ InternalZero (expressionAt85 (fun j => (p j:ℤ))) (shift p v) ∧
      ¬(shift p v 1+shift p v 2<1+shift p v 0*(p 0:V)) := by
  let b : V := v 0*(p 0:V)
  have hY' : v 7=s*(1+b)^3 := hY
  have ht := full_seed_exceeds_shift a R b s (v 9) (v 10) (v 3) (v 4) (v 5) u
    hR hs (hv 9) (hv 10) (hv 4) (hv 3)
    (by simpa only [←hY'] using hc)
    (by simpa only [←hY'] using hn)
    (by simpa only [←hY'] using hux)
    (by simpa only [←hY'] using he)
  apply shifted_zero_breaks_gap p v hb hv
  · simpa only [←hY',b] using ht
  · exact hz
end DiophantineConsistency.AdaptiveGap85ShiftSeedClient
