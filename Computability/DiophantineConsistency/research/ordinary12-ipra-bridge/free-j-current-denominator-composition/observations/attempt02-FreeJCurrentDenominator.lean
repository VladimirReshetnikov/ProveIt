import DiophantineConsistency.FreeJDenominator
import DiophantineConsistency.FreeJSignedTransport
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FreeJCurrentDenominator
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.ArithmeticSignedPairs
open DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011
open DiophantineConsistency.ModelDifferenceRing
open DiophantineConsistency.Ordinary12FreeJ
open FreeJGraphVBound FreeJDenominator FreeJOrdinaryTransport FreeJNormZero
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem denominator_shape (p : Fin 4 → ℤ) :
    graphD p = (parts p).d * ((2*(1-(parts p).q))*((parts p).n+(parts p).z)) := by rfl

theorem denominator_eval (p : Fin 4 → ℤ) (v : Fin 12 → V) :
    (graphD p).evalRing (fun i => ι (v i)) =
      let ev := fun e : Expr (Fin 12) => e.evalRing (fun i => ι (v i))
      ev (parts p).d * (2*(1-ev (parts p).q)*(ev (parts p).n+ev (parts p).z)) := by
  rw [denominator_shape]
  simp only [Expr.evalRing_mul, Expr.evalRing_sub, Expr.evalRing_add, Expr.evalRing_ofNat]

theorem auxiliary_with_nonzero_denominator (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀ j,0<v j) (hz : InternalZero (literal (fun j => (p j:ℤ))) v) :
    let ev := fun e : Expr (Fin 12) => e.evalRing (fun i => ι (v i))
    let q := ev (parts (fun j => (p j:ℤ))).q
    let d := ev (parts (fun j => (p j:ℤ))).d
    let z := ev (parts (fun j => (p j:ℤ))).z
    let n := ev (parts (fun j => (p j:ℤ))).n
    let w := n+z
    let r := 1-q
    let h := r*w*w+q*z*z-1
    let b := 2*r*w
    let A := d*h+q*r
    let D := d*b
    let Y := w*D-A
    D ≠ 0 ∧ q*z*z*D*D-(q-1)*Y*Y-D*D=0 := by
  let ports : Fin 4 → ℤ := fun j => (p j:ℤ)
  have hs := denominator_negative p v hb hl hh hv hz
  have hD : (graphD ports).evalRing (fun i => ι (v i)) ≠ 0 := by
    intro he
    have hzero := (internalZero_iff (graphD ports) v).mpr he
    change (pairEval (graphD ports) v).1 = (pairEval (graphD ports) v).2 at hzero
    exact (ne_of_lt hs) hzero
  have hq := actual_unpolarized_zero ports v hz
  have hid := cleared_auxiliary_identity
    ((parts ports).q.evalRing (fun i => ι (v i)))
    ((parts ports).d.evalRing (fun i => ι (v i)))
    ((parts ports).z.evalRing (fun i => ι (v i)))
    ((parts ports).n.evalRing (fun i => ι (v i)))
  dsimp only at hq hid ⊢
  constructor
  · simpa only [ports, denominator_eval] using hD
  · rw [hq, mul_zero, neg_zero] at hid
    exact hid
end FreeJCurrentDenominator
#print axioms FreeJCurrentDenominator.denominator_shape
#print axioms FreeJCurrentDenominator.denominator_eval
#print axioms FreeJCurrentDenominator.auxiliary_with_nonzero_denominator
