import DiophantineConsistency.Compact44.FreeJCurrentDenominator
import DiophantineConsistency.Compact44.ReducedNormSigned
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FreeJGraphIntegrality
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.ArithmeticSignedPairs
open DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011
open DiophantineConsistency.ModelDifferenceRing
open DiophantineConsistency.Ordinary12FreeJ
open FreeJGraphVBound FreeJDenominator FreeJOrdinaryTransport FreeJCurrentDenominator
open ReducedNormSigned
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graphQ_eval (v : Fin 12 → V) :
    let a := v 5*v 6+v 6
    let delta := (3+4*a)+a*a
    let f := 1+v 3
    let Q := delta*(f*f-1)
    graphQ.evalRing (fun i => ι (v i))=ι Q := by
  let a := v 5*v 6+v 6
  let delta := (3+4*a)+a*a
  let f := 1+v 3
  let Q := delta*(f*f-1)
  have hq := Q_eval v
  change Equivalent (pairEval graphQ v) (natural Q) at hq
  have heq : (pairEval graphQ v).1=(pairEval graphQ v).2+Q := by
    simpa [Equivalent,natural] using hq
  have heval := split_evalRing graphQ (fun i => ι (v i))
  rw [←evalSemiring_map,←evalSemiring_map] at heval
  change ι ((pairEval graphQ v).1)-ι ((pairEval graphQ v).2)=_ at heval
  calc
    graphQ.evalRing (fun i => ι (v i)) =
        ι ((pairEval graphQ v).1)-ι ((pairEval graphQ v).2) := heval.symm
    _=ι Q := by rw [heq,map_add]; ring

theorem graph_denominator_divides (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀ j,0<v j) (hz : InternalZero (literal (fun j => (p j:ℤ))) v) :
    let ev := fun e : Expr (Fin 12) => e.evalRing (fun i => ι (v i))
    let q := ev (parts (fun j => (p j:ℤ))).q
    let d := ev (parts (fun j => (p j:ℤ))).d
    let z := ev (parts (fun j => (p j:ℤ))).z
    let n := ev (parts (fun j => (p j:ℤ))).n
    let w := n+z
    let h := (1-q)*w*w+q*z*z-1
    let b := 2*(1-q)*w
    let A := d*h+q*(1-q)
    let D := d*b
    let Y := w*D-A
    D∣Y := by
  let ports : Fin 4 → ℤ := fun j => (p j:ℤ)
  let ev := fun e : Expr (Fin 12) => e.evalRing (fun i => ι (v i))
  let q := ev (parts ports).q
  let d := ev (parts ports).d
  let z := ev (parts ports).z
  let n := ev (parts ports).n
  let w := n+z
  let h := (1-q)*w*w+q*z*z-1
  let b := 2*(1-q)*w
  let A := d*h+q*(1-q)
  let D := d*b
  let Y := w*D-A
  let a := v 5*v 6+v 6
  let delta := (3+4*a)+a*a
  let f := 1+v 3
  let Q := delta*(f*f-1)
  let r : V := Q-1
  have hQ : 1<Q := Q_gt_one v (hv 3)
  have hr : 0<r := tsub_pos_iff_lt.mpr hQ
  have hQr : r+1=Q := tsub_add_cancel_of_le (le_of_lt hQ)
  have hshape : (parts ports).q=graphQ := by rfl
  have hqe : q=ι r+1 := by
    dsimp only [q,ev]
    rw [hshape,graphQ_eval]
    change ι Q=ι r+1
    rw [←hQr,map_add,map_one]
  have hgraph := auxiliary_with_nonzero_denominator p v hb hl hh hv hz
  change D≠0 ∧ q*z*z*D*D-(q-1)*Y*Y-D*D=0 at hgraph
  have heq1 : q*z*z*D*D-(q-1)*Y*Y=D*D := sub_eq_zero.mp hgraph.2
  have heq2 : q*z*z*D*D=(q-1)*Y*Y+D*D := by
    linarith [heq1]
  have heq3 : (ι r+1)*z*z*D*D=ι r*Y*Y+D*D := by
    rw [hqe] at heq2
    simpa only [add_sub_cancel_right] using heq2
  exact signed_denominator_divides r z Y D hr hgraph.1 heq3
end FreeJGraphIntegrality
#print axioms FreeJGraphIntegrality.graphQ_eval
#print axioms FreeJGraphIntegrality.graph_denominator_divides
