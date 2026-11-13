import P84QcubeGraph
import P79DirectPell
import FirstRootBridge

/-! Source-only graph-specific proposal. The three imported modules are draft
sources and require a future independently reviewed overlay/provider plan.
No elaboration, compilation, graph-to-endpoint or file binding is claimed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.DirectFirstRootGraphClientDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticSignedPairs
open DirectFirstRootModelDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The first-root parameters depend on beta and slots 0, 6, 7, 9 and 10,
not on the replaced first-root slot 8. -/
def q (beta : V) (v : Fin 14 → V) : V := 1+v 0*beta
def X (beta : V) (v : Fin 14 → V) : V := q beta v*v 6
def Y (beta : V) (v : Fin 14 → V) : V :=
  (q beta v*(q beta v*q beta v))*v 7
def k (v : Fin 14 → V) : V := v 9+v 10
def ell (beta : V) (v : Fin 14 → V) : V :=
  (X beta v*Y beta v)*(Y beta v*k v)
def scale (beta : V) (v : Fin 14 → V) : V :=
  (q beta v*(q beta v*q beta v))*(v 0*beta)
def firstP (beta : V) (v : Fin 14 → V) : V := ell beta v+k v
def radicand (beta : V) (v : Fin 14 → V) : V :=
  1+ell beta v*firstP beta v

def eval (e : Expr (Fin 14)) (v : Fin 14 → V) : DiffRing V :=
  e.evalRing (fun i => ι (v i))
def putRoot (v : Fin 14 → V) (r : V) : Fin 14 → V := Function.update v 8 r

/-- Both literal graphs have exactly the same other four expressions. -/
theorem common_fields (p : Fin 4 → ℤ) :
    (P84QcubeGraph.graph p).A1=(P79DirectPell.graph p).A1 ∧
    (P84QcubeGraph.graph p).aux=(P79DirectPell.graph p).aux ∧
    (P84QcubeGraph.graph p).gap=(P79DirectPell.graph p).gap ∧
    (P84QcubeGraph.graph p).guardResidual=(P79DirectPell.graph p).guardResidual := by
  exact ⟨rfl,rfl,rfl,rfl⟩

/-- Positive beta and slot zero make the natural first scale positive. -/
theorem scale_positive (beta : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hJ : 0<v 0) : 0<scale beta v := by
  have hb : 0<v 0*beta := mul_pos hJ hbeta
  have hq : 0<q beta v := by dsimp [q]; simp
  exact mul_pos (mul_pos hq (mul_pos hq hq)) hb

/-- The first Pell radicand is positive for every natural valuation. -/
theorem radicand_positive (beta : V) (v : Fin 14 → V) : 0<radicand beta v := by
  dsimp [radicand]
  simp

/-- Positive values at unchanged slots and a positive replacement remain positive. -/
theorem putRoot_positive (v : Fin 14 → V) (r : V)
    (hv : ∀ j, 0<v j) (hr : 0<r) : ∀ j, 0<putRoot v r j := by
  intro j
  by_cases hj : j=8
  · subst j
    simpa [putRoot] using hr
  · simpa [putRoot,hj] using hv j

/-- The old literal first residual evaluates to the scaled difference-ring
first residual. The beta cast is an explicit hypothesis; integer ports in the
other slots remain arbitrary and do not occur in this field. -/
theorem old_first_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V) (r : V)
    (hport : (p 0 : DiffRing V)=ι beta) :
    eval (P84QcubeGraph.graph p).A0 (putRoot v r) =
      (ι (scale beta v)*ι (scale beta v))*
        ((ι (firstP beta v)-ι r)*(ι (firstP beta v)-ι r)-ι (radicand beta v)) := by
  simp [eval, P84QcubeGraph.graph, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat,
    putRoot, Function.update, scale, firstP, radicand, ell, X, Y, q, k,
    hport, map_add, map_mul, map_one] <;> ring

/-- The direct graph's first residual evaluates to root² minus the same
natural radicand. -/
theorem direct_first_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V) (r : V)
    (hport : (p 0 : DiffRing V)=ι beta) :
    eval (P79DirectPell.graph p).A0 (putRoot v r) = ι r*ι r-ι (radicand beta v) := by
  simp [eval, P79DirectPell.graph, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat,
    putRoot, Function.update, radicand, firstP, ell, X, Y, q, k,
    hport, map_add, map_mul, map_one] <;> ring

/-- The other four old-graph evaluations ignore the changed slot. -/
theorem other_fields_ignore_root (p : Fin 4 → ℤ) (v : Fin 14 → V) (r : V) :
    eval (P84QcubeGraph.graph p).A1 (putRoot v r)=eval (P84QcubeGraph.graph p).A1 v ∧
    eval (P84QcubeGraph.graph p).aux (putRoot v r)=eval (P84QcubeGraph.graph p).aux v ∧
    eval (P84QcubeGraph.graph p).gap (putRoot v r)=eval (P84QcubeGraph.graph p).gap v ∧
    eval (P84QcubeGraph.graph p).guardResidual (putRoot v r)=
      eval (P84QcubeGraph.graph p).guardResidual v := by
  simp [eval, P84QcubeGraph.graph, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat,
    putRoot, Function.update]

/-- Fixed-other-coordinate existence equivalence, with the natural beta cast
explicit. This proposed theorem does not itself state the global iPRA endpoint. -/
theorem positive_first_coordinate_iff (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hJ : 0<v 0) (hport : (p 0 : DiffRing V)=ι beta) :
    (∃ r : V, 0<r ∧ InternalZero (P84QcubeGraph.graph p).output (putRoot v r)) ↔
    (∃ t : V, 0<t ∧ InternalZero (P79DirectPell.graph p).output (putRoot v t)) := by
  let b := eval (P84QcubeGraph.graph p).A1 v
  let c := eval (P84QcubeGraph.graph p).aux v-1
  let d := eval (P84QcubeGraph.graph p).gap v
  let e := eval (P84QcubeGraph.graph p).guardResidual v
  have hM := scale_positive beta v hbeta hJ
  have hD := radicand_positive beta v
  have hold (r : V) :
      InternalZero (P84QcubeGraph.graph p).output (putRoot v r) ↔
      fiveSquares ((ι (scale beta v)*ι (scale beta v))*
        ((ι (firstP beta v)-ι r)*(ι (firstP beta v)-ι r)-ι (radicand beta v))) b c d e=0 := by
    rw [internalZero_iff,P84QcubeGraph.output_shape]
    simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
      Expr.evalRing_ofNat, Expr.evalRing_constant, Int.cast_one, Nat.cast_one]
    change fiveSquares (eval (P84QcubeGraph.graph p).A0 (putRoot v r))
      (eval (P84QcubeGraph.graph p).A1 (putRoot v r))
      (eval (P84QcubeGraph.graph p).aux (putRoot v r)-1)
      (eval (P84QcubeGraph.graph p).gap (putRoot v r))
      (eval (P84QcubeGraph.graph p).guardResidual (putRoot v r))=0 ↔ _
    rcases other_fields_ignore_root p v r with ⟨h1,h2,h3,h4⟩
    rw [old_first_eval p beta v r hport,h1,h2,h3,h4]
    rfl
  have hnew (t : V) :
      InternalZero (P79DirectPell.graph p).output (putRoot v t) ↔
      fiveSquares (ι t*ι t-ι (radicand beta v)) b c d e=0 := by
    rw [internalZero_iff,P79DirectPell.output_shape]
    simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
      Expr.evalRing_ofNat, Expr.evalRing_constant, Int.cast_one, Nat.cast_one]
    rcases common_fields p with ⟨h1,h2,h3,h4⟩
    rw [← h1,← h2,← h3,← h4]
    change fiveSquares (eval (P79DirectPell.graph p).A0 (putRoot v t))
      (eval (P84QcubeGraph.graph p).A1 (putRoot v t))
      (eval (P84QcubeGraph.graph p).aux (putRoot v t)-1)
      (eval (P84QcubeGraph.graph p).gap (putRoot v t))
      (eval (P84QcubeGraph.graph p).guardResidual (putRoot v t))=0 ↔ _
    rcases other_fields_ignore_root p v t with ⟨g1,g2,g3,g4⟩
    rw [direct_first_eval p beta v t hport,g1,g2,g3,g4]
    rfl
  simpa only [hold,hnew] using
    (positive_first_zero_iff (scale beta v) (firstP beta v) (radicand beta v)
      b c d e hM hD)

end DiophantineConsistency.DirectFirstRootGraphClientDraft

#print axioms DiophantineConsistency.DirectFirstRootGraphClientDraft.positive_first_coordinate_iff
