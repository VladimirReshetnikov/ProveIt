import GuardRank85
import FirstRootBridge
import RingNormExtraction

/-! Source-only 85 field and natural norm replay. No 84/FreeJ zero, q|X,
Pell index or endpoint is assumed; bare imports remain unelaborated. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.DirectNorms85Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticSignedPairs
open DirectFirstRootModelDraft AuxRingNormExtractionDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def q (beta : V) (v : Fin 14 → V) : V := 1+v 0*beta
def X (v : Fin 14 → V) : V := v 6
def Y (beta : V) (v : Fin 14 → V) : V := q beta v*(q beta v*q beta v)*v 7
def U (beta : V) (v : Fin 14 → V) : V := Y beta v*(q beta v*q beta v)
def k (v : Fin 14 → V) : V := v 9+v 10
def a (beta : V) (v : Fin 14 → V) : V := X v*Y beta v+Y beta v
def c (beta : V) (v : Fin 14 → V) : V := v 9+Y beta v*k v
def Delta (beta : V) (v : Fin 14 → V) : V := 3+4*a beta v+a beta v*a beta v
def ell (beta : V) (v : Fin 14 → V) : V := (X v*Y beta v)*(Y beta v*k v)
def firstP (beta : V) (v : Fin 14 → V) : V := ell beta v+k v
def radicand (beta : V) (v : Fin 14 → V) : V := 1+ell beta v*firstP beta v
def scale (beta : V) (v : Fin 14 → V) : V := q beta v*(q beta v*q beta v)*(v 0*beta)
def eval (e : Expr (Fin 14)) (v : Fin 14 → V) : DiffRing V := e.evalRing (fun j => ι (v j))

/-- Exact signed first-field expression for the direct-X 85 graph. -/
theorem first_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hport : (p 0 : DiffRing V)=ι beta) :
    eval (P85QcubeGraph.graph p).A0 v=(ι (scale beta v)*ι (scale beta v))*
      ((ι (firstP beta v)-ι (v 8))*(ι (firstP beta v)-ι (v 8))-ι (radicand beta v)) := by
  simp [eval,P85QcubeGraph.graph,Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,q,X,Y,k,ell,firstP,
    radicand,scale,hport,map_add,map_mul,map_one] <;> ring

/-- Exact signed strong-field expression for the direct-X 85 graph. -/
theorem strong_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hport : (p 0 : DiffRing V)=ι beta) :
    eval (P85QcubeGraph.graph p).gap v=
      (ι (v 4)*ι (c beta v)*ι (c beta v))*(ι (v 4)*ι (c beta v)*ι (c beta v))-
        ι (Delta beta v)*(ι (v 3)*ι (v 3)-1) := by
  simp [eval,P85QcubeGraph.graph,Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,q,X,Y,k,a,c,Delta,
    hport,map_add,map_mul,map_one] <;> ring

/-- First natural magnitude norm directly from the 85 own-zero. -/
theorem first_norm (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hJ : 0<v 0) (hport : (p 0 : DiffRing V)=ι beta)
    (hz : InternalZero (P85QcubeGraph.graph p).output v) :
    0<magnitude (firstP beta v,v 8) ∧
      magnitude (firstP beta v,v 8)*magnitude (firstP beta v,v 8)=radicand beta v := by
  have hq : 0<q beta v := by dsimp [q]; simp
  have hM : 0<scale beta v := by
    dsimp [scale]
    exact mul_pos (mul_pos hq (mul_pos hq hq)) (mul_pos hJ hbeta)
  have hD : 0<radicand beta v := by dsimp [radicand]; simp
  have hf := (ZeroFields8485Draft.fields85 p v hz).1
  change eval (P85QcubeGraph.graph p).A0 v=0 at hf
  rw [first_eval p beta v hport] at hf
  exact root_of_scaled_residual (scale beta v) (firstP beta v) (v 8) (radicand beta v) hM hD hf

/-- Natural strong norm directly from the 85 own-zero. -/
theorem strong_norm (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hport : (p 0 : DiffRing V)=ι beta)
    (hz : InternalZero (P85QcubeGraph.graph p).output v) :
    (v 4*c beta v*c beta v)*(v 4*c beta v*c beta v)+Delta beta v=
      Delta beta v*(v 3*v 3) := by
  have hg := (ZeroFields8485Draft.fields85 p v hz).2.2.2.1
  change eval (P85QcubeGraph.graph p).gap v=0 at hg
  rw [strong_eval p beta v hport] at hg
  exact strong_norm_of_ring_residual _ _ _ _ hg

end DiophantineConsistency.DirectNorms85Draft

#print axioms DiophantineConsistency.DirectNorms85Draft.first_norm
#print axioms DiophantineConsistency.DirectNorms85Draft.strong_norm
