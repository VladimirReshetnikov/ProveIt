import P79DirectPell
import P78AuxRoot
import FirstRootBridge
import RingNormExtraction

/-! Source-only graph-norm client proposal. All three bare imports are draft
sources requiring a future reviewed overlay. No Lean elaboration has occurred. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.AuxGraphNormClientDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing DirectFirstRootModelDraft
open AuxRingNormExtractionDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def q (beta : V) (v : Fin 14 → V) : V := 1+v 0*beta
def X (beta : V) (v : Fin 14 → V) : V := q beta v*v 6
def Y (beta : V) (v : Fin 14 → V) : V := (q beta v*(q beta v*q beta v))*v 7
def U (beta : V) (v : Fin 14 → V) : V := Y beta v*(q beta v*q beta v)
def k (v : Fin 14 → V) : V := v 9+v 10
def a (beta : V) (v : Fin 14 → V) : V := X beta v*Y beta v+Y beta v
def c (beta : V) (v : Fin 14 → V) : V := v 9+Y beta v*k v
def Delta (beta : V) (v : Fin 14 → V) : V :=
  3+4*a beta v+a beta v*a beta v
def eval (e : Expr (Fin 14)) (v : Fin 14 → V) : DiffRing V := e.evalRing (fun j => ι (v j))

/-- Rank remains a difference-ring value; no natural-gap sign is assumed. -/
def rank (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V) : DiffRing V :=
  let qr := ι (q beta v)
  let br := ι (v 0*beta)
  (ι (v 2)+(qr-ι (v 1))*br)*(qr*qr-1)+ι (v 0)*((p 2 : DiffRing V)+(p 3 : DiffRing V)*qr)

def mainValue (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V) : DiffRing V :=
  let qr := ι (q beta v)
  let ar := ι (a beta v)
  let cr := ι (c beta v)
  let ur := ι (U beta v)
  let hr := 3+4*ar
  ur*(ι (X beta v)+ar*cr)+hr*(ur*ι (v 12)-(ι (k v)-rank p beta v-1))

def coeff (beta : V) (v : Fin 14 → V) : DiffRing V :=
  ι (Delta beta v)*(ι (v 3)*ι (v 3)-1)
def zvalue (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V) : DiffRing V :=
  (ι (v 3)*ι (v 3))*(ι (v 5)*ι (c beta v)-rank p beta v)-ι (c beta v)

/-- Proposed literal first field evaluation with beta's model cast explicit. -/
theorem first_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hport : (p 0 : DiffRing V)=ι beta) :
    eval (P79DirectPell.graph p).A0 v = ι (v 8)*ι (v 8)-
      ι (1+((X beta v*Y beta v)*(Y beta v*k v))*
        (((X beta v*Y beta v)*(Y beta v*k v))+k v)) := by
  simp [eval,P79DirectPell.graph,Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,q,X,Y,k,hport,
    map_add,map_mul,map_one] <;> ring

/-- Proposed literal main-field evaluation, keeping its signed value intact. -/
theorem main_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hport : (p 0 : DiffRing V)=ι beta) :
    eval (P79DirectPell.graph p).A1 v = mainValue p beta v*mainValue p beta v-
      (ι (U beta v)*ι (U beta v))*ι (1+Delta beta v*c beta v*c beta v) := by
  simp [eval,P79DirectPell.graph,Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,mainValue,rank,
    q,X,Y,U,k,a,c,Delta,hport,map_add,map_mul,map_one] <;> ring

/-- Proposed literal strong-field evaluation. -/
theorem strong_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hport : (p 0 : DiffRing V)=ι beta) :
    eval (P79DirectPell.graph p).gap v =
      (ι (v 4)*ι (c beta v)*ι (c beta v))*(ι (v 4)*ι (c beta v)*ι (c beta v))-
        ι (Delta beta v)*(ι (v 3)*ι (v 3)-1) := by
  simp [eval,P79DirectPell.graph,Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,q,X,Y,k,a,c,Delta,
    hport,map_add,map_mul,map_one] <;> ring

/-- Proposed extraction of the three zero fields from the literal sum of
five squares. It uses the separately drafted model square lemma. -/
theorem fields_of_zero (p : Fin 4 → ℤ) (v : Fin 14 → V)
    (hz : InternalZero (P79DirectPell.graph p).output v) :
    eval (P79DirectPell.graph p).A0 v=0 ∧
    eval (P79DirectPell.graph p).A1 v=0 ∧
    eval (P79DirectPell.graph p).gap v=0 := by
  rw [internalZero_iff,P79DirectPell.output_shape] at hz
  simp only [Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_ofNat,Expr.evalRing_constant,Int.cast_one,Nat.cast_one] at hz
  have hfive : fiveSquares (eval (P79DirectPell.graph p).A0 v)
      (eval (P79DirectPell.graph p).A1 v) (eval (P79DirectPell.graph p).aux v-1)
      (eval (P79DirectPell.graph p).gap v) (eval (P79DirectPell.graph p).guardResidual v)=0 := by
    simpa only [fiveSquares,eval] using hz
  rcases (fiveSquares_eq_zero_iff _ _ _ _ _).mp hfive with ⟨h0,h1,_,hs,_⟩
  exact ⟨h0,h1,hs⟩

/-- The first, main and strong expressions are literally shared by the two
source graphs; slot 11 affects only the auxiliary field. -/
theorem common_norm_fields (p : Fin 4 → ℤ) :
    (P78AuxRoot.graph p).A0=(P79DirectPell.graph p).A0 ∧
    (P78AuxRoot.graph p).A1=(P79DirectPell.graph p).A1 ∧
    (P78AuxRoot.graph p).gap=(P79DirectPell.graph p).gap := by
  exact ⟨rfl,rfl,rfl⟩

/-- Proposed zero-field extraction for the actual 78 graph, stated using the
shared 79 expressions. The auxiliary field itself is not identified. -/
theorem fields_of_78_zero (p : Fin 4 → ℤ) (v : Fin 14 → V)
    (hz : InternalZero (P78AuxRoot.graph p).output v) :
    eval (P79DirectPell.graph p).A0 v=0 ∧
    eval (P79DirectPell.graph p).A1 v=0 ∧
    eval (P79DirectPell.graph p).gap v=0 := by
  rw [internalZero_iff,P78AuxRoot.output_shape] at hz
  simp only [Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_ofNat,Expr.evalRing_constant,Int.cast_one,Nat.cast_one] at hz
  have hfive : fiveSquares (eval (P78AuxRoot.graph p).A0 v)
      (eval (P78AuxRoot.graph p).A1 v) (eval (P78AuxRoot.graph p).aux v-1)
      (eval (P78AuxRoot.graph p).gap v) (eval (P78AuxRoot.graph p).guardResidual v)=0 := by
    simpa only [fiveSquares,eval] using hz
  rcases (fiveSquares_eq_zero_iff _ _ _ _ _).mp hfive with ⟨h0,h1,_,hs,_⟩
  rcases common_norm_fields p with ⟨g0,g1,gs⟩
  rw [g0] at h0
  rw [g1] at h1
  rw [gs] at hs
  exact ⟨h0,h1,hs⟩

/-- Proposed strict bounds from the three shared field zeros. -/
theorem bounds_of_fields (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta)
    (hv : ∀ j, 0<v j) (h0 : eval (P79DirectPell.graph p).A0 v=0)
    (h1 : eval (P79DirectPell.graph p).A1 v=0)
    (hs : eval (P79DirectPell.graph p).gap v=0) :
    1<coeff beta v ∧ 1<zvalue p beta v*zvalue p beta v := by
  rw [first_eval p beta v hport] at h0
  rw [main_eval p beta v hport] at h1
  rw [strong_eval p beta v hport] at hs
  have hq : 0<q beta v := by dsimp [q]; simp
  have hX : 0<X beta v := mul_pos hq (hv 6)
  have hY : 0<Y beta v := mul_pos (mul_pos hq (mul_pos hq hq)) (hv 7)
  have hU : 0<U beta v := mul_pos hY (mul_pos hq hq)
  have hcdef : c beta v=v 9+Y beta v*(v 9+v 10) := rfl
  have hDdef : Delta beta v=3+4*(X beta v*Y beta v+Y beta v)+
      (X beta v*Y beta v+Y beta v)*(X beta v*Y beta v+Y beta v) := rfl
  have hQ : coeff beta v=(ι (v 4)*ι (c beta v)*ι (c beta v))*
      (ι (v 4)*ι (c beta v)*ι (c beta v)) := by
    dsimp only [coeff]
    exact (sub_eq_zero.mp hs).symm
  have hZ : zvalue p beta v+ι (c beta v)=
      (ι (v 3)*ι (v 3))*(ι (v 5)*ι (c beta v)-rank p beta v) := by
    dsimp only [zvalue]
    ring
  exact bounds_of_direct_field_residuals (X beta v) (Y beta v) (v 9) (v 10) (v 8)
    (Delta beta v) (c beta v) (v 4) (v 3) (U beta v) (mainValue p beta v)
    (zvalue p beta v) (coeff beta v) (ι (v 5)*ι (c beta v)-rank p beta v)
    hX hY (hv 9) (hv 10) (hv 4) hU hcdef hDdef h0 h1 hs hQ hZ

/-- Proposed 79-graph strict bounds; no auxiliary-coordinate map is claimed. -/
theorem bounds_of_79_positive_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta)
    (hv : ∀ j, 0<v j) (hz : InternalZero (P79DirectPell.graph p).output v) :
    1<coeff beta v ∧ 1<zvalue p beta v*zvalue p beta v := by
  obtain ⟨h0,h1,hs⟩ := fields_of_zero p v hz
  exact bounds_of_fields p beta v hbeta hport hv h0 h1 hs

/-- Proposed 78-graph strict bounds from that graph's own positive zero. -/
theorem bounds_of_78_positive_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta)
    (hv : ∀ j, 0<v j) (hz : InternalZero (P78AuxRoot.graph p).output v) :
    1<coeff beta v ∧ 1<zvalue p beta v*zvalue p beta v := by
  obtain ⟨h0,h1,hs⟩ := fields_of_78_zero p v hz
  exact bounds_of_fields p beta v hbeta hport hv h0 h1 hs

end DiophantineConsistency.AuxGraphNormClientDraft

#print axioms DiophantineConsistency.AuxGraphNormClientDraft.bounds_of_79_positive_zero
#print axioms DiophantineConsistency.AuxGraphNormClientDraft.bounds_of_78_positive_zero
