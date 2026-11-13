import IndependentYGraphDraft

/-! Unchecked draft: bind the generic size bound to an actual 76Y zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace IndependentYSizeDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open P64QCubeMap
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem strong_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    let q := (p 0:R)*v 0+1
    let Y := (q*q*q)*v 7
    let X := v 8*q
    let a := X*Y+Y
    let c := (v 10+v 11)*Y+v 10
    (P64QCube76Y.graph p).W.evalRing v =
      (v 5*(c*c))*(v 5*(c*c))-(a*a+(4*a+3))*(v 4*v 4-1) := by
  simp [P64QCube76Y.graph,Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat]

theorem actual_f_bound (p : Fin 4 → ℕ) (v : Fin 14 → V) (hv : ∀i,0<v i)
    (hz : InternalZero (P64QCube76Y.graph (fun j => (p j:ℤ))).output v) :
    let q : V := (p 0:V)*v 0+1
    let Y := (q*q*q)*v 7
    let c := (v 10+v 11)*Y+v 10
    (ι c:DiffRing V)+1 < (ι (v 4):DiffRing V)*ι (v 4) := by
  let pp : Fin 4 → ℤ := fun j => (p j:ℤ)
  let z : Fin 14 → DiffRing V := fun i => ι (v i)
  let q : V := (p 0:V)*v 0+1
  let Y : V := (q*q*q)*v 7
  let X : V := v 8*q
  let a : V := X*Y+Y
  let c : V := (v 10+v 11)*Y+v 10
  have hq : 0<q := by dsimp [q]; simp
  have hY : 0<Y := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 7)
  have hk2 : (2:V)≤v 10+v 11 := by
    simpa [one_add_one_eq_two] using add_le_add (pos_iff_one_le.mp (hv 10)) (pos_iff_one_le.mp (hv 11))
  have hc3 : (3:V)≤c := by
    calc
      (3:V)=2*1+1 := by norm_num
      _≤(v 10+v 11)*Y+v 10 := add_le_add (mul_le_mul hk2 (pos_iff_one_le.mp hY)
        (by norm_num) (Arithmetic.zero_le _)) (pos_iff_one_le.mp (hv 10))
      _=c := rfl
  obtain ⟨g,hg⟩ := IndependentYGraphDraft.main_root p v hv hz
  change g*g=(a*a+(4*a+3))*(c*c)+1 at hg
  have hnorm : (ι g:DiffRing V)*ι g =
      1+(((ι a:DiffRing V)+2)*((ι a:DiffRing V)+2)-1)*((ι c:DiffRing V)*ι c) := by
    have hh := congrArg (fun x : V => (ι x:DiffRing V)) hg
    simp only [map_add,map_mul,map_ofNat,map_one] at hh
    linear_combination hh
  obtain ⟨_,_,hw,_,_⟩ := IndependentYGraphDraft.residuals p v hv hz
  change (P64QCube76Y.graph pp).W.evalRing z=0 at hw
  have heval : (P64QCube76Y.graph pp).W.evalRing z =
      ((ι (v 5):DiffRing V)*((ι c:DiffRing V)*ι c))*
        ((ι (v 5):DiffRing V)*((ι c:DiffRing V)*ι c))-
      (((ι a:DiffRing V)+2)*((ι a:DiffRing V)+2)-1)*
        ((ι (v 4):DiffRing V)*ι (v 4)-1) := by
    rw [strong_eval]
    simp [z,pp,q,Y,X,a,c]
    <;> try simp
    <;> ring
  rw [heval] at hw
  have hstrong : (((ι a:DiffRing V)+2)*((ι a:DiffRing V)+2)-1)*
      ((ι (v 4):DiffRing V)*ι (v 4)-1) =
      ((ι (v 5):DiffRing V)*((ι c:DiffRing V)*ι c))*
        ((ι (v 5):DiffRing V)*((ι c:DiffRing V)*ι c)) := by
    linear_combination -hw
  have hn : (2:DiffRing V)≤(ι a:DiffRing V)+2 := by have h := ι_nonneg a; linarith
  have hc : (3:DiffRing V)≤ι c := by
    have hh := (ι_le_ι (V:=V)).mpr hc3
    rwa [map_ofNat] at hh
  have hf : (1:DiffRing V)≤ι (v 4) := ModelArithmetic.model_discrete _ (ModelArithmetic.ι_pos (hv 4))
  have hi : (1:DiffRing V)≤ι (v 5) := ModelArithmetic.model_discrete _ (ModelArithmetic.ι_pos (hv 5))
  exact IndependentYBounds.strong_f_bound ((ι a:DiffRing V)+2) (ι c) (ι g)
    (ι (v 4)) (ι (v 5)) hn hc (ι_nonneg g) hf hi hnorm hstrong

#print axioms IndependentYSizeDraft.actual_f_bound
end IndependentYSizeDraft
