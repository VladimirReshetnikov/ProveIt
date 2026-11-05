import P64QCube80
import P64QCubeBinding
import P64NormFirstReplacement
import P64ModelRemainderGap

/-! Draft: every positive 80-candidate zero has s<r0. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace P64QCube80Gap
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open ArithmeticPellRecurrence P64QCubeMap
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem main_same (p : Fin 4 → ℤ) : (P64QCube80.graph p).M=(P64QCube81.graph p).M := by rfl
theorem strong_same (p : Fin 4 → ℤ) : (P64QCube80.graph p).W=(P64QCube81.graph p).W := by rfl
theorem auxiliary_same (p : Fin 4 → ℤ) : (P64QCube80.graph p).Na=(P64QCube81.graph p).Na := by rfl
theorem transport_same (p : Fin 4 → ℤ) : (P64QCube80.graph p).Lt=(P64QCube81.graph p).Lt := by rfl
theorem output_shape (p : Fin 4 → ℤ) : (P64QCube80.graph p).output =
    (P64QCube80.graph p).A0*(P64QCube80.graph p).A0+
    (P64QCube80.graph p).M*(P64QCube80.graph p).M+
    (P64QCube80.graph p).W*(P64QCube80.graph p).W+
    (P64QCube80.graph p).Na*(P64QCube80.graph p).Na+
    (P64QCube80.graph p).Lt*(P64QCube80.graph p).Lt-1 := by rfl

theorem first_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    let q := (p 0:R)*v 0+1
    let Y := (q*q*q)*v 7
    let X := v 8*q
    let k := v 10+v 11
    let ell := (X*Y)*(k*Y)
    (P64QCube80.graph p).A0.evalRing v=(ell+v 9)*(ell+v 9)-(ell*(ell+k)+1) := by
  simp [P64QCube80.graph,Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat]

theorem graph_remainder (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hv : ∀i,0<v i)
    (hz : InternalZero (P64QCube80.graph (fun j => (p j:ℤ))).output v) : v 7<v 9 := by
  let pp : Fin 4 → ℤ := fun j => (p j:ℤ)
  let z : Fin 14 → DiffRing V := fun i => ι (v i)
  let w : Fin 14 → V := lift p v
  let q : V := (p 0:V)*v 0+1
  let X : V := v 8*q
  let Y : V := (q*q*q)*v 7
  let P : V := (X*Y)*Y
  let k : V := v 10+v 11
  let ell : V := P*k
  let a : V := X*Y+Y
  let first : DiffRing V := (P64QCube80.graph pp).A0.evalRing z
  have hs : first*first+(P64QCube80.graph pp).M.evalRing z*(P64QCube80.graph pp).M.evalRing z+
      (P64QCube80.graph pp).W.evalRing z*(P64QCube80.graph pp).W.evalRing z+
      (P64QCube80.graph pp).Na.evalRing z*(P64QCube80.graph pp).Na.evalRing z+
      (P64QCube80.graph pp).Lt.evalRing z*(P64QCube80.graph pp).Lt.evalRing z=1 := by
    have hh := hz
    rw [internalZero_iff,output_shape] at hh
    simp only [Expr.evalRing_add,Expr.evalRing_mul,Expr.evalRing_sub,Expr.evalRing_ofNat,Nat.cast_one] at hh
    exact sub_eq_zero.mp hh
  rw [main_same pp,strong_same pp,auxiliary_same pp,transport_same pp,
    ←P64QCubeBinding.main pp z,←P64QCubeBinding.strong pp z,
    ←P64QCubeBinding.auxiliary pp z,←P64QCubeBinding.transport pp z,←lift_cast p v] at hs
  obtain ⟨hfirst,hm,_,_,hlt⟩ := P64NormFirstReplacement.residuals p w (lift_pos p v hv) first hs
  have hwpos : ∀i,0<w i := lift_pos p v hv
  have hgap := (P64Root.transport p w hwpos hlt).1
  have hb : 0<(p 0:V) := by
    by_contra hn
    have he : (p 0:V)=0 := le_antisymm (le_of_not_gt hn) (by simp)
    rw [he,zero_mul,zero_add] at hgap
    have hone : 1≤w 1+w 2 := pos_iff_one_le.mp (add_pos (hwpos 1) (hwpos 2))
    exact (not_lt_of_ge hone) hgap
  have hF : w 1≤(p 0:V)*w 0+1 := le_trans (by simp) (le_of_lt hgap)
  have hYdiv : ((p 0:V)*w 0+1)*((p 0:V)*w 0+1)*((p 0:V)*w 0+1) ∣ w 7 := by
    refine ⟨v 7,?_⟩
    simp [w,lift]
  obtain ⟨g,hg,_⟩ := P64Root.main_root p w hwpos hb hF hYdiv hm
  have hq : 0<q := by dsimp [q]; simp
  have hq1 : 1≤q := by dsimp [q]; simp
  have hX : 0<X := mul_pos (hv 8) hq
  have hsY : v 7≤Y := by
    have hQ : 1≤q*q*q := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hq1 hq1) hq1
    calc
      v 7=1*v 7 := by ring
      _≤(q*q*q)*v 7 := mul_le_mul_of_nonneg_right hQ (by simp)
      _=Y := rfl
  have hfnorm : (ell+v 9)*(ell+v 9)=1+ell*(ell+k) := by
    have hh := hfirst
    change (P64QCube80.graph pp).A0.evalRing z=0 at hh
    rw [first_eval] at hh
    apply ι_injective
    simp only [ell,P,X,Y,k,q,map_add,map_mul,map_one]
    simp only [z,pp,P64Root.cast_nat] at hh
    linear_combination hh
  have hmain : g*g=1+delta a*(v 10+Y*k)*(v 10+Y*k) := by
    change g*g=(a*a+(4*a+3))*((k*Y+v 10)*(k*Y+v 10))+1 at hg
    rw [hg]
    dsimp [delta]
    ring
  exact P64ModelRemainderGap.remainder_gt X Y (v 7) k (v 10) (v 11) (v 9) g
    hX (hv 7) hsY (hv 10) (hv 11) rfl hfnorm hmain

#print axioms P64QCube80Gap.graph_remainder
end P64QCube80Gap
