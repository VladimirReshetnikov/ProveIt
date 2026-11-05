import P64QCube78
import P64QCube78Split

/-! Draft: recover the 79 residuals from an actual positive 78 zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace P64QCube78GraphSplit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open P64QCubeMap P64QCube78Split
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem main_same (p : Fin 4 → ℤ) : (P64QCube78.graph p).M=(P64QCube81.graph p).M := by rfl
theorem strong_same (p : Fin 4 → ℤ) : (P64QCube78.graph p).W=(P64QCube81.graph p).W := by rfl
theorem auxiliary_same (p : Fin 4 → ℤ) : (P64QCube78.graph p).Na=(P64QCube81.graph p).Na := by rfl
theorem transport_same (p : Fin 4 → ℤ) : (P64QCube78.graph p).Lt=(P64QCube81.graph p).Lt := by rfl
theorem output_shape (p : Fin 4 → ℤ) : (P64QCube78.graph p).output =
    (P64QCube78.graph p).A0*(P64QCube78.graph p).A0+
    (P64QCube78.graph p).M*(P64QCube78.graph p).M+
    (P64QCube78.graph p).W*(P64QCube78.graph p).W+
    (P64QCube78.graph p).Na*(P64QCube78.graph p).Na+
    (P64QCube78.graph p).Lt*(P64QCube78.graph p).Lt-2 := by rfl

theorem first_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    let q := (p 0:R)*v 0+1
    let Y := (q*q*q)*v 7
    let X := v 8*q
    let P := (X*Y)*Y
    let k := v 10+v 11
    (P64QCube78.graph p).A0.evalRing v=v 9*v 9-(P*k)*(P*k+k) := by
  simp [P64QCube78.graph,Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat]
  ring

theorem first_eq_one (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hv : ∀i,0<v i)
    (hz : InternalZero (P64QCube78.graph (fun j => (p j:ℤ))).output v) :
    (P64QCube78.graph (fun j => (p j:ℤ))).A0.evalRing (fun i => ι (v i)) = 1 := by
  let pp : Fin 4 → ℤ := fun j => (p j:ℤ)
  let z : Fin 14 → DiffRing V := fun i => ι (v i)
  let w : Fin 14 → V := lift p v
  let q : V := (p 0:V)*v 0+1
  let Y : V := (q*q*q)*v 7
  let X : V := v 8*q
  let P : V := (X*Y)*Y
  let k : V := v 10+v 11
  let first : DiffRing V := (P64QCube78.graph pp).A0.evalRing z
  have hs : first*first+(P64QCube78.graph pp).M.evalRing z*(P64QCube78.graph pp).M.evalRing z+
      (P64QCube78.graph pp).W.evalRing z*(P64QCube78.graph pp).W.evalRing z+
      (P64QCube78.graph pp).Na.evalRing z*(P64QCube78.graph pp).Na.evalRing z+
      (P64QCube78.graph pp).Lt.evalRing z*(P64QCube78.graph pp).Lt.evalRing z=2 := by
    have hh := hz
    rw [internalZero_iff,output_shape] at hh
    simp only [Expr.evalRing_add,Expr.evalRing_mul,Expr.evalRing_sub,Expr.evalRing_ofNat] at hh
    exact sub_eq_zero.mp hh
  have hq : 0<q := by dsimp [q]; simp
  have hX : 0<X := mul_pos (hv 8) hq
  have hY : 0<Y := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 7)
  have hP : 1≤P := pos_iff_one_le.mp (mul_pos (mul_pos hX hY) hY)
  have hk : 0<k := add_pos (hv 10) (hv 11)
  have hP' : (1:DiffRing V)≤ι P := by simpa using (ι_le_ι (V:=V)).mpr hP
  have hk' : (ι k:DiffRing V)≠0 := ne_of_gt (ModelArithmetic.ι_pos hk)
  have hfirst : first=(ι (v 9):DiffRing V)*ι (v 9) - (ι P*ι k)*(ι P*ι k+ι k) := by
    dsimp [first]
    rw [first_eval]
    simp [z,pp,P,X,Y,q,k]
  have hnzero : first≠0 := by rw [hfirst]; exact norm_ne_zero _ _ _ hP' hk'
  have hsq : first*first=1 := first_sq_one hs hnzero
  have hs1 : (0:DiffRing V)*0+(P64QCube78.graph pp).M.evalRing z*(P64QCube78.graph pp).M.evalRing z+
      (P64QCube78.graph pp).W.evalRing z*(P64QCube78.graph pp).W.evalRing z+
      (P64QCube78.graph pp).Na.evalRing z*(P64QCube78.graph pp).Na.evalRing z+
      (P64QCube78.graph pp).Lt.evalRing z*(P64QCube78.graph pp).Lt.evalRing z=1 := by
    linarith
  rw [main_same pp,strong_same pp,auxiliary_same pp,transport_same pp,
    ←P64QCubeBinding.main pp z,←P64QCubeBinding.strong pp z,
    ←P64QCubeBinding.auxiliary pp z,←P64QCubeBinding.transport pp z,←P64QCubeMap.lift_cast p v] at hs1
  obtain ⟨_,_,_,_,hlt⟩ := P64NormFirstReplacement.residuals p w (P64QCubeMap.lift_pos p v hv) 0 hs1
  have hgap := (P64Root.transport p w (P64QCubeMap.lift_pos p v hv) hlt).1
  have hb : 0<(p 0:V) := by
    by_contra hn
    have he : (p 0:V)=0 := le_antisymm (le_of_not_gt hn) (by simp)
    rw [he,zero_mul,zero_add] at hgap
    have hone : 1≤w 1+w 2 := pos_iff_one_le.mp (add_pos ((P64QCubeMap.lift_pos p v hv) 1) ((P64QCubeMap.lift_pos p v hv) 2))
    exact (not_lt_of_ge hone) hgap
  have hq2 : 2≤q := by
    have hh := one_le_mul_of_one_le_of_one_le (pos_iff_one_le.mp hb) (pos_iff_one_le.mp (hv 0))
    dsimp [q]
    have ht := add_le_add_right hh (1:V)
    simpa only [one_add_one_eq_two,add_comm] using ht
  have hX2 : 2≤X := by
    have hh := mul_le_mul (pos_iff_one_le.mp (hv 8)) hq2 (by norm_num) (by simp)
    simpa [X] using hh
  have hP2 : 2≤P := by
    have hy1 := pos_iff_one_le.mp hY
    have hh := mul_le_mul (mul_le_mul hX2 hy1 (by simp) (by simp)) hy1 (by simp) (by simp)
    simpa [P] using hh
  have hP2' : (2:DiffRing V)≤ι P := ModelArithmetic.two_le_ι hP2
  have hnneg : first≠ -1 := by rw [hfirst]; exact norm_ne_neg _ _ _ hP2'
  exact first_one hsq hnneg

#print axioms P64QCube78GraphSplit.first_eq_one
end P64QCube78GraphSplit
