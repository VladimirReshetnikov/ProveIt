import DiophantineConsistency.AdaptiveGap85FirstDivisibility
import DiophantineConsistency.AdaptiveDirectOrdinate86FixedForward
import DiophantineConsistency.ArithmeticAdaptiveConstructionFactorLemmas2011

/-! Model-uniform signed-root completion; the remaining three factors are open. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85FirstNormModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions
open ArithmeticAdaptiveFactorMagnitude2011 ArithmeticAdaptiveScaledNorms2011
open AdaptiveGap85Literal AdaptiveGap85FirstDivisibility ArithmeticAdaptiveConstructionFactorLemmas2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def witness (p : Fin 4 → ℕ) (J X Y eta zeta t first f i T y gamma : V) : Fin 13 → V :=
  let b := J*(p 0:V)
  let q := 1+b
  let Amin := (X-1)+(p 1:V)*q
  let k := eta+zeta
  let ell := (X*Y)*(Y*k)
  let s := ell+k+t+1
  let C := b*q*(s+1)
  let F := b*((s+1)*Amin+1)
  let r := first+k*(b*q*s)+b*s+1
  ![J,F,C,f,i,T,X,Y,r,eta,zeta,y,gamma]

theorem carrier_algebra (b Q Amin k ell t first : V) :
    let q := 1+b
    let s := ell+k+t+1
    let C := b*q*(s+1)
    let F := b*((s+1)*Amin+1)
    let r := first+k*(b*q*s)+b*s+1
    let M := Q*b
    let W := 1+k*b
    let A := Amin+1
    M*(ell+k+r)+(Q*t)*b+(F*q)*(W*Q) = (C*A)*(W*Q)+M*first := by
  dsimp only
  ring

theorem first_factor_unit (p : Fin 4 → ℕ) (v : Fin 13 → V) (tau : V)
    (hcut : let b := v 0*(p 0:V)
      let q := 1+b
      let Q := q*(q*q)
      let k := v 9+v 10
      let ell := (v 6*v 7)*(v 7*k)
      let M := Q*b
      let W := 1+k*b
      let A := v 6+(p 1:V)*q
      M*(ell+k+v 8)+v 7*b+(v 1*q)*(W*Q)=(v 2*A)*(W*Q)+M*tau)
    (hnorm : let k := v 9+v 10
      let ell := (v 6*v 7)*(v 7*k)
      tau*tau=1+ell*(ell+k)) :
    (pairEval (AdaptiveGap85Factors.factors (fun j => (p j:ℤ))).1 v).1 =
      (pairEval (AdaptiveGap85Factors.factors (fun j => (p j:ℤ))).1 v).2+1 := by
  let b := v 0*(p 0:V)
  let q := 1+b
  let Q := q*(q*q)
  let k := v 9+v 10
  let ell := (v 6*v 7)*(v 7*k)
  let M := Q*b
  let W := 1+k*b
  let A := v 6+(p 1:V)*q
  let root := M*tau
  let rhs := M*M*(1+ell*(ell+k))
  have hrep := first_root_rep85 p v
  have hroot : Equivalent (pairEval (rootTerm (AdaptiveGap85Factors.factors (fun j => (p j:ℤ))).1) v)
      (natural root) := by
    apply equivalent_trans hrep
    change (M*(ell+k+v 8)+v 7*b+(v 1*q)*(W*Q))+0=(v 2*A)*(W*Q)+root
    simpa only [add_zero,root] using hcut
  have hrhs : Equivalent (pairEval (rightTerm (AdaptiveGap85Factors.factors (fun j => (p j:ℤ))).1) v)
      (natural rhs) := by
    have heq : pairEval (rightTerm (AdaptiveGap85Factors.factors (fun j => (p j:ℤ))).1) v =
        pairEval (rightTerm (ArithmeticAdaptiveFactorMagnitude2011.factors (fun j => (p j:ℤ))).1) v := rfl
    rw [heq, first_rhs_pair p v]
    exact equivalent_refl _
  have hsq : root*root=rhs := by
    change (M*tau)*(M*tau)=M*M*(1+ell*(ell+k))
    calc _=M*M*(tau*tau) := by ring
         _=M*M*(1+ell*(ell+k)) := by rw [show tau*tau=1+ell*(ell+k) from hnorm]
  change (pairEval (1+(rootTerm (AdaptiveGap85Factors.factors (fun j => (p j:ℤ))).1 *
    rootTerm (AdaptiveGap85Factors.factors (fun j => (p j:ℤ))).1 -
    rightTerm (AdaptiveGap85Factors.factors (fun j => (p j:ℤ))).1)) v).1 = _
  exact square_factor_unit _ _ v root rhs hroot hrhs hsq

theorem completion_first_factor (p : Fin 4 → ℕ) (J X Y eta zeta t first f i T y gamma : V)
    (hX : 1≤X) (hY : Y=(1+J*(p 0:V))*((1+J*(p 0:V))*(1+J*(p 0:V)))*t)
    (hnorm : first*first=1+((X*Y)*(Y*(eta+zeta)))*(((X*Y)*(Y*(eta+zeta)))+(eta+zeta))) :
    let v := witness p J X Y eta zeta t first f i T y gamma
    (pairEval (AdaptiveGap85Factors.factors (fun j => (p j:ℤ))).1 v).1 =
      (pairEval (AdaptiveGap85Factors.factors (fun j => (p j:ℤ))).1 v).2+1 := by
  let v := witness p J X Y eta zeta t first f i T y gamma
  let b : V := J*(p 0:V)
  let q := 1+b
  let Q := q*(q*q)
  let Amin := (X-1)+(p 1:V)*q
  let k := eta+zeta
  let ell := (X*Y)*(Y*k)
  have hx : (X-1)+1=X := tsub_add_cancel_of_le hX
  have hA : X+(p 1:V)*q=Amin+1 := by
    calc
      _ = ((X-1)+1)+(p 1:V)*q := by rw [hx]
      _ = Amin+1 := by dsimp [Amin]; ring
  have hcut := carrier_algebra b Q Amin k ell t first
  dsimp only at hcut
  apply first_factor_unit p v first
  · simpa [v,witness,b,q,Q,Amin,k,ell,hA,hY] using hcut
  · simpa [v,witness,k,ell] using hnorm
theorem positive_completion (p : Fin 4 → ℕ) (J X Y eta zeta t first f i T y gamma : V)
    (hb : 0<(p 0:V)) (hJ : 0<J) (hX : 0<X) (hY : 0<Y)
    (heta : 0<eta) (hzeta : 0<zeta) (hfirst : 0<first)
    (hf : 0<f) (hi : 0 < i) (hT : 0<T) (hy : 0<y) (hgamma : 0<gamma) :
    let v := witness p J X Y eta zeta t first f i T y gamma
    (∀ j,0<v j) ∧ ¬(v 1+v 2<1+v 0*(p 0:V)) := by
  let b : V := J*(p 0:V)
  let q := 1+b
  let Amin := (X-1)+(p 1:V)*q
  let k := eta+zeta
  let ell := (X*Y)*(Y*k)
  let s := ell+k+t+1
  let C := b*q*(s+1)
  let F := b*((s+1)*Amin+1)
  let r := first+k*(b*q*s)+b*s+1
  have hport : 0<p 0 := by exact_mod_cast hb
  have hbpos : 0<b := mul_pos hJ hb
  have hqpos : 0<q := by dsimp [q]; exact lt_of_lt_of_le (by simp : (0:V)<1) (by simp)
  have hspos : 0<s := by dsimp [s]; exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  have hC : 0<C := by dsimp [C]; exact mul_pos (mul_pos hbpos hqpos) (lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _))
  have hF : 0<F := by dsimp [F]; exact mul_pos hbpos (lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _))
  have hr : 0<r := by dsimp [r]; exact lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
  have hb1 : 1≤b := pos_iff_one_le.mp hbpos
  have hs1 : 1≤s+1 := by simp
  have hqle : q≤C := by
    have h1 : q≤b*q := by simpa using (mul_le_mul_of_nonneg_right hb1 (Arithmetic.zero_le q))
    have h2 : b*q≤b*q*(s+1) := by simpa using (mul_le_mul_of_nonneg_left hs1 (Arithmetic.zero_le (b*q)))
    exact le_trans h1 h2
  constructor
  · intro j
    fin_cases j <;> simp [witness] <;> first | assumption | exact ⟨hJ,hport⟩
  · change ¬(F+C<q)
    apply not_lt_of_ge
    exact le_trans hqle (by simpa [add_comm] using le_add_of_nonneg_left (Arithmetic.zero_le F) C)

/-- Fixed-port first-factor completion in every IΣ₁ model. The remaining
factor units and existence of full zeros are not asserted. -/
theorem current_completion (J X Y eta zeta t first f i T y gamma : V)
    (hJ : 0<J) (hX : 0<X) (hYpos : 0<Y) (heta : 0<eta) (hzeta : 0<zeta)
    (hfirst : 0<first) (hf : 0<f) (hi : 0 < i) (hT : 0<T) (hy : 0<y) (hgamma : 0<gamma)
    (hY : Y=(1+J*(currentPorts 0:V))*((1+J*(currentPorts 0:V))*(1+J*(currentPorts 0:V)))*t)
    (hnorm : first*first=1+((X*Y)*(Y*(eta+zeta)))*(((X*Y)*(Y*(eta+zeta)))+(eta+zeta))) :
    let v := witness currentPorts J X Y eta zeta t first f i T y gamma
    (∀ j,0<v j) ∧ ¬(v 1+v 2<1+v 0*(currentPorts 0:V)) ∧
      (pairEval (AdaptiveGap85Factors.factors CurrentWindowCarry2011.ports).1 v).1 =
        (pairEval (AdaptiveGap85Factors.factors CurrentWindowCarry2011.ports).1 v).2+1 := by
  have hb := (AdaptiveDirectOrdinate86FixedForward.fixed_port_bounds (V:=V)).1
  have hp := positive_completion currentPorts J X Y eta zeta t first f i T y gamma
    hb hJ hX hYpos heta hzeta hfirst hf hi hT hy hgamma
  have hu := completion_first_factor currentPorts J X Y eta zeta t first f i T y gamma
    (pos_iff_one_le.mp hX) hY hnorm
  rw [currentPorts_cast] at hu
  exact ⟨hp.1,hp.2,hu⟩

end DiophantineConsistency.AdaptiveGap85FirstNormModel
