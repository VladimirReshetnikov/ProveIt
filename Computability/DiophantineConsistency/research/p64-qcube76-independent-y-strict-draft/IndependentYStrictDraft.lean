import IndependentYSizeDraft
import P64QCube76YBinding

/-! Unchecked draft: evaluate the auxiliary factor and derive the new-root guard. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace IndependentYStrictDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section Ring
variable {R : Type*} [CommRing R]

def cValue (p : Fin 4 → ℤ) (v : Fin 14 → R) : R :=
  let q := (p 0:R)*v 0+1
  let Y := q*q*q*v 7
  (v 10+v 11)*Y+v 10

def aValue (p : Fin 4 → ℤ) (v : Fin 14 → R) : R :=
  let q := (p 0:R)*v 0+1
  let Y := q*q*q*v 7
  (v 8*q)*Y+Y

def rankValue (p : Fin 4 → ℤ) (v : Fin 14 → R) : R :=
  let qm := (p 0:R)*v 0
  let q := qm+1
  let gap := qm*(q-v 1)+v 2
  gap*(q*q-1)+((p 2:R)+q*(p 3:R))*v 0

def termValue (p : Fin 4 → ℤ) (v : Fin 14 → R) : R :=
  cValue p v*v 6-rankValue p v

def deltaValue (p : Fin 4 → ℤ) (v : Fin 14 → R) : R :=
  let a := aValue p v
  a*a+(4*a+3)

theorem oldV_decomposition (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    P64QCube76YBinding.oldV p v=(v 4*v 4)*termValue p v-cValue p v := by
  rfl

theorem auxiliary_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P64QCube76Y.graph p).Na.evalRing v =
      (deltaValue p v*(v 4*v 4-1))*
        (P64QCube76YBinding.oldV p v*P64QCube76YBinding.oldV p v-v 12*v 12)+v 12*v 12 := by
  simp [P64QCube76Y.graph,deltaValue,aValue,P64QCube76YBinding.oldV,
    Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat]

end Ring

theorem actual_strict (p : Fin 4 → ℕ) (v : Fin 14 → V) (hv : ∀i,0<v i)
    (hz : InternalZero (P64QCube76Y.graph (fun j => (p j:ℤ))).output v) :
    P64QCube76YBinding.oldV (fun j => (p j:ℤ)) (fun i => ι (v i)) < ι (v 12) := by
  let pp : Fin 4 → ℤ := fun j => (p j:ℤ)
  let z : Fin 14 → DiffRing V := fun i => ι (v i)
  let q : V := (p 0:V)*v 0+1
  let Y : V := (q*q*q)*v 7
  let X : V := v 8*q
  let a : V := X*Y+Y
  let c : V := (v 10+v 11)*Y+v 10
  let cv : DiffRing V := cValue pp z
  let av : DiffRing V := aValue pp z
  let A : DiffRing V := deltaValue pp z*(z 4*z 4-1)
  let V0 : DiffRing V := P64QCube76YBinding.oldV pp z
  let y : DiffRing V := z 12
  let t : DiffRing V := termValue pp z
  have hcval : cv=ι c := by simp [cv,cValue,z,pp,q,Y,c]
  have haval : av=ι a := by simp [av,aValue,z,pp,q,Y,X,a]
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
  have hc : (3:DiffRing V)≤cv := by
    rw [hcval]
    have hh := (ι_le_ι (V:=V)).mpr hc3
    rwa [map_ofNat] at hh
  have hf : (1:DiffRing V)≤z 4 := ModelArithmetic.model_discrete _ (ModelArithmetic.ι_pos (hv 4))
  have hy : (1:DiffRing V)≤y := ModelArithmetic.model_discrete _ (ModelArithmetic.ι_pos (hv 12))
  have hsize : cv+1<z 4*z 4 := by
    have hh := IndependentYSizeDraft.actual_f_bound p v hv hz
    change (ι c:DiffRing V)+1 < (ι (v 4):DiffRing V)*ι (v 4) at hh
    simpa [hcval,z] using hh
  have hdelta : (2:DiffRing V)≤deltaValue pp z := by
    have ha : 0≤av := by rw [haval]; exact ι_nonneg a
    dsimp [deltaValue]
    change (2:DiffRing V)≤av*av+(4*av+3)
    nlinarith only [ha, sq_nonneg av]
  have hffpos : (0:DiffRing V)<z 4*z 4-1 := by linarith
  have hff : (1:DiffRing V)≤z 4*z 4-1 := ModelArithmetic.model_discrete _ hffpos
  have hA : (2:DiffRing V)≤A := by
    dsimp [A]
    have hh := mul_le_mul hdelta hff (by norm_num) (by linarith)
    simpa using hh
  have hV : V0=z 4*z 4*t-cv := by
    exact oldV_decomposition pp z
  obtain ⟨_,_,_,hn,_⟩ := IndependentYGraphDraft.residuals p v hv hz
  change (P64QCube76Y.graph pp).Na.evalRing z=1 at hn
  rw [auxiliary_eval] at hn
  have haux : A*(V0*V0-y*y)+y*y=1 := hn
  exact IndependentYBounds.strict_auxiliary A cv (z 4) V0 y t hA hc hf hy hsize hV haux

#print axioms IndependentYStrictDraft.oldV_decomposition
#print axioms IndependentYStrictDraft.auxiliary_eval
#print axioms IndependentYStrictDraft.actual_strict
end IndependentYStrictDraft
