import DiophantineConsistency.ArithmeticSignedPairExpressions
import DiophantineConsistency.ArithmeticAdaptiveStrongNorm2011

/-! Literal adaptive auxiliary factor as an internal signed Pell norm. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveAuxNorm2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveFactorUnits2011 ArithmeticAdaptiveScaledNorms2011
open ArithmeticAdaptiveTransport2011 ArithmeticAdaptiveStrongNorm2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
open ArithmeticSignedPairExpressions
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
def AuxNorm (p : Fin 4 → ℕ) (v : Fin 13 → V) : Prop :=
  let q : V := 1+v 0*(p 0:V)
  let k : V := v 9+v 10
  let c : V := v 9+v 7*k
  let I : V := (c*c)*v 4
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  let L : V := (v 3*v 3)*v 5*c
  let M : V := (v 3*v 3)*R+c
  let z : V := magnitude (L,M)
  let y : V := magnitude (L+v 11,M)
  I*I*z*z+y*y=1+I*I*y*y

theorem expressionAt_aux_norm (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (expressionAt (fun j => (p j:ℤ))) v) : AuxNorm p v := by
  let eB : Expr (Fin 13) := .mul (.var 0) (.constant (p 0))
  let eQ : Expr (Fin 13) := .add (.constant 1) eB
  let eK : Expr (Fin 13) := .add (.var 9) (.var 10)
  let eC : Expr (Fin 13) := .add (.var 9) (.mul (.var 7) eK)
  let eA : Expr (Fin 13) := .add (.mul (.var 6) (.var 7)) (.var 7)
  let eD : Expr (Fin 13) := .add (.add (.constant 3) (.mul (.constant 4) eA)) (.mul eA eA)
  let eI : Expr (Fin 13) := .mul (.mul eC eC) (.var 4)
  let eF : Expr (Fin 13) := .var 3
  let eR : Expr (Fin 13) := .add
    (.mul (.add (.var 2) (.mul (.sub eQ (.var 1)) eB)) (.sub (.mul eQ eQ) (.constant 1)))
    (.mul (.var 0) (.add (.constant (p 2)) (.mul (.constant (p 3)) eQ)))
  let eV : Expr (Fin 13) := .sub (.mul (.mul eF eF) (.sub (.mul (.var 5) eC) eR)) eC
  let eY : Expr (Fin 13) := .add eV (.var 11)
  let eH : Expr (Fin 13) := .mul eD (.sub (.mul eF eF) (.constant 1))
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let k : V := v 9+v 10
  let c : V := v 9+v 7*k
  let a : V := v 6*v 7+v 7
  let D : V := (3+4*a)+a*a
  let I : V := (c*c)*v 4
  let R' : V := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  let L : V := (v 3*v 3)*v 5*c
  let M : V := (v 3*v 3)*R+c
  let z : V := magnitude (L,M)
  let y : V := magnitude (L+v 11,M)
  have hq : 1≤q := le_of_lt (scaled_parameters_positive p v hb hv).1
  have hgap : v 1+v 2<q := tsub_pos_iff_lt.mp (expressionAt_transport_positive p v hb hv hz).2
  have hF : v 1≤q := le_trans (by simp : v 1≤v 1+v 2) (le_of_lt hgap)
  have hbq : q-1=b := by dsimp [q]; rw [add_comm]; simp
  have hRank : R'=R := by dsimp [R,R']; rw [hbq]; simp only [pow_two]; ring
  have hB : SignedRep eB v (natural b) := rep_mul_nat (rep_var v 0) (rep_nat v (p 0))
  have hQ : SignedRep eQ v (natural q) := rep_add_nat (rep_one v) hB
  have hK : SignedRep eK v (natural k) := rep_add_nat (rep_var v 9) (rep_var v 10)
  have hC : SignedRep eC v (natural c) := rep_add_nat (rep_var v 9) (rep_mul_nat (rep_var v 7) hK)
  have hA : SignedRep eA v (natural a) := rep_add_nat (rep_mul_nat (rep_var v 6) (rep_var v 7)) (rep_var v 7)
  have hD : SignedRep eD v (natural D) := rep_add_nat
    (rep_add_nat (rep_three v) (rep_mul_nat (rep_four v) hA)) (rep_mul_nat hA hA)
  have hq2 : (1:V)≤q*q := by simpa only [one_mul] using mul_le_mul hq hq (by simp) (by simp)
  have hR' : SignedRep eR v (natural R') := rep_add_nat
    (rep_mul_nat (rep_add_nat (rep_var v 2) (rep_mul_nat (rep_tsub hQ (rep_var v 1) hF) hB))
      (rep_tsub (rep_mul_nat hQ hQ) (rep_one v) hq2))
    (rep_mul_nat (rep_var v 0) (rep_add_nat (rep_nat v (p 2)) (rep_mul_nat (rep_nat v (p 3)) hQ)))
  have hR : SignedRep eR v (natural R) := by rw [hRank] at hR'; exact hR'
  have hF2 : SignedRep (.mul eF eF) v (natural (v 3*v 3)) := rep_mul_nat (rep_var v 3) (rep_var v 3)
  have hn : I*I+D=D*(v 3*v 3) := expressionAt_strong_norm p v hz
  have hH : SignedRep eH v (natural (I*I)) := by
    have h := rep_mul hD (rep_sub hF2 (rep_one v))
    have h' : SignedRep eH v (D*(v 3*v 3),D) := by
      simpa only [multiply,minus,natural,add_zero,zero_add,mul_zero,zero_mul,mul_one] using h
    apply equivalent_trans h'
    change D*(v 3*v 3)+0=D+I*I
    simpa only [add_zero,zero_add,add_comm] using hn.symm
  have hV : SignedRep eV v (L,M) := by
    have h := rep_sub (rep_mul hF2 (rep_sub (rep_mul_nat (rep_var v 5) hC) hR)) hC
    simpa only [L,M,multiply,minus,natural,add_zero,zero_add,mul_zero,zero_mul,mul_assoc] using h
  have hY : SignedRep eY v (L+v 11,M) := by
    have h := rep_add hV (rep_var v 11)
    simpa only [plus,natural,add_zero] using h
  have hV2 : SignedRep (.mul eV eV) v (natural (z*z)) :=
    equivalent_trans (rep_mul hV hV) (square_magnitude (L,M))
  have hY2 : SignedRep (.mul eY eY) v (natural (y*y)) :=
    equivalent_trans (rep_mul hY hY) (square_magnitude (L+v 11,M))
  have haux : SignedRep (.sub (.mul eY eY) (.mul eH (.sub (.mul eY eY) (.mul eV eV)))) v
      (y*y+(I*I)*(z*z),(I*I)*(y*y)) := by
    have h := rep_sub hY2 (rep_mul hH (rep_sub hY2 hV2))
    simpa only [multiply,minus,natural,add_zero,zero_add,mul_zero,zero_mul] using h
  have hu := (expressionAt_factor_units (fun j => (p j:ℤ)) v hz).2.2.1
  change (pairEval (.sub (.mul eY eY) (.mul eH (.sub (.mul eY eY) (.mul eV eV)))) v).1 =
    (pairEval (.sub (.mul eY eY) (.mul eH (.sub (.mul eY eY) (.mul eV eV)))) v).2+1 at hu
  have he := represented_unit hu haux
  calc
    I*I*z*z+y*y = y*y+(I*I)*(z*z) := by ring
    _=(I*I)*(y*y)+1 := he
    _=1+I*I*y*y := by ring

private theorem beta_positive_nat : 0<CurrentMasks2011.beta := by
  have hr : 1<CurrentMasks2011.radix := by unfold CurrentMasks2011.radix; norm_num
  have hp : 1<CurrentMasks2011.radix^2011 := one_lt_pow₀ hr (by decide)
  unfold CurrentMasks2011.beta
  omega

theorem current_aux_norm (v : Fin 13 → V) (hv : ∀j,0<v j)
    (hz : InternalZero expression v) : AuxNorm currentPorts v := by
  have hb : 0<(CurrentMasks2011.beta:V) := by exact_mod_cast beta_positive_nat
  have hp : 0<(currentPorts 0:V) := by simpa only [currentPorts,Matrix.cons_val_zero] using hb
  apply expressionAt_aux_norm currentPorts v hp hv
  rw [currentPorts_cast]; exact hz

theorem current_natural_aux_norm (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    AuxNorm currentPorts (fun j => v j+1) :=
  current_aux_norm _ (fun j => lt_of_le_of_lt (Arithmetic.zero_le (v j)) (lt_add_one _))
    ((internalZero_positiveShift expression v).mp hz)
end DiophantineConsistency.ArithmeticAdaptiveAuxNorm2011
