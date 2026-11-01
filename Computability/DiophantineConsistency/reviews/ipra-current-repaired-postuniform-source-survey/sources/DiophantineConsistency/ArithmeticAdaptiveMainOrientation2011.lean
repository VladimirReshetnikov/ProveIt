import DiophantineConsistency.ArithmeticSignedPairExpressions
import DiophantineConsistency.ArithmeticAdaptiveTransportQuotient2011

/-! The literal adaptive main root is positive; its quotient is oriented. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveMainOrientation2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs
open ArithmeticAdaptiveFactorMagnitude2011 ArithmeticAdaptiveScaledNorms2011
open ArithmeticAdaptiveQuotients2011 ArithmeticAdaptiveFirstDivisibility2011
open ArithmeticAdaptiveTransport2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
open ArithmeticSignedPairExpressions
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Exact signed representation of the main root, after the proved q>F gap. -/
theorem main_root_rep (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hq : 1≤1+v 0*(p 0:V)) (hF : v 1≤1+v 0*(p 0:V)) :
    let b : V := v 0*(p 0:V)
    let q : V := 1+b
    let U : V := v 7*(q*q)
    let E : V := v 6*v 7
    let k : V := v 9+v 10
    let c : V := v 9+v 7*k
    let a : V := E+v 7
    let H : V := 3+4*a
    let R : V := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)
    Equivalent (pairEval (rootTerm (factors (fun j => (p j:ℤ))).2.1) v)
      (U*(v 6+a*c)+H*(U*v 12+E*q+R+1),H*k) := by
  let eB : Expr (Fin 13) := .mul (.var 0) (.constant (p 0))
  let eQ : Expr (Fin 13) := .add (.constant 1) eB
  let eU : Expr (Fin 13) := .mul (.var 7) (.mul eQ eQ)
  let eE : Expr (Fin 13) := .mul (.var 6) (.var 7)
  let eK : Expr (Fin 13) := .add (.var 9) (.var 10)
  let eC : Expr (Fin 13) := .add (.var 9) (.mul (.var 7) eK)
  let eA : Expr (Fin 13) := .add eE (.var 7)
  let eH : Expr (Fin 13) := .add (.constant 3) (.mul (.constant 4) eA)
  let eR : Expr (Fin 13) := .add
    (.mul (.add (.var 2) (.mul (.sub eQ (.var 1)) eB)) (.sub (.mul eQ eQ) (.constant 1)))
    (.mul (.var 0) (.add (.constant (p 2)) (.mul (.constant (p 3)) eQ)))
  let eD : Expr (Fin 13) := .add
    (.mul eU (.add (.var 6) (.mul eA eC)))
    (.mul eH (.sub (.add (.mul eU (.var 12)) (.mul eE eQ))
      (.sub (.sub eK eR) (.constant 1))))
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let U : V := v 7*(q*q)
  let E : V := v 6*v 7
  let k : V := v 9+v 10
  let c : V := v 9+v 7*k
  let a : V := E+v 7
  let H : V := 3+4*a
  let R : V := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)
  have hB : SignedRep eB v (natural b) := rep_mul_nat (rep_var v 0) (rep_nat v (p 0))
  have hQ : SignedRep eQ v (natural q) := rep_add_nat (rep_one v) hB
  have hU : SignedRep eU v (natural U) := rep_mul_nat (rep_var v 7) (rep_mul_nat hQ hQ)
  have hE : SignedRep eE v (natural E) := rep_mul_nat (rep_var v 6) (rep_var v 7)
  have hK : SignedRep eK v (natural k) := rep_add_nat (rep_var v 9) (rep_var v 10)
  have hC : SignedRep eC v (natural c) := rep_add_nat (rep_var v 9) (rep_mul_nat (rep_var v 7) hK)
  have hA : SignedRep eA v (natural a) := rep_add_nat hE (rep_var v 7)
  have hH : SignedRep eH v (natural H) := rep_add_nat (rep_three v) (rep_mul_nat (rep_four v) hA)
  have hq2 : (1:V)≤q*q := by simpa only [one_mul] using mul_le_mul hq hq (by simp) (by simp)
  have hR : SignedRep eR v (natural R) := rep_add_nat
    (rep_mul_nat (rep_add_nat (rep_var v 2) (rep_mul_nat (rep_tsub hQ (rep_var v 1) hF) hB))
      (rep_tsub (rep_mul_nat hQ hQ) (rep_one v) hq2))
    (rep_mul_nat (rep_var v 0) (rep_add_nat (rep_nat v (p 2)) (rep_mul_nat (rep_nat v (p 3)) hQ)))
  have hneg : SignedRep (.sub (.sub eK eR) (.constant 1)) v (k,R+1) := by
    have h := rep_sub (rep_sub hK hR) (rep_one v)
    simpa only [minus,natural,add_zero,zero_add,Nat.cast_one,add_assoc] using h
  have hshift : SignedRep (.sub (.add (.mul eU (.var 12)) (.mul eE eQ))
      (.sub (.sub eK eR) (.constant 1))) v (U*v 12+E*q+R+1,k) := by
    have h := rep_sub (rep_add_nat (rep_mul_nat hU (rep_var v 12)) (rep_mul_nat hE hQ)) hneg
    simpa only [minus,natural,add_zero,zero_add,add_assoc] using h
  have hD := rep_add (rep_mul_nat hU (rep_add_nat (rep_var v 6) (rep_mul_nat hA hC)))
    (rep_mul hH hshift)
  change SignedRep eD v (U*(v 6+a*c)+H*(U*v 12+E*q+R+1),H*k)
  simpa only [plus,multiply,natural,add_zero,zero_add,mul_zero,zero_mul] using hD

/-- The actual main-root positive part dominates its negative k term. -/
theorem main_parts_positive (U X Y k eta gamma q R : V)
    (hU : 0<U) (hY : 8≤Y) (hk : 0<k) :
    let a := X*Y+Y
    let c := eta+Y*k
    let H := 3+4*a
    H*k < U*(X+a*c)+H*(U*gamma+X*Y*q+R+1) := by
  let a := X*Y+Y
  let c := eta+Y*k
  let H := 3+4*a
  have ha : 1≤a := by
    have hy : (1:V)≤Y := le_trans (by simp : (1:V)≤8) hY
    exact le_trans hy (by dsimp only [a]; simp)
  have hU1 : 1≤U := pos_iff_one_le.mp hU
  have hUY : 8≤U*Y := le_trans hY (le_mul_of_one_le_left (by simp) hU1)
  have hUa : 8*a≤U*a*Y := by
    have h := mul_le_mul_of_nonneg_right hUY (Arithmetic.zero_le a)
    simpa only [mul_assoc,mul_comm,mul_left_comm] using h
  have h4a : (4:V)≤4*a := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ha (by simp : (0:V)≤4)
  have hlt : (3:V)<4*a := lt_of_lt_of_le (by norm_num : (3:V)<4) h4a
  have hH : H<8*a := calc
    H=4*a+3 := by dsimp only [H]; ring
    _<4*a+4*a := by simpa only [add_comm] using add_lt_add_left hlt (4*a)
    _=8*a := by ring
  have hH' : H<U*a*Y := lt_of_lt_of_le hH hUa
  have hk' : H*k<(U*a*Y)*k := mul_lt_mul_of_pos_right hH' hk
  have hc : Y*k≤c := by dsimp only [c]; simp
  have hc' : (U*a)*(Y*k)≤(U*a)*c := mul_le_mul_of_nonneg_left hc (by simp)
  calc
    H*k<(U*a*Y)*k := hk'
    _=(U*a)*(Y*k) := by ring
    _≤(U*a)*c := hc'
    _≤U*(X+a*c) := by
      calc
        (U*a)*c=U*(a*c) := by ring
        _≤U*(X+a*c) := mul_le_mul_of_nonneg_left (by simp) (by simp)
    _≤U*(X+a*c)+H*(U*gamma+X*Y*q+R+1) := by simp

def MainOriented (p : Fin 4 → ℕ) (v : Fin 13 → V) : Prop :=
  let q : V := 1+v 0*(p 0:V)
  let U : V := v 7*(q*q)
  let k : V := v 9+v 10
  let c : V := v 9+v 7*k
  let a : V := v 6*v 7+v 7
  let delta : V := (3+4*a)+a*a
  ∃ main : V, 0<main ∧
    Equivalent (pairEval (rootTerm (factors (fun j => (p j:ℤ))).2.1) v) (natural (U*main)) ∧
    main*main=1+delta*(c*c)

/-- Positive transport and Pell quotients orient the main root. -/
theorem main_oriented_of_facts (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hquotients : Quotients p v) (htransport : TransportPositive p v)
    (hY : ∃ s : V, 0<s ∧ v 7 =
      ((1+v 0*(p 0:V))*((1+v 0*(p 0:V))*(1+v 0*(p 0:V))))*s) :
    MainOriented p v := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let Q : V := q*(q*q)
  let U : V := v 7*(q*q)
  let E : V := v 6*v 7
  let k : V := v 9+v 10
  let c : V := v 9+v 7*k
  let a : V := E+v 7
  let H : V := 3+4*a
  let R : V := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)
  let dp : V := U*(v 6+a*c)+H*(U*v 12+E*q+R+1)
  let dn : V := H*k
  let z := pairEval (rootTerm (factors (fun j => (p j:ℤ))).2.1) v
  have hp := scaled_parameters_positive p v hb hv
  have hq : 1<q := hp.1
  have hq1 : (1:V)≤q := le_of_lt hq
  have hq2 : (2:V)≤q := by simpa only [one_add_one_eq_two] using lt_iff_succ_le.mp hq
  have hU : 0<U := hp.2.2.1
  have hk : 0<k := hp.2.2.2.1
  have hsum : v 1+v 2<q := tsub_pos_iff_lt.mp htransport.2
  have hF : v 1≤q := le_trans (by simp : v 1≤v 1+v 2) (le_of_lt hsum)
  obtain ⟨s,hs,hsY⟩ := hY
  have hQ8 : (8:V)≤Q := calc
    8=2*(2*2) := by norm_num
    _≤q*(q*q) := mul_le_mul hq2 (mul_le_mul hq2 hq2 (by simp) (by simp)) (by simp) (by simp)
  have hY8 : (8:V)≤v 7 := calc
    8≤Q := hQ8
    _≤Q*s := le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hs)
    _=v 7 := hsY.symm
  have hpos : dn<dp := main_parts_positive U (v 6) (v 7) k (v 9) (v 12) q R hU hY8 hk
  obtain ⟨first,main,_,hmainp,_,_,hmain,hnorm⟩ := hquotients
  have hre : Equivalent z (dp,dn) := main_root_rep p v hq1 hF
  have hmag : magnitude z=magnitude (dp,dn) := magnitude_equivalent hre
  have heq : dp=dn+(dp-dn) := by rw [add_comm,tsub_add_cancel_of_le (le_of_lt hpos)]
  have hcan : magnitude (dp,dn)=dp-dn := magnitude_of_add heq
  have hdiff : dp-dn=U*main := hcan.symm.trans (hmag.symm.trans hmain)
  have hpart : Equivalent (dp,dn) (natural (U*main)) := by
    change dp+0=dn+U*main
    simpa only [add_zero,hdiff] using heq
  refine ⟨main,hmainp,equivalent_trans hre hpart,?_⟩
  exact hnorm


/-- An actual adaptive zero orients the main root and constructs its quotient. -/
theorem expressionAt_main_oriented (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (expressionAt (fun j => (p j:ℤ))) v) : MainOriented p v :=
  main_oriented_of_facts p v hb hv (expressionAt_quotients p v hb hv hz)
    (expressionAt_transport_positive p v hb hv hz) (expressionAt_Y_quotient p v hb hv hz)

private theorem beta_positive_nat : 0<CurrentMasks2011.beta := by
  have hr : 1<CurrentMasks2011.radix := by unfold CurrentMasks2011.radix; norm_num
  have hp : 1<CurrentMasks2011.radix^2011 := one_lt_pow₀ hr (by decide)
  unfold CurrentMasks2011.beta
  omega

theorem current_main_oriented (v : Fin 13 → V) (hv : ∀j,0<v j)
    (hz : InternalZero expression v) : MainOriented currentPorts v := by
  have hb : 0<(CurrentMasks2011.beta:V) := by exact_mod_cast beta_positive_nat
  have hp : 0<(currentPorts 0:V) := by simpa only [currentPorts,Matrix.cons_val_zero] using hb
  apply expressionAt_main_oriented currentPorts v hp hv
  rw [currentPorts_cast]
  exact hz

theorem current_natural_main_oriented (v : Fin 13 → V)
    (hz : InternalZero naturalExpression v) : MainOriented currentPorts (fun j => v j+1) :=
  current_main_oriented _
    (fun j => lt_of_le_of_lt (Arithmetic.zero_le (v j)) (lt_add_one _))
    ((internalZero_positiveShift expression v).mp hz)

end DiophantineConsistency.ArithmeticAdaptiveMainOrientation2011
