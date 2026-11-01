import DiophantineConsistency.ArithmeticAdaptiveEarlyIndex2011

/-! Comparison of the actual adaptive first and main Pell indices. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveIndexComparison2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptiveFirstDivisibility2011
open ArithmeticAdaptivePellIndices2011 ArithmeticAdaptiveEarlyIndex2011
open ArithmeticPellRecurrence ArithmeticPellCongruences
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Joint internal induction proves monotonicity in the actual Pell base. -/
theorem base_mono (a b : V) (hab : a≤b) (t : V) :
    xcoord t a≤xcoord t b ∧ ycoord t a≤ycoord t b := by
  have hbase : a+2≤b+2 := _root_.add_le_add hab (le_refl 2)
  have hd : delta a≤delta b := by
    unfold delta
    exact mul_le_mul (_root_.add_le_add hab (le_refl 1))
      (_root_.add_le_add hab (le_refl 3)) (by simp) (by simp)
  induction t using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ t ih =>
    constructor
    · rw [x_succ,x_succ]
      exact add_le_add (mul_le_mul hbase ih.1 (by simp) (by simp))
        (mul_le_mul hd ih.2 (by simp) (by simp))
    · rw [y_succ,y_succ]
      exact add_le_add ih.1 (mul_le_mul hbase ih.2 (by simp) (by simp))

def Comparison (p : Fin 4 → ℕ) (v : Fin 13 → V) : Prop :=
  let q : V := 1+v 0*(p 0:V)
  let M : V := (q*(q*q))*(v 0*(p 0:V))
  let U : V := v 7*(q*q)
  let Q : V := (v 6*v 7)*v 7
  let k : V := v 9+v 10
  let c : V := v 9+v 7*k
  let a : V := v 6*v 7+v 7
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  ∃ first main n m : V, 0<first ∧ 0<main ∧ 13≤n ∧ n<m ∧ 14≤m ∧ 2*R<c ∧
    magnitude (pairEval (rootTerm (factors (fun j => (p j:ℤ))).1) v)=M*first ∧
    Equivalent (pairEval (rootTerm (factors (fun j => (p j:ℤ))).2.1) v) (natural (U*main)) ∧
    xcoord n (2*(Q-1)+1)=first ∧ 2*ycoord n (2*(Q-1)+1)=k ∧
    xcoord m a=main ∧ ycoord m a=c ∧ (2*n)%(q^4)=R+1

theorem comparison_of_facts (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hv : ∀j,0<v j) (hY : 2≤v 7) (hi : Indices p v) (he : EarlyIndex p v) : Comparison p v := by
  let E : V := v 6*v 7
  let Y : V := v 7
  let Q : V := E*Y
  let B : V := 2*(Q-1)+1
  let k : V := v 9+v 10
  let c : V := v 9+Y*k
  let a : V := E+Y
  let q : V := 1+v 0*(p 0:V)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  have hE : 0<E := mul_pos (hv 6) (hv 7)
  have hk : 0<k := add_pos (hv 9) (hv 10)
  have hQ1 : Q-1+1=Q := tsub_add_cancel_of_le (pos_iff_one_le.mp (mul_pos hE (hv 7)))
  have hB : B+2=2*Q+1 := by
    dsimp [B]
    calc
      2*(Q-1)+1+2=2*(Q-1+1)+1 := by ring
      _=2*Q+1 := by rw [hQ1]
  have hab : a≤B := by
    have hEsub : E-1+1=E := tsub_add_cancel_of_le (pos_iff_one_le.mp hE)
    have hYsub : Y-2+2=Y := tsub_add_cancel_of_le hY
    have heq : a+2+(E-1)*(2*(Y-2)+3)+(Y-2)=B+2 := by
      rw [hB]
      calc
        a+2+(E-1)*(2*(Y-2)+3)+(Y-2)=
          (E-1+1)+(Y-2+2)+2+(E-1)*(2*(Y-2)+3)+(Y-2) := by rw [hEsub,hYsub]
        _=2*((E-1+1)*(Y-2+2))+1 := by ring
        _=2*Q+1 := by rw [hEsub,hYsub]
    have heq' : a+2≤B+2 := by rw [←heq]; simp
    exact (add_le_add_iff_right (2:V)).mp heq'
  obtain ⟨first,n,hfirst,hn13,_,hroot,hnx,hny,hnmod,_,hRk⟩ := he
  obtain ⟨_,main,_,m,_,hmain,_,_,_,_,_,horient,_,_,hmx,hmy⟩ := hi
  change 2*ycoord n B=k at hny
  change ycoord m a=c at hmy
  have hkc : k<c := calc
    k≤k*Y := le_mul_of_one_le_right (by simp) (le_trans (by simp : (1:V)≤2) hY)
    _<k*Y+v 9 := lt_add_of_pos_right _ (hv 9)
    _=c := by dsimp [c]; ring
  have hnm : n<m := by
    by_contra hn
    have hm : m≤n := le_of_not_gt hn
    have hc : c≤k := calc
      c=ycoord m a := hmy.symm
      _≤ycoord n a := (y_strictMono a).monotone hm
      _≤ycoord n B := (base_mono a B hab n).2
      _≤2*ycoord n B := le_mul_of_one_le_left (by simp) (by simp)
      _=k := hny
    exact (not_le_of_gt hkc) hc
  have hm14 : 14≤m := by
    have h := le_trans (_root_.add_le_add hn13 (le_refl (1:V))) (lt_iff_succ_le.mp hnm)
    simpa only [show (13:V)+1=14 by ring] using h
  have hhalf : 2*R<c := calc
    2*R<2*(R+1) := mul_lt_mul_of_pos_left (lt_add_one R) (by simp)
    _≤2*k := mul_le_mul_of_nonneg_left hRk (by simp)
    _≤k*Y := by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hY (Arithmetic.zero_le k)
    _<k*Y+v 9 := lt_add_of_pos_right _ (hv 9)
    _=c := by dsimp [c]; ring
  exact ⟨first,main,n,m,hfirst,hmain,hn13,hnm,hm14,hhalf,hroot,horient,hnx,hny,hmx,hmy,hnmod⟩

/-- A positive q³ quotient gives Y ≥ 2 when q > 1. -/
theorem two_le_of_positive_cube_quotient {q y : V} (hq : 1<q)
    (hY : ∃ s : V, 0<s ∧ y=q*(q*q)*s) : 2≤y := by
  have hq2 : 2≤q := by simpa only [one_add_one_eq_two] using lt_iff_succ_le.mp hq
  have hq1 : 1≤q := le_of_lt hq
  have hq3 : 2≤q^3 := calc
    2≤q := hq2
    _≤q*q := le_mul_of_one_le_right (by simp) hq1
    _≤q*q*q := le_mul_of_one_le_right (by simp) hq1
    _=q^3 := by ring
  obtain ⟨s,hs,hsY⟩ := hY
  calc
    2≤q^3 := hq3
    _≤q^3*s := le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hs)
    _=y := by simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using hsY.symm

theorem expressionAt_comparison (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (expressionAt (fun j => (p j:ℤ))) v) : Comparison p v := by
  have hY : 2≤v 7 := two_le_of_positive_cube_quotient
    (scaled_parameters_positive p v hb hv).1 (expressionAt_Y_quotient p v hb hv hz)
  exact comparison_of_facts p v hv hY (expressionAt_indices p v hb hv hz)
    (expressionAt_early_index p v hb hl hh hv hz)

theorem current_comparison (v : Fin 13 → V) (hv : ∀j,0<v j)
    (hz : InternalZero expression v) : Comparison currentPorts v := by
  have hY : 2≤v 7 := two_le_of_positive_cube_quotient
    (current_parameters_positive v hv).1 (current_Y_quotient v hv hz)
  exact comparison_of_facts currentPorts v hv hY (current_indices v hv hz) (current_early_index v hv hz)

theorem current_natural_comparison (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    Comparison currentPorts (fun j => v j+1) :=
  current_comparison _ (fun j => lt_of_le_of_lt (Arithmetic.zero_le (v j)) (lt_add_one _))
    ((internalZero_positiveShift expression v).mp hz)
end DiophantineConsistency.ArithmeticAdaptiveIndexComparison2011
