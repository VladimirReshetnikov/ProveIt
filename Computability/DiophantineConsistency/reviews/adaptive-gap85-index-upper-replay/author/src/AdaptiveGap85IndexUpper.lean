import DiophantineConsistency.AdaptiveGap85CurrentIndices
import DiophantineConsistency.ArithmeticPellPowerRecovery
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85IndexUpper
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellCongruences ArithmeticPellPowerRecovery
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveScaledNorms2011 AdaptiveGap85Literal
open AdaptiveGap85CurrentIndices
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private def comparisonDef : 𝚺₁.Semisentence 3 := .mkSigma
  “r a b. ∃ u v, !yDef u (r+1) b ∧ !yDef v (2*(r+1)) a ∧ (2*(a+2))*u≤v”

private instance comparison_defined : 𝚺₁-Relation₃[V]
    (fun r a b : V => (2*(a+2))*ycoord (r+1) b≤ycoord (2*(r+1)) a)
    via comparisonDef := .mk fun e => by
  simp [comparisonDef,Semiformula.eval_substs]

private instance comparison_definable : 𝚺₁-Relation₃[V]
    (fun r a b : V => (2*(a+2))*ycoord (r+1) b≤ycoord (2*(r+1)) a) :=
  comparison_defined.to_definable

theorem comparison (a b : V)
    (hsep : 2*(b+2)≤(2*a+3)*(2*a+3)) (r : V) :
    (2*(a+2))*ycoord (r+1) b≤ycoord (2*(r+1)) a := by
  induction r using ISigma1.sigma1_succ_induction
  · exact HierarchySymbol.Definable.comp₃
      (P := fun r a b : V => (2*(a+2))*ycoord (r+1) b≤ycoord (2*(r+1)) a)
      (f₁ := fun v => v 0) (f₂ := fun _ => a) (f₃ := fun _ => b)
      (by simp) (by simp) (by simp)
  case zero =>
    have hy1 : ycoord 1 b=1 := by simpa using y_succ (0:V) b
    have hy2 : ycoord 2 a=2*(a+2) := by
      have hy : ycoord 1 a=1 := by simpa using y_succ (0:V) a
      have hx : xcoord 1 a=a+2 := by simpa using x_succ (0:V) a
      have h := y_succ (1:V) a
      rw [hy,hx] at h
      simpa only [one_add_one_eq_two] using h.trans (by ring)
    simp only [zero_add, mul_one,hy1,hy2]
    exact le_refl _
  case succ r ih =>
    have hlo : (2*a+3)*(2*a+3)*ycoord (2*(r+1)) a < ycoord (2*((r+1)+1)) a := by
      calc
        _ = (2*a+3)*((2*a+3)*ycoord (2*(r+1)) a) := by ring
        _ < (2*a+3)*ycoord (2*(r+1)+1) a := mul_lt_mul_of_pos_left (y_lower a (2*(r+1))) (by simp)
        _ < ycoord (2*(r+1)+1+1) a := y_lower a (2*(r+1)+1)
        _ = _ := by congr 1; ring
    calc
      (2*(a+2))*ycoord ((r+1)+1) b ≤ (2*(a+2))*(2*(b+2)*ycoord (r+1) b) :=
        mul_le_mul_of_nonneg_left (y_upper b (r+1) (by simp)) (by simp)
      _ = 2*(b+2)*((2*(a+2))*ycoord (r+1) b) := by ring
      _ ≤ 2*(b+2)*ycoord (2*(r+1)) a := mul_le_mul_of_nonneg_left ih (by simp)
      _ ≤ ((2*a+3)*(2*a+3))*ycoord (2*(r+1)) a := mul_le_mul_of_nonneg_right hsep (by simp)
      _ ≤ ycoord (2*((r+1)+1)) a := le_of_lt hlo

theorem separation (X Y : V) (hX : 1≤X) (hY : 1≤Y) :
    2*(2*(X*Y*Y-1)+1+2)≤(2*(Y*(X+1))+3)*(2*(Y*(X+1))+3) := by
  have hQ : 1≤X*Y*Y := one_le_mul (one_le_mul hX hY) hY
  have hQe : X*Y*Y-1+1=X*Y*Y := tsub_add_cancel_of_le hQ
  have hxx : X≤(X+1)*(X+1) := calc
    X≤X+1 := by simp
    _≤(X+1)*(X+1) := le_mul_of_one_le_left (by simp) (by simp)
  have hmul : 4*(Y*Y)*X≤4*(Y*Y)*((X+1)*(X+1)) := mul_le_mul_of_nonneg_left hxx (by simp)
  have hrest : (2:V)≤12*Y*(X+1)+9 := le_trans (by norm_num : (2:V)≤9) (by simp)
  calc
    _ = 4*(Y*Y)*X+2 := by
      calc
        2*(2*(X*Y*Y-1)+1+2)=4*(X*Y*Y-1+1)+2 := by ring
        _=4*(Y*Y)*X+2 := by rw [hQe]; ring
    _ ≤ 4*(Y*Y)*((X+1)*(X+1))+(12*Y*(X+1)+9) := add_le_add hmul hrest
    _ = _ := by ring

theorem index_lt_double (X Y eta zeta n m : V) (hX : 1≤X) (hY : 1≤Y)
    (hn : 1≤n) (hz : 0<zeta)
    (hfirst : 2*ycoord n (2*(X*Y*Y-1)+1)=eta+zeta)
    (hmain : ycoord m (Y*(X+1))=eta+Y*(eta+zeta)) : m<2*n := by
  let a := Y*(X+1)
  let b := 2*(X*Y*Y-1)+1
  have hsep : 2*(b+2)≤(2*a+3)*(2*a+3) := separation X Y hX hY
  have ha : Y≤a := by dsimp [a]; exact le_mul_of_one_le_right (by simp) (by simp)
  have hcoef : 2*(Y+1)≤2*(a+2) := Arithmetic.mul_le_mul_left (a:=(2:V))
    (add_le_add ha (show (1:V)≤2 by simp))
  have hfirst' : 2*ycoord n b=eta+zeta := hfirst
  have hmain' : ycoord m a=eta+Y*(eta+zeta) := hmain
  have hcsmall : ycoord m a < (2*(a+2))*ycoord n b := by
    have heta : eta < 2*ycoord n b := by rw [hfirst']; exact lt_add_of_pos_right eta hz
    calc
      ycoord m a = Y*(2*ycoord n b)+eta := by rw [hmain',hfirst']; ring
      _ < Y*(2*ycoord n b)+2*ycoord n b := add_lt_add_of_le_of_lt (le_refl _) heta
      _ = (2*(Y+1))*ycoord n b := by ring
      _ ≤ (2*(a+2))*ycoord n b := mul_le_mul_of_nonneg_right hcoef (by simp)
  rcases zero_or_succ n with he|⟨r,he⟩
  · rw [he] at hn
    exact False.elim ((not_le_of_gt (by simp : (0:V)<1)) hn)
  · rw [he] at hcsmall ⊢
    have hcompare := comparison a b hsep r
    by_contra hm
    have hle : 2*(r+1)≤m := le_of_not_gt hm
    have hmono := (y_strictMono a).monotone hle
    exact (not_le_of_gt hcsmall) (le_trans hcompare hmono)

/-- An actual positive zero at the literal current ports has first and main
indices in the strict window n < m < 2n. This is necessary, not sufficient. -/
theorem current_zero_index_window (v : Fin 13 → V)
    (hv : ∀ j,0<v j)
    (hz : InternalZero (expressionAt85 (fun j => (currentPorts j:ℤ))) v) :
    let Q : V := (v 6*v 7)*v 7
    let k : V := v 9+v 10
    let c : V := v 9+v 7*k
    let a : V := v 6*v 7+v 7
    ∃ first main n m : V, 3≤n ∧ 5≤m ∧ n<m ∧ m<2*n ∧
      xcoord n (2*(Q-1)+1)=first ∧ 2*ycoord n (2*(Q-1)+1)=k ∧
      xcoord m a=main ∧ ycoord m a=c := by
  obtain ⟨first,main,n,m,hn,hm,hnm,hnx,hny,hmx,hmy⟩ :=
    current_zero_index_bounds v hv hz
  have hn1 : 1≤n := le_trans (by norm_num : (1:V)≤3) hn
  have hm2 : m<2*n := by
    apply index_lt_double (v 6) (v 7) (v 9) (v 10) n m
      (pos_iff_one_le.mp (hv 6)) (pos_iff_one_le.mp (hv 7)) hn1 (hv 10)
    · exact hny
    · have ha : v 7*(v 6+1)=v 6*v 7+v 7 := by ring
      rw [ha]
      exact hmy
  exact ⟨first,main,n,m,hn,hm,hnm,hm2,hnx,hny,hmx,hmy⟩
end DiophantineConsistency.AdaptiveGap85IndexUpper
