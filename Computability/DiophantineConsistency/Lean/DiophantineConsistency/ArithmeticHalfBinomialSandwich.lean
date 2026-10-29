import DiophantineConsistency.ArithmeticPow
import DiophantineConsistency.ArithmeticPellPowerRecovery

/-! The integer Pell sandwich for the half-binomial ratio, at arbitrary internal
`X Y r`, with no real numbers. Put `a = Y*(X+1)`, `B = 2*(X*Y*Y-1)+1`
(so the Pell base is `B+2 = 2XY²+1`), `c = ycoord (2r+1) a`,
`k = 2*ycoord (r+1) B`, `N = power (X+1) (2r)`, `D = power X r`. Then

* `k*N < 2*c*D` unconditionally (for `X,Y,r ≥ 1`);
* `2*c*D < k*(N+D)` once `72r < X+1` and `N < 2*(Y+1)*D`.

The second hypothesis is the form both clients can supply: the soundness client
derives it from `c < k*(Y+1)` and the lower bound, the construction client from
the binomial floor. No `η, ζ > 0` interval hypothesis is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticHalfBinomialSandwich
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPow ArithmeticPellRecurrence ArithmeticPellPowerRecovery
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem y_one (b : V) : ycoord 1 b=1 := by simpa using y_succ (0:V) b

/-! Fixed graphs for the two growth invariants (base parameter held fixed). -/
private def lowerDef : 𝚺₁.Semisentence 2 := .mkSigma
  “t b. ∃ p y, !powerDef p (2*b+3) t ∧ !yDef y (t+1) b ∧ p≤y”
private instance lower_defined :
    𝚺₁-Relation[V] (fun t b : V => power (2*b+3) t≤ycoord (t+1) b) via lowerDef :=
  .mk fun e => by simp [lowerDef,Semiformula.eval_substs]
private instance lower_definable :
    𝚺₁-Relation[V] (fun t b : V => power (2*b+3) t≤ycoord (t+1) b) :=
  lower_defined.to_definable

private def upperDef : 𝚺₁.Semisentence 2 := .mkSigma
  “t b. ∃ p y, !powerDef p (2*(b+2)) t ∧ !yDef y (t+1) b ∧ y≤p”
private instance upper_defined :
    𝚺₁-Relation[V] (fun t b : V => ycoord (t+1) b≤power (2*(b+2)) t) via upperDef :=
  .mk fun e => by simp [upperDef,Semiformula.eval_substs]
private instance upper_definable :
    𝚺₁-Relation[V] (fun t b : V => ycoord (t+1) b≤power (2*(b+2)) t) :=
  upper_defined.to_definable

/-- Pell growth from below: `(2b+3)^t ≤ y_{t+1}(b)`. -/
theorem power_le_ycoord (b t : V) : power (2*b+3) t≤ycoord (t+1) b := by
  induction t using ISigma1.sigma1_succ_induction
  · exact HierarchySymbol.Definable.comp₂
      (P := fun t b : V => power (2*b+3) t≤ycoord (t+1) b)
      (f := fun v => v 0) (g := fun _ => b) (by simp) (by simp)
  case zero => simp [y_one]
  case succ t ih =>
    rw [power_succ]
    calc
      (2*b+3)*power (2*b+3) t≤(2*b+3)*ycoord (t+1) b := mul_le_mul_of_nonneg_left ih (by simp)
      _≤ycoord (t+1+1) b := (y_lower b (t+1)).le

/-- Pell growth from above: `y_{t+1}(b) ≤ (2(b+2))^t`. -/
theorem ycoord_le_power (b t : V) : ycoord (t+1) b≤power (2*(b+2)) t := by
  induction t using ISigma1.sigma1_succ_induction
  · exact HierarchySymbol.Definable.comp₂
      (P := fun t b : V => ycoord (t+1) b≤power (2*(b+2)) t)
      (f := fun v => v 0) (g := fun _ => b) (by simp) (by simp)
  case zero => simp [y_one]
  case succ t ih =>
    rw [power_succ]
    calc
      ycoord (t+1+1) b≤2*(b+2)*ycoord (t+1) b := y_upper b (t+1) (by simp)
      _≤2*(b+2)*power (2*(b+2)) t := mul_le_mul_of_nonneg_left ih (by simp)

/-- The base identity `B+2 = 2XY²+1`, justified before any subtraction rewrite. -/
theorem base_eq (X Y : V) (hX : 1≤X) (hY : 1≤Y) : 2*(X*Y*Y-1)+1+2=2*X*Y*Y+1 := by
  have h1 : 1≤X*Y*Y := one_le_mul (one_le_mul hX hY) hY
  have he : X*Y*Y-1+1=X*Y*Y := tsub_add_cancel_of_le h1
  calc
    2*(X*Y*Y-1)+1+2=2*(X*Y*Y-1+1)+1 := by ring
    _=2*X*Y*Y+1 := by rw [he]; ring

theorem base_eq' (X Y : V) (hX : 1≤X) (hY : 1≤Y) : 2*(2*(X*Y*Y-1)+1)+3=4*X*Y*Y+1 := by
  apply add_right_cancel (b := (1:V))
  calc
    2*(2*(X*Y*Y-1)+1)+3+1=2*(2*(X*Y*Y-1)+1+2) := by ring
    _=2*(2*X*Y*Y+1) := by rw [base_eq X Y hX hY]
    _=(4*X*Y*Y+1)+1 := by ring

/-- Finite coefficient comparison for the lower estimate. -/
theorem lower_coefficient (X Y : V) (hX : 1≤X) (hY : 1≤Y) :
    2*(2*X*Y*Y+1)*((X+1)*(X+1))<(2*(Y*(X+1))+3)*(2*(Y*(X+1))+3)*X := by
  have hXY : X*X+X≤X*Y*(X+1) := by
    have := mul_le_mul_of_nonneg_left hY (by simp : (0:V)≤X*(X+1))
    calc
      X*X+X=X*(X+1)*1 := by ring
      _≤X*(X+1)*Y := this
      _=X*Y*(X+1) := by ring
  have h12 : 12*(X*X+X)≤12*(X*Y*(X+1)) := mul_le_mul_of_nonneg_left hXY (by simp)
  have h9 : (9:V)≤9*X := by
    simpa using mul_le_mul_of_nonneg_left hX (by simp : (0:V)≤9)
  have hsmall : 2*(X*X)+4*X+2<12*(X*Y*(X+1))+9*X := calc
    2*(X*X)+4*X+2<2*(X*X)+4*X+2+(10*(X*X)+8*X+7) := lt_add_of_pos_right _ (by
      exact lt_of_lt_of_le (by simp) (le_add_of_nonneg_left (by simp)))
    _=12*(X*X+X)+9 := by ring
    _≤12*(X*Y*(X+1))+9*X := add_le_add h12 h9
  calc
    2*(2*X*Y*Y+1)*((X+1)*(X+1))=4*X*(Y*Y*((X+1)*(X+1)))+(2*(X*X)+4*X+2) := by ring
    _<4*X*(Y*Y*((X+1)*(X+1)))+(12*(X*Y*(X+1))+9*X) := add_lt_add_of_le_of_lt le_rfl hsmall
    _=(2*(Y*(X+1))+3)*(2*(Y*(X+1))+3)*X := by ring

/-- Finite coefficient comparison for the upper estimate (`upper_key`). -/
theorem upper_coefficient (X Y : V) (hX : 1≤X) (hY : 1≤Y) :
    (2*(Y*(X+1)+2))*(2*(Y*(X+1)+2))*X*(Y*(X+1))≤
      (4*X*Y*Y+1)*((X+1)*(X+1))*(Y*(X+1)+9) := by
  have hX1 : 1≤X+1 := le_trans hX (le_add_of_nonneg_right (by simp))
  have ha1 : 1≤Y*(X+1) := one_le_mul hY hX1
  have hsq : Y*(X+1)≤(Y*(X+1))*(Y*(X+1)) :=
    le_mul_of_one_le_right (by simp) ha1
  have h16 : 16*X*(Y*(X+1))≤20*X*((Y*(X+1))*(Y*(X+1))) := by
    have h1 : 16*X*(Y*(X+1))≤16*X*((Y*(X+1))*(Y*(X+1))) :=
      mul_le_mul_of_nonneg_left hsq (by simp)
    have h2 : 16*X*((Y*(X+1))*(Y*(X+1)))≤20*X*((Y*(X+1))*(Y*(X+1))) := by
      have : (16:V)≤20 := by norm_num
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this (by simp)) (by simp)
    exact le_trans h1 h2
  calc
    (2*(Y*(X+1)+2))*(2*(Y*(X+1)+2))*X*(Y*(X+1))=
        4*X*((Y*(X+1))*(Y*(X+1))*(Y*(X+1)))+16*X*((Y*(X+1))*(Y*(X+1)))+16*X*(Y*(X+1)) := by
      ring
    _≤4*X*((Y*(X+1))*(Y*(X+1))*(Y*(X+1)))+16*X*((Y*(X+1))*(Y*(X+1)))+
        20*X*((Y*(X+1))*(Y*(X+1))) := add_le_add le_rfl h16
    _≤4*X*((Y*(X+1))*(Y*(X+1))*(Y*(X+1)))+16*X*((Y*(X+1))*(Y*(X+1)))+
        20*X*((Y*(X+1))*(Y*(X+1)))+(X+1)*(X+1)*(Y*(X+1)+9) := le_add_of_nonneg_right (by simp)
    _=(4*X*Y*Y+1)*((X+1)*(X+1))*(Y*(X+1)+9) := by ring


/-- The lower half of the sandwich, unconditional in the interval data. -/
theorem sandwich_lower (X Y r : V) (hX : 1≤X) (hY : 1≤Y) (hr : 1≤r) :
    2*ycoord (r+1) (2*(X*Y*Y-1)+1)*power (X+1) (2*r)<
      2*ycoord (2*r+1) (Y*(X+1))*power X r := by
  have hK : ycoord (r+1) (2*(X*Y*Y-1)+1)≤power (2*(2*X*Y*Y+1)) r := by
    have := ycoord_le_power (2*(X*Y*Y-1)+1) r
    rwa [show 2*(X*Y*Y-1)+1+2=2*X*Y*Y+1 from base_eq X Y hX hY] at this
  have hc : power ((2*(Y*(X+1))+3)*(2*(Y*(X+1))+3)) r≤ycoord (2*r+1) (Y*(X+1)) := by
    rw [power_mul_base,←power_add,show 2*r+1=r+r+1 by ring]
    exact power_le_ycoord (Y*(X+1)) (r+r)
  have hN : power (X+1) (2*r)=power ((X+1)*(X+1)) r := by
    rw [power_mul_base,←power_add,two_mul]
  have hr0 : 0<r := lt_of_lt_of_le (by simp) hr
  have hstrict := power_strict_base _ _ r (lower_coefficient X Y hX hY) hr0
  rw [power_mul_base (2*(2*X*Y*Y+1)) ((X+1)*(X+1)) r,
    power_mul_base ((2*(Y*(X+1))+3)*(2*(Y*(X+1))+3)) X r] at hstrict
  calc
    2*ycoord (r+1) (2*(X*Y*Y-1)+1)*power (X+1) (2*r)≤2*power (2*(2*X*Y*Y+1)) r*power ((X+1)*(X+1)) r := by
      rw [hN]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK (by simp)) (by simp)
    _=2*(power (2*(2*X*Y*Y+1)) r*power ((X+1)*(X+1)) r) := by ring
    _<2*(power ((2*(Y*(X+1))+3)*(2*(Y*(X+1))+3)) r*power X r) := mul_lt_mul_of_pos_left hstrict (by simp)
    _≤2*(ycoord (2*r+1) (Y*(X+1))*power X r) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc (by simp)) (by simp)
    _=2*ycoord (2*r+1) (Y*(X+1))*power X r := by ring

/-- The upper half of the sandwich. Its only interval input is the crude bound
`N < 2*(Y+1)*D`; there is no circular use of the sharp upper estimate. -/
theorem sandwich_upper (X Y r : V) (hX : 1≤X) (hY : 1≤Y) (hr : 1≤r) (h72 : 72*r<X+1)
    (hN : power (X+1) (2*r)<2*(Y+1)*power X r) :
    2*ycoord (2*r+1) (Y*(X+1))*power X r<
      2*ycoord (r+1) (2*(X*Y*Y-1)+1)*(power (X+1) (2*r)+power X r) := by
  have hupper := upper_coefficient X Y hX hY
  have hQ := base_eq' X Y hX hY
  have hKlow := power_le_ycoord (2*(X*Y*Y-1)+1) r
  have hcup := ycoord_le_power (Y*(X+1)) (2*r)
  have hKpos : 0<ycoord (r+1) (2*(X*Y*Y-1)+1) :=
    lt_of_lt_of_le (by simp) (time_le_y (r+1) _)
  rw [hQ] at hKlow
  obtain ⟨a,ha⟩ : ∃ a, Y*(X+1)=a := ⟨_,rfl⟩
  obtain ⟨K,hK⟩ : ∃ K, ycoord (r+1) (2*(X*Y*Y-1)+1)=K := ⟨_,rfl⟩
  obtain ⟨N,hNd⟩ : ∃ N, power (X+1) (2*r)=N := ⟨_,rfl⟩
  obtain ⟨D,hDd⟩ : ∃ D, power X r=D := ⟨_,rfl⟩
  rw [ha] at hupper hcup ⊢
  rw [hK] at hKlow hKpos ⊢
  rw [hNd,hDd] at hN ⊢
  obtain ⟨c,hc⟩ : ∃ c, ycoord (2*r+1) a=c := ⟨_,rfl⟩
  rw [hc] at hcup ⊢
  have hr0 : 0<r := lt_of_lt_of_le (by simp) hr
  have ha1 : 1≤a := by
    rw [←ha]; exact one_le_mul hY (le_trans hX (le_add_of_nonneg_right (by simp)))
  have hapos : 0<a := lt_of_lt_of_le (by simp) ha1
  have hDpos : 0<D := by rw [←hDd]; exact power_pos X r (lt_of_lt_of_le (by simp) hX)
  -- step 1: growth bounds as powers at the exponent r
  have hcD : c*D≤power ((2*(a+2))*(2*(a+2))*X) r := by
    rw [power_mul_base,power_mul_base,←power_add,←two_mul,hDd]
    exact mul_le_mul_of_nonneg_right hcup (by simp)
  have hKN : power ((4*X*Y*Y+1)*((X+1)*(X+1))) r≤K*N := by
    rw [power_mul_base,power_mul_base (X+1) (X+1),←power_add,←two_mul,hNd]
    exact mul_le_mul_of_nonneg_right hKlow (by simp)
  -- step 2: raise upper_key and apply the integer perturbation bound
  have hraise := power_mono_base _ _ r hupper
  rw [power_mul_base _ a,power_mul_base _ (a+9)] at hraise
  have h18 : 2*r*9≤a := by
    have h1 : 2*r*9≤72*r := by
      have : 2*r*9+54*r=72*r := by ring
      rw [←this]; exact le_add_of_nonneg_right (by simp)
    have h2 : X+1≤a := by
      rw [←ha]; calc X+1=1*(X+1) := (one_mul _).symm
        _≤Y*(X+1) := mul_le_mul_of_nonneg_right hY (by simp)
    exact le_trans h1 (le_trans h72.le h2)
  have hpert := perturbation a 9 r h18
  have hapow : 0<power a r := power_pos a r hapos
  have hcancel : a*power ((2*(a+2))*(2*(a+2))*X) r≤
      power ((4*X*Y*Y+1)*((X+1)*(X+1))) r*(a+2*r*9) := by
    apply le_of_mul_le_mul_right _ hapow
    calc
      a*power ((2*(a+2))*(2*(a+2))*X) r*power a r=
          a*(power ((2*(a+2))*(2*(a+2))*X) r*power a r) := by ring
      _≤a*(power ((4*X*Y*Y+1)*((X+1)*(X+1))) r*power (a+9) r) :=
          mul_le_mul_of_nonneg_left hraise (by simp)
      _=power ((4*X*Y*Y+1)*((X+1)*(X+1))) r*(a*power (a+9) r) := by ring
      _≤power ((4*X*Y*Y+1)*((X+1)*(X+1))) r*((a+2*r*9)*power a r) :=
          mul_le_mul_of_nonneg_left hpert (by simp)
      _=power ((4*X*Y*Y+1)*((X+1)*(X+1))) r*(a+2*r*9)*power a r := by ring
  -- step 3: 2*a*c*D ≤ k*N*(a+18r)
  have hmain : a*(2*c*D)≤2*K*N*(a+2*r*9) := calc
    a*(2*c*D)=2*(a*(c*D)) := by ring
    _≤2*(a*power ((2*(a+2))*(2*(a+2))*X) r) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcD (by simp)) (by simp)
    _≤2*(power ((4*X*Y*Y+1)*((X+1)*(X+1))) r*(a+2*r*9)) :=
        mul_le_mul_of_nonneg_left hcancel (by simp)
    _≤2*(K*N*(a+2*r*9)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKN (by simp)) (by simp)
    _=2*K*N*(a+2*r*9) := by ring
  -- step 4: the crude bound gives 18rN < aD
  have hcrude : 2*r*9*N<a*D := by
    have hYY : Y+1≤2*Y := by
      calc Y+1≤Y+Y := add_le_add le_rfl hY
        _=2*Y := (two_mul Y).symm
    have hra : 72*r*Y<a := by
      rw [←ha]
      have := mul_lt_mul_of_pos_right h72 (lt_of_lt_of_le (by simp) hY)
      rwa [mul_comm (X+1) Y] at this
    calc
      2*r*9*N<2*r*9*(2*(Y+1)*D) := mul_lt_mul_of_pos_left hN (by
        exact mul_pos (mul_pos (by simp) hr0) (by simp))
      _=36*r*((Y+1)*D) := by ring
      _≤36*r*((2*Y)*D) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hYY (by simp)) (by simp)
      _=(72*r*Y)*D := by ring
      _<a*D := mul_lt_mul_of_pos_right hra hDpos
  have hfinal : a*(2*c*D)<a*(2*K*(N+D)) := calc
    a*(2*c*D)≤2*K*N*(a+2*r*9) := hmain
    _=a*(2*K*N)+2*K*(2*r*9*N) := by ring
    _<a*(2*K*N)+2*K*(a*D) := add_lt_add_of_le_of_lt le_rfl
        (mul_lt_mul_of_pos_left hcrude (mul_pos (show (0:V)<2 by simp) hKpos))
    _=a*(2*K*(N+D)) := by ring
  exact lt_of_mul_lt_mul_left hfinal (by simp)

/-- The full sandwich in the form the soundness client uses: the interval
`c = k*Y+η`, `k = η+ζ`, `ζ > 0` supplies the crude bound. -/
theorem sandwich_of_interval (X Y r eta zeta : V) (hX : 1≤X) (hY : 1≤Y) (hr : 1≤r)
    (h72 : 72*r<X+1)
    (hck : ycoord (2*r+1) (Y*(X+1))=2*ycoord (r+1) (2*(X*Y*Y-1)+1)*Y+eta)
    (hk : 2*ycoord (r+1) (2*(X*Y*Y-1)+1)=eta+zeta) (hzeta : 0<zeta) :
    2*ycoord (r+1) (2*(X*Y*Y-1)+1)*power (X+1) (2*r)<
        2*ycoord (2*r+1) (Y*(X+1))*power X r ∧
      2*ycoord (2*r+1) (Y*(X+1))*power X r<
        2*ycoord (r+1) (2*(X*Y*Y-1)+1)*(power (X+1) (2*r)+power X r) := by
  have hlow := sandwich_lower X Y r hX hY hr
  refine ⟨hlow,sandwich_upper X Y r hX hY hr h72 ?_⟩
  obtain ⟨k,hkd⟩ : ∃ k, 2*ycoord (r+1) (2*(X*Y*Y-1)+1)=k := ⟨_,rfl⟩
  obtain ⟨c,hcd⟩ : ∃ c, ycoord (2*r+1) (Y*(X+1))=c := ⟨_,rfl⟩
  rw [hkd] at hck hk hlow
  rw [hcd] at hck hlow
  have hkpos : 0<k := by rw [hk]; exact lt_of_lt_of_le hzeta (le_add_of_nonneg_left (by simp))
  have hcY : c<k*(Y+1) := by
    rw [hck,mul_add,mul_one]
    exact add_lt_add_of_le_of_lt le_rfl (by rw [hk]; exact lt_add_of_pos_right eta hzeta)
  have hD : 0≤power X r := by simp
  have : k*power (X+1) (2*r)<k*(2*(Y+1)*power X r) := calc
    k*power (X+1) (2*r)<2*c*power X r := hlow
    _≤2*(k*(Y+1))*power X r :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcY.le (by simp)) hD
    _=k*(2*(Y+1)*power X r) := by ring
  exact lt_of_mul_lt_mul_left this hkpos.le

end DiophantineConsistency.ArithmeticHalfBinomialSandwich
