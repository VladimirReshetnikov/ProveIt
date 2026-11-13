import DiophantineConsistency.ArithmeticHalfBinomial

/-! # The sharpened half-binomial interval: `η > 0`

centered18 §4 in the form the 138 soundness needs. Put `X = 2^(2r+1)`, `a = Y(X+1)`,
`bF = 2(XY² − 1) + 1`, `c = ψ_a(2r+1)`, `K = ψ_bF(r+1)`, `k = 2K`, `N = (X+1)^(2r)`, `D = X^r`.

* `sandwich_upper_half` halves the slack of `ArithmeticHalfBinomialSandwich.sandwich_upper`:
  `2cD < K(2N + D)`, i.e. `c/k < N/(2D) + 1/4` (needs `144 r < X + 1`).
* `ArithmeticBinomExpansion.central_split`: `N = M D + v` with `M = binom(2r,r) + Xw` even and
  `Xv ≤ 2^(2r) D`, i.e. `v ≤ D/2`, so `N/(2D) ∈ [M/2, M/2 + 1/4]`.
* With the lower half `kN < 2cD`, `c/k ∈ (M/2, M/2 + 1/2)`. The centered interval
  `|c/k − Y| < 1/2` then gives `Y ≤ M/2 < c/k`, i.e. `η = c − kY > 0` (`eta_pos`).

The route doc's `Y = Y0` is not needed in this form; only `Y ≤ M/2` is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.P138HalfBinomial
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPow ArithmeticPellRecurrence ArithmeticPellPowerRecovery ArithmeticHalfBinomialSandwich
  ArithmeticBinomExpansion ArithmeticBinomLegendre ArithmeticHalfBinomial

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **The sharpened upper half**: `2cD < K(2N + D)`. -/
theorem sandwich_upper_half (X Y r : V) (hX : 1≤X) (hY : 1≤Y) (hr : 1≤r) (h144 : 144*r<X+1)
    (hN : power (X+1) (2*r)<2*(Y+1)*power X r) :
    2*ycoord (2*r+1) (Y*(X+1))*power X r<
      ycoord (r+1) (2*(X*Y*Y-1)+1)*(2*power (X+1) (2*r)+power X r) := by
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
  have hcD : c*D≤power ((2*(a+2))*(2*(a+2))*X) r := by
    rw [power_mul_base,power_mul_base,←power_add,←two_mul,hDd]
    exact mul_le_mul_of_nonneg_right hcup (by simp)
  have hKN : power ((4*X*Y*Y+1)*((X+1)*(X+1))) r≤K*N := by
    rw [power_mul_base,power_mul_base (X+1) (X+1),←power_add,←two_mul,hNd]
    exact mul_le_mul_of_nonneg_right hKlow (by simp)
  have hraise := power_mono_base _ _ r hupper
  rw [power_mul_base _ a,power_mul_base _ (a+9)] at hraise
  have hXa : X+1≤a := by
    rw [←ha]; calc X+1=1*(X+1) := (one_mul _).symm
      _≤Y*(X+1) := mul_le_mul_of_nonneg_right hY (by simp)
  have h18 : 2*r*9≤a := by
    have h1 : 2*r*9≤144*r := by
      have : 2*r*9+126*r=144*r := by ring
      rw [←this]; exact le_add_of_nonneg_right (by simp)
    exact le_trans h1 (le_trans h144.le hXa)
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
  have hmain : a*(2*c*D)≤2*K*N*(a+2*r*9) := calc
    a*(2*c*D)=2*(a*(c*D)) := by ring
    _≤2*(a*power ((2*(a+2))*(2*(a+2))*X) r) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcD (by simp)) (by simp)
    _≤2*(power ((4*X*Y*Y+1)*((X+1)*(X+1))) r*(a+2*r*9)) :=
        mul_le_mul_of_nonneg_left hcancel (by simp)
    _≤2*(K*N*(a+2*r*9)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKN (by simp)) (by simp)
    _=2*K*N*(a+2*r*9) := by ring
  -- the crude bound now gives `36 r N < a D`
  have hcrude : 36*r*N<a*D := by
    have hYY : Y+1≤2*Y := by
      calc Y+1≤Y+Y := add_le_add le_rfl hY
        _=2*Y := (two_mul Y).symm
    have hra : 144*r*Y<a := by
      rw [←ha]
      have := mul_lt_mul_of_pos_right h144 (lt_of_lt_of_le (by simp) hY)
      rwa [mul_comm (X+1) Y] at this
    calc
      36*r*N<36*r*(2*(Y+1)*D) := mul_lt_mul_of_pos_left hN (by
        exact mul_pos (by simp) hr0)
      _=72*r*((Y+1)*D) := by ring
      _≤72*r*((2*Y)*D) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hYY (by simp)) (by simp)
      _=(144*r*Y)*D := by ring
      _<a*D := mul_lt_mul_of_pos_right hra hDpos
  have hfinal : a*(2*c*D)<a*(K*(2*N+D)) := calc
    a*(2*c*D)≤2*K*N*(a+2*r*9) := hmain
    _=a*(2*K*N)+K*(36*r*N) := by ring
    _<a*(2*K*N)+K*(a*D) := add_lt_add_of_le_of_lt le_rfl (mul_lt_mul_of_pos_left hcrude hKpos)
    _=a*(K*(2*N+D)) := by ring
  exact lt_of_mul_lt_mul_left hfinal (by simp)

theorem hundred_forty_four_lt (r : V) (hr : 5≤r) : 144*r<Exp.exp (2*r+1)+1 := by
  have h1 : 1≤r := le_trans (by norm_num) hr
  obtain ⟨s,rfl⟩ : ∃ s, r=s+1 := ⟨r-1,(tsub_add_cancel_of_le h1).symm⟩
  have hs : 4≤s := by
    have : (4:V)+1≤s+1 := by simpa only [show (4:V)+1=5 by norm_num] using hr
    exact (add_le_add_iff_right 1).mp this
  have h72 := seventy_two_lt_exp s hs
  have he : Exp.exp (2*(s+1)+1)=4*Exp.exp (2*s+1) := by
    rw [show 2*(s+1)+1=(2*s+1)+1+1 by ring,exp_succ,exp_succ]; ring
  rw [he]
  have hs1 : (144:V)≤144*s := by
    simpa using mul_le_mul_of_nonneg_left (le_trans (by norm_num) hs : (1:V)≤s) (by simp : (0:V)≤144)
  calc 144*(s+1)=144*s+144 := by ring
    _≤144*s+144*s := add_le_add le_rfl hs1
    _=4*(72*s) := by ring
    _<4*Exp.exp (2*s+1) := mul_lt_mul_of_pos_left h72 (by simp)
    _≤4*Exp.exp (2*s+1)+1 := le_add_of_nonneg_right (by simp)

/-- **`η > 0`.** -/
theorem eta_pos (X Y r c k : V) (hr : 5≤r) (hX : X=Exp.exp (2*r+1)) (hY : 1≤Y)
    (hc : c=ycoord (2*r+1) (Y*(X+1))) (hk : k=2*ycoord (r+1) (2*(X*Y*Y-1)+1))
    (hlo : k*(2*Y)<2*c+k) (hhi : 2*c<k*(2*Y+1)) : k*Y<c := by
  have hr1 : 1≤r := le_trans (by norm_num) hr
  have hr0 : 0<r := lt_of_lt_of_le (by simp) hr1
  have hX1 : 1≤X := by rw [hX]; exact one_le_exp _
  have h144 : 144*r<X+1 := by rw [hX]; exact hundred_forty_four_lt r hr
  have hlow := sandwich_lower X Y r hX1 hY hr1
  obtain ⟨K,hKd⟩ : ∃ K, ycoord (r+1) (2*(X*Y*Y-1)+1)=K := ⟨_,rfl⟩
  obtain ⟨N,hNd⟩ : ∃ N, power (X+1) (2*r)=N := ⟨_,rfl⟩
  obtain ⟨D,hDd⟩ : ∃ D, power X r=D := ⟨_,rfl⟩
  rw [hKd,hNd,hDd,←hc] at hlow
  rw [hKd] at hk
  have hKpos : 0<K := by rw [←hKd]; exact lt_of_lt_of_le (by simp) (time_le_y (r+1) _)
  have hDpos : 0<D := by rw [←hDd]; exact power_pos X r (lt_of_lt_of_le (by simp) hX1)
  have hkpos : 0<k := by rw [hk]; exact mul_pos (by simp) hKpos
  -- the crude bound `N < 2(Y+1)D`
  have hN : N<2*(Y+1)*D := by
    have h1 : k*N<k*(2*(Y+1)*D) := calc
      k*N=2*K*N := by rw [hk]
      _<2*c*D := hlow
      _<k*(2*Y+1)*D := mul_lt_mul_of_pos_right hhi hDpos
      _≤k*(2*(Y+1))*D := by
          apply mul_le_mul_of_nonneg_right _ (by simp)
          apply mul_le_mul_of_nonneg_left _ (by simp)
          have : 2*Y+1+1=2*(Y+1) := by ring
          rw [←this]; exact le_add_of_nonneg_right (by simp)
      _=k*(2*(Y+1)*D) := by ring
    exact lt_of_mul_lt_mul_left h1 (by simp)
  have hup := sandwich_upper_half X Y r hX1 hY hr1 h144 (by rw [hNd,hDd]; exact hN)
  rw [hKd,hNd,hDd,←hc] at hup
  -- the central split, with `v ≤ D/2` and an even central part
  obtain ⟨v,w,hsplit,hv⟩ := central_split X r hX1
  rw [hNd,hDd] at hsplit
  rw [hDd] at hv
  have hX2 : X=2*Exp.exp (2*r) := by rw [hX,exp_succ]
  have h2v : 2*v≤D := by
    rw [hX2] at hv
    have : Exp.exp (2*r)*(2*v)≤Exp.exp (2*r)*D := by
      calc Exp.exp (2*r)*(2*v)=2*Exp.exp (2*r)*v := by ring
        _≤Exp.exp (2*r)*D := hv
    exact le_of_mul_le_mul_left this (exp_pos _)
  obtain ⟨β1,hβ1⟩ := two_dvd_central r hr0
  set M2 : V := β1+Exp.exp (2*r)*w with hM2
  have hNM : N=2*M2*D+v := by rw [hsplit,hβ1,hX2,hM2]; ring
  -- `c < K (2 M2 + 1)`
  have hcup : c<K*(2*M2+1) := by
    have h1 : 2*c*D<(2*(K*(2*M2+1)))*D := calc
      2*c*D<K*(2*N+D) := hup
      _=K*(4*M2*D+2*v+D) := by rw [hNM]; ring
      _≤K*(4*M2*D+D+D) := by
          apply mul_le_mul_of_nonneg_left _ (by simp)
          exact add_le_add (add_le_add le_rfl h2v) le_rfl
      _=(2*(K*(2*M2+1)))*D := by ring
    have h2 := lt_of_mul_lt_mul_right h1 (by simp)
    exact lt_of_mul_lt_mul_left h2 (by simp)
  -- `Y ≤ M2`
  have hYM : Y≤M2 := by
    have h1 : 2*K*(2*Y)<2*(c+K) := by
      calc 2*K*(2*Y)=k*(2*Y) := by rw [hk]
        _<2*c+k := hlo
        _=2*(c+K) := by rw [hk]; ring
    have h2 : 2*(K*Y)<2*(K*(M2+1)) := calc
      2*(K*Y)<c+K := by
          have : 2*(2*(K*Y))<2*(c+K) := by
            calc 2*(2*(K*Y))=2*K*(2*Y) := by ring
              _<2*(c+K) := h1
          exact lt_of_mul_lt_mul_left this (by simp)
      _<K*(2*M2+1)+K := add_lt_add_of_lt_of_le hcup le_rfl
      _=2*(K*(M2+1)) := by ring
    have h3 := lt_of_mul_lt_mul_left h2 (by simp)
    have h4 : Y<M2+1 := lt_of_mul_lt_mul_left h3 (by simp)
    exact lt_succ_iff_le.mp h4
  -- `2 K M2 < c`
  have hcM : 2*K*M2<c := by
    have h1 : (2*K*M2)*(2*D)<c*(2*D) := calc
      (2*K*M2)*(2*D)=2*K*(2*M2*D) := by ring
      _≤2*K*(2*M2*D+v) := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by simp)) (by simp)
      _=2*K*N := by rw [hNM]
      _<2*c*D := hlow
      _=c*(2*D) := by ring
    exact lt_of_mul_lt_mul_right h1 (by simp)
  calc k*Y=2*K*Y := by rw [hk]
    _≤2*K*M2 := mul_le_mul_of_nonneg_left hYM (by simp)
    _<c := hcM

#print axioms sandwich_upper_half
#print axioms hundred_forty_four_lt
#print axioms eta_pos

end DiophantineConsistency.P138HalfBinomial
