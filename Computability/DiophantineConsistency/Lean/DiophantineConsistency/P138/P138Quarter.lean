import DiophantineConsistency.P138.P138HalfBinomial
import DiophantineConsistency.ArithmeticBinomFactorial

/-! # The canonical quarter: `4η < k` at the outer seed

Completeness needs `4η < k` at the canonical outer data (`P138Cone.canonical_budget`; the
existing converse only provides `0 < η < k`). Notation as in `P138HalfBinomial`:
`X = 2^(2r+1)`, `a = Y(X+1)`, `bF = 2(XY² − 1) + 1`, `c = ψ_a(2r+1)`, `K = ψ_bF(r+1)`,
`k = 2K`, `N = (X+1)^(2r)`, `D = X^r`.

* `sandwich_upper_quarter` quarters the slack of `ArithmeticHalfBinomialSandwich.sandwich_upper`:
  `4cD < K(4N + D)`, i.e. `c/k < N/(2D) + 1/8` (needs `288 r < X + 1`).
* `central_quarter` sharpens `ArithmeticBinomExpansion.central_split`: `N = M D + v` with
  `M = binom(2r,r) + Xw` and `4v < D`. The remainder is `v = Σ_{j<r} binom(2r,j) X^j`; its top
  term is `binom(2r,r−1) X^(r−1)`, and `2 binom(2r,r−1) + 2 ≤ 2^(2r)` by the symmetry
  `binom(2r,r−1) = binom(2r,r+1)` (`binom_mul_fact`) and `binom(2r,r) ≥ 2`.
* So `c/k ∈ (M/2, M/2 + 1/4)`, while the seed interval `kY < c < kY + k` puts `c/k` in
  `(Y, Y+1)`. Hence `Y = M/2` and `4c < k(4Y + 1)`, i.e. `4η < k` (`eta_quarter`). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.P138Quarter
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPow ArithmeticPellRecurrence ArithmeticPellPowerRecovery ArithmeticHalfBinomialSandwich
  ArithmeticBinomExpansion ArithmeticBinomLegendre ArithmeticHalfBinomial ArithmeticBinomPascal
  ArithmeticBinomFactorial

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **The quartered upper half**: `4cD < K(4N + D)`. -/
theorem sandwich_upper_quarter (X Y r : V) (hX : 1≤X) (hY : 1≤Y) (hr : 1≤r) (h288 : 288*r<X+1)
    (hN : power (X+1) (2*r)<2*(Y+1)*power X r) :
    4*ycoord (2*r+1) (Y*(X+1))*power X r<
      ycoord (r+1) (2*(X*Y*Y-1)+1)*(4*power (X+1) (2*r)+power X r) := by
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
    have h1 : 2*r*9≤288*r := by
      have : 2*r*9+270*r=288*r := by ring
      rw [←this]; exact le_add_of_nonneg_right (by simp)
    exact le_trans h1 (le_trans h288.le hXa)
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
  have hmain : a*(c*D)≤K*N*(a+2*r*9) := calc
    a*(c*D)≤a*power ((2*(a+2))*(2*(a+2))*X) r := mul_le_mul_of_nonneg_left hcD (by simp)
    _≤power ((4*X*Y*Y+1)*((X+1)*(X+1))) r*(a+2*r*9) := hcancel
    _≤K*N*(a+2*r*9) := mul_le_mul_of_nonneg_right hKN (by simp)
  -- the crude bound now gives `72 r N < a D`
  have hcrude : 72*r*N<a*D := by
    have hYY : Y+1≤2*Y := by
      calc Y+1≤Y+Y := add_le_add le_rfl hY
        _=2*Y := (two_mul Y).symm
    have hra : 288*r*Y<a := by
      rw [←ha]
      have := mul_lt_mul_of_pos_right h288 (lt_of_lt_of_le (by simp) hY)
      rwa [mul_comm (X+1) Y] at this
    calc
      72*r*N<72*r*(2*(Y+1)*D) := mul_lt_mul_of_pos_left hN (by
        exact mul_pos (by simp) hr0)
      _=144*r*((Y+1)*D) := by ring
      _≤144*r*((2*Y)*D) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hYY (by simp)) (by simp)
      _=(288*r*Y)*D := by ring
      _<a*D := mul_lt_mul_of_pos_right hra hDpos
  have hfinal : a*(4*c*D)<a*(K*(4*N+D)) := calc
    a*(4*c*D)=4*(a*(c*D)) := by ring
    _≤4*(K*N*(a+2*r*9)) := mul_le_mul_of_nonneg_left hmain (by simp)
    _=a*(4*K*N)+K*(72*r*N) := by ring
    _<a*(4*K*N)+K*(a*D) := add_lt_add_of_le_of_lt le_rfl (mul_lt_mul_of_pos_left hcrude hKpos)
    _=a*(K*(4*N+D)) := by ring
  exact lt_of_mul_lt_mul_left hfinal (by simp)

theorem two_eighty_eight_lt (r : V) (hr : 6≤r) : 288*r<Exp.exp (2*r+1)+1 := by
  have h2 : 2≤r := le_trans (by norm_num) hr
  obtain ⟨s,rfl⟩ : ∃ s, r=s+2 := ⟨r-2,(tsub_add_cancel_of_le h2).symm⟩
  have hs : 4≤s := by
    have : (4:V)+2≤s+2 := by simpa only [show (4:V)+2=6 by norm_num] using hr
    exact (add_le_add_iff_right 2).mp this
  have h72 := seventy_two_lt_exp s hs
  have he : Exp.exp (2*(s+2)+1)=16*Exp.exp (2*s+1) := by
    rw [show 2*(s+2)+1=(2*s+1)+1+1+1+1 by ring,exp_succ,exp_succ,exp_succ,exp_succ]; ring
  rw [he]
  have hs1 : (576:V)≤144*s := by
    have := mul_le_mul_of_nonneg_left hs (by simp : (0:V)≤144)
    simpa only [show (144:V)*4=576 by norm_num] using this
  calc 288*(s+2)=288*s+576 := by ring
    _≤288*s+144*s := add_le_add le_rfl hs1
    _≤(288*s+144*s)+720*s := le_add_of_nonneg_right (by simp)
    _=16*(72*s) := by ring
    _<16*Exp.exp (2*s+1) := mul_lt_mul_of_pos_left h72 (by simp)
    _≤16*Exp.exp (2*s+1)+1 := le_add_of_nonneg_right (by simp)

/-- `binom(2(t+1), t+2) = binom(2(t+1), t)`. -/
theorem binom_symm_two (t : V) : binom (2*(t+1)) (t+2)=binom (2*(t+1)) t := by
  have e1 := binom_mul_fact t (t+2)
  have e2 := binom_mul_fact (t+2) t
  rw [show t+(t+2)=2*(t+1) by ring] at e1
  rw [show t+2+t=2*(t+1) by ring] at e2
  have hpos : 0<fact t*fact (t+2) := mul_pos (fact_pos t) (fact_pos (t+2))
  apply cancel_left hpos
  calc fact t*fact (t+2)*binom (2*(t+1)) (t+2)=binom (2*(t+1)) (t+2)*fact (t+2)*fact t := by ring
    _=fact (2*(t+1)) := e2
    _=binom (2*(t+1)) t*fact t*fact (t+2) := e1.symm
    _=fact t*fact (t+2)*binom (2*(t+1)) t := by ring

/-- `2 binom(2(t+1), t) + 2 ≤ 2^(2(t+1))`. -/
theorem binom_below_central (t : V) : 2*binom (2*(t+1)) t+2≤Exp.exp (2*(t+1)) := by
  have hrow := row_sum (2*(t+1))
  have hmono := bsum_mono 1 (2*(t+1)) (t+3) t
  rw [show t+3+t=2*(t+1)+1 by ring,hrow] at hmono
  rw [show t+3=t+2+1 by ring,bsum_succ,show t+2=t+1+1 by ring,bsum_succ,bsum_succ,
    one_power,one_power,one_power,mul_one,mul_one,mul_one,show t+1+1=t+2 by ring,
    binom_symm_two] at hmono
  have hc2 : 2≤binom (2*(t+1)) (t+1) := by
    obtain ⟨m,hm⟩ := two_dvd_central (t+1) (lt_of_lt_of_le (by simp) le_add_self)
    have hp := binom_pos (2*(t+1)) (t+1) (by
      rw [two_mul]; exact le_add_of_nonneg_right (by simp))
    rw [hm] at hp ⊢
    have hm1 : 1≤m := pos_iff_one_le.mp (pos_of_mul_pos_right hp (by simp))
    simpa using mul_le_mul_of_nonneg_left hm1 (by simp : (0:V)≤2)
  calc 2*binom (2*(t+1)) t+2=binom (2*(t+1)) t+2+binom (2*(t+1)) t := by ring
    _≤binom (2*(t+1)) t+binom (2*(t+1)) (t+1)+binom (2*(t+1)) t :=
        add_le_add (add_le_add le_rfl hc2) le_rfl
    _≤ArithmeticBinomExpansion.bsum 1 (2*(t+1)) t+binom (2*(t+1)) t+
        binom (2*(t+1)) (t+1)+binom (2*(t+1)) t := by
        rw [show ArithmeticBinomExpansion.bsum 1 (2*(t+1)) t+binom (2*(t+1)) t+
          binom (2*(t+1)) (t+1)+binom (2*(t+1)) t=(binom (2*(t+1)) t+binom (2*(t+1)) (t+1)+
          binom (2*(t+1)) t)+ArithmeticBinomExpansion.bsum 1 (2*(t+1)) t by ring]
        exact le_add_of_nonneg_right (by simp)
    _≤Exp.exp (2*(t+1)) := hmono

/-- **The quartered central split**: `(X+1)^(2r) = (binom(2r,r) + Xw) X^r + v`, `4v < X^r`. -/
theorem central_quarter (X r : V) (hr : 1≤r) (hX : X=Exp.exp (2*r+1)) :
    ∃ v w, power (X+1) (2*r)=(binom (2*r) r+X*w)*power X r+v ∧ 4*v<power X r := by
  rcases bsum_split X (2*r) r r with ⟨w,hw⟩
  refine ⟨ArithmeticBinomExpansion.bsum X (2*r) r,w,?_,?_⟩
  · rw [binomial_theorem,show 2*r+1=r+r+1 by ring,hw]
    ring
  obtain ⟨t,rfl⟩ : ∃ t, r=t+1 := ⟨r-1,(tsub_add_cancel_of_le hr).symm⟩
  have hX1 : 1≤X := by rw [hX]; exact one_le_exp _
  have hX0 : 0<X := lt_of_lt_of_le (by simp) hX1
  have hclaim := binom_below_central t
  obtain ⟨Q,hQ⟩ : ∃ Q, Exp.exp (2*(t+1))=Q := ⟨_,rfl⟩
  rw [hQ] at hclaim
  have hXQ : X=2*Q := by rw [hX,exp_succ,hQ]
  rw [bsum_succ,power_succ]
  have hs := bsum_scaled_le X (2*(t+1)) t hX1
  have hs1 := bsum_one_le (2*(t+1)) t
  rw [hQ] at hs1
  obtain ⟨S,hS⟩ : ∃ S, ArithmeticBinomExpansion.bsum X (2*(t+1)) t=S := ⟨_,rfl⟩
  obtain ⟨C,hC⟩ : ∃ C, binom (2*(t+1)) t=C := ⟨_,rfl⟩
  obtain ⟨P,hP⟩ : ∃ P, power X t=P := ⟨_,rfl⟩
  rw [hS,hP] at hs
  rw [hS,hC,hP]
  rw [hC] at hclaim
  have hP0 : 0<P := by rw [←hP]; exact power_pos X t hX0
  have hXS : X*S≤Q*P :=
    le_trans hs (mul_le_mul_of_nonneg_right hs1 (by simp))
  apply lt_of_mul_lt_mul_left _ (by simp : (0:V)≤X)
  calc X*(4*(S+C*P))=4*(X*S)+4*(C*(X*P)) := by ring
    _≤4*(Q*P)+4*(C*(X*P)) := add_le_add (mul_le_mul_of_nonneg_left hXS (by simp)) le_rfl
    _=4*Q*P*(2*C+1) := by rw [hXQ]; ring
    _<4*Q*P*(2*C+1)+4*Q*P := lt_add_of_pos_right _ (mul_pos (mul_pos (by simp)
        (lt_of_lt_of_le (by simp) (le_trans (le_add_of_nonneg_left (by simp)) hclaim))) hP0)
    _=4*Q*P*(2*C+2) := by ring
    _≤4*Q*P*Q := mul_le_mul_of_nonneg_left hclaim (by simp)
    _=X*(X*P) := by rw [hXQ]; ring

/-- **The canonical quarter.** With the seed interval `kY < c < kY + k`, `4c < k(4Y + 1)`. -/
theorem eta_quarter (X Y r c k : V) (hr : 6≤r) (hX : X=Exp.exp (2*r+1)) (hY : 1≤Y)
    (hc : c=ycoord (2*r+1) (Y*(X+1))) (hk : k=2*ycoord (r+1) (2*(X*Y*Y-1)+1))
    (hlo : k*Y<c) (hhi : c<k*Y+k) : 4*c<k*(4*Y+1) := by
  have hr1 : 1≤r := le_trans (by norm_num) hr
  have hr0 : 0<r := lt_of_lt_of_le (by simp) hr1
  have hX1 : 1≤X := by rw [hX]; exact one_le_exp _
  have h288 : 288*r<X+1 := by rw [hX]; exact two_eighty_eight_lt r hr
  have hlow := sandwich_lower X Y r hX1 hY hr1
  obtain ⟨K,hKd⟩ : ∃ K, ycoord (r+1) (2*(X*Y*Y-1)+1)=K := ⟨_,rfl⟩
  obtain ⟨N,hNd⟩ : ∃ N, power (X+1) (2*r)=N := ⟨_,rfl⟩
  obtain ⟨D,hDd⟩ : ∃ D, power X r=D := ⟨_,rfl⟩
  rw [hKd,hNd,hDd,←hc] at hlow
  rw [hKd] at hk
  have hKpos : 0<K := by rw [←hKd]; exact lt_of_lt_of_le (by simp) (time_le_y (r+1) _)
  have hDpos : 0<D := by rw [←hDd]; exact power_pos X r (lt_of_lt_of_le (by simp) hX1)
  -- the crude bound `N < 2(Y+1)D`
  have hN : N<2*(Y+1)*D := by
    have h1 : k*N<k*(2*(Y+1)*D) := calc
      k*N=2*K*N := by rw [hk]
      _<2*c*D := hlow
      _<2*(k*Y+k)*D := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hhi (by simp)) hDpos
      _=k*(2*(Y+1)*D) := by ring
    exact lt_of_mul_lt_mul_left h1 (by simp)
  have hup := sandwich_upper_quarter X Y r hX1 hY hr1 h288 (by rw [hNd,hDd]; exact hN)
  rw [hKd,hNd,hDd,←hc] at hup
  obtain ⟨v,w,hsplit,hv⟩ := central_quarter X r hr1 hX
  rw [hNd,hDd] at hsplit
  rw [hDd] at hv
  have hX2 : X=2*Exp.exp (2*r) := by rw [hX,exp_succ]
  obtain ⟨β1,hβ1⟩ := two_dvd_central r hr0
  obtain ⟨M2,hM2⟩ : ∃ M2, β1+Exp.exp (2*r)*w=M2 := ⟨_,rfl⟩
  have hNM : N=2*M2*D+v := by rw [hsplit,hβ1,hX2,←hM2]; ring
  -- `2c < K (4 M2 + 1)`
  have hcup : 2*c<K*(4*M2+1) := by
    have h1 : (2*c)*(2*D)<(K*(4*M2+1))*(2*D) := calc
      (2*c)*(2*D)=4*c*D := by ring
      _<K*(4*N+D) := hup
      _=K*(8*M2*D+4*v+D) := by rw [hNM]; ring
      _<K*(8*M2*D+D+D) := mul_lt_mul_of_pos_left
          (add_lt_add_of_lt_of_le (add_lt_add_of_le_of_lt le_rfl hv) le_rfl) hKpos
      _=(K*(4*M2+1))*(2*D) := by ring
    exact lt_of_mul_lt_mul_right h1 (by simp)
  -- `2 K M2 < c`
  have hcM : 2*K*M2<c := by
    have h1 : (2*K*M2)*(2*D)<c*(2*D) := calc
      (2*K*M2)*(2*D)=2*K*(2*M2*D) := by ring
      _≤2*K*(2*M2*D+v) := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by simp)) (by simp)
      _=2*K*N := by rw [hNM]
      _<2*c*D := hlow
      _=c*(2*D) := by ring
    exact lt_of_mul_lt_mul_right h1 (by simp)
  -- `Y = M2`
  have hYM : Y≤M2 := by
    have h1 : K*(4*Y)<K*(4*(M2+1)) := calc
      K*(4*Y)=2*(k*Y) := by rw [hk]; ring
      _<2*c := mul_lt_mul_of_pos_left hlo (by simp)
      _<K*(4*M2+1) := hcup
      _≤K*(4*M2+1+3) := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by simp)) (by simp)
      _=K*(4*(M2+1)) := by ring
    have h2 := lt_of_mul_lt_mul_left h1 (by simp)
    exact lt_succ_iff_le.mp (lt_of_mul_lt_mul_left h2 (by simp))
  have hMY : M2≤Y := by
    have h1 : k*M2<k*(Y+1) := calc
      k*M2=2*K*M2 := by rw [hk]
      _<c := hcM
      _<k*Y+k := hhi
      _=k*(Y+1) := by ring
    exact lt_succ_iff_le.mp (lt_of_mul_lt_mul_left h1 (by simp))
  have hYeq : Y=M2 := le_antisymm hYM hMY
  calc 4*c=2*(2*c) := by ring
    _<2*(K*(4*M2+1)) := mul_lt_mul_of_pos_left hcup (by simp)
    _=k*(4*Y+1) := by rw [hk,hYeq]; ring

/-- `4η < k` in the seed's own coordinates `c = kY + η`. -/
theorem eta_quarter' (X Y r k eta : V) (hr : 6≤r) (hX : X=Exp.exp (2*r+1)) (hY : 1≤Y)
    (hc : k*Y+eta=ycoord (2*r+1) (Y*(X+1))) (hk : k=2*ycoord (r+1) (2*(X*Y*Y-1)+1))
    (heta : 0<eta) (hetak : eta<k) : 4*eta<k := by
  have h := eta_quarter X Y r (k*Y+eta) k hr hX hY hc hk
    (lt_add_of_pos_right _ heta) (add_lt_add_of_le_of_lt le_rfl hetak)
  have h' : 4*(k*Y)+4*eta<4*(k*Y)+k := by
    calc 4*(k*Y)+4*eta=4*(k*Y+eta) := by ring
      _<k*(4*Y+1) := h
      _=4*(k*Y)+k := by ring
  exact lt_of_add_lt_add_left h'

#print axioms sandwich_upper_quarter
#print axioms two_eighty_eight_lt
#print axioms binom_symm_two
#print axioms binom_below_central
#print axioms central_quarter
#print axioms eta_quarter
#print axioms eta_quarter'

end DiophantineConsistency.P138Quarter
