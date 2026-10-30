import DiophantineConsistency.ArithmeticHalfBinomialSandwich
import DiophantineConsistency.ArithmeticBinomExpansion
import DiophantineConsistency.ArithmeticBinomLegendre

/-! The internal half-binomial extraction and the population bound (spec A6),
plus the construction-side binomial floor and Pell interval (spec stage S,
steps 2 and 4), at arbitrary internal parameters, with no real numbers.

Notation: `X = 2^(2r+1)`, `a = Y*(X+1)`, `B = 2*(X*Y*Y-1)+1`,
`c = ycoord (2r+1) a`, `k = 2*ycoord (r+1) B`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticHalfBinomial
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPow ArithmeticPellRecurrence ArithmeticBinomPascal ArithmeticBinomExpansion
  ArithmeticBinomLegendre ArithmeticBinaryPopulation ArithmeticHalfBinomialSandwich
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The source-sized base dominates the error coefficient: `72r < 2^(2r+1)` for `r ≥ 4`. -/
theorem seventy_two_lt_exp (r : V) (hr : 4≤r) : 72*r<Exp.exp (2*r+1) := by
  have all (s : V) : 72*(4+s)<Exp.exp (2*(4+s)+1) := by
    induction s using ISigma1.sigma1_succ_induction
    · definability
    case zero =>
      have h9 : (2*(4+0)+1:V)=0+1+1+1+1+1+1+1+1+1 := by ring
      rw [h9]
      simp only [exp_succ,exp_zero]
      exact_mod_cast (show 72*(4+0)<2*(2*(2*(2*(2*(2*(2*(2*(2*1)))))))) by decide)
    case succ s ih =>
      have he : Exp.exp (2*(4+(s+1))+1)=4*Exp.exp (2*(4+s)+1) := by
        rw [show 2*(4+(s+1))+1=(2*(4+s)+1)+1+1 by ring,exp_succ,exp_succ]
        ring
      have h72 : (72:V)≤72*(4+s) := by
        simpa using mul_le_mul_of_nonneg_left
          (show (1:V)≤4+s from le_trans (by simp) (le_add_of_nonneg_right (by simp)))
          (by simp : (0:V)≤72)
      rw [he]
      calc
        72*(4+(s+1))=72*(4+s)+72 := by ring
        _<Exp.exp (2*(4+s)+1)+72*(4+s) := add_lt_add_of_lt_of_le ih h72
        _≤Exp.exp (2*(4+s)+1)+Exp.exp (2*(4+s)+1) := add_le_add le_rfl ih.le
        _≤4*Exp.exp (2*(4+s)+1) := by
          have : Exp.exp (2*(4+s)+1)+Exp.exp (2*(4+s)+1)+2*Exp.exp (2*(4+s)+1)=
            4*Exp.exp (2*(4+s)+1) := by ring
          rw [←this]; exact le_add_of_nonneg_right (by simp)
  simpa only [add_tsub_cancel_of_le hr] using all (r-4)

private theorem dvd_of_add {d C b : V} (hd : 0<d) (hsum : d∣C+b) (hb : d∣b) : d∣C := by
  apply mod_eq_zero_iff_dvd.mp
  have hz : (C+b)%d = 0 := mod_eq_zero_iff_dvd.mpr hsum
  rwa [mod_add_remove_right_of_dvd hb hd] at hz

private theorem cancel_lt {m x y : V} (h : m*x<m*y) : x<y :=
  lt_of_mul_lt_mul_left h (by simp)

private theorem exp_dvd_exp_of_le {a b : V} (h : a≤b) : Exp.exp a∣Exp.exp b :=
  ⟨Exp.exp (b-a), by rw [←exp_add,add_tsub_cancel_of_le h]⟩

theorem rank_lower_of_radix (q F alpha J MC MF h : V)
    (hq16 : 16≤q) (halpha : 0<alpha) (hq : q=Exp.exp h) :
    3*h+1≤((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J := by
  let R := ((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J
  have hR : q^2-1≤R := by
    have h1 : 1≤(q-1)*(q-F)+alpha :=
      le_trans (pos_iff_one_le.mp halpha) (le_add_of_nonneg_left (by simp))
    exact le_trans (le_mul_of_one_le_left (by simp) h1) (le_add_of_nonneg_right (by simp))
  have hhq : h+1≤q := by rw [hq]; exact lt_iff_succ_le.mp (lt_exp h)
  have hsq : 3*h+1+1≤q^2 := calc
    3*h+1+1≤3*(h+1)+(16:V) := by
      have he : 3*h+1+1+(3+14:V)=3*(h+1)+16 := by ring
      rw [←he]; exact le_add_of_nonneg_right (by simp)
    _≤3*q+q := add_le_add (mul_le_mul_of_nonneg_left hhq (by simp)) hq16
    _=4*q := by ring
    _≤q*q := mul_le_mul_of_nonneg_right (le_trans (by norm_num : (4:V)≤16) hq16) (by simp)
    _=q^2 := by ring
  exact le_trans (le_tsub_of_add_le_right hsq) hR

/-- Recover a half-index at least four from a doubled index at least five. -/
theorem half_index_of_ge_five (n R : V) (hn5 : 5≤n) (hnR : 2*n=R+1) :
    ∃ r, r+1=n ∧ 4≤r ∧ R=2*r+1 := by
  have hn1 : 1≤n := le_trans (by simp) hn5
  let r : V := n-1
  have hrn : r+1=n := tsub_add_cancel_of_le hn1
  have hr4 : 4≤r := by
    apply (add_le_add_iff_right (1:V)).mp
    rw [hrn]
    simpa only [show (4:V)+1=5 by ring] using hn5
  have hR : R=2*r+1 := by
    apply add_right_cancel (b:=(1:V))
    rw [←hnR,←hrn]; ring
  exact ⟨r,hrn,hr4,hR⟩

/-- **Half-binomial extraction (soundness).** From the actual doubled Pell
coordinates and the interval `c = k*Y+η`, `k = η+ζ`, `η,ζ > 0`:
`2*Y = binom (2r) r + w*X`. -/
theorem half_binomial (X Y r eta zeta : V) (hr : 4≤r) (hX : X=Exp.exp (2*r+1)) (hY : 1≤Y)
    (hck : ycoord (2*r+1) (Y*(X+1))=2*ycoord (r+1) (2*(X*Y*Y-1)+1)*Y+eta)
    (hk : 2*ycoord (r+1) (2*(X*Y*Y-1)+1)=eta+zeta) (heta : 0<eta) (hzeta : 0<zeta) :
    ∃ w, 2*Y=binom (2*r) r+w*X := by
  have hr1 : 1≤r := le_trans (by simp) hr
  have hr0 : 0<r := lt_of_lt_of_le (by simp) hr1
  have hXbig : Exp.exp (2*r)<X := by rw [hX]; exact exp_monotone.mpr (by simp)
  have hX1 : 1≤X := le_trans (one_le_exp _) hXbig.le
  have h72 : 72*r<X+1 := lt_of_lt_of_le
    (by simpa only [hX] using seventy_two_lt_exp r hr) (le_add_of_nonneg_right (by simp))
  obtain ⟨hlow,hup⟩ := sandwich_of_interval X Y r eta zeta hX1 hY hr1 h72 hck hk hzeta
  obtain ⟨v,w,hN,hv⟩ := central_split_lt X r hXbig
  obtain ⟨C',hC'⟩ := two_dvd_central r hr0
  refine ⟨w,?_⟩
  obtain ⟨k,hkd⟩ : ∃ k, 2*ycoord (r+1) (2*(X*Y*Y-1)+1)=k := ⟨_,rfl⟩
  obtain ⟨c,hcd⟩ : ∃ c, ycoord (2*r+1) (Y*(X+1))=c := ⟨_,rfl⟩
  obtain ⟨D,hDd⟩ : ∃ D, power X r=D := ⟨_,rfl⟩
  rw [hkd] at hck hk hlow hup
  rw [hcd] at hck hlow hup
  rw [hDd] at hlow hup hN hv
  rw [hN] at hlow hup
  -- Q = binom + X*w = 2*t
  set t := C'+Exp.exp (2*r)*w with ht
  have hQ : binom (2*r) r+X*w=2*t := by rw [hC',hX,exp_succ,ht]; ring
  rw [hQ] at hlow hup
  have hkpos : 0<k := by rw [hk]; exact lt_of_lt_of_le hzeta (le_add_of_nonneg_left (by simp))
  have hDpos : 0<D := lt_of_le_of_lt (by simp) hv
  have hm : 0<2*k*D := mul_pos (mul_pos (by simp) hkpos) hDpos
  -- t < Y+1
  have hcY : c<k*(Y+1) := by
    rw [hck,mul_add,mul_one]
    exact add_lt_add_of_le_of_lt le_rfl (by rw [hk]; exact lt_add_of_pos_right eta hzeta)
  have h1 : (2*k*D)*t<(2*k*D)*(Y+1) := calc
    (2*k*D)*t≤k*(2*t*D+v) := by
      have : (2*k*D)*t+k*v=k*(2*t*D+v) := by ring
      rw [←this]; exact le_add_of_nonneg_right (by simp)
    _<2*c*D := hlow
    _≤2*(k*(Y+1))*D := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcY.le (by simp)) (by simp)
    _=(2*k*D)*(Y+1) := by ring
  -- Y < t+1
  have hYc : k*Y<c := by rw [hck]; exact lt_add_of_pos_right _ heta
  have h2 : (2*k*D)*Y<(2*k*D)*(t+1) := calc
    (2*k*D)*Y=2*(k*Y)*D := by ring
    _<2*c*D := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hYc (by simp)) hDpos
    _<k*(2*t*D+v+D) := hup
    _<k*(2*t*D+D+D) := mul_lt_mul_of_pos_left (add_lt_add_of_lt_of_le
        (add_lt_add_of_le_of_lt le_rfl hv) le_rfl) hkpos
    _=(2*k*D)*(t+1) := by ring
  have htY : t=Y := le_antisymm (lt_succ_iff_le.mp (cancel_lt h1))
    (lt_succ_iff_le.mp (cancel_lt h2))
  rw [mul_comm w X,hQ,htY]

/-- **Population bound (soundness).** If `2^(3h) ∣ Y` and `3h+1 ≤ 2r+1`, the
half-binomial identity forces `3h+2 ≤ σ(2r+1)`. -/
theorem population_lower (X Y r w h : V) (hX : X=Exp.exp (2*r+1))
    (hbin : 2*Y=binom (2*r) r+w*X) (hYq : Exp.exp (3*h)∣Y) (hh : 3*h+1≤2*r+1) :
    3*h+2≤population (2*r+1) := by
  have h2Y : Exp.exp (3*h+1)∣2*Y := by
    rcases hYq with ⟨y,rfl⟩
    exact ⟨y,by rw [exp_succ]; ring⟩
  have hXd : Exp.exp (3*h+1)∣w*X :=
    dvd_mul_of_dvd_right (by rw [hX]; exact exp_dvd_exp_of_le hh) w
  rw [hbin] at h2Y
  have hC := dvd_of_add (exp_pos _) h2Y hXd
  have hle := le_population_of_exp_dvd_central r (3*h+1) hC
  rw [population_odd]
  calc
    3*h+2=(3*h+1)+1 := by ring
    _≤population r+1 := add_le_add hle le_rfl

/-- **Binomial floor (construction).** For `X = 2^(2r+1)` and `3u+1 ≤ σ(r)`:
`(X+1)^(2r) = 2*Y*X^r + v` with `v < X^r`, `Y = s*2^(3u)`, `1 ≤ Y` and
`2*Y = binom (2r) r + w*X`. -/
theorem binomial_floor (X r u : V) (hr : 1≤r) (hX : X=Exp.exp (2*r+1))
    (hu : 3*u+1≤population r) :
    ∃ Y s v w, power (X+1) (2*r)=2*Y*power X r+v ∧ v<power X r ∧
      Y=s*Exp.exp (3*u) ∧ 1≤Y ∧ 2*Y=binom (2*r) r+w*X := by
  have hr0 : 0<r := lt_of_lt_of_le (by simp) hr
  have hXbig : Exp.exp (2*r)<X := by rw [hX]; exact exp_monotone.mpr (by simp)
  obtain ⟨v,w,hN,hv⟩ := central_split_lt X r hXbig
  have hpr : population r≤r := le_trans (population_le r).1 (population_le r).2
  have hbig : 3*u+1≤2*r+1 := le_trans hu (le_trans hpr (by
    rw [two_mul,add_assoc]; exact le_add_of_nonneg_right (by simp)))
  -- 2^(3u+1) divides the binomial and X
  have hCd : Exp.exp (3*u+1)∣binom (2*r) r :=
    dvd_trans (exp_dvd_exp_of_le hu) (exp_population_dvd_central r)
  have hXd : Exp.exp (3*u+1)∣X*w :=
    dvd_mul_of_dvd_left (by rw [hX]; exact exp_dvd_exp_of_le hbig) w
  obtain ⟨α,hα⟩ := hCd
  obtain ⟨β,hβ⟩ := hXd
  obtain ⟨m,hm⟩ : ∃ m, binom (2*r) r+X*w=Exp.exp (3*u+1)*m := ⟨α+β,by rw [hα,hβ]; ring⟩
  refine ⟨Exp.exp (3*u)*m,m,v,w,?_,hv,by ring,?_,?_⟩
  · rw [hN,hm,exp_succ]; ring
  · -- the central coefficient is positive, hence so is m
    have hCpos : 0<binom (2*r) r := binom_pos _ _ (by
      rw [two_mul]; exact le_add_of_nonneg_left (by simp))
    have hm0 : 0<m := pos_of_mul_pos_right
      (lt_of_lt_of_le hCpos (by rw [←hm]; exact le_add_of_nonneg_right (by simp))) (by simp)
    exact one_le_mul (one_le_exp _) (pos_iff_one_le.mp hm0)
  · rw [mul_comm w X,hm,exp_succ]; ring

/-- **Pell interval (construction).** If `(X+1)^(2r) = 2*Y*X^r + v` with
`v < X^r`, then `k*Y < c < k*(Y+1)`. No interval data is assumed. -/
theorem construction_interval (X Y r v : V) (hr : 4≤r) (hX : X=Exp.exp (2*r+1)) (hY : 1≤Y)
    (hN : power (X+1) (2*r)=2*Y*power X r+v) (hv : v<power X r) :
    2*ycoord (r+1) (2*(X*Y*Y-1)+1)*Y<ycoord (2*r+1) (Y*(X+1)) ∧
      ycoord (2*r+1) (Y*(X+1))<2*ycoord (r+1) (2*(X*Y*Y-1)+1)*(Y+1) := by
  have hr1 : 1≤r := le_trans (by simp) hr
  have hXbig : Exp.exp (2*r)<X := by rw [hX]; exact exp_monotone.mpr (by simp)
  have hX1 : 1≤X := le_trans (one_le_exp _) hXbig.le
  have h72 : 72*r<X+1 := lt_of_lt_of_le
    (by simpa only [hX] using seventy_two_lt_exp r hr) (le_add_of_nonneg_right (by simp))
  have hcrude : power (X+1) (2*r)<2*(Y+1)*power X r := by
    rw [hN]
    calc
      2*Y*power X r+v<2*Y*power X r+power X r := add_lt_add_of_le_of_lt le_rfl hv
      _≤2*(Y+1)*power X r := by
        have : 2*Y*power X r+power X r+power X r=2*(Y+1)*power X r := by ring
        rw [←this]; exact le_add_of_nonneg_right (by simp)
  have hlow := sandwich_lower X Y r hX1 hY hr1
  have hup := sandwich_upper X Y r hX1 hY hr1 h72 hcrude
  obtain ⟨k,hkd⟩ : ∃ k, 2*ycoord (r+1) (2*(X*Y*Y-1)+1)=k := ⟨_,rfl⟩
  obtain ⟨c,hcd⟩ : ∃ c, ycoord (2*r+1) (Y*(X+1))=c := ⟨_,rfl⟩
  obtain ⟨D,hDd⟩ : ∃ D, power X r=D := ⟨_,rfl⟩
  rw [hkd] at hlow hup ⊢
  rw [hcd] at hlow hup ⊢
  rw [hDd] at hlow hup hN hv
  rw [hN] at hlow hup
  have hDpos : 0<D := lt_of_le_of_lt (by simp) hv
  constructor
  · apply cancel_lt (m:=2*D)
    calc
      2*D*(k*Y)≤k*(2*Y*D+v) := by
        have : 2*D*(k*Y)+k*v=k*(2*Y*D+v) := by ring
        rw [←this]; exact le_add_of_nonneg_right (by simp)
      _<2*c*D := hlow
      _=2*D*c := by ring
  · apply cancel_lt (m:=2*D)
    calc
      2*D*c=2*c*D := by ring
      _<k*(2*Y*D+v+D) := hup
      _≤k*(2*Y*D+D+D) := mul_le_mul_of_nonneg_left (add_le_add
        (add_le_add le_rfl hv.le) le_rfl) (by simp)
      _=2*D*(k*(Y+1)) := by ring

end DiophantineConsistency.ArithmeticHalfBinomial
