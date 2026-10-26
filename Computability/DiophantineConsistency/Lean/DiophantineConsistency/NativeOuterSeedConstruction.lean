import DiophantineConsistency.NativeHalfBinomial
import Diophantine.Paper1982.Carries

/-!
# A fresh outer Pell seed from the exact native rank population

The native recipe uses a doubled first ordinate and a shifted main base.
The binomial floor and both ratio estimates are applied to that literal
recipe. No source solution, ratio interval, or divisibility is assumed.
-/

namespace DiophantineConsistency.NativeOuterSeedConstruction

open Diophantine Pell Jones1982 Jones1980

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- The odd-rank population supplies both required elementary size bounds. -/
theorem population_sizes {u R r : ℕ} (hu : 0 < u) (hR : R = 2*r+1)
    (hpop : σ 2 R = 3*u+2) :
    σ 2 r = 3*u+1 ∧ 4 ≤ r ∧ 3*u+1 < R := by
  have h := hpop
  rw [hR,σ_two_two_mul_add_one] at h
  have hr : σ 2 r ≤ r := Nat.digit_sum_le 2 r
  have hRR : σ 2 R ≤ R := Nat.digit_sum_le 2 R
  omega

/-- The exact binomial floor has the full common scale, with a strict
quarter-unit remainder. No Pell interval is supplied here. -/
theorem scaled_half_floor {u R r : ℕ} (hu : 0 < u) (hR : R = 2*r+1)
    (hpop : σ 2 R = 3*u+2) :
    ∃ s Y v : ℕ, 0 < s ∧ 0 < Y ∧ Y = s*(2^u)^3 ∧
      (2^R+1)^(2*r) = (2*Y)*(2^R)^r+v ∧ 4*v < (2^R)^r := by
  obtain ⟨hσ,hr,hsize⟩ := population_sizes hu hR hpop
  obtain ⟨Q,v,w,hfloor,hv,hQ⟩ := Ratio90.binomial_floor_two (by omega : 1 ≤ r)
    (show 2^(2*r+1) ≤ 2^R by rw [hR])
  have hcentral : 2^(3*u+1) ∣ (2*r).choose r :=
    (lemma_2_15 (3*u+1) r).mp (by omega)
  have hX : 2^(3*u+1) ∣ 2^R := pow_dvd_pow 2 (by omega)
  have hdiv : 2^(3*u+1) ∣ Q := by
    rw [hQ]
    exact dvd_add hcentral (dvd_mul_of_dvd_right hX w)
  obtain ⟨s,hs⟩ := hdiv
  have hQ0 : 0 < Q := by
    have hc : 0 < (2*r).choose r := Nat.choose_pos (by omega)
    omega
  have hs0 : 0 < s := by
    by_contra hh
    have : s = 0 := by omega
    rw [this,mul_zero] at hs
    omega
  let Y := 2^(3*u)*s
  have hY0 : 0 < Y := Nat.mul_pos (by positivity) hs0
  have hQY : Q = 2*Y := by
    rw [hs,pow_succ]
    dsimp [Y]
    ring
  have hscale : Y = s*(2^u)^3 := by
    dsimp [Y]
    rw [← pow_mul]
    rw [Nat.mul_comm 3 u,mul_comm]
  exact ⟨s,Y,v,hs0,hY0,hscale,by simpa only [hQY] using hfloor,hv⟩

/-- Both literal Pell pairs lie in the required open unit interval when Y
is the scaled half floor. This is the constructive direction. -/
theorem pell_interval {X Y r v : ℕ} (hX : 1 ≤ X) (hY : 1 ≤ Y) (hr : 4 ≤ r)
    (hfloor : (X+1)^(2*r) = (2*Y)*X^r+v) (hv : 4*v < X^r)
    (h72 : 72*r < X+1) (h16 : 16 ≤ Y*(X+1)) :
    let a := Y*(X+1)
    let P := 2*(X*Y^2)+1
    let c := yn (by omega : 1 < a+2) (2*r+1)
    let k := 2*yn (by dsimp [P]; nlinarith : 1 < P) (r+1)
    k*Y < c ∧ c < k*(Y+1) := by
  dsimp only
  let a := Y*(X+1)
  have hA : 1 < a+2 := by omega
  have hP : 1 < 2*(X*Y^2)+1 := by nlinarith
  let c := yn hA (2*r+1)
  let K := yn hP (r+1)
  have hK0 : 0 < K := lt_of_lt_of_le (Nat.succ_pos r) (yn_ge_n hP _)
  have hKR : (0:ℝ) < K := by exact_mod_cast hK0
  have hXR : (0:ℝ) < (X:ℝ)^r := by positivity
  have hfloorR : ((X:ℝ)+1)^(2*r) = (2*Y:ℝ)*(X:ℝ)^r+v := by
    exact_mod_cast hfloor
  have hvR : (4:ℝ)*v < (X:ℝ)^r := by exact_mod_cast hv
  have hξ : ((X:ℝ)+1)^(2*r)/(X:ℝ)^r = 2*Y+(v:ℝ)/(X:ℝ)^r := by
    rw [hfloorR]
    field_simp
  have hfrac : (v:ℝ)/(X:ℝ)^r < 1/4 := by
    rw [div_lt_iff₀ hXR]
    linarith
  have hξY : ((X:ℝ)+1)^(2*r)/(X:ℝ)^r < 2*(Y+1) := by
    rw [hξ]
    linarith
  have hlo := Ratio90.lower_estimate hX hY (by omega : 1 ≤ r) rfl hA rfl hP
    (rfl : c = ψ hA (2*r+1)) (rfl : K = ψ hP (r+1))
  have hup := NativeHalfBinomial.upper_estimate_scaled hX hY (by omega : 1 ≤ r) rfl hA rfl hP
    (rfl : c = ψ hA (2*r+1)) (rfl : K = ψ hP (r+1))
    hξY h72 h16
  have hloR : (K:ℝ)*((X:ℝ)+1)^(2*r) < (c:ℝ)*(X:ℝ)^r := by
    exact_mod_cast hlo
  have hlow : (2*K*Y:ℝ) < c := by
    rw [hfloorR] at hloR
    have hn : (0:ℝ) ≤ K*v := by positivity
    have hh : (2*K*Y:ℝ)*(X:ℝ)^r < c*(X:ℝ)^r := by nlinarith
    exact (mul_lt_mul_iff_left₀ hXR).mp (by nlinarith only [hh])
  have hupper : (c:ℝ) < (2*K*(Y+1):ℝ) := by
    rw [hξ] at hup
    have hh : (c:ℝ)/K < 2*(Y+1) := by linarith
    have hh' := (div_lt_iff₀ hKR).mp hh
    nlinarith only [hh']
  exact ⟨by exact_mod_cast hlow,by exact_mod_cast hupper⟩

/-- All coordinates needed for the native outer Pell and index rows.
The named registers are retained with exact defining equations. -/
structure Seed (u R : ℕ) where
  s : ℕ
  Y : ℕ
  a : ℕ
  k : ℕ
  c : ℕ
  D : ℕ
  tau : ℕ
  h : ℕ
  eta : ℕ
  zeta : ℕ
  gamma : ℕ
  s_pos : 0 < s
  Y_pos : 0 < Y
  a_pos : 0 < a
  k_pos : 0 < k
  c_pos : 0 < c
  D_pos : 0 < D
  tau_pos : 0 < tau
  h_pos : 0 < h
  eta_pos : 0 < eta
  zeta_pos : 0 < zeta
  gamma_pos : 0 < gamma
  scale : Y = s*(2^u)^3
  base : a = Y*(2^R+1)
  split : k = eta+zeta
  interval : c = k*Y+eta
  index : k = 1+R+(2^R*Y)*h
  root : D = 2^R+a*c+gamma*(4*a+3)
  first_norm : tau^2 = 1+(2^R*Y^2)*(2^R*Y^2+1)*k^2
  main_norm : D^2 = 1+((a+2)^2-1)*c^2
  main_index : c = yn (by omega : 1 < a+2) R

/-- The fresh native outer seed, constructed from odd rank and its exact
population alone. All later auxiliary and scalar bindings are separate. -/
theorem exists_outer_seed (u R r : ℕ) (hu : 0 < u) (hR : R = 2*r+1)
    (hpop : σ 2 R = 3*u+2) : Nonempty (Seed u R) := by
  obtain ⟨hσ,hr,hsize⟩ := population_sizes hu hR hpop
  obtain ⟨s,Y,v,hs,hY,hscale,hfloor,hv⟩ := scaled_half_floor hu hR hpop
  let X := 2^R
  have hX : 1 ≤ X := Nat.one_le_two_pow
  have hRX : R < X := Nat.lt_two_pow_self
  have hX16 : 16 ≤ X := by
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) (by omega : 4 ≤ R)
  let a := Y*(X+1)
  have ha : 0 < a := Nat.mul_pos hY (by omega)
  have hA : 1 < a+2 := by omega
  let Q := X*Y^2
  have hQ : 0 < Q := Nat.mul_pos (by omega) (pow_pos hY _)
  let P := 2*Q+1
  have hP : 1 < P := by dsimp [P]; omega
  let K := yn hP (r+1)
  let k := 2*K
  let tau := xn hP (r+1)
  let c := yn hA R
  let D := xn hA R
  have hK : 0 < K := lt_of_lt_of_le (Nat.succ_pos r) (yn_ge_n hP _)
  have hk : 0 < k := by dsimp [k]; omega
  have htau : 0 < tau := xn_pos' hP _
  have hc : 0 < c := JSWW1976.ψ_pos_of_pos hA (by omega)
  have hD : 0 < D := xn_pos' hA _
  have h72 : 72*r < X+1 := by
    have hh := NativeHalfBinomial.seventy_two_mul_lt_two_pow hr
    dsimp [X]
    rw [hR]
    omega
  have h16 : 16 ≤ Y*(X+1) := by nlinarith only [hY,hX16]
  obtain ⟨hlo,hhi⟩ := pell_interval hX hY hr hfloor hv h72 h16
  change k*Y < yn hA (2*r+1) at hlo
  change yn hA (2*r+1) < k*(Y+1) at hhi
  rw [← hR] at hlo hhi
  change k*Y < c at hlo
  change c < k*(Y+1) at hhi
  let eta := c-k*Y
  let zeta := k-eta
  have heta : 0 < eta := Nat.sub_pos_of_lt hlo
  have hinter : c = k*Y+eta := by dsimp [eta]; omega
  have hetak : eta < k := by nlinarith only [hinter,hhi]
  have hzeta : 0 < zeta := Nat.sub_pos_of_lt hetak
  have hsplit : k = eta+zeta := by dsimp [zeta]; omega
  let E := X*Y
  have hE : 0 < E := Nat.mul_pos (by omega) hY
  have hdiv : E ∣ P-1 := by
    refine ⟨2*Y,?_⟩
    have he : P = E*(2*Y)+1 := by dsimp [P,Q,E]; ring
    omega
  have hmod : k ≡ R+1 [MOD E] := by
    have hh := (Nat.ModEq.of_dvd hdiv (yn_modEq_a_sub_one hP (r+1))).mul_left 2
    change 2*K ≡ 2*(r+1) [MOD E] at hh
    simpa only [k,hR,show 2*r+1+1 = 2*(r+1) by ring] using hh
  have hKr : r+1 < K := by
    have hp : 2*P-1 ≤ K := by
      calc
        2*P-1 = (2*P-1)^1 := (pow_one _).symm
        _ ≤ (2*P-1)^r := Nat.pow_le_pow_right (by omega) (by omega)
        _ ≤ K := pow_le_ψ_succ hP r
    have hXY : X ≤ Q := by
      dsimp [Q]
      exact Nat.le_mul_of_pos_right _ (pow_pos hY _)
    have hXP : 2*X+1 ≤ P := by dsimp [P]; omega
    omega
  have hkR : R+1 < k := by dsimp [k]; omega
  obtain ⟨h,hh⟩ := (Nat.modEq_iff_dvd' hkR.le).mp hmod.symm
  have hh0 : 0 < h := by
    by_contra hn
    have : h = 0 := by omega
    rw [this,mul_zero] at hh
    omega
  have hindex : k = 1+R+E*h := by omega
  have hcX : X < c := by
    have hbase : X < 2*(a+2)-1 := by
      have he : 2*(a+2)-1 = 2*a+3 := by omega
      rw [he]
      dsimp [a]
      nlinarith only [hY,hX]
    have hp : 2*(a+2)-1 ≤ c := by
      calc
        2*(a+2)-1 = (2*(a+2)-1)^1 := (pow_one _).symm
        _ ≤ (2*(a+2)-1)^(R-1) := Nat.pow_le_pow_right (by omega) (by omega)
        _ ≤ c := by
          have hh := pow_le_ψ_succ hA (R-1)
          simpa only [Nat.sub_add_cancel (by omega : 1 ≤ R)] using hh
    omega
  have hrootlarge : X+a*c < D := by
    have hg := χ_gt hA R
    change (a+2-1)*c < D at hg
    have he : a+2-1 = a+1 := by omega
    rw [he] at hg
    nlinarith only [hg,hcX]
  have hrootmod : D ≡ X+a*c [MOD 4*a+3] := by
    have hh := χ_modEq_pow hA (by decide : 0 < (2:ℕ)) (by omega : 2 ≤ a+2) R
    have hm : 2*(a+2)*2-2*2-1 = 4*a+3 := by omega
    have hb : a+2-2 = a := by omega
    rw [hm,hb] at hh
    change D ≡ X+c*a [MOD 4*a+3] at hh
    simpa only [Nat.mul_comm c a] using hh
  obtain ⟨gamma,hgamma⟩ := (Nat.modEq_iff_dvd' hrootlarge.le).mp hrootmod.symm
  have hgamma0 : 0 < gamma := by
    by_contra hn
    have : gamma = 0 := by omega
    rw [this,mul_zero] at hgamma
    omega
  have hroot : D = X+a*c+gamma*(4*a+3) := by
    rw [mul_comm gamma]
    omega
  have hnorm : tau^2 = 1+Q*(Q+1)*k^2 := by
    have hh := χ_sq hP (r+1)
    change tau*tau = (P*P-1)*K*K+1 at hh
    have hp : P*P-1 = 4*Q*(Q+1) := by
      have he : P*P = 4*Q*(Q+1)+1 := by dsimp [P]; ring
      omega
    rw [hp] at hh
    dsimp [k]
    nlinarith only [hh]
  have hmain : D^2 = 1+((a+2)^2-1)*c^2 := by
    have hh := χ_sq hA R
    change D*D = ((a+2)*(a+2)-1)*c*c+1 at hh
    simpa only [pow_two,Nat.mul_assoc,Nat.add_comm] using hh
  exact ⟨⟨s,Y,a,k,c,D,tau,h,eta,zeta,gamma,hs,hY,ha,hk,hc,hD,htau,hh0,
    heta,hzeta,hgamma0,hscale,rfl,hsplit,hinter,hindex,hroot,hnorm,hmain,rfl⟩⟩

end DiophantineConsistency.NativeOuterSeedConstruction
