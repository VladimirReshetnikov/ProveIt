import DiophantineConsistency.NativeAdaptiveCarrierBootstrap
import DiophantineConsistency.NativeAdaptiveFactorThree

/-! The literal adaptive main carrier, before rank-window or index recovery.
All carrier cuts are signed integers. Positivity of the integral main root
is proved from the input hypotheses, not imposed by choosing its sign. -/

set_option autoImplicit false
set_option Elab.async false

namespace DiophantineConsistency.NativeAdaptiveMainBootstrap

def target (q F alpha J MC MF : ℤ) : ℤ :=
  ((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J

def mainDstar (q X Y k eta gamma v : ℤ) : ℤ :=
  let a := Y*(X+1)
  let c := k*Y+eta
  let H := 4*a+3
  let U := q^2*Y
  U*(X+a*c)+H*(U*gamma+q*X*Y-v)

def mainA1 (q X Y k eta gamma v : ℤ) : ℤ :=
  mainDstar q X Y k eta gamma v ^ 2 -
    (q^2*Y)^2 * (1+((Y*(X+1)+2)^2-1)*(k*Y+eta)^2)

/-- Only the lower target bound is needed here, not a restored source rank
or an upper window. MF is already the source-shifted port. -/
theorem target_positive {q F alpha J MC MF : ℤ}
    (hq : 1 < q) (halpha : 0 < alpha) (hJ : 0 < J)
    (hMC : 0 ≤ MC) (hMF : 0 ≤ MF) (hC : 0 < q-F-alpha) :
    0 < target q F alpha J MC MF := by
  have hqF : 0 < q-F := by omega
  have hcoef : 0 < (q-1)*(q-F)+alpha := by positivity
  have hq2 : 0 < q^2-1 := by nlinarith
  exact add_pos_of_pos_of_nonneg (mul_pos hcoef hq2) (by positivity)

/-- A positive first-carrier transport supplies the target's gap premise. -/
theorem target_positive_of_transport {q K X F alpha J MC MF Bt : ℤ}
    (hq : 1 < q) (hK : 0 ≤ K) (hX : 0 < X) (hF : 0 < F)
    (halpha : 0 < alpha) (hJ : 0 < J) (hMC : 0 ≤ MC) (hMF : 0 ≤ MF)
    (hBt : Bt = (q*K+X)*(q-F-alpha)-q*F) (hpos : 0 < Bt) :
    0 < target q F alpha J MC MF := by
  exact target_positive hq halpha hJ hMC hMF
    (NativeAdaptiveCarrierBootstrap.transport_positive (by omega) hK hX hF hBt hpos)

/-- The actual signed main carrier is positive even when v is negative.
The weak structural inequality v<k replaces every later rank-window bound. -/
theorem mainDstar_positive {q X Y k eta gamma v : ℤ}
    (hq : 1 < q) (hX : 0 < X) (hY : 0 < Y)
    (hk : 0 < k) (heta : 0 < eta) (hgamma : 0 < gamma)
    (hYdiv : q^3 ∣ Y) (hv : v < k) :
    0 < mainDstar q X Y k eta gamma v := by
  have hqpos : 0 < q := by omega
  have hq2 : (4 : ℤ) ≤ q^2 := by nlinarith
  have hq3 : (8 : ℤ) ≤ q^3 := by
    calc
      (8 : ℤ) = 2*4 := by norm_num
      _ ≤ q*q^2 := mul_le_mul (by omega) hq2 (by norm_num) hqpos.le
      _ = q^3 := by ring
  obtain ⟨s,hs⟩ := hYdiv
  have hspos : 0 < s := (mul_pos_iff_of_pos_left (pow_pos hqpos 3)).mp (by rwa [← hs])
  have hYlarge : (8 : ℤ) ≤ Y := by
    calc
      (8 : ℤ) ≤ q^3 := hq3
      _ ≤ q^3*s := le_mul_of_one_le_right (by positivity) (by omega)
      _ = Y := hs.symm
  let a := Y*(X+1)
  let H := 4*a+3
  let U := q^2*Y
  have ha : (4 : ℤ) ≤ a := by
    dsimp [a]
    have hp := mul_nonneg (show 0 ≤ Y-2 by omega) (show 0 ≤ X-1 by omega)
    nlinarith
  have hH : 0 < H := by dsimp [H]; omega
  have hU : 0 < U := by dsimp [U]; positivity
  have hY2 : (4 : ℤ) ≤ Y^2 := by nlinarith
  have hqY2 : (16 : ℤ) ≤ q^2*Y^2 :=
    mul_le_mul hq2 hY2 (by norm_num) (by positivity)
  have hB : 0 < U*a*Y-H := by
    have hp : (48 : ℤ) ≤ a*(q^2*Y^2-4) := by
      calc
        (48 : ℤ) = 4*12 := by norm_num
        _ ≤ a*(q^2*Y^2-4) := mul_le_mul ha
          (show (12 : ℤ) ≤ q^2*Y^2-4 by linarith) (by norm_num) (by omega)
    have he : U*a*Y-H = a*(q^2*Y^2-4)-3 := by dsimp [U,H]; ring
    rw [he]
    linarith
  have hshift : 0 < U*gamma+q*X*Y+k-v := by
    have hp : 0 < U*gamma := mul_pos hU hgamma
    have hp' : 0 < q*X*Y := mul_pos (mul_pos hqpos hX) hY
    linarith
  calc
    (0 : ℤ) < k*(U*a*Y-H)+(U*X+U*a*eta+H*(U*gamma+q*X*Y+k-v)) := by
      have ha' : 0 < a := by omega
      positivity
    _ = mainDstar q X Y k eta gamma v := by dsimp [mainDstar,U,H,a]; ring

/-- Cast a positive signed main norm into the generic natural Pell
classification. This retains D itself, not its absolute value. -/
theorem classify_positive_main_norm {a c D : ℤ}
    (ha : 0 ≤ a) (hc : 0 < c) (hD : 0 < D)
    (hnorm : D^2 = 1+((a+2)^2-1)*c^2) :
    ∃ p : ℕ, 0 < p ∧
      D = (Pell.xn (by omega : 1 < a.toNat+2) p : ℤ) ∧
      c = (Pell.yn (by omega : 1 < a.toNat+2) p : ℤ) := by
  have hac : (a.toNat : ℤ) = a := Int.toNat_of_nonneg ha
  have hcc : (c.toNat : ℤ) = c := Int.toNat_of_nonneg hc.le
  have hDc : (D.toNat : ℤ) = D := Int.toNat_of_nonneg hD.le
  have hz : (D.toNat : ℤ)^2 =
      1+((a.toNat : ℤ)^2+4*a.toNat+3)*(c.toNat : ℤ)^2 := by
    rw [hac,hcc,hDc]
    nlinarith [hnorm]
  have hn : D.toNat^2 = 1+(a.toNat^2+4*a.toNat+3)*c.toNat^2 := by
    exact_mod_cast hz
  have hdelta : (a.toNat+2)^2-1 = a.toNat^2+4*a.toNat+3 := by
    have he : (a.toNat+2)^2 = (a.toNat^2+4*a.toNat+3)+1 := by ring
    omega
  have hnormN : D.toNat^2 = 1+((a.toNat+2)^2-1)*c.toNat^2 := by rwa [hdelta]
  obtain ⟨p,hp,hd,hc'⟩ := NativePellBootstrap.main_classification (by omega) hnormN
  refine ⟨p,hp,?_,?_⟩
  · simpa only [hDc] using congrArg (fun z : ℕ => (z : ℤ)) hd
  · simpa only [hcc] using congrArg (fun z : ℕ => (z : ℤ)) hc'

/-- A1 supplies a positive integral main Pell solution and q^4|v. No
source, window, index comparison, or coprimality premise is present. -/
theorem main_carrier_bootstrap {q X Y k eta gamma v : ℤ}
    (hq : 1 < q) (hX : 0 < X) (hY : 0 < Y)
    (hk : 0 < k) (heta : 0 < eta) (hgamma : 0 < gamma)
    (hYdiv : q^3 ∣ Y) (hv : v < k)
    (h1 : mainA1 q X Y k eta gamma v = 0) :
    let a := Y*(X+1)
    let c := k*Y+eta
    ∃ D : ℤ, 0 < D ∧
      mainDstar q X Y k eta gamma v = q^2*Y*D ∧
      D^2 = 1+((a+2)^2-1)*c^2 ∧ q^4 ∣ v ∧
      ∃ p : ℕ, 0 < p ∧
        D = (Pell.xn (by omega : 1 < a.toNat+2) p : ℤ) ∧
        c = (Pell.yn (by omega : 1 < a.toNat+2) p : ℤ) := by
  let a := Y*(X+1)
  let c := k*Y+eta
  let H := 4*a+3
  let U := q^2*Y
  let Ds := mainDstar q X Y k eta gamma v
  have hqpos : 0 < q := by omega
  have ha : 0 < a := by dsimp [a]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hU : 0 < U := by dsimp [U]; positivity
  have hDs : 0 < Ds := mainDstar_positive hq hX hY hk heta hgamma hYdiv hv
  have hnorm : Ds^2 = U^2*(1+((a+2)^2-1)*c^2) := by
    change Ds^2-U^2*(1+((a+2)^2-1)*c^2)=0 at h1
    exact sub_eq_zero.mp h1
  have hdiv : U ∣ Ds := (Int.pow_dvd_pow_iff two_ne_zero).mp
    ⟨1+((a+2)^2-1)*c^2,hnorm⟩
  obtain ⟨D,hD⟩ := hdiv
  have hDpos : 0 < D := (mul_pos_iff_of_pos_left hU).mp (by rwa [← hD])
  have hn : D^2 = 1+((a+2)^2-1)*c^2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hU.ne')
    calc
      U^2*D^2=Ds^2 := by rw [← mul_pow,← hD]
      _ = U^2*(1+((a+2)^2-1)*c^2) := hnorm
  have ht : H*(q*X*Y-v)=U*(D-X-a*c-H*gamma) := by
    have he : Ds = U*(X+a*c)+H*(U*gamma+q*X*Y-v) := rfl
    linear_combination hD - he
  have hUdiv : q^5 ∣ U := by
    obtain ⟨s,hs⟩ := hYdiv
    exact ⟨s,by dsimp [U]; rw [hs]; ring⟩
  have hvdiv : q^4 ∣ v := NativeAdaptiveFactorThree.index_difference_dvd (X := X) hYdiv
    (dvd_trans hUdiv ⟨D-X-a*c-H*gamma,by simpa only [H,a,mul_assoc] using ht⟩)
  obtain ⟨p,hp,hd,hc'⟩ := classify_positive_main_norm ha.le hc hDpos hn
  exact ⟨D,hDpos,hD,hn,hvdiv,p,hp,hd,hc'⟩

/-- The actual target substitutes for v and derives v<k. Still no target
upper bound, source rank, or congruence condition on J is supplied. -/
theorem main_carrier_of_target {q X Y k eta gamma F alpha J MC MF : ℤ}
    (hq : 1 < q) (hX : 0 < X) (hY : 0 < Y)
    (hk : 0 < k) (heta : 0 < eta) (hgamma : 0 < gamma)
    (hYdiv : q^3 ∣ Y) (halpha : 0 < alpha) (hJ : 0 < J)
    (hMC : 0 ≤ MC) (hMF : 0 ≤ MF) (hC : 0 < q-F-alpha)
    (h1 : mainA1 q X Y k eta gamma (k-target q F alpha J MC MF-1)=0) :
    let a := Y*(X+1)
    let c := k*Y+eta
    ∃ D : ℤ, 0 < D ∧
      mainDstar q X Y k eta gamma (k-target q F alpha J MC MF-1)=q^2*Y*D ∧
      D^2=1+((a+2)^2-1)*c^2 ∧ q^4 ∣ k-target q F alpha J MC MF-1 ∧
      ∃ p : ℕ, 0 < p ∧
        D=(Pell.xn (by omega : 1 < a.toNat+2) p : ℤ) ∧
        c=(Pell.yn (by omega : 1 < a.toNat+2) p : ℤ) := by
  have hR := target_positive hq halpha hJ hMC hMF hC
  exact main_carrier_bootstrap hq hX hY hk heta hgamma hYdiv (by omega) h1

end DiophantineConsistency.NativeAdaptiveMainBootstrap
