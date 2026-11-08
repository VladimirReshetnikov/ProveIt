import DiophantineConsistency.BFS943.TransportOrder

/-! # Size of package 194's first-product centre `Ω₂` (ordered-ring core)

Write `x = A`, `u = U`, `e = E`, `U² b` for `θ`, and

  `Ω = u (2x (e V - u² b (e² + S²)) + S (4 u² b e - (b - c)))`,  `V = F b - c`,
  `F = 1 + 2 (x² - 1) u² e`,

with `x ≥ 2`, `u, e ≥ 1`, `0 < c ≤ u`, `0 ≤ S ≤ e` (package 194 §4; `S` is the
first-product remainder, `|V| = V0`). Then, for every integer `b`,

* `omega_upper`: `Ω ≤ 3 x u e V0` (package 194's (11) in the direction used
  by the sign argument; the three cases `b ≥ 1`, `b = 0`, `b ≤ -1` are
  treated separately, no sign of `V` is assumed);
* `omega_nonneg`: `0 ≤ Ω` when `b ≥ 1` (the completeness direction);
* `three_lt_five`: `3 x u e < 5 g` when `g² = e (1 + (x² - 1) u² e)`
  (`G = E F0`), since `25 G - 9 x² u² e² = 25 e + (16 x² - 25) u² e² > 0`.

The estimates are crude (they lose a factor `x²`), which is all the transport
argument needs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace111Estimate
variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The centre `Ω₂` as a function of its scalar inputs. -/
def omegaOf (x u e S c b Vs : K) : K :=
  u*((x+x)*(e*Vs-u*u*b*(e*e+S*S))+S*(4*(u*u*b*e)-(b-c)))

set_option maxHeartbeats 1000000 in
theorem omega_upper (x u e S c b Vs V0 : K)
    (hx : 2≤x) (hu : 1≤u) (he : 1≤e) (hc : 0<c) (hcu : c≤u) (hS0 : 0≤S) (hSe : S≤e)
    (hV : Vs=(1+2*((x*x-1)*(u*u*e)))*b-c) (hV0 : Vs*Vs=V0*V0) (hV0n : 0≤V0)
    (hdisc : ∀ y : K, 0<y → 1≤y) :
    omegaOf x u e S c b Vs≤3*(x*u*e)*V0 := by
  have hu0 : 0≤u := by linarith
  have he0 : 0≤e := by linarith
  have hx0 : 0≤x := by linarith
  have hue : 0≤u*e := mul_nonneg hu0 he0
  have hxue : 0≤x*u*e := mul_nonneg (mul_nonneg hx0 hu0) he0
  have huu : 1≤u*u := one_le_mul_of_one_le_of_one_le hu hu
  have huue : 1≤u*u*e := one_le_mul_of_one_le_of_one_le huu he
  have hue1 : 1≤u*e := one_le_mul_of_one_le_of_one_le hu he
  have hxx : 2*x≤x*x := mul_le_mul_of_nonneg_right hx hx0
  have hx2 : 3≤x*x-1 := by linarith
  have hF : 1+6*(u*u*e)≤1+2*((x*x-1)*(u*u*e)) := by
    have := mul_le_mul_of_nonneg_right hx2 (by linarith : (0:K)≤u*u*e)
    linarith
  have hSS : S*S≤e*e := mul_self_le_mul_self hS0 hSe
  have huc : u≤u*u*e := by
    have := le_mul_of_one_le_right hu0 hue1
    linarith
  unfold omegaOf
  rcases lt_trichotomy b 0 with hneg|hzero|hpos
  · -- b ≤ -1: V < 0, V0 = -V
    obtain ⟨W,hW⟩ : ∃ W : K, W=-b := ⟨-b,rfl⟩
    have hW1 : 1≤W := hdisc W (by rw [hW]; linarith)
    have hW0 : 0≤W := by linarith
    have hbW : b=-W := by rw [hW]; ring
    subst hbW
    set F : K := 1+2*((x*x-1)*(u*u*e)) with hFdef
    have hF1 : 1≤F := by linarith
    have hVs : Vs=-(F*W+c) := by rw [hV]; ring
    have hFW1 : 1≤F*W := one_le_mul_of_one_le_of_one_le hF1 hW1
    have hV0eq : V0=F*W+c := by
      have hsq : (V0-(F*W+c))*(V0+(F*W+c))=0 := by
        have h := hV0; rw [hVs] at h; linear_combination -h
      rcases mul_eq_zero.mp hsq with h|h
      · linear_combination h
      · exfalso; linarith
    have huuuW : 0≤u*u*u*W := mul_nonneg (mul_nonneg (mul_nonneg hu0 hu0) hu0) hW0
    have t1 : u*((x+x)*(e*Vs))=-(2*(x*u*e)*V0) := by rw [hVs,hV0eq]; ring
    have t2 : u*((x+x)*(-(u*u*(-W)*(e*e+S*S))))≤4*(x*u*e)*(u*u*e*W) := by
      have h1 : (0:K)≤(x+x)*(u*u*u*W) := mul_nonneg (by linarith) huuuW
      have := mul_le_mul_of_nonneg_left (add_le_add_left hSS (e*e)) h1
      linarith
    have t3 : u*(S*(4*(u*u*(-W)*e)))≤0 := by
      have h1 : 0≤u*u*W*e := mul_nonneg (mul_nonneg (mul_nonneg hu0 hu0) hW0) he0
      have : 0≤u*(S*(4*(u*u*W*e))) := mul_nonneg hu0 (mul_nonneg hS0 (by linarith))
      linarith
    have t4 : u*(S*(-(-W-c)))≤u*e*(W+c) := by
      have h1 : u*(S*(W+c))≤u*(e*(W+c)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hSe (by linarith)) hu0
      linarith
    have hV0big : u*e*(W+c)+4*(x*u*e)*(u*u*e*W)≤5*(x*u*e)*V0 := by
      rw [hV0eq]
      have hFW : 6*(u*u*e)*W≤(F-1)*W := mul_le_mul_of_nonneg_right (by linarith) hW0
      have h1 : x*u*e*(6*(u*u*e)*W)≤x*u*e*((F-1)*W) := mul_le_mul_of_nonneg_left hFW hxue
      have h2 : 1*(u*e*(W+c))≤x*(u*e*(W+c)) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hue (by linarith))
      have h3 : 0≤x*u*e*(u*u*e*W) := mul_nonneg hxue (mul_nonneg (by linarith) hW0)
      have h4 : 0≤x*u*e*W := mul_nonneg hxue hW0
      have h5 : 0≤x*u*e*c := mul_nonneg hxue hc.le
      linarith
    have hsplit : u*((x+x)*(e*Vs-u*u*(-W)*(e*e+S*S))+S*(4*(u*u*(-W)*e)-(-W-c)))=
        u*((x+x)*(e*Vs))+u*((x+x)*(-(u*u*(-W)*(e*e+S*S))))+u*(S*(4*(u*u*(-W)*e)))+
          u*(S*(-(-W-c))) := by ring
    rw [hsplit]
    linarith
  · -- b = 0
    subst hzero
    have hVs : Vs=-c := by rw [hV]; ring
    subst hVs
    have h2 : S-(x+x)*e≤0 := by
      have := mul_le_mul_of_nonneg_right (show (1:K)≤x+x by linarith) he0
      linarith
    have h3 : u*c*(S-(x+x)*e)≤0 := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hu0 hc.le) h2
    have h4 : 0≤3*(x*u*e)*V0 := mul_nonneg (mul_nonneg (by norm_num) hxue) hV0n
    linarith
  · -- b ≥ 1: V > 0, V0 = V
    have hb1 : 1≤b := hdisc b hpos
    have hb0 : 0≤b := by linarith
    set F : K := 1+2*((x*x-1)*(u*u*e)) with hFdef
    have hF1 : 1≤F := by linarith
    have hP : c≤u*u*e*b := by
      have h2 : u*u*e≤u*u*e*b := le_mul_of_one_le_right (by linarith) hb1
      linarith
    have hVpos : 0<Vs := by
      rw [hV]
      have : F≤F*b := le_mul_of_one_le_right (by linarith) hb1
      linarith
    have hV0eq : V0=Vs := by
      have hsq : (V0-Vs)*(V0+Vs)=0 := by linear_combination -hV0
      rcases mul_eq_zero.mp hsq with h|h
      · linear_combination h
      · exfalso; linarith
    rw [hV0eq]
    have huub : 0≤u*u*b := mul_nonneg (mul_nonneg hu0 hu0) hb0
    have t2 : u*((x+x)*(-(u*u*b*(e*e+S*S))))≤0 := by
      have : 0≤u*((x+x)*(u*u*b*(e*e+S*S))) := mul_nonneg hu0 (mul_nonneg (by linarith)
        (mul_nonneg huub (add_nonneg (mul_self_nonneg e) (mul_self_nonneg S))))
      linarith
    have t3 : u*(S*(4*(u*u*b*e)-(b-c)))≤u*e*(4*(u*u*b*e)+c) := by
      have h0 : 0≤u*u*b*e := mul_nonneg huub he0
      have h1 : u*(S*(4*(u*u*b*e)+c))≤u*(e*(4*(u*u*b*e)+c)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hSe (by linarith)) hu0
      have h2 : 0≤u*(S*b) := mul_nonneg hu0 (mul_nonneg hS0 hb0)
      linarith
    have hkey : 4*(u*u*b*e)+c≤x*Vs := by
      rw [hV]
      set P : K := u*u*e*b with hPdef
      have hpoly : 0≤2*x*x*x-3*x-5 := by
        have := mul_nonneg (show (0:K)≤x-2 by linarith)
          (show (0:K)≤2*x*x+4*x+5 by nlinarith)
        linarith
      have h1 : 0≤(2*x*x*x-3*x-5)*P := mul_nonneg hpoly (by linarith)
      have h2 : (x+1)*c≤(x+1)*P := mul_le_mul_of_nonneg_left hP (by linarith)
      have h3 : 0≤x*b := mul_nonneg hx0 hb0
      have hexp : x*(F*b-c)-(4*(u*u*b*e)+c)=(2*x*x*x-3*x-5)*P+(x+1)*(P-c)+x*b := by
        rw [hFdef,hPdef]; ring
      linarith
    have hmain : u*e*(4*(u*u*b*e)+c)≤u*e*(x*Vs) := mul_le_mul_of_nonneg_left hkey hue
    have hsplit : u*((x+x)*(e*Vs-u*u*b*(e*e+S*S))+S*(4*(u*u*b*e)-(b-c)))=
        2*(x*u*e)*Vs+u*((x+x)*(-(u*u*b*(e*e+S*S))))+u*(S*(4*(u*u*b*e)-(b-c))) := by ring
    rw [hsplit]
    linarith

set_option maxHeartbeats 1000000 in
theorem omega_nonneg (x u e S c b Vs : K)
    (hx : 2≤x) (hu : 1≤u) (he : 1≤e) (hc : 0<c) (hcu : c≤u) (hS0 : 0≤S) (hSe : S≤e)
    (hV : Vs=(1+2*((x*x-1)*(u*u*e)))*b-c) (hb1 : 1≤b) :
    0≤omegaOf x u e S c b Vs := by
  have hu0 : 0≤u := by linarith
  have he0 : 0≤e := by linarith
  have hx0 : 0≤x := by linarith
  have hb0 : 0≤b := by linarith
  have hue : 0≤u*e := mul_nonneg hu0 he0
  have hue1 : 1≤u*e := one_le_mul_of_one_le_of_one_le hu he
  have hSS : S*S≤e*e := mul_self_le_mul_self hS0 hSe
  have huub : 0≤u*u*b := mul_nonneg (mul_nonneg hu0 hu0) hb0
  have hP : c≤u*u*e*b := by
    have h1 : u≤u*(u*e) := le_mul_of_one_le_right hu0 hue1
    have h2 : u*u*e≤u*u*e*b := le_mul_of_one_le_right (mul_nonneg (mul_nonneg hu0 hu0) he0) hb1
    linarith
  unfold omegaOf
  have t2 : u*((x+x)*(u*u*b*(e*e+S*S)))≤u*e*((x+x)*(u*u*b*(e+e))) := by
    have h1 : (0:K)≤u*((x+x)*(u*u*b)) := mul_nonneg hu0 (mul_nonneg (by linarith) huub)
    have := mul_le_mul_of_nonneg_left (add_le_add_left hSS (e*e)) h1
    linarith
  have t3 : u*(S*b)≤u*e*b := by
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hSe hb0) hu0
    linarith
  have t4 : 0≤u*(S*(4*(u*u*b*e)+c)) :=
    mul_nonneg hu0 (mul_nonneg hS0 (by have := mul_nonneg huub he0; linarith))
  have hkey : (x+x)*(u*u*b*(e+e))+b≤(x+x)*Vs := by
    rw [hV]
    set P : K := u*u*e*b with hPdef
    have hpoly : 0≤4*x*x*x-12*x := by
      have := mul_nonneg (show (0:K)≤x-2 by linarith)
        (show (0:K)≤4*x*x+8*x+4 by nlinarith)
      linarith
    have h1 : 0≤(4*x*x*x-12*x)*P := mul_nonneg hpoly (by linarith)
    have h2 : 2*x*c≤2*x*P := mul_le_mul_of_nonneg_left hP (by linarith)
    have h3 : 0≤(2*x-1)*b := mul_nonneg (by linarith) hb0
    have h4 : 0≤2*x*P := mul_nonneg (by linarith) (by linarith)
    have hexp : (x+x)*((1+2*((x*x-1)*(u*u*e)))*b-c)-((x+x)*(u*u*b*(e+e))+b)=
        (4*x*x*x-12*x)*P+2*x*(P-c)+(2*x-1)*b+2*x*P := by rw [hPdef]; ring
    linarith
  have hmain : u*e*((x+x)*(u*u*b*(e+e))+b)≤u*e*((x+x)*Vs) := mul_le_mul_of_nonneg_left hkey hue
  have hsplit : u*((x+x)*(e*Vs-u*u*b*(e*e+S*S))+S*(4*(u*u*b*e)-(b-c)))=
      u*e*((x+x)*Vs)-u*((x+x)*(u*u*b*(e*e+S*S)))-u*(S*b)+u*(S*(4*(u*u*b*e)+c)) := by ring
  rw [hsplit]
  linarith

theorem three_lt_five (x u e g : K) (hx : 2≤x) (hu : 1≤u) (he : 1≤e) (hg : 0≤g)
    (hG : g*g=e*(1+(x*x-1)*(u*u)*e)) : 3*(x*u*e)<5*g := by
  have hu0 : 0≤u := by linarith
  have he0 : 0≤e := by linarith
  have hx0 : 0≤x := by linarith
  have h3 : 0≤3*(x*u*e) := mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hx0 hu0) he0)
  apply lt_of_mul_self_lt_mul_self₀ (by linarith)
  have hxx : 2*x≤x*x := mul_le_mul_of_nonneg_right hx hx0
  have hgap : 25*(e*(1+(x*x-1)*(u*u)*e))-(3*(x*u*e))*(3*(x*u*e))=
      25*e+(u*e)*(u*e)*(16*(x*x)-25) := by ring
  have hpoly : 0<16*(x*x)-25 := by linarith
  have hpos : 0<25*e+(u*e)*(u*e)*(16*(x*x)-25) := by
    have := mul_nonneg (mul_self_nonneg (u*e)) (le_of_lt hpoly)
    linarith
  have h5 : (5*g)*(5*g)=25*(g*g) := by ring
  rw [h5,hG]
  linarith

#print axioms Trace111Estimate.omega_upper
#print axioms Trace111Estimate.omega_nonneg
#print axioms Trace111Estimate.three_lt_five
end Trace111Estimate
