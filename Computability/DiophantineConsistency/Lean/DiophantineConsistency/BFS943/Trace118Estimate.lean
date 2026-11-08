import DiophantineConsistency.BFS943.TransportOrder

/-! # Size of package 193's whole-product centre and of its weighted transport

Ordered-ring core of package 193 (`193-transport-and-pell-reuse/positive/PROOF.md`
§§3–6). Write `x = A`, `u = U`, `e = E`, `θ = u² b`, and

  `Ω = u (x (4 e V - θ (4 e² + 3 S² + e₂²)) + 2 S (θ (3 e + e₂) - (b - c)))`,
  `V = F b - c`, `F = 1 + 2 (x² - 1) u² e`,

with `x ≥ 2`, `u, e ≥ 1`, `0 < c ≤ u`, `0 ≤ S ≤ e`, `0 ≤ e₂ ≤ e` (`S` is the
whole-product quotient remainder, `e₂ = (k Ybar)²`, `V0 = |V|`). Then

* `omega_upper`: `Ω ≤ 5 x u e V0` for every integer `b` (package 193 §3 in the
  direction used by the sign argument; the three cases `b ≥ 1`, `b = 0`,
  `b ≤ -1` are treated separately, no sign of `V` is assumed);
* `omega_nonneg`: `0 ≤ Ω` when `b ≥ 1` (the completeness direction);
* `g_le`: `g ≤ x u e` when `g² = e (1 + (x² - 1) u² e)` (`G = E F0`);
* `weighted_estimate`: package 193 §4. From the adjacent Pell norm
  `(1 + B) V0² = 1 + B y²` (`B = Q - 1`) alone, `b ≠ 0`, `y < 2 V0` and
  `F |b| > 2 B - c`; with the size hypothesis `52 e F² + u² c < 2 u² B` this
  gives `u² |b| > 52 e F`, hence for a shift `ws ≤ 5 x u e V0`
  `2 (4 g y + ws) < 26 x u e V0 < 52 x u e F |b| ≤ x u³ b²`, the new transport
  weight `L = A U³ b²`;
* `size_bound`: the size hypothesis from `Δ = x² - 1 ≥ 48`, `e ≤ u²`,
  `1 ≤ c ≤ u`, `a = Δ u² e`, `F = 1 + 2 a`, `B = Δ (4 a (1 + a)) - 1`;
* `complete_bounds`: the bounds `K < 2 g`, `-eclear < 2 g` used to keep the
  completeness coordinate `n` positive (package 193 §6), from the first-index
  size `8 v + 4 ≤ k` and `c² E ≤ g`.

The estimates are crude, which is all the transport argument needs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace118Estimate
variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The whole-product centre `Ω` as a function of its scalar inputs. -/
def omegaOf (x u e S e2 c b Vs : K) : K :=
  u*(x*(4*(e*Vs)-u*u*b*(4*(e*e)+3*(S*S)+e2*e2))+2*(S*(u*u*b*(3*e+e2)-(b-c))))

set_option maxHeartbeats 1000000 in
theorem omega_upper (x u e S e2 c b Vs V0 : K)
    (hx : 2≤x) (hu : 1≤u) (he : 1≤e) (hc : 0<c) (hcu : c≤u) (hS0 : 0≤S) (hSe : S≤e)
    (he20 : 0≤e2) (he2 : e2≤e)
    (hV : Vs=(1+2*((x*x-1)*(u*u*e)))*b-c) (hV0 : Vs*Vs=V0*V0) (hV0n : 0≤V0)
    (hdisc : ∀ y : K, 0<y → 1≤y) :
    omegaOf x u e S e2 c b Vs≤5*(x*u*e)*V0 := by
  have hu0 : 0≤u := by linarith
  have he0 : 0≤e := by linarith
  have hx0 : 0≤x := by linarith
  have hue : 0≤u*e := mul_nonneg hu0 he0
  have hxue : 0≤x*u*e := mul_nonneg (mul_nonneg hx0 hu0) he0
  have hue1 : 1≤u*e := one_le_mul_of_one_le_of_one_le hu he
  have hxx : 2*x≤x*x := mul_le_mul_of_nonneg_right hx hx0
  have hSS : S*S≤e*e := mul_self_le_mul_self hS0 hSe
  have he22 : e2*e2≤e*e := mul_self_le_mul_self he20 he2
  have hSc : 4*(e*e)+3*(S*S)+e2*e2≤8*(e*e) := by linarith
  have hSc0 : 0≤4*(e*e)+3*(S*S)+e2*e2 := by
    have := mul_self_nonneg e; have := mul_self_nonneg S; have := mul_self_nonneg e2; linarith
  have h3e : 3*e+e2≤4*e := by linarith
  have huue0 : 0≤u*u*e := mul_nonneg (mul_nonneg hu0 hu0) he0
  unfold omegaOf
  rcases lt_trichotomy b 0 with hneg|hzero|hpos
  · -- b ≤ -1: V < 0, V0 = -V
    obtain ⟨W,hW⟩ : ∃ W : K, W=-b := ⟨-b,rfl⟩
    have hW1 : 1≤W := hdisc W (by rw [hW]; linarith)
    have hW0 : 0≤W := by linarith
    have hbW : b=-W := by rw [hW]; ring
    subst hbW
    set F : K := 1+2*((x*x-1)*(u*u*e)) with hFdef
    have hFm : 6*(u*u*e)≤F-1 := by
      have := mul_le_mul_of_nonneg_right (show (3:K)≤x*x-1 by linarith) huue0
      rw [hFdef]; linarith
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
    have t2 : x*(u*u*u*W)*(4*(e*e)+3*(S*S)+e2*e2)≤x*(u*u*u*W)*(8*(e*e)) :=
      mul_le_mul_of_nonneg_left hSc (mul_nonneg hx0 huuuW)
    have t3 : 0≤u*S*(u*u*W*(3*e+e2)) :=
      mul_nonneg (mul_nonneg hu0 hS0) (mul_nonneg (mul_nonneg (mul_nonneg hu0 hu0) hW0) (by linarith))
    have t4 : u*S*(W+c)≤u*e*(W+c) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSe hu0) (by linarith)
    have hbig : x*(u*u*u*W)*(8*(e*e))+2*(u*e*(W+c))≤9*(x*u*e)*V0 := by
      rw [hV0eq]
      have h1 : x*u*e*(6*(u*u*e)*W)≤x*u*e*((F-1)*W) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hFm hW0) hxue
      have h0 : 0≤u*e*(W+c) := mul_nonneg hue (by linarith)
      have h2 : u*e*(W+c)≤x*(u*e*(W+c)) := le_mul_of_one_le_left h0 (by linarith)
      have h3 : 0≤x*u*e*(u*u*e*W) := mul_nonneg hxue (mul_nonneg huue0 hW0)
      have h4 : 0≤x*u*e*W := mul_nonneg hxue hW0
      have h5 : 0≤x*u*e*c := mul_nonneg hxue hc.le
      linarith
    have hsplit : u*(x*(4*(e*Vs)-u*u*(-W)*(4*(e*e)+3*(S*S)+e2*e2))+
        2*(S*(u*u*(-W)*(3*e+e2)-(-W-c))))=
        4*(x*u*e)*Vs+x*(u*u*u*W)*(4*(e*e)+3*(S*S)+e2*e2)-2*(u*S*(u*u*W*(3*e+e2)))+
          2*(u*S*(W+c)) := by ring
    have hVV : 4*(x*u*e)*Vs=-(4*(x*u*e)*V0) := by rw [hVs,hV0eq]; ring
    rw [hsplit,hVV]
    linarith
  · -- b = 0
    subst hzero
    have hVs : Vs=-c := by rw [hV]; ring
    subst hVs
    have h2 : S-2*(x*e)≤0 := by
      have := mul_le_mul_of_nonneg_right (show (1:K)≤x by linarith) he0
      linarith
    have h3 : 2*(u*c)*(S-2*(x*e))≤0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) (mul_nonneg hu0 hc.le)) h2
    have h4 : 0≤5*(x*u*e)*V0 := mul_nonneg (mul_nonneg (by norm_num) hxue) hV0n
    have hsplit : u*(x*(4*(e*(-c))-u*u*0*(4*(e*e)+3*(S*S)+e2*e2))+
        2*(S*(u*u*0*(3*e+e2)-(0-c))))=2*(u*c)*(S-2*(x*e)) := by ring
    rw [hsplit]
    linarith
  · -- b ≥ 1: V > 0, V0 = V
    have hb1 : 1≤b := hdisc b hpos
    have hb0 : 0≤b := by linarith
    set F : K := 1+2*((x*x-1)*(u*u*e)) with hFdef
    have hF1 : 1≤F := by
      have : 0≤(x*x-1)*(u*u*e) := mul_nonneg (by linarith) huue0
      rw [hFdef]; linarith
    have hP : c≤u*u*e*b := by
      have h1 : u≤u*(u*e) := le_mul_of_one_le_right hu0 hue1
      have h2 : u*u*e≤u*u*e*b := le_mul_of_one_le_right huue0 hb1
      have h3 : u*(u*e)=u*u*e := by ring
      linarith
    have hVpos : 0<Vs := by
      rw [hV]
      have : F≤F*b := le_mul_of_one_le_right (by linarith) hb1
      have hcF : c<F := by
        have : u*u*e≤(x*x-1)*(u*u*e) :=
          le_mul_of_one_le_left huue0 (by linarith)
        have : c≤u*u*e := le_trans hcu (by
          have := le_mul_of_one_le_right hu0 hue1
          have h3 : u*(u*e)=u*u*e := by ring
          linarith)
        rw [hFdef]; linarith
      linarith
    have hV0eq : V0=Vs := by
      have hsq : (V0-Vs)*(V0+Vs)=0 := by linear_combination -hV0
      rcases mul_eq_zero.mp hsq with h|h
      · linear_combination h
      · exfalso; linarith
    rw [hV0eq]
    have huub : 0≤u*u*b := mul_nonneg (mul_nonneg hu0 hu0) hb0
    have t2 : 0≤x*(u*u*u*b)*(4*(e*e)+3*(S*S)+e2*e2) :=
      mul_nonneg (mul_nonneg hx0 (mul_nonneg (mul_nonneg (mul_nonneg hu0 hu0) hu0) hb0)) hSc0
    have t3 : u*S*(u*u*b*(3*e+e2))≤u*e*(u*u*b*(4*e)) := by
      have h0 : 0≤u*u*b*(3*e+e2) := mul_nonneg huub (by linarith)
      have h1 : u*S*(u*u*b*(3*e+e2))≤u*e*(u*u*b*(3*e+e2)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSe hu0) h0
      have h2 : u*e*(u*u*b*(3*e+e2))≤u*e*(u*u*b*(4*e)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3e huub) hue
      linarith
    have t4 : 0≤u*S*b := mul_nonneg (mul_nonneg hu0 hS0) hb0
    have t5 : u*S*c≤u*e*c := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSe hu0) hc.le
    have hkey : 8*(u*u*e*b)+2*c≤x*Vs := by
      rw [hV]
      set P : K := u*u*e*b with hPdef
      have hpoly : 0≤2*x*x*x-3*x-10 := by
        have := mul_nonneg (show (0:K)≤x-2 by linarith)
          (show (0:K)≤2*x*x+4*x+5 by nlinarith)
        linarith
      have h1 : 0≤(2*x*x*x-3*x-10)*P := mul_nonneg hpoly (by linarith)
      have h2 : (x+2)*c≤(x+2)*P := mul_le_mul_of_nonneg_left hP (by linarith)
      have h3 : 0≤x*b := mul_nonneg hx0 hb0
      have hexp : x*(F*b-c)-(8*P+2*c)=(2*x*x*x-3*x-10)*P+(x+2)*(P-c)+x*b := by
        rw [hFdef,hPdef]; ring
      linarith
    have hmain : u*e*(8*(u*u*e*b)+2*c)≤u*e*(x*Vs) := mul_le_mul_of_nonneg_left hkey hue
    have hsplit : u*(x*(4*(e*Vs)-u*u*b*(4*(e*e)+3*(S*S)+e2*e2))+
        2*(S*(u*u*b*(3*e+e2)-(b-c))))=
        4*(x*u*e)*Vs-x*(u*u*u*b)*(4*(e*e)+3*(S*S)+e2*e2)+2*(u*S*(u*u*b*(3*e+e2)))-
          2*(u*S*b)+2*(u*S*c) := by ring
    have hexp2 : u*e*(u*u*b*(4*e))=4*(u*e*(u*u*e*b)) := by ring
    rw [hsplit]
    linarith

set_option maxHeartbeats 1000000 in
theorem omega_nonneg (x u e S e2 c b Vs : K)
    (hx : 2≤x) (hu : 1≤u) (he : 1≤e) (hc : 0<c) (hcu : c≤u) (hS0 : 0≤S) (hSe : S≤e)
    (he20 : 0≤e2) (he2 : e2≤e)
    (hV : Vs=(1+2*((x*x-1)*(u*u*e)))*b-c) (hb1 : 1≤b) :
    0≤omegaOf x u e S e2 c b Vs := by
  have hu0 : 0≤u := by linarith
  have he0 : 0≤e := by linarith
  have hx0 : 0≤x := by linarith
  have hb0 : 0≤b := by linarith
  have hue : 0≤u*e := mul_nonneg hu0 he0
  have hue1 : 1≤u*e := one_le_mul_of_one_le_of_one_le hu he
  have hSS : S*S≤e*e := mul_self_le_mul_self hS0 hSe
  have he22 : e2*e2≤e*e := mul_self_le_mul_self he20 he2
  have hSc : 4*(e*e)+3*(S*S)+e2*e2≤8*(e*e) := by linarith
  have huub : 0≤u*u*b := mul_nonneg (mul_nonneg hu0 hu0) hb0
  have huue0 : 0≤u*u*e := mul_nonneg (mul_nonneg hu0 hu0) he0
  have hP : c≤u*u*e*b := by
    have h1 : u≤u*(u*e) := le_mul_of_one_le_right hu0 hue1
    have h2 : u*u*e≤u*u*e*b := le_mul_of_one_le_right huue0 hb1
    have h3 : u*(u*e)=u*u*e := by ring
    linarith
  unfold omegaOf
  have t2 : x*(u*u*u*b)*(4*(e*e)+3*(S*S)+e2*e2)≤x*(u*u*u*b)*(8*(e*e)) :=
    mul_le_mul_of_nonneg_left hSc (mul_nonneg hx0 (mul_nonneg (mul_nonneg (mul_nonneg hu0 hu0) hu0) hb0))
  have t3 : 0≤u*S*(u*u*b*(3*e+e2)) :=
    mul_nonneg (mul_nonneg hu0 hS0) (mul_nonneg huub (by linarith))
  have t4 : u*S*b≤u*e*b := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSe hu0) hb0
  have t5 : 0≤u*S*c := mul_nonneg (mul_nonneg hu0 hS0) hc.le
  have hkey : 8*x*(u*u*e*b)+2*b≤4*x*Vs := by
    rw [hV]
    set P : K := u*u*e*b with hPdef
    have hx2 : 0≤2*x*x-5 := by nlinarith
    have hpoly : 0≤8*x*x*x-20*x := by
      have := mul_nonneg (show (0:K)≤4*x by linarith) hx2
      linarith
    have h1 : 0≤(8*x*x*x-20*x)*P := mul_nonneg hpoly (by linarith)
    have h2 : 4*x*c≤4*x*P := mul_le_mul_of_nonneg_left hP (by linarith)
    have h3 : 0≤(4*x-2)*b := mul_nonneg (by linarith) hb0
    have hexp : 4*x*((1+2*((x*x-1)*(u*u*e)))*b-c)-(8*x*P+2*b)=
        (8*x*x*x-20*x)*P+4*x*(P-c)+(4*x-2)*b := by rw [hPdef]; ring
    linarith
  have hmain : u*e*(8*x*(u*u*e*b)+2*b)≤u*e*(4*x*Vs) := mul_le_mul_of_nonneg_left hkey hue
  have hsplit : u*(x*(4*(e*Vs)-u*u*b*(4*(e*e)+3*(S*S)+e2*e2))+
      2*(S*(u*u*b*(3*e+e2)-(b-c))))=
      4*(x*u*e)*Vs-x*(u*u*u*b)*(4*(e*e)+3*(S*S)+e2*e2)+2*(u*S*(u*u*b*(3*e+e2)))-
        2*(u*S*b)+2*(u*S*c) := by ring
  have hexp2 : x*(u*u*u*b)*(8*(e*e))+2*(u*e*b)=u*e*(8*x*(u*u*e*b)+2*b) := by ring
  have hexp3 : 4*(x*u*e)*Vs=u*e*(4*x*Vs) := by ring
  rw [hsplit]
  linarith

/-- `g ≤ x u e` when `g² = e (1 + (x² - 1) u² e)`. -/
theorem g_le (x u e g : K) (hx : 1≤x) (hu : 1≤u) (he : 1≤e) (hg : 0≤g)
    (hG : g*g=e*(1+(x*x-1)*(u*u)*e)) : g≤x*u*e := by
  have hu0 : 0≤u := by linarith
  have he0 : 0≤e := by linarith
  have hx0 : 0≤x := by linarith
  have hxue : 0≤x*u*e := mul_nonneg (mul_nonneg hx0 hu0) he0
  apply (mul_self_le_mul_self_iff hg hxue).mpr
  have hue : 1≤u*e := one_le_mul_of_one_le_of_one_le hu he
  have h1 : u*e≤u*e*(u*e) := le_mul_of_one_le_right (by linarith) hue
  have h2 : e≤u*e := le_mul_of_one_le_left he0 hu
  have hexp : x*u*e*(x*u*e)-g*g=u*e*(u*e)-e := by rw [hG]; ring
  linarith

set_option maxHeartbeats 1000000 in
/-- The signed weighted transport estimate (package 193 §4). -/
theorem weighted_estimate (Bq F c b Vs V0 y g ws x u e : K)
    (hB : 0<Bq) (hBc : c<Bq) (hc : 1<c) (hcF : 2*c<F) (hg0 : 0≤g) (hgx : g≤x*u*e)
    (hx : 0<x) (hu : 0<u) (he : 0<e) (hws : ws≤5*(x*u*e)*V0) (hy : 0≤y)
    (hsize : 52*e*F*F+u*u*c<2*(u*u)*Bq)
    (hV : Vs=F*b-c) (hV0 : Vs*Vs=V0*V0) (hV0n : 0≤V0)
    (hnorm : (1+Bq)*(V0*V0)=1+Bq*(y*y)) (hdisc : ∀ x : K, 0<x → 1≤x) :
    2*(4*(g*y)+ws)<x*(u*u*u)*(b*b) ∧ 1≤b*b := by
  have hcpos : 0<c := lt_trans zero_lt_one hc
  have hFpos : 0<F := by linarith
  have hgap : Bq*(y*y-V0*V0)=V0*V0-1 := by linear_combination -hnorm
  -- b = 0 is impossible
  have hb0 : b≠0 := by
    intro hb
    have hVc : Vs=-c := by rw [hV,hb]; ring
    have hsq : (V0-c)*(V0+c)=0 := by
      have h := hV0
      rw [hVc] at h
      linear_combination -h
    have hV0c : V0=c := by
      rcases mul_eq_zero.mp hsq with h|h
      · linear_combination h
      · exfalso; linarith
    rw [hV0c] at hgap
    have hpos : 0<Bq*(y*y-c*c) := by rw [hgap]; nlinarith
    have hyy : c*c<y*y := by
      have := pos_of_mul_pos_right hpos (le_of_lt hB)
      linarith
    have hyc : c<y := lt_of_mul_self_lt_mul_self₀ hy hyy
    have hy1 : c+1≤y := by linarith [hdisc (y-c) (by linarith)]
    have hsq1 : (c+1)*(c+1)≤y*y := mul_self_le_mul_self (by linarith) hy1
    have h1 : Bq*(2*c+1)≤Bq*(y*y-c*c) :=
      mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hB)
    have h2 : c*(2*c+1)<Bq*(2*c+1) := mul_lt_mul_of_pos_right hBc (by linarith)
    nlinarith [mul_pos hcpos hcpos]
  -- unify the two signs of b
  have hW : ∃ W : K, 1≤W ∧ b*b=W*W ∧ V0-c≤F*W ∧ V0≤F*W+c ∧ F-c≤V0 := by
    rcases lt_or_gt_of_ne hb0 with hneg|hpos
    · have hb1 : 1≤-b := hdisc (-b) (by linarith)
      have hFb := mul_le_mul_of_nonneg_left hb1 (le_of_lt hFpos)
      have hVneg : Vs≤-F-c := by rw [hV]; linarith
      have hV0eq : V0=-Vs := by
        have hsq : (V0-(-Vs))*(V0+(-Vs))=0 := by linear_combination -hV0
        rcases mul_eq_zero.mp hsq with h|h
        · linear_combination h
        · exfalso; linarith
      refine ⟨-b,hb1,by ring,?_,?_,?_⟩
      · rw [hV0eq,hV]; linarith
      · rw [hV0eq,hV]; linarith
      · rw [hV0eq]; linarith
    · have hb1 : 1≤b := hdisc b hpos
      have hFb := mul_le_mul_of_nonneg_left hb1 (le_of_lt hFpos)
      have hVpos : F-c≤Vs := by rw [hV]; linarith
      have hV0eq : V0=Vs := by
        have hsq : (V0-Vs)*(V0+Vs)=0 := by linear_combination -hV0
        rcases mul_eq_zero.mp hsq with h|h
        · linear_combination h
        · exfalso; linarith
      refine ⟨b,hb1,rfl,?_,?_,?_⟩
      · rw [hV0eq,hV]; linarith
      · rw [hV0eq,hV]; linarith
      · rw [hV0eq]; exact hVpos
  obtain ⟨W,hW1,hbW,hFW,hFW',hFV⟩ := hW
  have hW0 : 0≤W := by linarith
  have hbb : 1≤b*b := by rw [hbW]; exact one_le_mul_of_one_le_of_one_le hW1 hW1
  refine ⟨?_,hbb⟩
  have hV01 : 1<V0 := by linarith
  have hV0pos : 0<V0 := by linarith
  -- the adjacent norm: y ≥ V0 + 1, hence V0 > 2 Bq, and y < 2 V0
  have hpos : 0<Bq*(y*y-V0*V0) := by rw [hgap]; nlinarith
  have hyy : V0*V0<y*y := by
    have := pos_of_mul_pos_right hpos (le_of_lt hB)
    linarith
  have hyV : V0<y := lt_of_mul_self_lt_mul_self₀ hy hyy
  have hy1 : V0+1≤y := by linarith [hdisc (y-V0) (by linarith)]
  have hsq1 : (V0+1)*(V0+1)≤y*y := mul_self_le_mul_self (by linarith) hy1
  have h1 : Bq*(2*V0+1)≤Bq*(y*y-V0*V0) :=
    mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hB)
  have h3 : (2*Bq)*V0<V0*V0 := by linarith
  have hV0big : 2*Bq<V0 := lt_of_mul_lt_mul_right h3 (le_of_lt hV0pos)
  have hy2 : y<2*V0 := by
    have hB1 : 1≤Bq := hdisc Bq hB
    have hle := mul_le_mul_of_nonneg_right (show 1+Bq≤4*Bq by linarith) (mul_self_nonneg V0)
    have hlt : Bq*(y*y)<Bq*((2*V0)*(2*V0)) := by linarith
    have hyy2 : y*y<(2*V0)*(2*V0) := lt_of_mul_lt_mul_left hlt (le_of_lt hB)
    exact lt_of_mul_self_lt_mul_self₀ (by linarith) hyy2
  -- u² |b| > 52 e F
  have hFWbig : 2*Bq-c<F*W := by linarith
  have huu : 0<u*u := mul_pos hu hu
  have h5 : u*u*(2*Bq-c)≤u*u*(F*W) := mul_le_mul_of_nonneg_left (le_of_lt hFWbig) (le_of_lt huu)
  have h6 : F*(52*e*F)<F*(u*u*W) := by linarith
  have h7 : 52*e*F<u*u*W := lt_of_mul_lt_mul_left h6 (le_of_lt hFpos)
  -- the transport bound
  have hxue : 0<x*u*e := mul_pos (mul_pos hx hu) he
  have hgy : g*y≤x*u*e*(2*V0) := by
    have := mul_le_mul hgx (le_of_lt hy2) hy (le_of_lt hxue)
    linarith
  have hV0F : V0<2*(F*W) := by
    have := mul_le_mul_of_nonneg_left hW1 (le_of_lt hFpos)
    linarith
  have h8 : x*u*e*V0<x*u*e*(2*(F*W)) := mul_lt_mul_of_pos_left hV0F hxue
  have h9 : x*u*W*(52*e*F)≤x*u*W*(u*u*W) :=
    mul_le_mul_of_nonneg_left (le_of_lt h7) (mul_nonneg (mul_nonneg (le_of_lt hx) (le_of_lt hu)) hW0)
  have hexp : x*(u*u*u)*(b*b)=x*u*W*(u*u*W) := by rw [hbW]; ring
  rw [hexp]
  linarith

set_option maxHeartbeats 1000000 in
/-- The size hypothesis of `weighted_estimate`. -/
theorem size_bound (Δ u e c a F Bq : K) (hΔ : 48≤Δ) (hu : 1≤u) (he : 1≤e) (hc : 1≤c)
    (hcu : c≤u) (heu : e≤u*u) (ha : a=Δ*(u*u)*e) (hF : F=1+2*a)
    (hBq : Bq=Δ*(4*a*(1+a))-1) : 52*e*F*F+u*u*c<2*(u*u)*Bq := by
  have hu0 : 0≤u := by linarith
  have he0 : 0≤e := by linarith
  have huu : 1≤u*u := one_le_mul_of_one_le_of_one_le hu hu
  have hua : u*u≤a := by
    rw [ha]
    have h1 : u*u≤Δ*(u*u) := le_mul_of_one_le_left (by linarith) (by linarith)
    have h2 : Δ*(u*u)≤Δ*(u*u)*e := le_mul_of_one_le_right (mul_nonneg (by linarith) (by linarith)) he
    linarith
  have ha1 : 1≤a := le_trans huu hua
  have hca : c≤a := le_trans hcu (le_trans (le_mul_of_one_le_right hu0 hu) hua)
  have hT0 : 0≤a*(1+a) := mul_nonneg (by linarith) (by linarith)
  have hT1 : a*a≤a*(1+a) := by nlinarith
  have hTa : a≤a*(1+a) := by nlinarith
  have hF2 : F*F=4*(a*(1+a))+1 := by rw [hF]; ring
  have h2u : 2*(u*u)*Bq=8*(Δ*(u*u))*(a*(1+a))-2*(u*u) := by rw [hBq]; ring
  have hΔu : 48*e≤Δ*(u*u) := mul_le_mul hΔ heu he0 (by linarith)
  have h1 : 48*e*(a*(1+a))≤Δ*(u*u)*(a*(1+a)) := mul_le_mul_of_nonneg_right hΔu hT0
  have h2 : u*u*c≤a*a := mul_le_mul hua hca (by linarith) (by linarith)
  have heT : a*(1+a)≤e*(a*(1+a)) := le_mul_of_one_le_left hT0 he
  have h4 : e≤e*(a*(1+a)) := le_mul_of_one_le_right he0 (le_trans ha1 hTa)
  have h6 : 0<e*(a*(1+a)) := mul_pos (by linarith) (by nlinarith)
  rw [h2u,show 52*e*F*F=52*e*(F*F) by ring,hF2]
  linarith

set_option maxHeartbeats 1000000 in
/-- The completeness size bounds `K < 2 g` and `-eclear < 2 g` (package 193 §6),
for `X = q w`, `Y = q s`, `v = X Y²`, `8 v + 4 ≤ k`, `k + 1 ≤ c`, `R ≤ c`,
`E = 1 + v (v + 1) k²` and `c² E ≤ g`. -/
theorem complete_bounds (q s w X Y v k c R E g : K) (hq : 1≤q) (hs : 1≤s) (hw : 1≤w)
    (hX : X=q*w) (hY : Y=q*s) (hv : v=X*Y*Y)
    (hk : 8*v+4≤k) (hkc : k+1≤c) (hRc : R≤c)
    (hE : E=1+v*(v+1)*(k*k)) (hg : c*c*E≤g) :
    X*(3*c-2*X)+2<2*g ∧
      6*(R+1+q*q*(q*q)*s-k)+v*k*(k*k-4)<2*g := by
  have hq0 : 0≤q := by linarith
  have hX1 : 1≤X := by rw [hX]; exact one_le_mul_of_one_le_of_one_le hq hw
  have hY1 : 1≤Y := by rw [hY]; exact one_le_mul_of_one_le_of_one_le hq hs
  have hqX : q≤X := by rw [hX]; exact le_mul_of_one_le_right hq0 hw
  have hqY : q≤Y := by rw [hY]; exact le_mul_of_one_le_right hq0 hs
  have hYY : 1≤Y*Y := one_le_mul_of_one_le_of_one_le hY1 hY1
  have hXv : X≤v := by
    rw [hv,mul_assoc]; exact le_mul_of_one_le_right (by linarith) hYY
  have hv1 : 1≤v := le_trans hX1 hXv
  have hv0 : 0≤v := by linarith
  have hk12 : 12≤k := by linarith
  have hc13 : 13≤c := by linarith
  have hk0 : 0≤k := by linarith
  have hc0 : 0≤c := by linarith
  have hkk : 1≤k*k := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
  have hvv1 : 0≤v*(v+1) := mul_nonneg hv0 (by linarith)
  have hvk : v*(k*k)≤v*(v+1)*(k*k) :=
    mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hv0 (by linarith)) (by linarith)
  have hvE : v*(k*k)≤E := by
    have := mul_nonneg hvv1 (show (0:K)≤k*k by linarith)
    rw [hE]; linarith
  have hE1 : 1≤E := by
    have := mul_nonneg hvv1 (show (0:K)≤k*k by linarith)
    rw [hE]; linarith
  have hE0 : 0≤E := by linarith
  have hvv : v*v≤E := by
    have h1 : v*v≤v*(v+1) := mul_le_mul_of_nonneg_left (by linarith) hv0
    have h2 : v*(v+1)≤v*(v+1)*(k*k) := le_mul_of_one_le_right hvv1 hkk
    rw [hE]; linarith
  have hXE : X≤E := le_trans hXv (le_trans (le_mul_of_one_le_right hv0 hv1) hvv)
  -- q⁴ s ≤ v² ≤ E
  have hq3s : q*q*q*s≤v := by
    have h1 : q*q≤X*q := mul_le_mul_of_nonneg_right hqX hq0
    have h2 : q*q*(q*s)≤X*q*Y := mul_le_mul h1 (le_of_eq hY.symm) (mul_nonneg hq0 (by linarith))
      (mul_nonneg (by linarith) hq0)
    have h3 : X*q*Y≤X*Y*Y := by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqY (by linarith : (0:K)≤X))
        (by linarith : (0:K)≤Y)
      linarith
    have h4 : q*q*q*s=q*q*(q*s) := by ring
    rw [hv]; linarith
  have hqv : q≤v := le_trans hqX hXv
  have hq4s : q*q*(q*q)*s≤E := by
    have h1 : q*q*(q*q)*s=(q*q*q*s)*q := by ring
    have h2 : (q*q*q*s)*q≤v*v := mul_le_mul hq3s hqv hq0 hv0
    linarith
  have hcE : 0≤c*E := mul_nonneg hc0 hE0
  have hcc : 13*c≤c*c := mul_le_mul_of_nonneg_right hc13 hc0
  have hccE : 13*(c*E)≤c*c*E := by
    have := mul_le_mul_of_nonneg_right hcc hE0; linarith
  have h3 : 1≤c*E := one_le_mul_of_one_le_of_one_le (by linarith) hE1
  constructor
  · -- K ≤ 3 c X + 2 < 2 c² E
    have h1 : 0≤X*X := mul_nonneg (by linarith) (by linarith)
    have h2 : c*X≤c*E := mul_le_mul_of_nonneg_left hXE hc0
    linarith
  · have h1 : 0≤v*k*4 := mul_nonneg (mul_nonneg hv0 hk0) (by norm_num)
    have h2 : v*k*(k*k)≤c*E := by
      have h' : v*(k*k)*k≤E*c := mul_le_mul hvE (by linarith) hk0 hE0
      have he' : v*k*(k*k)=v*(k*k)*k := by ring
      have hc' : E*c=c*E := by ring
      linarith
    have h4 : c≤c*E := le_mul_of_one_le_right hc0 hE1
    have h5 : E≤c*E := le_mul_of_one_le_left hE0 (by linarith)
    have hexp : v*k*(k*k-4)=v*k*(k*k)-v*k*4 := by ring
    rw [hexp]
    linarith

#print axioms Trace118Estimate.omega_upper
#print axioms Trace118Estimate.omega_nonneg
#print axioms Trace118Estimate.g_le
#print axioms Trace118Estimate.weighted_estimate
#print axioms Trace118Estimate.size_bound
#print axioms Trace118Estimate.complete_bounds
end Trace118Estimate
