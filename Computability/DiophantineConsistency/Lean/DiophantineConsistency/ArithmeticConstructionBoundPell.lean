import DiophantineConsistency.ArithmeticOuterSeed
import DiophantineConsistency.ArithmeticPellAuxiliarySeed

/-! **Explicit size bounds for the Pell stages of the construction**, in every
model of IΣ1.

The rank `R` determines elementary bounds for every Pell coordinate of the
outer seed (`ArithmeticOuterSeed`) and of the auxiliary seed
(`ArithmeticPellAuxiliarySeed`):

* `Ys R = (2^R+1)^R` bounds the seed ordinate `Y = s*q^3` (binomial floor);
* `As R = 2^R*Ys R+Ys R` bounds the main base `a = X*Y+Y`;
* `Ps R = (2*(2*2^R*Ys R^2+2))^R` bounds the first-index Pell values;
* `Gs R = (2*(As R+2))^R` bounds the main ordinate `c = y_R(a)` and its root;
* `Fs R = (2*(As R+2))^(R*Gs R)` bounds the auxiliary `f = x_{Rc}(a)` and `i`;
* `Is R` bounds `I = δ(a)*i*c^2`, and `Us R = (2*(Is R+2))^R` bounds `y_R(I-2)`.

All are built from `+`, `*`, `Exp.exp` and `ArithmeticPow.power`, and are
monotone in `R`. The only growth fact used is `y_{t+1}(b) ≤ (2(b+2))^t`
(`ArithmeticHalfBinomialSandwich.ycoord_le_power`).

`outer_seed_bound` repeats the proof of `ArithmeticOuterSeed.outer_seed` and
additionally records the binomial-floor bound on `Y`, the one coordinate whose
size the seed relations alone do not control. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticConstructionBoundPell
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPow ArithmeticPellRecurrence ArithmeticPellCongruences ArithmeticPellPowerRecovery
  ArithmeticBinaryPopulation ArithmeticHalfBinomial ArithmeticHalfBinomialSandwich
  ArithmeticOuterSeed
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Elementary monotonicity helpers -/

theorem mm {a b c d : V} (h1 : a ≤ b) (h2 : c ≤ d) : a * c ≤ b * d :=
  mul_le_mul h1 h2 (by simp) (by simp)

theorem pmono {x y m n : V} (hx : 1 ≤ x) (hxy : x ≤ y) (hmn : m ≤ n) :
    power x m ≤ power y n :=
  le_trans (power_mono_exponent x m n hx hmn) (power_mono_base x y n hxy)

theorem one_le_two_mul_add_two (b : V) : 1 ≤ 2 * (b + 2) :=
  le_trans (by simp : (1:V) ≤ 2) (le_mul_of_one_le_right (by simp)
    (le_trans (by simp : (1:V) ≤ 2) (le_add_of_nonneg_left (by simp))))

theorem le_self_mul {x y : V} (hy : 1 ≤ y) : x ≤ x * y := le_mul_of_one_le_right (by simp) hy

/-! ### Pell growth from above at every index -/

theorem y_le (t b : V) : ycoord t b ≤ power (2 * (b + 2)) t := by
  rcases zero_or_succ t with rfl | ⟨t, rfl⟩
  · simp
  · exact le_trans (ycoord_le_power b t)
      (power_mono_exponent _ _ _ (one_le_two_mul_add_two b) (le_add_of_nonneg_right (by simp)))

theorem x_le (t b : V) : xcoord t b ≤ power (2 * (b + 2)) t := by
  have h := ycoord_le_power b t
  rw [y_succ] at h
  exact le_trans (le_add_of_nonneg_right (by simp)) h

/-! ### The bound functions -/

/-- Bound on the seed ordinate `Y = s*q^3`. -/
def Ys (R : V) : V := power (Exp.exp R + 1) R
/-- Bound on the main Pell base `a = X*Y+Y`. -/
def As (R : V) : V := Exp.exp R * Ys R + Ys R
/-- Bound on the first-index base `2*(X*Y*Y-1)+1`. -/
def Bs (R : V) : V := 2 * Exp.exp R * Ys R * Ys R
/-- Bound on the first-index Pell values. -/
def Ps (R : V) : V := power (2 * (Bs R + 2)) R
/-- Bound on the main ordinate `c = y_R(a)` and the main abscissa. -/
def Gs (R : V) : V := power (2 * (As R + 2)) R
/-- Bound on the auxiliary abscissa `f = x_{Rc}(a)` and the quotient `i`. -/
def Fs (R : V) : V := power (2 * (As R + 2)) (R * Gs R)
/-- Bound on `I = δ(a)*i*c*c`. -/
def Is (R : V) : V := (As R + 1) * (As R + 3) * Fs R * Gs R * Gs R
/-- Bound on the auxiliary Pell values at base `I-2`. -/
def Us (R : V) : V := power (2 * (Is R + 2)) R

section mono
variable {R R' : V} (h : R ≤ R')
include h

theorem Ys_mono : Ys R ≤ Ys R' :=
  pmono (le_add_of_nonneg_left (by simp)) (add_le_add (exp_monotone_le.mpr h) le_rfl) h

theorem As_mono : As R ≤ As R' :=
  add_le_add (mm (exp_monotone_le.mpr h) (Ys_mono h)) (Ys_mono h)

theorem Bs_mono : Bs R ≤ Bs R' :=
  mm (mm (mm le_rfl (exp_monotone_le.mpr h)) (Ys_mono h)) (Ys_mono h)

theorem Ps_mono : Ps R ≤ Ps R' :=
  pmono (one_le_two_mul_add_two _) (mm le_rfl (add_le_add (Bs_mono h) le_rfl)) h

theorem Gs_mono : Gs R ≤ Gs R' :=
  pmono (one_le_two_mul_add_two _) (mm le_rfl (add_le_add (As_mono h) le_rfl)) h

theorem Fs_mono : Fs R ≤ Fs R' :=
  pmono (one_le_two_mul_add_two _) (mm le_rfl (add_le_add (As_mono h) le_rfl)) (mm h (Gs_mono h))

theorem Is_mono : Is R ≤ Is R' :=
  mm (mm (mm (mm (add_le_add (As_mono h) le_rfl) (add_le_add (As_mono h) le_rfl)) (Fs_mono h))
    (Gs_mono h)) (Gs_mono h)

theorem Us_mono : Us R ≤ Us R' :=
  pmono (one_le_two_mul_add_two _) (mm le_rfl (add_le_add (Is_mono h) le_rfl)) h

end mono

/-! ### The outer seed with the binomial-floor bound on `Y` -/

/-- **The outer Pell seed, with the size of its ordinate.** Same proof as
`ArithmeticOuterSeed.outer_seed`; the extra conjunct is `Y = s*q^3 ≤ (2^R+1)^R`,
read off the binomial floor `(X+1)^(2r) = 2*Y*X^r + v`. -/
theorem outer_seed_bound (u R : V) (hu : 0<u) (hodd : ∃ r, R=2*r+1) (hpop : population R=3*u+2) :
    ∃ s n eta zeta gamma : V, 0<s ∧ 0<n ∧ 0<eta ∧ 0<zeta ∧ 0<gamma ∧
      SeedRelations u R s n eta zeta gamma ∧ s*Exp.exp u^3 ≤ Ys R := by
  obtain ⟨r,rfl⟩ := hodd
  have hpr : population r=3*u+1 := by
    rw [population_odd] at hpop
    exact add_right_cancel (hpop.trans (by ring))
  have hu1 : 1≤u := by simpa using lt_iff_succ_le.mp hu
  have hr4 : 4≤r := by
    have h4 : (4:V)≤3*u+1 := by
      have : (3:V)*1≤3*u := mul_le_mul_of_nonneg_left hu1 (by simp)
      calc (4:V)=3*1+1 := by ring
        _≤3*u+1 := add_le_add this le_rfl
    rw [←hpr] at h4
    exact le_trans h4 (le_trans (population_le r).1 (population_le r).2)
  have hr1 : 1≤r := le_trans (by simp) hr4
  obtain ⟨X,hX⟩ : ∃ X, X=Exp.exp (2*r+1) := ⟨_,rfl⟩
  have hX1 : 1≤X := by rw [hX]; exact one_le_exp _
  obtain ⟨Y,s,v,w,hN,hv,hYs,hY1,_⟩ := binomial_floor X r u hr1 hX hpr.ge
  have hspos : 0<s := by
    rcases zero_or_succ s with h0|⟨s',hs'⟩
    · rw [h0,zero_mul] at hYs; rw [hYs] at hY1; simp at hY1
    · rw [hs']; simp
  have hY' : s*Exp.exp u^3=Y := by
    rw [hYs,show 3*u=u+u+u by ring,exp_add,exp_add]; ring
  -- the new size fact
  have hYbound : s*Exp.exp u^3 ≤ Ys (2*r+1) := by
    rw [hY', Ys, ← hX]
    have hp1 : 1 ≤ power X r := one_le_power X r hX1
    have h2p : 1 ≤ 2*power X r := le_trans hp1 (le_mul_of_one_le_left (by simp) (by simp))
    calc Y ≤ Y*(2*power X r) := le_self_mul h2p
      _ = 2*Y*power X r := by ring
      _ ≤ 2*Y*power X r+v := le_add_of_nonneg_right (by simp)
      _ = power (X+1) (2*r) := hN.symm
      _ ≤ power (X+1) (2*r+1) :=
          power_mono_exponent _ _ _ (le_add_of_nonneg_left (by simp))
            (le_add_of_nonneg_right (by simp))
  obtain ⟨hlo,hhi⟩ := construction_interval X Y r v hr4 hX hY1 hN hv
  obtain ⟨K,hKd⟩ : ∃ K, ycoord (r+1) (2*(X*Y*Y-1)+1)=K := ⟨_,rfl⟩
  obtain ⟨c,hcd⟩ : ∃ c, ycoord (2*r+1) (Y*(X+1))=c := ⟨_,rfl⟩
  rw [hKd,hcd] at hlo hhi
  obtain ⟨eta,heta_def⟩ : ∃ eta, eta=c-2*K*Y := ⟨_,rfl⟩
  have hc : 2*K*Y+eta=c := by rw [heta_def]; exact add_tsub_cancel_of_le hlo.le
  have heta : 0<eta := by rw [heta_def]; exact tsub_pos_of_lt hlo
  have hetak : eta<2*K := by
    have h : 2*K*Y+eta<2*K*Y+2*K := by rw [hc]; simpa [mul_add] using hhi
    exact lt_of_add_lt_add_left h
  obtain ⟨zeta,hzeta_def⟩ : ∃ zeta, zeta=2*K-eta := ⟨_,rfl⟩
  have hk : eta+zeta=2*K := by rw [hzeta_def]; exact add_tsub_cancel_of_le hetak.le
  have hzeta : 0<zeta := by rw [hzeta_def]; exact tsub_pos_of_lt hetak
  have hZ1 : 1≤X*Y*Y := one_le_mul (one_le_mul hX1 hY1) hY1
  have hB : 2*(X*Y*Y-1)+1+1=2*(X*Y*Y) := by
    have he : X*Y*Y-1+1=X*Y*Y := tsub_add_cancel_of_le hZ1
    calc
      2*(X*Y*Y-1)+1+1=2*(X*Y*Y-1+1) := by ring
      _=2*(X*Y*Y) := by rw [he]
  have hdvd : X*Y∣2*(X*Y*Y-1)+1+1 := ⟨2*Y,by rw [hB]; ring⟩
  obtain ⟨ρ,σ,hxρ,hyσ⟩ := residue_quotients (r+1) (2*(X*Y*Y-1)+1) (X*Y) hdvd
  rw [hKd] at hyσ
  have hEpos : 0<X*Y := lt_of_lt_of_le (by simp) (one_le_mul hX1 hY1)
  have hxgt := x_gt (r+1) (2*(X*Y*Y-1)+1)
  rw [hB,hKd,hxρ] at hxgt
  have hρ : 2*σ+2≤ρ := by
    have hK : σ+1≤K := by
      rw [hyσ]
      calc
        σ+1≤X*Y*σ+(r+1) := add_le_add (le_mul_of_one_le_left (by simp)
          (one_le_mul hX1 hY1)) (le_add_of_nonneg_left (by simp))
        _=r+1+X*Y*σ := by ring
    have h1 : X*Y*(2*σ+2)<X*Y*ρ+1 := calc
      X*Y*(2*σ+2)=2*(X*Y)*(σ+1) := by ring
      _≤2*(X*Y)*(Y*K) := mul_le_mul_of_nonneg_left
          (le_trans hK (le_mul_of_one_le_left (by simp) hY1)) (by simp)
      _=2*(X*Y*Y)*K := by ring
      _<1+X*Y*ρ := hxgt
      _=X*Y*ρ+1 := by ring
    exact le_of_mul_le_mul_left (lt_succ_iff_le.mp h1) hEpos
  obtain ⟨n,hn_def⟩ : ∃ n, n=ρ-2*σ := ⟨_,rfl⟩
  have hnρ : n+2*σ=ρ := by
    rw [hn_def]; exact tsub_add_cancel_of_le (le_trans (le_add_of_nonneg_right (by simp)) hρ)
  have hn : 0<n := by
    have : 2*σ+0<2*σ+n := by
      calc 2*σ+0<2*σ+2 := add_lt_add_of_le_of_lt le_rfl (by simp)
        _≤ρ := hρ
        _=2*σ+n := by rw [←hnρ]; ring
    exact lt_of_add_lt_add_left this
  obtain ⟨gamma,hgamma⟩ := projection_quotient (X*Y+Y) (2*r+1)
  have hYX : Y*(X+1)=X*Y+Y := by ring
  rw [hYX] at hcd
  rw [hcd,←hX] at hgamma
  have hxc := x_gt (2*r+1) (X*Y+Y)
  rw [hcd] at hxc
  have hcX : X<c := by
    rw [←hcd]
    have hp := power_le_ycoord (X*Y+Y) (r+r)
    rw [show r+r+1=2*r+1 by ring] at hp
    have hbase : X<2*(X*Y+Y)+3 := by
      have hXa : X≤X*Y+Y := le_trans (le_mul_of_one_le_right (by simp) hY1)
        (le_add_of_nonneg_right (by simp))
      calc
        X≤X*Y+Y := hXa
        _≤(X*Y+Y)+(X*Y+Y) := le_add_of_nonneg_right (by simp)
        _=2*(X*Y+Y) := (two_mul _).symm
        _<2*(X*Y+Y)+3 := lt_add_of_pos_right _ (by simp)
    have hmono : 2*(X*Y+Y)+3≤power (2*(X*Y+Y)+3) (r+r) := by
      have h13 : (1:V)≤2*(X*Y+Y)+3 := le_trans (by simp) (le_add_of_nonneg_left (by simp))
      have := power_mono_exponent (2*(X*Y+Y)+3) 1 (r+r) h13
        (le_trans hr1 (le_add_of_nonneg_right (by simp)))
      simpa using this
    exact lt_of_lt_of_le hbase (le_trans hmono hp)
  have hgpos : 0<gamma := by
    rcases zero_or_succ gamma with h0|⟨g,hg⟩
    · exfalso
      rw [h0,mul_zero,add_zero] at hgamma
      have : (X*Y+Y+1)*c<X+(X*Y+Y)*c := by rw [hgamma] at hxc; exact hxc
      have h2 : X+(X*Y+Y)*c<(X*Y+Y+1)*c := by
        calc X+(X*Y+Y)*c<c+(X*Y+Y)*c := add_lt_add_of_lt_of_le hcX le_rfl
          _=(X*Y+Y+1)*c := by ring
      exact (lt_asymm this) h2
    · rw [hg]; simp
  refine ⟨s,n,eta,zeta,gamma,hspos,hn,heta,hzeta,hgpos,?_,hYbound⟩
  dsimp only [SeedRelations]
  rw [←hX,hY',hk,hc]
  have htau : X*Y*n+2*K-(2*r+1)=xcoord (r+1) (2*(X*Y*Y-1)+1) := by
    rw [hxρ]
    apply tsub_eq_of_eq_add
    rw [←hnρ,hyσ]; ring
  have hnorm1 := norm (r+1) (2*(X*Y*Y-1)+1)
  have hdelta : delta (2*(X*Y*Y-1)+1)=(2*(X*Y*Y))*(2*(X*Y*Y)+2) := by
    unfold delta; rw [hB,show 2*(X*Y*Y-1)+1+3=2*(X*Y*Y-1)+1+1+2 by ring,hB]
  rw [hdelta,hKd] at hnorm1
  have hnorm2 := norm (2*r+1) (X*Y+Y)
  rw [hcd] at hnorm2
  unfold delta at hnorm2
  have hd : X+(X*Y+Y)*c+gamma*(4*(X*Y+Y)+3)=xcoord (2*r+1) (X*Y+Y) := by rw [hgamma]; ring
  refine ⟨?_,?_,hcd.symm,hd,r,rfl,htau,by rw [hKd]⟩
  · rw [htau,hnorm1]; ring
  · rw [hd,hnorm2]

/-! ### Sizes of the outer-seed coordinates from the seed relations -/

/-- Every outer-seed coordinate other than `s` is bounded by its relations,
given the bound on `Y`. Also returns the bounds on the main base `a` and the
main ordinate `c = y_R(a)` consumed by the auxiliary stage. -/
theorem seed_bounds (u R s n eta zeta gamma : V) (hs0 : 0 < s)
    (hs : s*Exp.exp u^3 ≤ Ys R) (h : SeedRelations u R s n eta zeta gamma) :
    n ≤ Ps R + R ∧ eta ≤ 2 * Ps R ∧ zeta ≤ 2 * Ps R ∧ gamma ≤ Gs R ∧
      Exp.exp R * (s*Exp.exp u^3) + s*Exp.exp u^3 ≤ As R ∧
      ycoord R (Exp.exp R * (s*Exp.exp u^3) + s*Exp.exp u^3) ≤ Gs R := by
  dsimp only [SeedRelations] at h
  obtain ⟨-, -, -, hd, r, hR, htau, hk⟩ := h
  set Y := s*Exp.exp u^3 with hYdef
  set X := Exp.exp R with hXdef
  have hX1 : 1 ≤ X := one_le_exp R
  have hY1 : 1 ≤ Y := one_le_mul (pos_iff_one_le.mp hs0) (one_le_pow₀ (one_le_exp u))
  have hrR : r+1 ≤ R := by rw [hR]; exact add_le_add (le_mul_of_one_le_left (by simp) (by simp)) le_rfl
  -- the first-index base
  have hZ1 : 1 ≤ X*Y*Y := one_le_mul (one_le_mul hX1 hY1) hY1
  have hBle : 2*(X*Y*Y-1)+1 ≤ Bs R := by
    have he : X*Y*Y-1+1 = X*Y*Y := tsub_add_cancel_of_le hZ1
    calc 2*(X*Y*Y-1)+1 ≤ 2*(X*Y*Y-1)+2 := add_le_add le_rfl (by simp)
      _ = 2*(X*Y*Y-1+1) := by ring
      _ = 2*(X*Y*Y) := by rw [he]
      _ ≤ Bs R := by
          unfold Bs
          rw [show 2*Exp.exp R*Ys R*Ys R = 2*(X*Ys R*Ys R) by rw [hXdef]; ring]
          exact mm le_rfl (mm (mm le_rfl hs) hs)
  have hPs : power (2*((2*(X*Y*Y-1)+1)+2)) (r+1) ≤ Ps R :=
    pmono (one_le_two_mul_add_two _) (mm le_rfl (add_le_add hBle le_rfl)) hrR
  have htauP : xcoord (r+1) (2*(X*Y*Y-1)+1) ≤ Ps R := le_trans (x_le _ _) hPs
  have hkP : eta+zeta ≤ 2*Ps R := by rw [hk]; exact mm le_rfl (le_trans (y_le _ _) hPs)
  -- the main base and ordinate
  have hA : X*Y+Y ≤ As R := add_le_add (mm le_rfl hs) hs
  have hG : ∀ t, t ≤ R → power (2*((X*Y+Y)+2)) t ≤ Gs R := fun t ht =>
    pmono (one_le_two_mul_add_two _) (mm le_rfl (add_le_add hA le_rfl)) ht
  refine ⟨?_, le_trans (le_add_of_nonneg_right (by simp)) hkP,
    le_trans (le_add_of_nonneg_left (by simp)) hkP, ?_, hA, le_trans (y_le _ _) (hG R le_rfl)⟩
  · -- `X*Y*n + k - R = τ`
    have h1 : X*Y*n + (eta+zeta) ≤ xcoord (r+1) (2*(X*Y*Y-1)+1) + R := by
      rw [← htau]; exact le_tsub_add
    calc n ≤ X*Y*n := le_mul_of_one_le_left (by simp) (one_le_mul hX1 hY1)
      _ ≤ X*Y*n + (eta+zeta) := le_add_of_nonneg_right (by simp)
      _ ≤ xcoord (r+1) (2*(X*Y*Y-1)+1) + R := h1
      _ ≤ Ps R + R := add_le_add htauP le_rfl
  · -- `d = X + a*c + γ*(4a+3) = x_R(a)`
    have h4 : 1 ≤ 4*(X*Y+Y)+3 := le_trans (by simp) (le_add_of_nonneg_left (by simp))
    calc gamma ≤ gamma*(4*(X*Y+Y)+3) := le_self_mul h4
      _ ≤ X+(X*Y+Y)*((eta+zeta)*Y+eta)+gamma*(4*(X*Y+Y)+3) := le_add_of_nonneg_left (by simp)
      _ = xcoord R (X*Y+Y) := hd
      _ ≤ Gs R := le_trans (x_le _ _) (hG R le_rfl)

/-! ### Sizes of the auxiliary-seed coordinates -/

/-- The auxiliary coordinates `f, i, T, y` (and the quotient `u`) are bounded
by the relations returned by `ArithmeticPellAuxiliarySeed.auxiliary_seed`. -/
theorem aux_bounds (a R f i T u y : V) (hR : 0 < R) (ha : a ≤ As R)
    (hf : 0 < f) (hi : 0 < i)
    (hfx : f = xcoord (R*ycoord R a) a)
    (hyic : ycoord (R*ycoord R a) a = i*ycoord R a*ycoord R a)
    (hy : y = ycoord R (delta a*i*ycoord R a*ycoord R a-2))
    (hux : xcoord R (delta a*i*ycoord R a*ycoord R a-2) = delta a*i*ycoord R a*ycoord R a*u)
    (hlit : f*f*ycoord R a*T = u+ycoord R a+f*f*R) :
    f ≤ Fs R ∧ i ≤ Fs R ∧ y ≤ Us R ∧ T ≤ Us R + Gs R + Fs R * Fs R * R := by
  set c := ycoord R a with hcdef
  have hc1 : 1 ≤ c := le_trans (pos_iff_one_le.mp hR) (time_le_y R a)
  have hbase : 2*(a+2) ≤ 2*(As R+2) := mm le_rfl (add_le_add ha le_rfl)
  have hcG : c ≤ Gs R :=
    le_trans (y_le _ _) (pmono (one_le_two_mul_add_two _) hbase le_rfl)
  have hF : power (2*(a+2)) (R*c) ≤ Fs R :=
    pmono (one_le_two_mul_add_two _) hbase (mm le_rfl hcG)
  have hfF : f ≤ Fs R := by rw [hfx]; exact le_trans (x_le _ _) hF
  have hiF : i ≤ Fs R := by
    calc i ≤ i*c*c := le_trans (le_self_mul hc1) (le_self_mul hc1)
      _ = ycoord (R*c) a := hyic.symm
      _ ≤ Fs R := le_trans (y_le _ _) hF
  set I := delta a*i*c*c with hIdef
  have hI : I ≤ Is R := by
    rw [hIdef, Is, delta]
    exact mm (mm (mm (mm (add_le_add ha le_rfl) (add_le_add ha le_rfl)) hiF) hcG) hcG
  have hU : power (2*((I-2)+2)) R ≤ Us R :=
    pmono (one_le_two_mul_add_two _) (mm le_rfl (add_le_add (le_trans tsub_le_self hI) le_rfl))
      le_rfl
  have hyU : y ≤ Us R := by rw [hy]; exact le_trans (y_le _ _) hU
  have hI1 : 1 ≤ I := by
    have hd1 : 1 ≤ delta a := one_le_mul (le_add_of_nonneg_left (by simp))
      (le_trans (by simp) (le_add_of_nonneg_left (by simp)))
    exact one_le_mul (one_le_mul (one_le_mul hd1 (pos_iff_one_le.mp hi)) hc1) hc1
  have huU : u ≤ Us R := by
    calc u ≤ I*u := le_mul_of_one_le_left (by simp) hI1
      _ = xcoord R (I-2) := hux.symm
      _ ≤ Us R := le_trans (x_le _ _) hU
  refine ⟨hfF, hiF, hyU, ?_⟩
  have hffc : 1 ≤ f*f*c := one_le_mul (one_le_mul (pos_iff_one_le.mp hf) (pos_iff_one_le.mp hf)) hc1
  calc T ≤ f*f*c*T := le_mul_of_one_le_left (by simp) hffc
    _ = u+c+f*f*R := hlit
    _ ≤ Us R + Gs R + Fs R * Fs R * R := add_le_add (add_le_add huU hcG) (mm (mm hfF hfF) le_rfl)

end DiophantineConsistency.ArithmeticConstructionBoundPell
