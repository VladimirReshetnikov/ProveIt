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

`outer_seed_bound` specializes the shared outer-seed theorem with its
binomial-floor bound on `Y`, the one coordinate whose size the seed relations
alone do not control. -/
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

private theorem pell_pmono {a b m n : V} (hab : a ≤ b) (hmn : m ≤ n) :
    power (2 * (a + 2)) m ≤ power (2 * (b + 2)) n :=
  pmono (one_le_two_mul_add_two _) (mm le_rfl (add_le_add hab le_rfl)) hmn

theorem le_self_mul {x y : V} (hy : 1 ≤ y) : x ≤ x * y := le_mul_of_one_le_right (by simp) hy

/-! ### Pell growth from above at every index -/

theorem x_le (t b : V) : xcoord t b ≤ power (2 * (b + 2)) t := by
  have h := ycoord_le_power b t
  rw [y_succ] at h
  exact le_trans (le_add_of_nonneg_right (by simp)) h

theorem y_le (t b : V) : ycoord t b ≤ power (2 * (b + 2)) t :=
  le_trans (le_of_lt (ordinate_lt_abscissa b t)) (x_le t b)

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
  pell_pmono (Bs_mono h) h

theorem Gs_mono : Gs R ≤ Gs R' :=
  pell_pmono (As_mono h) h

theorem Fs_mono : Fs R ≤ Fs R' :=
  pell_pmono (As_mono h) (mm h (Gs_mono h))

theorem Is_mono : Is R ≤ Is R' :=
  mm (mm (mm (mm (add_le_add (As_mono h) le_rfl) (add_le_add (As_mono h) le_rfl)) (Fs_mono h))
    (Gs_mono h)) (Gs_mono h)

theorem Us_mono : Us R ≤ Us R' :=
  pell_pmono (Is_mono h) h

end mono

/-! ### The outer seed with the binomial-floor bound on `Y` -/

/-- **The outer Pell seed, with the size of its ordinate.** The extra conjunct
`Y = s*q^3 ≤ (2^R+1)^R` follows from the shared binomial-floor construction. -/
theorem outer_seed_bound (u R : V) (hu : 0<u) (hodd : ∃ r, R=2*r+1) (hpop : population R=3*u+2) :
    ∃ s n eta zeta gamma : V, 0<s ∧ 0<n ∧ 0<eta ∧ 0<zeta ∧ 0<gamma ∧
      SeedRelations u R s n eta zeta gamma ∧ s*Exp.exp u^3 ≤ Ys R := by
  simpa only [Ys] using ArithmeticOuterSeed.outer_seed_with_size u R hu hodd hpop

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
    pell_pmono hBle hrR
  have htauP : xcoord (r+1) (2*(X*Y*Y-1)+1) ≤ Ps R := le_trans (x_le _ _) hPs
  have hkP : eta+zeta ≤ 2*Ps R := by rw [hk]; exact mm le_rfl (le_trans (y_le _ _) hPs)
  -- the main base and ordinate
  have hA : X*Y+Y ≤ As R := add_le_add (mm le_rfl hs) hs
  have hG : ∀ t, t ≤ R → power (2*((X*Y+Y)+2)) t ≤ Gs R := fun t ht =>
    pell_pmono hA ht
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
  have hcG : c ≤ Gs R :=
    le_trans (y_le _ _) (pell_pmono ha le_rfl)
  have hF : power (2*(a+2)) (R*c) ≤ Fs R :=
    pell_pmono ha (mm le_rfl hcG)
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
    pell_pmono (le_trans tsub_le_self hI) le_rfl
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
