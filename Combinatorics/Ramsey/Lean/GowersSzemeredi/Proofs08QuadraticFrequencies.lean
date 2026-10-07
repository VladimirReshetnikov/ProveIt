import GowersSzemeredi.Proofs03Equivalences
import GowersSzemeredi.Proofs05_10
import GowersSzemeredi.Proofs07AdditiveRestriction

/-! Dense Freiman frequency data extracted from quadratic nonuniformity.
The density of the original set is retained in both applications of additive
energy, before being bounded below by the nonuniformity parameter. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators ZMod
namespace LeanProofs.GowersSzemeredi

/-- The one-dimensional cube coordinates identify with the cyclic group. -/
def pointOneEquiv (N : Nat) : ZMod N ≃ Point N 1 where
  toFun x := fun _ ↦ x
  invFun x := x 0
  left_inv _ := rfl
  right_inv x := by funext i; fin_cases i; rfl

@[simp] theorem cubeDifference_pointOne {N : Nat} (f : ZMod N → Complex)
    (x : ZMod N) : cubeDifference f (pointOneEquiv N x) = difference f x := by
  change cubeDifference f (Fin.cons x (fun i ↦ Fin.elim0 i)) = difference f x
  rw [cubeDifference_cons]
  simp only [cubeDifference, List.ofFn_zero, iteratedDifference]

/-- Quadratic nonuniformity supplies a dense set of large derivative Fourier
coefficients whose frequency map is a Freiman homomorphism of order eight. -/
theorem quadratic_nonuniformity_freiman_frequencies
    (N : Nat) [NeZero N] [Fact N.Prime] (f : ZMod N → Complex)
    (alpha : Real) (hα : 0 < alpha) (hαone : alpha ≤ 1)
    (hf : DiscValued f) (hnot : ¬ UniformOfDegree f alpha 2) :
    ∃ B : Finset (ZMod N), ∃ phi : ZMod N → ZMod N,
      (alpha / 2) ^ (12359 : Nat) * N ≤ (B.card : Real) ∧
      FreimanHom 8 B phi ∧
      ∀ x ∈ B, alpha / 2 * N ≤ ‖fourier (difference f x) (phi x)‖ := by
  classical
  let a : Real := alpha / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hahalf : a ≤ 1 / 2 := by dsimp [a]; linarith
  have haone : a ≤ 1 := hahalf.trans (by norm_num)
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  obtain ⟨hi_ii, hii_iii, _, _, _, hvi_iii, _, hvii_vi⟩ :=
    lemma_3_1_holds N 2 f (by omega) hf alpha a a
      hα.le hαone ha.le haone ha.le haone
  have hnotvii : ¬ higherUniformConditionvii f a 2 := by
    intro hvii
    have hvi := hvii_vi (le_refl a) hvii
    have hiii := hvi_iii (by dsimp only [a]; ring_nf; exact le_rfl) hvi
    exact hnot (hi_ii.mpr (hii_iii.mpr hiii))
  let good : ZMod N → Prop := fun x ↦
    ∃ r, a * N ≤ ‖fourier (difference f x) r‖
  let B0 : Finset (ZMod N) := Finset.univ.filter good
  have hcountEq : countWhere (fun x : Point N 1 ↦
      ∃ r, a * N ≤ ‖fourier (cubeDifference f x) r‖) = B0.card := by
    unfold countWhere B0
    simp only [Finset.card_filter]
    have hs := (pointOneEquiv N).sum_comp (fun x : Point N 1 ↦
      @ite Nat (∃ r, a * N ≤ ‖fourier (cubeDifference f x) r‖)
        (Classical.propDecidable _) 1 0)
    simp only [cubeDifference_pointOne] at hs
    simpa only [good] using hs.symm
  have hB0 : a * N ≤ (B0.card : Real) := by
    unfold higherUniformConditionvii at hnotvii
    simp only [Nat.reduceSub, pow_one, hcountEq] at hnotvii
    exact (lt_of_not_ge hnotvii).le
  let phi : ZMod N → ZMod N := fun x ↦
    if hx : good x then Classical.choose hx else 0
  have hlarge (x : ZMod N) (hx : x ∈ B0) :
      a * N ≤ ‖fourier (difference f x) (phi x)‖ := by
    have hxgood : good x := (Finset.mem_filter.mp hx).2
    simpa only [phi, dif_pos hxgood] using Classical.choose_spec hxgood
  let rho : Real := B0.card / (N : Real)
  have harho : a ≤ rho := (le_div_iff₀ hN).2 hB0
  have hrho : 0 < rho := ha.trans_le harho
  have hcard : (B0.card : Real) = rho * N := by
    dsimp only [rho]
    field_simp
  let tau : Real := rho * a ^ 2
  have htau : 0 < tau := mul_pos hrho (pow_pos ha 2)
  have hsum : tau * (N : Real) ^ 3 ≤
      ∑ x ∈ B0, ‖fourier (difference f x) (phi x)‖ ^ 2 := by
    calc
      tau * (N : Real) ^ 3 = (rho * N) * (a * N) ^ 2 := by dsimp [tau]; ring
      _ = B0.card * (a * N) ^ 2 := by rw [← hcard]
      _ = ∑ _x ∈ B0, (a * N) ^ 2 := by simp
      _ ≤ _ := Finset.sum_le_sum fun x hx ↦
        pow_le_pow_left₀ (by positivity) (hlarge x hx) 2
  have hadd := proposition_6_1_holds N tau f B0 phi htau hf hsum
  let gamma : Real := rho * a ^ 8
  have hgamma : 0 < gamma := mul_pos hrho (pow_pos ha 8)
  have hquad : gamma * (rho * N) ^ 3 ≤ phiAdditiveCount B0 phi := by
    calc
      gamma * (rho * N) ^ 3 = tau ^ 4 * (N : Real) ^ 3 := by dsimp [gamma, tau]; ring
      _ ≤ _ := hadd
  obtain ⟨B, hsub, hmass, hfreiman⟩ :=
    corollary_7_6_holds N B0 phi rho gamma Fact.out hrho hgamma hcard hquad
  refine ⟨B, phi, ?_, hfreiman, fun x hx ↦ hlarge x (hsub hx)⟩
  have hc : a ^ 1882 ≤ (2 : Real) ^ (-(1882 : Real)) := by
    calc
      _ ≤ (1 / 2 : Real) ^ (1882 : Nat) := pow_le_pow_left₀ ha.le hahalf _
      _ = _ := by
        rw [Real.rpow_neg (by norm_num), one_div, inv_pow]
        exact congrArg (fun x : Real ↦ x⁻¹) (Real.rpow_natCast (2 : Real) 1882).symm
  have hcoef : a ^ 12359 ≤ (2 : Real) ^ (-(1882 : Real)) * a ^ 9312 * rho ^ 1165 := by
    calc
      a ^ 12359 = a ^ 1882 * a ^ 9312 * a ^ 1165 := by
        rw [show 12359 = 1882 + 9312 + 1165 by norm_num, pow_add, pow_add]
      _ ≤ _ := mul_le_mul
        (mul_le_mul_of_nonneg_right hc (pow_nonneg ha.le 9312))
        (pow_le_pow_left₀ ha.le harho 1165) (pow_nonneg ha.le 1165) (by positivity)
  calc
    a ^ 12359 * N ≤ ((2 : Real) ^ (-(1882 : Real)) * a ^ 9312 * rho ^ 1165) * N :=
      mul_le_mul_of_nonneg_right hcoef hN.le
    _ = (2 : Real) ^ (-(1882 : Real)) * gamma ^ 1164 * rho * N := by dsimp [gamma]; ring
    _ ≤ _ := hmass

end LeanProofs.GowersSzemeredi
