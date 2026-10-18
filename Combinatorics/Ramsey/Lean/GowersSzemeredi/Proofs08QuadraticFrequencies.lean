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
  set a : Real := alpha / 2 with ha_def
  have ha : 0 < a := by linarith
  have hahalf : a ≤ 1 / 2 := by linarith
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  obtain ⟨hi_ii, hii_iii, _, _, _, hvi_iii, _, hvii_vi⟩ :=
    lemma_3_1_holds N 2 f (by omega) hf alpha a a hα.le hαone ha.le (by linarith) ha.le
      (by linarith)
  have hnotvii : ¬ higherUniformConditionvii f a 2 := fun hvii ↦
    hnot (hi_ii.mpr (hii_iii.mpr (hvi_iii (by linarith) (hvii_vi le_rfl hvii))))
  -- the differences with a large Fourier coefficient, and a choice of such a frequency
  let good : ZMod N → Prop := fun x ↦ ∃ r, a * N ≤ ‖fourier (difference f x) r‖
  let B0 : Finset (ZMod N) := Finset.univ.filter good
  have hcountEq : countWhere (fun x : Point N 1 ↦
      ∃ r, a * N ≤ ‖fourier (cubeDifference f x) r‖) = B0.card := by
    unfold countWhere
    exact (Finset.card_equiv (pointOneEquiv N) fun y ↦ by simp [B0, good]).symm
  have hB0 : a * N ≤ (B0.card : Real) := by
    unfold higherUniformConditionvii at hnotvii
    simp only [Nat.reduceSub, pow_one, hcountEq] at hnotvii
    exact (lt_of_not_ge hnotvii).le
  choose! phi hlarge using fun x (hx : x ∈ B0) ↦ (Finset.mem_filter.mp hx).2
  let rho : Real := B0.card / (N : Real)
  have harho : a ≤ rho := (le_div_iff₀ hN).2 hB0
  have hrho : 0 < rho := ha.trans_le harho
  have hcard : (B0.card : Real) = rho * N := (div_mul_cancel₀ _ hN.ne').symm
  -- Proposition 6.1 and Corollary 7.6
  have hsum : rho * a ^ 2 * (N : Real) ^ 3 ≤
      ∑ x ∈ B0, ‖fourier (difference f x) (phi x)‖ ^ 2 := by
    have h := Finset.card_nsmul_le_sum B0 _ _ fun x hx ↦
      pow_le_pow_left₀ (by positivity) (hlarge x hx) 2
    rw [nsmul_eq_mul, hcard] at h
    linarith
  have hadd := proposition_6_1_holds N _ f B0 phi (mul_pos hrho (pow_pos ha 2)) hf hsum
  obtain ⟨B, hsub, hmass, hfreiman⟩ := corollary_7_6_holds N B0 phi rho (rho * a ^ 8)
    Fact.out hrho (mul_pos hrho (pow_pos ha 8)) hcard (by linarith)
  refine ⟨B, phi, ?_, hfreiman, fun x hx ↦ hlarge x (hsub hx)⟩
  have hc : a ^ 1882 ≤ (2 : Real) ^ (-(1882 : Real)) := by
    calc
      _ ≤ (1 / 2 : Real) ^ (1882 : Nat) := pow_le_pow_left₀ ha.le hahalf _
      _ = _ := by
        rw [Real.rpow_neg (by norm_num), one_div, inv_pow]
        exact congrArg (fun x : Real ↦ x⁻¹) (Real.rpow_natCast (2 : Real) 1882).symm
  calc
    a ^ 12359 * N = a ^ 1882 * a ^ 9312 * a ^ 1165 * N := by rw [← pow_add, ← pow_add]
    _ ≤ (2 : Real) ^ (-(1882 : Real)) * a ^ 9312 * rho ^ 1165 * N := by gcongr
    _ = (2 : Real) ^ (-(1882 : Real)) * (rho * a ^ 8) ^ 1164 * rho * N := by ring_nf
    _ ≤ _ := hmass

end LeanProofs.GowersSzemeredi
