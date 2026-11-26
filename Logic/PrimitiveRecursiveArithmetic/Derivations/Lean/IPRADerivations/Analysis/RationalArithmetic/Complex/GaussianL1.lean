import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianRootAlgebra
import IPRADerivations.Foundations.GapDecision

/-!
# The actual Gaussian coefficient L1 norm

For the finite-demand approximate-factorization construction, the L1 norm
is the sum of the two actual signed absolute values. Its triangle and
product bounds, exact natural scaling and comparison with squared Euclidean
norm are ordinary iPRA derivations. No canonical signed-part condition,
positive norm, supplied norm law or externally fixed degree is assumed.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianL1

open_ipra
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder
  (re im add mul scale zeroCode oneCode normSq bounded)
open LeanProofs.IPRA.Analysis.GaussianRootAlgebra
  (equal equal_re equal_im re_add im_add re_mul im_mul re_neg im_neg re_scale im_scale re_zero im_zero re_one im_one)
open LeanProofs.IPRA.Foundations.GapDecision (zabs subst_zabs zabs_sq zabs_congr zabs_tri zabs_neg)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem abs_ofNat (a : PTm n) : Γ ⊢[PRAAx] zabs (ZT.ofNat a) ≐ a :=
  (congrAdd (monus_zero a) (zero_monus a)).eqTrans (add_zero a)

/-- Multiplicativity of signed absolute value uses natural square
comparison, not an integral-domain assumption on the metatheory quotient. -/
theorem abs_multiply (a b : ZT n) : Γ ⊢[PRAAx] zabs (a*b) ≐ zabs a*zabs b := by
  have squares : Γ ⊢[PRAAx] zabs (a*b)*zabs (a*b) ≐ (zabs a*zabs b)*(zabs a*zabs b) := by
    have aa := zabs_sq (Γ := Γ) a
    have bb := zabs_sq (Γ := Γ) b
    have ab := zabs_sq (Γ := Γ) (a*b)
    simp only [ZT.toZ_mul,Q.mk_mul,map_mul] at aa bb ab
    apply deriveNat
    ipra_simps
    calc
      _ = (ZT.toZ Γ a*ZT.toZ Γ b)*(ZT.toZ Γ a*ZT.toZ Γ b) := ab
      _ = (ZT.toZ Γ a*ZT.toZ Γ a)*(ZT.toZ Γ b*ZT.toZ Γ b) := by ring
      _ = _ := by rw [← aa,← bb]; ring
  exact le_antisymm (nat_sqrt_mono (le_congr (.eqRefl _) squares (le_refl _)))
    (nat_sqrt_mono (le_congr (.eqRefl _) squares.eqSymm (le_refl _)))

theorem abs_scale (C : PTm n) (a : ZT n) : Γ ⊢[PRAAx] zabs (ZT.ofNat C*a) ≐ C*zabs a :=
  (abs_multiply _ _).eqTrans (congrMul (abs_ofNat C) (.eqRefl _))

def norm1 (a : PTm n) : PTm n := zabs (re a)+zabs (im a)

@[simp] theorem subst_norm1 {m : ℕ} (σ : Fin n → PTm m) (a : PTm n) :
    Syn.subst σ (norm1 a) = norm1 (Syn.subst σ a) := by
  unfold norm1
  rw [PTm.subst_add,subst_zabs,subst_zabs]
  simp only [ComplexLogarithmRemainder.subst_re,ComplexLogarithmRemainder.subst_im]

theorem norm1_equal {a b : PTm n} (h : Γ ⊢[PRAAx] equal a b) : Γ ⊢[PRAAx] norm1 a ≐ norm1 b :=
  congrAdd (zabs_congr (equal_re h)) (zabs_congr (equal_im h))

theorem norm1_zero : Γ ⊢[PRAAx] norm1 (zeroCode : PTm n) ≐ zero := by
  have r : Γ ⊢[PRAAx] zabs (re (zeroCode : PTm n)) ≐ zero :=
    (zabs_congr (v := ZT.ofNat zero) (by rw [re_zero,ZT.toZ_ofNat]; ipra_simps)).eqTrans (abs_ofNat zero)
  have i : Γ ⊢[PRAAx] zabs (im (zeroCode : PTm n)) ≐ zero :=
    (zabs_congr (v := ZT.ofNat zero) (by rw [im_zero,ZT.toZ_ofNat]; ipra_simps)).eqTrans (abs_ofNat zero)
  exact (congrAdd r i).eqTrans (zero_add zero)

theorem norm1_one : Γ ⊢[PRAAx] norm1 (oneCode : PTm n) ≐ one := by
  have r : Γ ⊢[PRAAx] zabs (re (oneCode : PTm n)) ≐ one :=
    (zabs_congr (v := ZT.ofNat one) (by rw [re_one,ZT.toZ_ofNat]; ipra_simps <;> ring)).eqTrans (abs_ofNat one)
  have i : Γ ⊢[PRAAx] zabs (im (oneCode : PTm n)) ≐ zero :=
    (zabs_congr (v := ZT.ofNat zero) (by rw [im_one,ZT.toZ_ofNat]; ipra_simps)).eqTrans (abs_ofNat zero)
  exact (congrAdd r i).eqTrans (add_zero one)

theorem norm1_add (a b : PTm n) : Γ ⊢[PRAAx] le (norm1 (add a b)) (norm1 a+norm1 b) := by
  have r := zabs_tri (Γ := Γ) (u := re a) (v := re b) (w := re (add a b)) (re_add a b)
  have i := zabs_tri (Γ := Γ) (u := im a) (v := im b) (w := im (add a b)) (im_add a b)
  exact le_congr (.eqRefl _) (by unfold norm1; ipra_ring) (add_le_add₂ r i)

theorem norm1_negative (a : PTm n) : Γ ⊢[PRAAx] norm1 (ComplexLogarithmRemainder.neg a) ≐ norm1 a :=
  congrAdd
    ((zabs_congr (v := -re a) (by rw [re_neg,ZT.toZ_neg])).eqTrans (zabs_neg _))
    ((zabs_congr (v := -im a) (by rw [im_neg,ZT.toZ_neg])).eqTrans (zabs_neg _))

theorem norm1_sub (a b : PTm n) : Γ ⊢[PRAAx]
    le (norm1 (GaussianRootAlgebra.sub a b)) (norm1 a+norm1 b) :=
  le_congr (.eqRefl _) (congrAdd (.eqRefl _) (norm1_negative b)) (norm1_add a _)

theorem norm1_multiply (a b : PTm n) : Γ ⊢[PRAAx] le (norm1 (mul a b)) (norm1 a*norm1 b) := by
  have r := zabs_tri (Γ := Γ) (u := re a*re b) (v := -(im a*im b)) (w := re (mul a b))
    (by simp only [re_mul,ZT.toZ_mul,ZT.toZ_neg] <;> ring)
  have i := zabs_tri (Γ := Γ) (u := re a*im b) (v := im a*re b) (w := im (mul a b))
    (by simp only [im_mul,ZT.toZ_mul] <;> ring)
  have r' := le_congr (.eqRefl _)
    (congrAdd (abs_multiply _ _) ((zabs_neg _).eqTrans (abs_multiply _ _))) r
  have i' := le_congr (.eqRefl _) (congrAdd (abs_multiply _ _) (abs_multiply _ _)) i
  exact le_congr (.eqRefl _) (by unfold norm1; ipra_ring) (add_le_add₂ r' i')

theorem norm1_scale (C a : PTm n) : Γ ⊢[PRAAx] norm1 (scale C a) ≐ C*norm1 a := by
  have r : Γ ⊢[PRAAx] zabs (re (scale C a)) ≐ C*zabs (re a) :=
    (zabs_congr (v := ZT.ofNat C*re a) (by rw [re_scale,ZT.toZ_mul,ZT.toZ_ofNat])).eqTrans (abs_scale C _)
  have i : Γ ⊢[PRAAx] zabs (im (scale C a)) ≐ C*zabs (im a) :=
    (zabs_congr (v := ZT.ofNat C*im a) (by rw [im_scale,ZT.toZ_mul,ZT.toZ_ofNat])).eqTrans (abs_scale C _)
  exact (congrAdd r i).eqTrans (by unfold norm1; ipra_ring)

theorem normSq_le_norm1_square (a : PTm n) : Γ ⊢[PRAAx] le (normSq a) (norm1 a*norm1 a) := by
  refine le_of_eq_add (d := two*zabs (re a)*zabs (im a)) ?_
  unfold norm1 normSq
  ipra_ring

theorem norm1_square_le_two_normSq (a : PTm n) : Γ ⊢[PRAAx] le (norm1 a*norm1 a) (two*normSq a) := by
  have e := natEq (Probability.Variance.ad_sq (Γ := Γ) (zabs (re a)) (zabs (im a)))
  refine le_of_eq_add (d := Probability.Variance.ad (zabs (re a)) (zabs (im a))*
    Probability.Variance.ad (zabs (re a)) (zabs (im a))) ?_
  apply deriveNat
  unfold norm1 normSq
  ipra_simps
  linear_combination -e

/-- The source estimate ||z||1≤2R follows from its actual squared
Euclidean comparison, including zero R. -/
theorem norm1_of_bounded (a R : PTm n) (h : Γ ⊢[PRAAx] bounded a R) :
    Γ ⊢[PRAAx] le (norm1 a) (two*R) := by
  apply nat_sqrt_mono
  have h' := le_trans (norm1_square_le_two_normSq a) (le_mul_mono (le_refl two) h)
  exact le_trans h' (le_of_eq_add (d := two*(R*R)) (by ipra_ring))

def norm1F : PR 1 := PTm.toPR (norm1 (var 0))
theorem norm1_program (a : PTm n) : Γ ⊢[PRAAx] ap1 norm1F a ≐ norm1 a := by
  simpa [norm1F,ap1] using toPR_eq (Γ := Γ) (norm1 (var 0) : PTm 1) ![a]

theorem gaussian_l1_algebra_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (norm1 (add (var 0) (var 1))) (norm1 (var 0)+norm1 (var 1)) ⋏
      (le (norm1 (mul (var 0) (var 1))) (norm1 (var 0)*norm1 (var 1)) ⋏
        (norm1 (scale (var 0) (var 1)) ≐ var 0*norm1 (var 1)))) :=
  closeUniv 2 (.andI (norm1_add _ _) (.andI (norm1_multiply _ _) (norm1_scale _ _)))

theorem gaussian_l1_euclidean_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (normSq (var 0)) (norm1 (var 0)*norm1 (var 0)) ⋏
      (le (norm1 (var 0)*norm1 (var 0)) (two*normSq (var 0)) ⋏
        (bounded (var 0) (var 1) ⟶ le (norm1 (var 0)) (two*var 1)))) :=
  closeUniv 2 (.andI (normSq_le_norm1_square _) (.andI (norm1_square_le_two_normSq _)
    (.impI (norm1_of_bounded _ _ Prf.hyp0))))

theorem gaussian_l1_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (ap1 norm1F (var 0) ≐ norm1 (var 0)) := closeUniv 1 (norm1_program _)

end LeanProofs.IPRA.Analysis.GaussianL1
