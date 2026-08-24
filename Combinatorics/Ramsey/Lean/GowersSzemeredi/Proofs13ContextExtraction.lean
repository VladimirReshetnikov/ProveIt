import GowersSzemeredi.Proofs03Equivalences
import GowersSzemeredi.Proofs05_10
import GowersSzemeredi.Proofs07AdditiveRestriction
import GowersSzemeredi.Proofs12Combination

/-!
# Extracting the separately Freiman context

This file proves Lemma 13.11.  There is a quantitative omission in the paper's
proof: on a fibre of density `rho`, Proposition 6.1 and Corollary 7.6 must be
used with additive parameter `rho * (alpha / 2) ^ 8`, not `rho`.  Keeping this
factor through both fibre restrictions gives density `(alpha / 2) ^ (2 ^ 24)`.
Lemma 12.6 then gives `(alpha / 2) ^ (2 ^ 68) * N ^ 32` arrangements.  The
sharp elementary upper bound `arrangementCount 8 A ≤ A.card ^ 15 * N ^ 2`
recovers the stated cardinality `(alpha / 2) ^ (2 ^ 66) * N ^ 2`.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private def contextSwapEquiv (N : Nat) : Pair N ≃ Point N 2 where
  toFun z := ![z.2, z.1]
  invFun x := (x 1, x 0)
  left_inv z := by ext <;> simp
  right_inv x := by
    funext i
    fin_cases i <;> simp

private lemma context_cubeDifference_eq {N : Nat}
    (f : ZMod N → Complex) (z : Pair N) :
    cubeDifference f (contextSwapEquiv N z) =
      secondDifference f z.1 z.2 := by
  change cubeDifference f (Fin.cons z.2 (Fin.cons z.1 (fun i ↦ Fin.elim0 i))) =
    secondDifference f z.1 z.2
  rw [cubeDifference_cons, cubeDifference_cons]
  simp only [cubeDifference, List.ofFn_zero, iteratedDifference, secondDifference]

private lemma context_countWhere_eq_sum_ite {X : Type*} [Fintype X]
    (P : X → Prop) :
    countWhere P = ∑ x : X,
      @ite Nat (P x) (Classical.propDecidable (P x)) 1 0 := by
  classical
  unfold countWhere
  simp

private lemma context_countWhere_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (P : Y → Prop) :
    countWhere P = countWhere (fun x ↦ P (e x)) := by
  classical
  simp_rw [context_countWhere_eq_sum_ite]
  exact (e.sum_comp (fun y ↦ if P y then 1 else 0)).symm

private lemma context_countWhere_prod {X Y : Type*} [Fintype X] [Fintype Y]
    (P : X → Y → Prop) :
    countWhere (fun z : X × Y ↦ P z.1 z.2) =
      ∑ x : X, countWhere (P x) := by
  classical
  simp_rw [context_countWhere_eq_sum_ite]
  rw [Fintype.sum_prod_type]

private lemma context_density_moment_identity (K R n : Real) (hn : n ≠ 0) :
    K * (R / n) ^ 1165 * n ^ 2 =
      (K * n) * (R ^ 1165 / n ^ 1164) := by
  field_simp [hn]

private lemma context_sum_vertical_card {N : Nat} [NeZero N]
    (B : Finset (Pair N)) :
    ∑ x : ZMod N, (verticalSection B x).card = B.card := by
  classical
  calc
    ∑ x : ZMod N, (verticalSection B x).card =
        ∑ x : ZMod N, countWhere (fun y : ZMod N ↦ (x, y) ∈ B) := by
      apply Fintype.sum_congr
      intro x
      unfold verticalSection countWhere
      apply congrArg Finset.card
      ext y
      simp
    _ = countWhere (fun z : Pair N ↦ z ∈ B) :=
      (context_countWhere_prod _).symm
    _ = B.card := by simp [countWhere]

private lemma context_sum_horizontal_card {N : Nat} [NeZero N]
    (B : Finset (Pair N)) :
    ∑ y : ZMod N, (horizontalSection B y).card = B.card := by
  classical
  calc
    ∑ y : ZMod N, (horizontalSection B y).card =
        ∑ y : ZMod N, countWhere (fun x : ZMod N ↦ (x, y) ∈ B) := by
      apply Fintype.sum_congr
      intro y
      unfold horizontalSection countWhere
      apply congrArg Finset.card
      ext x
      simp
    _ = ∑ x : ZMod N,
        countWhere (fun y : ZMod N ↦ (x, y) ∈ B) := by
      simp_rw [context_countWhere_eq_sum_ite]
      rw [Finset.sum_comm]
    _ = ∑ x : ZMod N, (verticalSection B x).card := by
      apply Fintype.sum_congr
      intro x
      unfold verticalSection countWhere
      apply congrArg Finset.card
      ext y
      simp
    _ = B.card := context_sum_vertical_card B

private lemma context_restrict_fibres {N : Nat} [NeZero N]
    (hprime : Nat.Prime N) (a : Real) (ha : 0 < a)
    (S : ZMod N → Finset (ZMod N))
    (g : ZMod N → ZMod N → Complex)
    (psi : ZMod N → ZMod N → ZMod N)
    (hg : ∀ x, DiscValued (g x))
    (hlarge : ∀ x y, y ∈ S x →
      a * N ≤ ‖fourier (difference (g x) y) (psi x y)‖) :
    ∃ T : ZMod N → Finset (ZMod N),
      (∀ x, T x ⊆ S x) ∧
      (∀ x, FreimanHom 8 (T x) (psi x)) ∧
      (2 : Real) ^ (-(1882 : Real)) * a ^ 9312 *
          ((∑ x : ZMod N, (S x).card / (N : Real)) / (N : Real)) ^ 1165 *
          (N : Real) ^ 2 ≤
        ∑ x : ZMod N, ((T x).card : Real) := by
  classical
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hN0 : (N : Real) ≠ 0 := hN.ne'
  let rho : ZMod N → Real := fun x ↦ (S x).card / (N : Real)
  have hrho_nonneg (x : ZMod N) : 0 ≤ rho x := by
    dsimp only [rho]
    positivity
  have hpiece : ∀ x, ∃ T : Finset (ZMod N),
      T ⊆ S x ∧
      (2 : Real) ^ (-(1882 : Real)) * a ^ 9312 *
          rho x ^ 1165 * (N : Real) ≤ (T.card : Real) ∧
      FreimanHom 8 T (psi x) := by
    intro x
    by_cases hx0 : (S x).card = 0
    · refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
      · simp [rho, hx0]
      · simp [FreimanHom]
    · have hrho : 0 < rho x := by
        dsimp only [rho]
        exact div_pos (by exact_mod_cast Nat.pos_of_ne_zero hx0) hN
      have hScard : ((S x).card : Real) = rho x * N := by
        dsimp only [rho]
        field_simp [hN0]
      let tau : Real := rho x * a ^ 2
      have htau : 0 < tau := mul_pos hrho (pow_pos ha 2)
      have hsum :
          tau * (N : Real) ^ 3 ≤
            ∑ y ∈ S x, ‖fourier (difference (g x) y) (psi x y)‖ ^ 2 := by
        calc
          tau * (N : Real) ^ 3 =
              (rho x * N) * (a * N) ^ 2 := by
            dsimp only [tau]
            ring
          _ = (S x).card * (a * N) ^ 2 := by rw [← hScard]
          _ = ∑ _y ∈ S x, (a * N) ^ 2 := by simp
          _ ≤ ∑ y ∈ S x,
              ‖fourier (difference (g x) y) (psi x y)‖ ^ 2 := by
            exact Finset.sum_le_sum fun y hy ↦
              pow_le_pow_left₀ (by positivity) (hlarge x y hy) 2
      have hadd := proposition_6_1_holds N tau (g x) (S x) (psi x)
        htau (hg x) hsum
      let gamma : Real := rho x * a ^ 8
      have hgamma : 0 < gamma := mul_pos hrho (pow_pos ha 8)
      have hquad :
          gamma * (rho x * N) ^ 3 ≤ phiAdditiveCount (S x) (psi x) := by
        calc
          gamma * (rho x * N) ^ 3 = tau ^ 4 * (N : Real) ^ 3 := by
            dsimp only [gamma, tau]
            ring
          _ ≤ (phiAdditiveCount (S x) (psi x) : Real) := hadd
      obtain ⟨T, hTsub, hTcard, hTfreiman⟩ :=
        corollary_7_6_holds N (S x) (psi x) (rho x) gamma hprime hrho hgamma
          hScard hquad
      refine ⟨T, hTsub, ?_, hTfreiman⟩
      calc
        (2 : Real) ^ (-(1882 : Real)) * a ^ 9312 * rho x ^ 1165 *
              (N : Real) =
            (2 : Real) ^ (-(1882 : Real)) * gamma ^ 1164 * rho x *
              (N : Real) := by
          dsimp only [gamma]
          ring
        _ ≤ (T.card : Real) := hTcard
  choose T hTsub hTcard hTfreiman using hpiece
  refine ⟨T, hTsub, hTfreiman, ?_⟩
  have hmean := pow_sum_div_card_le_sum_pow
    (s := (Finset.univ : Finset (ZMod N))) (f := rho)
    (fun x _ ↦ hrho_nonneg x) 1164
  simp only [Finset.card_univ, ZMod.card, Nat.reduceAdd] at hmean
  have hpieces :
      ∑ x : ZMod N,
          (2 : Real) ^ (-(1882 : Real)) * a ^ 9312 * rho x ^ 1165 * N ≤
        ∑ x : ZMod N, ((T x).card : Real) := by
    exact Finset.sum_le_sum fun x _ ↦ hTcard x
  calc
    (2 : Real) ^ (-(1882 : Real)) * a ^ 9312 *
          ((∑ x : ZMod N, (S x).card / (N : Real)) / (N : Real)) ^ 1165 *
          (N : Real) ^ 2 =
        ((2 : Real) ^ (-(1882 : Real)) * a ^ 9312 * N) *
          ((∑ x : ZMod N, rho x) ^ 1165 / (N : Real) ^ 1164) := by
      have hrhoSum :
          (∑ x : ZMod N, (S x).card / (N : Real)) =
            ∑ x : ZMod N, rho x := by rfl
      rw [hrhoSum]
      exact context_density_moment_identity
        ((2 : Real) ^ (-(1882 : Real)) * a ^ 9312)
        (∑ x : ZMod N, rho x) (N : Real) hN0
    _ ≤ ((2 : Real) ^ (-(1882 : Real)) * a ^ 9312 * N) *
          ∑ x : ZMod N, rho x ^ 1165 := by
      exact mul_le_mul_of_nonneg_left hmean (by positivity)
    _ = ∑ x : ZMod N,
          (2 : Real) ^ (-(1882 : Real)) * a ^ 9312 * rho x ^ 1165 * N := by
      rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro x
      ac_rfl
    _ ≤ ∑ x : ZMod N, ((T x).card : Real) := hpieces

private noncomputable def contextVerticalJoin {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) : Finset (Pair N) :=
  Finset.univ.filter fun z ↦ z.2 ∈ T z.1

private noncomputable def contextHorizontalJoin {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) : Finset (Pair N) :=
  Finset.univ.filter fun z ↦ z.1 ∈ T z.2

private lemma context_vertical_join_section {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (x : ZMod N) :
    verticalSection (contextVerticalJoin T) x = T x := by
  classical
  ext y
  simp [verticalSection, contextVerticalJoin]

private lemma context_horizontal_join_section {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (y : ZMod N) :
    horizontalSection (contextHorizontalJoin T) y = T y := by
  classical
  ext x
  simp [horizontalSection, contextHorizontalJoin]

private lemma context_vertical_join_card {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) :
    (contextVerticalJoin T).card = ∑ x : ZMod N, (T x).card := by
  classical
  calc
    (contextVerticalJoin T).card =
        countWhere (fun z : Pair N ↦ z.2 ∈ T z.1) := by
      unfold contextVerticalJoin countWhere
      apply congrArg Finset.card
      ext z
      simp
    _ = ∑ x : ZMod N, countWhere (fun y : ZMod N ↦ y ∈ T x) :=
      context_countWhere_prod (X := ZMod N) (Y := ZMod N)
        (fun x y ↦ y ∈ T x)
    _ = ∑ x : ZMod N, (T x).card := by simp [countWhere]

private lemma context_horizontal_join_card {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) :
    (contextHorizontalJoin T).card = ∑ y : ZMod N, (T y).card := by
  classical
  calc
    (contextHorizontalJoin T).card =
        countWhere (fun z : ZMod N × ZMod N ↦ z.1 ∈ T z.2) := by
      unfold contextHorizontalJoin countWhere
      apply congrArg Finset.card
      ext z
      simp
    _ = countWhere (fun z : ZMod N × ZMod N ↦ z.2 ∈ T z.1) := by
      simpa [Prod.swap] using context_countWhere_equiv
        (Equiv.prodComm (ZMod N) (ZMod N))
        (fun z : ZMod N × ZMod N ↦ z.1 ∈ T z.2)
    _ = ∑ y : ZMod N, countWhere (fun x : ZMod N ↦ x ∈ T y) :=
      context_countWhere_prod (X := ZMod N) (Y := ZMod N)
        (fun y x ↦ x ∈ T y)
    _ = ∑ y : ZMod N, (T y).card := by simp [countWhere]

private lemma context_vertical_restriction {N : Nat} [NeZero N]
    (hprime : Nat.Prime N) (a : Real) (ha : 0 < a)
    (f : ZMod N → Complex) (hf : DiscValued f)
    (B : Finset (Pair N)) (phi : Pair N → ZMod N)
    (hlarge : ∀ z, z ∈ B →
      a * N ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖) :
    ∃ B' : Finset (Pair N), B' ⊆ B ∧
      (2 : Real) ^ (-(1882 : Real)) * a ^ 9312 *
          ((B.card : Real) / (N : Real) ^ 2) ^ 1165 * (N : Real) ^ 2 ≤
        B'.card ∧
      ∀ x, FreimanHom 8 (verticalSection B' x) (fun y ↦ phi (x, y)) := by
  classical
  obtain ⟨T, hTsub, hTfreiman, hTcard⟩ := context_restrict_fibres hprime a ha
    (fun x ↦ verticalSection B x) (fun x ↦ difference f x)
    (fun x y ↦ phi (x, y)) (fun x ↦ difference_discValued hf x) (by
      intro x y hy
      have hxy : (x, y) ∈ B := by simpa [verticalSection] using hy
      simpa only [secondDifferenceFourier, secondDifference] using
        hlarge (x, y) hxy)
  let B' := contextVerticalJoin T
  refine ⟨B', ?_, ?_, ?_⟩
  · intro z hz
    have hzT : z.2 ∈ T z.1 := by simpa [B', contextVerticalJoin] using hz
    simpa [verticalSection] using hTsub z.1 hzT
  · have hsumReal :
        ∑ x : ZMod N, ((verticalSection B x).card : Real) = B.card := by
      exact_mod_cast context_sum_vertical_card B
    have hcardReal : (B'.card : Real) =
        ∑ x : ZMod N, ((T x).card : Real) := by
      exact_mod_cast context_vertical_join_card T
    have hdensity : (B.card : Real) / (N : Real) ^ 2 =
        (∑ x : ZMod N, (verticalSection B x).card / (N : Real)) /
          (N : Real) := by
      rw [← Finset.sum_div, hsumReal]
      field_simp [show (N : Real) ≠ 0 by exact_mod_cast NeZero.ne N]
    calc
      (2 : Real) ^ (-(1882 : Real)) * a ^ 9312 *
            ((B.card : Real) / (N : Real) ^ 2) ^ 1165 * (N : Real) ^ 2 =
          (2 : Real) ^ (-(1882 : Real)) * a ^ 9312 *
            ((∑ x : ZMod N, (verticalSection B x).card / (N : Real)) /
              (N : Real)) ^ 1165 * (N : Real) ^ 2 := by rw [hdensity]
      _ ≤ ∑ x : ZMod N, ((T x).card : Real) := hTcard
      _ = B'.card := hcardReal.symm
  · intro x
    rw [context_vertical_join_section]
    exact hTfreiman x

private lemma context_horizontal_restriction {N : Nat} [NeZero N]
    (hprime : Nat.Prime N) (a : Real) (ha : 0 < a)
    (f : ZMod N → Complex) (hf : DiscValued f)
    (B : Finset (Pair N)) (phi : Pair N → ZMod N)
    (hlarge : ∀ z, z ∈ B →
      a * N ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖) :
    ∃ B' : Finset (Pair N), B' ⊆ B ∧
      (2 : Real) ^ (-(1882 : Real)) * a ^ 9312 *
          ((B.card : Real) / (N : Real) ^ 2) ^ 1165 * (N : Real) ^ 2 ≤
        B'.card ∧
      ∀ y, FreimanHom 8 (horizontalSection B' y) (fun x ↦ phi (x, y)) := by
  classical
  obtain ⟨T, hTsub, hTfreiman, hTcard⟩ := context_restrict_fibres hprime a ha
    (fun y ↦ horizontalSection B y) (fun y ↦ difference f y)
    (fun y x ↦ phi (x, y)) (fun y ↦ difference_discValued hf y) (by
      intro y x hx
      have hxy : (x, y) ∈ B := by simpa [horizontalSection] using hx
      have h := hlarge (x, y) hxy
      unfold secondDifferenceFourier secondDifference at h
      rw [difference_comm f x y] at h
      exact h)
  let B' := contextHorizontalJoin T
  refine ⟨B', ?_, ?_, ?_⟩
  · intro z hz
    have hzT : z.1 ∈ T z.2 := by simpa [B', contextHorizontalJoin] using hz
    simpa [horizontalSection] using hTsub z.2 hzT
  · have hsumReal :
        ∑ y : ZMod N, ((horizontalSection B y).card : Real) = B.card := by
      exact_mod_cast context_sum_horizontal_card B
    have hcardReal : (B'.card : Real) =
        ∑ y : ZMod N, ((T y).card : Real) := by
      exact_mod_cast context_horizontal_join_card T
    have hdensity : (B.card : Real) / (N : Real) ^ 2 =
        (∑ y : ZMod N, (horizontalSection B y).card / (N : Real)) /
          (N : Real) := by
      rw [← Finset.sum_div, hsumReal]
      field_simp [show (N : Real) ≠ 0 by exact_mod_cast NeZero.ne N]
    calc
      (2 : Real) ^ (-(1882 : Real)) * a ^ 9312 *
            ((B.card : Real) / (N : Real) ^ 2) ^ 1165 * (N : Real) ^ 2 =
          (2 : Real) ^ (-(1882 : Real)) * a ^ 9312 *
            ((∑ y : ZMod N, (horizontalSection B y).card / (N : Real)) /
              (N : Real)) ^ 1165 * (N : Real) ^ 2 := by rw [hdensity]
      _ ≤ ∑ y : ZMod N, ((T y).card : Real) := hTcard
      _ = B'.card := hcardReal.symm
  · intro y
    rw [context_horizontal_join_section]
    exact hTfreiman y

private lemma context_cor76_constant_lower (a : Real) (ha : 0 ≤ a)
    (haHalf : a ≤ 1 / 2) :
    a ^ 1882 ≤ (2 : Real) ^ (-(1882 : Real)) := by
  calc
    a ^ 1882 ≤ (1 / 2 : Real) ^ 1882 :=
      pow_le_pow_left₀ ha haHalf 1882
    _ = (2 : Real) ^ (-(1882 : Real)) := by
      rw [Real.rpow_neg (by norm_num), one_div, inv_pow]
      exact congrArg (fun x : Real => x⁻¹)
        (Real.rpow_natCast (2 : Real) 1882).symm

private lemma context_eta_eq :
    (1 / 2 : Real) ^ 44 = (2 : Real) ^ (-(44 : Int)) := by
  rw [show (-(44 : Int)) = Int.negSucc 43 by decide, zpow_negSucc,
    one_div, inv_pow]

private lemma context_prefactor_lower (a : Real) (ha : 0 ≤ a)
    (haHalf : a ≤ 1 / 2) :
    a ^ ((2 : Nat) ^ 37) ≤ (2 : Real) ^ (-((2 : Real) ^ 37)) := by
  have ha2 : a ^ 2 ≤ (4 : Real)⁻¹ := by
    calc
      a ^ 2 ≤ (1 / 2 : Real) ^ 2 := pow_le_pow_left₀ ha haHalf 2
      _ = (4 : Real)⁻¹ := by norm_num
  calc
    a ^ ((2 : Nat) ^ 37) = (a ^ 2) ^ ((2 : Nat) ^ 36) := by
      rw [← pow_mul]
      congr 1
    _ ≤ ((4 : Real)⁻¹) ^ ((2 : Nat) ^ 36) :=
      pow_le_pow_left₀ (by positivity) ha2 _
    _ = (2 : Real) ^ (-((2 : Real) ^ 37)) := by
      symm
      rw [Real.rpow_neg (by positivity)]
      rw [show (2 : Real) ^ 37 =
          2 * (((2 : Nat) ^ 36 : Nat) : Real) by norm_num]
      rw [Real.rpow_mul_natCast (by norm_num : (0 : Real) ≤ 2)]
      norm_num only [Real.rpow_two]
      rw [← inv_pow]
      norm_num

private lemma context_coefficient_lower (a : Real) (ha : 0 < a)
    (haHalf : a ≤ 1 / 2) (haOne : a ≤ 1) :
    a ^ ((2 : Nat) ^ 68) ≤
      (2 : Real) ^ (-((2 : Real) ^ 37)) *
        (a ^ ((2 : Nat) ^ 24)) ^ ((2 : Nat) ^ 43) *
        a ^ ((2 : Nat) ^ 45) *
        ((1 / 2 : Real) ^ 44) ^ ((2 : Nat) ^ 36) := by
  have hpref := context_prefactor_lower a ha.le haHalf
  have ha44 : a ^ 44 ≤ (1 / 2 : Real) ^ 44 :=
    pow_le_pow_left₀ ha.le haHalf 44
  have hetaRaw : a ^ (44 * ((2 : Nat) ^ 36)) ≤
      ((1 / 2 : Real) ^ 44) ^ ((2 : Nat) ^ 36) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) ha44 _
  have heta : a ^ ((2 : Nat) ^ 42) ≤
      ((1 / 2 : Real) ^ 44) ^ ((2 : Nat) ^ 36) := by
    exact (pow_le_pow_of_le_one ha.le haOne (by norm_num)).trans hetaRaw
  have hexponent :
      (2 : Nat) ^ 37 + (2 : Nat) ^ 67 + (2 : Nat) ^ 45 + (2 : Nat) ^ 42 ≤
        (2 : Nat) ^ 68 := by norm_num
  have hbetaExponent :
      (a ^ ((2 : Nat) ^ 24)) ^ ((2 : Nat) ^ 43) =
        a ^ ((2 : Nat) ^ 67) := by
    rw [← pow_mul]
    congr 1
  calc
    a ^ ((2 : Nat) ^ 68) ≤
        a ^ ((2 : Nat) ^ 37 + (2 : Nat) ^ 67 +
          (2 : Nat) ^ 45 + (2 : Nat) ^ 42) :=
      pow_le_pow_of_le_one ha.le haOne hexponent
    _ = a ^ ((2 : Nat) ^ 37) * a ^ ((2 : Nat) ^ 67) *
          a ^ ((2 : Nat) ^ 45) * a ^ ((2 : Nat) ^ 42) := by
      rw [pow_add, pow_add, pow_add]
    _ = a ^ ((2 : Nat) ^ 37) *
          (a ^ ((2 : Nat) ^ 24)) ^ ((2 : Nat) ^ 43) *
          a ^ ((2 : Nat) ^ 45) * a ^ ((2 : Nat) ^ 42) := by
      rw [hbetaExponent]
    _ ≤ (2 : Real) ^ (-((2 : Real) ^ 37)) *
          (a ^ ((2 : Nat) ^ 24)) ^ ((2 : Nat) ^ 43) *
          a ^ ((2 : Nat) ^ 45) *
          ((1 / 2 : Real) ^ 44) ^ ((2 : Nat) ^ 36) := by
      have hmiddle : 0 ≤
          (a ^ ((2 : Nat) ^ 24)) ^ ((2 : Nat) ^ 43) := by positivity
      have hgamma : 0 ≤ a ^ ((2 : Nat) ^ 45) := by positivity
      have hpref' :
          a ^ ((2 : Nat) ^ 37) *
              (a ^ ((2 : Nat) ^ 24)) ^ ((2 : Nat) ^ 43) ≤
            (2 : Real) ^ (-((2 : Real) ^ 37)) *
              (a ^ ((2 : Nat) ^ 24)) ^ ((2 : Nat) ^ 43) :=
        mul_le_mul_of_nonneg_right hpref hmiddle
      have hpref'' :
          a ^ ((2 : Nat) ^ 37) *
                (a ^ ((2 : Nat) ^ 24)) ^ ((2 : Nat) ^ 43) *
              a ^ ((2 : Nat) ^ 45) ≤
            (2 : Real) ^ (-((2 : Real) ^ 37)) *
                (a ^ ((2 : Nat) ^ 24)) ^ ((2 : Nat) ^ 43) *
              a ^ ((2 : Nat) ^ 45) :=
        mul_le_mul_of_nonneg_right hpref' hgamma
      exact mul_le_mul hpref'' heta (by positivity) (by positivity)

private def contextRestrictionLeft : Finset (Fin 16) :=
  Finset.univ.filter fun i ↦ (i : Nat) < 8

private def contextRestrictionRight : Finset (Fin 16) :=
  Finset.univ.filter fun i ↦ 8 ≤ (i : Nat)

private lemma context_zero_mem_left : (0 : Fin 16) ∈ contextRestrictionLeft := by
  simp [contextRestrictionLeft]

private lemma context_zero_notMem_right : (0 : Fin 16) ∉ contextRestrictionRight := by
  simp [contextRestrictionRight]

private lemma context_additive_ext {N : Nat}
    {x y : Fin 16 → ZMod N} (hx : IsAdditiveTuple (k := 8) x)
    (hy : IsAdditiveTuple (k := 8) y)
    (htail : ∀ i : Fin 15, x i.succ = y i.succ) : x = y := by
  have hoff : ∀ i : Fin 16, i ≠ 0 → x i = y i := by
    intro i hi
    rcases i with ⟨(_ | i), hiBound⟩
    · exact (hi rfl).elim
    · exact htail ⟨i, by omega⟩
  unfold IsAdditiveTuple at hx hy
  change (∑ i ∈ contextRestrictionLeft, x i) =
      ∑ i ∈ contextRestrictionRight, x i at hx
  change (∑ i ∈ contextRestrictionLeft, y i) =
      ∑ i ∈ contextRestrictionRight, y i at hy
  have hleft :
      (∑ i ∈ contextRestrictionLeft.erase 0, x i) =
        ∑ i ∈ contextRestrictionLeft.erase 0, y i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hoff i (Finset.ne_of_mem_erase hi)
  have hright :
      (∑ i ∈ contextRestrictionRight, x i) =
        ∑ i ∈ contextRestrictionRight, y i := by
    apply Finset.sum_congr rfl
    intro i hi
    apply hoff i
    intro hzero
    subst i
    exact context_zero_notMem_right hi
  funext i
  refine Fin.cases ?_ (fun j ↦ htail j) i
  apply add_left_cancel (a := ∑ i ∈ contextRestrictionLeft.erase 0, x i)
  calc
    (∑ i ∈ contextRestrictionLeft.erase 0, x i) + x 0 =
        ∑ i ∈ contextRestrictionLeft, x i :=
      Finset.sum_erase_add _ _ context_zero_mem_left
    _ = ∑ i ∈ contextRestrictionRight, x i := hx
    _ = ∑ i ∈ contextRestrictionRight, y i := hright
    _ = ∑ i ∈ contextRestrictionLeft, y i := hy.symm
    _ = (∑ i ∈ contextRestrictionLeft.erase 0, y i) + y 0 := by
      symm
      exact Finset.sum_erase_add _ _ context_zero_mem_left
    _ = (∑ i ∈ contextRestrictionLeft.erase 0, x i) + y 0 := by rw [hleft]

private abbrev contextTailCode {N : Nat} [NeZero N]
    (B : Finset (Pair N)) :=
  (Fin 15 → ↑B) × ZMod N × ZMod N

private def contextEncodeArrangement {N : Nat} [NeZero N]
    (B : Finset (Pair N))
    (R : {R : DArrangement N 8 // R.IsIn B}) : contextTailCode B :=
  (fun i ↦ ⟨(R.1.x i.succ, R.1.y i.succ), (R.2.2 i.succ).1⟩,
    R.1.y 0, R.1.height)

private lemma contextEncodeArrangement_injective {N : Nat} [NeZero N]
    (B : Finset (Pair N)) :
    Function.Injective (contextEncodeArrangement B) := by
  intro R S hcode
  apply Subtype.ext
  have hfun :
      (fun i : Fin 15 ↦
        (⟨(R.1.x i.succ, R.1.y i.succ), (R.2.2 i.succ).1⟩ : ↑B)) =
        fun i : Fin 15 ↦
          ⟨(S.1.x i.succ, S.1.y i.succ), (S.2.2 i.succ).1⟩ :=
    congrArg Prod.fst hcode
  have hxTail : ∀ i : Fin 15, R.1.x i.succ = S.1.x i.succ := by
    intro i
    exact congrArg (fun q ↦ (q i : Pair N).1) hfun
  have hyTail : ∀ i : Fin 15, R.1.y i.succ = S.1.y i.succ := by
    intro i
    exact congrArg (fun q ↦ (q i : Pair N).2) hfun
  have hx : R.1.x = S.1.x :=
    context_additive_ext R.2.1 S.2.1 hxTail
  have hy0 : R.1.y 0 = S.1.y 0 :=
    congrArg (fun c ↦ c.2.1) hcode
  have hy : R.1.y = S.1.y := by
    funext i
    refine Fin.cases hy0 (fun j ↦ hyTail j) i
  have hh : R.1.height = S.1.height :=
    congrArg (fun c ↦ c.2.2) hcode
  exact Prod.ext hx (Prod.ext hy hh)

private lemma context_arrangementCount_le_card_pow {N : Nat} [NeZero N]
    (B : Finset (Pair N)) :
    arrangementCount 8 B ≤ B.card ^ 15 * N ^ 2 := by
  classical
  unfold arrangementCount countWhere
  calc
    (Finset.univ.filter fun R : DArrangement N 8 ↦ R.IsIn B).card =
        Fintype.card {R : DArrangement N 8 // R.IsIn B} := by
      rw [Finset.filter_congr_decidable]
      exact (Fintype.card_subtype _).symm
    _ ≤ Fintype.card (contextTailCode B) :=
      Fintype.card_le_of_injective (contextEncodeArrangement B)
        (contextEncodeArrangement_injective B)
    _ = B.card ^ 15 * N ^ 2 := by
      simp only [contextTailCode, Fintype.card_prod, Fintype.card_fun,
        Fintype.card_fin, Fintype.card_coe, ZMod.card]
      ring

private lemma context_card_lower_of_arrangements {N : Nat} [NeZero N]
    (a : Real) (ha : 0 < a) (haOne : a ≤ 1)
    (A : Finset (Pair N))
    (harr : a ^ ((2 : Nat) ^ 68) * (N : Real) ^ 32 ≤
      arrangementCount 8 A) :
    a ^ ((2 : Nat) ^ 66) * (N : Real) ^ 2 ≤ A.card := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hN2 : 0 < (N : Real) ^ 2 := pow_pos hN 2
  have hupperNat := context_arrangementCount_le_card_pow A
  have hupper : (arrangementCount 8 A : Real) ≤
      (A.card : Real) ^ 15 * (N : Real) ^ 2 := by
    exact_mod_cast hupperNat
  by_contra hcard
  have hcardlt : (A.card : Real) <
      a ^ ((2 : Nat) ^ 66) * (N : Real) ^ 2 := lt_of_not_ge hcard
  have hpowlt : (A.card : Real) ^ 15 <
      (a ^ ((2 : Nat) ^ 66) * (N : Real) ^ 2) ^ 15 :=
    pow_lt_pow_left₀ hcardlt (by positivity) (by norm_num)
  have hcoefficient :
      (a ^ ((2 : Nat) ^ 66)) ^ 15 ≤ a ^ ((2 : Nat) ^ 68) := by
    rw [← pow_mul]
    exact pow_le_pow_of_le_one ha.le haOne (by norm_num)
  have hcontra : (arrangementCount 8 A : Real) <
      a ^ ((2 : Nat) ^ 68) * (N : Real) ^ 32 := by
    calc
      (arrangementCount 8 A : Real) ≤
          (A.card : Real) ^ 15 * (N : Real) ^ 2 := hupper
      _ < (a ^ ((2 : Nat) ^ 66) * (N : Real) ^ 2) ^ 15 *
          (N : Real) ^ 2 := mul_lt_mul_of_pos_right hpowlt hN2
      _ = (a ^ ((2 : Nat) ^ 66)) ^ 15 * (N : Real) ^ 32 := by ring
      _ ≤ a ^ ((2 : Nat) ^ 68) * (N : Real) ^ 32 :=
        mul_le_mul_of_nonneg_right hcoefficient (by positivity)
  exact (not_lt_of_ge harr) hcontra

/-- **Gowers, Lemma 13.11.** Failure of cubic uniformity yields a large
two-dimensional domain on which the selected Fourier frequency is separately
an order-eight Freiman homomorphism and respects almost every arrangement. -/
theorem lemma_13_11_holds : lemma_13_11 := by
  intro alpha halpha halphaOne
  let a : Real := alpha / 2
  let beta : Real := a ^ ((2 : Nat) ^ 24)
  let eta : Real := (1 / 2 : Real) ^ 44
  have ha : 0 < a := by dsimp only [a]; positivity
  have haHalf : a ≤ 1 / 2 := by dsimp only [a]; nlinarith
  have haOne : a ≤ 1 := haHalf.trans (by norm_num)
  have hbeta : 0 < beta := pow_pos ha _
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have hetaOne : eta ≤ 1 := by
    dsimp only [eta]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨N0, hN0⟩ :=
    lemma_12_6_holds beta a eta hbeta ha heta hetaOne
  refine ⟨N0, ?_⟩
  intro N _ _ hN f hf hnotUniform
  classical
  have hprime : Nat.Prime N := Fact.out
  have hNreal : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hN2 : 0 < (N : Real) ^ 2 := pow_pos hNreal 2
  obtain ⟨hi_ii, hii_iii, _hii_iv, _hi_v, _hiii_vi, hvi_iii,
      _hvi_vii, hvii_vi⟩ :=
    lemma_3_1_holds N 3 f (by omega) hf alpha a a
      halpha.le halphaOne ha.le haOne ha.le haOne
  have hnotvii : ¬ higherUniformConditionvii f a 3 := by
    intro hvii
    have hvi := hvii_vi (le_refl a) hvii
    have hiii := hvi_iii (by dsimp only [a]; ring_nf; exact le_rfl) hvi
    exact hnotUniform (hi_ii.mpr (hii_iii.mpr hiii))
  let P : Point N 2 → Prop := fun x ↦
    ∃ r : ZMod N, a * N ≤ ‖fourier (cubeDifference f x) r‖
  have hcount : a * (N : Real) ^ 2 < (countWhere P : Real) := by
    unfold higherUniformConditionvii at hnotvii
    simp only [Nat.reduceSub] at hnotvii
    exact lt_of_not_ge hnotvii
  let good : Pair N → Prop := fun z ↦ P (contextSwapEquiv N z)
  let A0 : Finset (Pair N) := Finset.univ.filter good
  have hcountEq : countWhere P = A0.card := by
    calc
      countWhere P = countWhere (fun z : Pair N ↦ P (contextSwapEquiv N z)) :=
        context_countWhere_equiv (contextSwapEquiv N) P
      _ = A0.card := by
        unfold A0 countWhere
        apply congrArg Finset.card
        ext z
        simp [good]
  have hA0card : a * (N : Real) ^ 2 ≤ A0.card := by
    rw [hcountEq] at hcount
    exact hcount.le
  let phi : Pair N → ZMod N := fun z ↦
    if hz : good z then Classical.choose hz else 0
  have hphi (z : Pair N) (hz : z ∈ A0) :
      a * N ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖ := by
    have hzgood : good z := by simpa [A0] using hz
    have hzlarge := Classical.choose_spec hzgood
    unfold secondDifferenceFourier
    rw [← context_cubeDifference_eq f z]
    simpa only [phi, dif_pos hzgood] using hzlarge
  obtain ⟨B1, hB1sub, hB1raw, hB1vertical⟩ :=
    context_vertical_restriction hprime a ha f hf A0 phi hphi
  have hconstant := context_cor76_constant_lower a ha.le haHalf
  have hA0density : a ≤ (A0.card : Real) / (N : Real) ^ 2 :=
    (le_div_iff₀ hN2).2 hA0card
  have hB1coefficient :
      a ^ 12359 ≤ (2 : Real) ^ (-(1882 : Real)) * a ^ 9312 *
        ((A0.card : Real) / (N : Real) ^ 2) ^ 1165 := by
    have hdensityPow : a ^ 1165 ≤
        ((A0.card : Real) / (N : Real) ^ 2) ^ 1165 :=
      pow_le_pow_left₀ ha.le hA0density 1165
    have hconstantMul : a ^ 1882 * a ^ 9312 ≤
        (2 : Real) ^ (-(1882 : Real)) * a ^ 9312 :=
      mul_le_mul_of_nonneg_right hconstant (pow_nonneg ha.le 9312)
    calc
      a ^ 12359 = a ^ 1882 * a ^ 9312 * a ^ 1165 := by
        rw [show 12359 = 1882 + 9312 + 1165 by norm_num, pow_add, pow_add]
      _ ≤ (2 : Real) ^ (-(1882 : Real)) * a ^ 9312 *
          ((A0.card : Real) / (N : Real) ^ 2) ^ 1165 :=
        mul_le_mul hconstantMul hdensityPow (pow_nonneg ha.le 1165) (by positivity)
  have hB1card : a ^ 12359 * (N : Real) ^ 2 ≤ B1.card :=
    (mul_le_mul_of_nonneg_right hB1coefficient hN2.le).trans hB1raw
  have hB1density : a ^ 12359 ≤ (B1.card : Real) / (N : Real) ^ 2 :=
    (le_div_iff₀ hN2).2 hB1card
  have hB1large (z : Pair N) (hz : z ∈ B1) :
      a * N ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖ :=
    hphi z (hB1sub hz)
  obtain ⟨B2, hB2sub, hB2raw, hB2horizontal⟩ :=
    context_horizontal_restriction hprime a ha f hf B1 phi hB1large
  have hB2coefficient :
      a ^ 14409429 ≤ (2 : Real) ^ (-(1882 : Real)) * a ^ 9312 *
        ((B1.card : Real) / (N : Real) ^ 2) ^ 1165 := by
    have hdensityPow : (a ^ 12359) ^ 1165 ≤
        ((B1.card : Real) / (N : Real) ^ 2) ^ 1165 :=
      pow_le_pow_left₀ (by positivity) hB1density 1165
    have hconstantMul : a ^ 1882 * a ^ 9312 ≤
        (2 : Real) ^ (-(1882 : Real)) * a ^ 9312 :=
      mul_le_mul_of_nonneg_right hconstant (pow_nonneg ha.le 9312)
    calc
      a ^ 14409429 = a ^ 1882 * a ^ 9312 * (a ^ 12359) ^ 1165 := by
        rw [show 14409429 = 1882 + 9312 + 12359 * 1165 by norm_num,
          pow_add, pow_add, pow_mul]
      _ ≤ (2 : Real) ^ (-(1882 : Real)) * a ^ 9312 *
          ((B1.card : Real) / (N : Real) ^ 2) ^ 1165 :=
        mul_le_mul hconstantMul hdensityPow (by positivity) (by positivity)
  have hbetaPower : beta ≤ a ^ 14409429 := by
    dsimp only [beta]
    exact pow_le_pow_of_le_one ha.le haOne (by norm_num)
  have hB2card : beta * (N : Real) ^ 2 ≤ B2.card :=
    (mul_le_mul_of_nonneg_right
      (hbetaPower.trans hB2coefficient) hN2.le).trans hB2raw
  have hB2large (z : Pair N) (hz : z ∈ B2) :
      a * N ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖ :=
    hB1large z (hB2sub hz)
  obtain ⟨A, hAsub, harrRaw, hmostly⟩ :=
    hN0 N hN f B2 phi hf hB2card hB2large
  have harr : a ^ ((2 : Nat) ^ 68) * (N : Real) ^ 32 ≤
      arrangementCount 8 A :=
    (mul_le_mul_of_nonneg_right
      (context_coefficient_lower a ha haHalf haOne) (by positivity)).trans harrRaw
  refine ⟨A, phi, ?_, ?_, ?_, ?_⟩
  · simpa only [a] using context_card_lower_of_arrangements a ha haOne A harr
  · constructor
    · intro x
      have hsec : (↑(verticalSection A x) : Set (ZMod N)) ⊆
          ↑(verticalSection B1 x) := by
        intro y hy
        have hyA : (x, y) ∈ A := by simpa [verticalSection] using hy
        have hyB1 := hB2sub (hAsub hyA)
        simpa [verticalSection] using hyB1
      exact IsAddFreimanHom.subset hsec (hB1vertical x) (Set.mapsTo_univ _ _)
    · intro y
      have hsec : (↑(horizontalSection A y) : Set (ZMod N)) ⊆
          ↑(horizontalSection B2 y) := by
        intro x hx
        have hxA : (x, y) ∈ A := by simpa [horizontalSection] using hx
        simpa [horizontalSection] using hAsub hxA
      exact IsAddFreimanHom.subset hsec (hB2horizontal y) (Set.mapsTo_univ _ _)
  · simpa only [MostlyRespectsEight, eta, context_eta_eq] using hmostly
  · intro z hz
    have hzlarge := hB2large z (hAsub hz)
    dsimp only [a] at hzlarge
    convert hzlarge using 1
    ring

end LeanProofs.GowersSzemeredi
