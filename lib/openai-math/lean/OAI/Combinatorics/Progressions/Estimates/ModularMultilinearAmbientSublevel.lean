/- Modified for ProveIt: use Finsupp.mapDomain_apply for injective
reindexing on Mathlib v4.32.0. Mathematical statements unchanged. -/
import Mathlib.Algebra.MvPolynomial.Equiv
import OAI.Combinatorics.Progressions.Estimates.ModularMultilinearSublevelFiber
import OAI.Combinatorics.Progressions.Estimates.ModularMultilinearSublevelNumerics
import OAI.Combinatorics.Progressions.Geometry.FiniteUniformCoordinateRefresh
import OAI.Combinatorics.Progressions.Polynomial.ModularMultilinearSublevelPolynomial

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped Classical BigOperators

variable {I J R : Type*} [CommRing R]

theorem degreeOf_polynomialTranslate_le (P : MvPolynomial I R) (v : I → R) (i : I) :
    degreeOf i (polynomialTranslate v P) ≤ degreeOf i P := by
  let w : I → ℕ := Pi.single i 1
  have hP : P ∈ weightedSupportLE w (degreeOf i P) := by
    intro a ha
    change Finsupp.weight w a ≤ degreeOf i P
    rw [Finsupp.weight_single_one_apply]
    exact monomial_le_degreeOf i ha
  have ht := weightedSupportLE_aeval w w (fun j => X j + C (v j))
    (fun j => (weightedSupportLE w (w j)).add_mem
      (weightedSupportLE_X w j) (weightedSupportLE_C w (w j) (v j))) hP
  apply degreeOf_le_iff.mpr
  intro a ha
  have hh : Finsupp.weight w a ≤ degreeOf i P := ht ha
  simpa only [w, Finsupp.weight_single_one_apply] using hh

theorem top_coeff_polynomialTranslate (P : MvPolynomial I R) (v : I → R)
    (a : I →₀ ℕ) (hP : P.totalDegree ≤ a.degree) :
    (polynomialTranslate v P).coeff a = P.coeff a := by
  have ht := polynomialTranslate_sub_mem_weightedSupportLT v (1 : I → ℕ)
    (fun _ => by simp) ((mem_weightedSupportLE_one_iff P a.degree).mpr hP)
  have hz : (polynomialTranslate v P - P).coeff a = 0 := by
    by_contra hn
    have hh : Finsupp.weight (1 : I → ℕ) a < a.degree := ht (mem_support_iff.mpr hn)
    have he : Finsupp.weight (1 : I → ℕ) a = a.degree := by
      simp [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum]
    rw [he] at hh
    exact (lt_irrefl _) hh
  simpa only [coeff_sub, sub_eq_zero] using hz

theorem degreeOf_killCompl_le (f : J → I) (hf : Function.Injective f)
    (P : MvPolynomial I R) (j : J) :
    degreeOf j (killCompl hf P) ≤ degreeOf (f j) P := by
  apply degreeOf_le_iff.mpr
  intro a ha
  have ham : a.mapDomain f ∈ P.support := by
    simpa only [mem_support_iff, coeff_killCompl] using ha
  have hh := monomial_le_degreeOf (f j) ham
  simpa only [Finsupp.mapDomain_apply hf] using hh

noncomputable def conditionPolynomial (f : J → I) (hf : Function.Injective f)
    (v : I → R) (P : MvPolynomial I R) : MvPolynomial J R :=
  killCompl hf (polynomialTranslate (fun i => if i ∈ Set.range f then 0 else v i) P)

theorem degreeOf_conditionPolynomial_le (f : J → I) (hf : Function.Injective f)
    (v : I → R) (P : MvPolynomial I R) (j : J) :
    degreeOf j (conditionPolynomial f hf v P) ≤ degreeOf (f j) P :=
  (degreeOf_killCompl_le f hf _ j).trans (degreeOf_polynomialTranslate_le P _ (f j))

theorem coeff_conditionPolynomial_top (f : J → I) (hf : Function.Injective f)
    (v : I → R) (P : MvPolynomial I R) (a : J →₀ ℕ)
    (hP : P.totalDegree ≤ a.degree) :
    (conditionPolynomial f hf v P).coeff a = P.coeff (a.mapDomain f) := by
  rw [conditionPolynomial, coeff_killCompl]
  apply top_coeff_polynomialTranslate
  simpa only [Finsupp.degree_mapDomain] using hP

theorem eval_conditionPolynomial (f : J → I) (hf : Function.Injective f)
    (v : I → R) (P : MvPolynomial I R) (y : J → R) :
    eval y (conditionPolynomial f hf v P) = eval (Function.extend f y v) P := by
  unfold conditionPolynomial
  induction P using MvPolynomial.induction_on with
  | C c => simp only [polynomialTranslate_C, killCompl_C, eval_C]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, hP, polynomialTranslate_X, map_add, killCompl_C, eval_C, eval_X]
    congr 1
    by_cases hi : i ∈ Set.range f
    · obtain ⟨j, rfl⟩ := hi
      simp only [show f j ∈ Set.range f from ⟨j, rfl⟩, ite_true, add_zero,
        hf.extend_apply]
      rw [← rename_X f j, killCompl_rename_app, eval_X]
    · simp only [hi, ite_false, Function.extend_apply' y v i hi]
      have hz : killCompl hf (X i : MvPolynomial I R) = 0 := by
        simp only [killCompl, aeval_X, hi, dite_false]
      rw [hz, map_zero, zero_add]

theorem conditionPolynomial_fullSquarefree {r : ℕ} (f : Fin r → I)
    (hf : Function.Injective f) (v : I → R) (P : MvPolynomial I R)
    (hP : P.totalDegree ≤ r) (hmulti : ∀ i, degreeOf i P ≤ 1) :
    (∀ j, degreeOf j (conditionPolynomial f hf v P) ≤ 1) ∧
      (conditionPolynomial f hf v P).coeff (fullShiftExponent r) =
        P.coeff ((fullShiftExponent r).mapDomain f) := by
  constructor
  · intro j
    exact (degreeOf_conditionPolynomial_le f hf v P j).trans (hmulti (f j))
  · apply coeff_conditionPolynomial_top
    change P.totalDegree ≤ (fullShiftExponent r).sum (fun _ e => e)
    rwa [fullShiftExponent_sum]

theorem fullShiftExponent_mapDomain [Fintype I] {r : ℕ} (f : Fin r → I)
    (hf : Function.Injective f) :
    (fullShiftExponent r).mapDomain f =
      (SquarefreeIndex.ofFinset (Finset.univ.image f)).val := by
  ext i
  rw [SquarefreeIndex.ofFinset_apply]
  by_cases hi : i ∈ Set.range f
  · obtain ⟨j, rfl⟩ := hi
    rw [Finsupp.mapDomain_apply hf, fullShiftExponent_apply]
    simp only [Finset.mem_image, Finset.mem_univ, true_and, exists_apply_eq_apply, ite_true]
  · rw [Finsupp.mapDomain_of_notMem_range _ _ hi]
    have hn : i ∉ Finset.univ.image f := by simpa only [Finset.mem_image,
      Finset.mem_univ, true_and, Set.mem_range] using hi
    simp only [hn, ite_false]

theorem expect_eval_conditionPolynomial [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Fintype R]
    (f : J → I) (hf : Function.Injective f) (P : MvPolynomial I R) (F : R → ℝ) :
    (𝔼 v : I → R, 𝔼 y : J → R, F (eval y (conditionPolynomial f hf v P))) =
      𝔼 x : I → R, F (eval x P) := by
  simp only [eval_conditionPolynomial]
  exact expect_coordinate_resampling f hf (fun x => F (eval x P))

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem modularPolynomial_zero_reduction {I : Type*} [Fintype I] [DecidableEq I]
    {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (P : MvPolynomial I (ZMod N)) :
    (𝔼 x : I → ZMod N,
      if ZMod.castHom hMN (ZMod M) (MvPolynomial.eval x P) = 0 then (1 : ℝ) else 0) =
      𝔼 y : I → ZMod M,
        if MvPolynomial.eval y (P.map (ZMod.castHom hMN (ZMod M))) = 0 then (1 : ℝ) else 0 := by
  let f : (I → ZMod N) →+ (I → ZMod M) :=
    { toFun := fun x i => ZMod.castHom hMN (ZMod M) (x i)
      map_zero' := by ext i; simp
      map_add' := by intro x y; ext i; exact map_add (ZMod.castHom hMN (ZMod M)) (x i) (y i) }
  have hf : Function.Surjective f := by
    intro y
    choose x hx using fun i => ZMod.castHom_surjective hMN (y i)
    exact ⟨x, funext hx⟩
  have h := expect_surjective_hom f hf (fun y =>
    if MvPolynomial.eval y (P.map (ZMod.castHom hMN (ZMod M))) = 0 then (1 : ℝ) else 0)
  convert h using 1
  apply Finset.expect_congr rfl
  intro x _
  rw [MvPolynomial.map_eval]
  rfl

theorem modularAffine_zero_split {X R S : Type*} [Fintype X] [Nonempty X] [Fintype R]
    [Nonempty R] [DecidableEq R] [DecidableEq S] [Zero R] [Add R] [Mul R] [Zero S]
    (g h : X → R) (reduce : R → S) {ε : ℝ} (hε : 0 ≤ ε)
    (hfiber : ∀ c d : R, reduce c ≠ 0 →
      (𝔼 t : R, if t * c + d = 0 then (1 : ℝ) else 0) ≤ ε) :
    (𝔼 x : X, 𝔼 t : R, if t * g x + h x = 0 then (1 : ℝ) else 0) ≤
      (𝔼 x : X, if reduce (g x) = 0 then (1 : ℝ) else 0) + ε := by
  calc
    _ ≤ 𝔼 x : X, ((if reduce (g x) = 0 then (1 : ℝ) else 0) + ε) := by
      apply Finset.expect_le_expect
      intro x _
      by_cases hx : reduce (g x) = 0
      · simp only [hx, ite_true]
        have hle : (𝔼 t : R, if t * g x + h x = 0 then (1 : ℝ) else 0) ≤ 1 := by
          calc
            _ ≤ 𝔼 _t : R, (1 : ℝ) := Finset.expect_le_expect (by intro t _; split_ifs <;> norm_num)
            _ = 1 := Fintype.expect_const _
        linarith
      · simpa only [hx, ite_false, zero_add] using hfiber (g x) (h x) hx
    _ ≤ _ := by
      rw [Finset.expect_add_distrib]
      rw [Fintype.expect_const]

end Erdos3

end

section

namespace Erdos3
open MvPolynomial
open scoped BigOperators Classical

private theorem multiaffine_map {I R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (P : MvPolynomial I R) (hP : ∀ i, degreeOf i P ≤ 1) :
    ∀ i, degreeOf i (P.map f) ≤ 1 := by
  intro i
  rw [degreeOf_le_iff]
  intro m hm
  exact degreeOf_le_iff.mp (hP i) m (support_map_subset f P hm)

theorem modularMultilinear_full_sublevel (r : ℕ) {p a : ℕ} [NeZero p]
    (hp : p.Prime) (ha : 0 < a)
    (P : MvPolynomial (Fin (r + 1)) (ZMod (p ^ a)))
    (hP : ∀ i, degreeOf i P ≤ 1)
    (hunit : IsUnit (P.coeff
      (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (r + 1)))).val)) :
    (𝔼 x : Fin (r + 1) → ZMod (p ^ a),
      if eval x P = 0 then (1 : ℝ) else 0) ≤
        ((r + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ r) := by
  induction r generalizing a with
  | zero =>
    let G := (finSuccEquiv (ZMod (p ^ a)) 0 P).coeff 1
    let H := (finSuccEquiv (ZMod (p ^ a)) 0 P).coeff 0
    let y : Fin 0 → ZMod (p ^ a) := fun i => Fin.elim0 i
    have hG : IsUnit (eval y G) := by
      have hcoef := fullSquarefree_finSuccEquiv_coeff P
      have hz : (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin 0))).val = 0 := by
        ext i; exact Fin.elim0 i
      rw [hz] at hcoef
      have he : eval y G = G.coeff 0 := by
        have hconst : G = C (G.coeff 0) := by
          have hh := (isEmptyRingEquiv (ZMod (p ^ a)) (Fin 0)).symm_apply_apply G
          simpa only [isEmptyRingEquiv_eq_coeff_zero,
            isEmptyRingEquiv_symm_apply] using hh.symm
        conv_lhs => rw [hconst, eval_C]
      rw [he, hcoef]
      exact hunit
    let : Fact (1 < p ^ 1) := ⟨by simpa using hp.one_lt⟩
    have hc : ZMod.castHom (pow_dvd_pow p (show 1 ≤ a by omega)) (ZMod (p ^ 1))
        (eval y G) ≠ 0 := by
      have hi := hG.map (ZMod.castHom (pow_dvd_pow p (show 1 ≤ a by omega)) (ZMod (p ^ 1)))
      exact hi.ne_zero
    have hf := zmod_prime_power_affine_zero_expect_le_rpow hp (show 1 ≤ 1 by omega)
      (show 1 ≤ a by omega) (eval y G) (eval y H) hc
    rw [expect_fin_cons]
    simp_rw [multiaffine_eval_fin_cons P (hP 0)]
    simp_rw [expect_empty_tuple]
    simp only [Nat.cast_one, zero_add, pow_zero, div_one, one_mul]
    convert hf using 1
    · congr 1; funext t; rw [mul_comm]
    · congr 1; ring
  | succ r ih =>
    let b := (a + 1) / 2
    have hb := modularSublevel_half_depth ha
    let f : ZMod (p ^ a) →+* ZMod (p ^ b) :=
      ZMod.castHom (pow_dvd_pow p hb.2.1) (ZMod (p ^ b))
    let G := (finSuccEquiv (ZMod (p ^ a)) (r + 1) P).coeff 1
    let H := (finSuccEquiv (ZMod (p ^ a)) (r + 1) P).coeff 0
    have hG : ∀ i, degreeOf i G ≤ 1 := multiaffine_finSuccEquiv_coeff P hP 1
    have hGu : IsUnit (G.coeff
        (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (r + 1)))).val) := by
      rw [fullSquarefree_finSuccEquiv_coeff]
      exact hunit
    have hGfu : IsUnit ((G.map f).coeff
        (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (r + 1)))).val) := by
      rw [coeff_map]
      exact hGu.map f
    have hsmall := ih hb.1 (G.map f) (multiaffine_map f G hG) hGfu
    have hbad : (𝔼 y : Fin (r + 1) → ZMod (p ^ a),
        if f (eval y G) = 0 then (1 : ℝ) else 0) ≤
          ((r + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(b : ℝ) / (2 : ℝ) ^ r) := by
      change (𝔼 y : Fin (r + 1) → ZMod (p ^ a),
        if ZMod.castHom (pow_dvd_pow p hb.2.1) (ZMod (p ^ b)) (eval y G) = 0
          then (1 : ℝ) else 0) ≤ _
      rw [modularPolynomial_zero_reduction (pow_dvd_pow p hb.2.1)]
      exact hsmall
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    have hfiber (c d : ZMod (p ^ a)) (hc : f c ≠ 0) :
        (𝔼 t : ZMod (p ^ a), if t * c + d = 0 then (1 : ℝ) else 0) ≤
          (p : ℝ) ^ (-(a : ℝ) / 2) := by
      have h := zmod_prime_power_affine_zero_expect_le_rpow hp hb.1 hb.2.1 c d hc
      simpa only [mul_comm c] using h.trans (modularSublevel_fiber_exponent hp1 ha)
    have hsplit := modularAffine_zero_split (fun y => eval y G) (fun y => eval y H) f
      (Real.rpow_nonneg (show (0 : ℝ) ≤ p by positivity) (-(a : ℝ) / 2)) hfiber
    rw [expect_fin_cons]
    simp_rw [multiaffine_eval_fin_cons P (hP 0)]
    rw [Finset.expect_comm]
    apply hsplit.trans
    apply (add_le_add hbad (le_refl ((p : ℝ) ^ (-(a : ℝ) / 2)))).trans
    simpa only [Nat.succ_sub_one] using
      modularSublevel_induction_bound hp1 ha (Nat.succ_pos r)

end Erdos3

end

section

namespace Erdos3
open MvPolynomial
open scoped BigOperators Classical

theorem modularMultilinear_sublevel {I : Type*} [Fintype I] [DecidableEq I]
    (r : ℕ) {p a : ℕ} [NeZero p] (hp : p.Prime) (ha : 0 < a)
    (P : MvPolynomial I (ZMod (p ^ a))) (f : Fin (r + 1) → I)
    (hf : Function.Injective f) (hdeg : P.totalDegree ≤ r + 1)
    (hP : ∀ i, degreeOf i P ≤ 1)
    (hunit : IsUnit (P.coeff ((fullShiftExponent (r + 1)).mapDomain f))) :
    (𝔼 x : I → ZMod (p ^ a), if eval x P = 0 then (1 : ℝ) else 0) ≤
        ((r + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ r) := by
  rw [← expect_eval_conditionPolynomial f hf P (fun z => if z = 0 then (1 : ℝ) else 0)]
  calc
    _ ≤ 𝔼 _v : I → ZMod (p ^ a),
        ((r + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ r) := by
      apply Finset.expect_le_expect
      intro v _
      have h := conditionPolynomial_fullSquarefree f hf v P hdeg hP
      apply modularMultilinear_full_sublevel r hp ha _ h.1
      have he : (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin (r + 1)))).val =
          fullShiftExponent (r + 1) := by
        ext i
        simp [SquarefreeIndex.ofFinset_apply, fullShiftExponent_apply]
      rw [he, h.2]
      exact hunit
    _ = _ := Fintype.expect_const _

theorem modularMultilinear_sublevel_of_pos {I : Type*} [Fintype I] [DecidableEq I]
    {r p a : ℕ} [NeZero p] (hr : 0 < r) (hp : p.Prime) (ha : 0 < a)
    (P : MvPolynomial I (ZMod (p ^ a))) (f : Fin r → I)
    (hf : Function.Injective f) (hdeg : P.totalDegree ≤ r)
    (hP : ∀ i, degreeOf i P ≤ 1)
    (hunit : IsUnit (P.coeff ((fullShiftExponent r).mapDomain f))) :
    (𝔼 x : I → ZMod (p ^ a), if eval x P = 0 then (1 : ℝ) else 0) ≤
        (r : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ (r - 1)) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  simpa only [Nat.succ_sub_one] using modularMultilinear_sublevel r hp ha P f hf hdeg hP hunit

end Erdos3

end

end OAI
