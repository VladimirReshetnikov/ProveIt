import GowersSzemeredi.Proofs03Basic

/-!
# Lower bounds for additive cubes

This module connects the paper's concrete cube counter with iterated
differences of an indicator function and proves Gowers's Lemma 3.7 by finite
Cauchy--Schwarz.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-- The unsigned cube product.  For indicator functions conjugation has no
effect, so this is the corresponding iterated difference. -/
private def cubeProduct {N d : Nat} (f : ZMod N → Complex)
    (a : Point N d) (s : ZMod N) : Complex :=
  ∏ e : Fin d → Bool, f (s - ∑ i, if e i then a i else 0)

private lemma cubeProduct_cons {N n : Nat} (f : ZMod N → Complex)
    (r : ZMod N) (a : Point N n) (s : ZMod N) :
    cubeProduct f (Fin.cons r a) s =
      cubeProduct f a s * cubeProduct f a (s - r) := by
  let E := Fin.consEquiv (fun _ : Fin (n + 1) ↦ Bool)
  unfold cubeProduct
  calc
    ∏ e : Fin (n + 1) → Bool,
        f (s - ∑ i, if e i then Fin.cons r a i else 0) =
        ∏ p : Bool × (Fin n → Bool),
          f (s - ∑ i, if E p i then Fin.cons r a i else 0) := by
      exact (E.prod_comp fun e ↦
        f (s - ∑ i, if e i then Fin.cons r a i else 0)).symm
    _ = (∏ e : Fin n → Bool,
          f (s - (r + ∑ i, if e i then a i else 0))) *
        ∏ e : Fin n → Bool,
          f (s - ∑ i, if e i then a i else 0) := by
      rw [Fintype.prod_prod_type, Fintype.prod_bool]
      simp [E, Fin.sum_univ_succ]
    _ = (∏ e : Fin n → Bool,
          f (s - ∑ i, if e i then a i else 0)) *
        ∏ e : Fin n → Bool,
          f (s - r - ∑ i, if e i then a i else 0) := by
      rw [mul_comm]
      simp only [sub_add_eq_sub_sub]
    _ = (∏ e : Fin n → Bool,
          f (s - ∑ i, if e i then a i else 0)) *
        ∏ e : Fin n → Bool,
          f ((s - r) - ∑ i, if e i then a i else 0) := by rfl

private lemma cubeDifference_indicator_eq_cubeProduct {N d : Nat}
    (A : Finset (ZMod N)) (a : Point N d) (s : ZMod N) :
    cubeDifference (indicator A) a s = cubeProduct (indicator A) a s := by
  induction d generalizing s with
  | zero =>
      simp [cubeDifference, cubeProduct, iteratedDifference]
  | succ n ih =>
      let r := a 0
      let b : Point N n := Fin.tail a
      have ha : a = Fin.cons r b := by
        funext i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · rfl
        · rfl
      rw [ha, cubeDifference_cons, cubeProduct_cons]
      simp only [difference, ih]
      have hreal (x : ZMod N) : star (cubeProduct (indicator A) b x) =
          cubeProduct (indicator A) b x := by
        unfold cubeProduct indicator
        simp
      rw [hreal]

private noncomputable def cubeMembershipIndicator {N d : Nat}
    (A : Finset (ZMod N)) (a : Point N d) (s : ZMod N) : Complex := by
  classical
  exact if ({ base := s, side := a } : AdditiveCube N d).IsIn A then 1 else 0

private lemma cubeProduct_indicator_neg_eq_vertexIndicator {N d : Nat}
    (A : Finset (ZMod N)) (a : Point N d) (s : ZMod N) :
    cubeProduct (indicator A) (fun i ↦ -a i) s =
      cubeMembershipIndicator A a s := by
  classical
  have harg (e : Fin d → Bool) :
      s - ∑ i, (if e i then -(a i) else 0) =
        ({ base := s, side := a } : AdditiveCube N d).vertex e := by
    unfold AdditiveCube.vertex
    have hsum : (∑ i, if e i then -(a i) else 0) =
        -∑ i, if e i then a i else 0 := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : e i <;> simp [hi]
    rw [hsum]
    abel
  unfold cubeProduct indicator cubeMembershipIndicator AdditiveCube.IsIn
  simp_rw [harg]
  rw [Fintype.prod_boole]
  by_cases h : ∀ e : Fin d → Bool,
      ({ base := s, side := a } : AdditiveCube N d).vertex e ∈ A <;>
    simp [h]

lemma sum_cubeDifference_indicator_eq_cubeCount {N d : Nat} [NeZero N]
    (A : Finset (ZMod N)) :
    ∑ a : Point N d, ∑ s : ZMod N, cubeDifference (indicator A) a s =
      (cubeCount (d := d) A : Complex) := by
  classical
  let F : Point N d → Complex := fun a ↦
    ∑ s : ZMod N, cubeDifference (indicator A) a s
  have hneg : (∑ a : Point N d, F (-a)) = ∑ a : Point N d, F a :=
    Fintype.sum_equiv (Equiv.neg (Point N d)) _ _ (fun _ ↦ rfl)
  calc
    ∑ a : Point N d, ∑ s : ZMod N, cubeDifference (indicator A) a s =
        ∑ a : Point N d, ∑ s : ZMod N,
          cubeDifference (indicator A) (-a) s := by
      simpa only [F] using hneg.symm
    _ = ∑ a : Point N d, ∑ s : ZMod N, cubeMembershipIndicator A a s := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro s _
      rw [cubeDifference_indicator_eq_cubeProduct]
      change cubeProduct (indicator A) (fun i ↦ -a i) s =
        cubeMembershipIndicator A a s
      exact cubeProduct_indicator_neg_eq_vertexIndicator A a s
    _ = ∑ p : ZMod N × Point N d,
          cubeMembershipIndicator A p.2 p.1 := by
      rw [Fintype.sum_prod_type, sum_comm]
    _ = (cubeCount (d := d) A : Complex) := by
      simp [cubeMembershipIndicator, cubeCount, countWhere]

private lemma cubeCount_succ_eq_sum_norm_sq {N d : Nat} [NeZero N]
    (A : Finset (ZMod N)) :
    (cubeCount (d := d + 1) A : Real) =
      ∑ a : Point N d,
        ‖∑ s : ZMod N, cubeDifference (indicator A) a s‖ ^ 2 := by
  have h := congrArg Complex.re
    (sum_cube_succ_eq_sum_norm_sq (n := d) (indicator A))
  rw [sum_cubeDifference_indicator_eq_cubeCount] at h
  simpa only [Complex.natCast_re, Complex.ofReal_re] using h

private lemma cubeCount_zero {N : Nat} [NeZero N] (A : Finset (ZMod N)) :
    cubeCount (d := 0) A = A.card := by
  have h := congrArg Complex.re
    (sum_cubeDifference_indicator_eq_cubeCount (d := 0) A)
  simpa [cubeDifference, iteratedDifference] using h.symm

private lemma cubeCount_sq_le_card_mul_succ {N d : Nat} [NeZero N]
    (A : Finset (ZMod N)) :
    (cubeCount (d := d) A : Real) ^ 2 ≤
      (N : Real) ^ d * (cubeCount (d := d + 1) A : Real) := by
  let X : Point N d → Complex := fun a ↦
    ∑ s : ZMod N, cubeDifference (indicator A) a s
  have htotal : ∑ a : Point N d, X a =
      (cubeCount (d := d) A : Complex) :=
    sum_cubeDifference_indicator_eq_cubeCount A
  have hnorm : ‖∑ a : Point N d, X a‖ = (cubeCount (d := d) A : Real) := by
    rw [htotal]
    simp
  have htriangle : ‖∑ a : Point N d, X a‖ ≤
      ∑ a : Point N d, ‖X a‖ := by
    simpa using norm_sum_le (Finset.univ : Finset (Point N d)) X
  have hcauchy : (∑ a : Point N d, ‖X a‖) ^ 2 ≤
      (Fintype.card (Point N d) : Real) * ∑ a : Point N d, ‖X a‖ ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Point N d))) (f := fun a ↦ ‖X a‖))
  calc
    (cubeCount (d := d) A : Real) ^ 2 =
        ‖∑ a : Point N d, X a‖ ^ 2 := by rw [hnorm]
    _ ≤ (∑ a : Point N d, ‖X a‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htriangle 2
    _ ≤ (Fintype.card (Point N d) : Real) *
        ∑ a : Point N d, ‖X a‖ ^ 2 := hcauchy
    _ = (N : Real) ^ d * (cubeCount (d := d + 1) A : Real) := by
      rw [← cubeCount_succ_eq_sum_norm_sq]
      simp [Point, ZMod.card]

/-- **Gowers, Lemma 3.7.** Every set has at least the random-density number
of additive cubes in every dimension. -/
theorem lemma_3_7_holds : lemma_3_7 := by
  intro N d _ A delta hcard
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hdelta : 0 ≤ delta := by
    have hdeltaN : 0 ≤ delta * (N : Real) := by
      rw [← hcard]
      positivity
    nlinarith
  induction d with
  | zero =>
      rw [cubeCount_zero]
      simpa using hcard.symm.le
  | succ d ih =>
      have htarget0 :
          0 ≤ delta ^ ((2 : Nat) ^ d) * (N : Real) ^ (d + 1) :=
        mul_nonneg (pow_nonneg hdelta _) (pow_nonneg hN.le _)
      have ihsq :
          (delta ^ ((2 : Nat) ^ d) * (N : Real) ^ (d + 1)) ^ 2 ≤
            (cubeCount (d := d) A : Real) ^ 2 :=
        pow_le_pow_left₀ htarget0 ih 2
      have hscale :
          (delta ^ ((2 : Nat) ^ (d + 1)) * (N : Real) ^ (d + 2)) *
              (N : Real) ^ d =
            (delta ^ ((2 : Nat) ^ d) * (N : Real) ^ (d + 1)) ^ 2 := by
        have hnscale : (N : Real) ^ (d + 2) * (N : Real) ^ d =
            ((N : Real) ^ (d + 1)) ^ 2 := by
          rw [← pow_add, ← pow_mul]
          congr 1
          omega
        rw [show (2 : Nat) ^ (d + 1) = (2 : Nat) ^ d * 2 by
          rw [pow_succ], pow_mul, mul_pow, mul_assoc, hnscale]
      apply le_of_mul_le_mul_right _ (pow_pos hN d)
      calc
        (delta ^ ((2 : Nat) ^ (d + 1)) * (N : Real) ^ (d + 2)) *
            (N : Real) ^ d =
          (delta ^ ((2 : Nat) ^ d) * (N : Real) ^ (d + 1)) ^ 2 := hscale
        _ ≤ (cubeCount (d := d) A : Real) ^ 2 := ihsq
        _ ≤ (N : Real) ^ d * (cubeCount (d := d + 1) A : Real) :=
          cubeCount_sq_le_card_mul_succ A
        _ = (cubeCount (d := d + 1) A : Real) * (N : Real) ^ d := by ring

end LeanProofs.GowersSzemeredi
