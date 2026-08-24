import GowersSzemeredi.Proofs03Equivalences
import GowersSzemeredi.Proofs12
import GowersSzemeredi.Proofs14Fourier

/-!
# Product-property criteria from Section 14

This module proves Lemmas 14.2 and 14.3.  The coordinate being varied is
handled uniformly by deleting and reinserting an arbitrary `Fin` coordinate.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private lemma prop14_iteratedDifference_perm {N : Nat}
    (f : ZMod N → Complex) {a b : List (ZMod N)} (h : List.Perm a b) :
    iteratedDifference f a = iteratedDifference f b := by
  induction h with
  | nil => rfl
  | cons x h ih =>
      simp only [iteratedDifference]
      rw [ih]
  | swap x y l =>
      simp only [iteratedDifference]
      exact difference_comm (iteratedDifference f l) x y
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private lemma prop14_ofFn_insertNth_perm {n : Nat} {X : Type*}
    (j : Fin (n + 1)) (x : X) (y : Fin n → X) :
    List.Perm (List.ofFn (j.insertNth x y)) (x :: List.ofFn y) := by
  induction n with
  | zero =>
      have hj : j = 0 := Fin.eq_zero j
      subst j
      simp [Fin.insertNth_zero']
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [Fin.insertNth_zero']
      · have hy : y = Fin.cons (y 0) (Fin.tail y) := by
          funext i
          refine Fin.cases ?_ (fun i => ?_) i
          · simp
          · rfl
        rw [hy, Fin.insertNth_succ_cons, List.ofFn_cons, List.ofFn_cons]
        exact (List.Perm.cons _ (ih j (Fin.tail y))).trans
          (List.Perm.swap _ _ _)

private def prop142Component {N n : Nat} (f : ZMod N → Complex)
    (y : Point N (n + 1)) (j : Fin (n + 1)) : ZMod N → Complex :=
  cubeDifference f (j.removeNth y)

private lemma prop142_component_difference {N n : Nat}
    (f : ZMod N → Complex) (y : Point N (n + 1))
    (j : Fin (n + 1)) (x : ZMod N) :
    difference (prop142Component f y j) x =
      cubeDifference f (replaceCoordinate y j x) := by
  rw [show prop142Component f y j = cubeDifference f (j.removeNth y) by rfl,
    ← cubeDifference_cons]
  have hpoint : replaceCoordinate y j x = j.insertNth x (j.removeNth y) := by
    rw [Fin.insertNth_removeNth]
    rfl
  rw [hpoint]
  unfold cubeDifference
  apply prop14_iteratedDifference_perm
  rw [List.ofFn_cons]
  exact (prop14_ofFn_insertNth_perm j x (j.removeNth y)).symm

private lemma prop142_component_disc {N n : Nat} (f : ZMod N → Complex)
    (hf : DiscValued f) (y : Point N (n + 1)) (j : Fin (n + 1)) :
    DiscValued (prop142Component f y j) :=
  cubeDifference_discValued hf (j.removeNth y)

private def prop14RestrictedWeight {N : Nat} [NeZero N]
    (E : Finset (ZMod N)) (theta : ZMod N → Real) : ZMod N → Real :=
  fun x => if x ∈ E then theta x else 0

private def prop14QuadEquiv (X : Type*) : (Fin 4 → X) ≃ (Fin 4 → X) where
  toFun q := ![q 0, q 3, q 2, q 1]
  invFun q := ![q 0, q 3, q 2, q 1]
  left_inv q := by funext i; fin_cases i <;> rfl
  right_inv q := by funext i; fin_cases i <;> rfl

private lemma prop14_prod_fin_four (a : Fin 4 → Real) :
    (∏ i, a i) = a 0 * a 1 * a 2 * a 3 := by
  rw [Fin.prod_univ_four]

private lemma prop14_restricted_weight_eq_energy {N p : Nat} [NeZero N]
    (E : Finset (ZMod N)) (theta : ZMod N → Real)
    (sigma : Fin p → ZMod N → ZMod N) :
    simultaneouslyAdditiveWeight (prop14RestrictedWeight E theta) sigma =
      weightedSimultaneousAdditiveEnergy E theta sigma := by
  classical
  unfold simultaneouslyAdditiveWeight weightedSimultaneousAdditiveEnergy
  apply Fintype.sum_equiv (prop14QuadEquiv (ZMod N))
  intro q
  simp only [prop14QuadEquiv, IsSimultaneouslyAdditive,
    IsAdditiveQuadruple]
  have hadd :
      q 0 - q 1 = q 2 - q 3 ↔ q 0 + q 3 = q 2 + q 1 :=
    sub_eq_sub_iff_add_eq_add
  have hsigma :
      (∀ i, sigma i (q 0) - sigma i (q 1) =
          sigma i (q 2) - sigma i (q 3)) ↔
        ∀ i, sigma i (q 0) + sigma i (q 3) =
          sigma i (q 2) + sigma i (q 1) := by
    constructor <;> intro h i
    · exact sub_eq_sub_iff_add_eq_add.mp (h i)
    · exact sub_eq_sub_iff_add_eq_add.mpr (h i)
  have hmem :
      (∀ t, ![q 0, q 3, q 2, q 1] t ∈ E) ↔
        q 0 ∈ E ∧ q 1 ∈ E ∧ q 2 ∈ E ∧ q 3 ∈ E := by
    constructor
    · intro h
      exact ⟨h 0, h 3, h 2, h 1⟩
    · rintro ⟨h0, h1, h2, h3⟩ t
      fin_cases t <;> assumption
  by_cases h0 : q 0 ∈ E <;> by_cases h1 : q 1 ∈ E <;>
    by_cases h2 : q 2 ∈ E <;> by_cases h3 : q 3 ∈ E <;>
    simp [prop14RestrictedWeight, h0, h1, h2, h3, hadd, hsigma, hmem,
      prop14_prod_fin_four]
  ring_nf

/-- Lemma 14.2, uniformly for every coordinate direction. -/
theorem lemma_14_2_holds : lemma_14_2 := by
  intro N k _ gamma f B phi hgamma hf hlarge p j y E theta htheta hmem
  cases k with
  | zero => exact Fin.elim0 j
  | succ n =>
      let lambda := prop14RestrictedWeight E theta
      let f' : Fin p → ZMod N → Complex :=
        fun i => prop142Component f (y i) j
      let sigma : Fin p → ZMod N → ZMod N :=
        fun i => coordinateRestriction phi (y i) j
      let T : Real := ∑ x ∈ E, theta x
      have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
      have hTnonneg : 0 ≤ T := by
        dsimp only [T]
        exact Finset.sum_nonneg fun _ _ => htheta _
      change gamma ^ (8 * p) * (N : Real)⁻¹ * T ^ 4 ≤
        weightedSimultaneousAdditiveEnergy E theta sigma
      by_cases hTzero : T = 0
      · rw [hTzero]
        simp only [pow_succ, pow_zero, mul_zero]
        unfold weightedSimultaneousAdditiveEnergy
        apply Finset.sum_nonneg
        intro q _
        split_ifs
        · exact Finset.prod_nonneg fun t _ => htheta (q t)
        · exact le_rfl
      · have hT : 0 < T := lt_of_le_of_ne hTnonneg (Ne.symm hTzero)
        let alpha : Real := gamma ^ (2 * p) * (N : Real)⁻¹ * T
        have halpha : 0 < alpha := by
          dsimp only [alpha]
          positivity
        have hlambda : ∀ x, 0 ≤ lambda x := by
          intro x
          simp only [lambda, prop14RestrictedWeight]
          split_ifs
          · exact htheta x
          · exact le_rfl
        have hf' : ∀ i, DiscValued (f' i) := by
          intro i
          exact prop142_component_disc f hf (y i) j
        have hcoeff (i : Fin p) (x : ZMod N) (hx : x ∈ E) :
            gamma * (N : Real) ≤
              ‖fourier (difference (f' i) x) (sigma i x)‖ := by
          rw [show difference (f' i) x =
              cubeDifference f (replaceCoordinate (y i) j x) by
            exact prop142_component_difference f (y i) j x]
          exact hlarge _ (hmem i x hx)
        have hprod (x : ZMod N) (hx : x ∈ E) :
            (gamma * (N : Real)) ^ (2 * p) ≤
              ∏ i : Fin p, ‖fourier (difference (f' i) x) (sigma i x)‖ ^ 2 := by
          have hi (i : Fin p) :
              (gamma * (N : Real)) ^ 2 ≤
                ‖fourier (difference (f' i) x) (sigma i x)‖ ^ 2 :=
            (sq_le_sq₀ (mul_nonneg hgamma.le hN.le) (norm_nonneg _)).2
              (hcoeff i x hx)
          calc
            (gamma * (N : Real)) ^ (2 * p) =
                ∏ _i : Fin p, (gamma * (N : Real)) ^ 2 := by
                  simp only [Finset.prod_const, Finset.card_univ,
                    Fintype.card_fin]
                  rw [← pow_mul]
            _ ≤ _ := Finset.prod_le_prod
              (fun _ _ => pow_nonneg (mul_nonneg hgamma.le hN.le) 2)
              (fun i _ => hi i)
        have hinput :
            alpha * (N : Real) ^ (2 * p + 1) ≤
              ∑ x : ZMod N, lambda x *
                ∏ i : Fin p,
                  ‖fourier (difference (f' i) x) (sigma i x)‖ ^ 2 := by
          calc
            alpha * (N : Real) ^ (2 * p + 1) =
                (∑ x : ZMod N, lambda x) *
                  (gamma * (N : Real)) ^ (2 * p) := by
                    have hlambda_sum : (∑ x : ZMod N, lambda x) = T := by
                      simp [lambda, prop14RestrictedWeight, T]
                    rw [hlambda_sum]
                    dsimp only [alpha]
                    field_simp
                    ring
            _ = ∑ x : ZMod N,
                lambda x * (gamma * (N : Real)) ^ (2 * p) := by
                  rw [Finset.sum_mul]
            _ ≤ ∑ x : ZMod N, lambda x *
                ∏ i : Fin p,
                  ‖fourier (difference (f' i) x) (sigma i x)‖ ^ 2 := by
                    apply Finset.sum_le_sum
                    intro x _
                    by_cases hx : x ∈ E
                    · exact mul_le_mul_of_nonneg_left (hprod x hx) (hlambda x)
                    · simp [lambda, prop14RestrictedWeight, hx]
        have hresult := proposition_12_1_holds N p lambda f' sigma alpha
          halpha hlambda hf' hinput
        rw [prop14_restricted_weight_eq_energy E theta sigma] at hresult
        calc
          gamma ^ (8 * p) * (N : Real)⁻¹ * T ^ 4 =
              alpha ^ 4 * (N : Real) ^ 3 := by
                dsimp only [alpha]
                field_simp
                rw [← pow_mul]
                ring
          _ ≤ weightedSimultaneousAdditiveEnergy E theta sigma := hresult

private lemma prop14_countWhere_eq_sum_ite {X : Type*} [Fintype X]
    (P : X → Prop) :
    countWhere P = ∑ x : X,
      @ite Nat (P x) (Classical.propDecidable (P x)) 1 0 := by
  classical
  unfold countWhere
  simpa using
    (Finset.sum_boole (R := Nat) P (Finset.univ : Finset X)).symm

private lemma prop143_boolWeight_insertNth {n : Nat}
    (j : Fin (n + 1)) (b : Bool) (e : Fin n → Bool) :
    boolWeight (j.insertNth b e) = (if b then 1 else 0) + boolWeight e := by
  classical
  unfold boolWeight
  rw [prop14_countWhere_eq_sum_ite, prop14_countWhere_eq_sum_ite]
  let ind : Bool → Nat := fun c => if c then 1 else 0
  have hind (c : Bool) :
      @ite Nat (c = true) (Classical.propDecidable (c = true)) 1 0 = ind c := by
    cases c <;> simp [ind]
  have hfun :
      (fun i : Fin (n + 1) =>
        ind ((j.insertNth b e : Fin (n + 1) → Bool) i)) =
        j.insertNth (ind b) (fun i : Fin n => ind (e i)) := by
    rw [Fin.eq_insertNth_iff]
    constructor
    · simp
    · funext i
      simp [Fin.removeNth_apply]
  calc
    (∑ i : Fin (n + 1),
        @ite Nat ((j.insertNth b e : Fin (n + 1) → Bool) i = true)
          (Classical.propDecidable _) 1 0) =
        ∑ i : Fin (n + 1),
          ind ((j.insertNth b e : Fin (n + 1) → Bool) i) := by
          apply Finset.sum_congr rfl
          intro i _
          exact hind _
    _ =
        ∑ i : Fin (n + 1),
          (j.insertNth (ind b) (fun i : Fin n => ind (e i))) i := by
              apply Finset.sum_congr rfl
              intro i _
              exact congrFun hfun i
    _ = ind b + ∑ i : Fin n, ind (e i) := Fin.sum_insertNth j _ _
    _ = (if b then 1 else 0) + ∑ i : Fin n, ind (e i) := by
          congr 1
    _ = (if b then 1 else 0) +
        ∑ i : Fin n,
          @ite Nat (e i = true) (Classical.propDecidable _) 1 0 := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          exact (hind _).symm

private def prop143Component {N n : Nat}
    (f : Point N (n + 2) → Complex) (z : Point N (n + 1))
    (j : Fin (n + 1)) (u : Point N n) : Pair N → Complex :=
  fun v => ∏ e : Fin n → Bool,
    let w := f (appendCoordinate
      (j.insertNth v.1
        (fun t => u t + if e t then (j.removeNth z) t else 0)) v.2)
    if Even (boolWeight e + n) then w else star w

private lemma prop143_component_disc {N n : Nat}
    (f : Point N (n + 2) → Complex) (hf : DiscValued f)
    (z : Point N (n + 1)) (j : Fin (n + 1)) (u : Point N n) :
    DiscValued (prop143Component f z j u) := by
  intro v
  rw [prop143Component, norm_prod]
  apply Finset.prod_le_one
  · intro e _
    positivity
  · intro e _
    dsimp only
    split_ifs
    · exact hf _
    · simpa only [norm_star] using hf _

private lemma prop143_vertex_insertNth {N n : Nat}
    (z : Point N (n + 1)) (j : Fin (n + 1))
    (u : Point N n) (a h : ZMod N) (b : Bool) (e : Fin n → Bool) :
    (fun i => (j.insertNth a u : Point N (n + 1)) i +
      if (j.insertNth b e : Fin (n + 1) → Bool) i then
        (replaceCoordinate z j h) i else 0) =
      j.insertNth (a + if b then h else 0)
        (fun t => u t + if e t then (j.removeNth z) t else 0) := by
  rw [Fin.eq_insertNth_iff]
  constructor
  · simp [replaceCoordinate]
  · funext t
    simp [Fin.removeNth_apply, replaceCoordinate]

private lemma prop143_even_false {n : Nat} (j : Fin (n + 1))
    (e : Fin n → Bool) :
    Even (boolWeight (j.insertNth false e) + (n + 1)) ↔
      ¬ Even (boolWeight e + n) := by
  rw [prop143_boolWeight_insertNth]
  simp only [Bool.false_eq_true, if_false, zero_add]
  rw [show boolWeight e + (n + 1) = (boolWeight e + n) + 1 by omega,
    Nat.even_add_one]

private lemma prop143_even_true {n : Nat} (j : Fin (n + 1))
    (e : Fin n → Bool) :
    Even (boolWeight (j.insertNth true e) + (n + 1)) ↔
      Even (boolWeight e + n) := by
  rw [prop143_boolWeight_insertNth]
  simp only [if_true]
  rw [show 1 + boolWeight e + (n + 1) = (boolWeight e + n) + 2 by omega]
  rw [show boolWeight e + n + 2 = (boolWeight e + n + 1) + 1 by omega,
    Nat.even_add_one, Nat.even_add_one, not_not]

private lemma prop143_cube_product_eq {N n : Nat} [NeZero N]
    (f : Point N (n + 2) → Complex) (z : Point N (n + 1))
    (j : Fin (n + 1)) (u : Point N n) (a h b : ZMod N) :
    (∏ e : Fin (n + 1) → Bool,
      let w := f (appendCoordinate
        (fun i => (j.insertNth a u : Point N (n + 1)) i +
          if e i then (replaceCoordinate z j h) i else 0) b)
      if Even (boolWeight e + (n + 1)) then w else star w) =
      prop143Component f z j u (a + h, b) *
        star (prop143Component f z j u (a, b)) := by
  let F : (Fin (n + 1) → Bool) → Complex := fun e =>
    let w := f (appendCoordinate
      (fun i => (j.insertNth a u : Point N (n + 1)) i +
        if e i then (replaceCoordinate z j h) i else 0) b)
    if Even (boolWeight e + (n + 1)) then w else star w
  calc
    (∏ e : Fin (n + 1) → Bool,
      let w := f (appendCoordinate
        (fun i => (j.insertNth a u : Point N (n + 1)) i +
          if e i then (replaceCoordinate z j h) i else 0) b)
      if Even (boolWeight e + (n + 1)) then w else star w) =
        ∏ be : Bool × (Fin n → Bool), F (j.insertNth be.1 be.2) := by
          exact Fintype.prod_equiv
            (Fin.insertNthEquiv (fun _ : Fin (n + 1) => Bool) j).symm
            F (fun be => F (j.insertNth be.1 be.2)) (fun e =>
              congrArg F
                ((Fin.insertNthEquiv (fun _ : Fin (n + 1) => Bool) j).apply_symm_apply e).symm)
    _ = (∏ e : Fin n → Bool, F (j.insertNth true e)) *
        ∏ e : Fin n → Bool, F (j.insertNth false e) := by
          rw [Fintype.prod_prod_type, Fintype.prod_bool]
    _ = prop143Component f z j u (a + h, b) *
        star (prop143Component f z j u (a, b)) := by
      congr 1
      · apply Finset.prod_congr rfl
        intro e _
        simp only [F]
        rw [show (fun i => (j.insertNth a u : Point N (n + 1)) i +
            if (j.insertNth true e : Fin (n + 1) → Bool) i then
              (replaceCoordinate z j h) i else 0) =
            j.insertNth (a + h)
              (fun t => u t + if e t then (j.removeNth z) t else 0) by
          simpa using prop143_vertex_insertNth z j u a h true e]
        simp only [prop143_even_true]
      · rw [prop143Component, star_prod]
        apply Finset.prod_congr rfl
        intro e _
        simp only [F]
        rw [show (fun i => (j.insertNth a u : Point N (n + 1)) i +
            if (j.insertNth false e : Fin (n + 1) → Bool) i then
              (replaceCoordinate z j h) i else 0) =
            j.insertNth a
              (fun t => u t + if e t then (j.removeNth z) t else 0) by
          simpa using prop143_vertex_insertNth z j u a h false e]
        simp only [prop143_even_false]
        by_cases he : Even (boolWeight e + n) <;> simp [he]

private lemma prop143_correlation_decomposition {N n : Nat} [NeZero N]
    (f : Point N (n + 2) → Complex) (z : Point N (n + 1))
    (j : Fin (n + 1)) (h b : ZMod N) :
    higherCubeCorrelation f (replaceCoordinate z j h) b =
      ∑ u : Point N n, firstCoordinateCorrelation
        (prop143Component f z j u) h b := by
  let F : Point N (n + 1) → Complex := fun x =>
    ∏ e : Fin (n + 1) → Bool,
      let w := f (appendCoordinate
        (fun i => x i + if e i then (replaceCoordinate z j h) i else 0) b)
      if Even (boolWeight e + (n + 1)) then w else star w
  calc
    higherCubeCorrelation f (replaceCoordinate z j h) b =
        ∑ x : Point N (n + 1), F x := by rfl
    _ = ∑ au : ZMod N × Point N n, F (j.insertNth au.1 au.2) := by
          exact Fintype.sum_equiv
            (Fin.insertNthEquiv (fun _ : Fin (n + 1) => ZMod N) j).symm
            F (fun au => F (j.insertNth au.1 au.2)) (fun x =>
              congrArg F
                ((Fin.insertNthEquiv (fun _ : Fin (n + 1) => ZMod N) j).apply_symm_apply x).symm)
    _ = ∑ u : Point N n, ∑ a : ZMod N,
        F (j.insertNth a u) := by
          rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = ∑ u : Point N n, ∑ a : ZMod N,
        prop143Component f z j u (a + h, b) *
          star (prop143Component f z j u (a, b)) := by
            apply Finset.sum_congr rfl
            intro u _
            apply Finset.sum_congr rfl
            intro a _
            exact prop143_cube_product_eq f z j u a h b
    _ = _ := by rfl

private lemma prop143_fourier_decomposition {N n : Nat} [NeZero N]
    (f : Point N (n + 2) → Complex) (z : Point N (n + 1))
    (j : Fin (n + 1)) (h r : ZMod N) :
    fourier (higherCubeCorrelation f (replaceCoordinate z j h)) r =
      ∑ u : Point N n,
        fourier (firstCoordinateCorrelation (prop143Component f z j u) h) r := by
  simp only [fourier, ZMod.dft_apply, smul_eq_mul]
  simp_rw [prop143_correlation_decomposition f z j h]
  simp_rw [mul_sum]
  rw [Finset.sum_comm]

private lemma prop143_fourier_sq_le {N n : Nat} [NeZero N]
    (f : Point N (n + 2) → Complex) (z : Point N (n + 1))
    (j : Fin (n + 1)) (h r : ZMod N) :
    ‖fourier (higherCubeCorrelation f (replaceCoordinate z j h)) r‖ ^ 2 ≤
      (N : Real) ^ n * ∑ u : Point N n,
        ‖fourier (firstCoordinateCorrelation (prop143Component f z j u) h) r‖ ^ 2 := by
  have hcard : Fintype.card (Point N n) = N ^ n := by simp [Point]
  have htriangle :
      ‖fourier (higherCubeCorrelation f (replaceCoordinate z j h)) r‖ ≤
        ∑ u : Point N n,
          ‖fourier (firstCoordinateCorrelation (prop143Component f z j u) h) r‖ := by
    rw [prop143_fourier_decomposition]
    exact norm_sum_le _ _
  calc
    ‖fourier (higherCubeCorrelation f (replaceCoordinate z j h)) r‖ ^ 2 ≤
        (∑ u : Point N n,
          ‖fourier (firstCoordinateCorrelation
            (prop143Component f z j u) h) r‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)).2
        htriangle
    _ ≤ (N : Real) ^ n * ∑ u : Point N n,
        ‖fourier (firstCoordinateCorrelation (prop143Component f z j u) h) r‖ ^ 2 := by
      simpa only [Finset.card_univ, hcard, Nat.cast_pow] using
        (sq_sum_le_card_mul_sum_sq
          (s := (Finset.univ : Finset (Point N n)))
          (f := fun u =>
            ‖fourier (firstCoordinateCorrelation
              (prop143Component f z j u) h) r‖))

private lemma prop14_univ_restricted_energy_eq {N p : Nat} [NeZero N]
    (E : Finset (ZMod N)) (theta : ZMod N → Real)
    (sigma : Fin p → ZMod N → ZMod N) :
    weightedSimultaneousAdditiveEnergy Finset.univ
        (prop14RestrictedWeight E theta) sigma =
      weightedSimultaneousAdditiveEnergy E theta sigma := by
  calc
    weightedSimultaneousAdditiveEnergy Finset.univ
        (prop14RestrictedWeight E theta) sigma =
        simultaneouslyAdditiveWeight
          (prop14RestrictedWeight Finset.univ
            (prop14RestrictedWeight E theta)) sigma :=
      (prop14_restricted_weight_eq_energy Finset.univ
        (prop14RestrictedWeight E theta) sigma).symm
    _ = simultaneouslyAdditiveWeight (prop14RestrictedWeight E theta) sigma := by
      apply congrArg (fun w => simultaneouslyAdditiveWeight w sigma)
      funext x
      simp [prop14RestrictedWeight]
    _ = weightedSimultaneousAdditiveEnergy E theta sigma :=
      prop14_restricted_weight_eq_energy E theta sigma

/-- Lemma 14.3.  The proof averages over the individual lower-dimensional
cube-product components, avoiding cross terms in the sum suggested in the
paper's informal proof. -/
theorem lemma_14_3_holds : lemma_14_3 := by
  intro N k _ gamma f B phi hgamma hf hlarge p j y E theta htheta hmem
  cases k with
  | zero => exact Fin.elim0 j
  | succ n =>
      let U := Point N n
      let V := Fin p → U
      let lambda := prop14RestrictedWeight E theta
      let sigma : Fin p → ZMod N → ZMod N :=
        fun i => coordinateRestriction phi (y i) j
      let T : Real := ∑ x ∈ E, theta x
      let C : V → Fin p → Pair N → Complex := fun v i =>
        prop143Component f (y i) j (v i)
      let S : V → Real := fun v =>
        ∑ x : ZMod N, lambda x * ∏ i : Fin p,
          ‖fourier (firstCoordinateCorrelation (C v i) x) (sigma i x)‖ ^ 2
      have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
      have hNn : (0 : Real) < (N : Real) ^ n := by positivity
      have hTnonneg : 0 ≤ T := by
        dsimp only [T]
        exact Finset.sum_nonneg fun _ _ => htheta _
      change gamma ^ (8 * p) * (N : Real)⁻¹ * T ^ 4 ≤
        weightedSimultaneousAdditiveEnergy E theta sigma
      by_cases hTzero : T = 0
      · rw [hTzero]
        simp only [pow_succ, pow_zero, mul_zero]
        unfold weightedSimultaneousAdditiveEnergy
        apply Finset.sum_nonneg
        intro q _
        split_ifs
        · exact Finset.prod_nonneg fun t _ => htheta (q t)
        · exact le_rfl
      · have hT : 0 < T := lt_of_le_of_ne hTnonneg (Ne.symm hTzero)
        have hcomponentSum (i : Fin p) (x : ZMod N) (hx : x ∈ E) :
            gamma ^ 2 * (N : Real) ^ (n + 4) ≤
              ∑ u : U,
                ‖fourier (firstCoordinateCorrelation
                  (prop143Component f (y i) j u) x) (sigma i x)‖ ^ 2 := by
          have hnorm : gamma * (N : Real) ^ (n + 2) ≤
              ‖fourier (higherCubeCorrelation f
                (replaceCoordinate (y i) j x)) (sigma i x)‖ := by
            simpa only [sigma, coordinateRestriction,
              show n + 1 + 1 = n + 2 by omega] using
              hlarge _ (hmem i x hx)
          have hsq : (gamma * (N : Real) ^ (n + 2)) ^ 2 ≤
              ‖fourier (higherCubeCorrelation f
                (replaceCoordinate (y i) j x)) (sigma i x)‖ ^ 2 :=
            (sq_le_sq₀ (mul_nonneg hgamma.le (by positivity))
              (norm_nonneg _)).2 hnorm
          have hupper := prop143_fourier_sq_le f (y i) j x (sigma i x)
          apply le_of_mul_le_mul_left _ hNn
          calc
            (N : Real) ^ n *
                (gamma ^ 2 * (N : Real) ^ (n + 4)) =
                (gamma * (N : Real) ^ (n + 2)) ^ 2 := by
                  rw [show (N : Real) ^ (n + 4) =
                      (N : Real) ^ n * (N : Real) ^ 4 by rw [pow_add],
                    show (N : Real) ^ (n + 2) =
                      (N : Real) ^ n * (N : Real) ^ 2 by rw [pow_add]]
                  ring
            _ ≤ ‖fourier (higherCubeCorrelation f
                (replaceCoordinate (y i) j x)) (sigma i x)‖ ^ 2 := hsq
            _ ≤ (N : Real) ^ n * ∑ u : Point N n,
                ‖fourier (firstCoordinateCorrelation
                  (prop143Component f (y i) j u) x) (sigma i x)‖ ^ 2 :=
              hupper
        have hcomponentProd (x : ZMod N) (hx : x ∈ E) :
            (gamma ^ 2 * (N : Real) ^ (n + 4)) ^ p ≤
              ∏ i : Fin p, ∑ u : U,
                ‖fourier (firstCoordinateCorrelation
                  (prop143Component f (y i) j u) x) (sigma i x)‖ ^ 2 := by
          calc
            (gamma ^ 2 * (N : Real) ^ (n + 4)) ^ p =
                ∏ _i : Fin p,
                  (gamma ^ 2 * (N : Real) ^ (n + 4)) := by
                    simp
            _ ≤ _ := Finset.prod_le_prod
              (fun _ _ => mul_nonneg (sq_nonneg _) (by positivity))
              (fun i _ => hcomponentSum i x hx)
        have htotalEq :
            (∑ v : V, S v) = ∑ x : ZMod N, lambda x *
              ∏ i : Fin p, ∑ u : U,
                ‖fourier (firstCoordinateCorrelation
                  (prop143Component f (y i) j u) x) (sigma i x)‖ ^ 2 := by
          dsimp only [S, C]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro x _
          rw [← Finset.mul_sum]
          congr 1
          exact (Fintype.prod_sum (fun i (u : U) =>
            ‖fourier (firstCoordinateCorrelation
              (prop143Component f (y i) j u) x) (sigma i x)‖ ^ 2)).symm
        have hlambdaSum : (∑ x : ZMod N, lambda x) = T := by
          simp [lambda, prop14RestrictedWeight, T]
        have htotal :
            T * (gamma ^ 2 * (N : Real) ^ (n + 4)) ^ p ≤
              ∑ v : V, S v := by
          calc
            T * (gamma ^ 2 * (N : Real) ^ (n + 4)) ^ p =
                (∑ x : ZMod N, lambda x) *
                  (gamma ^ 2 * (N : Real) ^ (n + 4)) ^ p := by
                    rw [hlambdaSum]
            _ = ∑ x : ZMod N, lambda x *
                (gamma ^ 2 * (N : Real) ^ (n + 4)) ^ p := by
                  rw [Finset.sum_mul]
            _ ≤ ∑ x : ZMod N, lambda x *
                ∏ i : Fin p, ∑ u : U,
                  ‖fourier (firstCoordinateCorrelation
                    (prop143Component f (y i) j u) x) (sigma i x)‖ ^ 2 := by
                      apply Finset.sum_le_sum
                      intro x _
                      by_cases hx : x ∈ E
                      · exact mul_le_mul_of_nonneg_left
                          (hcomponentProd x hx) (by
                            simp [lambda, prop14RestrictedWeight, hx, htheta x])
                      · simp [lambda, prop14RestrictedWeight, hx]
            _ = ∑ v : V, S v := htotalEq.symm
        let threshold : Real :=
          gamma ^ (2 * p) * (N : Real) ^ (4 * p) * T
        have hcardV : Fintype.card V = N ^ (n * p) := by
          simp [V, U, Point, ← pow_mul]
        have haverage : (∑ _v : V, threshold) ≤ ∑ v : V, S v := by
          calc
            (∑ _v : V, threshold) =
                (N : Real) ^ (n * p) * threshold := by
                  simp only [Finset.sum_const, Finset.card_univ, hcardV,
                    nsmul_eq_mul]
                  push_cast
                  rfl
            _ = T * (gamma ^ 2 * (N : Real) ^ (n + 4)) ^ p := by
              dsimp only [threshold]
              rw [mul_pow,
                show (gamma ^ 2) ^ p = gamma ^ (2 * p) by rw [← pow_mul],
                show ((N : Real) ^ (n + 4)) ^ p =
                  (N : Real) ^ ((n + 4) * p) by rw [← pow_mul]]
              rw [← show (N : Real) ^ (n * p) * (N : Real) ^ (4 * p) =
                (N : Real) ^ ((n + 4) * p) by
                  rw [← pow_add]
                  congr 1
                  ring]
              ring
            _ ≤ ∑ v : V, S v := htotal
        have hVnonempty : (Finset.univ : Finset V).Nonempty :=
          ⟨default, Finset.mem_univ _⟩
        have haverage' :
            (∑ v ∈ (Finset.univ : Finset V), threshold) ≤
              ∑ v ∈ (Finset.univ : Finset V), S v := by
          simpa only [Finset.sum_filter, Finset.filter_true_of_mem] using haverage
        obtain ⟨v, _, hv⟩ :=
          Finset.exists_le_of_sum_le hVnonempty haverage'
        let alpha : Real := gamma ^ (2 * p) * (N : Real)⁻¹ * T
        have halpha : 0 < alpha := by
          dsimp only [alpha]
          positivity
        have hlambda : ∀ x, 0 ≤ lambda x := by
          intro x
          simp only [lambda, prop14RestrictedWeight]
          split_ifs
          · exact htheta x
          · exact le_rfl
        have hCdisc : ∀ i, DiscValued (C v i) := by
          intro i
          exact prop143_component_disc f hf (y i) j (v i)
        have hinput :
            alpha * (N : Real) ^ (4 * p + 1) ≤
              ∑ x : ZMod N, lambda x * ∏ i : Fin p,
                ‖fourier (firstCoordinateCorrelation (C v i) x) (sigma i x)‖ ^ 2 := by
          calc
            alpha * (N : Real) ^ (4 * p + 1) = threshold := by
              dsimp only [alpha, threshold]
              field_simp
              ring
            _ ≤ S v := hv
            _ = _ := by rfl
        have hresult := proposition_14_1_holds N p lambda (C v) sigma alpha
          halpha.le hlambda hCdisc hinput
        rw [prop14_univ_restricted_energy_eq E theta sigma] at hresult
        calc
          gamma ^ (8 * p) * (N : Real)⁻¹ * T ^ 4 =
              alpha ^ 4 * (N : Real) ^ 3 := by
                dsimp only [alpha]
                field_simp
                rw [← pow_mul]
                ring
          _ ≤ weightedSimultaneousAdditiveEnergy E theta sigma := hresult

end LeanProofs.GowersSzemeredi
