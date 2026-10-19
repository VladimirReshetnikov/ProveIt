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
  | cons x _ ih =>
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
      · have hy : y = Fin.cons (y 0) (Fin.tail y) := by norm_num
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

private def prop14RestrictedWeight {N : Nat} [NeZero N]
    (E : Finset (ZMod N)) (theta : ZMod N → Real) : ZMod N → Real :=
  fun x => if x ∈ E then theta x else 0

private lemma prop14_restricted_weight_eq_energy {N p : Nat} [NeZero N]
    (E : Finset (ZMod N)) (theta : ZMod N → Real)
    (sigma : Fin p → ZMod N → ZMod N) :
    simultaneouslyAdditiveWeight (prop14RestrictedWeight E theta) sigma =
      weightedSimultaneousAdditiveEnergy E theta sigma := by
  unfold simultaneouslyAdditiveWeight weightedSimultaneousAdditiveEnergy
  refine Fintype.sum_equiv
    ({ toFun q := ![q 0, q 3, q 2, q 1]
       invFun q := ![q 0, q 3, q 2, q 1]
       left_inv q := by funext i; fin_cases i <;> rfl
       right_inv q := by funext i; fin_cases i <;> rfl } : (Fin 4 → ZMod N) ≃ (Fin 4 → ZMod N))
    _ _ fun q => ?_
  -- the restricted weights multiply to a single indicator of `q 0, …, q 3 ∈ E`
  simp only [IsSimultaneouslyAdditive, IsAdditiveQuadruple, sub_eq_sub_iff_add_eq_add,
    Fin.prod_univ_four, Equiv.coe_fn_mk, Matrix.cons_val, prop14RestrictedWeight,
    ite_zero_mul_ite_zero, ← ite_and]
  exact if_congr ⟨fun ⟨hA, ⟨⟨h0, h1⟩, h2⟩, h3⟩ => ⟨fun t => by fin_cases t <;> assumption, hA⟩,
    fun ⟨h, hA⟩ => ⟨hA, ⟨⟨h 0, h 3⟩, h 2⟩, h 1⟩⟩ (by ring) rfl

/-- Lemma 14.2, uniformly for every coordinate direction. -/
theorem lemma_14_2_holds : lemma_14_2 := by
  intro N k _ gamma f B phi hgamma hf hlarge p j y E theta htheta hmem
  cases k with
  | zero => exact Fin.elim0 j
  | succ n =>
      have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
      rcases (Finset.sum_nonneg fun x _ => htheta x : 0 ≤ ∑ x ∈ E, theta x).eq_or_lt with hT | hT
      · -- an empty weight: the energy is nonnegative
        have h0 : 0 ≤ weightedSimultaneousAdditiveEnergy E theta
            (fun i => coordinateRestriction phi (y i) j) :=
          Finset.sum_nonneg fun q _ => by
            split_ifs
            exacts [Finset.prod_nonneg fun t _ => htheta _, le_rfl]
        simpa [← hT] using h0
      -- Proposition 12.1 for the components `x ↦ ∂_{y_i} f` with `α = γ^(2p)·T/N`
      have hinput : gamma ^ (2 * p) * (N : Real)⁻¹ * (∑ x ∈ E, theta x) *
            (N : Real) ^ (2 * p + 1) ≤
          ∑ x, prop14RestrictedWeight E theta x * ∏ i : Fin p,
            ‖fourier (difference (prop142Component f (y i) j) x)
              (coordinateRestriction phi (y i) j x)‖ ^ 2 := by
        calc _ = ∑ x ∈ E, theta x * ∏ _i : Fin p, (gamma * N) ^ 2 := by
              rw [← Finset.sum_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
              field_simp
              ring
          _ ≤ ∑ x ∈ E, theta x * ∏ i : Fin p,
                ‖fourier (difference (prop142Component f (y i) j) x)
                  (coordinateRestriction phi (y i) j x)‖ ^ 2 := by
              gcongr with x hx i
              · exact htheta x
              rw [prop142_component_difference]
              exact hlarge _ (hmem i x hx)
          _ = _ := by simp [prop14RestrictedWeight, ite_mul]
      have h := proposition_12_1_holds N p (prop14RestrictedWeight E theta)
        (fun i => prop142Component f (y i) j) (fun i => coordinateRestriction phi (y i) j) _
        (by positivity) (fun x => ite_nonneg (htheta x) le_rfl)
        (fun i => cubeDifference_discValued hf (j.removeNth (y i))) hinput
      rw [prop14_restricted_weight_eq_energy] at h
      convert h using 1
      field_simp
      ring

alias prop14_countWhere_eq_sum_ite := gcs_countWhere_eq_sum_ite

alias prop143_boolWeight_insertNth := gcs_boolWeight_insertNth

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
  -- split each vertex `e` at the coordinate `j` into its `j`th bit and the rest
  rw [← Fintype.prod_bijective (fun be : Bool × (Fin n → Bool) =>
      (j.insertNth be.1 be.2 : Fin (n + 1) → Bool))
    (Fin.insertNthEquiv (fun _ : Fin (n + 1) => Bool) j).bijective _ _ fun _ => rfl,
    Fintype.prod_prod_type, Fintype.prod_bool]
  simp only [prop143Component, star_prod]
  congr 1 <;> refine Finset.prod_congr rfl fun e _ => ?_
  · rw [prop143_vertex_insertNth z j u a h true e, if_pos rfl]
    simp only [prop143_even_true]
  · rw [prop143_vertex_insertNth z j u a h false e]
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
            refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun a _ => ?_
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
  calc _ ≤ (∑ u : Point N n,
        ‖fourier (firstCoordinateCorrelation (prop143Component f z j u) h) r‖) ^ 2 := by
        rw [prop143_fourier_decomposition]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ _ := by
      simpa only [Finset.card_univ, hcard, Nat.cast_pow] using
        sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun u : Point N n =>
          ‖fourier (firstCoordinateCorrelation (prop143Component f z j u) h) r‖)

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
      have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
      have hT : 0 ≤ ∑ x ∈ E, theta x := Finset.sum_nonneg fun x _ => htheta x
      -- at `x ∈ E`, the components on the `i`th line carry Fourier mass `γ²·N^(n+4)`
      have hcomp (i : Fin p) (x : ZMod N) (hx : x ∈ E) :
          gamma ^ 2 * (N : Real) ^ (n + 4) ≤ ∑ u : Point N n,
            ‖fourier (firstCoordinateCorrelation (prop143Component f (y i) j u) x)
              (coordinateRestriction phi (y i) j x)‖ ^ 2 := by
        refine le_of_mul_le_mul_left ?_ (by positivity : (0 : Real) < N ^ n)
        calc (N : Real) ^ n * (gamma ^ 2 * (N : Real) ^ (n + 4)) =
              (gamma * (N : Real) ^ (n + 1 + 1)) ^ 2 := by ring
          _ ≤ _ := pow_le_pow_left₀ (by positivity) (hlarge _ (hmem i x hx)) 2
          _ ≤ _ := prop143_fourier_sq_le f (y i) j x _
      -- averaging over the choices `v` of one component per line
      have hV : (Fintype.card (Fin p → Point N n) : Real) = (N : Real) ^ (n * p) := by
        simp [Point, ← pow_mul]
      have hsum := calc
        ∑ _v : Fin p → Point N n, gamma ^ (2 * p) * (N : Real) ^ (4 * p) * ∑ x ∈ E, theta x
            = ∑ x ∈ E, theta x * ∏ _i : Fin p, gamma ^ 2 * (N : Real) ^ (n + 4) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hV, ← Finset.sum_mul,
                Finset.prod_const, Finset.card_univ, Fintype.card_fin]
              ring
          _ ≤ ∑ x ∈ E, theta x * ∏ i : Fin p, ∑ u : Point N n,
                ‖fourier (firstCoordinateCorrelation (prop143Component f (y i) j u) x)
                  (coordinateRestriction phi (y i) j x)‖ ^ 2 := by
              gcongr with x hx i
              · exact htheta x
              exact hcomp i x hx
          _ = ∑ x, prop14RestrictedWeight E theta x * ∏ i : Fin p, ∑ u : Point N n,
                ‖fourier (firstCoordinateCorrelation (prop143Component f (y i) j u) x)
                  (coordinateRestriction phi (y i) j x)‖ ^ 2 := by
              simp [prop14RestrictedWeight, ite_mul]
          _ = ∑ v : Fin p → Point N n, ∑ x, prop14RestrictedWeight E theta x * ∏ i : Fin p,
                ‖fourier (firstCoordinateCorrelation (prop143Component f (y i) j (v i)) x)
                  (coordinateRestriction phi (y i) j x)‖ ^ 2 := by
              simp_rw [Fintype.prod_sum, Finset.mul_sum]
              exact Finset.sum_comm
      obtain ⟨v, -, hv⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
      -- Proposition 14.1 for the components `v` with `α = γ^(2p)·T/N`
      have h := proposition_14_1_holds N p (prop14RestrictedWeight E theta)
        (fun i => prop143Component f (y i) j (v i)) (fun i => coordinateRestriction phi (y i) j)
        (gamma ^ (2 * p) * (N : Real)⁻¹ * ∑ x ∈ E, theta x) (by positivity)
        (fun x => ite_nonneg (htheta x) le_rfl)
        (fun i => prop143_component_disc f hf (y i) j (v i))
        (le_of_eq_of_le (by field_simp; ring) hv)
      rw [prop14_univ_restricted_energy_eq] at h
      convert h using 1
      field_simp
      ring

end LeanProofs.GowersSzemeredi
