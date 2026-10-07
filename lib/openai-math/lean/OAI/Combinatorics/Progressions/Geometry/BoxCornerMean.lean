/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Geometry.BoxDifferenceHom

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def MissesBoxCoordinate {n : ℕ} {X : Type*} (U : (Fin n → X) → ℂ) (i : Fin n) : Prop :=
  ∀ x a, U (Function.update x i a) = U x

theorem missesBoxCoordinate_head {n : ℕ} {X : Type*}
    {U : (Fin (n + 1) → X) → ℂ} (hU : MissesBoxCoordinate U 0)
    (a b : X) (x : Fin n → X) : U (Fin.cons a x) = U (Fin.cons b x) := by
  simpa only [Fin.update_cons_zero] using hU (Fin.cons b x) a

noncomputable def boxTailPhase {n : ℕ} {X : Type*}
    (F : (Fin (n + 1) → X) → ℂ) (a b : X) (x : Fin n → X) : ℂ :=
  F (Fin.cons a x) * star (F (Fin.cons b x))

noncomputable def boxTailTests {n : ℕ} {X : Type*}
    (U : Fin (n + 1) → (Fin (n + 1) → X) → ℂ) (a b : X)
    (i : Fin n) (x : Fin n → X) : ℂ :=
  U i.succ (Fin.cons a x) * star (U i.succ (Fin.cons b x))

theorem boxTailTests_misses {n : ℕ} {X : Type*}
    (U : Fin (n + 1) → (Fin (n + 1) → X) → ℂ)
    (hU : ∀ i, MissesBoxCoordinate (U i) i) (a b : X) (i : Fin n) :
    MissesBoxCoordinate (boxTailTests U a b i) i := by
  intro x c
  simp only [boxTailTests, Fin.cons_update]
  rw [hU i.succ (Fin.cons a x) c, hU i.succ (Fin.cons b x) c]

theorem boxTailTests_norm {n : ℕ} {X : Type*}
    (U : Fin (n + 1) → (Fin (n + 1) → X) → ℂ)
    (hU : ∀ i x, ‖U i x‖ ≤ 1) (a b : X) (i : Fin n) (x : Fin n → X) :
    ‖boxTailTests U a b i x‖ ≤ 1 := by
  rw [boxTailTests, norm_mul, norm_star]
  exact (mul_le_mul (hU _ _) (hU _ _) (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)

noncomputable def boxTestCorrelation {n : ℕ} {X : Type*} [Fintype X]
    (F : (Fin n → X) → ℂ) (U : Fin n → (Fin n → X) → ℂ) : ℂ :=
  𝔼 x, F x * ∏ i, U i x

theorem boxTestCorrelation_zero {X : Type*} [Fintype X]
    (F : (Fin 0 → X) → ℂ) (U : Fin 0 → (Fin 0 → X) → ℂ) :
    boxTestCorrelation F U = F (fun i => Fin.elim0 i) := by
  simp only [boxTestCorrelation, Fin.prod_univ_zero, mul_one, expect_empty_tuple]

noncomputable def boxPhaseMoment {X : Type*} [Fintype X] (n : ℕ)
    (F : (Fin n → X) → ℂ) : ℂ :=
  𝔼 u, 𝔼 v, iteratedBoxDifference n (fun x (_ : Unit) => F x) u v ()

theorem boxPhaseMoment_zero {X : Type*} [Fintype X] (F : (Fin 0 → X) → ℂ) :
    boxPhaseMoment 0 F = F (fun i => Fin.elim0 i) := by
  simp only [boxPhaseMoment, iteratedBoxDifference, Fintype.expect_const]

theorem boxPhaseMoment_succ {X : Type*} [Fintype X] (n : ℕ)
    (F : (Fin (n + 1) → X) → ℂ) :
    boxPhaseMoment (n + 1) F = 𝔼 a, 𝔼 b, boxPhaseMoment n (boxTailPhase F a b) := by
  rw [boxPhaseMoment, expect_two_dependent_fin_cons]
  rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def boxCorner {n : ℕ} {X : Type*} (u v : Fin n → X) (ω : Fin n → Bool) : Fin n → X :=
  fun i => if ω i then v i else u i

def boxCornerProduct {n : ℕ} {X : Type*} (F : (Fin n → X) → ℂ) (u v : Fin n → X) : ℂ :=
  ∏ ω : Fin n → Bool, conjugationPower (booleanWeight ω) (F (boxCorner u v ω))

theorem conjugationPower_eq_if_mod (n : ℕ) (z : ℂ) :
    conjugationPower n z = if n % 2 = 0 then z else star z := by
  induction n with
  | zero => simp [conjugationPower]
  | succ n ih =>
    have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hn with hn | hn <;>
      simp [conjugationPower, ih, Nat.add_mod, hn]

theorem boxCorner_cons_false {n : ℕ} {X : Type*} (u v : Fin (n + 1) → X) (ω : Fin n → Bool) :
    boxCorner u v (Fin.cons false ω) = Fin.cons (u 0) (boxCorner (Fin.tail u) (Fin.tail v) ω) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem boxCorner_cons_true {n : ℕ} {X : Type*} (u v : Fin (n + 1) → X) (ω : Fin n → Bool) :
    boxCorner u v (Fin.cons true ω) = Fin.cons (v 0) (boxCorner (Fin.tail u) (Fin.tail v) ω) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem boxCornerProduct_mul {n : ℕ} {X : Type*} (F G : (Fin n → X) → ℂ) (u v : Fin n → X) :
    boxCornerProduct (fun x => F x * G x) u v = boxCornerProduct F u v * boxCornerProduct G u v := by
  simp only [boxCornerProduct, map_mul, Finset.prod_mul_distrib]

theorem boxCornerProduct_star {n : ℕ} {X : Type*} (F : (Fin n → X) → ℂ) (u v : Fin n → X) :
    boxCornerProduct (fun x => star (F x)) u v = star (boxCornerProduct F u v) := by
  simp only [boxCornerProduct, conjugationPower_star, star_prod]

theorem boxCornerProduct_succ {n : ℕ} {X : Type*} (F : (Fin (n + 1) → X) → ℂ)
    (u v : Fin (n + 1) → X) :
    boxCornerProduct F u v =
      boxCornerProduct (fun x => F (Fin.cons (u 0) x)) (Fin.tail u) (Fin.tail v) *
        star (boxCornerProduct (fun x => F (Fin.cons (v 0) x)) (Fin.tail u) (Fin.tail v)) := by
  simp only [boxCornerProduct]
  rw [prod_bool_tuple_succ]
  simp only [booleanWeight_cons_false, booleanWeight_cons_true, boxCorner_cons_false,
    boxCorner_cons_true, conjugationPower, RingHom.comp_apply, starRingEnd_apply, star_prod]

theorem iteratedBoxDifference_eq_cornerProduct {X Z : Type*} (n : ℕ)
    (F : (Fin n → X) → Z → ℂ) (u v : Fin n → X) (z : Z) :
    iteratedBoxDifference n F u v z = boxCornerProduct (fun x => F x z) u v := by
  induction n with
  | zero =>
    rw [boxCornerProduct, Fintype.prod_subsingleton _ (default : Fin 0 → Bool)]
    simp only [booleanWeight, Fin.sum_univ_zero, conjugationPower, RingHom.id_apply, iteratedBoxDifference]
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    rw [iteratedBoxDifference, ih, boxCornerProduct_mul, boxCornerProduct_star, boxCornerProduct_succ]

theorem boxPhaseMoment_eq_expect_cornerProduct {n : ℕ} {X : Type*} [Fintype X]
    (F : (Fin n → X) → ℂ) :
    boxPhaseMoment n F = 𝔼 u, 𝔼 v, boxCornerProduct F u v := by
  simp only [boxPhaseMoment, iteratedBoxDifference_eq_cornerProduct]

theorem boxCorner_pair {n : ℕ} {X : Type*} (x : (Fin n × Bool) → X) (ω : Fin n → Bool) :
    boxCorner (fun i => x (i, false)) (fun i => x (i, true)) ω = fun i => x (i, ω i) := by
  funext i
  cases h : ω i <;> simp [boxCorner, h]

theorem boxCornerProduct_map {n : ℕ} {X Y : Type*} (φ : X → Y)
    (F : (Fin n → Y) → ℂ) (u v : Fin n → X) :
    boxCornerProduct (fun x => F (fun i => φ (x i))) u v =
      boxCornerProduct F (fun i => φ (u i)) (fun i => φ (v i)) := by
  unfold boxCornerProduct
  apply Finset.prod_congr rfl
  intro ω _
  apply congrArg (conjugationPower (booleanWeight ω))
  change F (fun i => φ (boxCorner u v ω i)) =
    F (boxCorner (fun i => φ (u i)) (fun i => φ (v i)) ω)
  apply congrArg F
  funext i
  cases h : ω i <;> simp [boxCorner, h]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def boxTailAmplitude {n : ℕ} {X : Type*}
    (F : (Fin (n + 1) → X) → ℂ) (U : Fin (n + 1) → (Fin (n + 1) → X) → ℂ)
    (a : X) (x : Fin n → X) : ℂ :=
  F (Fin.cons a x) * ∏ i : Fin n, U i.succ (Fin.cons a x)

theorem boxTailAmplitude_cross {n : ℕ} {X : Type*}
    (F : (Fin (n + 1) → X) → ℂ) (U : Fin (n + 1) → (Fin (n + 1) → X) → ℂ)
    (a b : X) (x : Fin n → X) :
    boxTailAmplitude F U a x * star (boxTailAmplitude F U b x) =
      boxTailPhase F a b x * ∏ i, boxTailTests U a b i x := by
  simp only [boxTailAmplitude, boxTailPhase, boxTailTests, star_mul, star_prod,
    Finset.prod_mul_distrib]
  ring

theorem boxTestCorrelation_head {n : ℕ} {X : Type*} [Fintype X]
    (F : (Fin (n + 1) → X) → ℂ) (U : Fin (n + 1) → (Fin (n + 1) → X) → ℂ)
    (hU : MissesBoxCoordinate (U 0) 0) (base : X) :
    boxTestCorrelation F U =
      𝔼 x : Fin n → X, U 0 (Fin.cons base x) * (𝔼 a, boxTailAmplitude F U a x) := by
  rw [boxTestCorrelation, expect_dependent_fin_cons, Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro x _
  rw [Finset.mul_expect]
  apply Finset.expect_congr rfl
  intro a _
  rw [Fin.prod_univ_succ, missesBoxCoordinate_head hU a base x]
  unfold boxTailAmplitude
  ring

theorem boxTestCorrelation_square_le {n : ℕ} {X : Type*} [Fintype X] [Nonempty X]
    (F : (Fin (n + 1) → X) → ℂ) (U : Fin (n + 1) → (Fin (n + 1) → X) → ℂ)
    (hU : ∀ x, ‖U 0 x‖ ≤ 1) (hmiss : MissesBoxCoordinate (U 0) 0) :
    ‖boxTestCorrelation F U‖ ^ 2 ≤
      (𝔼 a, 𝔼 b, boxTestCorrelation (boxTailPhase F a b) (boxTailTests U a b)).re := by
  let base : X := Classical.choice inferInstance
  have h := finite_family_cauchy_schwarz_re
    (fun x : Fin n → X => U 0 (Fin.cons base x)) (boxTailAmplitude F U)
    (fun x => hU (Fin.cons base x))
  rw [← boxTestCorrelation_head F U hmiss base] at h
  simp only [one_pow, one_mul] at h
  simp_rw [boxTailAmplitude_cross] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def boxCornerAnchor {n : ℕ} {X : Type*}
    (F : (Fin n → X) → ℂ) (a z : Fin n → X) : ℂ := by
  classical
  exact ∏ ω ∈ (Finset.univ.erase (fun _ : Fin n => false)),
    conjugationPower (booleanWeight ω) (F (boxCorner z a ω))

theorem boxCornerProduct_eq_mul_anchor {n : ℕ} {X : Type*}
    (F : (Fin n → X) → ℂ) (z a : Fin n → X) :
    boxCornerProduct F z a = F z * boxCornerAnchor F a z := by
  classical
  have h := (Finset.mul_prod_erase Finset.univ
    (fun ω => conjugationPower (booleanWeight ω) (F (boxCorner z a ω)))
    (Finset.mem_univ (fun _ : Fin n => false))).symm
  have hz : boxCorner z a (fun _ => false) = z := rfl
  simpa [boxCornerProduct, boxCornerAnchor, booleanWeight, hz, conjugationPower] using h

theorem boxCornerAnchor_norm_le_one {n : ℕ} {X : Type*}
    (F : (Fin n → X) → ℂ) (hF : ∀ z, ‖F z‖ ≤ 1) (a z : Fin n → X) :
    ‖boxCornerAnchor F a z‖ ≤ 1 := by
  classical
  unfold boxCornerAnchor
  rw [norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro ω _
  rw [conjugationPower_eq_if_mod]
  split_ifs <;> simpa only [norm_star] using hF (boxCorner z a ω)

theorem boxCornerAnchor_map {n : ℕ} {X Y : Type*} (φ : X → Y)
    (F : (Fin n → Y) → ℂ) (a z : Fin n → X) :
    boxCornerAnchor (fun x => F (fun i => φ (x i))) a z =
      boxCornerAnchor F (fun i => φ (a i)) (fun i => φ (z i)) := by
  classical
  unfold boxCornerAnchor
  apply Finset.prod_congr rfl
  intro ω _
  apply congrArg (conjugationPower (booleanWeight ω))
  apply congrArg F
  funext i
  cases h : ω i <;> simp [boxCorner, h]

theorem boxCornerAnchor_prod_equiv {n m : ℕ} {X : Type*}
    (e : Fin m ≃ (Finset.univ.erase (fun _ : Fin n => false)))
    (F : (Fin n → X) → ℂ) (a z : Fin n → X) :
    (∏ l, conjugationPower (booleanWeight (e l).val) (F (boxCorner z a (e l).val))) =
      boxCornerAnchor F a z := by
  classical
  calc
    _ = ∏ ω : (Finset.univ.erase (fun _ : Fin n => false)),
        conjugationPower (booleanWeight ω.val) (F (boxCorner z a ω.val)) :=
      Fintype.prod_equiv e _ _ (fun _ => rfl)
    _ = _ := by
      unfold boxCornerAnchor
      exact Finset.prod_coe_sort (Finset.univ.erase (fun _ : Fin n => false))
        (fun ω : Fin n → Bool => conjugationPower (booleanWeight ω) (F (boxCorner z a ω)))

theorem exists_box_corner_anchor_correlation {n : ℕ} {X : Type*}
    [Fintype X] [Nonempty X] (F : (Fin n → X) → ℂ) :
    ∃ a : Fin n → X, (boxPhaseMoment n F).re ≤
      ‖𝔼 z : Fin n → X, F z * boxCornerAnchor F a z‖ := by
  have hm : boxPhaseMoment n F =
      𝔼 a : Fin n → X, 𝔼 z : Fin n → X, F z * boxCornerAnchor F a z := by
    rw [boxPhaseMoment_eq_expect_cornerProduct, Finset.expect_comm]
    simp_rw [boxCornerProduct_eq_mul_anchor]
  have hmean : (boxPhaseMoment n F).re =
      𝔼 a : Fin n → X, (𝔼 z : Fin n → X, F z * boxCornerAnchor F a z).re := by
    rw [hm, expect_re]
  obtain ⟨a, _, ha⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean.le
  exact ⟨a, ha.trans (Complex.re_le_norm _)⟩

theorem exists_true_of_ne_false {n : ℕ} {ω : Fin n → Bool}
    (h : ω ≠ fun _ => false) : ∃ k, ω k = true := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp h
  refine ⟨k, ?_⟩
  cases he : ω k <;> simp_all

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem boxTest_cauchySchwarz {X : Type*} [Fintype X] [Nonempty X] (n : ℕ) :
    ∀ (F : (Fin (n + 1) → X) → ℂ) (U : Fin (n + 1) → (Fin (n + 1) → X) → ℂ),
      (∀ i x, ‖U i x‖ ≤ 1) → (∀ i, MissesBoxCoordinate (U i) i) →
      ‖boxTestCorrelation F U‖ ^ (2 ^ (n + 1)) ≤ (boxPhaseMoment (n + 1) F).re := by
  induction n with
  | zero =>
    intro F U hU hmiss
    simpa only [Nat.zero_add, pow_one, boxPhaseMoment_succ,
      boxPhaseMoment_zero, boxTestCorrelation_zero] using
      boxTestCorrelation_square_le F U (hU 0) (hmiss 0)
  | succ n ih =>
    intro F U hU hmiss
    have hr : (𝔼 a, 𝔼 b, boxTestCorrelation (boxTailPhase F a b) (boxTailTests U a b)).re ≤
        𝔼 a, 𝔼 b, ‖boxTestCorrelation (boxTailPhase F a b) (boxTailTests U a b)‖ := by
      simp only [expect_re]
      apply Finset.expect_le_expect
      intro a _
      apply Finset.expect_le_expect
      intro b _
      exact Complex.re_le_norm _
    have hcs := (boxTestCorrelation_square_le F U (hU 0) (hmiss 0)).trans hr
    calc
      _ = (‖boxTestCorrelation F U‖ ^ 2) ^ (2 ^ (n + 1)) := by
        rw [← pow_mul, pow_succ]
        congr 1
        omega
      _ ≤ (𝔼 a, 𝔼 b, ‖boxTestCorrelation (boxTailPhase F a b) (boxTailTests U a b)‖) ^
          (2 ^ (n + 1)) := pow_le_pow_left₀ (sq_nonneg _) hcs _
      _ ≤ 𝔼 a, 𝔼 b, ‖boxTestCorrelation (boxTailPhase F a b) (boxTailTests U a b)‖ ^
          (2 ^ (n + 1)) := expect_double_pow_two_pow_le (n + 1) _ (fun _ _ => norm_nonneg _)
      _ ≤ 𝔼 a, 𝔼 b, (boxPhaseMoment (n + 1) (boxTailPhase F a b)).re := by
        apply Finset.expect_le_expect
        intro a _
        apply Finset.expect_le_expect
        intro b _
        exact ih _ _ (boxTailTests_norm U hU a b) (boxTailTests_misses U hmiss a b)
      _ = _ := by rw [boxPhaseMoment_succ]; simp only [expect_re]

theorem boxTest_cauchySchwarz_of_pos {X : Type*} [Fintype X] [Nonempty X] {h : ℕ}
    (hh : 0 < h) (F : (Fin h → X) → ℂ) (U : Fin h → (Fin h → X) → ℂ)
    (hU : ∀ i x, ‖U i x‖ ≤ 1) (hmiss : ∀ i, MissesBoxCoordinate (U i) i) :
    ‖boxTestCorrelation F U‖ ^ (2 ^ h) ≤ (boxPhaseMoment h F).re := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hh)
  exact boxTest_cauchySchwarz n F U hU hmiss

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def assignedBoxTest {n : ℕ} {S X : Type*} [Fintype S]
    (assignment : S → Fin n) (U : S → (Fin n → X) → ℂ)
    (i : Fin n) (x : Fin n → X) : ℂ :=
  ∏ s, if assignment s = i then U s x else 1

theorem assignedBoxTest_prod {n : ℕ} {S X : Type*} [Fintype S]
    (assignment : S → Fin n) (U : S → (Fin n → X) → ℂ) (x : Fin n → X) :
    (∏ i, assignedBoxTest assignment U i x) = ∏ s, U s x := by
  unfold assignedBoxTest
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro s _
  simp

theorem assignedBoxTest_norm {n : ℕ} {S X : Type*} [Fintype S]
    (assignment : S → Fin n) (U : S → (Fin n → X) → ℂ)
    (hU : ∀ s x, ‖U s x‖ ≤ 1) (i : Fin n) (x : Fin n → X) :
    ‖assignedBoxTest assignment U i x‖ ≤ 1 := by
  rw [assignedBoxTest, norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro s _
  split_ifs
  · exact hU s x
  · simp only [norm_one, le_refl]

theorem assignedBoxTest_misses {n : ℕ} {S X : Type*} [Fintype S]
    (assignment : S → Fin n) (U : S → (Fin n → X) → ℂ)
    (hU : ∀ s, MissesBoxCoordinate (U s) (assignment s)) (i : Fin n) :
    MissesBoxCoordinate (assignedBoxTest assignment U i) i := by
  intro x a
  apply Finset.prod_congr rfl
  intro s _
  by_cases hs : assignment s = i
  · simp only [hs, ite_true]
    simpa only [hs] using hU s x a
  · simp only [hs, ite_false]

theorem assigned_site_cauchySchwarz {h : ℕ} {S X : Type*}
    [Fintype S] [Fintype X] [Nonempty X] (hh : 0 < h)
    (F : (Fin h → X) → ℂ) (assignment : S → Fin h)
    (U : S → (Fin h → X) → ℂ) (hU : ∀ s x, ‖U s x‖ ≤ 1)
    (hmiss : ∀ s, MissesBoxCoordinate (U s) (assignment s)) :
    ‖𝔼 x, F x * ∏ s, U s x‖ ^ (2 ^ h) ≤ (boxPhaseMoment h F).re := by
  have hc := boxTest_cauchySchwarz_of_pos hh F (assignedBoxTest assignment U)
    (assignedBoxTest_norm assignment U hU) (assignedBoxTest_misses assignment U hmiss)
  simpa only [boxTestCorrelation, assignedBoxTest_prod] using hc

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def boxPairEquiv (n : ℕ) (X : Type*) :
    ((Fin n × Bool) → X) ≃ ((Fin n → X) × (Fin n → X)) where
  toFun x := (fun i => x (i, false), fun i => x (i, true))
  invFun u := fun p => if p.2 then u.2 p.1 else u.1 p.1
  left_inv x := by
    funext p
    rcases p with ⟨i, b⟩
    cases b <;> rfl
  right_inv u := by
    rcases u with ⟨u, v⟩
    rfl

theorem integerBox_cornerProduct_mean (n N : ℕ) [NeZero N] (F : (Fin n → ℤ) → ℂ) :
    (𝔼 x ∈ integerBox (fun _ : Fin n × Bool => N),
      boxCornerProduct F (fun i => x (i, false)) (fun i => x (i, true))) =
      boxPhaseMoment n (fun x : Fin n → ZMod N => F (fun i => (x i).val)) := by
  rw [integerBox_expect_eq_zmod, boxPhaseMoment_eq_expect_cornerProduct]
  have hmap (u v : Fin n → ZMod N) :
      boxCornerProduct (fun x => F (fun i => ((x i).val : ℤ))) u v =
        boxCornerProduct F (fun i => ((u i).val : ℤ)) (fun i => ((v i).val : ℤ)) :=
    boxCornerProduct_map (fun z : ZMod N => (z.val : ℤ)) F u v
  simp_rw [hmap]
  calc
    _ = 𝔼 u : (Fin n → ZMod N) × (Fin n → ZMod N),
        boxCornerProduct F (fun i => (u.1 i).val) (fun i => (u.2 i).val) := by
      apply Fintype.expect_equiv (boxPairEquiv n (ZMod N))
      intro x
      rfl
    _ = _ := expect_prod_split _

end Erdos3

end

end OAI
