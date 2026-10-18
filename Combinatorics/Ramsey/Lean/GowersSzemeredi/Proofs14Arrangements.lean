import GowersSzemeredi.Proofs14Configurations
import Mathlib.Algebra.Order.Chebyshev

/-!
# Product property and respected parallelepiped pairs

This module proves Corollary 14.6.  We first apply Corollary 14.5 in every
last-coordinate section.  For a fixed reference cube, the product property
then produces additive quadruples of cross-sections and vertex values.  The
resulting auxiliary objects map to respected `2`-arrangements; adjoining the
base of the reference cube makes this map injective.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private def cor146Embed {N k : Nat} (x : Point N k) (r : ZMod N) :
    Point N (k + 1) := Fin.snoc x r

private lemma cor146_embed_eq_append {N k : Nat} (x : Point N k)
    (r : ZMod N) : cor146Embed x r = appendCoordinate x r := rfl

private noncomputable def cor146Section {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (r : ZMod N) : Finset (Point N k) := by
  classical
  exact Finset.univ.filter fun x => cor146Embed x r ∈ B

private def cor146SectionPhi {N k : Nat}
    (phi : Point N (k + 1) → ZMod N) (r : ZMod N) : Point N k → ZMod N :=
  fun x => phi (cor146Embed x r)

private lemma cor146_replace_embed {N k : Nat} (y : Point N k)
    (r x : ZMod N) (j : Fin k) :
    replaceCoordinate (cor146Embed y r) j.castSucc x =
      cor146Embed (replaceCoordinate y j x) r := by
  simp [cor146Embed, replaceCoordinate]

private lemma cor146_section_product_property {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (gamma : Real) (hproduct : HasProductProperty B phi gamma) (r : ZMod N) :
    HasProductProperty (cor146Section B r) (cor146SectionPhi phi r) gamma := by
  intro p j y E theta htheta hmem
  have h := hproduct p j.castSucc (fun i => cor146Embed (y i) r) E theta htheta
  rw [show (fun i => coordinateRestriction phi (cor146Embed (y i) r) j.castSucc) =
      fun i => coordinateRestriction (cor146SectionPhi phi r) (y i) j by
    funext i x
    simp only [coordinateRestriction, cor146SectionPhi, cor146_replace_embed]] at h
  apply h
  intro i x hx
  rw [cor146_replace_embed]
  simpa [cor146Section] using hmem i x hx

private lemma cor146_sum_section_card {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) :
    ∑ r : ZMod N, (cor146Section B r).card = B.card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (s := B) (t := Finset.univ)
    (f := fun z => z (Fin.last k)) fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun r _ => Finset.card_nbij' (cor146Embed · r) Fin.init
    (fun x hx => ?_) (fun z hz => ?_) (fun x _ => Fin.init_snoc _ _) fun z hz => ?_
  · simpa [cor146Section, cor146Embed] using hx
  · obtain ⟨hzB, rfl⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hz)
    simpa [cor146Section, cor146Embed] using hzB
  · obtain ⟨-, rfl⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hz)
    exact Fin.snoc_init_self z

private lemma cor146_sum_section_density {N k : Nat} [NeZero N]
    (beta : Real) (B : Finset (Point N (k + 1)))
    (hcard : (B.card : Real) = beta * (N : Real) ^ (k + 1)) :
    ∑ r : ZMod N, (cor146Section B r).card / (N : Real) ^ k = beta * N := by
  calc
    ∑ r : ZMod N, (cor146Section B r).card / (N : Real) ^ k =
        (∑ r : ZMod N, ((cor146Section B r).card : Real)) /
          (N : Real) ^ k := by rw [Finset.sum_div]
    _ = (B.card : Real) / (N : Real) ^ k := by
      congr 1
      exact_mod_cast cor146_sum_section_card B
    _ = beta * N := by
      have hN : (N : Real) ≠ 0 := by exact_mod_cast (NeZero.ne N)
      rw [hcard, pow_succ]
      field_simp

private def cor146GoodPair {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (K : AxisCube N k) (r : ZMod N) (K' : AxisCube N k) : Prop :=
  K.IsIn (cor146Section B r) ∧ K'.IsIn (cor146Section B r) ∧
    K.IsCongruent K' ∧
      K.value (cor146SectionPhi phi r) = K'.value (cor146SectionPhi phi r)

private noncomputable def cor146GoodSet {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (K : AxisCube N k) (r : ZMod N) : Finset (AxisCube N k) := by
  classical
  exact Finset.univ.filter (cor146GoodPair B phi K r)

private def cor146Theta {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (K : AxisCube N k) (r : ZMod N) : Real :=
  (cor146GoodSet B phi K r).card

private lemma cor146_pair_count_eq_sum {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (r : ZMod N) :
    respectedCubePairCount (cor146Section B r) (cor146SectionPhi phi r) =
      ∑ K : AxisCube N k, (cor146GoodSet B phi K r).card := by
  unfold respectedCubePairCount
  change countWhere (fun z : AxisCube N k × AxisCube N k =>
    cor146GoodPair B phi z.1 r z.2) = _
  rw [show countWhere (fun z : AxisCube N k × AxisCube N k =>
      cor146GoodPair B phi z.1 r z.2) =
      ∑ K : AxisCube N k, countWhere (fun K' : AxisCube N k =>
        cor146GoodPair B phi K r K') from
    prop144_countWhere_prod (fun K K' => cor146GoodPair B phi K r K')]
  apply Fintype.sum_congr
  intro K
  unfold cor146GoodSet countWhere cor146GoodPair
  apply congrArg Finset.card
  ext K'
  simp

private lemma cor146_axis_cube_card (N k : Nat) [NeZero N] :
    Fintype.card (AxisCube N k) = N ^ (2 * k) := by
  simp only [AxisCube, Point, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, ZMod.card]
  rw [← pow_add]
  congr 1
  omega

private lemma cor146_pair_first_moment {N k : Nat} [NeZero N]
    (beta gamma : Real) (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N)
    (hk : 1 ≤ k) (_hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hgamma_one : gamma ≤ 1)
    (hcard : (B.card : Real) = beta * (N : Real) ^ (k + 1))
    (hproduct : HasProductProperty B phi gamma) :
    beta ^ (4 ^ k) * gamma ^ (2 * k * 4 ^ k) *
        (N : Real) ^ (3 * k + 1) ≤
      ∑ K : AxisCube N k, ∑ r : ZMod N, cor146Theta B phi K r := by
  have hN : 0 < (N : Real) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have ha0 : 4 ^ k ≠ 0 := by positivity
  let d : ZMod N → Real := fun r => (cor146Section B r).card / (N : Real) ^ k
  have hd_sum : ∑ r, d r = beta * N := cor146_sum_section_density beta B hcard
  have hmean := pow_sum_div_card_le_sum_pow (s := Finset.univ) (f := d)
    (fun r _ => by positivity) (4 ^ k - 1)
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 ha0), hd_sum, Finset.card_univ, ZMod.card,
    mul_pow, ← mul_pow_sub_one ha0 (N : Real), ← mul_assoc,
    mul_div_cancel_right₀ _ (by positivity)] at hmean
  calc beta ^ (4 ^ k) * gamma ^ (2 * k * 4 ^ k) * (N : Real) ^ (3 * k + 1)
      = beta ^ 4 ^ k * N * (gamma ^ (2 * k * 4 ^ k) * (N : Real) ^ (3 * k)) := by ring
    _ ≤ ∑ r, d r ^ 4 ^ k * (gamma ^ (2 * k * 4 ^ k) * (N : Real) ^ (3 * k)) := by
      rw [← Finset.sum_mul]
      gcongr
    _ ≤ ∑ r, (respectedCubePairCount (cor146Section B r) (cor146SectionPhi phi r) : Real) := by
      gcongr with r
      rcases (show 0 ≤ d r by positivity).eq_or_lt with hr | hr
      · rw [← hr, zero_pow ha0, zero_mul]
        positivity
      · simpa only [mul_assoc] using corollary_14_5_holds N k (d r) gamma _ _ hk hr hgamma
          hgamma_one (div_mul_cancel₀ _ (by positivity)).symm
          (cor146_section_product_property B phi gamma hproduct r)
    _ = ∑ K : AxisCube N k, ∑ r : ZMod N, cor146Theta B phi K r := by
      simp only [cor146_pair_count_eq_sum, Nat.cast_sum, cor146Theta]
      exact Finset.sum_comm

private def cor146Average {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (K : AxisCube N k) : Real :=
  (∑ r : ZMod N, cor146Theta B phi K r) / N

private lemma cor146_average_fourth_moment {N k : Nat} [NeZero N]
    (beta gamma : Real) (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N)
    (_hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hfirst : beta ^ (4 ^ k) * gamma ^ (2 * k * 4 ^ k) *
        (N : Real) ^ (3 * k + 1) ≤
      ∑ K : AxisCube N k, ∑ r : ZMod N, cor146Theta B phi K r) :
    (beta ^ (4 ^ k) * gamma ^ (2 * k * 4 ^ k)) ^ 4 *
        (N : Real) ^ (6 * k) ≤
      ∑ K : AxisCube N k, (cor146Average B phi K) ^ 4 := by
  have hN : 0 < (N : Real) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hmean := pow_sum_div_card_le_sum_pow (s := Finset.univ) (f := cor146Average B phi)
    (fun K _ => by unfold cor146Average cor146Theta; positivity) 3
  simp only [Finset.card_univ, cor146_axis_cube_card, Nat.cast_pow] at hmean
  have hsum : beta ^ (4 ^ k) * gamma ^ (2 * k * 4 ^ k) * (N : Real) ^ (3 * k) ≤
      ∑ K, cor146Average B phi K := by
    simp only [cor146Average, ← Finset.sum_div]
    rw [le_div_iff₀ hN, mul_assoc, ← pow_succ]
    exact hfirst
  calc (beta ^ (4 ^ k) * gamma ^ (2 * k * 4 ^ k)) ^ 4 * (N : Real) ^ (6 * k)
      = (beta ^ (4 ^ k) * gamma ^ (2 * k * 4 ^ k) * (N : Real) ^ (3 * k)) ^ 4 /
          ((N : Real) ^ (2 * k)) ^ 3 := by
        rw [eq_div_iff (by positivity)]
        ring
    _ ≤ (∑ K, cor146Average B phi K) ^ 4 / ((N : Real) ^ (2 * k)) ^ 3 := by gcongr
    _ ≤ _ := hmean

private def cor146VertexEquiv (k : Nat) :
    Fin (Fintype.card (Fin k → Bool)) ≃ (Fin k → Bool) :=
  (Fintype.equivFin (Fin k → Bool)).symm

private lemma cor146_vertex_card (k : Nat) :
    Fintype.card (Fin k → Bool) = 2 ^ k := by simp

private noncomputable def cor146ReferenceSection {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (K : AxisCube N k) : Finset (ZMod N) := by
  classical
  exact Finset.univ.filter fun r => K.IsIn (cor146Section B r)

private def cor146Sigma {N k : Nat}
    (phi : Point N (k + 1) → ZMod N) (K : AxisCube N k)
    (i : Fin (Fintype.card (Fin k → Bool))) (r : ZMod N) : ZMod N :=
  phi (cor146Embed (K.vertex (cor146VertexEquiv k i)) r)

private def cor146EnergyCondition {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (K : AxisCube N k) (q : Fin 4 → ZMod N) : Prop :=
  (∀ t, q t ∈ cor146ReferenceSection B K) ∧ IsAdditiveQuadruple q ∧
    ∀ i, IsAdditiveQuadruple (fun t => cor146Sigma phi K i (q t))

private def cor146FiberGood {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (K : AxisCube N k)
    (z : (Fin 4 → ZMod N) × (Fin 4 → AxisCube N k)) : Prop :=
  cor146EnergyCondition B phi K z.1 ∧
    ∀ t, z.2 t ∈ cor146GoodSet B phi K (z.1 t)

private lemma cor146_replace_last {N k : Nat} (y : Point N k) (r x : ZMod N) :
    replaceCoordinate (cor146Embed y r) (Fin.last k) x = cor146Embed y x := by
  simp [cor146Embed, replaceCoordinate, Fin.update_snoc_last]

private lemma cor146_count_choices {I Y : Type*} [Fintype I] [Fintype Y]
    [DecidableEq I]
    (S : I → Finset Y) :
    countWhere (fun f : I → Y => ∀ i, f i ∈ S i) =
      ∏ i : I, (S i).card := by
  classical
  unfold countWhere
  rw [Finset.filter_congr_decidable]
  calc
    (Finset.univ.filter fun f : I → Y => ∀ i, f i ∈ S i).card =
        (Fintype.piFinset S).card := by
      apply congrArg Finset.card
      ext f
      simp [Fintype.mem_piFinset]
    _ = ∏ i : I, (S i).card := Fintype.card_piFinset S

private lemma cor146_energy_eq_fiber_count {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (K : AxisCube N k) :
    weightedSimultaneousAdditiveEnergy (cor146ReferenceSection B K)
        (cor146Theta B phi K) (cor146Sigma phi K) =
      (countWhere (cor146FiberGood B phi K) : Nat) := by
  rw [show countWhere (cor146FiberGood B phi K) =
      ∑ q, countWhere fun f => cor146FiberGood B phi K (q, f) from
    prop144_countWhere_prod fun q f => cor146FiberGood B phi K (q, f)]
  unfold weightedSimultaneousAdditiveEnergy
  push_cast
  refine Finset.sum_congr rfl fun q _ => ?_
  split_ifs with hq
  · simp [cor146FiberGood, cor146EnergyCondition, hq, cor146_count_choices, cor146Theta]
  · simp [cor146FiberGood, cor146EnergyCondition, hq]

private lemma cor146_theta_eq_zero_of_not_reference {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (K : AxisCube N k) (r : ZMod N)
    (hr : r ∉ cor146ReferenceSection B K) : cor146Theta B phi K r = 0 := by
  have hr' : ¬ K.IsIn (cor146Section B r) := by
    simpa [cor146ReferenceSection] using hr
  have hempty : cor146GoodSet B phi K r = ∅ := by
    ext K'
    simp only [cor146GoodSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, iff_false]
    exact fun hgood => hr' hgood.1
  simp [cor146Theta, hempty]

private lemma cor146_sum_theta_reference {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (K : AxisCube N k) :
    ∑ r ∈ cor146ReferenceSection B K, cor146Theta B phi K r =
      ∑ r : ZMod N, cor146Theta B phi K r := by
  apply Finset.sum_subset (Finset.subset_univ _)
  intro r _ hr
  exact cor146_theta_eq_zero_of_not_reference B phi K r hr

private lemma cor146_product_lower {N k : Nat} [NeZero N]
    (gamma : Real) (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N)
    (hproduct : HasProductProperty B phi gamma) (K : AxisCube N k) :
    gamma ^ (8 * 2 ^ k) * (N : Real) ^ 3 *
        (cor146Average B phi K) ^ 4 ≤
      ((countWhere (cor146FiberGood B phi K) : Nat) : Real) := by
  let p := Fintype.card (Fin k → Bool)
  let y : Fin p → Point N (k + 1) := fun i =>
    cor146Embed (K.vertex (cor146VertexEquiv k i)) 0
  have hmem : ∀ (i : Fin p) x, x ∈ cor146ReferenceSection B K →
      replaceCoordinate (y i) (Fin.last k) x ∈ B := by
    intro i x hx
    simp only [cor146ReferenceSection, cor146Section, AxisCube.IsIn, Finset.mem_filter,
      Finset.mem_univ, true_and] at hx
    simpa only [y, cor146_replace_last] using hx (cor146VertexEquiv k i)
  have h := hproduct p (Fin.last k) y (cor146ReferenceSection B K)
    (cor146Theta B phi K) (fun _ => by unfold cor146Theta; positivity) hmem
  have hsigma : (fun i => coordinateRestriction phi (y i) (Fin.last k)) =
      cor146Sigma phi K := by
    funext i x
    simp only [coordinateRestriction, y, cor146_replace_last, cor146Sigma]
  rw [hsigma, cor146_energy_eq_fiber_count, cor146_sum_theta_reference] at h
  have hN : (N : Real) ≠ 0 := by exact_mod_cast NeZero.ne N
  refine le_of_eq_of_le ?_ h
  rw [show p = 2 ^ k from cor146_vertex_card k, cor146Average]
  field_simp

private lemma cor146_additiveTuple_two_iff {G : Type*} [AddCommMonoid G]
    (q : Fin 4 → G) :
    IsAdditiveTuple (k := 2) q ↔ IsAdditiveQuadruple q := by
  unfold IsAdditiveTuple IsAdditiveQuadruple
  rw [show (Finset.univ.filter (fun i : Fin 4 => (i : Nat) < 2)) =
      {0, 1} by decide]
  rw [show (Finset.univ.filter (fun i : Fin 4 => 2 ≤ (i : Nat))) =
      {2, 3} by decide]
  simp

private def cor146Build {N k : Nat}
    (z : AxisCube N k ×
      ((Fin 4 → ZMod N) × (Fin 4 → AxisCube N k))) :
    GeneralArrangement N k 2 :=
  (z.1.side, fun t => (z.2.2 t).base, z.2.1)

private lemma cor146_build_cube {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (K : AxisCube N k) (q : Fin 4 → ZMod N)
    (f : Fin 4 → AxisCube N k)
    (hgood : ∀ t, f t ∈ cor146GoodSet B phi K (q t)) (t : Fin 4) :
    (cor146Build (K, q, f)).cube t = f t := by
  have ht : K.IsCongruent (f t) := by
    have htgood : cor146GoodPair B phi K (q t) (f t) := by
      simpa [cor146GoodSet] using hgood t
    exact htgood.2.2.1
  apply Prod.ext
  · rfl
  · exact ht

private lemma cor146_reference_values_additive {N k : Nat} [NeZero N]
    (phi : Point N (k + 1) → ZMod N) (K : AxisCube N k)
    (q : Fin 4 → ZMod N)
    (himage : ∀ i, IsAdditiveQuadruple
      (fun t => cor146Sigma phi K i (q t))) :
    IsAdditiveQuadruple
      (fun t => K.value (cor146SectionPhi phi (q t))) := by
  unfold IsAdditiveQuadruple AxisCube.value
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Fintype.sum_congr
  intro e
  let i := (cor146VertexEquiv k).symm e
  have hi := himage i
  have hi' :
      phi (cor146Embed (K.vertex e) (q 0)) +
          phi (cor146Embed (K.vertex e) (q 1)) =
        phi (cor146Embed (K.vertex e) (q 2)) +
          phi (cor146Embed (K.vertex e) (q 3)) := by
    simpa [IsAdditiveQuadruple, cor146Sigma, i] using hi
  unfold cor146SectionPhi
  linear_combination (-1 : ZMod N) ^ boolWeight e * hi'

private lemma cor146_build_cubeValue {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (K : AxisCube N k) (q : Fin 4 → ZMod N)
    (f : Fin 4 → AxisCube N k)
    (hgood : ∀ t, f t ∈ cor146GoodSet B phi K (q t)) (t : Fin 4) :
    (cor146Build (K, q, f)).cubeValue phi t =
      (f t).value (cor146SectionPhi phi (q t)) := by
  unfold GeneralArrangement.cubeValue AxisCube.value
  apply Fintype.sum_congr
  intro e
  congr 1
  unfold GeneralArrangement.vertex
  rw [cor146_build_cube B phi K q f hgood]
  change phi (appendCoordinate ((f t).vertex e) (q t)) =
    phi (cor146Embed ((f t).vertex e) (q t))
  rw [cor146_embed_eq_append]

private lemma cor146_build_good {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (K : AxisCube N k) (q : Fin 4 → ZMod N)
    (f : Fin 4 → AxisCube N k)
    (hsource : cor146FiberGood B phi K (q, f)) :
    (cor146Build (K, q, f)).IsIn B ∧
      (cor146Build (K, q, f)).IsRespected phi := by
  have ht (t : Fin 4) : cor146GoodPair B phi K (q t) (f t) := by
    simpa [cor146GoodSet] using hsource.2 t
  refine ⟨⟨(cor146_additiveTuple_two_iff q).2 hsource.1.2.1, fun e t => ?_⟩,
    (cor146_additiveTuple_two_iff _).2 ?_⟩
  · unfold GeneralArrangement.vertex
    rw [cor146_build_cube B phi K q f hsource.2]
    exact (by simpa [cor146Section] using (ht t).2.1 e : cor146Embed ((f t).vertex e) (q t) ∈ B)
  · have href := cor146_reference_values_additive phi K q hsource.1.2.2
    unfold IsAdditiveQuadruple at href ⊢
    simpa only [cor146_build_cubeValue B phi K q f hsource.2, fun t => ((ht t).2.2.2).symm]
      using href

private def cor146SourceGood {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (z : AxisCube N k ×
      ((Fin 4 → ZMod N) × (Fin 4 → AxisCube N k))) : Prop :=
  cor146FiberGood B phi z.1 z.2

private def cor146AugmentedBuild {N k : Nat}
    (z : AxisCube N k ×
      ((Fin 4 → ZMod N) × (Fin 4 → AxisCube N k))) :
    GeneralArrangement N k 2 × Point N k :=
  (cor146Build z, z.1.base)

private lemma cor146_augmented_injective {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    {K L : AxisCube N k} {q q' : Fin 4 → ZMod N}
    {f g : Fin 4 → AxisCube N k}
    (hf : cor146FiberGood B phi K (q, f))
    (hg : cor146FiberGood B phi L (q', g))
    (h : cor146AugmentedBuild (K, q, f) =
      cor146AugmentedBuild (L, q', g)) :
    (K, q, f) = (L, q', g) := by
  simp only [cor146AugmentedBuild, cor146Build, Prod.mk.injEq] at h
  obtain ⟨⟨hs, hb, rfl⟩, hK⟩ := h
  have hside {K : AxisCube N k} {q : Fin 4 → ZMod N} {f : Fin 4 → AxisCube N k}
      (hf : cor146FiberGood B phi K (q, f)) (t : Fin 4) : (f t).side = K.side :=
    (by simpa [cor146GoodSet] using hf.2 t : cor146GoodPair B phi K (q t) (f t)).2.2.1.symm
  exact Prod.ext (Prod.ext hK hs) (Prod.ext rfl (funext fun t =>
    Prod.ext (congrFun hb t) ((hside hf t).trans (hs.trans (hside hg t).symm))))

private lemma cor146_source_count_le {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N) :
    ∑ K : AxisCube N k, countWhere (cor146FiberGood B phi K) ≤
      respectedGeneralArrangementCount 2 B phi * N ^ k := by
  classical
  rw [← show countWhere (cor146SourceGood B phi) =
      ∑ K : AxisCube N k, countWhere (cor146FiberGood B phi K) from
    prop144_countWhere_prod
      (X := AxisCube N k)
      (Y := (Fin 4 → ZMod N) × (Fin 4 → AxisCube N k))
      (fun K z => cor146FiberGood B phi K z)]
  unfold countWhere respectedGeneralArrangementCount
  rw [Finset.filter_congr_decidable, Finset.filter_congr_decidable]
  calc
    (Finset.univ.filter (cor146SourceGood B phi)).card ≤
        ((Finset.univ.filter (fun R : GeneralArrangement N k 2 =>
          R.IsIn B ∧ R.IsRespected phi)) ×ˢ
            (Finset.univ : Finset (Point N k))).card := by
      refine Finset.card_le_card_of_injOn cor146AugmentedBuild ?_ ?_
      · intro z hz
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
          true_and, Finset.mem_product] at hz ⊢
        exact ⟨cor146_build_good B phi z.1 z.2.1 z.2.2 hz, trivial⟩
      · intro z hz w hw hzw
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
          true_and] at hz hw
        exact cor146_augmented_injective B phi hz hw hzw
    _ = (Finset.univ.filter (fun R : GeneralArrangement N k 2 =>
          R.IsIn B ∧ R.IsRespected phi)).card * N ^ k := by norm_num
    _ = respectedGeneralArrangementCount 2 B phi * N ^ k := by
      congr 1
      unfold respectedGeneralArrangementCount countWhere
      apply congrArg Finset.card
      ext R
      simp

private lemma cor146_direct_constant_identity {N k : Nat} [NeZero N]
    (beta gamma : Real) :
    (beta ^ (4 ^ (k + 1)) *
        gamma ^ (2 * k * 4 ^ (k + 1) + 8 * 2 ^ k) *
        (N : Real) ^ (5 * k + 3)) * (N : Real) ^ k =
      gamma ^ (8 * 2 ^ k) * (N : Real) ^ 3 *
        ((beta ^ (4 ^ k) * gamma ^ (2 * k * 4 ^ k)) ^ 4 *
          (N : Real) ^ (6 * k)) := by
  have hfour : 4 ^ (k + 1) = 4 ^ k * 4 := by rw [pow_succ]
  have hgamma : 2 * k * 4 ^ (k + 1) + 8 * 2 ^ k =
      (2 * k * 4 ^ k) * 4 + 8 * 2 ^ k := by ring
  have hNpow : (N : Real) ^ (5 * k + 3) * (N : Real) ^ k =
      (N : Real) ^ 3 * (N : Real) ^ (6 * k) := by ring
  rw [hgamma, hfour, pow_add, pow_mul, pow_mul, mul_pow]
  calc
    (beta ^ 4 ^ k) ^ 4 *
        ((gamma ^ (2 * k * 4 ^ k)) ^ 4 * gamma ^ (8 * 2 ^ k)) *
        (N : Real) ^ (5 * k + 3) * (N : Real) ^ k =
      ((beta ^ 4 ^ k) ^ 4 *
        ((gamma ^ (2 * k * 4 ^ k)) ^ 4 * gamma ^ (8 * 2 ^ k))) *
        ((N : Real) ^ (5 * k + 3) * (N : Real) ^ k) := by ring
    _ = ((beta ^ 4 ^ k) ^ 4 *
        ((gamma ^ (2 * k * 4 ^ k)) ^ 4 * gamma ^ (8 * 2 ^ k))) *
        ((N : Real) ^ 3 * (N : Real) ^ (6 * k)) := by rw [hNpow]
    _ = gamma ^ (8 * 2 ^ k) * (N : Real) ^ 3 *
        ((beta ^ 4 ^ k) ^ 4 * (gamma ^ (2 * k * 4 ^ k)) ^ 4 *
          (N : Real) ^ (6 * k)) := by ring

private lemma cor146_direct_lower {N k : Nat} [NeZero N]
    (beta gamma : Real) (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N)
    (_hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hproduct : HasProductProperty B phi gamma)
    (hfourth :
      (beta ^ (4 ^ k) * gamma ^ (2 * k * 4 ^ k)) ^ 4 *
          (N : Real) ^ (6 * k) ≤
        ∑ K : AxisCube N k, (cor146Average B phi K) ^ 4) :
    beta ^ (4 ^ (k + 1)) *
        gamma ^ (2 * k * 4 ^ (k + 1) + 8 * 2 ^ k) *
        (N : Real) ^ (5 * k + 3) ≤
      respectedGeneralArrangementCount 2 B phi := by
  have hN : 0 < (N : Real) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  refine le_of_mul_le_mul_right ?_ (pow_pos hN k)
  rw [cor146_direct_constant_identity beta gamma]
  calc _ ≤ ∑ K : AxisCube N k,
        gamma ^ (8 * 2 ^ k) * (N : Real) ^ 3 * (cor146Average B phi K) ^ 4 := by
        rw [← Finset.mul_sum]
        gcongr
    _ ≤ ∑ K : AxisCube N k, ((countWhere (cor146FiberGood B phi K) : Nat) : Real) :=
        Finset.sum_le_sum fun K _ => cor146_product_lower gamma B phi hproduct K
    _ ≤ _ := by exact_mod_cast cor146_source_count_le B phi

private lemma cor146_gamma_exponent_le (k : Nat) (hk : 1 ≤ k) :
    2 * k * 4 ^ (k + 1) + 8 * 2 ^ k ≤ 3 * k * 4 ^ (k + 1) := by
  by_cases hk_one : k = 1
  · subst k
    norm_num
  · have hk_two : 2 ≤ k := by omega
    have hpow : 2 ^ k ≤ 4 ^ k := Nat.pow_le_pow_left (by omega) k
    have hfirst : 8 * 2 ^ k ≤ 8 * 4 ^ k := Nat.mul_le_mul_left 8 hpow
    have hsecond : 8 * 4 ^ k ≤ (4 * k) * 4 ^ k :=
      Nat.mul_le_mul_right (4 ^ k) (by omega)
    have hextra : 8 * 2 ^ k ≤ k * 4 ^ (k + 1) := by
      calc
        8 * 2 ^ k ≤ 8 * 4 ^ k := hfirst
        _ ≤ (4 * k) * 4 ^ k := hsecond
        _ = k * 4 ^ (k + 1) := by rw [pow_succ]; ring
    calc
      2 * k * 4 ^ (k + 1) + 8 * 2 ^ k ≤
          2 * k * 4 ^ (k + 1) + k * 4 ^ (k + 1) :=
        Nat.add_le_add_left hextra _
      _ = 3 * k * 4 ^ (k + 1) := by ring

theorem corollary_14_6_holds : corollary_14_6 := by
  intro N k _ beta gamma B phi hk hbeta hgamma hgamma_one hcard hproduct
  have hfirst := cor146_pair_first_moment beta gamma B phi hk hbeta hgamma
    hgamma_one hcard hproduct
  have hfourth := cor146_average_fourth_moment beta gamma B phi hbeta hgamma hfirst
  have hdirect := cor146_direct_lower beta gamma B phi hbeta hgamma hproduct hfourth
  have hexponent := cor146_gamma_exponent_le k hk
  have hgamma_power :
      gamma ^ (3 * k * 4 ^ (k + 1)) ≤
        gamma ^ (2 * k * 4 ^ (k + 1) + 8 * 2 ^ k) :=
    pow_le_pow_of_le_one hgamma.le hgamma_one hexponent
  have hbeta_power : 0 ≤ beta ^ (4 ^ (k + 1)) := pow_nonneg hbeta.le _
  have hN_power : 0 ≤ (N : Real) ^ (5 * k + 3) := by positivity
  calc
    beta ^ (4 ^ (k + 1)) * gamma ^ (3 * k * 4 ^ (k + 1)) *
        (N : Real) ^ (5 * k + 3) ≤
      beta ^ (4 ^ (k + 1)) *
        gamma ^ (2 * k * 4 ^ (k + 1) + 8 * 2 ^ k) *
        (N : Real) ^ (5 * k + 3) := by gcongr
    _ ≤ (respectedGeneralArrangementCount 2 B phi : Real) := hdirect

end LeanProofs.GowersSzemeredi
