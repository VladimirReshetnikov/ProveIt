import GowersSzemeredi.Proofs13LargeSpectrumCover
import GowersSzemeredi.Proofs07ProgressionLinearity
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The initial progression in the bilinear extraction

This file proves the repaired Gowers's Lemma 13.4 (`lemma_13_4_holds`).  The
counterexamples to two omitted hypotheses in the printed statement are among
the declarations of `Proofs13InitialProgressionSide` listed below.

`lemma134FullContext`, `lemma134Unrepaired`, `lemma134Unrepaired_false`,
`lemma134_theta_two_q_bound`, `lemma_13_4_at_real_graph_bound`,
`lemma_13_4_fixed_real_bound`, `lemma_13_4_modulus_one_concrete_counterexample`,
`lemma_13_4_modulus_one_counterexample` and
`lemma_13_4_theta_range_counterexample` are in `Proofs13InitialProgressionSide`,
outside the final route. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-! ### Elementary parameter bounds and the zero-length branch -/

private lemma lemma134_theta_le_one {N : Nat} [NeZero N]
    (S : Section13Context N) (theta : Real)
    (hthetaBound : theta ≤ S.alpha ^ 32 / 4) : theta ≤ 1 := by
  have halphaPow : S.alpha ^ 32 ≤ 1 :=
    pow_le_one₀ S.alpha_pos.le S.alpha_at_most_one
  nlinarith

private lemma lemma134_qBound_one_le {N : Nat} [NeZero N]
    (S : Section13Context N) (theta : Real) (htheta : 0 < theta)
    (hthetaBound : theta ≤ S.alpha ^ 32 / 4) :
    1 ≤ section13QBound theta := by
  have hthetaOne := lemma134_theta_le_one S theta hthetaBound
  have hz : 1 ≤ theta ^ (-(10479 : Int)) :=
    one_le_zpow_of_nonpos₀ htheta hthetaOne (by norm_num)
  unfold section13QBound
  have htwo : (1 : Real) ≤ 2 ^ (1882 : Nat) :=
    one_le_pow₀ (by norm_num)
  calc
    (1 : Real) = 1 * 1 := by ring
    _ ≤ 2 ^ (1882 : Nat) * theta ^ (-(10479 : Int)) :=
      mul_le_mul htwo hz (by norm_num) (by positivity)

private lemma lemma134_thetaOne_pos (theta : Real) (htheta : 0 < theta) :
    0 < section13ThetaOne theta := by
  unfold section13ThetaOne
  positivity

private lemma lemma134_thetaOne_le_one {N : Nat} [NeZero N]
    (S : Section13Context N) (theta : Real) (htheta : 0 < theta)
    (hthetaBound : theta ≤ S.alpha ^ 32 / 4) :
    section13ThetaOne theta ≤ 1 := by
  have hthetaOne := lemma134_theta_le_one S theta hthetaBound
  have hpow : theta ^ 10477 ≤ 1 :=
    pow_le_one₀ htheta.le hthetaOne
  have htwo : (2 : Real) ^ (-(1882 : Int)) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num)
  unfold section13ThetaOne
  nlinarith [mul_le_mul htwo hpow (by positivity) (by positivity)]

private def lemma134Scale (N : Nat) (theta : Real) (q : Nat) : Real :=
  section13ThetaOne theta / (64 * Real.pi) *
    (N : Real) ^ (section13ThetaOne theta ^ 2 / (16 * (q : Real)))

private def lemma134EmptyProgression (N : Nat) : ModAP N where
  start := 0
  step := 1
  length := 0

/-! ### Averaging over translated progressions -/

private def lemma134Progression {N : Nat} (d s : ZMod N) (l : Nat) :
    ModAP N where
  start := s
  step := d
  length := l

private lemma lemma134_progression_proper {N l : Nat} [NeZero N]
    [Fact N.Prime] (d s : ZMod N) (hd : d ≠ 0) (hlN : l ≤ N) :
    (lemma134Progression d s l).IsProper := by
  unfold ModAP.IsProper ModAP.carrier lemma134Progression
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro i _ j _ hij
    have hmul : ((i : Nat) : ZMod N) * d = ((j : Nat) : ZMod N) * d :=
      add_left_cancel hij
    have hcast : ((i : Nat) : ZMod N) = ((j : Nat) : ZMod N) :=
      mul_right_cancel₀ hd hmul
    have hiN : (i : Nat) < N := i.isLt.trans_le hlN
    have hjN : (j : Nat) < N := j.isLt.trans_le hlN
    apply Fin.ext
    have := congrArg ZMod.val hcast
    simpa [ZMod.val_natCast_of_lt hiN, ZMod.val_natCast_of_lt hjN] using this

private def lemma134StartSet {N : Nat} (d h : ZMod N) (l : Nat) :
    Finset (ZMod N) :=
  Finset.univ.image fun j : Fin l => h - (j : Nat) * d

private lemma lemma134_startSet_card {N l : Nat} [NeZero N]
    [Fact N.Prime] (d h : ZMod N) (hd : d ≠ 0) (hlN : l ≤ N) :
    (lemma134StartSet d h l).card = l := by
  unfold lemma134StartSet
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro i _ j _ hij
    have hmul : ((i : Nat) : ZMod N) * d = ((j : Nat) : ZMod N) * d :=
      sub_right_inj.mp hij
    have hcast : ((i : Nat) : ZMod N) = ((j : Nat) : ZMod N) :=
      mul_right_cancel₀ hd hmul
    have hiN : (i : Nat) < N := i.isLt.trans_le hlN
    have hjN : (j : Nat) < N := j.isLt.trans_le hlN
    apply Fin.ext
    have := congrArg ZMod.val hcast
    simpa [ZMod.val_natCast_of_lt hiN, ZMod.val_natCast_of_lt hjN] using this

private lemma lemma134_mem_progression_iff_start {N l : Nat}
    (d s h : ZMod N) :
    h ∈ (lemma134Progression d s l).carrier ↔
      s ∈ lemma134StartSet d h l := by
  unfold lemma134Progression lemma134StartSet ModAP.carrier
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨j, ?_⟩
    ring
  · rintro ⟨j, rfl⟩
    refine ⟨j, ?_⟩
    ring

private lemma lemma134_sum_indicator_progression {N l : Nat} [NeZero N]
    [Fact N.Prime] (d h : ZMod N) (hd : d ≠ 0) (hlN : l ≤ N)
    (w : Real) :
    (∑ s : ZMod N,
      if h ∈ (lemma134Progression d s l).carrier then w else 0) =
      l * w := by
  simp_rw [lemma134_mem_progression_iff_start]
  rw [← Finset.sum_filter]
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [Finset.sum_const, nsmul_eq_mul, lemma134_startSet_card d h hd hlN]

private lemma lemma134_goodWeight_inter_sum {N l : Nat} [NeZero N]
    [Fact N.Prime] (S : Section13Context N) (G : Finset (ZMod N))
    (d : ZMod N) (hd : d ≠ 0) (hlN : l ≤ N) :
    (∑ s : ZMod N,
      (goodHeightWeight S
        ((lemma134Progression d s l).carrier ∩ G) : Real)) =
      l * goodHeightWeight S G := by
  classical
  simp only [goodHeightWeight, Nat.cast_sum, Finset.inter_comm _ G, ← Finset.filter_inter,
    ← Finset.sum_ite_mem, Nat.cast_ite, Nat.cast_zero]
  rw [Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun h _ => lemma134_sum_indicator_progression d h hd hlN _

private lemma lemma134_exists_progression_average {N l : Nat} [NeZero N]
    [Fact N.Prime] (S : Section13Context N) (G : Finset (ZMod N))
    (d : ZMod N) (hd : d ≠ 0) (hlN : l ≤ N) :
    ∃ s : ZMod N,
      (l : Real) * goodHeightWeight S G ≤
        (N : Real) * goodHeightWeight S
          ((lemma134Progression d s l).carrier ∩ G) := by
  let W : ZMod N → Real := fun s =>
    goodHeightWeight S ((lemma134Progression d s l).carrier ∩ G)
  have hsum : ∑ s : ZMod N, W s =
      (l : Real) * goodHeightWeight S G := by
    exact lemma134_goodWeight_inter_sum S G d hd hlN
  have hU : (Finset.univ : Finset (ZMod N)).Nonempty :=
    Finset.univ_nonempty
  have haverage :
      ∑ _ : ZMod N, ((l : Real) * goodHeightWeight S G) ≤
        ∑ s : ZMod N, (N : Real) * W s := by
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    rw [← Finset.mul_sum, hsum]
  obtain ⟨s, _, hs⟩ := Finset.exists_le_of_sum_le hU haverage
  exact ⟨s, hs⟩

/-! ### Finite-fibre collision estimates -/

/-- The fibre of a map, kept as a finite type rather than a finite set. -/
private abbrev lemma134Fiber {X Y : Type*} (f : X → Y) (y : Y) :=
  {x : X // f x = y}

/-- Ordered pairs on which a map takes the same value. -/
private abbrev lemma134Collision {X Y : Type*} (f : X → Y) :=
  {p : X × X // f p.1 = f p.2}

private noncomputable def lemma134CollisionSet {X Y : Type*}
    [Fintype X] (f : X → Y) : Finset (X × X) := by
  classical
  exact Finset.univ.filter fun p => f p.1 = f p.2

private def lemma134_collisionEquiv {X Y : Type*} (f : X → Y) :
    lemma134Collision f ≃
      Σ y, lemma134Fiber f y × lemma134Fiber f y where
  toFun p := ⟨f p.1.1, ⟨p.1.1, rfl⟩,
    ⟨p.1.2, p.2.symm ▸ rfl⟩⟩
  invFun z := ⟨(z.2.1.1, z.2.2.1), z.2.1.2.trans z.2.2.2.symm⟩
  left_inv p := by
    apply Subtype.ext
    rfl
  right_inv z := by
    rcases z with ⟨y, ⟨x, hx⟩, ⟨x', hx'⟩⟩
    subst y
    simp

/-- Cauchy--Schwarz in its finite-fibre form: a map into a type of size `M`
has at least `|X|²/M` ordered collisions. -/
private lemma lemma134_collision_lower {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq Y] (f : X → Y) :
    (Fintype.card X : Real) ^ 2 ≤
      Fintype.card Y * (lemma134CollisionSet f).card := by
  have hX := Fintype.card_congr (Equiv.sigmaFiberEquiv f).symm
  have hC := Fintype.card_congr (lemma134_collisionEquiv f)
  rw [Fintype.card_sigma] at hX hC
  simp only [Fintype.card_prod, ← sq] at hC
  have hset : (lemma134CollisionSet f).card = Fintype.card (lemma134Collision f) := by
    unfold lemma134CollisionSet
    rw [Finset.filter_congr_decidable]
    exact (Fintype.card_subtype fun p : X × X => f p.1 = f p.2).symm
  -- Cauchy--Schwarz over the fibres, in `ℕ`
  have key : Fintype.card X ^ 2 ≤ Fintype.card Y * (lemma134CollisionSet f).card := by
    rw [hset, hC, hX]
    exact sq_sum_le_card_mul_sum_sq
  exact_mod_cast key

/-! We apply the collision bound three times to vertical edges.  The nested
types below are respectively pairs, quadruples, and octuples of edges of one
common height. -/

private abbrev lemma134Edge {N : Nat} [NeZero N]
    (A : Finset (Pair N)) :=
  {e : Pair N × ZMod N //
    e.1 ∈ A ∧ (e.1.1, e.1.2 + e.2) ∈ A}

private def lemma134Edge.height {N : Nat} [NeZero N]
    {A : Finset (Pair N)} (e : lemma134Edge A) : ZMod N := e.1.2

private def lemma134Edge.x {N : Nat} [NeZero N]
    {A : Finset (Pair N)} (e : lemma134Edge A) : ZMod N := e.1.1.1

private def lemma134Edge.y {N : Nat} [NeZero N]
    {A : Finset (Pair N)} (e : lemma134Edge A) : ZMod N := e.1.1.2

private abbrev lemma134EdgeTwo {N : Nat} [NeZero N]
    (A : Finset (Pair N)) :=
  ↥(lemma134CollisionSet (lemma134Edge.height (A := A)))

private def lemma134EdgeTwo.height {N : Nat} [NeZero N]
    {A : Finset (Pair N)} (e : lemma134EdgeTwo A) : ZMod N :=
  e.1.1.height

private abbrev lemma134EdgeFour {N : Nat} [NeZero N]
    (A : Finset (Pair N)) :=
  ↥(lemma134CollisionSet (lemma134EdgeTwo.height (A := A)))

private def lemma134EdgeFour.height {N : Nat} [NeZero N]
    {A : Finset (Pair N)} (e : lemma134EdgeFour A) : ZMod N :=
  e.1.1.height

private abbrev lemma134EdgeEight {N : Nat} [NeZero N]
    (A : Finset (Pair N)) :=
  ↥(lemma134CollisionSet (lemma134EdgeFour.height (A := A)))

private def lemma134_edgePairEquiv {N : Nat} [NeZero N]
    (A : Finset (Pair N)) :
    ↥(lemma134CollisionSet (fun z : A => z.1.1)) ≃ lemma134Edge A where
  toFun p := by
    have hp : p.1.1.1.1 = p.1.2.1.1 := by
      simpa [lemma134CollisionSet] using p.2
    let z := p.1.1.1
    let z' := p.1.2.1
    refine ⟨(z, z'.2 - z.2), p.1.1.2, ?_⟩
    convert p.1.2.2 using 1
    apply Prod.ext
    · exact hp
    · simp only [z, z']
      abel
  invFun e :=
    ⟨(⟨e.1.1, e.2.1⟩, ⟨(e.x, e.y + e.height), e.2.2⟩), by
      simp [lemma134CollisionSet, lemma134Edge.x]⟩
  left_inv p := by
    have hp : p.1.1.1.1 = p.1.2.1.1 := by
      simpa [lemma134CollisionSet] using p.2
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext
    · rfl
    · apply Prod.ext
      · exact hp
      · simp [lemma134Edge.y, lemma134Edge.height]
  right_inv e := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · simp [lemma134Edge.y, lemma134Edge.height]

private lemma lemma134_edge_card_lower {N : Nat} [NeZero N]
    (A : Finset (Pair N)) :
    (A.card : Real) ^ 2 ≤ N * Fintype.card (lemma134Edge A) := by
  have h := lemma134_collision_lower (fun z : A => z.1.1)
  have hcard := Fintype.card_congr (lemma134_edgePairEquiv A)
  simp only [Fintype.card_coe] at hcard
  rw [hcard] at h
  simpa only [Fintype.card_coe, ZMod.card] using h

private lemma lemma134_edge_eight_lower {N : Nat} [NeZero N]
    (A : Finset (Pair N)) :
    (Fintype.card (lemma134Edge A) : Real) ^ 8 ≤
      (N : Real) ^ 7 * Fintype.card (lemma134EdgeEight A) := by
  have h₂ := lemma134_collision_lower (lemma134Edge.height (A := A))
  have h₄ := lemma134_collision_lower (lemma134EdgeTwo.height (A := A))
  have h₈ := lemma134_collision_lower (lemma134EdgeFour.height (A := A))
  simp only [Fintype.card_coe, ZMod.card] at h₂ h₄ h₈ ⊢
  -- `e ^ 4 ≤ N ^ 3 * e₄`, then square once more and apply `h₈`
  have h₄' : (Fintype.card (lemma134Edge A) : Real) ^ 4 ≤
      N ^ 3 * (lemma134CollisionSet (lemma134EdgeTwo.height (A := A))).card := by
    linarith [pow_le_pow_left₀ (by positivity) h₂ 2,
      mul_le_mul_of_nonneg_left h₄ (sq_nonneg (N : Real))]
  linarith [pow_le_pow_left₀ (by positivity) h₄' 2,
    mul_le_mul_of_nonneg_left h₈ (pow_nonneg (Nat.cast_nonneg N : (0 : Real) ≤ N) 6)]

private def lemma134EdgeTwo.get {N : Nat} [NeZero N]
    {A : Finset (Pair N)} (e : lemma134EdgeTwo A) :
    Fin 2 → lemma134Edge A :=
  ![e.1.1, e.1.2]

private lemma lemma134EdgeTwo.get_height {N : Nat} [NeZero N]
    {A : Finset (Pair N)} (e : lemma134EdgeTwo A) (i : Fin 2) :
    (e.get i).height = e.height := by
  have heq : e.1.1.height = e.1.2.height := by
    have he := e.2
    simp only [lemma134CollisionSet, Finset.mem_filter, Finset.mem_univ,
      true_and] at he
    exact he
  fin_cases i <;> simp [lemma134EdgeTwo.get, lemma134EdgeTwo.height, heq]

private def lemma134EdgeFour.get {N : Nat} [NeZero N]
    {A : Finset (Pair N)} (e : lemma134EdgeFour A) :
    Fin 4 → lemma134Edge A :=
  ![e.1.1.get 0, e.1.1.get 1, e.1.2.get 0, e.1.2.get 1]

private lemma lemma134EdgeFour.get_height {N : Nat} [NeZero N]
    {A : Finset (Pair N)} (e : lemma134EdgeFour A) (i : Fin 4) :
    (e.get i).height = e.height := by
  have heq : e.1.1.height = e.1.2.height := by
    have he := e.2
    simp only [lemma134CollisionSet, Finset.mem_filter, Finset.mem_univ,
      true_and] at he
    exact he
  fin_cases i <;>
    simp [lemma134EdgeFour.get, lemma134EdgeFour.height,
      lemma134EdgeTwo.get_height, heq]

private def lemma134EdgeEight.height {N : Nat} [NeZero N]
    {A : Finset (Pair N)} (e : lemma134EdgeEight A) : ZMod N :=
  e.1.1.height

private def lemma134EdgeEight.get {N : Nat} [NeZero N]
    {A : Finset (Pair N)} (e : lemma134EdgeEight A) :
    Fin 8 → lemma134Edge A :=
  ![e.1.1.get 0, e.1.1.get 1, e.1.1.get 2, e.1.1.get 3,
    e.1.2.get 0, e.1.2.get 1, e.1.2.get 2, e.1.2.get 3]

private lemma lemma134EdgeEight.get_height {N : Nat} [NeZero N]
    {A : Finset (Pair N)} (e : lemma134EdgeEight A) (i : Fin 8) :
    (e.get i).height = e.height := by
  have heq : e.1.1.height = e.1.2.height := by
    have he := e.2
    simp only [lemma134CollisionSet, Finset.mem_filter, Finset.mem_univ,
      true_and] at he
    exact he
  fin_cases i <;>
    simp [lemma134EdgeEight.get, lemma134EdgeEight.height,
      lemma134EdgeFour.get_height, heq]

private lemma lemma134EdgeEight.get_injective {N : Nat} [NeZero N]
    {A : Finset (Pair N)} :
    Function.Injective (lemma134EdgeEight.get (A := A)) := by
  intro e e' h
  -- the eight entries of `get` are the eight leaves of the nested pairs
  have h' := congrFun h
  exact Subtype.ext (Prod.ext
    (Subtype.ext (Prod.ext (Subtype.ext (Prod.ext (h' 0) (h' 1)))
      (Subtype.ext (Prod.ext (h' 2) (h' 3)))))
    (Subtype.ext (Prod.ext (Subtype.ext (Prod.ext (h' 4) (h' 5)))
      (Subtype.ext (Prod.ext (h' 6) (h' 7))))))

private def lemma134EdgeEight.key {N : Nat} [NeZero N]
    {A : Finset (Pair N)} (e : lemma134EdgeEight A) :
    ZMod N × ZMod N :=
  (e.height, ∑ i, (e.get i).x)

private abbrev lemma134ArrangementCollision {N : Nat} [NeZero N]
    (A : Finset (Pair N)) :=
  ↥(lemma134CollisionSet (lemma134EdgeEight.key (A := A)))

private lemma lemma134_arrangement_collision_lower {N : Nat} [NeZero N]
    (A : Finset (Pair N)) :
    (Fintype.card (lemma134EdgeEight A) : Real) ^ 2 ≤
      (N : Real) ^ 2 * Fintype.card (lemma134ArrangementCollision A) := by
  simpa only [Fintype.card_prod, Fintype.card_coe, ZMod.card,
    Nat.cast_mul, Nat.cast_pow, pow_two] using
    lemma134_collision_lower (lemma134EdgeEight.key (A := A))

private def lemma134EdgeSixteenGet {N : Nat} [NeZero N]
    {A : Finset (Pair N)}
    (p : lemma134EdgeEight A × lemma134EdgeEight A) :
    Fin 16 → lemma134Edge A :=
  fun i => @Fin.addCases 8 8 (fun _ => lemma134Edge A)
    p.1.get p.2.get i

@[simp] private lemma lemma134EdgeSixteenGet_castAdd {N : Nat} [NeZero N]
    {A : Finset (Pair N)}
    (p : lemma134EdgeEight A × lemma134EdgeEight A) (i : Fin 8) :
    lemma134EdgeSixteenGet p (Fin.castAdd 8 i) = p.1.get i := by
  unfold lemma134EdgeSixteenGet
  exact Fin.addCases_left i

@[simp] private lemma lemma134EdgeSixteenGet_natAdd {N : Nat} [NeZero N]
    {A : Finset (Pair N)}
    (p : lemma134EdgeEight A × lemma134EdgeEight A) (i : Fin 8) :
    lemma134EdgeSixteenGet p (Fin.natAdd 8 i) = p.2.get i := by
  unfold lemma134EdgeSixteenGet
  exact Fin.addCases_right i

private lemma lemma134_arrangementCollision_key_eq {N : Nat} [NeZero N]
    {A : Finset (Pair N)} (p : lemma134ArrangementCollision A) :
    p.1.1.key = p.1.2.key := by
  have hp := p.2
  simp only [lemma134CollisionSet, Finset.mem_filter, Finset.mem_univ,
    true_and] at hp
  exact hp

private lemma lemma134EdgeSixteenGet_height {N : Nat} [NeZero N]
    {A : Finset (Pair N)} (p : lemma134ArrangementCollision A)
    (i : Fin 16) :
    (lemma134EdgeSixteenGet p.1 i).height = p.1.1.height := by
  have hh : p.1.1.height = p.1.2.height :=
    congrArg Prod.fst (lemma134_arrangementCollision_key_eq p)
  by_cases hi : (i : Nat) < 8
  · let j : Fin 8 := ⟨i, hi⟩
    have hij : i = Fin.castAdd 8 j := by apply Fin.ext; rfl
    rw [hij, lemma134EdgeSixteenGet_castAdd, p.1.1.get_height]
  · have _ : 8 ≤ (i : Nat) := by omega
    let j : Fin 8 := ⟨(i : Nat) - 8, by omega⟩
    have hij : i = Fin.natAdd 8 j := by
      apply Fin.ext
      simp [j]
      omega
    rw [hij, lemma134EdgeSixteenGet_natAdd, p.1.2.get_height]
    exact hh.symm

private lemma lemma134_left_indices :
    (Finset.univ.filter (fun i : Fin 16 => (i : Nat) < 8)) =
      Finset.univ.map (Fin.castAddEmb (n := 8) 8) := by
  decide

private lemma lemma134_right_indices :
    (Finset.univ.filter (fun i : Fin 16 => 8 ≤ (i : Nat))) =
      Finset.univ.map (Fin.natAddEmb (m := 8) 8) := by
  decide

private def lemma134CollisionArrangement {N : Nat} [NeZero N]
    {A : Finset (Pair N)} (p : lemma134ArrangementCollision A) :
    DArrangement N 8 :=
  (fun i => (lemma134EdgeSixteenGet p.1 i).x,
    fun i => (lemma134EdgeSixteenGet p.1 i).y,
    p.1.1.height)

private lemma lemma134CollisionArrangement_isIn {N : Nat} [NeZero N]
    {A : Finset (Pair N)} (p : lemma134ArrangementCollision A) :
    (lemma134CollisionArrangement p).IsIn A := by
  constructor
  · unfold IsAdditiveTuple
    rw [lemma134_left_indices, lemma134_right_indices]
    simp only [Finset.sum_map]
    have hsum := congrArg Prod.snd (lemma134_arrangementCollision_key_eq p)
    change (∑ i : Fin 8, (p.1.1.get i).x) =
      ∑ i : Fin 8, (p.1.2.get i).x
    simpa [lemma134EdgeEight.key] using hsum
  · intro i
    let e := lemma134EdgeSixteenGet p.1 i
    have heheight : e.height = p.1.1.height :=
      lemma134EdgeSixteenGet_height p i
    constructor
    · change (e.x, e.y) ∈ A
      exact e.2.1
    · change (e.x, e.y + p.1.1.height) ∈ A
      rw [← heheight]
      exact e.2.2

private def lemma134ToArrangement {N : Nat} [NeZero N]
    (A : Finset (Pair N)) (p : lemma134ArrangementCollision A) :
    {R : DArrangement N 8 // R.IsIn A} :=
  ⟨lemma134CollisionArrangement p, lemma134CollisionArrangement_isIn p⟩

private lemma lemma134ToArrangement_injective {N : Nat} [NeZero N]
    (A : Finset (Pair N)) : Function.Injective (lemma134ToArrangement A) := by
  intro p q hpq
  have hR : lemma134CollisionArrangement p = lemma134CollisionArrangement q :=
    congrArg Subtype.val hpq
  have hh : p.1.1.height = q.1.1.height := congrArg DArrangement.height hR
  -- the sixteen edges of `p` and of `q` coincide
  have hget (j : Fin 16) : lemma134EdgeSixteenGet p.1 j = lemma134EdgeSixteenGet q.1 j :=
    Subtype.ext (Prod.ext (Prod.ext (congrFun (congrArg DArrangement.x hR) j)
      (congrFun (congrArg DArrangement.y hR) j))
      ((lemma134EdgeSixteenGet_height p j).trans
        (hh.trans (lemma134EdgeSixteenGet_height q j).symm)))
  apply Subtype.ext
  apply Prod.ext <;> apply lemma134EdgeEight.get_injective <;> funext i
  · simpa only [lemma134EdgeSixteenGet_castAdd] using hget (Fin.castAdd 8 i)
  · simpa only [lemma134EdgeSixteenGet_natAdd] using hget (Fin.natAdd 8 i)

private lemma lemma134_arrangement_collision_card_le {N : Nat} [NeZero N]
    (A : Finset (Pair N)) :
    Fintype.card (lemma134ArrangementCollision A) ≤ arrangementCount 8 A := by
  classical
  have hinj := Fintype.card_le_of_injective (lemma134ToArrangement A)
    (lemma134ToArrangement_injective A)
  unfold arrangementCount countWhere
  rw [Finset.filter_congr_decidable]
  rw [← Fintype.card_subtype]
  exact hinj

/-- The unweighted `2d`-tuple density estimate specialized to the vertical
8-arrangements used in Section 13. -/
private lemma lemma134_arrangement_count_lower_card {N : Nat} [NeZero N]
    (A : Finset (Pair N)) :
    (A.card : Real) ^ 32 ≤
      (N : Real) ^ 32 * arrangementCount 8 A := by
  have hN : (0 : Real) ≤ N := Nat.cast_nonneg N
  have hcount : (Fintype.card (lemma134ArrangementCollision A) : Real) ≤
      arrangementCount 8 A := by
    exact_mod_cast lemma134_arrangement_collision_card_le A
  -- `|A| ^ 32 ≤ N ^ 16 e ^ 16 ≤ N ^ 30 e₈ ^ 2 ≤ N ^ 32 c ≤ N ^ 32 * count`
  linarith [pow_le_pow_left₀ (by positivity) (lemma134_edge_card_lower A) 16,
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (lemma134_edge_eight_lower A) 2)
      (pow_nonneg hN 16),
    mul_le_mul_of_nonneg_left (lemma134_arrangement_collision_lower A) (pow_nonneg hN 30),
    mul_le_mul_of_nonneg_left hcount (pow_nonneg hN 32)]

private lemma lemma134_arrangement_count_lower {N : Nat} [NeZero N]
    (S : Section13Context N) :
    S.alpha ^ 32 * (N : Real) ^ 32 ≤ arrangementCount 8 S.A := by
  have hraw := lemma134_arrangement_count_lower_card S.A
  rw [S.card_A] at hraw
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hNpow : 0 < (N : Real) ^ 32 := pow_pos hN 32
  have hcancel : (N : Real) ^ 32 *
      (S.alpha ^ 32 * (N : Real) ^ 32) ≤
      (N : Real) ^ 32 * arrangementCount 8 S.A := by linarith
  exact le_of_mul_le_mul_left hcancel hNpow

/-! ### Good heights carry a positive fraction of the arrangements -/

private lemma lemma134_sectionC_total {N : Nat} [NeZero N]
    (S : Section13Context N) :
    ∑ h : ZMod N, section13C S h = arrangementCount 8 S.A := by
  classical
  let T : Finset (DArrangement N 8) :=
    Finset.univ.filter fun R => R.IsIn S.A
  have hmap : Set.MapsTo DArrangement.height (T : Set (DArrangement N 8))
      (Finset.univ : Finset (ZMod N)) := by norm_num
  have hfiber := Finset.card_eq_sum_card_fiberwise hmap
  have hheight (h : ZMod N) : section13C S h =
      (T.filter fun R => R.height = h).card := by
    unfold section13C arrangementCountAtHeight countWhere
    rw [Finset.filter_congr_decidable]
    apply congrArg Finset.card
    ext R
    simp [T]
  have htotal : T.card = arrangementCount 8 S.A := rfl
  calc
    (∑ h : ZMod N, section13C S h) =
        ∑ h : ZMod N, (T.filter fun R => R.height = h).card := by
      apply Finset.sum_congr rfl
      intro h _
      exact hheight h
    _ = T.card := by simpa using hfiber.symm
    _ = arrangementCount 8 S.A := htotal

private lemma lemma134_sectionG_total {N : Nat} [NeZero N]
    (S : Section13Context N) :
    ∑ h : ZMod N, section13G S h =
      respectedArrangementCount 8 S.A S.phi := by
  classical
  let T : Finset (DArrangement N 8) :=
    Finset.univ.filter fun R => R.IsIn S.A ∧ R.IsRespected S.phi
  have hmap : Set.MapsTo DArrangement.height (T : Set (DArrangement N 8))
      (Finset.univ : Finset (ZMod N)) := by norm_num
  have hfiber := Finset.card_eq_sum_card_fiberwise hmap
  have hheight (h : ZMod N) : section13G S h =
      (T.filter fun R => R.height = h).card := by
    unfold section13G respectedArrangementCountAtHeight countWhere
    rw [Finset.filter_congr_decidable]
    apply congrArg Finset.card
    ext R
    simp [T]
    tauto
  have htotal : T.card = respectedArrangementCount 8 S.A S.phi := by
    unfold respectedArrangementCount countWhere
    rw [Finset.filter_congr_decidable]
  calc
    (∑ h : ZMod N, section13G S h) =
        ∑ h : ZMod N, (T.filter fun R => R.height = h).card := by
      apply Finset.sum_congr rfl
      intro h _
      exact hheight h
    _ = T.card := by simpa using hfiber.symm
    _ = respectedArrangementCount 8 S.A S.phi := htotal

private lemma lemma134_sectionG_le_C {N : Nat} [NeZero N]
    (S : Section13Context N) (h : ZMod N) :
    section13G S h ≤ section13C S h := by
  unfold section13G section13C respectedArrangementCountAtHeight
    arrangementCountAtHeight countWhere
  exact Finset.card_le_card (by
    intro R
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto)

private abbrev lemma134AtHeightCode (N : Nat) :=
  (Fin 15 → ZMod N) × (Fin 16 → ZMod N)

private def lemma134EncodeAtHeight {N : Nat} [NeZero N]
    (A : Finset (Pair N)) (h : ZMod N)
    (R : {R : DArrangement N 8 // R.IsIn A ∧ R.height = h}) :
    lemma134AtHeightCode N :=
  (fun i => R.1.x i.succ, R.1.y)

private lemma lemma134EncodeAtHeight_injective {N : Nat} [NeZero N]
    (A : Finset (Pair N)) (h : ZMod N) :
    Function.Injective (lemma134EncodeAtHeight A h) := by
  intro R T hcode
  apply Subtype.ext
  have hxTail : ∀ i : Fin 15, R.1.x i.succ = T.1.x i.succ := by
    exact fun i => congrFun (congrArg Prod.fst hcode) i
  have hx : R.1.x = T.1.x :=
    lemma134_additive_ext R.2.1.1 T.2.1.1 hxTail
  have hy : R.1.y = T.1.y := congrArg Prod.snd hcode
  have hh : R.1.height = T.1.height := R.2.2.trans T.2.2.symm
  exact Prod.ext hx (Prod.ext hy hh)

lemma lemma134_sectionC_upper {N : Nat} [NeZero N]
    (S : Section13Context N) (h : ZMod N) :
    section13C S h ≤ N ^ 31 := by
  classical
  unfold section13C arrangementCountAtHeight countWhere
  rw [Finset.filter_congr_decidable]
  rw [← Fintype.card_subtype]
  calc
    Fintype.card {R : DArrangement N 8 //
        R.IsIn S.A ∧ R.height = h} ≤
        Fintype.card (lemma134AtHeightCode N) :=
      Fintype.card_le_of_injective (lemma134EncodeAtHeight S.A h)
        (lemma134EncodeAtHeight_injective S.A h)
    _ = N ^ 31 := by
      simp [lemma134AtHeightCode]
      ring

private lemma lemma134_good_univ_lower {N : Nat} [NeZero N]
    (S : Section13Context N) :
    (arrangementCount 8 S.A : Real) / 2 ≤
      goodHeightWeight S Finset.univ := by
  classical
  have heta : 0 < S.eta := by rw [S.eta_value]; positivity
  have hm : (1 - S.eta) * arrangementCount 8 S.A ≤ respectedArrangementCount 8 S.A S.phi :=
    S.mostly_respected
  have hC : ∑ h : ZMod N, (section13C S h : Real) = arrangementCount 8 S.A := by
    exact_mod_cast lemma134_sectionC_total S
  have hG : ∑ h : ZMod N, (section13G S h : Real) = respectedArrangementCount 8 S.A S.phi := by
    exact_mod_cast lemma134_sectionG_total S
  have hW : (goodHeightWeight S Finset.univ : Real) =
      ∑ h, if IsGoodHeight S h then (section13C S h : Real) else 0 := by
    simp [goodHeightWeight, Finset.sum_filter]
  -- a bad height loses at least a `2 * eta` fraction of its arrangements
  have hper (h : ZMod N) : 2 * S.eta * section13C S h ≤
      2 * S.eta * (if IsGoodHeight S h then (section13C S h : Real) else 0) +
        (section13C S h - section13G S h) := by
    have hGC : (section13G S h : Real) ≤ section13C S h := by
      exact_mod_cast lemma134_sectionG_le_C S h
    split_ifs with hgood
    · linarith
    · linarith [not_le.mp hgood]
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun h _ => hper h
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hC, hG] at hsum
  rw [hW]
  refine le_of_mul_le_mul_left ?_ heta
  linarith

private lemma lemma134_good_exceptional_lower {N : Nat} [NeZero N]
    (S : Section13Context N) (theta : Real) (G : Finset (ZMod N))
    (_htheta : 0 < theta) (hthetaBound : theta ≤ S.alpha ^ 32 / 4)
    (hGcard : (1 - theta) * N ≤ G.card) :
    S.alpha ^ 32 * (N : Real) ^ 32 / 4 ≤ goodHeightWeight S G := by
  classical
  let g : ZMod N → Real := fun h => if IsGoodHeight S h then (section13C S h : Real) else 0
  have hW (H : Finset (ZMod N)) : (goodHeightWeight S H : Real) = ∑ h ∈ H, g h := by
    simp [g, goodHeightWeight, Finset.sum_filter]
  -- the at most `theta * N` heights outside `G` carry at most `theta * N ^ 32`
  have hE : ∑ h ∈ Finset.univ \ G, g h ≤ ((Finset.univ \ G).card : Real) * N ^ 31 := by
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun h _ => ?_
    simp only [g]
    split_ifs
    · exact_mod_cast lemma134_sectionC_upper S h
    · positivity
  have hcard : ((Finset.univ \ G).card : Real) + G.card = N := by
    exact_mod_cast (Finset.card_sdiff_add_card_eq_card (Finset.subset_univ G)).trans (ZMod.card N)
  have huniv := lemma134_good_univ_lower S
  rw [hW, ← Finset.sum_sdiff (Finset.subset_univ G)] at huniv
  rw [hW]
  linarith [lemma134_arrangement_count_lower S,
    mul_le_mul_of_nonneg_right (show ((Finset.univ \ G).card : Real) ≤ theta * N by linarith)
      (by positivity : (0 : Real) ≤ (N : Real) ^ 31),
    mul_le_mul_of_nonneg_right hthetaBound (by positivity : (0 : Real) ≤ (N : Real) ^ 32)]

/-! ### The progression length and affine restrictions -/

private lemma lemma134_scale_le_modulus {N q : Nat} [NeZero N]
    (theta : Real) (htheta : 0 < theta)
    (htheta₁One : section13ThetaOne theta ≤ 1) (hq : 0 < q) :
    lemma134Scale N theta q ≤ N := by
  have htheta₁ := lemma134_thetaOne_pos theta htheta
  have hq₁ : (1 : Real) ≤ q := by exact_mod_cast hq
  have hsq := pow_le_one₀ (n := 2) htheta₁.le htheta₁One
  unfold lemma134Scale
  -- the coefficient and the exponent are both at most one
  calc _ ≤ 1 * (N : Real) ^ (1 : Real) :=
        mul_le_mul ((div_le_one₀ (by positivity)).mpr (by linarith [Real.pi_gt_three]))
          (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast NeZero.pos N)
            ((div_le_one₀ (by positivity)).mpr (by linarith))) (by positivity) zero_le_one
    _ = N := by rw [one_mul, Real.rpow_one]

private lemma lemma134_progression_difference {N l : Nat}
    (d s x y : ZMod N)
    (hx : x ∈ (lemma134Progression d s l).carrier)
    (hy : y ∈ (lemma134Progression d s l).carrier) :
    x - y ∈ symmetricMultiples d l := by
  unfold lemma134Progression ModAP.carrier at hx hy
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx hy
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hy
  unfold symmetricMultiples
  rw [Finset.mem_image]
  let z : Int := (i : Nat) - (j : Nat)
  refine ⟨z, Finset.mem_Icc.mpr ?_, ?_⟩
  · dsimp only [z]
    constructor <;> omega
  · dsimp only [z]
    push_cast
    ring

private def lemma134Density {N : Nat} (B : Finset (ZMod N)) : Real :=
  (B.card : Real) / N

private def lemma134SpectrumUnion {N q₀ : Nat} [NeZero N]
    (B : Fin q₀ → Finset (ZMod N)) : Finset (ZMod N) :=
  Finset.univ.biUnion fun i => section7Spectrum (B i) (lemma134Density (B i))

private lemma lemma134_density_card {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) :
    (B.card : Real) = lemma134Density B * N := by
  unfold lemma134Density
  exact (div_mul_cancel₀ (B.card : Real)
    (by exact_mod_cast NeZero.ne N : (N : Real) ≠ 0)).symm

private lemma lemma134_density_lower {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (theta₁ : Real) (_htheta₁ : 0 < theta₁)
    (hB : theta₁ * N ≤ (B.card : Real)) :
    theta₁ ≤ lemma134Density B := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  unfold lemma134Density
  exact (le_div_iff₀ hN).2 hB

private lemma lemma134_individual_bohr {N q₀ l : Nat} [NeZero N]
    (B : Fin q₀ → Finset (ZMod N)) (theta₁ : Real)
    (htheta₁ : 0 < theta₁) (hl : 0 < l)
    (hBlarge : ∀ i, theta₁ * N ≤ (B i).card)
    (d : ZMod N)
    (hd : d ∈ bohr (lemma134SpectrumUnion B)
      (theta₁ / (32 * Real.pi * l))) (i : Fin q₀) :
    d ∈ bohr (section7Spectrum (B i) (lemma134Density (B i)))
      (lemma134Density (B i) / (32 * Real.pi * l)) := by
  have hbeta := lemma134_density_lower (B i) theta₁ htheta₁ (hBlarge i)
  rw [bohr, Finset.mem_filter] at hd ⊢
  refine ⟨hd.1, fun r hr =>
    (hd.2 r (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hr⟩)).trans ?_⟩
  gcongr

private lemma lemma134_piece_affine_on_progression
    {N q₀ l : Nat} [NeZero N]
    (B : Fin q₀ → Finset (ZMod N))
    (sigma : Fin q₀ → ZMod N → ZMod N)
    (theta₁ : Real) (hprime : Nat.Prime N) (htheta₁ : 0 < theta₁)
    (hl : 0 < l) (hBlarge : ∀ i, theta₁ * N ≤ (B i).card)
    (hFreiman : ∀ i, FreimanHom 8 (B i) (sigma i))
    (d s : ZMod N)
    (hd : d ∈ bohr (lemma134SpectrumUnion B)
      (theta₁ / (32 * Real.pi * l))) :
    ∀ i : Fin q₀, ∃ a b : ZMod N,
      ∀ h, h ∈ B i ∩ (lemma134Progression d s l).carrier →
        sigma i h = a * h + b := by
  intro i
  have hbeta := lemma134_density_lower (B i) theta₁ htheta₁ (hBlarge i)
  obtain ⟨c, hc⟩ := corollary_7_9_holds N (B i) (sigma i) _ hprime (htheta₁.trans_le hbeta)
    (lemma134_density_card (B i)) (hFreiman i) l hl d
    (lemma134_individual_bohr B theta₁ htheta₁ hl hBlarge d hd i)
  by_cases hne : (B i ∩ (lemma134Progression d s l).carrier).Nonempty
  · obtain ⟨y, hy⟩ := hne
    refine ⟨c, sigma i y - c * y, fun x hx => ?_⟩
    rw [Finset.mem_inter] at hx hy
    linear_combination hc x hx.1 y hy.1 (lemma134_progression_difference d s x y hx.2 hy.2)
  · exact ⟨0, 0, fun h hh => (hne ⟨h, hh⟩).elim⟩

/-! ### A common Bohr step for the Freiman cover -/

private lemma lemma134_spectrum_union_card
    {N q₀ q : Nat} [NeZero N]
    (B : Fin q₀ → Finset (ZMod N))
    (sigma : Fin q₀ → ZMod N → ZMod N)
    (theta₁ : Real) (htheta₁ : 0 < theta₁)
    (hq : q₀ ≤ q)
    (hBlarge : ∀ i, theta₁ * N ≤ (B i).card)
    (hFreiman : ∀ i, FreimanHom 8 (B i) (sigma i)) :
    ((lemma134SpectrumUnion B).card : Real) ≤
      16 * q * theta₁ ^ (-(2 : Real)) := by
  calc ((lemma134SpectrumUnion B).card : Real)
      ≤ ∑ i : Fin q₀, ((section7Spectrum (B i) (lemma134Density (B i))).card : Real) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin q₀, 16 * theta₁ ^ (-(2 : Real)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hbeta := lemma134_density_lower (B i) theta₁ htheta₁ (hBlarge i)
        exact (lemma_7_8_holds N (B i) (sigma i) _ (htheta₁.trans_le hbeta)
          (lemma134_density_card (B i)) (hFreiman i)).1.trans (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos htheta₁ hbeta (by norm_num)) (by norm_num))
    _ = 16 * q₀ * theta₁ ^ (-(2 : Real)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    _ ≤ 16 * q * theta₁ ^ (-(2 : Real)) := by gcongr

private lemma lemma134_exists_common_step
    {N q₀ q l : Nat} [NeZero N] [Fact N.Prime]
    (B : Fin q₀ → Finset (ZMod N))
    (sigma : Fin q₀ → ZMod N → ZMod N)
    (theta : Real) (htheta : 0 < theta)
    (htheta₁One : section13ThetaOne theta ≤ 1)
    (hq : 0 < q) (hq₀q : q₀ ≤ q)
    (hl : 0 < l)
    (hlScale : (l : Real) < lemma134Scale N theta q)
    (hBlarge : ∀ i,
      section13ThetaOne theta * N ≤ (B i).card)
    (hFreiman : ∀ i, FreimanHom 8 (B i) (sigma i)) :
    ∃ d : ZMod N,
      d ∈ bohr (lemma134SpectrumUnion B)
        (section13ThetaOne theta / (32 * Real.pi * l)) ∧
      d ≠ 0 := by
  let theta₁ := section13ThetaOne theta
  let K := lemma134SpectrumUnion B
  let exponent : Real := theta₁ ^ 2 / (16 * (q : Real))
  let delta : Real := theta₁ / (32 * Real.pi * (l : Real))
  have htheta₁ : 0 < theta₁ := lemma134_thetaOne_pos theta htheta
  have hdelta : 0 < delta := by positivity
  have hdeltaOne : delta ≤ 1 := by
    have hlOne : (1 : Real) ≤ l := by exact_mod_cast hl
    rw [div_le_one₀ (by positivity)]
    nlinarith [Real.pi_gt_three]
  by_cases hKempty : K = ∅
  · exact ⟨1, by simp [K, hKempty, bohr], one_ne_zero⟩
  have hKne : K.Nonempty := Finset.nonempty_iff_ne_empty.mpr hKempty
  have hKpos : (0 : Real) < K.card := by exact_mod_cast Finset.card_pos.mpr hKne
  have hKcard := lemma134_spectrum_union_card B sigma theta₁ htheta₁ hq₀q hBlarge hFreiman
  rw [Real.rpow_neg htheta₁.le, Real.rpow_two, ← div_eq_mul_inv,
    le_div_iff₀ (by positivity)] at hKcard
  -- `|K| ≤ 16 q / θ₁²` gives `exponent ≤ 1 / |K|`, and `l < scale` gives `2 N ^ (-exponent) < δ`
  have hexponentCard : exponent ≤ 1 / (K.card : Real) := by
    rw [div_le_div_iff₀ (by positivity) hKpos]
    linarith
  have hX : (0 : Real) < (N : Real) ^ exponent :=
    Real.rpow_pos_of_pos (by exact_mod_cast NeZero.pos N) _
  have hlX : l * (64 * Real.pi) < theta₁ * (N : Real) ^ exponent := by
    rw [← lt_div_iff₀ (by positivity), mul_div_right_comm]
    exact hlScale
  have hmono : (N : Real) ^ (-(1 / (K.card : Real))) ≤ ((N : Real) ^ exponent)⁻¹ := by
    rw [← Real.rpow_neg (Nat.cast_nonneg N)]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (Fact.out : N.Prime).one_le)
      (neg_le_neg hexponentCard)
  have hstep : 2 * ((N : Real) ^ exponent)⁻¹ < delta := by
    rw [← div_eq_mul_inv, div_lt_div_iff₀ hX (by positivity)]
    linarith
  obtain ⟨d, hdK, hdne⟩ := (lemma_7_7_holds N K delta (Fact.out : Nat.Prime N).two_le hdelta
    hdeltaOne).2 hKne (by linarith)
  exact ⟨d, hdK, bne_iff_ne.mp hdne⟩

/-! ### Lemma 13.4 -/

/-- The full Lemma 13.4 conclusion with the displayed real graph budget
used in the floor defining the progression length. The finite list has its
actual natural cardinality, bounded by that same real budget. -/
def IsStage134DataAtRealBound {N : Nat} [NeZero N] (S : Section13Context N)
    (theta Qbound : Real) (D : Stage134Data N) : Prop :=
  0 < D.q ∧ D.P.step != 0 ∧ D.P.IsProper ∧ D.H ⊆ D.P.carrier ∧
  (D.q : Real) ≤ Qbound ∧
  IsNatFloor
    (section13ThetaOne theta / (64 * Real.pi) *
      (N : Real) ^ (section13ThetaOne theta ^ 2 / (16 * Qbound))) D.m ∧
  (D.P.length = D.m ∨ D.P.length + 1 = D.m) ∧
  S.alpha ^ 32 * (N : Real) ^ 31 * D.P.length / 8 ≤ goodHeightWeight S D.H ∧
  ∀ h, h ∈ D.H → ∀ r,
    theta * (N : Real) ^ 2 ≤ ‖fourier (verticalEdgeFiberFunction S.A h) r‖ →
    ∃ i, r = D.a i * h + D.b i

/-- One construction for a graph budget chosen from the actual list size.
The source count bound is retained separately from the budget in the floor. -/
theorem lemma134_at_graph_budget
    (N : Nat) [NeZero N] (S : Section13Context N) (theta : Real)
    (budget : Nat → Real)
    (hprime : N.Prime) (htheta : 0 < theta) (hthetaBound : theta ≤ S.alpha ^ 32 / 4)
    (hbudget : ∀ q : Nat, 0 < q → (q : Real) ≤ section13QBound theta →
      (q : Real) ≤ budget q) :
    ∃ D : Stage134Data N, (D.q : Real) ≤ section13QBound theta ∧
      IsStage134DataAtRealBound S theta (budget D.q) D := by
  letI : Fact N.Prime := ⟨hprime⟩
  obtain ⟨q₀, B, sigma, G, hGcard, hFreiman, hBlarge, hq₀Bound, hcover⟩ :=
    corollary_13_3_holds N S.A theta hprime htheta
  let q := max 1 q₀
  have hq : 0 < q := by omega
  have hq₀q : q₀ ≤ q := by omega
  have hqBound : (q : Real) ≤ section13QBound theta := by
    simpa only [q, Nat.cast_max, Nat.cast_one] using
      max_le (lemma134_qBound_one_le S theta htheta hthetaBound) hq₀Bound
  have htheta₁ := lemma134_thetaOne_pos theta htheta
  have htheta₁One := lemma134_thetaOne_le_one S theta htheta hthetaBound
  let Qbound : Real := budget q
  have hqQ : (q : Real) ≤ Qbound := hbudget q hq hqBound
  let scale : Real := section13ThetaOne theta / (64 * Real.pi) *
    (N : Real) ^ (section13ThetaOne theta ^ 2 / (16 * Qbound))
  have hscaleMono : scale ≤ lemma134Scale N theta q :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hprime.one_le)
      (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith))) (by positivity)
  let m : Nat := ⌊scale⌋₊
  have hfloor : IsNatFloor scale m := (Nat.floor_eq_iff (by positivity)).mp rfl
  by_cases hmSmall : m ≤ 1
  · let D : Stage134Data N :=
      { q := q, m := m, P := lemma134EmptyProgression N, H := ∅, a := fun _ => 0, b := fun _ => 0 }
    exact ⟨D, hqBound, hq, bne_iff_ne.mpr one_ne_zero,
      show (∅ : Finset (ZMod N)).card = 0 from Finset.card_empty, by simp [D], hqQ, hfloor,
      show 0 = m ∨ 0 + 1 = m by omega, by simp [D, lemma134EmptyProgression, goodHeightWeight],
      by simp [D]⟩
  let l := m - 1
  have hl : 0 < l := by omega
  have hlScale : (l : Real) < lemma134Scale N theta q :=
    (Nat.cast_lt.mpr (by omega : l < m)).trans_le (hfloor.1.trans hscaleMono)
  have hmN : m ≤ N := by
    exact_mod_cast hfloor.1.trans
      (hscaleMono.trans (lemma134_scale_le_modulus theta htheta htheta₁One hq))
  have hlN : l ≤ N := by omega
  obtain ⟨d, hdBohr, hd⟩ := lemma134_exists_common_step B sigma theta htheta
    htheta₁One hq hq₀q hl hlScale hBlarge hFreiman
  obtain ⟨s, havg⟩ := lemma134_exists_progression_average S G d hd hlN
  let P := lemma134Progression d s l
  let H := P.carrier ∩ G
  choose a₀ b₀ haffine using lemma134_piece_affine_on_progression B sigma
    (section13ThetaOne theta) hprime htheta₁ hl hBlarge hFreiman d s hdBohr
  let a : Fin q → ZMod N := fun j => if hj : (j : Nat) < q₀ then a₀ ⟨j, hj⟩ else 0
  let b : Fin q → ZMod N := fun j => if hj : (j : Nat) < q₀ then b₀ ⟨j, hj⟩ else 0
  let D : Stage134Data N := { q := q, m := m, P := P, H := H, a := a, b := b }
  refine ⟨D, hqBound, hq, bne_iff_ne.mpr hd, lemma134_progression_proper d s hd hlN,
    Finset.inter_subset_left, hqQ, hfloor, Or.inr (show l + 1 = m by omega), ?_, ?_⟩
  · change S.alpha ^ 32 * (N : Real) ^ 31 * l / 8 ≤ goodHeightWeight S H
    have hgoodG := lemma134_good_exceptional_lower S theta G htheta hthetaBound hGcard
    refine le_of_mul_le_mul_left ?_ (show (0 : Real) < N by exact_mod_cast NeZero.pos N)
    linarith [mul_le_mul_of_nonneg_left hgoodG (Nat.cast_nonneg l),
      (by positivity : (0 : Real) ≤ l * (S.alpha ^ 32 * (N : Real) ^ 32))]
  · intro h hh r hr
    obtain ⟨hhP, hhG⟩ := Finset.mem_inter.mp hh
    obtain ⟨i, hiB, rfl⟩ := hcover h hhG r hr
    refine ⟨Fin.castLE hq₀q i, ?_⟩
    rw [haffine i h (Finset.mem_inter.mpr ⟨hiB, hhP⟩)]
    simp [D, a, b, Fin.castLE]

/-- **Gowers, Lemma 13.4**, with the prime-modulus and quantitative
`theta`-range hypotheses restored in the statement. -/
theorem lemma_13_4_holds : lemma_13_4 := by
  intro N _ S theta hprime htheta hthetaBound
  obtain ⟨D, hqBound, hD⟩ := lemma134_at_graph_budget N S theta (fun q => (q : Real))
    hprime htheta hthetaBound (fun _ _ _ => le_rfl)
  rcases hD with ⟨hq, hstep, hproper, hH, _, hfloor, hlength, hweight, hcover⟩
  exact ⟨D, hq, hstep, hproper, hH, hqBound, hfloor, hlength, hweight, hcover⟩

end LeanProofs.GowersSzemeredi
