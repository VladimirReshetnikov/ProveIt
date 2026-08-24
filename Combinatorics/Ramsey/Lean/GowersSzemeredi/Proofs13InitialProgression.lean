import GowersSzemeredi.Proofs13LargeSpectrumCover
import GowersSzemeredi.Proofs07ProgressionLinearity
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The initial progression in the bilinear extraction

This file proves Gowers's Lemma 13.4.  It also records counterexamples to two
omitted hypotheses in the printed statement before giving the repaired result.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-! ### Auditing the printed parameter range -/

/-- The statement before its missing hypotheses are restored. -/
private def lemma134Unrepaired : Prop :=
  ∀ (N : Nat) [NeZero N] (S : Section13Context N) (theta : Real),
    0 < theta → ∃ D : Stage134Data N, IsStage134Data S theta D

/-- The full domain with the zero function supplies a context at every
nonzero modulus, so the counterexamples below are not vacuous. -/
private def lemma134FullContext (N : Nat) [NeZero N] : Section13Context N where
  A := Finset.univ
  phi := fun _ => 0
  alpha := 1
  eta := (2 : Real) ^ (-(44 : Int))
  alpha_pos := by norm_num
  alpha_at_most_one := le_rfl
  card_A := by simp [ZMod.card]; ring
  separately_freiman := by
    constructor
    · intro x
      refine ⟨?_, ?_⟩
      · intro y _
        simp
      · intro s t _ _ _ _ _
        simp
    · intro y
      refine ⟨?_, ?_⟩
      · intro x _
        simp
      · intro s t _ _ _ _ _
        simp
  eta_value := rfl
  mostly_respected := by
    have hcount : respectedArrangementCount 8
        (Finset.univ : Finset (Pair N)) (fun _ : Pair N => (0 : ZMod N)) =
        arrangementCount 8 (Finset.univ : Finset (Pair N)) := by
      apply countWhere_congr
      intro R
      constructor
      · exact fun h => h.1
      · intro hR
        refine ⟨hR, ?_⟩
        unfold DArrangement.IsRespected IsAdditiveTuple
        simp
    unfold MostlyRespectsEight
    rw [hcount]
    have heta : 0 ≤ (2 : Real) ^ (-(44 : Int)) := by positivity
    have hcountNonneg : 0 ≤
        (arrangementCount 8 (Finset.univ : Finset (Pair N)) : Real) := by
      positivity
    nlinarith

private lemma lemma134_theta_two_q_bound :
    section13QBound 2 < 1 := by
  unfold section13QBound
  rw [zpow_neg, ← div_eq_mul_inv]
  apply (div_lt_one₀ (by positivity : (0 : Real) < 2 ^ 10479)).2
  exact pow_lt_pow_right₀ (by norm_num : (1 : Real) < 2) (by omega)

/-- For `theta = 2`, the asserted positive integer `q` is bounded strictly
below one.  Thus an upper bound on `theta` is genuinely necessary. -/
theorem lemma_13_4_theta_range_counterexample
    (N : Nat) [NeZero N] (S : Section13Context N) :
    ¬ ∃ D : Stage134Data N, IsStage134Data S 2 D := by
  rintro ⟨D, hD⟩
  have hqPos : 0 < D.q := hD.1
  have hqBound : (D.q : Real) ≤ section13QBound 2 := hD.2.2.2.2.1
  have hqOne : (1 : Real) ≤ D.q := by exact_mod_cast hqPos
  linarith [lemma134_theta_two_q_bound]

/-- At modulus one there is no nonzero progression step, independently of
all other data.  This witnesses the missing prime/nontrivial-modulus
hypothesis in the printed statement. -/
theorem lemma_13_4_modulus_one_counterexample
    (S : Section13Context 1) (theta : Real) :
    ¬ ∃ D : Stage134Data 1, IsStage134Data S theta D := by
  rintro ⟨D, hD⟩
  have hstep : D.P.step ≠ 0 := bne_iff_ne.mp hD.2.1
  exact hstep (Subsingleton.elim _ _)

/-- The modulus-one obstruction is nonvacuous even at a positive `theta`
which satisfies the repaired quantitative upper bound. -/
theorem lemma_13_4_modulus_one_concrete_counterexample :
    ∃ S : Section13Context 1,
      0 < (1 / 8 : Real) ∧ (1 / 8 : Real) ≤ S.alpha ^ 32 / 4 ∧
      ¬ ∃ D : Stage134Data 1, IsStage134Data S (1 / 8) D := by
  refine ⟨lemma134FullContext 1, by norm_num, ?_,
    lemma_13_4_modulus_one_counterexample (lemma134FullContext 1) (1 / 8)⟩
  norm_num [lemma134FullContext]

private theorem lemma134Unrepaired_false : ¬ lemma134Unrepaired := by
  intro h
  have hout := h 2 (lemma134FullContext 2) 2 (by norm_num)
  exact lemma_13_4_theta_range_counterexample 2 (lemma134FullContext 2) hout

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
  have htwo : (2 : Real) ^ (-(1882 : Int)) ≤ 1 := by
    exact zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num)
  unfold section13ThetaOne
  nlinarith [mul_le_mul htwo hpow (by positivity) (by positivity)]

private def lemma134Scale (N : Nat) (theta : Real) (q : Nat) : Real :=
  section13ThetaOne theta / (64 * Real.pi) *
    (N : Real) ^ (section13ThetaOne theta ^ 2 / (16 * (q : Real)))

private def lemma134Floor (N : Nat) (theta : Real) (q : Nat) : Nat :=
  ⌊lemma134Scale N theta q⌋₊

private lemma lemma134_scale_nonneg (N : Nat) (theta : Real) (q : Nat)
    (htheta : 0 < theta) : 0 ≤ lemma134Scale N theta q := by
  unfold lemma134Scale
  exact mul_nonneg
    (div_nonneg (lemma134_thetaOne_pos theta htheta).le (by positivity))
    (Real.rpow_nonneg (by positivity) _)

private lemma lemma134_floor_spec (N : Nat) (theta : Real) (q : Nat)
    (htheta : 0 < theta) :
    IsNatFloor (lemma134Scale N theta q) (lemma134Floor N theta q) := by
  unfold IsNatFloor lemma134Floor
  exact (Nat.floor_eq_iff (lemma134_scale_nonneg N theta q htheta)).1 rfl

private def lemma134EmptyProgression (N : Nat) : ModAP N where
  start := 0
  step := 1
  length := 0

private lemma lemma134_empty_stage {N : Nat} [NeZero N]
    (S : Section13Context N) (theta : Real) (q : Nat)
    (hprime : Nat.Prime N) (htheta : 0 < theta) (hq : 0 < q)
    (hqBound : (q : Real) ≤ section13QBound theta)
    (hm : lemma134Floor N theta q ≤ 1) :
    ∃ D : Stage134Data N, IsStage134Data S theta D := by
  letI : Fact N.Prime := ⟨hprime⟩
  let P := lemma134EmptyProgression N
  let D : Stage134Data N :=
    { q := q
      m := lemma134Floor N theta q
      P := P
      H := ∅
      a := fun _ => 0
      b := fun _ => 0 }
  refine ⟨D, hq, ?_, ?_, ?_, hqBound, ?_, ?_, ?_, ?_⟩
  · change (1 : ZMod N) != 0
    exact bne_iff_ne.mpr one_ne_zero
  · change (Finset.card ∅ : Nat) = 0
    simp
  · simp [D, P, lemma134EmptyProgression, ModAP.carrier]
  · simpa only [D, lemma134Scale] using
      lemma134_floor_spec N theta q htheta
  ·
    have hzeroOrOne : lemma134Floor N theta q = 0 ∨
        lemma134Floor N theta q = 1 := by omega
    rcases hzeroOrOne with hm0 | hm1
    · left
      change 0 = lemma134Floor N theta q
      exact hm0.symm
    · right
      change 0 + 1 = lemma134Floor N theta q
      exact hm1.symm
  · simp [goodHeightWeight, D, P, lemma134EmptyProgression]
  · simp [D]

/-! ### Averaging over translated progressions -/

private def lemma134Progression {N : Nat} (d s : ZMod N) (l : Nat) :
    ModAP N where
  start := s
  step := d
  length := l

private lemma lemma134_progression_proper {N l : Nat} [NeZero N]
    [Fact N.Prime] (d s : ZMod N) (hd : d ≠ 0) (hlN : l ≤ N) :
    (lemma134Progression d s l).IsProper := by
  classical
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
  classical
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
  classical
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
  classical
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
  unfold goodHeightWeight
  have hfilter (s : ZMod N) :
      (((lemma134Progression d s l).carrier ∩ G).filter
        (IsGoodHeight S)) =
      (G.filter (IsGoodHeight S)).filter fun h =>
        h ∈ (lemma134Progression d s l).carrier := by
    ext h
    simp only [Finset.mem_filter, Finset.mem_inter]
    tauto
  simp_rw [hfilter]
  calc
    (∑ s : ZMod N,
        (↑(((G.filter (IsGoodHeight S)).filter fun h =>
          h ∈ (lemma134Progression d s l).carrier).sum
            (section13C S)) : Real)) =
        ∑ s : ZMod N, ∑ h ∈ G.filter (IsGoodHeight S),
          if h ∈ (lemma134Progression d s l).carrier then
            (section13C S h : Real) else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      norm_cast
      rw [Finset.sum_filter]
    _ = ∑ h ∈ G.filter (IsGoodHeight S),
        ∑ s : ZMod N,
          if h ∈ (lemma134Progression d s l).carrier then
            (section13C S h : Real) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ h ∈ G.filter (IsGoodHeight S),
        (l : Real) * section13C S h := by
      apply Finset.sum_congr rfl
      intro h _
      exact lemma134_sum_indicator_progression d h hd hlN _
    _ = (l : Real) *
        ((G.filter (IsGoodHeight S)).sum (section13C S) : Nat) := by
      rw [← Finset.mul_sum]
      norm_cast

private lemma lemma134_exists_progression_average {N l : Nat} [NeZero N]
    [Fact N.Prime] (S : Section13Context N) (G : Finset (ZMod N))
    (d : ZMod N) (hd : d ≠ 0) (hlN : l ≤ N) :
    ∃ s : ZMod N,
      (l : Real) * goodHeightWeight S G ≤
        (N : Real) * goodHeightWeight S
          ((lemma134Progression d s l).carrier ∩ G) := by
  classical
  let W : ZMod N → Real := fun s =>
    goodHeightWeight S ((lemma134Progression d s l).carrier ∩ G)
  have hsum : ∑ s : ZMod N, W s =
      (l : Real) * goodHeightWeight S G := by
    exact lemma134_goodWeight_inter_sum S G d hd hlN
  have hU : (Finset.univ : Finset (ZMod N)).Nonempty :=
    Finset.univ_nonempty
  have haverage :
      ∑ s : ZMod N, ((l : Real) * goodHeightWeight S G) ≤
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

private def lemma134_fiberEquiv {X Y : Type*} (f : X → Y) :
    X ≃ Σ y, lemma134Fiber f y where
  toFun x := ⟨f x, x, rfl⟩
  invFun z := z.2.1
  left_inv _ := rfl
  right_inv z := by
    rcases z with ⟨y, ⟨x, hx⟩⟩
    subst y
    rfl

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
  classical
  let c : Y → Real := fun y => Fintype.card (lemma134Fiber f y)
  have hsource : (Fintype.card X : Real) = ∑ y : Y, c y := by
    have hcard := Fintype.card_congr (lemma134_fiberEquiv f)
    rw [Fintype.card_sigma] at hcard
    rw [hcard]
    simp only [c, Nat.cast_sum]
  have hcollision :
      (Fintype.card (lemma134Collision f) : Real) =
        ∑ y : Y, (c y) ^ 2 := by
    have hcard := Fintype.card_congr (lemma134_collisionEquiv f)
    rw [Fintype.card_sigma] at hcard
    simp only [Fintype.card_prod] at hcard
    rw [hcard]
    simp only [c, Nat.cast_sum, Nat.cast_mul, pow_two]
  have hcollisionSet :
      (lemma134CollisionSet f).card =
        Fintype.card (lemma134Collision f) := by
    unfold lemma134CollisionSet
    rw [Finset.filter_congr_decidable]
    exact (Fintype.card_subtype fun p : X × X => f p.1 = f p.2).symm
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset Y)) (f := c)
  rw [hcollisionSet]
  simpa [hsource, hcollision] using hcs

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
  classical
  have h := lemma134_collision_lower (fun z : A => z.1.1)
  have hcard := Fintype.card_congr (lemma134_edgePairEquiv A)
  simp only [Fintype.card_coe] at hcard
  rw [hcard] at h
  simpa only [Fintype.card_coe, ZMod.card] using h

private lemma lemma134_edge_eight_lower {N : Nat} [NeZero N]
    (A : Finset (Pair N)) :
    (Fintype.card (lemma134Edge A) : Real) ^ 8 ≤
      (N : Real) ^ 7 * Fintype.card (lemma134EdgeEight A) := by
  classical
  let e : Real := Fintype.card (lemma134Edge A)
  let e₂ : Real := Fintype.card (lemma134EdgeTwo A)
  let e₄ : Real := Fintype.card (lemma134EdgeFour A)
  let e₈ : Real := Fintype.card (lemma134EdgeEight A)
  have h₂ : e ^ 2 ≤ N * e₂ := by
    simpa only [e, e₂, Fintype.card_coe, ZMod.card] using
      lemma134_collision_lower (lemma134Edge.height (A := A))
  have h₄ : e₂ ^ 2 ≤ N * e₄ := by
    simpa only [e₂, e₄, Fintype.card_coe, ZMod.card] using
      lemma134_collision_lower (lemma134EdgeTwo.height (A := A))
  have h₈ : e₄ ^ 2 ≤ N * e₈ := by
    simpa only [e₄, e₈, Fintype.card_coe, ZMod.card] using
      lemma134_collision_lower (lemma134EdgeFour.height (A := A))
  have he : 0 ≤ e := by positivity
  have hN : 0 ≤ (N : Real) := by positivity
  have hsquare₂ : (e ^ 2) ^ 2 ≤ (N * e₂) ^ 2 :=
    pow_le_pow_left₀ (sq_nonneg e) h₂ 2
  have heFour : e ^ 4 ≤ N ^ 3 * e₄ := by
    calc
      e ^ 4 = (e ^ 2) ^ 2 := by ring
      _ ≤ (N * e₂) ^ 2 := hsquare₂
      _ = N ^ 2 * e₂ ^ 2 := by ring
      _ ≤ N ^ 2 * (N * e₄) :=
        mul_le_mul_of_nonneg_left h₄ (sq_nonneg (N : Real))
      _ = N ^ 3 * e₄ := by ring
  have hsquare₄ : (e ^ 4) ^ 2 ≤ (N ^ 3 * e₄) ^ 2 :=
    pow_le_pow_left₀ (pow_nonneg he 4) heFour 2
  change e ^ 8 ≤ N ^ 7 * e₈
  calc
    e ^ 8 = (e ^ 4) ^ 2 := by ring
    _ ≤ (N ^ 3 * e₄) ^ 2 := hsquare₄
    _ = N ^ 6 * e₄ ^ 2 := by ring
    _ ≤ N ^ 6 * (N * e₈) :=
      mul_le_mul_of_nonneg_left h₈ (pow_nonneg hN 6)
    _ = N ^ 7 * e₈ := by ring

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
  apply Subtype.ext
  apply Prod.ext <;> apply Subtype.ext
  · apply Prod.ext <;> apply Subtype.ext <;> apply Prod.ext
    · simpa [lemma134EdgeEight.get, lemma134EdgeFour.get,
        lemma134EdgeTwo.get] using congrFun h 0
    · simpa [lemma134EdgeEight.get, lemma134EdgeFour.get,
        lemma134EdgeTwo.get] using congrFun h 1
    · simpa [lemma134EdgeEight.get, lemma134EdgeFour.get,
        lemma134EdgeTwo.get] using congrFun h 2
    · simpa [lemma134EdgeEight.get, lemma134EdgeFour.get,
        lemma134EdgeTwo.get] using congrFun h 3
  · apply Prod.ext <;> apply Subtype.ext <;> apply Prod.ext
    · simpa [lemma134EdgeEight.get, lemma134EdgeFour.get,
        lemma134EdgeTwo.get] using congrFun h 4
    · simpa [lemma134EdgeEight.get, lemma134EdgeFour.get,
        lemma134EdgeTwo.get] using congrFun h 5
    · simpa [lemma134EdgeEight.get, lemma134EdgeFour.get,
        lemma134EdgeTwo.get] using congrFun h 6
    · simpa [lemma134EdgeEight.get, lemma134EdgeFour.get,
        lemma134EdgeTwo.get] using congrFun h 7

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
  classical
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
    rw [hij]
    rw [lemma134EdgeSixteenGet_castAdd, p.1.1.get_height]
  · have hi8 : 8 ≤ (i : Nat) := by omega
    let j : Fin 8 := ⟨(i : Nat) - 8, by omega⟩
    have hij : i = Fin.natAdd 8 j := by
      apply Fin.ext
      simp [j]
      omega
    rw [hij]
    rw [lemma134EdgeSixteenGet_natAdd, p.1.2.get_height]
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
  have hR : lemma134CollisionArrangement p =
      lemma134CollisionArrangement q := congrArg Subtype.val hpq
  have hx : (lemma134CollisionArrangement p).x =
      (lemma134CollisionArrangement q).x := congrArg DArrangement.x hR
  have hy : (lemma134CollisionArrangement p).y =
      (lemma134CollisionArrangement q).y := congrArg DArrangement.y hR
  have hh : p.1.1.height = q.1.1.height := by
    simpa [lemma134CollisionArrangement, DArrangement.height] using
      congrArg DArrangement.height hR
  have hpHeight : p.1.1.height = p.1.2.height :=
    congrArg Prod.fst (lemma134_arrangementCollision_key_eq p)
  have hqHeight : q.1.1.height = q.1.2.height :=
    congrArg Prod.fst (lemma134_arrangementCollision_key_eq q)
  apply Subtype.ext
  apply Prod.ext
  · apply lemma134EdgeEight.get_injective
    funext i
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · simpa [lemma134CollisionArrangement, lemma134EdgeSixteenGet,
          lemma134Edge.x, DArrangement.x] using
          congrFun hx (Fin.castAdd 8 i)
      · simpa [lemma134CollisionArrangement, lemma134EdgeSixteenGet,
          lemma134Edge.y, DArrangement.y] using
          congrFun hy (Fin.castAdd 8 i)
    · change (p.1.1.get i).height = (q.1.1.get i).height
      rw [p.1.1.get_height i, q.1.1.get_height i]
      exact hh
  · apply lemma134EdgeEight.get_injective
    funext i
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · change (p.1.2.get i).x = (q.1.2.get i).x
        have hxi := congrFun hx (Fin.natAdd 8 i)
        change (lemma134EdgeSixteenGet p.1 (Fin.natAdd 8 i)).x =
          (lemma134EdgeSixteenGet q.1 (Fin.natAdd 8 i)).x at hxi
        simpa only [lemma134EdgeSixteenGet_natAdd] using hxi
      · change (p.1.2.get i).y = (q.1.2.get i).y
        have hyi := congrFun hy (Fin.natAdd 8 i)
        change (lemma134EdgeSixteenGet p.1 (Fin.natAdd 8 i)).y =
          (lemma134EdgeSixteenGet q.1 (Fin.natAdd 8 i)).y at hyi
        simpa only [lemma134EdgeSixteenGet_natAdd] using hyi
    · change (p.1.2.get i).height = (q.1.2.get i).height
      rw [p.1.2.get_height i, q.1.2.get_height i]
      exact hpHeight.symm.trans (hh.trans hqHeight)

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
  classical
  let e : Real := Fintype.card (lemma134Edge A)
  let e₈ : Real := Fintype.card (lemma134EdgeEight A)
  let c : Real := Fintype.card (lemma134ArrangementCollision A)
  have hA : (A.card : Real) ^ 2 ≤ N * e := by
    simpa only [e] using lemma134_edge_card_lower A
  have hE : e ^ 8 ≤ N ^ 7 * e₈ := by
    simpa only [e, e₈] using lemma134_edge_eight_lower A
  have hC : e₈ ^ 2 ≤ N ^ 2 * c := by
    simpa only [e₈, c] using lemma134_arrangement_collision_lower A
  have hcountNat := lemma134_arrangement_collision_card_le A
  have hcount : c ≤ (arrangementCount 8 A : Real) := by
    dsimp only [c]
    exact Nat.cast_le.mpr hcountNat
  have hA16 : ((A.card : Real) ^ 2) ^ 16 ≤ (N * e) ^ 16 :=
    pow_le_pow_left₀ (sq_nonneg (A.card : Real)) hA 16
  have hE2 : (e ^ 8) ^ 2 ≤ (N ^ 7 * e₈) ^ 2 :=
    pow_le_pow_left₀ (pow_nonneg (by positivity : 0 ≤ e) 8) hE 2
  have hN : 0 ≤ (N : Real) := by positivity
  calc
    (A.card : Real) ^ 32 = ((A.card : Real) ^ 2) ^ 16 := by ring
    _ ≤ (N * e) ^ 16 := hA16
    _ = N ^ 16 * (e ^ 8) ^ 2 := by ring
    _ ≤ N ^ 16 * (N ^ 7 * e₈) ^ 2 :=
      mul_le_mul_of_nonneg_left hE2 (pow_nonneg hN 16)
    _ = N ^ 30 * e₈ ^ 2 := by ring
    _ ≤ N ^ 30 * (N ^ 2 * c) :=
      mul_le_mul_of_nonneg_left hC (pow_nonneg hN 30)
    _ = N ^ 32 * c := by ring
    _ ≤ N ^ 32 * arrangementCount 8 A :=
      mul_le_mul_of_nonneg_left hcount (pow_nonneg hN 32)

private lemma lemma134_arrangement_count_lower {N : Nat} [NeZero N]
    (S : Section13Context N) :
    S.alpha ^ 32 * (N : Real) ^ 32 ≤ arrangementCount 8 S.A := by
  have hraw := lemma134_arrangement_count_lower_card S.A
  rw [S.card_A] at hraw
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hNpow : 0 < (N : Real) ^ 32 := pow_pos hN 32
  have hcancel : (N : Real) ^ 32 *
      (S.alpha ^ 32 * (N : Real) ^ 32) ≤
      (N : Real) ^ 32 * arrangementCount 8 S.A := by
    calc
      (N : Real) ^ 32 * (S.alpha ^ 32 * (N : Real) ^ 32) =
          (S.alpha * (N : Real) ^ 2) ^ 32 := by ring
      _ ≤ (N : Real) ^ 32 * arrangementCount 8 S.A := hraw
  exact le_of_mul_le_mul_left hcancel hNpow

/-! ### Good heights carry a positive fraction of the arrangements -/

private lemma lemma134_sectionC_total {N : Nat} [NeZero N]
    (S : Section13Context N) :
    ∑ h : ZMod N, section13C S h = arrangementCount 8 S.A := by
  classical
  let T : Finset (DArrangement N 8) :=
    Finset.univ.filter fun R => R.IsIn S.A
  have hmap : Set.MapsTo DArrangement.height (T : Set (DArrangement N 8))
      (Finset.univ : Finset (ZMod N)) := by
    intro R _
    simp
  have hfiber := Finset.card_eq_sum_card_fiberwise hmap
  have hheight (h : ZMod N) : section13C S h =
      (T.filter fun R => R.height = h).card := by
    unfold section13C arrangementCountAtHeight countWhere
    rw [Finset.filter_congr_decidable]
    apply congrArg Finset.card
    ext R
    simp [T]
  have htotal : T.card = arrangementCount 8 S.A := by
    unfold arrangementCount countWhere
    rw [Finset.filter_congr_decidable]
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
      (Finset.univ : Finset (ZMod N)) := by
    intro R _
    simp
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
  classical
  unfold section13G section13C respectedArrangementCountAtHeight
    arrangementCountAtHeight countWhere
  exact Finset.card_le_card (by
    intro R
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto)

private def lemma134Left : Finset (Fin 16) :=
  Finset.univ.filter fun i => (i : Nat) < 8

private def lemma134Right : Finset (Fin 16) :=
  Finset.univ.filter fun i => 8 ≤ (i : Nat)

private lemma lemma134_zero_mem_left : (0 : Fin 16) ∈ lemma134Left := by
  simp [lemma134Left]

private lemma lemma134_zero_notMem_right : (0 : Fin 16) ∉ lemma134Right := by
  simp [lemma134Right]

private lemma lemma134_additive_ext {N : Nat}
    {x y : Fin 16 → ZMod N} (hx : IsAdditiveTuple (k := 8) x)
    (hy : IsAdditiveTuple (k := 8) y)
    (htail : ∀ i : Fin 15, x i.succ = y i.succ) : x = y := by
  have hoff : ∀ i : Fin 16, i ≠ 0 → x i = y i := by
    intro i hi
    rcases i with ⟨(_ | i), hiBound⟩
    · exact (hi rfl).elim
    · exact htail ⟨i, by omega⟩
  unfold IsAdditiveTuple at hx hy
  change (∑ i ∈ lemma134Left, x i) = ∑ i ∈ lemma134Right, x i at hx
  change (∑ i ∈ lemma134Left, y i) = ∑ i ∈ lemma134Right, y i at hy
  have hleft :
      (∑ i ∈ lemma134Left.erase 0, x i) =
        ∑ i ∈ lemma134Left.erase 0, y i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hoff i (Finset.ne_of_mem_erase hi)
  have hright :
      (∑ i ∈ lemma134Right, x i) = ∑ i ∈ lemma134Right, y i := by
    apply Finset.sum_congr rfl
    intro i hi
    apply hoff i
    intro hzero
    subst i
    exact lemma134_zero_notMem_right hi
  funext i
  refine Fin.cases ?_ (fun j => htail j) i
  apply add_left_cancel (a := ∑ i ∈ lemma134Left.erase 0, x i)
  calc
    (∑ i ∈ lemma134Left.erase 0, x i) + x 0 =
        ∑ i ∈ lemma134Left, x i :=
      Finset.sum_erase_add _ _ lemma134_zero_mem_left
    _ = ∑ i ∈ lemma134Right, x i := hx
    _ = ∑ i ∈ lemma134Right, y i := hright
    _ = ∑ i ∈ lemma134Left, y i := hy.symm
    _ = (∑ i ∈ lemma134Left.erase 0, y i) + y 0 := by
      symm
      exact Finset.sum_erase_add _ _ lemma134_zero_mem_left
    _ = (∑ i ∈ lemma134Left.erase 0, x i) + y 0 := by rw [hleft]

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
    intro i
    exact congrFun (congrArg Prod.fst hcode) i
  have hx : R.1.x = T.1.x :=
    lemma134_additive_ext R.2.1.1 T.2.1.1 hxTail
  have hy : R.1.y = T.1.y := congrArg Prod.snd hcode
  have hh : R.1.height = T.1.height := R.2.2.trans T.2.2.symm
  exact Prod.ext hx (Prod.ext hy hh)

private lemma lemma134_sectionC_upper {N : Nat} [NeZero N]
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
  let good := Finset.univ.filter (IsGoodHeight S)
  let bad := Finset.univ.filter fun h => ¬ IsGoodHeight S h
  let C : Real := ∑ h : ZMod N, section13C S h
  let G : Real := ∑ h : ZMod N, section13G S h
  let Cbad : Real := ∑ h ∈ bad, section13C S h
  let Cgood : Real := ∑ h ∈ good, section13C S h
  have heta : 0 < S.eta := by
    rw [S.eta_value]
    positivity
  have hGC (h : ZMod N) : (section13G S h : Real) ≤ section13C S h := by
    exact_mod_cast lemma134_sectionG_le_C S h
  have hbad (h : ZMod N) (hh : h ∈ bad) :
      2 * S.eta * section13C S h ≤
        (section13C S h : Real) - section13G S h := by
    have hh' : ¬ IsGoodHeight S h := by
      simpa [bad] using hh
    have hlt := not_le.mp hh'
    nlinarith
  have hbadDeficit :
      2 * S.eta * Cbad ≤ C - G := by
    calc
      2 * S.eta * Cbad =
          ∑ h ∈ bad, 2 * S.eta * section13C S h := by
        simp [Cbad, Finset.mul_sum]
      _ ≤ ∑ h ∈ bad,
          ((section13C S h : Real) - section13G S h) := by
        exact Finset.sum_le_sum fun h hh => hbad h hh
      _ ≤ ∑ h : ZMod N,
          ((section13C S h : Real) - section13G S h) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (by simp [bad])
        intro h _ hh
        exact sub_nonneg.mpr (hGC h)
      _ = C - G := by
        simp [C, G, Finset.sum_sub_distrib]
  have hmostly : (1 - S.eta) * C ≤ G := by
    unfold C G
    have hCtotal : (∑ h : ZMod N, (section13C S h : Real)) =
        arrangementCount 8 S.A := by
      exact_mod_cast lemma134_sectionC_total S
    have hGtotal : (∑ h : ZMod N, (section13G S h : Real)) =
        respectedArrangementCount 8 S.A S.phi := by
      exact_mod_cast lemma134_sectionG_total S
    rw [hCtotal, hGtotal]
    exact S.mostly_respected
  have hdeficit : 2 * S.eta * Cbad ≤ S.eta * C := by
    linarith
  have htwice : 2 * Cbad ≤ C := by
    apply le_of_mul_le_mul_left (a := S.eta)
    · nlinarith
    · exact heta
  have hpartition : Cgood + Cbad = C := by
    unfold Cgood Cbad C good bad
    simp only [Finset.sum_filter_add_sum_filter_not]
  have hgoodHalf : C / 2 ≤ Cgood := by nlinarith
  have hCtotal : (∑ h : ZMod N, (section13C S h : Real)) =
      arrangementCount 8 S.A := by
    exact_mod_cast lemma134_sectionC_total S
  unfold C at hgoodHalf
  rw [hCtotal] at hgoodHalf
  simpa [Cgood, good, goodHeightWeight] using hgoodHalf

private lemma lemma134_good_exceptional_lower {N : Nat} [NeZero N]
    (S : Section13Context N) (theta : Real) (G : Finset (ZMod N))
    (_htheta : 0 < theta) (hthetaBound : theta ≤ S.alpha ^ 32 / 4)
    (hGcard : (1 - theta) * N ≤ G.card) :
    S.alpha ^ 32 * (N : Real) ^ 32 / 4 ≤ goodHeightWeight S G := by
  classical
  let E : Finset (ZMod N) := Finset.univ \ G
  have hpartitionCard : E.card + G.card = N := by
    unfold E
    rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ G)]
    simp [ZMod.card]
  have hpartitionCardR : (E.card : Real) + G.card = N := by
    exact_mod_cast hpartitionCard
  have hEcard : (E.card : Real) ≤ theta * N := by
    linarith
  have hEweightNat : goodHeightWeight S E ≤ E.card * N ^ 31 := by
    unfold goodHeightWeight
    calc
      (E.filter (IsGoodHeight S)).sum (section13C S) ≤
          E.sum (section13C S) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro i _ _
        omega
      _ ≤ E.card • N ^ 31 :=
        Finset.sum_le_card_nsmul E (section13C S) (N ^ 31)
          (fun h _ => lemma134_sectionC_upper S h)
      _ = E.card * N ^ 31 := by simp
  have hEweight : (goodHeightWeight S E : Real) ≤
      theta * (N : Real) ^ 32 := by
    have hEweightR : (goodHeightWeight S E : Real) ≤
        (E.card : Real) * (N : Real) ^ 31 := by
      exact_mod_cast hEweightNat
    calc
      (goodHeightWeight S E : Real) ≤
          (E.card : Real) * (N : Real) ^ 31 := hEweightR
      _ ≤ (theta * N) * (N : Real) ^ 31 :=
        mul_le_mul_of_nonneg_right hEcard (by positivity)
      _ = theta * (N : Real) ^ 32 := by ring
  have hdisj : Disjoint G E := by
    exact Finset.disjoint_sdiff
  have hunion : G ∪ E = Finset.univ := by
    simp [E]
  have hweightPartition :
      goodHeightWeight S G + goodHeightWeight S E =
        goodHeightWeight S Finset.univ := by
    unfold goodHeightWeight
    rw [← Finset.sum_union]
    · rw [← Finset.filter_union, hunion]
    · exact Disjoint.mono (Finset.filter_subset _ _)
        (Finset.filter_subset _ _) hdisj
  have huniv := lemma134_good_univ_lower S
  have htotal := lemma134_arrangement_count_lower S
  have hunivAlpha :
      S.alpha ^ 32 * (N : Real) ^ 32 / 2 ≤
        goodHeightWeight S Finset.univ := by
    exact (div_le_div_of_nonneg_right htotal (by norm_num)).trans huniv
  have hthetaLoss : theta * (N : Real) ^ 32 ≤
      S.alpha ^ 32 * (N : Real) ^ 32 / 4 := by
    nlinarith [mul_le_mul_of_nonneg_right hthetaBound
      (show 0 ≤ (N : Real) ^ 32 by positivity)]
  have hweightPartitionR :
      (goodHeightWeight S G : Real) + goodHeightWeight S E =
        goodHeightWeight S Finset.univ := by
    exact_mod_cast hweightPartition
  nlinarith

/-! ### The progression length and affine restrictions -/

private lemma lemma134_scale_le_modulus {N q : Nat} [NeZero N]
    (theta : Real) (htheta : 0 < theta)
    (htheta₁One : section13ThetaOne theta ≤ 1) (hq : 0 < q) :
    lemma134Scale N theta q ≤ N := by
  let theta₁ := section13ThetaOne theta
  let exponent : Real := theta₁ ^ 2 / (16 * (q : Real))
  have htheta₁ : 0 < theta₁ := lemma134_thetaOne_pos theta htheta
  have hthetaSq : theta₁ ^ 2 ≤ 1 := by
    have htheta₁One' : theta₁ ≤ 1 := htheta₁One
    nlinarith [sq_nonneg (theta₁ - 1)]
  have hqOne : (1 : Real) ≤ q := by exact_mod_cast hq
  have hden : (0 : Real) < 16 * (q : Real) := by positivity
  have hexponentNonneg : 0 ≤ exponent := by
    unfold exponent
    positivity
  have hexponentOne : exponent ≤ 1 := by
    unfold exponent
    apply (div_le_one₀ hden).2
    nlinarith
  have hNOne : (1 : Real) ≤ N := by exact_mod_cast NeZero.pos N
  have hrpow : (N : Real) ^ exponent ≤ N := by
    calc
      (N : Real) ^ exponent ≤ (N : Real) ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hNOne hexponentOne
      _ = N := by rw [Real.rpow_one]
  have hcoefficient : theta₁ / (64 * Real.pi) ≤ 1 := by
    apply (div_le_one₀ (by positivity : (0 : Real) < 64 * Real.pi)).2
    have htheta₁One' : theta₁ ≤ 1 := htheta₁One
    nlinarith [Real.pi_gt_three]
  unfold lemma134Scale
  change theta₁ / (64 * Real.pi) * (N : Real) ^ exponent ≤ N
  calc
    theta₁ / (64 * Real.pi) * (N : Real) ^ exponent ≤
        1 * (N : Real) :=
      mul_le_mul hcoefficient hrpow (Real.rpow_nonneg (by positivity) _)
        (by norm_num)
    _ = N := one_mul _

private lemma lemma134_floor_pred_bounds {N q : Nat} [NeZero N]
    (theta : Real) (htheta : 0 < theta)
    (htheta₁One : section13ThetaOne theta ≤ 1) (hq : 0 < q)
    (hm : 2 ≤ lemma134Floor N theta q) :
    let l := lemma134Floor N theta q - 1
    0 < l ∧ (l : Real) < lemma134Scale N theta q ∧ l ≤ N := by
  let m := lemma134Floor N theta q
  let l := m - 1
  have hfloor := lemma134_floor_spec N theta q htheta
  have hl : 0 < l := by omega
  have hlm : l < m := by omega
  have hlScale : (l : Real) < lemma134Scale N theta q := by
    exact (by exact_mod_cast hlm : (l : Real) < m).trans_le hfloor.1
  have hmNReal : (m : Real) ≤ N :=
    hfloor.1.trans (lemma134_scale_le_modulus theta htheta htheta₁One hq)
  have hmN : m ≤ N := by exact_mod_cast hmNReal
  exact ⟨hl, hlScale, (Nat.sub_le m 1).trans hmN⟩

private lemma lemma134_progression_difference {N l : Nat}
    (d s x y : ZMod N)
    (hx : x ∈ (lemma134Progression d s l).carrier)
    (hy : y ∈ (lemma134Progression d s l).carrier) :
    x - y ∈ symmetricMultiples d l := by
  classical
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
  classical
  have hbeta := lemma134_density_lower (B i) theta₁ htheta₁ (hBlarge i)
  rw [bohr, Finset.mem_filter] at hd ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  intro r hr
  have hrUnion : r ∈ lemma134SpectrumUnion B := by
    unfold lemma134SpectrumUnion
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hr⟩
  have hdr := hd.2 r hrUnion
  calc
    (centeredAbs (r * d) : Real) ≤
        theta₁ / (32 * Real.pi * (l : Real)) * N := hdr
    _ ≤ lemma134Density (B i) / (32 * Real.pi * (l : Real)) * N := by
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
  letI : Fact N.Prime := ⟨hprime⟩
  intro i
  have hbeta := lemma134_density_lower (B i) theta₁ htheta₁ (hBlarge i)
  have hbetaPos : 0 < lemma134Density (B i) := htheta₁.trans_le hbeta
  have hd' := lemma134_individual_bohr B theta₁ htheta₁ hl hBlarge d hd i
  obtain ⟨c, hc⟩ := corollary_7_9_holds N (B i) (sigma i)
    (lemma134Density (B i)) hprime hbetaPos (lemma134_density_card (B i))
    (hFreiman i) l hl d hd'
  by_cases hnonempty : (B i ∩ (lemma134Progression d s l).carrier).Nonempty
  · obtain ⟨y, hy⟩ := hnonempty
    refine ⟨c, sigma i y - c * y, ?_⟩
    intro x hx
    have hx' := Finset.mem_inter.mp hx
    have hy' := Finset.mem_inter.mp hy
    have hxy := hc x hx'.1 y hy'.1
      (lemma134_progression_difference d s x y hx'.2 hy'.2)
    linear_combination hxy
  · refine ⟨0, 0, ?_⟩
    intro h hh
    exact (hnonempty ⟨h, hh⟩).elim

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
  classical
  have hper (i : Fin q₀) :
      ((section7Spectrum (B i) (lemma134Density (B i))).card : Real) ≤
        16 * theta₁ ^ (-(2 : Real)) := by
    have hbeta := lemma134_density_lower (B i) theta₁ htheta₁ (hBlarge i)
    have hbetaPos : 0 < lemma134Density (B i) := htheta₁.trans_le hbeta
    have hK := (lemma_7_8_holds N (B i) (sigma i)
      (lemma134Density (B i)) hbetaPos (lemma134_density_card (B i))
      (hFreiman i)).1
    calc
      ((section7Spectrum (B i) (lemma134Density (B i))).card : Real) ≤
          16 * lemma134Density (B i) ^ (-(2 : Real)) := hK
      _ ≤ 16 * theta₁ ^ (-(2 : Real)) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos htheta₁ hbeta
            (by norm_num : -(2 : Real) ≤ 0)) (by norm_num)
  have hcardNat : (lemma134SpectrumUnion B).card ≤
      ∑ i : Fin q₀,
        (section7Spectrum (B i) (lemma134Density (B i))).card := by
    exact Finset.card_biUnion_le
  have hcardReal : ((lemma134SpectrumUnion B).card : Real) ≤
      ∑ i : Fin q₀,
        ((section7Spectrum (B i) (lemma134Density (B i))).card : Real) := by
    exact_mod_cast hcardNat
  calc
    ((lemma134SpectrumUnion B).card : Real) ≤
        ∑ i : Fin q₀,
          ((section7Spectrum (B i) (lemma134Density (B i))).card : Real) :=
      hcardReal
    _ ≤ ∑ _i : Fin q₀, 16 * theta₁ ^ (-(2 : Real)) := by
      exact Finset.sum_le_sum fun i _ => hper i
    _ = (q₀ : Real) * (16 * theta₁ ^ (-(2 : Real))) := by simp
    _ ≤ (q : Real) * (16 * theta₁ ^ (-(2 : Real))) := by
      gcongr
    _ = 16 * q * theta₁ ^ (-(2 : Real)) := by ring

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
  classical
  let theta₁ := section13ThetaOne theta
  let K := lemma134SpectrumUnion B
  let exponent : Real := theta₁ ^ 2 / (16 * (q : Real))
  let delta : Real := theta₁ / (32 * Real.pi * (l : Real))
  have htheta₁ : 0 < theta₁ := lemma134_thetaOne_pos theta htheta
  have hqR : (0 : Real) < q := by exact_mod_cast hq
  have hlR : (0 : Real) < l := by exact_mod_cast hl
  have hdelta : 0 < delta := by
    unfold delta
    positivity
  have hdeltaOne : delta ≤ 1 := by
    unfold delta
    apply (div_le_one₀ (by positivity :
      (0 : Real) < 32 * Real.pi * (l : Real))).2
    have htheta₁One' : theta₁ ≤ 1 := htheta₁One
    have hlOne : (1 : Real) ≤ l := by exact_mod_cast hl
    calc
      theta₁ ≤ 1 := htheta₁One'
      _ ≤ 32 * Real.pi * 1 := by nlinarith [Real.pi_gt_three]
      _ ≤ 32 * Real.pi * (l : Real) :=
        mul_le_mul_of_nonneg_left hlOne (by positivity)
  by_cases hKempty : K = ∅
  · refine ⟨1, ?_, one_ne_zero⟩
    simp [K, hKempty, bohr]
  · have hKne : K.Nonempty := Finset.nonempty_iff_ne_empty.mpr hKempty
    have hKposNat : 0 < K.card := Finset.card_pos.mpr hKne
    have hKpos : (0 : Real) < K.card := by exact_mod_cast hKposNat
    have hKcard := lemma134_spectrum_union_card B sigma theta₁ htheta₁
      hq₀q hBlarge hFreiman
    have hthetaSq : 0 < theta₁ ^ 2 := sq_pos_of_pos htheta₁
    have hnegPow : theta₁ ^ (-(2 : Real)) = (theta₁ ^ 2)⁻¹ := by
      rw [show (-(2 : Real)) = -((2 : Nat) : Real) by norm_num,
        Real.rpow_neg htheta₁.le, Real.rpow_natCast]
    have hcardScaled : (K.card : Real) * theta₁ ^ 2 ≤
        16 * (q : Real) := by
      calc
        (K.card : Real) * theta₁ ^ 2 ≤
            (16 * (q : Real) * theta₁ ^ (-(2 : Real))) *
              theta₁ ^ 2 :=
          mul_le_mul_of_nonneg_right hKcard hthetaSq.le
        _ = 16 * (q : Real) := by
          rw [hnegPow]
          field_simp
    have hexponentCard : exponent ≤ ((K.card : Real))⁻¹ := by
      unfold exponent
      rw [← one_div]
      apply (div_le_div_iff₀ (by positivity : (0 : Real) < 16 * q) hKpos).2
      simpa only [one_mul, mul_comm] using hcardScaled
    have hrpowMono :
        (N : Real) ^ (-(((K.card : Nat) : Real)⁻¹)) ≤
          (N : Real) ^ (-exponent) := by
      apply Real.rpow_le_rpow_of_exponent_le
      · exact_mod_cast (Fact.out : Nat.Prime N).one_le
      · exact neg_le_neg hexponentCard
    have hscale' : (l : Real) <
        theta₁ / (64 * Real.pi) * (N : Real) ^ exponent := by
      simpa only [lemma134Scale, theta₁, exponent] using hlScale
    have htarget :
        2 * (N : Real) ^ (-exponent) < delta := by
      have hT : 0 < (N : Real) ^ exponent :=
        Real.rpow_pos_of_pos (by exact_mod_cast NeZero.pos N) _
      have hden : (0 : Real) < 32 * Real.pi * (l : Real) := by positivity
      rw [Real.rpow_neg (by positivity : (0 : Real) ≤ N)]
      change 2 * ((N : Real) ^ exponent)⁻¹ < theta₁ / _
      rw [← div_eq_mul_inv]
      apply (div_lt_div_iff₀ hT hden).2
      calc
        2 * (32 * Real.pi * (l : Real)) =
            (64 * Real.pi) * (l : Real) := by ring
        _ < (64 * Real.pi) *
            (theta₁ / (64 * Real.pi) * (N : Real) ^ exponent) :=
          mul_lt_mul_of_pos_left hscale' (by positivity)
        _ = theta₁ * (N : Real) ^ exponent := by
          field_simp
    have hthreshold :
        2 * (N : Real) ^
            (-(1 / ((K.card : Nat) : Real))) < delta := by
      have heq : -(1 / ((K.card : Nat) : Real)) =
          -(((K.card : Nat) : Real)⁻¹) := by rw [one_div]
      rw [heq]
      exact (mul_le_mul_of_nonneg_left hrpowMono (by norm_num)).trans_lt htarget
    obtain ⟨_, hnonzero⟩ := lemma_7_7_holds N K delta
      (Fact.out : Nat.Prime N).two_le hdelta hdeltaOne
    obtain ⟨d, hdK, hdne⟩ := hnonzero hKne hthreshold
    exact ⟨d, by simpa only [K, delta, theta₁] using hdK,
      bne_iff_ne.mp hdne⟩

/-! ### Lemma 13.4 -/

/-- **Gowers, Lemma 13.4**, with the prime-modulus and quantitative
`theta`-range hypotheses restored in the statement. -/
theorem lemma_13_4_holds : lemma_13_4 := by
  intro N _ S theta hprime htheta hthetaBound
  classical
  letI : Fact N.Prime := ⟨hprime⟩
  obtain ⟨q₀, B, sigma, G, hGcard, hFreiman, hBlarge,
      hq₀Bound, hcover⟩ :=
    corollary_13_3_holds N S.A theta hprime htheta
  let q := max 1 q₀
  have hq : 0 < q := by
    exact (by norm_num : 0 < 1).trans_le (Nat.le_max_left 1 q₀)
  have hq₀q : q₀ ≤ q := Nat.le_max_right 1 q₀
  have hqBound : (q : Real) ≤ section13QBound theta := by
    have hOneBound := lemma134_qBound_one_le S theta htheta hthetaBound
    simpa only [q, Nat.cast_max, Nat.cast_one] using
      (max_le hOneBound hq₀Bound)
  have htheta₁ : 0 < section13ThetaOne theta :=
    lemma134_thetaOne_pos theta htheta
  have htheta₁One : section13ThetaOne theta ≤ 1 :=
    lemma134_thetaOne_le_one S theta htheta hthetaBound
  let m := lemma134Floor N theta q
  by_cases hmSmall : m ≤ 1
  · exact lemma134_empty_stage S theta q hprime htheta hq hqBound
      (by simpa only [m] using hmSmall)
  · have hmLarge : 2 ≤ m := by omega
    let l := m - 1
    obtain ⟨hl, hlScale, hlN⟩ :=
      lemma134_floor_pred_bounds theta htheta htheta₁One hq
        (by simpa only [m] using hmLarge)
    obtain ⟨d, hdBohr, hd⟩ := lemma134_exists_common_step B sigma theta htheta
      htheta₁One hq hq₀q hl hlScale hBlarge hFreiman
    obtain ⟨s, havg⟩ :=
      lemma134_exists_progression_average S G d hd hlN
    let P := lemma134Progression d s l
    let H := P.carrier ∩ G
    have hproper : P.IsProper := by
      exact lemma134_progression_proper d s hd hlN
    have hgoodG : S.alpha ^ 32 * (N : Real) ^ 32 / 4 ≤
        goodHeightWeight S G :=
      lemma134_good_exceptional_lower S theta G htheta hthetaBound hGcard
    have hpFirst := lemma134_piece_affine_on_progression B sigma
      (section13ThetaOne theta) hprime htheta₁ hl hBlarge hFreiman d s hdBohr
    choose a₀ b₀ haffine using hpFirst
    let a : Fin q → ZMod N := fun j =>
      if hj : (j : Nat) < q₀ then a₀ ⟨j, hj⟩ else 0
    let b : Fin q → ZMod N := fun j =>
      if hj : (j : Nat) < q₀ then b₀ ⟨j, hj⟩ else 0
    let D : Stage134Data N :=
      { q := q
        m := m
        P := P
        H := H
        a := a
        b := b }
    refine ⟨D, hq, ?_, hproper, ?_, hqBound, ?_, ?_, ?_, ?_⟩
    · change d != 0
      exact bne_iff_ne.mpr hd
    · intro h hh
      exact (Finset.mem_inter.mp hh).1
    · simpa only [D, m, lemma134Scale] using
        lemma134_floor_spec N theta q htheta
    · right
      change l + 1 = m
      omega
    · have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
      have hsource :
          (l : Real) * (S.alpha ^ 32 * (N : Real) ^ 32 / 4) ≤
            (N : Real) * goodHeightWeight S H := by
        calc
          (l : Real) * (S.alpha ^ 32 * (N : Real) ^ 32 / 4) ≤
              (l : Real) * goodHeightWeight S G :=
            mul_le_mul_of_nonneg_left hgoodG (by positivity)
          _ ≤ (N : Real) * goodHeightWeight S H := by
            simpa only [H, P] using havg
      apply le_of_mul_le_mul_left (a := (N : Real))
      · calc
          (N : Real) *
              (S.alpha ^ 32 * (N : Real) ^ 31 * (l : Real) / 8) =
              (l : Real) * (S.alpha ^ 32 * (N : Real) ^ 32 / 8) := by ring
          _ ≤ (l : Real) * (S.alpha ^ 32 * (N : Real) ^ 32 / 4) := by
            have hnonneg : 0 ≤
                (l : Real) * (S.alpha ^ 32 * (N : Real) ^ 32) := by
              positivity
            nlinarith
          _ ≤ (N : Real) * goodHeightWeight S H := hsource
      · exact hN
    · intro h hh r hr
      have hh' := Finset.mem_inter.mp hh
      obtain ⟨i, hiB, hir⟩ := hcover h hh'.2 r hr
      let j : Fin q := Fin.castLE hq₀q i
      refine ⟨j, ?_⟩
      have hsigma := haffine i h
        (Finset.mem_inter.mpr ⟨hiB, hh'.1⟩)
      rw [hir, hsigma]
      simp [D, a, b, j, Fin.castLE]

end LeanProofs.GowersSzemeredi
