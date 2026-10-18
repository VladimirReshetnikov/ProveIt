import GowersSzemeredi.Proofs16PolyCoverTwo
import GowersSzemeredi.Proofs18LengthSixExponents

/-! Uniform classes with power controls: the interface of route (II) in every
dimension (Notes L.6, E1).

A `PowerUniformClass k V dC dE dT` is a downward closed class `U` of
`k`-dimensional relations, containing `∅`, at each pair of parameters `(θ, γ)`,
with:
* `decomp`: above the threshold `(V·2/(γθ))^dT`, every product relation `Γ`
  of size `≤ γ⁻²N^k` has a good set `J`, with `|J| ≥ (1-θ)N^k`, on which
  `Γ` restricts to a member. `J` depends on `Γ` alone.
* `cover`: the union of any `n` members is multiply multilinear, with count
  `w^dC` and width exponent `w^(-dE)`, where
  `w = uniformBase V n θ γ ρ = (n+1)·V·2/(γθρ)`.

The power envelopes are monotone in `n`, as the slice providers of the
family piece cover need (`abstract_family_piece_cover_with`). The degrees
are symbolic, as the degree budget of Notes L.6 needs.

* `PowerUniformClass.polyCoverAt`: a class gives `PolyCoverAt k` at degree
  `D ≥ dC, dE, dT + k + 1`. Small moduli are covered by singleton boxes.
* `PowerUniformClass.theorem162At`: hence Theorem 16.2 in dimension `k`
  whenever `D ≤ 2^(2^(k+8))` and `2V ≤ 2^(2^(2^(k+6)) - 1)`;
  `PowerUniformClass.theorem162At_tower` allows `D ≤ 2^(2^(2^(k+6)))`.
* `powerUniformClass_two`: dimension two is a class at degrees
  `(2^89, 2^130, 2^45)`, for any `V` bounding the constants of the family
  Lemma 16.6 in dimension one. It uses the pieces `PolyPieceTwo` and the
  bounds of `Proofs16UniformCoverTwoBounds`.

`PowerUniformClass.theorem162At`, `PowerUniformClass.theorem162At_tower`,
`nPieces_le_base` and `powerUniformClass_two` are in
`Proofs16PowerUniformClassSide`, outside the final route. -/
set_option autoImplicit false
set_option exponentiation.threshold 1024
noncomputable section
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-- The base `(n+1)·V·2/(γθρ)` of the power controls of a family of `n` members. -/
def uniformBase (V : Real) (n : Nat) (theta gamma rho : Real) : Real :=
  ((n : Real) + 1) * V * (2 / (gamma * theta * rho))

/-- **A uniform class of `k`-dimensional relations**, with threshold `Thr θ γ`
and family controls `Cnt θ γ n`, `Exp θ γ n` for `n` members. -/
structure UniformClassWith (k : Nat) (Thr : Real → Real → Real)
    (Cnt Exp : Real → Real → Nat → Real → Real) where
  U : (N : Nat) → [NeZero N] → Real → Real → Finset (Point N k × ZMod N) → Prop
  mono : ∀ (N : Nat) [NeZero N] (theta gamma : Real) (Gamma Gamma' : Finset (Point N k × ZMod N)),
    Gamma ⊆ Gamma' → U N theta gamma Gamma' → U N theta gamma Gamma
  empty : ∀ (N : Nat) [NeZero N] (theta gamma : Real), U N theta gamma ∅
  decomp : ∀ (theta gamma : Real), 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], Thr theta gamma ≤ (N : Real) →
    ∀ Gamma : Finset (Point N k × ZMod N),
      (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ k →
      RelationProductProperty gamma Gamma →
      ∃ J : Finset (Point N k), (1 - theta) * (N : Real) ^ k ≤ J.card ∧
        U N theta gamma (restrictRelation Gamma J)
  cover : ∀ (theta gamma : Real), 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    ∀ (N : Nat) [NeZero N] [Fact N.Prime] (n : Nat) (Gamma : Fin n → Finset (Point N k × ZMod N)),
      (∀ i, U N theta gamma (Gamma i)) →
      MultiplyLinearWith (Cnt theta gamma n) (Exp theta gamma n) (Finset.univ.biUnion Gamma)

/-- **A uniform class with power controls**: threshold `(V·2/(γθ))^dT`, count
`w^dC` and width exponent `w^(-dE)` in the base `w = uniformBase V n θ γ ρ`. -/
abbrev PowerUniformClass (k : Nat) (V : Real) (dC dE dT : Nat) :=
  UniformClassWith k (fun theta gamma => (V * (2 / (gamma * theta))) ^ dT)
    (fun theta gamma n rho => uniformBase V n theta gamma rho ^ dC)
    (fun theta gamma n rho => (uniformBase V n theta gamma rho ^ dE)⁻¹)

theorem uniformBase_facts {V : Real} (hV : 1 ≤ V) (n : Nat) {theta gamma rho : Real}
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho)
    (hr1 : rho ≤ 1) :
    2 / (gamma * theta) ≤ uniformBase V n theta gamma rho ∧
      rho⁻¹ ≤ uniformBase V n theta gamma rho ∧
      (n : Real) + 1 ≤ uniformBase V n theta gamma rho ∧
      V * (2 / (gamma * theta)) ≤ uniformBase V n theta gamma rho ∧
      2 ≤ uniformBase V n theta gamma rho := by
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hri : 1 ≤ rho⁻¹ := one_le_inv₀ hr |>.mpr hr1
  have hsplit : 2 / (gamma * theta * rho) = 2 / (gamma * theta) * rho⁻¹ := by
    field_simp
  set u := 2 / (gamma * theta) with hu
  clear_value u
  have hn1 : (1 : Real) ≤ (n : Real) + 1 := by
    have : (0 : Real) ≤ n := Nat.cast_nonneg n
    linarith
  have hnV : (1 : Real) ≤ ((n : Real) + 1) * V := one_le_mul_of_one_le_of_one_le hn1 hV
  have hur : u ≤ u * rho⁻¹ := le_mul_of_one_le_right (by linarith) hri
  have hw : u * rho⁻¹ ≤ uniformBase V n theta gamma rho := by
    unfold uniformBase
    rw [hsplit]
    exact le_mul_of_one_le_left (by positivity) hnV
  have hVu : V * u ≤ uniformBase V n theta gamma rho := by
    unfold uniformBase
    rw [hsplit]
    have h1 : V * u ≤ ((n : Real) + 1) * V * u := by
      rw [mul_assoc]
      exact le_mul_of_one_le_left (mul_nonneg (by linarith) (by linarith)) hn1
    calc V * u ≤ ((n : Real) + 1) * V * u := h1
      _ ≤ ((n : Real) + 1) * V * (u * rho⁻¹) :=
        mul_le_mul_of_nonneg_left hur (by positivity)
  have hnw : (n : Real) + 1 ≤ uniformBase V n theta gamma rho := by
    have h1 : (n : Real) + 1 ≤ ((n : Real) + 1) * V := le_mul_of_one_le_right (by linarith) hV
    have h2 : ((n : Real) + 1) * V ≤ ((n : Real) + 1) * V * u :=
      le_mul_of_one_le_right (by positivity) (by linarith)
    have h3 : ((n : Real) + 1) * V * u ≤ uniformBase V n theta gamma rho := by
      unfold uniformBase
      rw [hsplit]
      exact mul_le_mul_of_nonneg_left hur (by positivity)
    linarith
  refine ⟨hur.trans hw, ?_, hnw, hVu, hu2.trans (hur.trans hw)⟩
  have : rho⁻¹ ≤ u * rho⁻¹ := le_mul_of_one_le_left (by positivity) (by linarith)
  exact this.trans hw

/-- The coarse count and capped width fit the same uniform power budget. -/
theorem uniformBase_small_controls {V gamma theta rho : Real} (hV : 1 ≤ V)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hr : 0 < rho) (hr1 : rho ≤ 1) {k dT D : Nat} (hDT : dT + k + 1 ≤ D) :
    ((3 ^ k * ⌈(V * (2 / (gamma * theta))) ^ dT⌉₊ : Nat) : Real) ≤
        uniformBase V 1 theta gamma rho ^ D ∧
      (uniformBase V 1 theta gamma rho ^ D)⁻¹ ≤
        section16CappedWidthExponent (uniformBase V 1 theta gamma rho ^ D)⁻¹
          ((V * (2 / (gamma * theta))) ^ dT) := by
  obtain ⟨hu2, huw, -⟩ := prod_scale_radius_bounds hg hg1 ht ht1 hr hr1
  have hVW := mul_le_mul hV (hu2.trans huw)
    (by norm_num : (0 : Real) ≤ 2) (by linarith only [hV] : 0 ≤ V)
  have hw3 : 3 ≤ uniformBase V 1 theta gamma rho := by
    unfold uniformBase
    norm_num only [Nat.cast_one]
    nlinarith only [hVW]
  obtain ⟨-, -, -, hbase, hw2⟩ := uniformBase_facts hV 1 hg hg1 ht ht1 hr hr1
  set w := uniformBase V 1 theta gamma rho
  have hw1 : 1 ≤ w := le_trans (by norm_num) hw2
  have hw0 : 0 ≤ w := zero_le_one.trans hw1
  have hb0 : 0 ≤ V * (2 / (gamma * theta)) :=
    mul_nonneg (zero_le_one.trans hV) (div_pos (by norm_num) (mul_pos hg ht)).le
  have hT := pow_le_pow_left₀ hb0 hbase dT
  constructor
  · have hceil := ceil_le_pow_succ hw2 (pow_nonneg hb0 dT) hT
    rw [Nat.cast_mul, Nat.cast_pow]
    calc (3 : Real) ^ k * (⌈(V * (2 / (gamma * theta))) ^ dT⌉₊ : Real)
        ≤ w ^ k * w ^ (dT + 1) :=
          mul_le_mul (pow_le_pow_left₀ (by norm_num) hw3 k) hceil
            (Nat.cast_nonneg _) (pow_nonneg hw0 _)
      _ = w ^ (dT + k + 1) := by rw [← pow_add]; congr 1 <;> omega
      _ ≤ w ^ D := pow_le_pow_right₀ hw1 hDT
  · have he : 0 < (w ^ D)⁻¹ := inv_pos.mpr (pow_pos (lt_of_lt_of_le (by norm_num) hw2) _)
    have hcap := capped_inv_le_pow (r := D) (n := dT) hw2 he
      (by simpa only [inv_inv] using (le_rfl : w ^ D ≤ w ^ D)) (le_exp_pow_of_le_pow hT) (by omega)
    have h := inv_anti₀ (inv_pos.mpr (section16CappedWidthExponent_pos he)) hcap
    simpa only [inv_inv] using h

theorem restrictRelation_univ {N k : Nat} [NeZero N] (Gamma : Finset (Point N k × ZMod N)) :
    restrictRelation Gamma Finset.univ = Gamma := by
  unfold restrictRelation
  exact Finset.filter_true_of_mem fun z _ => Finset.mem_univ _

/-! ### From a class to `PolyCoverAt` and Theorem 16.2 -/

/-- **A uniform class gives `PolyCoverAt k`** at any degree `D ≥ dC, dE, dT + k + 1`. -/
theorem PowerUniformClass.polyCoverAt {k : Nat} {V : Real} {dC dE dT : Nat}
    (C : PowerUniformClass k V dC dE dT) (hk : 0 < k) (hV : 1 ≤ V) {D : Nat} (hDC : dC ≤ D)
    (hDE : dE ≤ D) (hDT : dT + k + 1 ≤ D) :
    PolyCoverAt k (fun gamma theta rho => uniformBase V 1 theta gamma rho ^ D)
      (fun gamma theta rho => (uniformBase V 1 theta gamma rho ^ D)⁻¹) := by
  intro N _ _ gamma theta hg hg1 ht ht1 Gamma hsize hprod
  have hfacts := fun rho (hr : 0 < rho) (hr1 : rho ≤ 1) =>
    uniformBase_facts hV 1 hg hg1 ht ht1 hr hr1
  by_cases hN : (V * (2 / (gamma * theta))) ^ dT ≤ (N : Real)
  · obtain ⟨J, hJ, hU⟩ := C.decomp theta gamma ht ht1 hg hg1 N hN Gamma hsize hprod
    refine ⟨J, hJ, ?_⟩
    have hcov := C.cover theta gamma ht ht1 hg hg1 N 1 (fun _ => restrictRelation Gamma J)
      (fun _ => hU)
    refine (hcov.subset ?_).weaken ?_ ?_ ?_
    · intro z hz
      exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ _, hz⟩
    · intro rho hr hr1
      exact pow_le_pow_right₀ (le_trans (by norm_num) (hfacts rho hr hr1).2.2.2.2) hDC
    · intro rho hr _
      have := (hfacts rho hr (by assumption)).2.2.2.2
      positivity
    · intro rho hr hr1
      have hw2 := (hfacts rho hr hr1).2.2.2.2
      exact inv_anti₀ (pow_pos (by linarith) _)
        (pow_le_pow_right₀ (by linarith) hDE)
  · have hNlt : (N : Real) < (V * (2 / (gamma * theta))) ^ dT := lt_of_not_ge hN
    refine ⟨Finset.univ, ?_, ?_⟩
    · have hc : ((Finset.univ : Finset (Point N k)).card : Real) = (N : Real) ^ k := by
        simp [Point, ZMod.card]
      rw [hc]
      have : (0 : Real) ≤ (N : Real) ^ k := by positivity
      nlinarith
    have hcov := multiplyLinearWith_of_small_modulus hk hNlt
      (restrictRelation Gamma Finset.univ)
      (fun rho => uniformBase V 1 theta gamma rho ^ D)
      (fun rho => (uniformBase V 1 theta gamma rho ^ D)⁻¹)
      (fun s hs hs1 => by have := (hfacts s hs hs1).2.2.2.2; positivity)
    refine hcov.weaken ?_ ?_ ?_
    · intro rho hr hr1
      exact max_le le_rfl (uniformBase_small_controls hV hg hg1 ht ht1 hr hr1 hDT).1
    · intro rho hr hr1
      have := (hfacts rho hr hr1).2.2.2.2
      positivity
    · intro rho hr hr1
      exact (uniformBase_small_controls hV hg hg1 ht ht1 hr hr1 hDT).2

end LeanProofs.GowersSzemeredi
