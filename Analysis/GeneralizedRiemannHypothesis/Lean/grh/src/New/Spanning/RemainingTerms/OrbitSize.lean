import New.Spanning.Unfolding.Terms

/-!
# Near terms in the filling theorem: the bound for an orbit, the tail and the open-cell term

This file defines the size allotted to a near orbit of terms `γ` and bounds the tail and the
open-cell term by it. The data are `S : New.Filling E 𝔰` for a shape `𝔰`, with the size hypotheses
`New.Filling.IsAdmissible`, which compare all constants with powers of the large parameter `b`.
For admissible data, if `S.termDiscNorm γ` is at least 1, then the orbit bound at the top cell
rank, with that norm as gauge, bounds the open-cell term of `γ` and, if `γ` is near, also the tail.
Here `k = |κ|`, `f` is the number of infinite places and `τ = b^(kf/4)`.

## Main definitions and results

* `New.Filling.cellRankSecondMoment`: the second moment D_j against which the size of a term of cell
  rank j is measured. It is the main second moment at the top cell rank and τ^(−16) = b^(−4kf) times
  the identity second moment below it.
* `New.Filling.orbitBound`: the bound allotted to a near orbit, as a function of its cell rank j and
  of its gauge x. It is τ² (D_j / (n_p (M^(2j'f) x)^k))^(1/2) with j' = min ϱ j, in units of the
  covolume ν.
* `New.Filling.IsNear.inv_pow_le_orbitBound`, `New.Filling.prod_pairingBoundSq_le`: the two bounds
  by the orbit bound at the top cell rank, for the tail and for the open-cell term.

Notions from other files:
* `New.Filling.termDisc`: 𝗀(γ) = |D_{ϱ+1}|² − N²|D_ϱ|², with D_l the leading minors of
  `New.Filling.frameProducts γ`.
* `New.Filling.mainSecondMoment`, `New.Filling.identitySecondMoment`: the numbers
  sourceDim² / (besselDegree · mass), with the mass of the genus of the standard lattice, and
  sourceDim times the order of the reduced image of the Bessel subgroup `besselS`.
* `New.Filling.unipotentCovolume`: the number ν that serves as covolume of the unipotent group.
* `New.Filling.IsNear` (from `New.Spanning.Unfolding.Terms`): `γ` joins two boxed archimedean
  points.
* `New.Filling.termDiscNorm`, `New.Filling.pairCountScale` (from `New.Spanning.Unfolding.Terms`):
  the product over the infinite places of |𝗀(γ)|_v, and the number n_p = #R̄₀ n_X N^(−kf).
-/

noncomputable section

section OrbitBound

open Real Finset Fintype ComplexOrder

namespace New.Filling

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} (S : Filling E 𝔰)

/-- The second moment `D_j` against which the size of a term of cell rank `j` is measured:
`mainSecondMoment` at the top cell rank `ϱ + 1`, and `τ ^ (-16)` times `identitySecondMoment` below
it, where `τ` is `tailScale`. -/
noncomputable def cellRankSecondMoment (j : Fin (𝔰.ϱ + 2)) : ℝ :=
  if 𝔰.ϱ < j then S.mainSecondMoment else S.identitySecondMoment / S.tailScale ^ 16

/-- The bound `τ² (D_j / (n_p (M ^ (2 j' f) x) ^ k)) ^ (1 / 2)`, `j' = min ϱ j`, for one near orbit
of terms under left and right multiplication by the groups `classUnipotent₀`, of cell rank `j` and
gauge `x`, in units of the covolume `unipotentCovolume`. Here `τ` is `tailScale`, `D_j` is
`cellRankSecondMoment j`, `n_p` is `pairCountScale`, `M` is the level `S.M`, `k` is the rank of `X₀`
and `f` is the number of infinite places. -/
noncomputable def orbitBound (j : Fin (𝔰.ϱ + 2)) (x : ℝ) : ℝ :=
  S.tailScale ^ 2 * √(S.cellRankSecondMoment j /
    (S.pairCountScale * (S.M ^ (2 * min 𝔰.ϱ j * numInfPlaces E) * x) ^ 𝔰.k))

variable {S} {γ : S.G E}

/-- At every infinite place the absolute value of `S.termDisc γ = |D_n|² - N² |D_{n-1}|²` is at most
`|D_n|²`, where `D_l` is the leading minor of order `l` of the matrix `S.frameProducts γ` of
products of the frame with its image under `γ`, and `n = ϱ + 1`. -/
lemma norm_map_termDisc_le (v : NumberField.InfinitePlace E) :
    ‖Φ v (S.termDisc γ)‖ ≤ ‖Φ v (leadingMinor (S.frameProducts γ) ⊤)‖ ^ 2 := by
  show _ ≤ ‖Φ v (S.frameProducts γ).det‖ ^ 2
  have h_eq : ‖Φ v (S.termDisc γ)‖ = ‖Φ v (S.frameProducts γ).det‖ ^ 2 -
      (S.N * ‖Φ v (leadingMinor (S.frameProducts γ) 𝔰.top.castSucc)‖) ^ 2 := by
    rw [← Complex.ofReal_inj, ← map_termDisc_eq_norm]
    simp [frameDisc, Complex.mul_conj', mul_pow]
  exact h_eq.le.trans (sub_le_self _ (sq_nonneg _))

/-- For admissible data with size parameter `b = S.b` and a near term `γ` (see `IsNear`), the
product of the absolute values of `S.termDisc γ` over the `f` infinite places is at most
`b ^ (270 n² f)`, `n = ϱ + 1`. -/
lemma IsNear.termDiscNorm_le [S.IsAdmissible] (h_near : S.IsNear γ) :
    S.termDiscNorm γ ≤ S.b ^ (270 * 𝔰.n ^ 2 * numInfPlaces E) := by
  grw [termDiscNorm, Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun v _ ↦
    (norm_map_termDisc_le v).trans (h_near.norm_map_leadingMinor_sq_le ⊤ v)]
  rw [prod_const, Finset.card_univ, ← pow_mul]

/-- The second moment `D_j` against which the size of a term of cell rank `j` is measured is
nonnegative. -/
lemma cellRankSecondMoment_nonneg [S.IsAdmissible] (j : Fin (𝔰.ϱ + 2)) :
    0 ≤ S.cellRankSecondMoment j := by
  rw [cellRankSecondMoment]
  split_ifs <;> positivity [mainSecondMoment_nonneg (S := S), identitySecondMoment_nonneg (S := S),
    two_le_tailScale (S := S)]

/-- At the top cell rank the orbit bound at `x` is
`τ² (mainSecondMoment / (pairCountScale M ^ (2 ϱ f k) x ^ k)) ^ (1 / 2)`, where `τ` is `tailScale`,
`M` is the level and `f` is the number of infinite places. -/
lemma orbitBound_top [S.IsAdmissible] (x : ℝ) : S.orbitBound ⊤ x = S.tailScale ^ 2 *
    √(S.mainSecondMoment / (S.pairCountScale *
      (S.M ^ (2 * 𝔰.ϱ * numInfPlaces E * 𝔰.k) * x ^ 𝔰.k))) := by
  rw [orbitBound, cellRankSecondMoment, ite_eq_left (by simp), min_eq_left (by simp), mul_pow,
    ← pow_mul]

/-- For admissible data, `pairCountScale` is at most the main second moment. -/
lemma pairCountScale_le_mainSecondMoment [S.IsAdmissible] :
    S.pairCountScale ≤ S.mainSecondMoment := by
  have : Nonempty 𝔰.κ := ⟨𝔰.k₀⟩
  -- `pairCountScale ≤ identitySecondMoment ≤ τ⁻⁴⁴ mainSecondMoment`, and `τ = tailScale ≥ 1`
  grw [pairCountScale, ← tailScale_pow_mul_identitySecondMoment_le, identitySecondMoment, sourceDim,
    ← S.N_prime.one_le, ← one_le_tailScale, ← NeZero.one_le (n := card S.BesselCoord)]
  simp

/-- Let the data be admissible, with size parameter `b = S.b`. Let `γ` be near, that is, some
archimedean point `y` has both `y` and `γ⁻¹ y` in `boxedPoints`, and let `x = termDiscNorm γ` be the
product of the absolute values of `termDisc γ` over the infinite places. If `1 ≤ x`, then the bound
`orbitBound ⊤ x` allotted to an orbit of the top cell rank `ϱ + 1` is at least `b ^ (-k³ f)`. -/
lemma IsNear.inv_pow_le_orbitBound [S.IsAdmissible] (h_near : S.IsNear γ)
    (h_one_le : 1 ≤ S.termDiscNorm γ) :
    (S.b ^ (𝔰.k ^ 3 * numInfPlaces E))⁻¹ ≤ S.orbitBound ⊤ (S.termDiscNorm γ) := by
  have hb : 1 ≤ S.b := S.one_le_b
  have hM : 2 ≤ S.M := two_le_M
  have h_pairs : 0 < S.pairCountScale := pairCountScale_pos
  have h_exponent : 23 * (2 * 𝔰.ϱ * numInfPlaces E * 𝔰.k) + 270 * 𝔰.n ^ 2 * numInfPlaces E * 𝔰.k ≤
      𝔰.k ^ 3 * numInfPlaces E * 2 := by
    obtain ⟨k₀, hk₀ : 1000 * (2 * 𝔰.ϱ + 2) ^ 9 + k₀ = 𝔰.k⟩ := S.pow_le_k.dest
    rw [← hk₀]
    lia
  grw [orbitBound_top, ← pairCountScale_le_mainSecondMoment, ← one_le_tailScale, one_pow, one_mul]
  -- compare the squares: the pair count cancels
  refine le_sqrt_of_sq_le ?_
  have h_den : (S.M : ℝ) ^ (2 * 𝔰.ϱ * numInfPlaces E * 𝔰.k) * S.termDiscNorm γ ^ 𝔰.k ≤
      S.b ^ (𝔰.k ^ 3 * numInfPlaces E * 2) := by
    grw [M_le_b_pow, h_near.termDiscNorm_le, ← pow_mul, ← pow_mul, ← pow_add,
      pow_le_pow_right₀ hb h_exponent]
  rw [div_mul_cancel_left₀ h_pairs.ne', inv_pow, ← pow_mul]
  exact inv_anti₀ (by positivity) h_den

variable (S) in
/-- The factor of the product over the infinite places of the open-cell bounds `pairingBoundSq` at
`S.ratToInf γ v` that does not depend on `γ`: the product with the absolute values of
`S.termDisc γ` replaced by `1` (see `prod_pairingBoundSq_eq`). -/
noncomputable def pairingBoundConst : ℝ :=
  ∏ v : NumberField.InfinitePlace E,
    (S.frameBoxRadius ^ (9 * 𝔰.n) / (∏ a : Fin 𝔰.n, S.frameScaleSq v a) ^ 2) ^ (10 ^ 5 * 𝔰.n ^ 4) *
      ((card (S.besselSystem v).Index : ℝ) ^ 2 / ((S.besselSystem v).deg * 𝔰.openCellConst *
        ((∏ a : Fin 𝔰.n, S.frameScaleSq v a) ^ 2 / 2) ^ (𝔰.k - 1)))

/-- For every rational `γ`, the product over the infinite places `v` of the open-cell bounds
`pairingBoundSq` is `pairingBoundConst / x ^ (10 ^ 5 n ^ 4 + (k - 1))`, where `x = termDiscNorm γ`,
`n = ϱ + 1` and `k` is the rank of `X₀`. -/
lemma prod_pairingBoundSq_eq :
    ∏ v : NumberField.InfinitePlace E,
        pairingBoundSq (S.ratToInf γ v) (S.besselSystem v).deg S.frameBoxRadius
          (card (S.besselSystem v).Index) =
      S.pairingBoundConst / S.termDiscNorm γ ^ (10 ^ 5 * 𝔰.n ^ 4 + (𝔰.k - 1)) := by
  rw [pairingBoundConst, termDiscNorm, ← prod_pow, ← prod_div_distrib]
  refine prod_congr rfl fun v _ ↦ ?_
  rw [pairingBoundSq, gramDiscReal_realFrameGram_ratToInf]
  simp only [div_eq_mul_inv, mul_inv, mul_pow, pow_add, inv_pow]
  ring

/-- Let the data be admissible, with size parameter `b = S.b`, let `n = ϱ + 1` be the number of
frame vectors and `k` the rank of `X₀`. At an infinite place `v` let
`s_a = S.frameScaleSq v a = (S.realM v) ^ (2 (ϱ - a)) / N` be the squared scale of the frame vector
of index `a`. The product `s` of the `s_a` lies between `b ^ (-60 n²)` and `b ^ (46 n²)`, and
`∏ s_a ^ (k + 2 (ϱ - a))`, the factor of `frameScaleProd` at `v`, is at most `s ^ k b ^ (92 n³)`. -/
lemma prod_frameScaleSq_bounds [S.IsAdmissible] (v : NumberField.InfinitePlace E) :
    (S.b ^ (60 * 𝔰.n ^ 2))⁻¹ ≤ ∏ a : Fin 𝔰.n, S.frameScaleSq v a ∧
    ∏ a : Fin 𝔰.n, S.frameScaleSq v a ≤ S.b ^ (46 * 𝔰.n ^ 2) ∧
    ∏ a : Fin 𝔰.n, S.frameScaleSq v a ^ (𝔰.k + 2 * (𝔰.ϱ - a)) ≤
      (∏ a : Fin 𝔰.n, S.frameScaleSq v a) ^ 𝔰.k * S.b ^ (92 * 𝔰.n ^ 3) := by
  have hb : 1 ≤ S.b := S.one_le_b
  have hN : (1 : ℝ) ≤ S.N := Nat.one_le_cast.2 S.N_prime.one_le
  have h_lower (a : Fin 𝔰.n) : (S.b ^ (60 * 𝔰.n))⁻¹ ≤ S.frameScaleSq v a := by
    grw [frameScaleSq, ← pow_abs_two_mul, ← one_le_abs_realM, one_pow, N_le, one_div]
  have h_upper (a : Fin 𝔰.n) : S.frameScaleSq v a ≤ S.b ^ (46 * 𝔰.n) := by
    grw [frameScaleSq, ← pow_abs_two_mul, abs_realM_le, ← hN, div_one, ← pow_mul]
    exact pow_le_pow_right₀ hb (by lia)
  have h_pos (a : Fin 𝔰.n) : 0 ≤ S.frameScaleSq v a := (S.frameScaleSq_pos v a).le
  refine ⟨?_, ?_, ?_⟩
  · grw [← prod_le_prod₀ (fun _ _ ↦ by positivity) fun a _ ↦ h_lower a]
    simp [← pow_mul, mul_assoc, ← sq]
  · grw [prod_le_prod₀ (fun a _ ↦ h_pos a) fun a _ ↦ h_upper a]
    simp [← pow_mul, mul_assoc, ← sq]
  · simp only [pow_add, prod_mul_distrib, prod_pow]
    gcongr
    · exact pow_nonneg (prod_nonneg fun a _ ↦ h_pos a) _
    have h_factor (a : Fin 𝔰.n) :
        S.frameScaleSq v a ^ (2 * (𝔰.ϱ - a)) ≤ S.b ^ (92 * 𝔰.n ^ 2) := by
      grw [h_upper a, ← pow_mul]
      exacts [pow_le_pow_right₀ hb (by nlinarith [Nat.sub_le 𝔰.ϱ a]), h_pos a]
    grw [prod_le_prod₀ (fun a _ ↦ pow_nonneg (h_pos a) _) fun a _ ↦ h_factor a]
    simp [← pow_mul, mul_assoc, ← pow_succ]

/-- For admissible data, `pairingBoundConst ≤ 2 ^ (k f) τ d² / (deg c_G ^ f Λ²)`. The left side is
the factor of the product over the infinite places of the open-cell bounds `pairingBoundSq` that
does not depend on the rational element at which they are taken. The numbers `d = card BesselCoord`
and `deg = besselDegree` are the products of the dimensions and of the degrees of the Bessel systems
at these places, `c_G = openCellConst` is a quotient of volumes of unitary groups, and
`Λ = frameScaleProd` is the product over all infinite `v` and all `a ≤ ϱ` of `s ^ (k + 2 (ϱ - a))`,
with `s = (S.realM v) ^ (2 (ϱ - a)) / N` the squared scale of the frame vector of index `a` at
`v`. -/
lemma pairingBoundConst_le_mul [S.IsAdmissible] :
    S.pairingBoundConst ≤ 2 ^ (𝔰.k * numInfPlaces E) * S.tailScale * (card S.BesselCoord ^ 2 /
      (S.besselDegree * 𝔰.openCellConst ^ numInfPlaces E * S.frameScaleProd ^ 2)) := by
  have hb : 1 ≤ S.b := S.one_le_b
  have h_const : 0 < 𝔰.openCellConst := 𝔰.openCellConst_pos
  have h_radius : 0 < S.frameBoxRadius := pow_pos b_pos _
  have h_degree : 0 < ∏ v : NumberField.InfinitePlace E, (S.besselSystem v).deg :=
    S.besselDegree_pos
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, 𝔰.k = k₀ + 1 := ⟨𝔰.k - 1, by grind [S.pow_le_k]⟩
  let e : ℕ := 453 * 𝔰.n ^ 2 * (10 ^ 5 * 𝔰.n ^ 4) + (92 * 𝔰.n ^ 2 + 184 * 𝔰.n ^ 3)
  have h_place (v : NumberField.InfinitePlace E) :
      (S.frameBoxRadius ^ (9 * 𝔰.n) / (∏ a : Fin 𝔰.n, S.frameScaleSq v a) ^ 2) ^
          (10 ^ 5 * 𝔰.n ^ 4) *
        ((card (S.besselSystem v).Index : ℝ) ^ 2 / ((S.besselSystem v).deg * 𝔰.openCellConst *
          ((∏ a : Fin 𝔰.n, S.frameScaleSq v a) ^ 2 / 2) ^ (𝔰.k - 1))) ≤
      2 ^ 𝔰.k * S.b ^ e * (card (S.besselSystem v).Index ^ 2 /
        ((S.besselSystem v).deg * 𝔰.openCellConst *
          (∏ a : Fin 𝔰.n, S.frameScaleSq v a ^ (𝔰.k + 2 * (𝔰.ϱ - a))) ^ 2)) := by
    obtain ⟨h_lower, h_upper, h_local⟩ := prod_frameScaleSq_bounds (S := S) v
    set s : ℝ := ∏ a : Fin 𝔰.n, S.frameScaleSq v a
    have hs : 0 < s := lt_of_lt_of_le (by positivity) h_lower
    have h_deg : 0 < (S.besselSystem v).deg := (S.besselSystem v).deg_pos
    have h_pos : 0 < ∏ a : Fin 𝔰.n, S.frameScaleSq v a ^ (𝔰.k + 2 * (𝔰.ϱ - a)) :=
      prod_pos fun a _ ↦ pow_pos (div_pos ((even_two_mul _).pow_pos (by simp))
        (Nat.cast_pos.2 S.N_prime.pos)) _
    have h_box : S.frameBoxRadius ^ (9 * 𝔰.n) / s ^ 2 ≤ S.b ^ (453 * 𝔰.n ^ 2) := by
      grw [← h_lower, frameBoxRadius]
      exact le_of_eq (by field_simp; ring)
    grw [h_box, h_local]
    calc
      _ = 2 ^ k₀ * (S.b ^ (453 * 𝔰.n ^ 2)) ^ (10 ^ 5 * 𝔰.n ^ 4) * s ^ 2 *
          (card (S.besselSystem v).Index ^ 2 /
            ((S.besselSystem v).deg * 𝔰.openCellConst * (s ^ 𝔰.k) ^ 2)) := by
        rw [hk₀, Nat.add_sub_cancel, div_pow]
        field_simp
        ring
      _ ≤ 2 ^ 𝔰.k * (S.b ^ (453 * 𝔰.n ^ 2)) ^ (10 ^ 5 * 𝔰.n ^ 4) * (S.b ^ (46 * 𝔰.n ^ 2)) ^ 2 *
          (card (S.besselSystem v).Index ^ 2 /
            ((S.besselSystem v).deg * 𝔰.openCellConst * (s ^ 𝔰.k) ^ 2)) := by
        gcongr
        exacts [one_le_two, k₀.le_succ.trans_eq hk₀.symm]
      _ = _ := by
        simp only [e, pow_add, ← pow_mul]
        field_simp
        ring
  have h_exponent : e * numInfPlaces E ≤ 10 ^ 5 * 𝔰.n ^ 9 * numInfPlaces E := by
    have h_large : 1000 ≤ 𝔰.n := by linarith [S.ten_pow_five_le_varrho]
    have h_two : 𝔰.n ^ 2 ≤ 𝔰.n ^ 6 := Nat.pow_le_pow_right 𝔰.ϱ.succ_pos (by norm_num)
    have h_three : 𝔰.n ^ 3 ≤ 𝔰.n ^ 6 := Nat.pow_le_pow_right 𝔰.ϱ.succ_pos (by norm_num)
    have h_nine : 1000 * 𝔰.n ^ 6 ≤ 𝔰.n ^ 9 :=
      (Nat.mul_le_mul_right _ (h_large.trans (Nat.le_self_pow three_ne_zero _))).trans_eq (by ring)
    have h_six : 453 * 𝔰.n ^ 2 * (10 ^ 5 * 𝔰.n ^ 4) = 453 * 10 ^ 5 * 𝔰.n ^ 6 := by ring
    refine Nat.mul_le_mul_right _ ?_
    unfold e
    rw [h_six]
    omega
  refine (prod_le_prod₀ (fun v _ ↦ by
    have h_deg : 0 < (S.besselSystem v).deg := (S.besselSystem v).deg_pos
    positivity) fun v _ ↦ h_place v).trans ?_
  simp only [prod_mul_distrib, prod_div_distrib, prod_const, prod_pow, card_univ, ← pow_mul]
  rw [← Nat.cast_prod, ← Fintype.card_pi]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_tailScale h_exponent) (by positivity))
      (div_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg h_degree.le (by positivity)) (sq_nonneg _)))

/-- For admissible data (`S.IsAdmissible`), `2 ^ (k f) n_p M ^ (2 ϱ f k) ≤ τ a_* vol(Ô) ^ n`, where
`n = 𝔰.n = ϱ + 1`. Here `k` is the rank of `X₀`, `f` is the number of infinite places,
`τ = tailScale = b ^ (k f / 4)` for the size parameter `b`, `M = p₀ p₁` is the level and
`vol(Ô) = volÔ E = 2 ^ f / √|disc E|`. With `R̄₀` the reduced image of the Bessel subgroup, `n_X`
the number of classes and `N = -h(z, z)` the prime `S.N`, `n_p = pairCountScale` is
`#R̄₀ n_X N ^ (-k f)`, and `a_* = scaledSiegelConst` is `#R̄₀ n_X` times
`unipotentOrder = M ^ (f ϱ (2 k + 2 ϱ + 1))` times `siegelConst = (π ^ k / ((k - 1)! N ^ k)) ^ f
|disc E| ^ (1 / 4) vol(Ô) ^ k`. -/
lemma two_pow_mul_pairCountScale_mul_le [S.IsAdmissible] :
    2 ^ (𝔰.k * numInfPlaces E) * (S.pairCountScale * S.M ^ (2 * 𝔰.ϱ * numInfPlaces E * 𝔰.k)) ≤
      S.tailScale * (S.scaledSiegelConst * volÔ E ^ 𝔰.n) := by
  -- With `x = 200 f k rd` we have `x ^ 1000 ≤ b`, so `x ^ (4 k f) ≤ τ`. This absorbs the powers of
  -- `2`, `k` and `rd`, and `unipotentOrder` is at least `M ^ (2 ϱ f k)`.
  set f : ℕ := numInfPlaces E with hf_eq
  set rd : ℝ := NumberField.rootDiscr E
  set x : ℝ := 200 * (f * 𝔰.k) * rd with hx
  have h_discr : (1 : ℝ) ≤ |(NumberField.discr E : ℝ)| :=
    mod_cast Int.one_le_abs (NumberField.discr_ne_zero E)
  have h_rd : 1 ≤ rd := one_le_rpow (mod_cast h_discr) (by positivity)
  have hf : (1 : ℝ) ≤ f := Nat.one_le_cast.2 NeZero.one_le
  have hk : (1 : ℝ) ≤ 𝔰.k := Nat.one_le_cast.2 (by grind [S.pow_le_k])
  have hN : (0 : ℝ) < S.N := Nat.cast_pos.2 S.N_prime.pos
  have hM : (1 : ℝ) ≤ S.M := Nat.one_le_cast.2 (one_le_two.trans two_le_M)
  have h_two : 2 ≤ x := by nlinarith [mul_le_mul hf hk zero_le_one (by positivity)]
  have h_k_le : 𝔰.k ≤ x := by nlinarith [mul_le_mul hf h_rd zero_le_one (by positivity)]
  have h_rd_le : rd ≤ x := by nlinarith [mul_le_mul hf hk zero_le_one (by positivity)]
  have hτ : 1 ≤ S.tailScale := one_le_tailScale
  have h_tail : x ^ (4 * (𝔰.k * f)) ≤ S.tailScale := by
    refine le_of_pow_le_pow_left₀ (by norm_num : 250 ≠ 0) (by positivity) ?_
    calc
      _ = (x ^ 1000) ^ (𝔰.k * f) := by
        rw [← pow_mul, ← pow_mul]
        congr 1
        ring
      _ ≤ S.tailScale ^ 4 := by grw [S.mul_rootDiscr_pow_le, tailScale_pow_four]
      _ ≤ _ := pow_le_pow_right₀ hτ (by norm_num)
  have h_siegel : (x ^ (3 * (𝔰.k * f)))⁻¹ / S.N ^ (𝔰.k * f) ≤ S.siegelConst * volÔ E ^ 𝔰.n := by
    have h_volume : (x ^ f)⁻¹ ≤ volÔ E := by
      rw [volÔ_eq]
      gcongr
      exact (half_le_self (by positivity)).trans h_rd_le
    have h_factorial : ((𝔰.k - 1).factorial : ℝ) ≤ x ^ 𝔰.k := by
      grw [Nat.factorial_le tsub_le_self, Nat.factorial_le_pow, Nat.cast_pow, h_k_le]
    have h_root_discr : 1 ≤ √√|(NumberField.discr E : ℝ)| := by rwa [one_le_sqrt, one_le_sqrt]
    have h_power : (x ^ f)⁻¹ ^ 𝔰.k ≤ volÔ E ^ 𝔰.n := by
      grw [← h_volume]
      exact pow_le_pow_of_le_one (by positivity)
        (inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))) (by grind [S.thousand_mul_le_k])
    grw [siegelConst, ← h_power, ← h_volume, h_factorial, ← h_root_discr,
      ← one_le_pow₀ (one_le_two.trans two_le_pi), ← hf_eq]
    simp only [div_pow, inv_pow]
    exact le_of_eq (by field_simp; ring)
  have h_order : (S.M : ℝ) ^ (2 * 𝔰.ϱ * f * 𝔰.k) ≤ S.unipotentOrder := by
    simpa [unipotentOrder] using pow_le_pow_right₀ hM (by lia : 2 * 𝔰.ϱ * f * 𝔰.k ≤ _)
  grw [scaledSiegelConst, mul_assoc _ S.siegelConst, ← h_siegel, ← h_order, ← h_tail, h_two,
    pairCountScale]
  exact le_of_eq (by field_simp; ring)

/-- For admissible data, `pairingBoundConst` is at most `(ν τ² / 2)²
mainSecondMoment / (pairCountScale M ^ (2 ϱ f k))`. Here `ν` is `unipotentCovolume`, `τ` is
`tailScale`, `M` is the level, `ϱ` is the number of hyperbolic planes, `k` is the rank of `X₀` and
`f` is the number of infinite places. -/
lemma pairingBoundConst_le [S.IsAdmissible] :
    S.pairingBoundConst ≤ (S.unipotentCovolume * S.tailScale ^ 2 / 2) ^ 2 *
      (S.mainSecondMoment / (S.pairCountScale * S.M ^ (2 * 𝔰.ϱ * numInfPlaces E * 𝔰.k))) := by
  -- The bound `scaledSiegelConst_le` joins `pairingBoundConst_le_mul` and
  -- `two_pow_mul_pairCountScale_mul_le`.
  have hτ : 2 ≤ S.tailScale := two_le_tailScale
  have h_scale : 0 < S.frameScaleProd := S.frameScaleProd_pos
  have h_degree : 0 < S.besselDegree := S.besselDegree_pos
  have h_const : 0 < 𝔰.openCellConst := 𝔰.openCellConst_pos
  have h_volume : (0 : ℝ) < volÔ E := by rw [volÔ_eq]; positivity [rootDiscr_pos E]
  have h_moment : 0 ≤ S.mainSecondMoment := mainSecondMoment_nonneg
  have h_pairs : 0 < S.pairCountScale := pairCountScale_pos
  have hM : 2 ≤ S.M := two_le_M
  have hb : 0 < S.b := b_pos
  have h_small : S.b⁻¹ ^ 9 ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ S.one_le_b)
  rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
  calc
    _ ≤ S.tailScale * (card S.BesselCoord ^ 2 /
        (S.besselDegree * 𝔰.openCellConst ^ numInfPlaces E * S.frameScaleProd ^ 2)) *
        (2 ^ (𝔰.k * numInfPlaces E) *
          (S.pairCountScale * S.M ^ (2 * 𝔰.ϱ * numInfPlaces E * 𝔰.k))) := by
      grw [pairingBoundConst_le_mul]
      exact le_of_eq (by ring)
    _ ≤ 2 * S.tailScale ^ 2 * S.unipotentCovolume ^ 2 * S.mainSecondMoment := by
      grw [two_pow_mul_pairCountScale_mul_le, IsAdmissible.scaledSiegelConst_le, h_small]
      exact le_of_eq (by field_simp; ring)
    _ ≤ _ := by
      have h_eight : 8 ≤ S.tailScale ^ 2 := by
        grw [← pow_le_tailScale (S := S) (e := 1) NeZero.one_le, pow_one]
        nlinarith [S.thousand_le_b]
      rw [div_pow, mul_pow, pow_right_comm]
      gcongr
      nlinarith [mul_le_mul_of_nonneg_left h_eight
        (by positivity : 0 ≤ S.tailScale ^ 2 * S.unipotentCovolume ^ 2)]

/-- Let the data be admissible (`S.IsAdmissible`), let `γ` be rational, and let `x = termDiscNorm γ`
be the product of the absolute values of `termDisc γ` over the infinite places. If `1 ≤ x`, then the
product over the infinite places `v` of the open-cell bounds `pairingBoundSq` at `S.ratToInf γ v` is
at most `(ν σ / 2)²`. Here `ν` is `unipotentCovolume`, and `σ = orbitBound ⊤ x` is the value at `x`
of the bound `orbitBound` for an orbit of the top cell rank `⊤ = ϱ + 1`. -/
lemma prod_pairingBoundSq_le [S.IsAdmissible] (h_one_le : 1 ≤ S.termDiscNorm γ) :
    ∏ v : NumberField.InfinitePlace E,
        pairingBoundSq (S.ratToInf γ v) (S.besselSystem v).deg S.frameBoxRadius
          (card (S.besselSystem v).Index) ≤
      (S.unipotentCovolume * S.orbitBound ⊤ (S.termDiscNorm γ) / 2) ^ 2 := by
  have h_const : 0 ≤ S.mainSecondMoment /
    (S.pairCountScale * S.M ^ (2 * 𝔰.ϱ * numInfPlaces E * 𝔰.k)) :=
    div_nonneg mainSecondMoment_nonneg (mul_nonneg pairCountScale_pos.le (by positivity))
  have h_norm : 0 < S.termDiscNorm γ := one_pos.trans_le h_one_le
  have h_exponent : 𝔰.k ≤ 10 ^ 5 * 𝔰.n ^ 4 + (𝔰.k - 1) := by
    grind [Nat.pow_pos (n := 4) 𝔰.ϱ.succ_pos]
  calc
    _ ≤ (S.unipotentCovolume * S.tailScale ^ 2 / 2) ^ 2 *
        (S.mainSecondMoment / (S.pairCountScale * S.M ^ (2 * 𝔰.ϱ * numInfPlaces E * 𝔰.k))) /
          S.termDiscNorm γ ^ 𝔰.k := by
      rw [prod_pairingBoundSq_eq]
      exact div_le_div₀ (by positivity) pairingBoundConst_le (by positivity)
        (pow_le_pow_right₀ h_one_le h_exponent)
    _ = _ := by
      rw [orbitBound_top, ← mul_assoc S.pairCountScale, ← div_div S.mainSecondMoment (_ * _),
        div_pow, div_pow, mul_pow, mul_pow, mul_pow,
        Real.sq_sqrt (div_nonneg h_const (by positivity))]
      ring

end New.Filling

end OrbitBound

end
