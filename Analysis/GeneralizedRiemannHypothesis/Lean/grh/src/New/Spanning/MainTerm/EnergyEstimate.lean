import New.Spanning.MainTerm.FiniteSieveSystem
import New.Spanning.RemainingTerms.Size
import New.UpperBound.Objects.LabelsAndIndexTypes

/-!
# Main-term bound for the second moment over open reductions fixing given vectors

This file proves the main-term estimate of the filling theorem. The subgroup
`New.Filling.fixer Sg D` consists of the reductions s that fix the given vectors `D w` modulo w or
its conjugate, at the chosen places `w ∈ Sg` above the first prime. It shows that every term over an
open reduction lies in the big cell. It then proves Siegel's step and uses it to bound the sum over
the open reductions that fix the vectors at `Sg`.

## Main definitions and results

* `New.Filling.IsFillingData.mul_sum_norm_sum_cosetAmplitude_sq_le`: Siegel's step, which bounds the
  squared norms of finitely many class sums by densities at finite places weighted by the local
  bounds.
* `New.Filling.sum_norm_sum_cosetAmplitude_sq_le`: the estimate for finitely many distinct classes
  whose reductions fix the vectors at `Sg`. The bound is (1 + b⁻⁴) b^(−6 𝔰.k |Sg|) times the main
  second moment times `unipotentCovolume`².
* `New.Filling.linkSecondMoment_isOpenElement_le`: the squared norms of the class sums of the cut
  function add up to at most the same bound. The sum runs over all links, pairs of classes and
  reductions s that are open and fix the vectors at `Sg`; only terms with `termDisc γ ≠ 0` enter.

Notions from other files:
* `New.Filling.IsAdmissible`: The standing hypotheses: `sourceLevel` is the preimage of K(M),
  `reduction` is onto, and size inequalities hold between b, M and ϖ, κ_v, N, the constant
  `scaledSiegelConst`, the second moments, the number of Bessel coordinates and an index.
* `New.Filling.mainSecondMoment`: The real number `sourceDim`² / (`besselDegree` · mass), with the
  mass `New.mass` of the genus of the standard lattice of rank dim V.
* `New.Filling.termsOver` c s c': The terms over (c, s, c'): rational γ such that h_c⁻¹ γ h_c' lies
  in the stabiliser K of the lattice and has reduction s.

## Relation to the literature

In the unfolded second moment of the Poincaré series, the summed main terms are dominated by the
quadratic form of a positive kernel of local Bessel (orbital) integrals at a finite set of primes,
with a constant close to one. With the sieve this bounds the main term above. Kloosterman sums as
local orbital integrals, normal forms for Bessel double cosets and Siegel's formula are known in the
literature. Related work: Jacquet–Ye, Germs of Kloosterman integrals for GL(3), 1999; Y. Liu,
Relative trace formulae toward Bessel and Fourier–Jacobi periods, 2014; Siegel, Über die analytische
Theorie der quadratischen Formen, 1935.
-/

section MainTermEstimate

open MeasureTheory Real Finset Matrix Filter Fintype RingHom Complex

namespace New.Filling

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}

/-- The leading minors of the frame products (the products of the frame of the middle form over
the lattice with its image under `X`) commute with ring maps. -/
lemma leadingMinor_frameGram_map {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R')
    (X : Matrix 𝔰.BesselIndex 𝔰.BesselIndex R) (l : Fin (𝔰.n + 1)) :
    leadingMinor ((S.latticeMiddle R').frameGram (X.map φ)) l =
      φ (leadingMinor ((S.latticeMiddle R).frameGram X) l) := by
  rw [leadingMinor, leadingMinor, map_det, Shape.Form.frameGram, Shape.Form.frameGram,
    ← S.map_splitGram_latticeMiddle φ, ← Matrix.map_mul, RingHom.mapMatrix_apply, submatrix_map,
    submatrix_map]

/-- If `γ ∈ S.termsOver c s c'`, that is, `h_c⁻¹ γ h_c'` lies in K and has reduction `s`, then for
each `l` the leading minor of order `l` of `S.frameProducts γ` is integral. At every place `w` in
`S.chosenPlaces i` its reduction `reduceAt w` equals the same minor of
`(S.latticeMiddle (ResField w)).frameGram (s i w)`. -/
lemma exists_leadingMinor_reduceAt_eq {c c' : S.Classes} {s : S.ResidueGL} {γ : S.G E}
    (hγ : γ ∈ S.termsOver c s c') (l : Fin (𝔰.n + 1)) :
    ∃ δ : Ô E, δ.1 = algebraMap E (𝔸f E) (leadingMinor (S.frameProducts γ) l) ∧
      ∀ (i : Fin 2) (w : S.chosenPlaces i), reduceAt w.1 δ =
        leadingMinor ((S.latticeMiddle (ResField w.1)).frameGram (s i w).1) l := by
  -- The translate of `γ` by class representatives has an integral matrix with the frame products of
  -- `γ` and reduction `s`.
  obtain ⟨k, rfl, hk⟩ := hγ
  let X : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (Ô E) :=
    of fun a b ↦ ⟨k.1.1.1 a b, (mem_intGL.1 k.2).1 a b⟩
  refine ⟨leadingMinor ((S.latticeMiddle (Ô E)).frameGram X) l, ?_, fun i w ↦ ?_⟩
  · have h_gram : (S.latticeMiddle (𝔸f E)).frameGram (X.map (Ô E).subtype) =
        (S.frameProducts γ).map (algebraMap E (𝔸f E)) :=
      (congrArg (fun g : S.GFin ↦ (S.latticeMiddle (𝔸f E)).frameGram g.1.1) hk).trans
        frameGram_translateByClassReps
    rw [← (Ô E).coe_subtype, ← leadingMinor_frameGram_map, h_gram, leadingMinor, leadingMinor,
      map_det, RingHom.mapMatrix_apply, submatrix_map]
  · rw [show (S.reduction k i w).1 = X.map (reduceAt w.1) from rfl, leadingMinor_frameGram_map]

/-- If `s` is open, that is, at some chosen place above the first prime none of its proper leading
minors of frame products vanishes, then for every term `γ` over a block `(c, s, c')` no proper
leading minor of the frame products of `γ` vanishes: `γ` lies in the big cell. -/
lemma IsOpenElement.leadingMinor_ne_zero {c c' : S.Classes} {s : S.ResidueGL}
    (hs : S.IsOpenElement s) {γ : S.G E} (hγ : γ ∈ S.termsOver c s c') (l : Fin 𝔰.n) :
    leadingMinor (S.frameProducts γ) l.castSucc ≠ 0 := by
  obtain ⟨w, hw⟩ := hs
  obtain ⟨δ, hδ, h_red⟩ := exists_leadingMinor_reduceAt_eq hγ l.castSucc
  intro h_zero
  exact hw l (by rw [← h_red, show δ = 0 from Subtype.ext (by simp [hδ, h_zero]), map_zero])

/-- With `f` the number of infinite places, the factor `(1 + S.b⁻¹ ^ 10) ^ f` of the sieve is at
most `1 + S.b⁻¹ ^ 9`, because `f ≤ S.b / 1000` by the hypothesis `S.IsAdmissible`. -/
lemma one_add_inv_pow_ten_pow_le [S.IsAdmissible] :
    (1 + S.b⁻¹ ^ 10) ^ Core.numInfPlaces E ≤ 1 + S.b⁻¹ ^ 9 := by
  have hb_one : 1 ≤ S.b := le_trans (by norm_num) S.thousand_le_b
  set u : ℝ := S.b⁻¹ ^ 9 / 1000 with hu_def
  have hu : 0 ≤ u := by positivity
  have h_le_one : S.b⁻¹ ^ 9 ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hb_one)
  have h_exp : |rexp u - 1| ≤ 2 * |u| := abs_exp_sub_one_le (abs_le.2 ⟨by linarith, by linarith⟩)
  calc (1 + S.b⁻¹ ^ 10) ^ Core.numInfPlaces E
      ≤ rexp (S.b⁻¹ ^ 10) ^ Core.numInfPlaces E := by grw [add_comm, add_one_le_exp]
    _ = rexp (Core.numInfPlaces E * S.b⁻¹ ^ 10) := (Real.exp_nat_mul _ _).symm
    _ ≤ rexp (S.b / 1000 * S.b⁻¹ ^ 10) := by grw [S.numInfPlaces_le_div]
    _ = rexp u := by simp [u, field]
    _ ≤ 1 + S.b⁻¹ ^ 9 := by linarith [le_abs_self (rexp u - 1), abs_of_nonneg hu]

/-- For `0 ≤ u ≤ 1 / 1000` one has `(1 + u⁶) ((1 + u⁹)² (1 + u⁶) + u¹⁰) ≤ 1 + u⁴`. With `u = b⁻¹`
this collects the error factors in `sieve_constant_le`. -/
lemma one_add_pow_six_mul_add_pow_ten_le_one_add_pow_four {u : ℝ} (hu : 0 ≤ u)
    (hu_le : u ≤ 1 / 1000) :
    (1 + u ^ 6) * ((1 + u ^ 9) * (1 + u ^ 9) * (1 + u ^ 6) + u ^ 10) ≤ 1 + u ^ 4 := by
  -- All powers on the left are at most `s = u ^ 4 / 100`.
  have hu_one : u ≤ 1 := by linarith
  set s : ℝ := u ^ 4 / 100 with hs_def
  have hs : 0 ≤ s := by positivity
  have hs_one : s ≤ 1 := by linarith [pow_le_one₀ hu hu_one (n := 4)]
  have h_six : u ^ 6 ≤ s := by
    have h_sq : u ^ 2 ≤ 1 / 100 := by nlinarith
    calc u ^ 6 = u ^ 4 * u ^ 2 := by ring
      _ ≤ u ^ 4 * (1 / 100) := by gcongr
      _ = s := by ring
  have h_nine : u ^ 9 ≤ s := (pow_le_pow_of_le_one hu hu_one (by norm_num)).trans h_six
  have h_ten : u ^ 10 ≤ s := (pow_le_pow_of_le_one hu hu_one (by norm_num)).trans h_six
  calc
    _ ≤ (1 + s) * ((1 + s) * (1 + s) * (1 + s) + s) := by gcongr
    _ = 1 + s * (5 + 7 * s + 4 * s ^ 2 + s ^ 3) := by ring
    _ ≤ 1 + s * (5 + 7 * 1 + 4 * 1 ^ 2 + 1 ^ 3) := by gcongr
    _ ≤ 1 + u ^ 4 := by linarith

/-- The normalising constant `r` of the main term, used with `k = 𝔰.k - 1`: the product over the
infinite places of √`openCellConst` and powers of the squared scales `frameScaleSq` of the frame
vectors, divided by the number of Bessel coordinates. -/
noncomputable abbrev normalizingConst (S : Filling E 𝔰) [S.IsAdmissible] (k : ℕ) : ℝ :=
  (∏ v : NumberField.InfinitePlace E,
    √𝔰.openCellConst * ∏ a : Fin 𝔰.n, S.frameScaleSq v a ^ (k + 2 * a.rev)) /
      Fintype.card S.BesselCoord

/-- Assume `S.IsAdmissible` and `𝔰.k = kPred + 1`. The product of the Poisson summation constants
`S.poissonConst i` over `i < 𝔰.n` is `S.normalizingConst kPred ^ 2` times
`volÔ E ^ 𝔰.n (dim / Λ) ^ 2 / c_G ^ f`, where `dim = Fintype.card S.BesselCoord` is the number of
Bessel coordinates, `Λ = S.frameScaleProd`, `c_G = 𝔰.openCellConst` and `f` is the number of
infinite places. -/
lemma prod_poissonConst_eq [S.IsAdmissible] {kPred : ℕ} (hk : 𝔰.k = kPred + 1) :
    ∏ i ∈ Finset.range 𝔰.n, S.poissonConst i =
      S.normalizingConst kPred ^ 2 *
        (volÔ E ^ 𝔰.n * (Fintype.card S.BesselCoord / S.frameScaleProd) ^ 2 /
          𝔰.openCellConst ^ Core.numInfPlaces E) := by
  have h_scale (v : NumberField.InfinitePlace E) (a : ℕ) : S.frameScaleSq v a ≠ 0 :=
    (S.frameScaleSq_pos v a).ne'
  have h_cell : 𝔰.openCellConst ≠ 0 := 𝔰.openCellConst_pos.ne'
  -- one factor `S.frameScaleSq v a` splits off each power in `S.frameScaleProd`
  have h_prod : S.frameScaleProd =
      (∏ v : NumberField.InfinitePlace E, ∏ a : Fin 𝔰.n,
        S.frameScaleSq v a ^ (kPred + 2 * a.rev)) *
        ∏ a : Fin 𝔰.n, ∏ v : NumberField.InfinitePlace E, S.frameScaleSq v a := by
    rw [Finset.prod_comm (s := univ) (t := univ) (f := fun (a : Fin 𝔰.n) v ↦ S.frameScaleSq v a)]
    simp only [frameScaleProd, hk, ← prod_mul_distrib, ← pow_succ, Fin.val_rev, Nat.succ_sub_succ,
      add_right_comm kPred 1]
  simp only [poissonConst, normalizingConst, prod_range, prod_div_distrib, prod_const, card_univ,
    card_range, prod_mul_distrib, prod_pow, h_prod, div_pow, mul_pow, ← pow_mul, mul_comm _ 2]
  rw [pow_mul √𝔰.openCellConst, sq_sqrt 𝔰.openCellConst_pos.le]
  field [prod_eq_zero_iff, h_scale]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum Finset.prod Finset.univ in
/-- The error is measured against the identity second moment. Let `f` be the number of infinite
places, `n = 𝔰.n = ϱ + 1` the number of frame vectors, `k = 𝔰.k` and `dim` the number of Bessel
coordinates. The left side has three factors: the constant `scaledSiegelConst` of Siegel's step; the
quotient `vol(Ô) ^ n (dim / Λ)² / c_G ^ f` of the constants of Poisson summation by the squared
normalising constant, where `Λ = frameScaleProd` is a product of powers of the squared scales of the
frame vectors and `c_G = openCellConst = vol U(k)² / (vol U(k + 2ϱ + 1) vol U(k - 1))`; and
`decayConst`, the product over the infinite places `v` of a volume ratio of the shape times
`(|κ_v| ^ (2ϱ + 1) / (M N)) ^ (k - n⁷)` with `κ_v = S.realM v`. It is at most `b ^ (n⁹ f)` times
`dim * identitySecondMoment * unipotentCovolume²`. Here `identitySecondMoment` is the order of the
reduction of the Bessel subgroup times the number of classes times `dim`. -/
lemma scaledSiegelConst_mul_decayConst_le [S.IsAdmissible] :
    S.scaledSiegelConst * (volÔ E ^ 𝔰.n * (Fintype.card S.BesselCoord / S.frameScaleProd) ^ 2 /
        𝔰.openCellConst ^ Core.numInfPlaces E) * S.decayConst ≤
      S.b ^ (𝔰.n ^ 9 * Core.numInfPlaces E) *
        (Fintype.card S.BesselCoord * S.identitySecondMoment * S.unipotentCovolume ^ 2) := by
  -- Apart from the common factor `c`, both sides are `f`-th powers, of `A` and of `b ^ n⁹ * B`.
  have hb : 1 ≤ S.b := S.one_le_b
  have hM : (1 : ℝ) ≤ S.M := mod_cast one_le_two.trans two_le_M
  have hN : (1 : ℝ) ≤ S.N := mod_cast S.N_prime.pos
  obtain ⟨s, hs, hs_sq⟩ : ∃ s : ℝ, 1 ≤ s ∧ NumberField.rootDiscr E = s ^ 2 :=
    ⟨√(NumberField.rootDiscr E), Real.one_le_sqrt.2 (one_le_rootDiscr E),
      (sq_sqrt (rootDiscr_pos E).le).symm⟩
  obtain ⟨K, hK⟩ : ∃ K : ℕ, 𝔰.k = 𝔰.n ^ 7 + K := exists_add_of_le (by
    grw [← S.pow_le_k, Nat.pow_le_pow_right 𝔰.ϱ.succ_pos (by norm_num : 7 ≤ 9)]
    lia)
  -- `Q ^ f` is the product of the `|κ_v|` and `x` the base of the decay at one place. The power
  -- `S.M ^ D` is an explicit factor of `A`, and its square is a factor of `B`.
  let Q : ℝ := S.M * s ^ 2 / (2 * π)
  let x : ℝ := Q ^ (2 * 𝔰.ϱ + 1) / (S.M * S.N)
  let D : ℕ := 𝔰.ϱ * (2 * 𝔰.k + 2 * 𝔰.ϱ + 1)
  let A : ℝ := S.M ^ D * (π ^ 𝔰.k / (𝔰.k - 1).factorial / S.N ^ 𝔰.k * s * (2 / s ^ 2) ^ 𝔰.k) *
    ((2 / s ^ 2) ^ 𝔰.n / 𝔰.openCellConst) * (𝔰.scaledVolumeRatio * x ^ K)
  let B : ℝ := (S.M ^ D / S.N ^ 𝔰.k * (s ^ 2 / 2) ^ (𝔰.ϱ * (𝔰.k + 𝔰.ϱ)) * s ^ 𝔰.ϱ) ^ 2
  let c : ℝ := Nat.card (S.reducedImage besselS) * card S.Classes *
    (card S.BesselCoord / S.frameScaleProd) ^ 2
  have h_kappa : ∏ v, |S.realM v| = Q ^ Core.numInfPlaces E := by rw [prod_abs_realM, hs_sq]
  have h_disc : √√|(NumberField.discr E : ℝ)| = s ^ Core.numInfPlaces E := by
    rw [abs_discr_eq_rootDiscr_pow, sqrt_sq (pow_pos (rootDiscr_pos E) _).le, hs_sq,
      pow_right_comm, sqrt_sq (by positivity)]
  have h_vol : (volÔ E : ℝ) = (2 / s ^ 2) ^ Core.numInfPlaces E := by
    rw [volÔ_eq, hs_sq, ← inv_pow, inv_div]
  have h_left : S.scaledSiegelConst * (volÔ E ^ 𝔰.n * (card S.BesselCoord / S.frameScaleProd) ^ 2 /
      𝔰.openCellConst ^ Core.numInfPlaces E) * S.decayConst = c * A ^ Core.numInfPlaces E := by
    rw [scaledSiegelConst, unipotentOrder, Nat.cast_pow]
    simp only [siegelConst, decayConst, show 𝔰.k - 𝔰.n ^ 7 = K by lia, prod_mul_distrib, prod_pow,
      prod_div_distrib, prod_const, card_univ, h_kappa, h_disc, h_vol, A, c, x, D, mul_pow, div_pow]
    ring
  have h_right : card S.BesselCoord * S.identitySecondMoment * S.unipotentCovolume ^ 2 =
      c * B ^ Core.numInfPlaces E := by
    have h_sum : ∑ a ∈ range 𝔰.ϱ, (a + (𝔰.k + 1) + a) = 𝔰.ϱ * (𝔰.k + 𝔰.ϱ) := by
      induction 𝔰.ϱ with
      | zero => simp
      | succ n ih => grind [sum_range_succ]
    simp only [identitySecondMoment, sourceDim, unipotentCovolume, h_sum, h_disc, h_vol,
      Nat.cast_mul, B, c, D, mul_pow, div_pow, div_div_eq_mul_div]
    ring
  -- At one place, `A` is `B` times factors that do not depend on `k`.
  have hQ : 1 ≤ Q :=
    (one_le_pow_iff_of_nonneg (by positivity) Fintype.card_ne_zero).1
      ((Finset.one_le_prod₀ fun v _ ↦ S.one_le_abs_realM v).trans_eq h_kappa)
  have h_place : A = B * ((2 / s ^ 2) ^ (𝔰.n + 2 * 𝔰.ϱ ^ 2) * (s / s ^ (2 * 𝔰.ϱ)) /
      (2 * S.M ^ (𝔰.ϱ * (2 * 𝔰.ϱ + 1))) * x⁻¹ ^ 𝔰.n ^ 7) := by
    have h_x : x ^ K = x ^ 𝔰.k * x⁻¹ ^ 𝔰.n ^ 7 := by
      simp [hK, pow_add, field]
    simp only [A, B, h_x]
    generalize x⁻¹ ^ 𝔰.n ^ 7 = y
    simp only [x, Q, D, Shape.openCellConst, Shape.scaledVolumeRatio, sphereDensity, one_pow,
      mul_pow, div_pow]
    field_simp [(volU_pos _).ne']
    ring
  -- Those factors are at most `b ^ n⁹`: `2 / s²` is at most `b`, `s / s^(2ϱ)` at most `1` and
  -- `x⁻¹` at most a power of `b`.
  have h_factor : (2 / s ^ 2) ^ (𝔰.n + 2 * 𝔰.ϱ ^ 2) * (s / s ^ (2 * 𝔰.ϱ)) /
      (2 * S.M ^ (𝔰.ϱ * (2 * 𝔰.ϱ + 1))) * x⁻¹ ^ 𝔰.n ^ 7 ≤ S.b ^ 𝔰.n ^ 9 := by
    have h_two : 2 / s ^ 2 ≤ S.b := (div_le_self zero_le_two (one_le_pow₀ hs)).trans two_le_b
    have h_s : s / s ^ (2 * 𝔰.ϱ) ≤ 1 :=
      div_le_one_of_le₀ (le_self_pow₀ hs (by grind [S.ten_pow_five_le_varrho])) (by positivity)
    have h_inv : x⁻¹ ≤ S.b ^ 23 * S.b ^ (60 * 𝔰.n) := by
      grw [inv_div, div_le_self (by positivity) (one_le_pow₀ hQ), S.M_le_b_pow, S.N_le]
    grw [div_le_self (by positivity) (by bound), h_two, h_s, h_inv, mul_one, ← pow_add, ← pow_mul,
      ← pow_add]
    refine pow_le_pow_right₀ hb ?_
    obtain ⟨m, hm⟩ : ∃ m : ℕ, 𝔰.ϱ = 10 ^ 5 + m := exists_add_of_le S.ten_pow_five_le_varrho
    simp only [Shape.n, hm]
    lia
  rw [h_left, h_right, pow_mul, mul_left_comm, ← mul_pow, h_place, mul_comm B]
  gcongr

/-- Let `S` be admissible with size parameter `b`, `kPred = 𝔰.k - 1`, and let the number `numSieved`
of places at which vectors are fixed be at most `f`, the number of infinite places. The theorem
`sieve` bounds a sum of last entry densities over pairs of heads by `(∏ i, poissonConst i) * ((∏ v,
(1 + b⁻¹⁰) / deg v) * m + ε)`. Here `poissonConst i`, the constant of Poisson summation in entry
`i`, is vol(Ô) over the Jacobian of the scaling at the infinite places; `deg v` is the degree of the
Bessel system at `v`; `m` bounds the mass at the finite places; and
`ε = b^(2403 𝔰.n⁹ f) * decayConst` is the error, `decayConst` being the product of the constants in
the decay at the infinite places. For `m = (1 + b⁻⁶) / b^(6 𝔰.k numSieved)`, this bound times the
constant `(1 + b⁻⁶) * scaledSiegelConst` of Siegel's step is at most `r² (1 + b⁻⁴) b^(-6 𝔰.k
numSieved) * mainSecondMoment * unipotentCovolume²`, where `r = S.normalizingConst kPred` and
`mainSecondMoment = sourceDim² / ((∏ v, deg v) * mass)`, with the mass of the genus of the standard
Hermitian lattice of rank `𝔰.r`. -/
lemma sieve_constant_le [S.IsAdmissible] {kPred numSieved : ℕ} (hk : 𝔰.k = kPred + 1)
    (h_numSieved : numSieved ≤ Core.numInfPlaces E) :
    (1 + S.b⁻¹ ^ 6) * S.scaledSiegelConst *
        ((∏ i ∈ Finset.range 𝔰.n, S.poissonConst i) *
          ((∏ v : NumberField.InfinitePlace E, (1 + S.b⁻¹ ^ 10) / (S.besselSystem v).deg) *
              ((1 + S.b⁻¹ ^ 6) / (S.b ^ (6 * 𝔰.k)) ^ numSieved) +
            S.b ^ (2403 * 𝔰.n ^ 9 * Core.numInfPlaces E) * S.decayConst)) ≤
      S.normalizingConst kPred ^ 2 *
        ((1 + (S.b ^ 4)⁻¹) * (S.b ^ (6 * 𝔰.k))⁻¹ ^ numSieved * S.mainSecondMoment *
          S.unipotentCovolume ^ 2) := by
  have hb : 1 ≤ S.b := S.one_le_b
  have h_main : 0 ≤ S.mainSecondMoment := mainSecondMoment_nonneg
  have h_id : 0 ≤ S.identitySecondMoment := identitySecondMoment_nonneg
  have h_deg : 0 < S.besselDegree := S.besselDegree_pos
  have h_cell : 0 < 𝔰.openCellConst := 𝔰.openCellConst_pos
  rw [prod_poissonConst_eq hk]
  set f : ℕ := Core.numInfPlaces E
  set r : ℝ := S.normalizingConst kPred
  set w : ℝ := volÔ E ^ 𝔰.n * (card S.BesselCoord / S.frameScaleProd) ^ 2 / 𝔰.openCellConst ^ f
  set y : ℝ := (S.b ^ (6 * 𝔰.k))⁻¹ ^ numSieved * S.mainSecondMoment * S.unipotentCovolume ^ 2
  -- The masses: the constants make up the main second moment.
  have h_const : S.scaledSiegelConst * w ≤
      (1 + S.b⁻¹ ^ 9) * S.mainSecondMoment * S.besselDegree * S.unipotentCovolume ^ 2 := by
    have h_scale : 0 < S.frameScaleProd :=
      prod_pos fun v _ ↦ prod_pos fun a _ ↦ pow_pos (S.frameScaleSq_pos v a) _
    grw [IsAdmissible.scaledSiegelConst_le]
    refine le_of_eq ?_
    simp only [w, f]
    field_simp [volÔ_ne_zero (E := E)]
  have h_mass : S.scaledSiegelConst * w * ((∏ v, (1 + S.b⁻¹ ^ 10) / (S.besselSystem v).deg) *
      ((1 + S.b⁻¹ ^ 6) / (S.b ^ (6 * 𝔰.k)) ^ numSieved)) ≤
        (1 + S.b⁻¹ ^ 9) * (1 + S.b⁻¹ ^ 9) * (1 + S.b⁻¹ ^ 6) * y := by
    grw [prod_div_distrib, prod_const, card_univ, ← besselDegree, h_const,
      one_add_inv_pow_ten_pow_le]
    refine le_of_eq ?_
    simp only [y, inv_pow (S.b ^ (6 * 𝔰.k))]
    field_simp
  -- The errors: they are at most `b ^ (O(n⁹ f))` times `dim` times the identity second moment,
  -- which is at most `b ^ (-11 𝔰.k f)` times the main second moment.
  have h_error : S.scaledSiegelConst * w * (S.b ^ (2403 * 𝔰.n ^ 9 * f) * S.decayConst) ≤
      S.b⁻¹ ^ 10 * y := by
    have h_exp : 2403 * 𝔰.n ^ 9 * f + 𝔰.n ^ 9 * f + 2 * 𝔰.k * f + (10 + 6 * 𝔰.k * numSieved) ≤
        11 * (𝔰.k * f) := by
      have h_rank : 512000 * 𝔰.n ^ 9 ≤ 𝔰.k := S.pow_le_k.trans_eq' (by ring)
      linarith [Nat.mul_le_mul_right f h_rank, Nat.mul_le_mul_left 𝔰.k h_numSieved,
        show 0 < 𝔰.n ^ 9 * f from Nat.mul_pos (by positivity) Fintype.card_pos]
    calc
      _ = S.b ^ (2403 * 𝔰.n ^ 9 * f) * (S.scaledSiegelConst * w * S.decayConst) := by ring
      _ ≤ S.b ^ (2403 * 𝔰.n ^ 9 * f) * (S.b ^ (𝔰.n ^ 9 * f) *
          (S.b ^ (2 * 𝔰.k * f) * S.identitySecondMoment * S.unipotentCovolume ^ 2)) := by
        grw [scaledSiegelConst_mul_decayConst_le, IsAdmissible.card_besselCoord_le]
      _ = S.b ^ (2403 * 𝔰.n ^ 9 * f + 𝔰.n ^ 9 * f + 2 * 𝔰.k * f + (10 + 6 * 𝔰.k * numSieved)) *
          S.identitySecondMoment *
          (S.b⁻¹ ^ 10 * (S.b ^ (6 * 𝔰.k))⁻¹ ^ numSieved * S.unipotentCovolume ^ 2) := by
        simp only [pow_add, inv_pow, ← pow_mul]
        field_simp
      _ ≤ S.mainSecondMoment *
          (S.b⁻¹ ^ 10 * (S.b ^ (6 * 𝔰.k))⁻¹ ^ numSieved * S.unipotentCovolume ^ 2) := by
        grw [h_exp, IsAdmissible.mul_identitySecondMoment_le]
      _ = _ := by ring
  calc
    _ = r ^ 2 * ((1 + S.b⁻¹ ^ 6) *
        (S.scaledSiegelConst * w * ((∏ v, (1 + S.b⁻¹ ^ 10) / (S.besselSystem v).deg) *
          ((1 + S.b⁻¹ ^ 6) / (S.b ^ (6 * 𝔰.k)) ^ numSieved)) +
        S.scaledSiegelConst * w * (S.b ^ (2403 * 𝔰.n ^ 9 * f) * S.decayConst))) := by ring
    _ ≤ r ^ 2 * ((1 + S.b⁻¹ ^ 6) *
        ((1 + S.b⁻¹ ^ 9) * (1 + S.b⁻¹ ^ 9) * (1 + S.b⁻¹ ^ 6) + S.b⁻¹ ^ 10) * y) := by
      grw [h_mass, h_error]
      exact le_of_eq (by ring)
    _ ≤ r ^ 2 * ((1 + S.b⁻¹ ^ 4) * y) := by
      grw [one_add_pow_six_mul_add_pow_ten_le_one_add_pow_four (by positivity)
        (by simpa using inv_anti₀ (by simp) S.thousand_le_b)]
    _ = _ := by ring

/-- The square of the normalising constant is positive. -/
lemma normalizingConst_sq_pos [S.IsAdmissible] (kPred : ℕ) :
    0 < S.normalizingConst kPred ^ 2 := by
  have h_prod : 0 < ∏ v : NumberField.InfinitePlace E,
      √𝔰.openCellConst * ∏ a : Fin 𝔰.n, S.frameScaleSq v a ^ (kPred + 2 * a.rev) :=
    prod_pos fun v _ ↦ mul_pos (Real.sqrt_pos.2 𝔰.openCellConst_pos)
      (prod_pos fun a _ ↦ pow_pos (S.frameScaleSq_pos v a) _)
  unfold normalizingConst
  positivity

/-- Let `P` be a structure of finite place on the product of the completions at `T`, and `G` a
filling datum for it. Let the head have ϱ first entries `p`, units off `T`, and last entry `t` with
‖t‖² > N² at every infinite place; `x v a` is its entry of index `a` under `Φ v` times
`S.frameScaleSq v a = κ_v^(2(ϱ - a)) / N`, the squared scale of the frame vector `a`
(`κ_v = S.realM v`). The first factor on the left is the product over `v` of the scalars of
`normalizedOrbitalIntegral` at `x v`; in it `openCellConst` is a ratio of volumes of compact unitary
groups and `(S.besselSystem v).Index` indexes a basis of the value space of the Bessel functions at
`v`. The second factor `G.headDensity` is a product of powers of the moduli of `p` for `P`. Their
product is `S.normalizingConst kPred`, with `kPred = 𝔰.k - 1`, times the square root of (∏ (‖t‖² -
N²))^(𝔰.k - 1). By the product formula the powers of `p` cancel; the constant collects
√`openCellConst`, the powers of the squared scales and the numbers of indices. -/
lemma gramScalar_mul_headDensity [WeilData E]
    [S.IsAdmissible] {T : Finset (FinPlace E)} [T.StarStable] {P : Floors.IntegralPlace (LocProd T)}
    {G : Floors.PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T))
      (𝔰.ϱ + 1 + 2 * 𝔰.ϱ + 5)} (_hG : S.IsFillingData T G) {kPred : ℕ} (hk : 𝔰.k = kPred + 1)
    {T₀ : Finset Eˣ} (hT₀ : ∀ x ∈ T₀, x.val ∈ ratIntegralOff T ∧ x⁻¹.val ∈ ratIntegralOff T)
    {t : Eˣ} (h_large : ∀ v : NumberField.InfinitePlace E, S.N ^ 2 < ‖Φ v t.val‖ ^ 2)
    (p : Fin 𝔰.ϱ → T₀) :
    let x (v : NumberField.InfinitePlace E) (a : ℕ) : ℂˣ :=
      unitOrOne (S.frameScaleSq v a * Φ v (padTuple (fun b : Fin 𝔰.ϱ ↦ (p b).val) t a).val)
    (∏ v : NumberField.InfinitePlace E, √𝔰.openCellConst *
        √(‖(x v 𝔰.ϱ).val‖ ^ 2 - 1) ^ (𝔰.k - 1) / Fintype.card (S.besselSystem v).Index *
        ∏ a ∈ Finset.range 𝔰.ϱ, ‖(x v a).val‖ ^ (𝔰.k + 1 + 2 * (𝔰.ϱ - (a + 1)))) *
      (G.headDensity 𝔰.ϱ (Units.map (ratToPlaces T) ∘ padTuple (fun b : Fin 𝔰.ϱ ↦ (p b).val) t)
        1).toReal =
      S.normalizingConst kPred *
        √((∏ v : NumberField.InfinitePlace E, (‖Φ v t.val‖ ^ 2 - S.N ^ 2)) ^ (𝔰.k - 1)) := by
  intro x
  have h_sqrt : √((∏ v : NumberField.InfinitePlace E, (‖Φ v t.val‖ ^ 2 - S.N ^ 2)) ^ (𝔰.k - 1)) =
      (∏ v : NumberField.InfinitePlace E, √(‖Φ v t.val‖ ^ 2 - S.N ^ 2)) ^ (𝔰.k - 1) := by
    simp [sqrt_eq_rpow, rpow_pow_comm, finsetProd_rpow, (h_large _).le, prod_nonneg]
  -- The product formula cancels the entries of the head.
  have h_product (a : Fin 𝔰.ϱ) :
      P.modulus (evalPlaces T (p a : Eˣ).val) ^ (2⁻¹ : ℝ) =
        (∏ v : NumberField.InfinitePlace E, ‖Φ v (p a : Eˣ).val‖ₑ)⁻¹ :=
    P.modulus_evalPlaces_rpow_half (hT₀ (p a) (p a).prop)
  have h_scale (v : NumberField.InfinitePlace E) (a : ℕ) : S.frameScaleSq v a ≠ 0 :=
    (S.frameScaleSq_pos v a).ne'
  -- In the normalising constant, split off the scale of the last frame vector.
  have h_const : S.normalizingConst kPred =
      (∏ v : NumberField.InfinitePlace E, √𝔰.openCellConst *
        ((∏ a : Fin 𝔰.ϱ, S.frameScaleSq v a ^ (kPred + 2 * (a.rev + 1))) *
          S.frameScaleSq v 𝔰.ϱ ^ kPred)) / Fintype.card S.BesselCoord := by
    simp only [normalizingConst, Fin.prod_univ_castSucc, Fin.rev_castSucc, Fin.rev_last,
      Fin.val_castSucc, Fin.val_succ, Fin.val_last, Fin.val_zero, mul_zero, add_zero]
  rw [h_sqrt, h_const]
  simp [x, frameScaleSq.eq_1 S _ 𝔰.ϱ, div_pow, div_mul_eq_mul_div, div_sub_one, -one_div, hk,
    mul_add, unitOrOne, mul_pow, abs_of_pos, pow_add, padTuple, prod_pow, prod_range, h_scale,
    Floors.PlaceData.headDensity, h_product,
    Finset.prod_comm (t := (univ : Finset (Fin 𝔰.ϱ))), prod_eq_zero_iff, field,
    Nat.Prime.ne_zero, prod_mul_distrib]

/-- Let `S` be an admissible filling, and `σ` a rational element of the floor group (it fixes the
hyperbolic basis vectors `e_a`, `e*_a` for `a < ϱ`) with last frame product `t`. A head is a tuple
`p` of ϱ entries from a finite set `T₀` of units of `E`, followed by `t`; `x v p a` is its entry of
index `a` under the embedding `Φ v`, times the squared scale `S.frameScaleSq v a` of the frame
vector `a` at `v`. The Weyl element `w_p` of the head sends `e_a` to `p_a e*_a` and `e*_a` to
`e_a / p̄_a` for `a < ϱ`. Let `W = S.besselFn .cut` be the product over the infinite places of the
cut Bessel functions W♭, which have bounded support modulo the Bessel subgroup, and let
`besselOrbitalIntegral volume W γ` be the tensor ∫ W(g) ⊗ W(γ⁻¹ g)^* dg. Let `R p q` be the product
over `v` of `bandLimit 𝔰.n`, the top one of the forms on pairs of heads that the Bessel system at
`v` provides for the sieve. Then `R` is the Gram matrix of the orbital integrals at `γ = w_p σ`,
each weighted by the product over `v` of the scalar of `normalizedOrbitalIntegral`, √c_G · (|x_ϱ|² -
1)^((k - 1)/2) · |I|⁻¹ · ∏_{a<ϱ} |x_a|^(k + 1 + 2(ϱ - a - 1)), where `x = x v p`, `k = 𝔰.k`,
`c_G = 𝔰.openCellConst` and `I` is the index set of the Bessel system at `v`. -/
lemma prod_bandLimit_eq_gram [S.IsAdmissible] {T₀ : Finset Eˣ} {σ : S.G E} {t : Eˣ}
    (hσ : σ ∈ Shape.Form.floorGroup 𝔰.ϱ) (h_tail : S.frameProducts σ 𝔰.top 𝔰.top = t) :
    let x (v : NumberField.InfinitePlace E) (p : Fin 𝔰.ϱ → T₀) (a : ℕ) : ℂˣ :=
      unitOrOne (S.frameScaleSq v a * Φ v (padTuple (fun b : Fin 𝔰.ϱ ↦ (p b).val) t a).val)
    let R : Matrix (Fin 𝔰.ϱ → T₀) (Fin 𝔰.ϱ → T₀) ℂ := fun p q : Fin 𝔰.ϱ → T₀ ↦
      ∏ v : NumberField.InfinitePlace E, (S.besselSystem v).bandLimit 𝔰.n (x v p) (x v q)
    R = Matrix.gram ℂ fun p : Fin 𝔰.ϱ → T₀ ↦
      (∏ v : NumberField.InfinitePlace E, √𝔰.openCellConst *
          √(‖(x v p 𝔰.ϱ).val‖ ^ 2 - 1) ^ (𝔰.k - 1) / Fintype.card (S.besselSystem v).Index *
          ∏ a ∈ Finset.range 𝔰.ϱ, ‖(x v p a).val‖ ^ (𝔰.k + 1 + 2 * (𝔰.ϱ - (a + 1)))) •
        besselOrbitalIntegral volume
          (fun g : NumberField.InfinitePlace E → 𝔰.G₁ ↦ WithLp.toLp 2 (S.besselFn .cut g))
          (S.ratToInf
            (Floors.FloorGroups.weylElem 𝔰.ϱ (padTuple (fun a : Fin 𝔰.ϱ ↦ (p a).val) t) * σ)) := by
  intro x R
  ext p q
  -- At each infinite place both heads end in the last frame product of `σ`, so the band limit is an
  -- inner product of normalised orbital integrals.
  have h_local (v : NumberField.InfinitePlace E) :
      (S.besselSystem v).bandLimit 𝔰.n (x v p) (x v q) =
        inner ℂ (normalizedOrbitalIntegral (S.ratToInf σ v) ((S.besselSystem v).besselFn .cut)
          (x v p))
          (normalizedOrbitalIntegral (S.ratToInf σ v) ((S.besselSystem v).besselFn .cut)
            (x v q)) := by
    have h_last : realFrameGram (S.ratToInf σ v) 𝔰.top 𝔰.top = x v p 𝔰.ϱ := by
      simp [h_tail, x, frameScaleSq, padTuple, unitOrOne, S.N_prime.ne_zero]
    have h_same : x v q 𝔰.ϱ = x v p 𝔰.ϱ := by simp [x, padTuple]
    exact (S.besselSystem v).hasLocalBounds.right (S.ratToInf σ v)
      (hσ.ratToInf_mem_agreeWithOneOn v) (x v p) (x v q) h_last h_same
  refine (prod_congr rfl fun v _ ↦ h_local v).trans ?_
  -- the scaled orbital integrals of the product vector are the products of the local ones
  simp_rw [normalizedOrbitalIntegral, gram_apply, inner_smul_left_eq_smul, inner_smul_right_eq_smul,
    real_smul]
  simp only [inner, besselFn, besselOrbitalIntegral, Pi.mul_apply, Pi.inv_apply, Complex.star_def,
    prod_univ_sum, ratToInf_weylElem_mul, prod_mul_distrib, ← map_prod, sum_prod_type,
    ← integral_fintype_prod_volume_eq_prod, ← ofReal_prod]
  rfl'

variable [WeilData E]

/-- Siegel's step. Let `S` be an admissible filling of shape `𝔰` over a CM field `E` with Weil data,
and let `kPred = 𝔰.k - 1`. Let `1 / M`, `1 / N`, the lattice basis and its inverse be integral off
the finite set of places `T`. Let `P` be a structure of finite place on the product of the
completions at `T`, `G` a filling datum for it, and `Y` a group between the congruence group of `G`
and the integral points. Take finitely many distinct classes `(c i, S.reduction (n i), c' i, σ i)`,
with `σ i` in the floor group, last entry `t i` with ‖t i‖² > N² at every infinite place, position
integral off `T` and lift `n i` in `Y` at `T`.

On the left, `S.cosetAmplitude .cut c s c' γ` is the sum of the amplitudes of the cut function at
`u γ u'⁻¹` over the rational unipotent `u`, `u'` for which this element lies over `(c, s, c')`. It
is summed over `γ = w_p σ`, for the Weyl elements `w_p` of the heads with first entries `p` in a
finite set `T₀` of units off `T`. The squared norms of these class sums, times `r²` for the
normalising constant `r`, add up to at most `(1 + b⁻⁶) * S.scaledSiegelConst` times the real part of
a sum over the last entries and the pairs of heads. The summand is the product of the top forms
`bandLimit 𝔰.n` of the Bessel systems at the infinite places with the density `G.lastEntryDensity`
at `T`, divided by `Y.massRatio = vol(Y) vol(K) / fl²`, where `K` is the congruence group of `G` and
`fl = G.unipotentMass`. -/
lemma IsFillingData.mul_sum_norm_sum_cosetAmplitude_sq_le [S.IsAdmissible] {T : Finset (FinPlace E)}
    [T.StarStable] [Fact (S.ideleM⁻¹.val ∈ integralOff T)] {P : Floors.IntegralPlace (LocProd T)}
    {G : Floors.PlaceData (Fin (𝔰.k - (6 * 𝔰.ϱ + 13))) (S.latticeMiddle (LocProd T))
      (𝔰.ϱ + 1 + 2 * 𝔰.ϱ + 5)} (hG : S.IsFillingData T G) (Y : G.IntermediateGroup)
    {kPred : ℕ} (hk : 𝔰.k = kPred + 1) {ι : Type} [Fintype ι] [DecidableEq Eˣ]
    {c c' : ι → S.Classes} {σ : ι → S.G E} {n : ι → S.latticeStabilizer} {t : ι → Eˣ}
    (h_inj : (fun i : ι ↦ (c i, c' i, S.reduction (n i), σ i)).Injective)
    (hσ : ∀ i : ι, σ i ∈ Shape.Form.floorGroup 𝔰.ϱ)
    (h_tail : ∀ i : ι, S.frameProducts (σ i) 𝔰.top 𝔰.top = t i)
    (h_large : ∀ (i : ι) (v : NumberField.InfinitePlace E), S.N ^ 2 < ‖Φ v (t i).val‖ ^ 2)
    (hn_mem_Y : ∀ i : ι, S.toPlaces T (n i) ∈ Y.val) {T₀ : Finset Eˣ}
    (hT₀ : ∀ x ∈ T₀, x.val ∈ ratIntegralOff T ∧ x⁻¹.val ∈ ratIntegralOff T)
    (hT_basis : S.latticeBasis ∈ intGL 𝔰.BesselIndex (integralOff T))
    (hT_N : (S.N : E)⁻¹ ∈ ratIntegralOff T)
    (h_off : ∀ i : ι, S.IsIntegralOff T (S.translateByClassReps (c i) (c' i) (σ i))) :
    let r : ℝ := S.normalizingConst kPred
    -- the heads at the infinite place `v` and at `T`
    let x (v : NumberField.InfinitePlace E) (p : Fin 𝔰.ϱ → T₀) (t : Eˣ) (a : ℕ) : ℂˣ :=
      unitOrOne (S.frameScaleSq v a * Φ v (padTuple (fun b : Fin 𝔰.ϱ ↦ (p b).val) t a).val)
    let y (p : Fin 𝔰.ϱ → T₀) (t : Eˣ) : ℕ → (LocProd T)ˣ :=
      Units.map (ratToPlaces T) ∘ padTuple (fun a : Fin 𝔰.ϱ ↦ (p a).val) t
    r ^ 2 * ∑ i : ι, ‖∑ p : Fin 𝔰.ϱ → T₀, S.cosetAmplitude .cut (c i) (S.reduction (n i)) (c' i)
        (Floors.FloorGroups.weylElem 𝔰.ϱ (padTuple (fun a : Fin 𝔰.ϱ ↦ (p a).val) (t i)) *
          σ i)‖ ^ 2 ≤
      (1 + S.b⁻¹ ^ 6) * S.scaledSiegelConst *
        (∑ t' ∈ univ.image t, ∑ p : Fin 𝔰.ϱ → T₀, ∑ q : Fin 𝔰.ϱ → T₀,
          (∏ v : NumberField.InfinitePlace E,
            (S.besselSystem v).bandLimit 𝔰.n (x v p t') (x v q t')) *
          (G.lastEntryDensity (S.piNAt T) Y (y p t') (y q t') / Y.massRatio.toReal)).re := by
  -- Group the classes by their last entry, and apply
  -- `sum_mul_norm_sum_cosetAmplitude_sq_le_lastEntryDensity` to each group. `R t` is the product of
  -- the top kernels at the infinite places, and `ρ t p` that of the scalars in
  -- `normalizedOrbitalIntegral`.
  intro r x y
  let R (t : Eˣ) : Matrix (Fin 𝔰.ϱ → T₀) (Fin 𝔰.ϱ → T₀) ℂ :=
    fun p q ↦ ∏ v, (S.besselSystem v).bandLimit 𝔰.n (x v p t) (x v q t)
  let ρ (t : Eˣ) (p : Fin 𝔰.ϱ → T₀) : ℝ :=
    ∏ v, √𝔰.openCellConst * √(‖(x v p t 𝔰.ϱ).1‖ ^ 2 - 1) ^ (𝔰.k - 1) /
      card (S.besselSystem v).Index *
      ∏ a ∈ range 𝔰.ϱ, ‖(x v p t a).1‖ ^ (𝔰.k + 1 + 2 * (𝔰.ϱ - (a + 1)))
  have h_weight (i : ι) (p : Fin 𝔰.ϱ → T₀) :
      ρ (t i) p * (G.headDensity 𝔰.ϱ (y p (t i)) 1).toReal =
        r * √((∏ v, (‖Φ v (t i).1‖ ^ 2 - S.N ^ 2)) ^ (𝔰.k - 1)) :=
    gramScalar_mul_headDensity hG hk hT₀ (h_large i) p
  -- the classes with the last entry of `i`
  have h_top (i : ι) :
      ∑ j : {j // t j = t i}, r ^ 2 * ‖∑ p : Fin 𝔰.ϱ → T₀, S.cosetAmplitude .cut (c j)
          (S.reduction (n j)) (c' j)
          (Floors.FloorGroups.weylElem 𝔰.ϱ (padTuple (fun a ↦ (p a).1) (t i)) * σ j)‖ ^ 2 ≤
        (1 + S.b⁻¹ ^ 6) * S.scaledSiegelConst * (∑ p, ∑ q, R (t i) p q *
          (G.lastEntryDensity (S.piNAt T) Y (y p (t i)) (y q (t i)) / Y.massRatio.toReal)).re := by
    have h_fiber_tail (j : {j // t j = t i}) : S.frameProducts (σ j) 𝔰.top 𝔰.top = t i := by
      rw [h_tail j, j.2]
    have h_fiber_gram (j : {j // t j = t i}) : R (t i) = .gram ℂ fun p : Fin 𝔰.ϱ → T₀ ↦
        ρ (t i) p • besselOrbitalIntegral volume (fun g ↦ .toLp 2 (S.besselFn .cut g))
          (S.ratToInf
            (Floors.FloorGroups.weylElem 𝔰.ϱ (padTuple (fun a ↦ (p a).1) (t i)) * σ j)) :=
      prod_bandLimit_eq_gram (hσ j) (h_fiber_tail j)
    have h_head (p : Fin 𝔰.ϱ → T₀) (l : ℕ) (hl : l < 𝔰.ϱ) :
        (padTuple (fun a ↦ (p a).1) (t i) l).1 ∈ ratIntegralOff T ∧
          (padTuple (fun a ↦ (p a).1) (t i) l)⁻¹.1 ∈ ratIntegralOff T := by
      simpa only [padTuple, dite_eq_left hl] using hT₀ _ (p ⟨l, hl⟩).2
    exact hG.sum_mul_norm_sum_cosetAmplitude_sq_le_lastEntryDensity hT_basis hT_N
      (j := {j // t j = t i})
      (c := (c ·)) (c' := (c' ·)) (h_inj.comp Subtype.val_injective) (hσ ·) h_fiber_tail (h_large i)
      (hn_mem_Y ·) (h_off ·) ⟨i, rfl⟩ (fun p ↦ by simp [padTuple]) h_head h_fiber_gram (h_weight i)
  rw [mul_sum, ← sum_fiberwise_of_maps_to fun i ↦ mem_image_of_mem t, re_sum, mul_sum]
  refine sum_le_sum (forall_mem_image.2 fun i _ ↦ ?_)
  rw [sum_subtype (p := fun j : ι ↦ t j = t i) (F := inferInstance) _ (by simp)]
  simpa only [Subtype.prop (p := (t · = t i))] using h_top i

/-- Let `S` be an admissible filling of shape `𝔰` over a CM field `E` with Weil data, with size
parameter `b = S.b`, and `Sg` a set of chosen places above the first level prime p₀
(`S.chosenPlaces 0`). Take finitely many distinct classes `(c i, S.reduction (n i), c' i, σ i)`
whose last entries `t i` lie in a finite set `T₀` of units off `T`, whose positions are integral off
`T` and whose reductions are in `S.fixer Sg D`. Here `σ i` is in the floor group, its last frame
product is `t i`, and ‖t i‖² > N² at every infinite place; `1 / M`, `1 / N`, the lattice basis and
its inverse are integral off `T`. The double coset sum `S.cosetAmplitude .cut c s c' γ` adds the
amplitudes of the cut Bessel function at `u γ u'⁻¹` over the rational unipotent `u`, `u'` for which
this element lies over `(c, s, c')`. These sums, added over the heads with entries in `T₀`, have
total square norm at most `(1 + b⁻⁴) b^(-6 𝔰.k |Sg|)` times
`mainSecondMoment = sourceDim² / (besselDegree * mass)` times `unipotentCovolume²`. -/
lemma sum_norm_sum_cosetAmplitude_sq_le [S.IsAdmissible] (Sg : Finset (S.chosenPlaces 0))
    (D : ∀ w : S.chosenPlaces 0, S.FrameVector w) {ι : Type} [Fintype ι] {c c' : ι → S.Classes}
    {σ : ι → S.G E} {n : ι → S.latticeStabilizer} {t : ι → Eˣ}
    (h_inj : (fun i : ι ↦ (c i, c' i, S.reduction (n i), σ i)).Injective)
    (hσ : ∀ i : ι, σ i ∈ Shape.Form.floorGroup 𝔰.ϱ)
    (h_tail : ∀ i : ι, S.frameProducts (σ i) 𝔰.top 𝔰.top = t i)
    (h_large : ∀ (i : ι) (v : NumberField.InfinitePlace E), S.N ^ 2 < ‖Φ v (t i).val‖ ^ 2)
    (hn_fix : ∀ i : ι, S.reduction (n i) ∈ S.fixer Sg D)
    {T₀ : Finset Eˣ} (ht : ∀ i : ι, t i ∈ T₀) {T : Finset (FinPlace E)} [T.StarStable]
    (hT₀ : ∀ x ∈ T₀, x.val ∈ ratIntegralOff T ∧ x⁻¹.val ∈ ratIntegralOff T)
    [hT_M : Fact (S.ideleM⁻¹.val ∈ integralOff T)]
    (hT_basis : S.latticeBasis ∈ intGL 𝔰.BesselIndex (integralOff T))
    (hT_N : (S.N : E)⁻¹ ∈ ratIntegralOff T)
    (h_off : ∀ i : ι, S.IsIntegralOff T (S.translateByClassReps (c i) (c' i) (σ i))) :
    ∑ i : ι, ‖∑ p : Fin 𝔰.ϱ → T₀, S.cosetAmplitude .cut (c i) (S.reduction (n i)) (c' i)
        (Floors.FloorGroups.weylElem 𝔰.ϱ (padTuple (fun a : Fin 𝔰.ϱ ↦ (p a).val) (t i)) *
          σ i)‖ ^ 2 ≤
      (1 + (S.b ^ 4)⁻¹) * (S.b ^ (6 * 𝔰.k))⁻¹ ^ #Sg * S.mainSecondMoment *
        S.unipotentCovolume ^ 2 := by
  classical
  -- Siegel's step bounds the sum by the top densities, `sieve` bounds these, and
  -- `sieve_constant_le` evaluates the constant.
  obtain ⟨kPred, hk⟩ : ∃ kPred : ℕ, 𝔰.k = kPred + 1 := ⟨𝔰.k - 1, by grind [S.thousand_mul_le_k]⟩
  -- at `T`: a filling datum `G`, and a group `Y` that contains the components of the `n i` and
  -- whose normalised forms are a system for the sieve, with the density at the last entry as top
  -- form
  obtain ⟨P, G, hG⟩ := S.exists_isFillingData T
  obtain ⟨Y, hY_mem, hY_sys⟩ := hG.exists_intermediateGroup_sieveSystem Sg D
  -- the heads at the infinite place `v` and at `T`, and the weighted sum of the top densities
  let x (v : NumberField.InfinitePlace E) (p : Fin 𝔰.ϱ → T₀) (t : Eˣ) (a : ℕ) : ℂˣ :=
    unitOrOne (S.frameScaleSq v a * Φ v (padTuple (fun b ↦ (p b).val) t a).val)
  let y (p : Fin 𝔰.ϱ → T₀) (t : Eˣ) : ℕ → (LocProd T)ˣ :=
    Units.map (ratToPlaces T) ∘ padTuple (fun a ↦ (p a).val) t
  let topSum : ℝ := (∑ t' ∈ univ.image t, ∑ p : Fin 𝔰.ϱ → T₀, ∑ q : Fin 𝔰.ϱ → T₀,
    (∏ v, (S.besselSystem v).bandLimit 𝔰.n (x v p t') (x v q t')) *
      (G.lastEntryDensity (S.piNAt T) Y (y p t') (y q t') / Y.massRatio.toReal)).re
  have h_siegel : S.normalizingConst kPred ^ 2 * ∑ i : ι, ‖∑ p : Fin 𝔰.ϱ → T₀,
      S.cosetAmplitude .cut (c i) (S.reduction (n i)) (c' i)
        (Floors.FloorGroups.weylElem 𝔰.ϱ (padTuple (fun a ↦ (p a).val) (t i)) * σ i)‖ ^ 2 ≤
      (1 + S.b⁻¹ ^ 6) * S.scaledSiegelConst * topSum :=
    hG.mul_sum_norm_sum_cosetAmplitude_sq_le Y hk h_inj hσ h_tail h_large
      (fun i ↦ hY_mem (n i) (hn_fix i)) hT₀ hT_basis hT_N h_off
  have h_sieve : topSum ≤ (∏ i ∈ range 𝔰.n, S.poissonConst i) *
      ((∏ v, (1 + S.b⁻¹ ^ 10) / (S.besselSystem v).deg) *
          ((1 + S.b⁻¹ ^ 6) / (S.b ^ (6 * 𝔰.k)) ^ #Sg) +
        S.b ^ (2403 * 𝔰.n ^ 9 * Core.numInfPlaces E) * S.decayConst) := by
    have h_top_index : ¬𝔰.n ≤ 𝔰.ϱ := Nat.not_succ_le_self 𝔰.ϱ
    simpa only [ite_eq_right h_top_index] using
      S.sieve T hT₀ hT_M.out hY_sys (U := univ.image t) (image_subset_iff.2 fun i _ ↦ ht i)
  have h_coeff : 0 ≤ (1 + S.b⁻¹ ^ 6) * S.scaledSiegelConst := by
    unfold scaledSiegelConst siegelConst
    positivity
  have hSg : #Sg ≤ Core.numInfPlaces E := Sg.card_le_univ.trans_eq (S.card_chosenPlaces 0)
  refine le_of_mul_le_mul_left (h_siegel.trans ?_) (normalizingConst_sq_pos kPred)
  exact (mul_le_mul_of_nonneg_left h_sieve h_coeff).trans (sieve_constant_le hk hSg)

/-- Let `S` be an admissible filling of shape `𝔰` over a CM field `E` with Weil data, `Sg` a set of
chosen places above the first level prime p₀, and `D w` a nonzero vector of the span of the frame
modulo `w` or modulo its conjugate. On the left, `linkSecondMoment` sums the squared norms of the
class sums of the cut function over all links, pairs of classes, and reductions `s` that are open
and fix `D w` for `w ∈ Sg`. With `X` the isotropic span of `e₁, …, e_ϱ`, the link of a term `γ` is
the module of pairs of classes in `X^⊥/X` of `t` and `γ⁻¹ t`, for `t` orthogonal to `X` and `γ X`;
each class sum runs over the terms of one link. Only terms `γ` with
`termDisc γ = |Δ|² - N² |Δ'|² ≠ 0` enter, where `Δ` is the determinant and `Δ'` the leading minor of
size ϱ of the frame products of `γ`. The bound is `(1 + b⁻⁴) b^(-6 𝔰.k |Sg|)` times
`mainSecondMoment = sourceDim² / (besselDegree * mass)` times `unipotentCovolume²`. Here `b` is the
size parameter of `S`, `𝔰.k` is the rank of X₀, `mass` is the mass of the genus of the standard
Hermitian lattice of rank `𝔰.r`, and `unipotentCovolume` is an explicit number which, if `E`
contains a primitive 5040th root of unity, is the integral of the cutoff `S.classCutoff c` over the
real unipotent group, for every class `c` (`lintegral_classCutoff_eq_unipotentCovolume`). -/
theorem linkSecondMoment_isOpenElement_le [S.IsAdmissible] (Sg : Finset (S.chosenPlaces 0))
    (D : ∀ w : S.chosenPlaces 0, S.FrameVector w) :
    linkSecondMoment {γ : S.G E | S.termDisc γ ≠ 0}
      {s : S.ResidueGL | s ∈ S.fixer Sg D ∧ S.IsOpenElement s} ≤
      .ofReal ((1 + (S.b ^ 4)⁻¹) * (S.b ^ (6 * 𝔰.k))⁻¹ ^ #Sg * S.mainSecondMoment *
        S.unipotentCovolume ^ 2) := by
  -- The left side is a sum of squared norms of blocks. It suffices to bound finite sums `F` of
  -- nonzero blocks; each is a finite sum of double coset sums over the tuples `p` of entries in
  -- `S.entrySet`. These entries are units off the set `T` of places, and the inverses of the level
  -- and of `N` are integral there.
  obtain ⟨T, _, hT₀, hT_M, hT_basis, hT_N⟩ := S.exists_places_integralOff S.entrySet
  simp_rw [linkSecondMoment, ← ENNReal.tsum_prod]
  refine (tsum_subtype_support _).ge.trans (ENNReal.summable.tsum_le_of_sum_le fun F ↦ ?_)
  -- a block `j` has two classes, a reduction and a link
  let block (j : F) : S.Classes × S.Classes × {s | s ∈ S.fixer Sg D ∧ S.IsOpenElement s} ×
      Submodule E (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex → E) := j.val.val
  let c (j : F) : S.Classes := (block j).fst
  let c' (j : F) : S.Classes := (block j).snd.fst
  let s (j : F) : S.ResidueGL := (block j).snd.snd.fst
  let Λ (j : F) : Submodule E (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex → E) := (block j).snd.snd.snd
  let classSum (j : F) : EuclideanSpace ℂ (S.BesselCoord × S.BesselCoord) :=
    S.amplitudeSum .cut (S.termsOfLink (Λ j)) (c j) (s j) (c' j)
  have hs (j : F) : s j ∈ S.fixer Sg D ∧ S.IsOpenElement (s j) := (block j).snd.snd.fst.prop
  have h_ne (j : F) : classSum j ≠ 0 := by simpa using show ‖classSum j‖ₑ ^ 2 ≠ 0 from j.val.prop
  have h_class (j : F) : ∃ (t : Eˣ) (σ : S.G E) (n : S.latticeStabilizer),
      S.NamesLink T (c j) (s j) (c' j) (Λ j) t σ n ∧
      classSum j = ∑ p : Fin 𝔰.ϱ → S.entrySet, S.cosetAmplitude .cut (c j) (s j) (c' j)
        (Floors.FloorGroups.weylElem 𝔰.ϱ (padTuple (fun a ↦ (p a).1) t) * σ) :=
    exists_amplitudeSum_eq_sum_cosetAmplitude hT₀ (h_ne j)
      fun _ ↦ (hs j).right.leadingMinor_ne_zero
  choose t σ n h_names h_sum using h_class
  have h_red (j : F) : S.reduction (n j) = s j := (h_names j).reduction_eq
  -- distinct blocks give distinct tuples `(c j, c' j, S.reduction (n j), σ j)`: `S.reduction (n j)`
  -- is the reduction of `j` and `σ j` determines its link
  have h_inj : (fun j ↦ (c j, c' j, S.reduction (n j), σ j)).Injective := by
    intro i j h
    obtain ⟨hc, hc', h_s, h_eq⟩ : c i = c j ∧ c' i = c' j ∧ s i = s j ∧ σ i = σ j := by
      simpa [h_red] using h
    have hΛ : Λ i = Λ j := by rw [(h_names i).link_eq, (h_names j).link_eq, h_eq]
    exact Subtype.ext (Subtype.ext (Prod.ext hc (Prod.ext hc' (Prod.ext (Subtype.ext h_s) hΛ))))
  have h_bound : ∑ j : F, ‖classSum j‖ ^ 2 ≤
      (1 + (S.b ^ 4)⁻¹) * (S.b ^ (6 * 𝔰.k))⁻¹ ^ #Sg * S.mainSecondMoment *
        S.unipotentCovolume ^ 2 := by
    simpa only [h_sum, ← h_red] using sum_norm_sum_cosetAmplitude_sq_le Sg D h_inj
      (fun j ↦ (h_names j).mem_floorGroup)
      (fun j ↦ (h_names j).frameProducts_top_top) (fun j ↦ (h_names j).sq_lt_norm_sq)
      (by simpa only [h_red] using fun j ↦ (hs j).left)
      (fun j ↦ (h_names j).mem_entrySet) hT₀ hT_basis hT_N fun j ↦ (h_names j).isIntegralOff
  refine le_of_eq_of_le ?_ (ENNReal.ofReal_le_ofReal h_bound)
  simp only [ENNReal.ofReal_sum_of_nonneg fun j _ ↦ sq_nonneg ‖classSum j‖,
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  exact (F.sum_coe_sort _).symm

end New.Filling

end MainTermEstimate
