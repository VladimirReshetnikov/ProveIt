import Lib.Weil.DualPair.Flip
import New.Determinant.Exchange.RealVectors
import New.Determinant.Exchange.VanishingDescends

/-!
# Exchange of theta integrals for matched functions and for data modulo an ideal

The exchange identity compares the theta integrals to U(W) from two spaces of complementary ranks.
For matched functions at the ramified places of a tame character, it holds with a constant whose
absolute value is expressed, up to a factor free of the character, through L-values and the ratio
`New.Exchange.equalRankThetaRatio`. This ratio is the squared absolute value of the theta integral
in equal rank, divided by the product of L-values `L_*` at half the rank of the space. For a
suitable Schwartz vector it is a nonzero constant that does not depend on the character. Together
these give the exchange theorem for finite data given by functions on matrices over `O_E / 𝔪`.

## Main definitions and results

* `New.Exchange.exchange_of_matches`: the exchange identity, with the constant measured by
  `New.Exchange.lValueProdInt` and `New.Exchange.equalRankThetaRatio`.
* `New.Exchange.exists_equalRankThetaRatio_eq_const`: the value of that ratio on `H ⊕ W`, for `W` of
  rank `2 k + 2 q` with `q` negative signs and `k ≤ μ`.
* `New.Exchange.exchange_theorem`, `New.Exchange.exchange_identity`: the exchange theorem, for one
  choice and for all choices of splitting characters.

Notions from other files:
* `New.PairFock E s t` is the Fock space of real data for a pair of spaces with signs `s`, `t`. A
  vector is a Schwartz vector (`New.Exchange.IsSchwartzVector`) if all its moments `fockMoment N v`
  are finite.
* `New.Exchange.thetaIntegral S T a b f` is the function g ↦ ∫ θ^{S,T}_{a,b}(f)(g,h) dh on U(S), the
  integral of the theta kernel `New.pairTheta` over [U(T)]. `New.Exchange.thetaLarge` and
  `New.Exchange.thetaSmall` are its cases for a datum v ⊗ Φ: Φ is read at the ramified places of a
  tame character, or Φ of the transpose is read at their conjugates.
* `New.Exchange.SplitTameChar.semilocalChar` is the character t ↦ ν(t/t̄) of ∏_{w∈S} E_w, t read as
  an idele supported on S, extended by 0 to non-invertible elements.
* `New.Exchange.lValueProd` is the number `L_*(e)` = (∏_{w ∈ S} Nw)^(e²) · ∏_{z=1}^{e}
  |L^S(z, ν)|²; `New.Exchange.lValueProdInt` extends it to integers by `L_*(-e) = L_*(e)⁻¹`.
* `υ` is the splitting character of the Weil data, `upsilonU1` its restriction to the norm-one
  ideles, and `rankTwist a n` is the character `a υ ^ ⌊|n| / 2⌋` of [U(1)].
* `AreMatched O σ χ Φ Ψ` says that `Φ` and `Ψ` are supported on the last rows of `k⁻¹` and the first
  columns of `k`, for `k` invertible over `O` and split by `σ`, and differ there by `χ (det k)`.
* `stdRowDatum σ χ z` and `stdColDatum χ z` are the standard functions of an integral matrix `z`:
  they send `x` to `χ⁻¹` of the determinant of `z` stacked on `x`, respectively of `z * x`, and to
  zero where this is not defined over the integers.
* `localDatum S T v Φ r` is the vector with real part `v`, the function `Φ` at the places that `r`
  reads, and the vacuum elsewhere; `modDatum S T 𝔪 Φ v` is the same for a function `Φ` modulo `𝔪`.

## Relation to the literature

Let V and V' be hermitian spaces of type `New.Space` over a CM field with `New.WeilData` whose ranks
and negative signs add up to those of W, which has q negative signs, with 2q + 2 ≤ rk W and rk
V − rk V' = 2e ≥ 0, and let the weights μ satisfy rk W ≤ 2μ + 2q. Then theta integrals over U(V) and
U(V') agree on matched ramified data up to a nonzero constant c, so theta lifts can be exchanged.
Only |c|² is given, up to an uncomputed factor: it is sized by the conductor and the Hecke L-values
at 1,…,e. Equal theta lifts of characters of complementary groups are known for trivial characters
(Siegel–Weil) and for O(3), O(1) to Mp(2). Related work: Snitz, Theta correspondence of automorphic
characters, J. Number Theory 122 (2007), arXiv math/0509486; Erez, Morphisms of global theta lifts
of non-trivial automorphic characters of orthogonal groups, arXiv 2401.13469, 2024; Gan–Qiu–Takeda,
The regularized Siegel–Weil formula (second term identity) and the Rallis inner product formula,
2014.
-/

noncomputable section

namespace New.Exchange

/-!
## The exchange identity for matched functions

`New.Exchange.exchange_of_matches` compares the theta integrals to U(W) from two spaces V and U of
complementary ranks. The identity at the top of the tower descends by removing planes
(`exists_rowColExchangeIdentity_of_even_rank`), passes from standard data to all matched functions
(`thetaLarge_eq_smul_of_areMatched`), and is translated from `(W, U⁻)` back to `(U, W)`
(`exists_mul_thetaSmall_adjointDatum_eq_mul_integral`).
-/

section ExchangeCore

open Matrix MeasureTheory NumberField Fintype Fock CoordChange Weil Seesaw

variable {E : Type} [Field E] [CMType E] [WeilData E] {n r b : Type} [Fintype n] [DecidableEq n]
  [Fintype r] [DecidableEq r] [Fintype b] [DecidableEq b] {s : n → ℤˣ} {t : r → ℤˣ} {u : b → ℤˣ}

variable (E s u) in
/-- Passing to adjoint maps: the change of coordinates that carries data for the pair `(U, W)` to
data for `(W, U⁻)`. Here `W` has signs `s`, `U` has signs `u` and the opposite space `U⁻` has
signs `-u`. -/
abbrev adjointCoords : CoordChange E (.id ℂ) (homSigns u s) (homSigns s (-u)) :=
  flipCoords (E := E) (s := s) star_normNegOne_mul_self (t := u) rfl

/-- On finite adelic matrices `adjointCoords` is the conjugate transpose, scaled by the integral
unit `normNegOne` of norm `-1`. -/
lemma adjointCoords_finEquiv_apply (x : b × n → 𝔸f E) (i : n × b) :
    (adjointCoords E s u).finEquiv x i = (normNegOne (E := E) : Ô E) * star (x i.swap) :=
  rfl

/-- The real vector `y^ad` for `(W, U⁻)` that belongs to a real vector `y` for `(U, W)`: the image
of `y` under the real part of `adjointCoords`. -/
def adjointDatum (y : PairFock E u s) : PairFock E s (-u) := (adjointCoords E s u).realMap y

/-- Let `U`, `W` have signs `u`, `s` and let `y` be a vector of the real Fock space of `(U, W)` all
of whose moments are finite. Then so are all moments of `adjointDatum y`, the vector for `(W, U⁻)`
obtained by passing to adjoint maps; the opposite space `U⁻` has signs `-u`. -/
lemma IsSchwartzVector.adjointDatum {y : PairFock E u s} (hy : IsSchwartzVector y) :
    IsSchwartzVector (adjointDatum y) := by
  -- The real part `f.realEquiv` of the change of coordinates preserves the norm and the measure.
  let f : CoordChange E (.id ℂ) (homSigns u s) (homSigns s (-u)) := adjointCoords E s u
  have h_norm (x : InfinitePlace E × b × n → ℂ) : ‖f.realEquiv x‖₊ = ‖x‖₊ := by
    have h_coord (i : InfinitePlace E × n × b) : ‖f.realEquiv x i‖₊ = ‖x (i.1, i.2.swap)‖₊ := by
      simp [f, flipCoords, starCoordEquiv, nnnorm, Prod.map, abs_unit_intCast]
    refine eq_of_forall_ge_iff fun c ↦ ?_
    simp only [pi_nnnorm_le_iff, h_coord, Prod.forall, Prod.swap_prod_mk]
    exact forall_congr' fun _ ↦ forall_comm
  have h_measure : MeasurePreserving f.realEquiv (normalizedVolume _) (normalizedVolume _) :=
    Heisenberg.IsVacuum.measurePreserving_equiv (realHeisenberg 1) (realHeisenberg 1)
      f.vac_realEquiv
  intro N
  calc fockMoment N (Exchange.adjointDatum y)
      = ∫⁻ x, (1 + ‖f.realEquiv x‖ₑ) ^ N * ‖y (f.realEquiv x)‖ₑ ∂normalizedVolume _ := by
        simp only [enorm, h_norm]
        rfl
    _ = fockMoment N y := h_measure.lintegral_comp_emb f.realEquiv.measurableEmbedding
        fun x ↦ (1 + ‖x‖ₑ) ^ N * ‖y x‖ₑ
    _ ≠ ⊤ := hy N

/-- `New.G.neg` carries the rational points of `U` onto those of the opposite space
`U⁻ = flipSpace U`. -/
lemma neg_mem_flipSpace_Gamma_iff (U : Space E b u) (g : G E u) :
    G.neg g ∈ (flipSpace U).Γ ↔ g ∈ U.Γ := by
  simp [flipSpace, Space.mem_Gamma_iff_range, ← map_inv, ← smul_one_eq_diagonal, ← mul_assoc,
    ← star_mul]

/-- Multiplying the argument by a unit `ε` of `O` divides the second of two matched functions by
`χ ε ^ card b`, the value of `χ` at the determinant of the scalar matrix `ε` of size `b`. -/
lemma _root_.New.AreMatched.right_eq_pow_mul_apply_smul {R : Type} [CommRing R] {O : Subring R}
    {σ : b ⊕ r ≃ n} {χ : MulChar R ℂ} {Φ : Matrix r n R → ℂ} {Ψ : Matrix n b R → ℂ}
    (h : AreMatched O σ χ Φ Ψ) (ε : Oˣ) (X : Matrix n b R) :
    Ψ X = χ ε ^ card b * Ψ ((ε.val : R) • X) := by
  have h_smul : (ε.val : R) • X = X * scalar b (ε.val : R) := by simp [← ext_iff, mul_comm]
  rw [h_smul, mul_comm]
  simpa [eq_comm] using h.right_mul _ ⟨.scalar b ε, rfl⟩ X

/-- Let `σ` split `n` into `b` and `r`, let `𝔠` be a tame character: a character `ν = 𝔠.character`
of `[U(1)]` of weight `μ`, tamely ramified exactly at a finite set `S = 𝔠.ramifiedPlaces` of split
places, and let `y` lie in the real Fock space of `(U, W)`. There is a number `a` of modulus one
with the following property. Let `Ψ` be a Schwartz–Bruhat function on left invertible matrices that
is matched with some `Φ`: `Φ` is supported on the last rows of `k⁻¹` and `Ψ` on the first columns of
`k` (split by `σ`), for `k` in `GL_n` of the local integers at `S`, and there
`Φ = 𝔠.semilocalChar (det k) * Ψ`. Let `U⁻ = flipSpace U` be the opposite space, `adjointCoords` the
passage to adjoint maps from `(U, W)` to `(W, U⁻)`, and `y^ad = adjointDatum y` the image of `y`.
Then the datum with real part `y^ad`, the function `x ↦ Ψ xᵀ` at the conjugates of `S`
(`𝔠.readsAt.star`) and the vacuum elsewhere is `a` times the image of the datum with real part `y`,
the function `Ψ` at `S` (`𝔠.readsAt`) and the vacuum elsewhere. -/
lemma exists_localDatum_adjointDatum_eq_smul (W : Space E n s) (U : Space E b u) (σ : b ⊕ r ≃ n)
    {μ : InfinitePlace E → ℤ} (𝔠 : SplitTameChar E μ) (y : PairFock E u s) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ ∀ (Φ : Matrix r n (LocProd 𝔠.ramifiedPlaces) → ℂ)
      (Ψ : Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ),
      Ψ ∈ schwartzBruhat HasLeftInv → AreMatched SemilocalField.O σ 𝔠.semilocalChar Φ Ψ →
        localDatum W (flipSpace U) (adjointDatum y)
            (fun x : Matrix b n (LocProd 𝔠.ramifiedPlaces) ↦ Ψ xᵀ) 𝔠.readsAt.star =
          a • (adjointCoords E s u).map (localDatum U W y Ψ 𝔠.readsAt) := by
  let f : CoordChange E (.id ℂ) (homSigns u s) (homSigns s (-u)) := adjointCoords E s u
  -- `ε` is the component at `𝔠.ramifiedPlaces` of the integral unit `normNegOne` of norm `-1`.
  let ε : (SemilocalField.O : Subring (LocProd 𝔠.ramifiedPlaces))ˣ :=
    normNegOne.map ((evalPlaces 𝔠.ramifiedPlaces).restrict _ _ evalPlaces_mem_O).toMonoidHom
  refine ⟨𝔠.semilocalChar ε ^ card b,
    by simp [TameLocalChar.norm_eq_one, IsIntegralUnit, isIntegralUnit_iff_isUnit.2],
    fun Φ Ψ hΨ hΦΨ ↦ ?_⟩
  -- The flip transposes the matrix and scales it by `ε`, dividing `Ψ` by
  -- `𝔠.semilocalChar ε ^ card b`.
  have h_scale (x : b × n → 𝔸f E) :
      Ψ ((vecToMatrix x).map ((evalPlaces 𝔠.ramifiedPlaces).comp (starRingEnd (𝔸f E))))ᵀ =
        𝔠.semilocalChar ε ^ card b * Ψ ((vecToMatrix (f.finEquiv x)).map
          (evalPlaces 𝔠.ramifiedPlaces)) := by
    have h_matrix : (vecToMatrix (f.finEquiv x)).map (evalPlaces 𝔠.ramifiedPlaces) =
      (ε.val : LocProd 𝔠.ramifiedPlaces) •
        ((vecToMatrix x).map ((evalPlaces 𝔠.ramifiedPlaces).comp (starRingEnd (𝔸f E))))ᵀ := by
      simp [f, adjointCoords_finEquiv_apply, vecToMatrix, starRingEnd_apply, ← ext_iff, ε]
    rw [h_matrix]
    exact hΦΨ.right_eq_pow_mul_apply_smul ε _
  rw [map_integrated, flipCoords_map_schrodingerOp _ _ U W (flipSpace U) 𝔠.readsAt.disjoint_star _
    (hΨ := 𝔠.readsAt.isSchwartzBruhat hΨ), ← map_smul, Space.smul_schrodingerOp]
  -- Both sides have real part `y^ad`; the functions that name their finite parts agree.
  change (W.hom (flipSpace U)).integrated (adjointDatum y) ((W.hom (flipSpace U)).schrodingerOp
      (star ⁻¹' (𝔠.ramifiedPlaces : Set (FinPlace E)))
      (fun x ↦ Ψ ((vecToMatrix x).map ((evalPlaces 𝔠.ramifiedPlaces).comp (starRingEnd (𝔸f E))))ᵀ)
        _) =
    (W.hom (flipSpace U)).integrated (adjointDatum y) ((W.hom (flipSpace U)).schrodingerOp _
      (fun x ↦ 𝔠.semilocalChar ε ^ card b * Ψ
        ((vecToMatrix (f.finEquiv x)).map (evalPlaces 𝔠.ramifiedPlaces))) _)
  simp only [h_scale]

/-- Let `W` have even rank, split by `σ` into `b` and `r`, let `𝔠` be a tame character: a character
`ν = 𝔠.character` of `[U(1)]` of weight `μ`, tamely ramified exactly at a finite set
`S = 𝔠.ramifiedPlaces` of split places, and put `γ = rankTwist ν⁻¹ n = ν⁻¹ υ ^ (rk W / 2)`. There is
a number `d` of modulus one with the following property. Let `Ψ` be a Schwartz–Bruhat function on
left invertible matrices that is matched with some `Φ`: `Φ` is supported on the last rows of `k⁻¹`
and `Ψ` on the first columns of `k` (split by `σ`), for `k` in `GL_n` of the local integers at `S`,
and there `Φ = 𝔠.semilocalChar (det k) * Ψ`. Let `U⁻ = flipSpace U` be the opposite space and
`y^ad = adjointDatum y` the image of `y` under passage to adjoint maps. Then for `g` in the adelic
group `U(W) = G E s`, `γ (det g)` times `thetaSmall`, the theta integral of `(W, U⁻)` over `[U(U⁻)]`
with characters `ν υ ^ (rk W / 2)`, `υ ^ rk U`, real part `y^ad` and `x ↦ Ψ xᵀ` at the conjugates of
`S`, is `d` times the integral over the quotient `[U(U)]` of the theta kernel `pairTheta` of
`(U, W)` with characters `γ`, `γ`, real part `y` and `Ψ` at `S`. -/
lemma exists_mul_thetaSmall_adjointDatum_eq_mul_integral (W : Space E n s) (U : Space E b u)
    (σ : b ⊕ r ≃ n)
    (h_even : 2 ∣ card n) {μ : InfinitePlace E → ℤ} (𝔠 : SplitTameChar E μ) (y : PairFock E u s) :
    ∃ d : ℂ, ‖d‖ = 1 ∧ ∀ (Φ : Matrix r n (LocProd 𝔠.ramifiedPlaces) → ℂ)
      (Ψ : Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ),
      Ψ ∈ schwartzBruhat HasLeftInv → AreMatched SemilocalField.O σ 𝔠.semilocalChar Φ Ψ →
        ∀ g : G E s,
        (rankTwist 𝔠.character⁻¹ n).val g.det * thetaSmall W (flipSpace U) 𝔠 (adjointDatum y) Ψ g =
          d * ∫ h : G E u, pairTheta U W (rankTwist 𝔠.character⁻¹ n) (rankTwist 𝔠.character⁻¹ n)
            (localDatum U W y Ψ 𝔠.readsAt) (h, g) ∂U.quotMeasure := by
  -- The flip changes the theta kernel by a constant `d` and the datum by a constant `a`.
  obtain ⟨d, hd, h_flip⟩ :=
    exists_pairTheta_flip star_normNegOne_mul_self rfl U W (flipSpace U) 1
      (by simp [flipSpace, G.adeleMatrix_one, ← ext_iff]) (rankTwist 𝔠.character⁻¹ n)
  obtain ⟨a, ha, h_datum⟩ := exists_localDatum_adjointDatum_eq_smul W U σ 𝔠 y
  refine ⟨a * d, by rw [norm_mul, ha, hd, mul_one], fun Φ Ψ hΨ hΦΨ g ↦ ?_⟩
  obtain ⟨k, hk⟩ := h_even
  -- `G.neg` carries the integral over `[U(U⁻)]` to the one over `[U(U)]`; compare the characters.
  have h_neg (F : G E (-u) → ℂ) :
      ∫ h : G E (-u), F h ∂(flipSpace U).quotMeasure =
        ∫ h : G E u, F (G.neg h) ∂U.quotMeasure :=
    (isForm_neg_iff_and_integral_neg U (flipSpace U) (neg_mem_flipSpace_Gamma_iff U)).2 F
  rw [thetaSmall, thetaIntegral, h_datum Φ Ψ hΨ hΦΨ, h_neg, ← integral_const_mul,
    ← integral_const_mul]
  congr with h
  -- As `card n = 2 * k`, the characters of the two kernels differ by `γ (det g)`.
  rw [mul_assoc, ← h_flip _ _ h g h.neg (by simp [G.adeleMatrix_neg, G.adeleMatrix_one])]
  simp [pairTheta, pairWeil, pairChar_apply, circleChar_inv_apply, G.det_neg, rankTwist, hk,
    pow_mul', field]

/-- Let `W` have even rank `rk U + rk V` (`σ`, `h_even`), let `𝔠` be a tame character: a character
`ν = 𝔠.character` of `[U(1)]` of weight `μ`, tamely ramified exactly at a finite set
`S = 𝔠.ramifiedPlaces` of split places, put `χ = 𝔠.semilocalChar`, and let `v`, `y` be real Schwartz
vectors. The standard functions `stdRowDatum σ χ z`, `stdColDatum χ z` send `x` to `χ⁻¹` of the
determinant of `z` stacked on `x`, resp. of `z * x`. Suppose that `thetaLarge` is `c` times
`thetaSmall` on them for all `z` with integral entries. Then the same holds for all matched `Φ`, `Ψ`
with `Ψ` locally constant, and `Ψ` has compact support in the left invertible matrices. -/
lemma thetaLarge_eq_smul_of_areMatched (W : Space E n s) (V : Space E r t) (U : Space E b u)
    (σ : b ⊕ r ≃ n) (h_even : 2 ∣ card n) {μ : InfinitePlace E → ℤ} {𝔠 : SplitTameChar E μ}
    {v : PairFock E s t} {y : PairFock E s u} (hv : IsSchwartzVector v) (hy : IsSchwartzVector y)
    {c : ℂ}
    (h_std : ∀ z : Matrix b n (LocProd 𝔠.ramifiedPlaces), IsIntMatrix SemilocalField.O z →
      thetaLarge W V 𝔠 v (stdRowDatum σ 𝔠.semilocalChar z) = c • thetaSmall W U 𝔠 y
        (stdColDatum 𝔠.semilocalChar z))
    {Φ : Matrix r n (LocProd 𝔠.ramifiedPlaces) → ℂ} {Ψ : Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ}
    (hΨ : IsLocallyConstant Ψ) (hΦΨ : AreMatched SemilocalField.O σ 𝔠.semilocalChar Φ Ψ) :
    Ψ ∈ schwartzBruhat HasLeftInv ∧ thetaLarge W V 𝔠 v Φ = c • thetaSmall W U 𝔠 y Ψ := by
  -- The difference `𝒟 Ψ` of the two sides is equivariant, so its kernel is a stable space; it
  -- contains a standard datum, which generates.
  obtain ⟨M, 𝒟, h𝒟, h_diff⟩ : ∃ (M : Submodule ℂ (Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ))
      (𝒟 : (Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ) →ₗ[ℂ] G E s → ℂ),
      IsEquivariantLift 𝔠 W M 𝒟 ∧
      ∀ {Φ : Matrix r n (LocProd 𝔠.ramifiedPlaces) → ℂ}
        {Ψ : Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ},
        IsLocallyConstant Ψ → AreMatched SemilocalField.O σ 𝔠.semilocalChar Φ Ψ →
        Ψ ∈ M ∧ 𝒟 Ψ = thetaLarge W V 𝔠 v Φ - c • thetaSmall W U 𝔠 y Ψ :=
    exists_isEquivariantLift_eq_thetaLarge_sub_smul W V U 𝔠 σ h_even hv hy c
  obtain ⟨h_primitive, z, hz, h_inv⟩ :=
    isPrimitiveMatrix_firstCols σ (one_mem _ : (1 : GL n (LocProd 𝔠.ramifiedPlaces)) ∈ _)
  obtain ⟨h_mem, h_value⟩ :=
    h_diff (stdColDatum_mem_schwartzBruhat _ hz).1 (areMatched_stdRowDatum_stdColDatum σ hz)
  have h_std_ker : stdColDatum 𝔠.semilocalChar z ∈ M ⊓ 𝒟.ker :=
    ⟨h_mem, by simp [h_value, h_std z hz]⟩
  -- The standard datum is taken with multiplicity `1`.
  obtain ⟨hΨ_mem, hΨ_ker : 𝒟 Ψ = 0⟩ :=
    match_mem_of_stdColDatum h𝒟.comp_mul_mem_ker (inf_le_left.trans h𝒟.le_schwartzBruhat) hΨ hΦΨ
      h_std_ker h_primitive hz h_inv 1 (by simp) one_ne_zero
  obtain ⟨-, hΨ_value⟩ := h_diff hΨ hΦΨ
  exact ⟨h𝒟.le_schwartzBruhat hΨ_mem, sub_eq_zero.1 (hΨ_value.symm.trans hΨ_ker)⟩

/-- Let `W₀ = H ⊕ W` with `H` a hyperbolic plane, and let `W` have even rank `rk U + rk V` (`σ`,
`h_even`) and as many negative signs (`negCount`) as `V ⊕ U⁻`, with `U⁻` the opposite space
(`h_signs`). For real Schwartz vectors `z` for `(W₀, W₀)` and `y` for `(W, U)` there is a vector `v`
for `(W, V)` with `RowColExchangeIdentity W V U μ σ v y`: `v` and `y` are Schwartz, and there is a
real `C` such that each tame character `𝔠` of weight `μ` has a number `c` with (a) and (b). (a)
`C |c| ^ 2` is `L_*(rk V - rk W / 2)` times the equal rank ratio `|I(z)(1)| ^ 2 / L_*(rk W₀ / 2)`,
where `I(z)` is the theta integral of `(W₀, W₀)` at `z` and `χ⁻¹(det)`, `χ = 𝔠.semilocalChar`. (b)
On the standard functions `stdRowDatum σ χ`, `stdColDatum χ` of each integral matrix (`χ⁻¹` of the
determinant that it completes), `thetaLarge` over `[U(V)]` at `v` is `c` times `thetaSmall` over
`[U(U)]` at `y`. -/
lemma exists_rowColExchangeIdentity_of_even_rank (W : Space E n s) (U : Space E b u)
    (μ : InfinitePlace E → ℤ) (V : Space E r t) (σ : b ⊕ r ≃ n)
    {z : PairFock E (hyperbolicSigns Unit ⊕ᵥ s) (hyperbolicSigns Unit ⊕ᵥ s)} {y : PairFock E s u}
    (hz : IsSchwartzVector z) (hy : IsSchwartzVector y)
    (h_signs : negCount u + negCount s = card b + negCount t) (h_even : 2 ∣ card n) :
    ∃ v : PairFock E s t, RowColExchangeIdentity W V U μ σ v y
      fun 𝔠 : SplitTameChar E μ ↦ equalRankThetaRatio (hyperbolicSum Unit W) 𝔠 z := by
  -- The tower is `W`, `W₀`, `W₀ ⊕ H ^ rk U`. Take `w` on `W₀` with zero term `y`, and on top the
  -- vectors `x`, `x'` of the large triple, where `x'` has zero term `w`.
  let A : (hyperbolicSum Unit W).Splitting W Unit := removePlanes Unit W
  obtain ⟨w, hw, hw_zero⟩ := exists_isSchwartzVector_realSlice_zero_eq A U hy
  have h_even₀ : 2 ∣ card ((Unit ⊕ Unit) ⊕ n) := by simpa using h_even.add (dvd_refl 2)
  let W₀ : Space E ((Unit ⊕ Unit) ⊕ n) (hyperbolicSigns Unit ⊕ᵥ s) := hyperbolicSum Unit W
  let σ' := (Equiv.sumAssoc b b ((Unit ⊕ Unit) ⊕ n)).symm
  obtain ⟨x, x', hx'_zero, h_top⟩ :=
    exists_rowColExchangeIdentity_sum (removePlanes b W₀) A U σ' h_even₀ μ hw hz
  -- Remove the `rk U + 1` planes; zero terms are taken in stages.
  have h_signs₀ : negCount (u ⊕ᵥ (hyperbolicSigns Unit ⊕ᵥ s)) = card (b ⊕ Unit) + negCount t := by
    simpa +arith [negCount_sumElim, negCount_one_and_neg_one] using h_signs
  have h_zero_term : realSlice ((removePlanes b W₀).symm.comp A) U 0 x' = y := by
    rw [realSlice_zero_comp U W (removePlanes b W₀).symm A x', hx'_zero, hw_zero]
  rw [← h_zero_term]
  exact exists_rowColExchangeIdentity_removing_planes U (U.sum W₀) ((removePlanes b W₀).symm.comp A)
    V σ h_signs₀ h_even h_top

/-- Let `W₀ = H ⊕ W` with `H` a hyperbolic plane, and let `W` have even rank `rk U + rk V` (`σ`,
`h_even`) and as many negative signs as `U` and `V` together (`h_signs`). Let `z` for `(W₀, W₀)` and
`y` for `(U, W)` be real Schwartz vectors. There are `C` and a Schwartz vector `v` for `(W, V)` such
that each tame character `𝔠` of weight `μ` has a number `c` with (a) and (b). Put `ν = 𝔠.character`,
`S = 𝔠.ramifiedPlaces`, `χ = 𝔠.semilocalChar` and `γ = ν⁻¹ υ ^ (rk W / 2)`, where `υ` is the
splitting character of the Weil data on norm-one ideles (`upsilonU1`). (a) `C |c| ^ 2` is
`L_*(rk V - rk W / 2)` times the equal rank ratio `|I(z)(1)| ^ 2 / L_*(rk W₀ / 2)`, where `I(z)` is
the theta integral of `(W₀, W₀)` at `z` and `χ⁻¹(det)`, `L_*(e) = ∏_{w ∈ S} q_w ^ (e ^ 2)
∏_{1 ≤ i ≤ e} |L^S(i, ν)| ^ 2` and `L_*(-e) = L_*(e)⁻¹` (`lValueProdInt`). (b) For all matched
functions `Φ`, `Ψ` with `Ψ` locally constant, the integral over `[U(V)]` of the theta kernel of
`(W, V)` with characters `γ`, `1` at `(v, Φ)` is `c` times the integral over `[U(U)]` of the theta
kernel of `(U, W)` with characters `γ`, `γ` at `(y, Ψ)`, as functions on `U(W) = G E s`. -/
lemma exchange_of_matches (W : Space E n s) (U : Space E b u) (μ : InfinitePlace E → ℤ)
    (V : Space E r t) (σ : b ⊕ r ≃ n)
    {z : PairFock E (hyperbolicSigns Unit ⊕ᵥ s) (hyperbolicSigns Unit ⊕ᵥ s)} {y : PairFock E u s}
    (hz : IsSchwartzVector z) (hy : IsSchwartzVector y)
    (h_signs : negCount s = negCount t + negCount u) (h_even : 2 ∣ card n) :
    ∃ (C : ℝ) (v : PairFock E s t), IsSchwartzVector v ∧ ∀ 𝔠 : SplitTameChar E μ,
      let γ : AutChar E := rankTwist 𝔠.character⁻¹ n
      ∃ c : ℂ,
        -- (a) the modulus of the constant
        C * ‖c‖ ^ 2 =
          lValueProdInt 𝔠 (card r - card n / 2) * equalRankThetaRatio (hyperbolicSum Unit W) 𝔠 z ∧
        -- (b) the identity of theta integrals, for all matched functions
        ∀ (Φ : Matrix r n (LocProd 𝔠.ramifiedPlaces) → ℂ)
          (Ψ : Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ),
          IsLocallyConstant Ψ → AreMatched SemilocalField.O σ 𝔠.semilocalChar Φ Ψ → ∀ g : G E s,
          thetaIntegral W V γ 1 (localDatum W V v Φ 𝔠.readsAt) g =
            c * ∫ h : G E u, pairTheta U W γ γ (localDatum U W y Ψ 𝔠.readsAt) (h, g)
              ∂U.quotMeasure := by
  -- Descend on standard data for `(W, V, U⁻)`, pass to all matched functions, and return to
  -- `(U, W)`.
  have h_signs_flip : negCount (-u) + negCount s = card b + negCount t := by
    linarith [negCount_neg_add u]
  obtain ⟨v, hv, -, C, h_std⟩ :=
    exists_rowColExchangeIdentity_of_even_rank W (flipSpace U) μ V σ hz hy.adjointDatum h_signs_flip
      h_even
  refine ⟨C, v, hv, fun 𝔠 ↦ ?_⟩
  obtain ⟨c, hc, h_std_data⟩ := h_std 𝔠
  obtain ⟨d, hd, h_form⟩ := exists_mul_thetaSmall_adjointDatum_eq_mul_integral W U σ h_even 𝔠 y
  refine ⟨c * d, by rw [norm_mul, hd, mul_one, hc], fun Φ Ψ hΨ hΦΨ g ↦ ?_⟩
  obtain ⟨hΨ_mem, h_eq⟩ := thetaLarge_eq_smul_of_areMatched W V (flipSpace U) σ h_even hv
    hy.adjointDatum h_std_data hΨ hΦΨ
  -- In `thetaLarge` the second character enters as its inverse at `det g`.
  calc thetaIntegral W V (rankTwist 𝔠.character⁻¹ n) 1 (localDatum W V v Φ 𝔠.readsAt) g
      = (rankTwist 𝔠.character⁻¹ n).val g.det * thetaLarge W V 𝔠 v Φ g := by
        rw [thetaLarge, thetaIntegral, thetaIntegral, ← integral_const_mul]
        congr with h
        simp [pairTheta, pairWeil, pairChar_apply, field]
    _ = c * ((rankTwist 𝔠.character⁻¹ n).val g.det *
          thetaSmall W (flipSpace U) 𝔠 (adjointDatum y) Ψ g) := by
        rw [h_eq, Pi.smul_apply, smul_eq_mul, mul_left_comm]
    _ = c * d * ∫ h : G E u, pairTheta U W (rankTwist 𝔠.character⁻¹ n) (rankTwist 𝔠.character⁻¹ n)
          (localDatum U W y Ψ 𝔠.readsAt) (h, g) ∂U.quotMeasure := by
        rw [h_form Φ Ψ hΨ_mem hΦΨ g, mul_assoc]

end ExchangeCore

/-!
## The value of the equal rank theta integral

For `W₀ = H ⊕ W` of even rank and a Schwartz vector `v`, the theta integral of `(W₀, W₀)` on `v` and
the datum `χ⁻¹(det)` is a constant `I₀(v)`. Let `rk W = 2 k + 2 q`, where `q` is the number of
negative signs of `W`, and `k ≤ μ`. We find `v` with `|I₀(v)| ^ 2 = C L_*(rk W₀ / 2)`, where `C ≠ 0`
does not depend on the character (`exists_equalRankThetaRatio_eq_const`). The value for the standard
positive definite `W` (`exists_equalRankThetaRatio_const_ne_zero`) is carried up one hyperbolic
plane at a time; the ratio depends only on the signs of `W₀` (`equalRankThetaRatio_eq_of_signs_eq`).

Let `J` be positive definite of rank `2 k`, `k ≤ μ`, and `Y = H ⊕ J`. For a space `X` write
`r_X(v) = |I(v)(1)| ^ 2 / L_*(rk X / 2)` (`equalRankThetaRatio`), where `I(v)` is the theta integral
of `(X, X)`. Put `L_*(-k) = L_*(k)⁻¹`.

1. Non-vanishing (`exists_equalRankThetaRatio_ne_zero`). Fix the character, and suppose `r_Y(v) = 0`
   for all `v`. The periods that compute the Fourier coefficients for `(H ^ (2 k) ⊕ Y, J⁻ ⊕ Y)` are
   then zero, so this theta integral vanishes on standard data at every Schwartz vector
   (`thetaLargeVanishes_of_equalRankThetaRatio_eq_zero`). Vanishing descends along the `2 k + 1`
   planes to `(J, 0)` (`ThetaLargeVanishes.of_add_planes`, which uses the functional equation of
   `L`). But there the integral of the vacuum is a volume, not zero.
2. The identity used twice (`exists_equalRankThetaRatio_sq_eq`). Fix `v` for `(Y, Y)`. The identity
   for `(J, J, 0)` gives `y` such that `I(y)` is a constant `c₁` times a volume, with
   `B |c₁| ^ 2 = L_*(k) r_Y(v)`. The identity for `(J, 0, J)`, with `y` on the right, gives a number
   `ξ` and `c₂` with `C |c₂| ^ 2 = L_*(-k) r_Y(v)`. Integrating the theta kernel of `y` over both
   groups, in both orders, gives `ξ = c₁ c₂`. So `r_Y(v) ^ 2 = B C |ξ| ^ 2`, where `B`, `C`, `ξ` do
   not depend on the character.
3. The first floor (`exists_equalRankThetaRatio_const_ne_zero`). For the `v` that step 1 gives for
   one character, `r_Y(v) ≥ 0` is one nonzero number for all characters.
4. Adding a plane (`exists_equalRankThetaRatio_add_plane`). Let `W' = W ⊕ H` and `rk W = 2 d`. Given
   `v` for `(W, W)`, choose `v'` for `(W', W')` whose cone integral has the theta integrals of `v`.
   The constant function `I(v')` equals its constant term `κ I(v)(1)`, and `|κ| ^ 2` is a constant
   times `L_*(d + 1) / L_*(d)`.
-/

section EqualRankValue

open MeasureTheory NumberField Fintype Space Equiv Fock MixedModel Heisenberg OrthogonalSum

variable {E n : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n] {s : n → ℤˣ}

/-- Let `𝔠` be a tame character, `χ = 𝔠.semilocalChar` and `γ = rankTwist 𝔠.character⁻¹
n = 𝔠.character⁻¹ υ ^ ⌊rk W / 2⌋`. Suppose that `thetaLarge`, the theta integral of `(W, W)` over
the second `[U(W)]` with characters `γ`, `γ`, vanishes at the finite datum `χ⁻¹(det)`
(`stdColDatum χ 1`) for all real Schwartz vectors, and let `w` be such a vector for `(W, V.sum W)`.
Form `thetaOnRealData`, the theta series as a functional of the real vector, with characters `γ` and
`γ β` for any character `β`, and finite datum `f ⊗ χ⁻¹(det)` (`boxProd` of `f` for `(W, V)` and
`namedVector`, the vacuum with this function put in at the ramified places, which `𝔠.readsAt`
reads), after the Heisenberg translation by the adelic matrix with rows `x` for `V` and `0` for `W`.
Then for `g` in `U(W)` and `y` in `U(V)` its value at `w` and `(g, (y, l))` has integral zero over
`l` in `[U(W)]`. -/
lemma integral_thetaOnRealData_eq_zero (W : Space E n s) {μ : InfinitePlace E → ℤ}
    {𝔠 : SplitTameChar E μ}
    (h_zero : ∀ v : PairFock E s s, IsSchwartzVector v → ∀ g : G E s,
      thetaLarge W W 𝔠 v (stdColDatum 𝔠.semilocalChar 1) g = 0)
    {r : Type} [Fintype r] [DecidableEq r] {t : r → ℤˣ} (V : Space E r t)
    {w : PairFock E s (Sum.elim t s)} (hw : IsSchwartzVector w) (β : AutChar E) (f : 𝒮 (W.hom V))
    (x : Matrix r n (𝔸 E)) (g : G E s) (y : G E t) :
    ∫ l : G E s, thetaOnRealData W (V.sum W) (rankTwist 𝔠.character⁻¹ n)
      (rankTwist 𝔠.character⁻¹ n * β)
      (boxProd (homSigns_sum_target signs_comp_refl) f
        (namedVector W W (stdColDatum 𝔠.semilocalChar 1) 𝔠.readsAt))
      (Matrix.fromRows x 0) (g, G.sum (y, l)) w ∂W.quotMeasure = 0 := by
  -- Expand `w` into coherent states `realHeisenbergOp u vacVector`. The isomorphism `φ` splits `u`
  -- into its coordinates for `V` and for `W`, and the state is the product of the two coherent
  -- states. Evaluating the first factor leaves the datum `∫ w u • F u` for `(W, W)`.
  let α : AutChar E := rankTwist 𝔠.character⁻¹ n
  let f₀ : 𝒮 (W.hom W) := namedVector W W (stdColDatum 𝔠.semilocalChar 1) 𝔠.readsAt
  let T : PairFock E s t →L[ℂ] ℂ := thetaOnRealData W V α β f x (g, y)
  let φ : (InfinitePlace E × (r ⊕ n) × n → ℂ) ≃ₜ+
      (InfinitePlace E × r × n → ℂ) × (InfinitePlace E × n × n → ℂ) :=
    (realCoordSum (realSigns_comp_split (E := E)
      (homSigns_sum_target (s' := s) (signs_comp_refl : Sum.elim t s ∘ _ = _)))).equiv.symm
  let F (u : InfinitePlace E × (r ⊕ n) × n → ℂ) : PairFock E s s :=
    T (realHeisenbergOp (φ u).1 Fock.vacVector) • realHeisenbergOp (φ u).2 Fock.vacVector
  let C : ℝ := ‖T‖ * ‖(Fock.vacVector : PairFock E s t)‖
  have h_moment (N : ℕ) (u : InfinitePlace E × (r ⊕ n) × n → ℂ) : fockMoment N (F u) ≤
      fockMoment N (Fock.vacVector : PairFock E s s) * ENNReal.ofReal C * (1 + ‖u‖ₑ) ^ N := by
    have h_norm : ‖(φ u).2‖ₑ ≤ ‖u‖ₑ := enorm_le_iff_norm_le.2 (pi_norm_comp_le u _)
    have h_coeff : ‖T (realHeisenbergOp (φ u).1 Fock.vacVector)‖ₑ ≤ ENNReal.ofReal C := by
      grw [← ofReal_norm, T.le_opNorm, Heisenberg.Rep.norm_map]
    calc fockMoment N (F u)
        ≤ ENNReal.ofReal C * ((1 + ‖(φ u).2‖ₑ) ^ N *
            fockMoment N (Fock.vacVector : PairFock E s s)) := by
          grw [fockMoment_smul, fockMoment_realHeisenbergOp_le, h_coeff]
      _ ≤ _ := by grw [h_norm, mul_comm, mul_rotate]
  have h_finite (N : ℕ) : ∫⁻ u, fockMoment N (w u • F u) ∂normalizedVolume _ ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [ENNReal.mul_eq_top, isSchwartzVector_vacVector _, hw _])
      (lintegral_fockMoment_smul_le (h_moment N))
  obtain ⟨h_integrable, h_schwartz⟩ := isSchwartzVector_integral (by fun_prop) h_finite
  have h_coherent (u : InfinitePlace E × (r ⊕ n) × n → ℂ) :
      (realHeisenbergOp u Fock.vacVector : PairFock E s (Sum.elim t s)) =
        realBoxProd (realSigns_comp_split (homSigns_sum_target signs_comp_refl))
          (realHeisenbergOp (φ u).1 Fock.vacVector) (realHeisenbergOp (φ u).2 Fock.vacVector) := by
    rw [realBoxProd, ← heisenbergOp_tmul, tmul_vacElem]
  -- The integral is `thetaLarge` of that datum: compare the integrands at `l`.
  rw [← h_zero _ h_schwartz g]
  refine integral_congr_ae (.of_forall fun l ↦ ?_)
  let S : PairFock E s (Sum.elim t s) →L[ℂ] ℂ := thetaOnRealData W (V.sum W) α (α * β)
    (boxProd (homSigns_sum_target signs_comp_refl) f f₀) (Matrix.fromRows x 0) (g, G.sum (y, l))
  let L : PairFock E s s →L[ℂ] ℂ :=
    θ (W.hom W) ∘L pairWeil W W α α (g, l) ∘L (integrated (W.hom W)).flip f₀
  have h_product (u : InfinitePlace E × (r ⊕ n) × n → ℂ) :
      S (realHeisenbergOp u Fock.vacVector) = L (F u) := by
    rw [h_coherent, map_smul]
    exact thetaOnRealData_boxProd_eq_mul V α β f f₀ x g y _ _ l
  calc S w = ∫ u, w u • S (realHeisenbergOp u Fock.vacVector) ∂normalizedVolume _ :=
        IsVacuum.map_eq_integral w S
    _ = ∫ u, L (w u • F u) ∂normalizedVolume _ := by simp only [h_product, map_smul]
    _ = L (∫ u, w u • F u ∂normalizedVolume _) := L.integral_comp_comm h_integrable

omit [WeilData E] in
/-- The real Weil representation `realPairWeil` of a pair of unitary groups with signs `s`, `t` and
weights `γ`, `γ'` preserves the Fock vectors all of whose moments are finite. -/
lemma isSchwartzVector_realPairWeil {r : Type} [Fintype r] [DecidableEq r] {t : r → ℤˣ}
    (γ γ' : InfinitePlace E → ℤ) (p : GInf E s × GInf E t) {v : PairFock E s t}
    (hv : IsSchwartzVector v) : IsSchwartzVector (realPairWeil γ γ' p v) := by
  intro N
  have h_weil : fockMoment N (realWeil (pairHomInf p) v) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [ENNReal.mul_eq_top, isSchwartzVector_vacVector N, hv N])
      (fockMoment_realWeil_le N (pairHomInf p))
  simp [realPairWeil_apply_apply, fockMoment_smul, ENNReal.mul_eq_top, h_weil]

variable {m : Type} [Fintype m] [DecidableEq m]

-- The index types of the spaces in the proof nest too deeply for the default instance size.
set_option synthInstance.maxSize 512 in
/-- Let `J = stdSpace E m` be positive definite of even rank `2 k`,
`Y = H ⊕ J = hyperbolicSum Unit J` with `H` a hyperbolic plane, and `𝔠` a tame character: a
character `ν = 𝔠.character` of `[U(1)]` of weight `μ`, tamely ramified exactly at a finite set
`S = 𝔠.ramifiedPlaces` of split places. Suppose that the equal rank ratio of `Y`, the normalised
square of the theta integral of `(Y, Y)` at `1`, is zero at every Schwartz vector. Then the theta
integral of the pair `(H ^ (2 k) ⊕ Y, J⁻ ⊕ Y)` vanishes at every Schwartz vector and every standard
datum: `𝔠.semilocalChar⁻¹` of the determinant of an integral `m`-row matrix completed by a variable
one, the rows being ordered by `sumAssoc`. -/
lemma thetaLargeVanishes_of_equalRankThetaRatio_eq_zero {μ : InfinitePlace E → ℤ}
    (hm : 2 ∣ card m) {𝔠 : SplitTameChar E μ}
    (h_zero : ∀ v : PairFock E (Sum.elim (hyperbolicSigns Unit) 1)
      (Sum.elim (hyperbolicSigns Unit) 1),
      IsSchwartzVector v → equalRankThetaRatio (hyperbolicSum Unit (stdSpace E m)) 𝔠 v = 0) :
    ThetaLargeVanishes 𝔠 (hyperbolicSum m (hyperbolicSum Unit (stdSpace E m)))
      ((stdSpace E m).neg.sum (hyperbolicSum Unit (stdSpace E m)))
      (sumAssoc m m ((Unit ⊕ Unit) ⊕ m)).symm := by
  -- The periods over `[U(Y)]` of a Schwartz `v` are values of the equal rank integral, so they are
  -- zero. This is the identity of periods with period `0`, whose factor `C` is then zero.
  let Y : Space E ((Unit ⊕ Unit) ⊕ m) (Sum.elim (hyperbolicSigns Unit) 1) :=
    hyperbolicSum Unit (stdSpace E m)
  have h_even : 2 ∣ card ((Unit ⊕ Unit) ⊕ m) := by simpa using hm.add (dvd_refl 2)
  have h_theta (v : PairFock E (Sum.elim (hyperbolicSigns Unit) 1)
    (Sum.elim (hyperbolicSigns Unit) 1))
      (hv : IsSchwartzVector v) (g : G E (Sum.elim (hyperbolicSigns Unit) 1)) :
      thetaLarge Y Y 𝔠 v (stdColDatum 𝔠.semilocalChar 1) g = 0 := by
    rw [thetaLarge_eq_apply_one_of_even_rank (removePlanes Unit (stdSpace E m)) _ h_even hv]
    simpa [equalRankThetaRatio, (lValueProdInt_pos 𝔠 _).ne'] using h_zero v hv
  intro v hv z hz g
  have h_period : IsPeriodIdentity (hyperbolicSum m Y) (removePlanes m Y) (stdSpace E m).neg 𝔠
      v vacVector 1 0 := by
    refine fun h ↦ ⟨1, fun B β f x g y ↦ ?_⟩
    rw [mul_zero, zero_div, zero_mul]
    exact integral_thetaOnRealData_eq_zero Y h_theta (stdSpace E m).neg
      (isSchwartzVector_realPairWeil _ _ _ (isSchwartzVector_slice _ _ hv)) β f x g y
  obtain ⟨K, -, h_identity⟩ :=
    exists_thetaLarge_eq_smul_of_isPeriodIdentity _ (removePlanes _ Y)
      (removePlanes Unit (stdSpace E m))
      (stdSpace E m).neg (σ' := (sumAssoc m m ((Unit ⊕ Unit) ⊕ m)).symm) h_even (ρ := 1)
      zero_le_one (by simp) hv isSchwartzVector_vacVector
      (.inr (by simp +arith [negCount_sumElim, negCount_one_and_neg_one]))
  obtain ⟨C, hC, h_eq⟩ := h_identity 𝔠 0 h_period
  obtain rfl : C = 0 := by simpa using hC
  rw [h_eq z hz, zero_smul, Pi.zero_apply]

/-- Non-vanishing: let `J = stdSpace E m` be the positive definite space of rank `2 k` and let
`k ≤ μ w` at every infinite place `w`. Let `𝔠` be a tame character: a character of `[U(1)]` of
weight `μ`, tamely ramified exactly at a finite set of split places. There is a Schwartz vector `v`
at which the equal rank ratio of `Y = H ⊕ J = hyperbolicSum Unit J`, the normalised square of the
theta integral of `(Y, Y)` at `1`, is not zero. -/
lemma exists_equalRankThetaRatio_ne_zero (μ : InfinitePlace E → ℤ) {k : ℕ}
    (hm : card m = 2 * k) (hμ : ∀ w : InfinitePlace E, k ≤ μ w) (𝔠 : SplitTameChar E μ) :
    ∃ v : PairFock E (Sum.elim (hyperbolicSigns Unit) 1) (Sum.elim (hyperbolicSigns Unit) 1),
      IsSchwartzVector v ∧ equalRankThetaRatio (hyperbolicSum Unit (stdSpace E m)) 𝔠 v ≠ 0 := by
  -- Otherwise the theta integral of `(H ^ (2 k) ⊕ Y, J⁻ ⊕ Y)`, `Y = H ⊕ J`, vanishes at every
  -- Schwartz vector and standard datum. Vanishing descends to `(J, 0)`, but there the integral of
  -- the vacuum is a volume, not zero.
  by_contra! h_zero
  have h_top : ThetaLargeVanishes 𝔠 (hyperbolicSum m (hyperbolicSum Unit (stdSpace E m)))
      ((stdSpace E m).neg.sum (hyperbolicSum Unit (stdSpace E m)))
      (sumAssoc m m ((Unit ⊕ Unit) ⊕ m)).symm :=
    thetaLargeVanishes_of_equalRankThetaRatio_eq_zero ⟨k, hm⟩ h_zero
  have h_bottom : ThetaLargeVanishes 𝔠 (stdSpace E m) (stdSpace E Empty) (sumEmpty m Empty) := by
    refine h_top.of_add_planes hμ (j := 2 * k + 1) (by simp) _ _ _ ⟨k, hm⟩ ?_ ?_ ?_ ?_
    all_goals simp +arith [hm, negCount_sumElim, negCount_one_and_neg_one]
  have h_vanish : thetaLarge (stdSpace E m) (stdSpace E Empty) 𝔠 vacVector
      (stdRowDatum (sumEmpty m Empty) 𝔠.semilocalChar 1) 1 = 0 :=
    h_bottom vacVector isSchwartzVector_vacVector 1 .one 1
  have h_value : stdRowDatum (sumEmpty m Empty) 𝔠.semilocalChar 1 0 = 1 := stdColDatum_one_one 𝔠
  rw [thetaLarge_stdSpace_empty_vacVector_one, h_value, mul_one, Complex.ofReal_eq_zero] at h_vanish
  have : SecondCountableTopology (G E (1 : Empty → ℤˣ)) := inferInstance
  exact measureReal_univ_ne_zero h_vanish

/-- Let `J` be positive definite. Let the integral of the theta kernel of `(J, J)` over the target
group be the constant `a`, and let `c` times its integral over the source group be the constant `b`.
Then `b = c a`, by Fubini's theorem. -/
lemma eq_mul_of_integral_pairTheta (J : Space E n 1) (γ : AutChar E) (f : 𝒮 (J.hom J)) {a b c : ℂ}
    (h_target : ∀ g : G E (1 : n → ℤˣ),
      ∫ h : G E (1 : n → ℤˣ), pairTheta J J γ γ f (g, h) ∂J.quotMeasure = a)
    (h_source : ∀ g : G E (1 : n → ℤˣ),
      b = c * ∫ h : G E (1 : n → ℤˣ), pairTheta J J γ γ f (h, g) ∂J.quotMeasure) :
    b = c * a := by
  have h_swap : ∫ g, ∫ h, pairTheta J J γ γ f (h, g) ∂J.quotMeasure ∂J.quotMeasure =
      ∫ h, ∫ g, pairTheta J J γ γ f (h, g) ∂J.quotMeasure ∂J.quotMeasure := by
    have h_one : (fun _ ↦ 1) ∈ J.rapidFunctions :=
      (J.isAutomorphic_const 1).mem_rapidFunctions fun _ _ ↦ rfl
    simpa [lift, pairTheta] using
      (pairThetaKer J J γ γ).integral_mul_lift_eq_integral_mul_lift_swap (φ := f) h_one h_one
  have h_mean : ∫ _, b ∂J.quotMeasure = c * ∫ _, a ∂J.quotMeasure := calc
    _ = ∫ g, c * ∫ h, pairTheta J J γ γ f (h, g) ∂J.quotMeasure ∂J.quotMeasure :=
        congrArg _ (funext h_source)
    _ = c * ∫ h, ∫ g, pairTheta J J γ γ f (h, g) ∂J.quotMeasure ∂J.quotMeasure := by
        rw [integral_const_mul, h_swap]
    _ = _ := by simp only [h_target]
  simp only [integral_const, Complex.real_smul] at h_mean
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.2 measureReal_univ_ne_zero)
    (by linear_combination h_mean)

/-- The exchange identity for `(J, J, 0)`. Let `J` be positive definite of rank `2 k` and `v` a
Schwartz vector for `(H ⊕ J, H ⊕ J)`, with `H` a hyperbolic plane. There are `B` and a Schwartz `y`
for `(J, J)` such that, for each tame character `𝔠` of weight `μ`, the theta integral of `y` and the
finite datum `stdColDatum χ 1`, the function `χ⁻¹(det)` for `χ = 𝔠.semilocalChar`, is a constant `c`
times the volume of `[U(0)]`, where `B |c| ^ 2` is `L_*(k)` times the equal rank ratio
`|I(v)(1)| ^ 2 / L_*(k + 1)`. Here `I(v)` is the theta integral at `v` and `χ⁻¹(det)`, and
`L_*(e) = ∏_{w ∈ S} q_w ^ (e ^ 2) ∏_{1 ≤ i ≤ e} |L^S(i, ν)| ^ 2` for `ν = 𝔠.character` and
`S = 𝔠.ramifiedPlaces`. -/
lemma exists_thetaLarge_eq_mul_quotMeasure (μ : InfinitePlace E → ℤ) {k : ℕ} (hm : card m = 2 * k)
    (J : Space E m 1)
    {v : PairFock E (Sum.elim (hyperbolicSigns Unit) (1 : m → ℤˣ))
      (Sum.elim (hyperbolicSigns Unit) (1 : m → ℤˣ))}
    (hv : IsSchwartzVector v) :
    ∃ (B : ℝ) (y : PairFock E (1 : m → ℤˣ) 1), IsSchwartzVector y ∧
      ∀ 𝔠 : SplitTameChar E μ, ∃ c : ℂ,
        B * ‖c‖ ^ 2 = lValueProdInt 𝔠 k * equalRankThetaRatio (hyperbolicSum Unit J) 𝔠 v ∧
        ∀ g : G E (1 : m → ℤˣ), thetaLarge J J 𝔠 y (stdColDatum 𝔠.semilocalChar 1) g =
          c * (stdSpace E Empty).quotMeasure.real Set.univ := by
  let Z : Space E Empty 1 := stdSpace E Empty
  obtain ⟨B, y, hy, h_all⟩ := exchange_of_matches J Z μ J (emptySum Empty m) hv
    isSchwartzVector_vacVector (by simp [negCount_one_and_neg_one]) ⟨k, hm⟩
  refine ⟨B, y, hy, fun 𝔠 ↦ ?_⟩
  obtain ⟨c, hc, h_exchange⟩ := h_all 𝔠
  have h_rank : (card m - card m / 2 : ℤ) = k := by omega
  refine ⟨c, by rw [hc, h_rank], fun g ↦ ?_⟩
  let γ : AutChar E := rankTwist 𝔠.character⁻¹ m
  let f : 𝒮 (J.hom J) := localDatum J J y (stdColDatum 𝔠.semilocalChar 1) 𝔠.readsAt
  have h_identity : thetaIntegral J J γ 1 f g = c * ∫ h, pairTheta Z J γ γ
      (localDatum Z J vacVector (stdColDatum 𝔠.semilocalChar 0) 𝔠.readsAt) (h, g) ∂Z.quotMeasure :=
    h_exchange (stdColDatum 𝔠.semilocalChar 1) (stdColDatum 𝔠.semilocalChar 0) (.of_discrete _)
      (areMatched_stdRowDatum_stdColDatum (emptySum Empty m) (s := 0) nofun) g
  -- The second character enters both sides as its inverse at `det g`.
  refine mul_left_cancel₀ (γ.val g.det).coe_ne_zero ?_
  calc γ.val g.det * thetaIntegral J J γ γ f g = thetaIntegral J J γ 1 f g := by
        rw [thetaIntegral, thetaIntegral, ← integral_const_mul]
        congr with h
        simp [pairTheta, pairWeil_apply, pairChar_apply, field]
    _ = γ.val g.det * (c * Z.quotMeasure.real Set.univ) := by
        rw [h_identity]
        simp [pairTheta_source_zero, stdColDatum, IsIntMatrix, invOnUnits, IsIntegralUnit, Z, γ,
          field]

/-- The exchange identity for `(J, 0, J)`. Let `J` be positive definite of rank `2 k`, and let `v`
for `(H ⊕ J, H ⊕ J)`, with `H` a hyperbolic plane, and `y` for `(J, J)` be Schwartz vectors. There
are `C` and a number `ξ` such that each tame character `𝔠` of weight `μ` has a number `c` as
follows. The volume of `[U(0)]` times `ξ` is `c` times the integral over the first `[U(J)]` of the
theta kernel of `(J, J)` with both characters `γ = ν⁻¹ υ ^ k` and datum `y` at the infinite places,
`χ⁻¹(det)` (`stdColDatum χ 1`) at `S` and the vacuum elsewhere (`localDatum`), and `C |c| ^ 2` is
`L_*(-k) = L_*(k)⁻¹` times the equal rank ratio `|I(v)(1)| ^ 2 / L_*(k + 1)`. Here
`ν = 𝔠.character`, `S = 𝔠.ramifiedPlaces`, `χ = 𝔠.semilocalChar`, `υ` is the splitting character of
the Weil data on norm-one ideles, `I(v)` is the theta integral at `v` and `χ⁻¹(det)`, and
`L_*(e) = ∏_{w ∈ S} q_w ^ (e ^ 2) ∏_{1 ≤ i ≤ e} |L^S(i, ν)| ^ 2`. -/
lemma exists_quotMeasure_mul_eq_mul_integral_pairTheta (μ : InfinitePlace E → ℤ) {k : ℕ}
    (hm : card m = 2 * k) (J : Space E m 1)
    {v : PairFock E (Sum.elim (hyperbolicSigns Unit) (1 : m → ℤˣ))
      (Sum.elim (hyperbolicSigns Unit) (1 : m → ℤˣ))}
    {y : PairFock E (1 : m → ℤˣ) 1} (hv : IsSchwartzVector v) (hy : IsSchwartzVector y) :
    ∃ (C : ℝ) (ξ : ℂ), ∀ 𝔠 : SplitTameChar E μ,
      let γ : AutChar E := rankTwist 𝔠.character⁻¹ m
      ∃ c : ℂ,
        C * ‖c‖ ^ 2 = lValueProdInt 𝔠 (-k) * equalRankThetaRatio (hyperbolicSum Unit J) 𝔠 v ∧
        ∀ g : G E (1 : m → ℤˣ), (stdSpace E Empty).quotMeasure.real Set.univ * ξ =
          c * ∫ h : G E (1 : m → ℤˣ), pairTheta J J γ γ
            (localDatum J J y (stdColDatum 𝔠.semilocalChar 1) 𝔠.readsAt) (h, g) ∂J.quotMeasure := by
  let Z : Space E Empty 1 := stdSpace E Empty
  obtain ⟨C, x, -, h_all⟩ := exchange_of_matches J J μ Z
    (sumEmpty m Empty) hv hy (by simp [negCount_one_and_neg_one]) ⟨k, hm⟩
  -- The vector `x` lies in the Fock space `ℂ` of `(J, 0)`, and `ξ` is its value.
  refine ⟨C, θ (J.hom Z) (integrated (J.hom Z) x (J.hom Z).vacElem), fun 𝔠 ↦ ?_⟩
  obtain ⟨c, hc, h_exchange⟩ := h_all 𝔠
  have h_size :
      C * ‖c‖ ^ 2 = lValueProdInt 𝔠 (-k) * equalRankThetaRatio (hyperbolicSum Unit J) 𝔠 v := by
    simpa [hm] using hc
  refine ⟨c, h_size, fun g ↦ ?_⟩
  let γ : AutChar E := rankTwist 𝔠.character⁻¹ m
  let Φ : Matrix Empty m (LocProd 𝔠.ramifiedPlaces) → ℂ :=
    stdRowDatum (sumEmpty m Empty) 𝔠.semilocalChar 1
  let Ψ : Matrix m m (LocProd 𝔠.ramifiedPlaces) → ℂ := stdColDatum 𝔠.semilocalChar 1
  have h_locally_const : IsLocallyConstant Ψ :=
    (stdColDatum_mem_schwartzBruhat 𝔠.semilocalChar .one).1
  have h_matched : AreMatched SemilocalField.O (sumEmpty m Empty) 𝔠.semilocalChar Φ Ψ :=
    areMatched_stdRowDatum_stdColDatum (sumEmpty m Empty) .one
  have h_identity : thetaIntegral J Z γ 1 (localDatum J Z x Φ 𝔠.readsAt) g =
      c * ∫ h : G E (1 : m → ℤˣ), pairTheta J J γ γ (localDatum J J y Ψ 𝔠.readsAt) (h, g)
        ∂J.quotMeasure :=
    h_exchange Φ Ψ h_locally_const h_matched g
  -- On the zero space the theta kernel only reads `Φ 0`, which is `1`.
  have h_value : Φ 0 = 1 := stdColDatum_one_one 𝔠
  simpa [thetaIntegral, pairTheta_target_zero, Z, h_value] using h_identity

/-- The exchange identity used twice. Let `J` be positive definite of rank `2 k` and `v` a Schwartz
vector for `(H ⊕ J, H ⊕ J)`, with `H` a hyperbolic plane. As `𝔠` runs through the tame characters of
weight `μ`, the square of the equal rank ratio `|I(v)(1)| ^ 2 / L_*(k + 1)` is one number `D`. Here
`I(v)` is the theta integral `thetaLarge` with real part `v` and the function `χ⁻¹(det)` at the
ramified places, `χ = 𝔠.semilocalChar`, and `L_*(e) = ∏_{w ∈ S} q_w ^ (e ^ 2) ∏_{1 ≤ i ≤ e} |L^S(i,
ν)| ^ 2` for `ν = 𝔠.character` and `S = 𝔠.ramifiedPlaces`. -/
lemma exists_equalRankThetaRatio_sq_eq (μ : InfinitePlace E → ℤ) {k : ℕ} (hm : card m = 2 * k)
    (J : Space E m 1)
    {v : PairFock E (Sum.elim (hyperbolicSigns Unit) (1 : m → ℤˣ))
      (Sum.elim (hyperbolicSigns Unit) (1 : m → ℤˣ))}
    (hv : IsSchwartzVector v) :
    ∃ D : ℝ, ∀ 𝔠 : SplitTameChar E μ, equalRankThetaRatio (hyperbolicSum Unit J) 𝔠 v ^ 2 = D := by
  let ratio (𝔠 : SplitTameChar E μ) : ℝ := equalRankThetaRatio (hyperbolicSum Unit J) 𝔠 v
  let vol : ℝ := (stdSpace E Empty).quotMeasure.real Set.univ
  have : SecondCountableTopology (G E (1 : Empty → ℤˣ)) := inferInstance
  have h_vol : (vol : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 measureReal_univ_ne_zero
  obtain ⟨B, y, hy, h_exch₁⟩ := exists_thetaLarge_eq_mul_quotMeasure μ hm J hv
  obtain ⟨C, ξ, h_exch₂⟩ := exists_quotMeasure_mul_eq_mul_integral_pairTheta μ hm J hv hy
  refine ⟨B * C * ‖ξ‖ ^ 2, fun 𝔠 ↦ ?_⟩
  -- Both identities concern the theta kernel of `f`, integrated once over each group.
  let γ : AutChar E := rankTwist 𝔠.character⁻¹ m
  let f : 𝒮 (J.hom J) := localDatum J J y (stdColDatum 𝔠.semilocalChar 1) 𝔠.readsAt
  obtain ⟨c₁, hc₁, h_target⟩ : ∃ c₁ : ℂ, B * ‖c₁‖ ^ 2 = lValueProdInt 𝔠 k * ratio 𝔠 ∧
      ∀ g : G E 1, thetaLarge J J 𝔠 y (stdColDatum 𝔠.semilocalChar 1) g = c₁ * vol := h_exch₁ 𝔠
  obtain ⟨c₂, hc₂, h_source⟩ : ∃ c₂ : ℂ, C * ‖c₂‖ ^ 2 = lValueProdInt 𝔠 (-k) * ratio 𝔠 ∧
      ∀ g : G E 1, vol * ξ = c₂ * ∫ h, pairTheta J J γ γ f (h, g) ∂J.quotMeasure := h_exch₂ 𝔠
  have h_mean : vol * ξ = c₂ * (c₁ * vol) := eq_mul_of_integral_pairTheta J γ f h_target h_source
  have h_prod : ξ = c₂ * c₁ := mul_left_cancel₀ h_vol (by linear_combination h_mean)
  have h_inverse : lValueProdInt 𝔠 k * lValueProdInt 𝔠 (-k) = 1 := by
    simp [lValueProdInt_natCast, lValueProdInt_neg_natCast, (lValueProd_pos 𝔠 k).ne']
  calc ratio 𝔠 ^ 2 = (lValueProdInt 𝔠 k * ratio 𝔠) * (lValueProdInt 𝔠 (-k) * ratio 𝔠) := by
        rw [mul_mul_mul_comm, h_inverse, one_mul, sq]
    _ = B * C * ‖ξ‖ ^ 2 := by
        simp only [ratio, ← hc₁, ← hc₂, h_prod, norm_mul]
        ring

/-- The value on the first floor. Let `J` be the standard positive definite space of rank `2 k` and
`k ≤ μ` at every infinite place. Some Schwartz vector `v` for `(H ⊕ J, H ⊕ J)` has an equal rank
ratio that is one number `C ≠ 0` for all tame characters of weight `μ`. -/
lemma exists_equalRankThetaRatio_const_ne_zero (μ : InfinitePlace E → ℤ) {k : ℕ}
    (hm : card m = 2 * k) (hμ : ∀ w : InfinitePlace E, k ≤ μ w) :
    ∃ v : PairFock E (Sum.elim (hyperbolicSigns Unit) (1 : m → ℤˣ))
      (Sum.elim (hyperbolicSigns Unit) 1),
      IsSchwartzVector v ∧ ∃ C ≠ (0 : ℝ),
        ∀ 𝔠 : SplitTameChar E μ, equalRankThetaRatio (hyperbolicSum Unit (stdSpace E m)) 𝔠 v =
          C := by
  obtain h_empty | ⟨⟨𝔠₀⟩⟩ := isEmpty_or_nonempty (SplitTameChar E μ)
  · exact ⟨vacVector, isSchwartzVector_vacVector, 1, one_ne_zero, h_empty.elim⟩
  obtain ⟨v, hv, h_ne⟩ := exists_equalRankThetaRatio_ne_zero μ hm hμ 𝔠₀
  -- The ratio of `v` is nonnegative and has constant square, so it is a nonzero constant.
  obtain ⟨D, h_sq⟩ := exists_equalRankThetaRatio_sq_eq μ hm _ hv
  have h_nonneg (𝔠 : SplitTameChar E μ) :
      0 ≤ equalRankThetaRatio (hyperbolicSum Unit (stdSpace E m)) 𝔠 v :=
    div_nonneg (sq_nonneg _) (lValueProdInt_pos 𝔠 _).le
  refine ⟨v, hv, _, h_ne, fun 𝔠 ↦ (sq_eq_sq₀ (h_nonneg 𝔠) (h_nonneg 𝔠₀)).1 ?_⟩
  rw [h_sq, h_sq]

/-- Adding a plane. Let `W` have even rank and let `A` be an adapted splitting `W' = W ⊕ H` with `H`
a hyperbolic plane (its frames are orthonormal at the infinite and integral at the finite places).
Each Schwartz vector `v` for `(W, W)` has a Schwartz vector `v'` for `(W', W')` whose equal rank
ratio is `C` times the ratio `|I(v)(1)| ^ 2 / L_*(rk W / 2)` of `v`. The constant `C > 0` is the
same for all tame characters `𝔠` of weight `μ`. Here `I(v)` is the theta integral `thetaLarge` with
real part `v` and the function `χ⁻¹(det)` at the ramified places, `χ = 𝔠.semilocalChar`, and
`L_*(e) = ∏_{w ∈ S} q_w ^ (e ^ 2) ∏_{1 ≤ i ≤ e} |L^S(i, ν)| ^ 2` for `ν = 𝔠.character` and
`S = 𝔠.ramifiedPlaces`. -/
lemma exists_equalRankThetaRatio_add_plane {W : Space E n s} (μ : InfinitePlace E → ℤ)
    {n' : Type} [Fintype n'] [DecidableEq n'] {s' : n' → ℤˣ}
    {W' : Space E n' s'} (A : W'.Splitting W Unit) [IsBaseAdapted A] (h_even : 2 ∣ card n)
    {v : PairFock E s s} (hv : IsSchwartzVector v) :
    ∃ v' : PairFock E s' s', IsSchwartzVector v' ∧ ∃ C > (0 : ℝ), ∀ 𝔠 : SplitTameChar E μ,
      equalRankThetaRatio W' 𝔠 v' = C * equalRankThetaRatio W 𝔠 v := by
  -- Choose `v'` whose cone integral has the theta integrals of `v`. On `W'` the theta integral is
  -- constant, so it equals its constant term.
  obtain ⟨d, hd⟩ : ∃ d : ℕ, card n = 2 * d := exists_eq_mul_right_of_dvd h_even
  have hd' : card n' = 2 * (d + 1) := by simp [A.card_eq, hd, mul_add, add_comm]
  obtain ⟨C, hC, h_plane⟩ := exists_planeConstantTerm_eq_thetaLarge_cone A A (emptySum Empty n')
    (emptySum Empty n) h_even μ (z := d) (by omega)
  obtain ⟨v', hv', h_cone⟩ :=
    exists_thetaLarge_cone_eq A A μ (emptySum Empty n) h_even (z := d + 1) (by positivity) hv
  refine ⟨v', hv', C ^ 2, by positivity, fun 𝔠 ↦ ?_⟩
  obtain ⟨κ, hκ, h_all⟩ := h_plane 𝔠
  have h_term : planeConstantTerm 𝔠 W' A (emptySum Empty n') v' 0 1 1 =
      κ * thetaLarge W W 𝔠 (cone A A μ (d + 1) v')
        (stdRowDatum (emptySum Empty n) 𝔠.semilocalChar 0) 1 :=
    h_all v' hv' 0 nofun 1 1 (.inl rfl)
  have h_const (g : G E s') : thetaLarge W' W' 𝔠 v' (stdColDatum 𝔠.semilocalChar 1) g =
      thetaLarge W' W' 𝔠 v' (stdColDatum 𝔠.semilocalChar 1) 1 :=
    thetaLarge_eq_apply_one_of_even_rank A 𝔠 ⟨d + 1, hd'⟩ hv' g
  -- With no extra rows, `stdRowDatum (emptySum Empty n) 𝔠.semilocalChar 0` unfolds to
  -- `stdColDatum 𝔠.semilocalChar 1`.
  have h_value : thetaLarge W' W' 𝔠 v' (stdColDatum 𝔠.semilocalChar 1) 1 =
      κ * thetaLarge W W 𝔠 v (stdColDatum 𝔠.semilocalChar 1) 1 := calc
    _ = ∫ q, thetaLarge W' W' 𝔠 v' (stdColDatum 𝔠.semilocalChar 1)
          (lineRadical A q * A.levi (Matrix.GeneralLinearGroup.scalar Unit 1, 1))
          ∂radicalMeasure := by
        simp_rw [h_const (_ * _)]
        simp
    _ = κ * thetaLarge W W 𝔠 (cone A A μ (d + 1) v')
          (stdRowDatum (emptySum Empty n) 𝔠.semilocalChar 0) 1 := h_term
    _ = κ * thetaLarge W W 𝔠 v (stdRowDatum (emptySum Empty n) 𝔠.semilocalChar 0) 1 := by
        rw [h_cone]
  have h_sharp : lSharp 𝔠 (d + 1) ≠ 0 := (lSharp_pos 𝔠 (by simp)).ne'
  rw [equalRankThetaRatio, equalRankThetaRatio, h_value, norm_mul, hκ,
    show (card n / 2 : ℤ) = d by omega, show (card n' / 2 : ℤ) = d + 1 by omega, lValueProdInt_succ]
  field_simp

/-- Let `Y` have even rank and let `A` be an adapted splitting `Y = W ⊕ H` with `H` a hyperbolic
plane (its frames are orthonormal at the infinite and integral at the finite places). Let `Y₁` be
any space with the signs of `Y`, `𝔠` a tame character and `v` a Schwartz vector (all Fock moments
finite). Then the equal rank ratio `|I(1)| ^ 2 / L_*(rank / 2)` is the same for `Y₁` and `Y`, where
`I` is the theta integral of `v` and `𝔠.semilocalChar⁻¹(det)` for the pair `(Y₁, Y₁)`, resp.
`(Y, Y)`, and `L_* = lValueProdInt 𝔠` is a product of partial L-values of `𝔠`. -/
lemma equalRankThetaRatio_eq_of_signs_eq {W : Space E n s} {μ : InfinitePlace E → ℤ}
    {n' : Type} [Fintype n'] [DecidableEq n'] {s' : n' → ℤˣ}
    {Y : Space E n' s'} (A : Y.Splitting W Unit) [IsBaseAdapted A] (Y₁ : Space E n' s')
    (h_even : 2 ∣ card n') (𝔠 : SplitTameChar E μ) {v : PairFock E s' s'}
    (hv : IsSchwartzVector v) :
    equalRankThetaRatio Y₁ 𝔠 v = equalRankThetaRatio Y 𝔠 v := by
  -- Changing the space moves the point and multiplies by a number of modulus one; the theta
  -- integral of `Y` is constant.
  obtain ⟨γ, hγ⟩ := exists_thetaLarge_thetaSmall_eq_circle_mul Y Y₁ Y Y₁ Y Y
  obtain ⟨⟨u, h_move⟩, -⟩ := hγ 𝔠
  simp [equalRankThetaRatio, h_move, thetaLarge_eq_apply_one_of_even_rank A 𝔠 h_even hv,
    Circle.norm_coe]

/-- The value of the equal rank ratio. Let `rk W = 2 k + 2 q`, where `q` is the number of negative
signs of `W`, and `k ≤ μ` at every infinite place. There are a Schwartz vector (all Fock moments
finite) `v` for `(H ⊕ W, H ⊕ W)`, with `H` a hyperbolic plane, and `C ≠ 0` such that
`|I(v)(1)| ^ 2 / L_*(rk W / 2 + 1) = C` for every tame character `𝔠` of weight `μ`. Here `I(v)` is
the theta integral `thetaLarge` with real part `v` and the function `χ⁻¹(det)` at the ramified
places, `χ = 𝔠.semilocalChar`, and `L_*(e) = ∏_{w ∈ S} q_w ^ (e ^ 2) ∏_{1 ≤ i ≤ e} |L^S(i, ν)| ^ 2`
for `ν = 𝔠.character` and `S = 𝔠.ramifiedPlaces`. -/
lemma exists_equalRankThetaRatio_eq_const (W : Space E n s) (μ : InfinitePlace E → ℤ) (k : ℕ)
    (h_rank : card n = 2 * k + 2 * negCount s) (hμ : ∀ w : InfinitePlace E, k ≤ μ w) :
    ∃ v : PairFock E (Sum.elim (hyperbolicSigns Unit) s) (Sum.elim (hyperbolicSigns Unit) s),
      IsSchwartzVector v ∧ ∃ C ≠ (0 : ℝ),
        ∀ 𝔠 : SplitTameChar E μ, equalRankThetaRatio (hyperbolicSum Unit W) 𝔠 v = C := by
  -- The space `H ⊕ W` has the signs of `E ^ (2 k) ⊕ H ^ (q + 1)`: climb from the first floor.
  have h_even : 2 ∣ card ((Unit ⊕ Unit) ⊕ n) := ⟨1 + k + negCount s, by simp +arith [h_rank]⟩
  induction hq : negCount s generalizing n with
  | zero =>
    obtain rfl : s = 1 := funext fun i ↦ (Int.units_eq_one_or (s i)).resolve_right fun h ↦
      (card_eq_zero_iff.1 hq).false ⟨i, h⟩
    obtain ⟨v, hv, C, hC, h_first⟩ :=
      exists_equalRankThetaRatio_const_ne_zero μ (m := n) (by rw [h_rank, hq]; rfl) hμ
    refine ⟨v, hv, C, hC, fun 𝔠 ↦ ?_⟩
    rw [equalRankThetaRatio_eq_of_signs_eq (removePlanes Unit (stdSpace E n)) _ h_even 𝔠 hv,
      h_first]
  | succ q ih =>
    let W₀ := hyperbolicSum (Fin q) (stdSpace E (Fin (2 * k)))
    have h_neg : negCount (Sum.elim (hyperbolicSigns (Fin q)) (1 : Fin (2 * k) → ℤˣ)) = q := by
      simp [negCount_sumElim, negCount_one_and_neg_one]
    have h_even₀ : 2 ∣ card ((Unit ⊕ Unit) ⊕ (Fin q ⊕ Fin q) ⊕ Fin (2 * k)) :=
      ⟨1 + k + q, by simp +arith⟩
    obtain ⟨v, hv, C, hC, h_below⟩ := ih W₀ (by simp +arith [h_neg]) h_even₀ h_neg
    -- Add a plane to `H ⊕ W₀` so that the new space `Y` has the signs of `H ⊕ W`.
    obtain ⟨Y, A, _⟩ : ∃ (Y : Space E ((Unit ⊕ Unit) ⊕ n) (Sum.elim (hyperbolicSigns Unit) s))
        (A : Y.Splitting (hyperbolicSum Unit W₀) Unit), IsBaseAdapted A :=
      exists_isBaseAdapted Unit _ _ (by simp +arith [h_rank, hq])
        (by simp +arith [hq, negCount_sumElim, negCount_one_and_neg_one])
    obtain ⟨v', hv', C', hC', h_up⟩ := exists_equalRankThetaRatio_add_plane μ A h_even₀ hv
    refine ⟨v', hv', C' * C, mul_ne_zero hC'.ne' hC, fun 𝔠 ↦ ?_⟩
    rw [equalRankThetaRatio_eq_of_signs_eq A _ h_even 𝔠 hv', h_up, h_below]

end EqualRankValue

/-!
## The exchange theorem for data modulo an ideal

`New.Exchange.exchange_theorem` exchanges a theta integral over `[U(V)]` for one over `[U(V')]`, for
finite data given by functions on matrices over `O_E / 𝔪`. It is deduced from
`New.Exchange.exchange_of_matches`, the same exchange for data on the completions at the primes of
`𝔪`, and the value `New.Exchange.exists_equalRankThetaRatio_eq_const`.
-/

section ExchangeTheorem

open RingHom Fintype Rows Modulus IsLinearMap

/-- The space character `α.spaceChar p` is the Hecke character `x ↦ α (x / x̄) υ x ^ (-p)`. In even
rank `card N = p + q` those of `α` in rank `p` and of `α'` in rank `q` multiply to the inverse of
the base change `x ↦ ν (x / x̄)` exactly if `α * α' = rankTwist ν⁻¹ N = ν⁻¹ υ ^ (card N / 2)`. -/
lemma spaceChar_mul_spaceChar_eq_iff {E : Type} [Field E] [CMType E] [WeilData E]
    {N : Type} [Fintype N] {α α' ν : AutChar E} {p q : ℕ}
    (h_card : card N = p + q) (h_even : 2 ∣ card N) :
    α.spaceChar p * α'.spaceChar q = ν.baseChange⁻¹ ↔ α * α' = rankTwist ν⁻¹ N := by
  classical
  have h_mul : α.spaceChar p * α'.spaceChar q = (α * α').spaceChar (card N) := by
    rw [h_card, AutChar.spaceChar_mul]
  rw [h_mul, ← map_inv, ← spaceChar_rankTwist h_even]
  simp only [AutChar.spaceChar, mul_left_inj, AutChar.baseChange_injective.eq_iff]

variable {E : Type} [Field E] [CMType E] [WeilData E] {n a b : Type} [Fintype n] [DecidableEq n]
  [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] {s : n → ℤˣ} {t : a → ℤˣ} {t' : b → ℤˣ}
  (W : Space E n s) (V : Space E a t) (V' : Space E b t')

/-- Let `W`, `V`, `V'` be spaces with coordinates indexed by `n`, `a`, `b`, split by
`σ : b ⊕ a ≃ n`, and let the tame character `𝔠` be ramified exactly at the primes of the modulus
`𝔪`. Let `Φ`, `Ψ` be matched functions over `O_E / 𝔪` for the product `χ` of the residue characters
of `𝔠`: `Φ` is supported on the last rows of `k⁻¹` and `Ψ` on the first columns of `k` (split by
`σ`), for `k` in `GL_n(O_E / 𝔪)` (the subring `⊤`), and there `Φ = χ (det k) * Ψ`. Then there are
functions `Φ'`, `Ψ'` on matrices over the completions at these primes, matched over the local
integers `SemilocalField.O` for `𝔠.semilocalChar`, with `Ψ'` locally constant, that give the same
adelic data as `Φ` for `(W, V)` and `Ψ` for `(V', W)`, whatever the real vector. -/
lemma exists_areMatched_modDatum_eq (σ : b ⊕ a ≃ n) {μ : NumberField.InfinitePlace E → ℤ}
    (𝔪 : Modulus E) (𝔠 : SplitTameChar E μ)
    (h_ramified : (𝔠.ramifiedPlaces : Set (FinPlace E)) = 𝔪.places)
    {Φ : Matrix a n 𝔪.ResidueRing → ℂ} {Ψ : Matrix n b 𝔪.ResidueRing → ℂ}
    (h_matched : AreMatched ⊤ σ (𝔪.charOfTamePart 𝔠.tamePart) Φ Ψ) :
    ∃ (Φ' : Matrix a n (LocProd 𝔠.ramifiedPlaces) → ℂ)
      (Ψ' : Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ),
      IsLocallyConstant Ψ' ∧
      AreMatched SemilocalField.O σ 𝔠.semilocalChar Φ' Ψ' ∧
      (∀ x : PairFock E s t, modDatum W V 𝔪 Φ x = localDatum W V x Φ' 𝔠.readsAt) ∧
      ∀ v : PairFock E t' s, modDatum V' W 𝔪 Ψ v = localDatum V' W v Ψ' 𝔠.readsAt := by
  -- `Φ'` and `Ψ'` are the lifts along the reduction `π` from the local integers to `𝔪.ResidueRing`.
  have h_reads : ReadsAt 𝔪.places (evalPlaces 𝔠.ramifiedPlaces) := by
    simpa only [h_ramified] using 𝔠.readsAt
  -- `ρ` is a continuous section of the projection `evalPlaces 𝔠.ramifiedPlaces` to the components
  -- at `𝔪`
  obtain ⟨ρ, hρ_cont, ev_ρ, ρ_ev⟩ := h_reads.exists_section.2
  let ev : Ô E →+* SemilocalField.O := (evalPlaces 𝔠.ramifiedPlaces).restrict _ _ evalPlaces_mem_O
  let sec (y : SemilocalField.O (F := LocProd 𝔠.ramifiedPlaces)) : Ô E :=
    ⟨ρ y, by simpa [← ρ_ev, ev_ρ] using (h_reads.mem_iff (ρ y)).1 (by simp [ev_ρ])⟩
  have h_sec : Function.RightInverse sec ev := fun y ↦ Subtype.ext (ev_ρ y)
  -- reduction modulo `𝔪` only sees these components, so it factors as `π ∘ ev`
  have h_ker : ker ev ≤ ker 𝔪.reduction := fun y hy ↦ by
    rw [mem_ker, ← map_zero 𝔪.reduction]
    exact 𝔪.reduction_congr fun w hw ↦
      congrFun (congrArg Subtype.val hy) ⟨w, h_ramified.ge hw⟩
  let π : SemilocalField.O →+* 𝔪.ResidueRing := ev.liftOfRightInverse sec h_sec ⟨𝔪.reduction, h_ker⟩
  -- `π` is compatible with the residue maps, so it detects units; it is onto since
  -- `𝔪.reduction` is onto
  have π_res (i : 𝔠.ramifiedPlaces) (u : SemilocalField.O) :
      modulusResidue 𝔪 (h_ramified.le i.2) (π u) = residueAt i u :=
    (modulusResidue_reduction 𝔪 (h_ramified.le i.2) (sec u)).trans
      (congrArg (IsLocalRing.residue (LocInt i.val)) (Subtype.ext (congrFun (ev_ρ u) i)))
  have π_local : IsLocalHom π := by
    refine ⟨fun u hu ↦ isUnit_iff_residueAt_ne_zero.2 fun i ↦ ?_⟩
    rw [← π_res]
    exact (hu.map _).ne_zero
  have π_surj : Function.Surjective π :=
    𝔪.reduction_surjective.forall.2 fun y ↦ ⟨ev y, liftOfRightInverse_comp_apply ..⟩
  -- on units both characters are the product of the residue characters `𝔠.tamePart`
  have π_char (u : SemilocalField.O) (hu : IsUnit u) :
      𝔠.semilocalChar u.val = 𝔪.charOfTamePart 𝔠.tamePart (π u) := calc
    _ = ∏ i : 𝔠.ramifiedPlaces, 𝔠.tamePart i (residueAt i u) :=
        𝔠.localChar_apply_of_isUnit _ u hu
    _ = ∏ᶠ i : 𝔠.ramifiedPlaces, 𝔠.tamePart i (modulusResidue 𝔪 (h_ramified.le i.2) (π u)) := by
        simp only [π_res, finprod_eq_prod_of_fintype]
    _ = ∏ᶠ w : 𝔪.places, 𝔠.tamePart w (modulusResidue 𝔪 w.2 (π u)) :=
        finprod_comp_equiv (f := fun w : 𝔪.places ↦ 𝔠.tamePart w (modulusResidue 𝔪 w.2 (π u)))
          (.subtypeEquivRight (Set.ext_iff.1 h_ramified))
  -- lifting from `𝔪.ResidueRing` to adeles is lifting along `π`, then reading the components
  have π_ev (z : 𝔸f E) (hz : evalPlaces 𝔠.ramifiedPlaces z ∈ SemilocalField.O) :
      π ⟨evalPlaces 𝔠.ramifiedPlaces z, hz⟩ = 𝔪.reduction
        ⟨idem 𝔪.places * z, (h_reads.mem_iff z).1 hz⟩ :=
    congrArg 𝔪.reduction (Subtype.ext (ρ_ev z))
  have h_lift {n n' : Type} [Fintype n] [Fintype n'] (Φ : Matrix n' n 𝔪.ResidueRing → ℂ) :
      𝔪.liftFn (Φ ∘ vecToMatrix) = fun y ↦
        liftIntegralFn π Φ (vecToMatrix (evalPlaces 𝔠.ramifiedPlaces ∘ y)) := by
    ext y
    rw [liftFn_apply, liftIntegralFn, mk'_apply]
    have h_int : (∀ i : n' × n, idem 𝔪.places * y i ∈ Ô E) ↔
        ∀ (i : n') (j : n), vecToMatrix (evalPlaces 𝔠.ramifiedPlaces ∘ y) i j ∈
          SemilocalField.O := by
      simp [vecToMatrix, h_reads.mem_iff]
    by_cases h : ∀ i : n' × n, idem 𝔪.places * y i ∈ Ô E
    · rw [dite_eq_left h, dite_eq_left (h_int.1 h)]
      exact congrArg Φ (Matrix.ext fun i j ↦ (π_ev (y (i, j)) (h_int.1 h i j)).symm)
    · rw [dite_eq_right h, dite_eq_right (mt h_int.2 h)]
  have h_locally_const : IsLocallyConstant (liftIntegralFn π Ψ) := by
    have h_schwartz : IsSchwartzBruhat 𝔪.places (𝔪.liftFn (Ψ ∘ vecToMatrix)) :=
      isSchwartzBruhat_liftFn 𝔪 (Ψ ∘ vecToMatrix)
    rw [h_lift] at h_schwartz
    simpa [Function.comp_def, ev_ρ] using
      h_schwartz.locally_constant.comp_continuous (f := fun y ↦ ρ ∘ matrixToVec y)
        (by fun_prop [matrixToVec])
  refine ⟨liftIntegralFn π Φ, liftIntegralFn π Ψ, h_locally_const,
    h_matched.lift_of_reduction π π_local π_surj π_char, fun x ↦ ?_, fun v ↦ ?_⟩
  all_goals
    rw [modDatum, h_lift, ← h_ramified, localDatum]
    rfl

/-- Let `W`, `V`, `V'` have ranks `|n| = |b| + |a|` (split by `σ`), `|a| = |b| + 2e` and `|b|`. Let
`W` have as many negative signs `q` as `V` and `V'` together, with `2q + 2 ≤ |n|`. Let the weights
satisfy `|n| ≤ 2 μ + 2q`, and let `v` be a real Schwartz vector for `(V', W)`. There are `C` and a
Schwartz `x` for `(W, V)` such that every character `ν` of `[U(1)]` of weight `μ` that is tame for
`(𝔪, χ)` (ramified exactly at the primes of `𝔪`, with residue character `χ`) has some `c ≠ 0` with
(a) and (b). (a) `‖c‖²` is `C` times `lValueProd 𝔪.places ν e`, a power of the norm of the primes of
`𝔪` times the product of the squares of the partial L-values `|L^S(z, ν)|` for `z = 1, …, e`, with
`S` the primes of `𝔪`; so `C > 0` as soon as such a `ν` exists. (b) For all matched functions `Φ`,
`Ψ` modulo `𝔪`, the theta integral of `(x, Φ)` over `[U(V)]` is `c` times that of `(v, Ψ)` over
`[U(V')]`, as functions on `U(W)`. The left side has the characters `γ` and `1`, the right side `γ`
and `γ`, with `γ = rankTwist ν⁻¹ n = ν⁻¹ υ ^ (|n| / 2)`. -/
lemma exchange_theorem (σ : b ⊕ a ≃ n) (h_signs : negCount s = negCount t + negCount t') {e : ℕ}
    (h_rank : card a = card b + 2 * e) (h_few_neg : 2 * negCount s + 2 ≤ card n)
    {μ : NumberField.InfinitePlace E → ℤ}
    (hμ : ∀ τ : NumberField.InfinitePlace E, card n ≤ 2 * μ τ + 2 * negCount s)
    {v : Fock.fockSpace (realSigns E (homSigns t' s))} (hv : IsSchwartzVector v) :
    ∃ (C : ℝ) (x : Fock.fockSpace (realSigns E (homSigns s t))),
      IsSchwartzVector x ∧
      ∀ (𝔪 : Modulus E) (ν : AutChar E) (χ : MulChar 𝔪.ResidueRing ℂ), IsTameFor 𝔪 ν μ χ →
        let γ : AutChar E := rankTwist ν⁻¹ n
        ∃ c ≠ (0 : ℂ),
          -- (a) the size of the constant
          ‖c‖ ^ 2 = C * lValueProd 𝔪.places ν e ∧
          -- (b) the exchange of the two theta integrals on matched functions modulo `𝔪`
          ∀ (Φ : Matrix a n 𝔪.ResidueRing → ℂ) (Ψ : Matrix n b 𝔪.ResidueRing → ℂ),
            AreMatched ⊤ σ χ Φ Ψ →
            ∀ g : G E s,
            thetaIntegral W V γ 1 (modDatum W V 𝔪 Φ x) g =
              c *
                ∫ h : G E t', pairTheta V' W γ γ (modDatum V' W 𝔪 Ψ v) (h, g) ∂V'.quotMeasure := by
  -- Lift matched functions modulo `𝔪` to the completions at its primes and apply
  -- `exchange_of_matches`, at a `z` whose equal rank ratio is a nonzero constant.
  have h_card : card n = 2 * card b + 2 * e := by
    rw [← card_congr σ, card_sum, h_rank]
    ring
  have h_weight (w : NumberField.InfinitePlace E) : (card n / 2 - negCount s : ℕ) ≤ μ w := by
    have h_bound : (card n : ℤ) ≤ 2 * μ w + 2 * negCount s := hμ w
    omega
  obtain ⟨z, hz, C₀, hC₀, h_value⟩ :
      ∃ z : PairFock E (Sum.elim (hyperbolicSigns Unit) s) (Sum.elim (hyperbolicSigns Unit) s),
        IsSchwartzVector z ∧ ∃ C₀ ≠ (0 : ℝ),
          ∀ 𝔠 : SplitTameChar E μ, equalRankThetaRatio (hyperbolicSum Unit W) 𝔠 z = C₀ :=
    exists_equalRankThetaRatio_eq_const W μ (card n / 2 - negCount s) (by omega) h_weight
  obtain ⟨C, x, hx, h_core⟩ := exchange_of_matches W V' μ V σ hz hv h_signs (by omega)
  refine ⟨C₀ / C, x, hx, fun 𝔪 ν χ ⟨h_ne, ψ, hν, h_ram, hχ⟩ ↦ ?_⟩
  -- the tame character ramified at the primes of `𝔪`
  have h_places : 𝔪.places.toFinite.toFinset = 𝔪.places := 𝔪.places.toFinite.coe_toFinset
  let 𝔠 : SplitTameChar E μ :=
    { character := ν, tamePart := ψ, hasWeight := hν, ramifiedPlaces := 𝔪.places.toFinite.toFinset
      nonempty := 𝔪.places.toFinite.toFinset_nonempty.2 (Set.nonempty_coe_sort.1 h_ne)
      star_notMem := fun w hw hw' ↦ 𝔪.not_le_star w (h_places.le hw) (h_places.le hw')
      ne_one_iff := by simpa using h_ram
      weight_pos := fun w ↦ by linarith [hμ w] }
  obtain ⟨c, hc, h_exch⟩ := h_core 𝔠
  -- the size of `c`: the right side below is not zero, so neither `C` nor `c` is
  have hL : lValueProdInt 𝔠 e = lValueProd 𝔪.places ν e := by
    rw [lValueProdInt_natCast]
    exact congrArg (fun S : Set (FinPlace E) ↦ lValueProd S ν e) h_places
  replace hc : C * ‖c‖ ^ 2 = lValueProd 𝔪.places ν e * C₀ := by
    rw [hc, show (card a - card n / 2 : ℤ) = e by omega, hL, h_value]
  have hL_ne : lValueProd 𝔪.places ν e ≠ 0 := hL.symm.trans_ne (lValueProdInt_pos 𝔠 e).ne'
  obtain ⟨hC, hc_ne⟩ : C ≠ 0 ∧ c ≠ 0 := by simpa using hc.trans_ne (mul_ne_zero hL_ne hC₀)
  have h_size : ‖c‖ ^ 2 = C₀ / C * lValueProd 𝔪.places ν e := by
    field_simp
    linear_combination hc
  refine ⟨c, hc_ne, h_size, fun Φ Ψ h_matched ↦ ?_⟩
  -- matched functions modulo `𝔪` give the same data as matched functions on the completions
  obtain ⟨Φ', Ψ', h_locally_const, h_matched', hΦ, hΨ⟩ :
      ∃ (Φ' : Matrix a n (LocProd 𝔠.ramifiedPlaces) → ℂ)
        (Ψ' : Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ),
        IsLocallyConstant Ψ' ∧ AreMatched SemilocalField.O σ 𝔠.semilocalChar Φ' Ψ' ∧
        (∀ x, modDatum W V 𝔪 Φ x = localDatum W V x Φ' 𝔠.readsAt) ∧
        ∀ v, modDatum V' W 𝔪 Ψ v = localDatum V' W v Ψ' 𝔠.readsAt :=
    exists_areMatched_modDatum_eq W V V' σ 𝔪 𝔠 h_places (by rwa [hχ] at h_matched)
  rw [hΦ, hΨ]
  exact h_exch Φ' Ψ' h_locally_const h_matched'

/-- Let `W`, `V`, `V'` have ranks `|n| = |b| + |a|` (split by `σ`), `|a| = |b| + 2e`, `|b|`. Let `W`
have as many negative signs `q` as `V` and `V'` together, with `2q + 2 ≤ |n| ≤ 2 μ + 2q`, and let
`v` be a real Schwartz vector for `(V', W)`. There are `C > 0` and a Schwartz vector `x` for
`(W, V)`, chosen before `𝔪` and `ν`, such that every character `ν` of `[U(1)]` of weight `μ` that is
tame for `(𝔪, χ)` has a number `c` as follows. Its size is `‖c‖² = C * lValueProd 𝔪.places ν e ≠ 0`.
For all `α`, `α'` such that the characters `α.spaceChar |a|` of `V` and `α'.spaceChar |b|` of `V'`
have product inverse to the base change `x ↦ ν (x / x̄)`, and all matched functions `Φ`, `Ψ` modulo
`𝔪`, the theta integral of `(x, Φ)` over `[U(V)]` is `c` times that of `(v, Ψ)` over `[U(V')]`, as
functions on `U(W)`. The character of `W` is `rankTwist ν⁻¹ n = ν⁻¹ υ ^ (|n| / 2)`, and `modDatum`
puts a function modulo `𝔪` at the primes of `𝔪` and the vacuum at the other finite places. -/
theorem exchange_identity (σ : b ⊕ a ≃ n) (h_signs : negCount s = negCount t + negCount t')
    {e : ℕ} (h_rank : card a = card b + 2 * e) (h_few_neg : 2 * negCount s + 2 ≤ card n)
    {μ : NumberField.InfinitePlace E → ℤ}
    (hμ : ∀ τ : NumberField.InfinitePlace E, card n ≤ 2 * μ τ + 2 * negCount s)
    {v : PairFock E t' s} (hv : IsSchwartzVector v) :
    ∃ C : ℝ, 0 < C ∧ ∃ x : PairFock E s t, IsSchwartzVector x ∧
      ∀ (𝔪 : Modulus E) (ν : AutChar E) (χ : MulChar 𝔪.ResidueRing ℂ), IsTameFor 𝔪 ν μ χ →
      ∃ c : ℂ,
        ‖c‖ ^ 2 = C * lValueProd 𝔪.places ν e ∧
        C * lValueProd 𝔪.places ν e ≠ 0 ∧
        ∀ α α' : AutChar E,
          α.spaceChar (card a) * α'.spaceChar (card b) = ν.baseChange⁻¹ →
          ∀ (Φ : Matrix a n 𝔪.ResidueRing → ℂ) (Ψ : Matrix n b 𝔪.ResidueRing → ℂ),
            AreMatched ⊤ σ χ Φ Ψ →
            ∀ g : G E s,
              thetaIntegral W V (rankTwist ν⁻¹ n) α (modDatum W V 𝔪 Φ x) g =
                c * ∫ h : G E t',
                  pairTheta V' W α' (rankTwist ν⁻¹ n) (modDatum V' W 𝔪 Ψ v) (h, g)
                  ∂V'.quotMeasure := by
  -- `exchange_theorem` is the case `α = 1`, `α' = rankTwist ν⁻¹ n`; other splitting characters
  -- multiply both sides by the same factor `α (det g)⁻¹`.
  obtain ⟨C, x, hx, h_exch⟩ := exchange_theorem W V V' σ h_signs h_rank h_few_neg hμ hv
  obtain hC | hC := le_or_gt C 0
  · -- If `C ≤ 0` there is no pair `(𝔪, ν)`: `‖c‖ ^ 2 > 0`, but `C` times the `L`-values is `≤ 0`.
    refine ⟨1, one_pos, x, hx, fun 𝔪 ν χ h_tame ↦ ?_⟩
    obtain ⟨c, hc, h_size, -⟩ := h_exch 𝔪 ν χ h_tame
    have h_L : 0 ≤ lValueProd 𝔪.places ν e := by
      unfold lValueProd
      positivity
    nlinarith [norm_pos_iff.mpr hc]
  refine ⟨C, hC, x, hx, fun 𝔪 ν χ h_tame ↦ ?_⟩
  obtain ⟨c, hc, h_size, h_base⟩ := h_exch 𝔪 ν χ h_tame
  refine ⟨c, h_size, by simp [← h_size, hc], fun α α' h_prod Φ Ψ h_matched g ↦ ?_⟩
  set γ : AutChar E := rankTwist ν⁻¹ n
  have h_card : card n = card a + card b := by rw [add_comm, ← card_sum, card_congr σ]
  -- The splitting characters determine `α * α' = γ`.
  have h_char : α * α' = γ :=
    (spaceChar_mul_spaceChar_eq_iff h_card ⟨card b + e, by omega⟩).1 h_prod
  have h_char' : γ * α⁻¹ = α' := by rw [← h_char, mul_inv_cancel_comm]
  -- The twist law on both kernels, with the factor `d = α (det g)⁻¹`.
  let d : ℂ := (α.val g.det : ℂ)⁻¹
  have h_left (h : G E t) : pairTheta W V γ α (modDatum W V 𝔪 Φ x) (g, h) =
      d * pairTheta W V γ 1 (modDatum W V 𝔪 Φ x) (g, h) := by
    simpa using pairTheta_twist W V γ 1 1 α (modDatum W V 𝔪 Φ x) g h
  have h_right (h : G E t') : pairTheta V' W α' γ (modDatum V' W 𝔪 Ψ v) (h, g) =
      d * pairTheta V' W γ γ (modDatum V' W 𝔪 Ψ v) (h, g) := by
    simpa [h_char', circleChar_inv_apply] using
      pairTheta_twist V' W γ γ α⁻¹ 1 (modDatum V' W 𝔪 Ψ v) h g
  calc thetaIntegral W V γ α (modDatum W V 𝔪 Φ x) g
      = d * thetaIntegral W V γ 1 (modDatum W V 𝔪 Φ x) g := by
        simp only [thetaIntegral, h_left, MeasureTheory.integral_const_mul]
    _ = c * ∫ h : G E t', pairTheta V' W α' γ (modDatum V' W 𝔪 Ψ v) (h, g) ∂V'.quotMeasure := by
        simp only [h_base Φ Ψ h_matched g, h_right, MeasureTheory.integral_const_mul, mul_left_comm]

end ExchangeTheorem

end New.Exchange

end
