import Lib.SiegelWeil.Tower.FunctionalEquation
import New.Determinant.Exchange.ConeImage
import New.Determinant.Exchange.RemovingPlanes

/-!
# Vanishing of theta integrals descends along hyperbolic planes

If the theta integral of `(W ⊕ H, V ⊕ H)` vanishes on all Schwartz vectors and standard data, so
does that of `(W, V)`, provided `W` has even rank and `rk V - rk W / 2 ≥ -k` for a natural number
`k ≤ min μ`. The constant term along the new isotropic line is a value of Tate's integral, and for
the vectors of `exists_thetaLarge_cone_eq_mul` this integral is, by analytic continuation, the theta
integral of `(W, V)` times factors that do not vanish at the value in question.

Notions from other files:
* `thetaLarge W V 𝔠 v Φ`: the theta integral over `[U(V)]` of `v ⊗ Φ`, a function on `G E s`;
* `stdRowDatum σ χ y`: the finite datum `x ↦ χ⁻¹ (det (y; x))`, supported where the square matrix
  `(y; x)`, with rows ordered by `σ`, is invertible and integral;
* `SplitTameChar E μ`: a tame character of weight `μ`, ramified at a finite set of split places;
* `negCount s`: the number of signs `-1` among `s`.

## Relation to the literature

See `New.Determinant.Exchange.TheoremForPartners` for related work.
-/

noncomputable section

namespace New.Exchange

open MeasureTheory Fintype Space Set
open NumberField (InfinitePlace)

variable {E : Type} [Field E] [CMType E] [WeilData E] {n n' r r' b : Type} [Fintype n]
  [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype r] [DecidableEq r] [Fintype r']
  [DecidableEq r'] [Fintype b] [DecidableEq b] {s : n → ℤˣ} {s' : n' → ℤˣ} {t : r → ℤˣ}
  {t' : r' → ℤˣ} {μ : InfinitePlace E → ℤ} {𝔠 : SplitTameChar E μ}

variable (𝔠) in
/-- Let `W` and `V` be hermitian spaces over `E` with bases indexed by `n` and `r` and with signs
`s` and `t` at the infinite places. The theta integral of `(W, V)` for the split tame character `𝔠`,
a function on the adelic unitary group `G E s` of `W`, vanishes on all Schwartz vectors `v` (all
Fock moments finite) of the Fock space `PairFock E s t` of `Hom(W, V)` and all standard data
`stdRowDatum σ 𝔠.semilocalChar y`. Here `y` is any integral `b × n` matrix over the product of the
completions at the ramified places `𝔠.ramifiedPlaces`, and `σ` orders the rows of `y` and of an
`r × n` matrix into a square matrix. -/
def ThetaLargeVanishes (W : Space E n s) (V : Space E r t) (σ : b ⊕ r ≃ n) : Prop :=
  ∀ v : PairFock E s t, IsSchwartzVector v →
    ∀ y : Matrix b n (LocProd 𝔠.ramifiedPlaces), IsIntMatrix SemilocalField.O y →
      ∀ g : G E s, thetaLarge W V 𝔠 v (stdRowDatum σ 𝔠.semilocalChar y) g = 0

omit [Fintype b] [DecidableEq b] in
/-- Let `W`, `W₁` be hermitian spaces with the same signs `s`, and `V`, `V₁` with the same signs
`t`. If, for the split tame character `𝔠`, the theta integral of `(W, V)` at every point of the
unitary group of `W` vanishes on all Schwartz vectors and all standard data, so does that of
`(W₁, V₁)`. -/
lemma ThetaLargeVanishes.congr_spaces {W : Space E n s} {V : Space E r t} {σ : b ⊕ r ≃ n}
    (h_zero : ThetaLargeVanishes 𝔠 W V σ) (W₁ : Space E n s) (V₁ : Space E r t) :
    ThetaLargeVanishes 𝔠 W₁ V₁ σ := by
  obtain ⟨γ, h_transport⟩ := exists_thetaLarge_thetaSmall_eq_circle_mul W W₁ V V₁ V V₁
  -- The integral of `(W₁, V₁)` at `g` is `u` times that of `(W, V)` at `γ * g`.
  obtain ⟨u, h_eq_mul⟩ := (h_transport 𝔠).left
  intro v hv y hy g
  rw [h_eq_mul, h_zero v hv y hy, mul_zero]

/-- Adding a hyperbolic plane, with signs `hyperbolicSigns Unit` (one `+1` and one `-1`), to signs
`ε` adds one negative sign. -/
lemma negCount_sumElim_hyperbolicSigns_unit {m : Type} [Fintype m] (ε : m → ℤˣ) :
    negCount (Sum.elim (hyperbolicSigns Unit) ε) = negCount ε + 1 := by
  simp +arith [negCount_sumElim, negCount_one_and_neg_one]

/-- Descent along one hyperbolic plane `H`. Let `A` and `X` be adapted splittings (orthonormal at
the infinite and integral at the finite places) `W' = W ⊕ H` and `V' = V ⊕ H` of hermitian spaces.
Let `W` be of even rank and `-k ≤ rk V - rk W / 2`, with `k ≤ μ w` at every infinite place `w`,
where `μ` is the weight of the split tame character `𝔠`.

If at every point of the unitary group of `W'` the theta integral of `(W', V')` vanishes on all
Schwartz vectors (finite weighted norms) and all data `stdRowDatum σ' 𝔠.semilocalChar y'`, then at
every point `g` of the unitary group of `W` that of `(W, V)` vanishes on all Schwartz vectors and
all data `stdRowDatum σ 𝔠.semilocalChar y`. Here `y'` and `y` are arbitrary integral matrices at
the ramified places of `𝔠`, with rows indexed by `b` and columns by the bases of `W'` and `W`; the
orderings `σ` and `σ'` of these rows and those indexed by the basis of `V`, respectively `V'`, into
a square matrix are arbitrary. -/
theorem ThetaLargeVanishes.of_add_plane {k : ℕ} {W : Space E n s} {W' : Space E n' s'}
    {V : Space E r t} {V' : Space E r' t'} (A : W'.Splitting W Unit) (X : V'.Splitting V Unit)
    [IsBaseAdapted A] [IsBaseAdapted X] (σ : b ⊕ r ≃ n) {σ' : b ⊕ r' ≃ n'} (hn_even : 2 ∣ card n)
    (hk_le : ∀ w : InfinitePlace E, k ≤ μ w) (h_range : -(k : ℤ) ≤ card r - card n / 2)
    (h_zero : ThetaLargeVanishes 𝔠 W' V' σ') : ThetaLargeVanishes 𝔠 W V σ := by
  intro v hv y hy g
  -- Tate's integral of a suitable vector `v'` of `(W', V')` is a product of simple factors and the
  -- theta integral of `(W, V)` at `v`. Its value at `e + 1`, for `e = rk V - rk W / 2`, where these
  -- factors are non-zero, is a constant term of the theta integral of `(W', V')`, hence zero.
  let I : ℂ := thetaLarge W V 𝔠 v (stdRowDatum σ 𝔠.semilocalChar y) g
  obtain ⟨B, hB_pos, hB_analytic, h_image⟩ :=
    exists_thetaLarge_cone_eq_mul A X μ σ hn_even
  -- For `x > 0` the theta integral of `(W, V)` at the cone integral of `v'` is `B x * I`.
  obtain ⟨v', hv', h_cone⟩ := h_image v hv
  -- `Λ` continues the L-function `x ↦ 𝔠.character.L 𝔠.ramifiedPlaces x` analytically to `x > -k`.
  obtain ⟨Λ, hΛ_analytic, hΛ_eq, hΛ_ne⟩ := exists_analytic_extension_ne_zero hk_le 𝔠
  obtain ⟨a, ha_pos, h_zeta⟩ := exists_zetaIntegral A X σ' σ hn_even μ
  obtain ⟨ε, hε_norm, h_zeta_char⟩ := h_zeta 𝔠
  let P (x : ℝ) : ℝ :=
    ideleAbs (WeilData.scaleIdele E) ^ x * ∏ w : 𝔠.ramifiedPlaces, (w.val.q : ℝ) ^ (x - 1 / 2)
  let e : ℤ := card r - card n / 2
  obtain ⟨𝒵, h𝒵_analytic, h_constantTerm_eq, h_tate_eq⟩ :
      ∃ 𝒵 : ℝ → ℂ, AnalyticOnNhd ℝ 𝒵 univ ∧ planeConstantTerm 𝔠 V' A σ' v' y 1 g = 𝒵 (e + 1) ∧
        ∀ (β : Bool) (x : ℝ), 1 ≤ x → 𝒵 (cond β x (1 - x)) =
          ε β * P x * 𝔠.character.L 𝔠.ramifiedPlaces x *
            thetaLarge W V 𝔠 (∫ p, coneIntegrand A X μ β x v' p ∂Measure.haar.prod Measure.haar)
              (stdRowDatum σ 𝔠.semilocalChar y) g :=
    h_zeta_char v' hv' y hy 1 g (Or.inl rfl)
  -- For `x ≥ 1`, hence for `x > -k`, Tate's integral of `v'` is `ε P(x) Λ(x) B(x) I`.
  let R (x : ℝ) : ℂ := ε true * P x * Λ x * (B x * I)
  have h_product : EqOn 𝒵 R (Ioi (-(k : ℝ))) := by
    have h_analytic : AnalyticOnNhd ℝ R (Ioi (-(k : ℝ))) := fun x hx ↦
      ((analyticAt_const.mul (analyticAt_ideleAbs_rpow_mul_prod_rpow 𝔠 x)).mul
        (hΛ_analytic x hx)).mul ((hB_analytic x (mem_univ x)).mul analyticAt_const)
    have h_two_mem : (2 : ℝ) ∈ Ioi (-(k : ℝ)) :=
      mem_Ioi.2 ((neg_nonpos.2 k.cast_nonneg).trans_lt two_pos)
    refine (h𝒵_analytic.mono (subset_univ _)).eqOn_of_preconnected_of_eventuallyEq h_analytic
      isPreconnected_Ioi h_two_mem ?_
    filter_upwards [Ici_mem_nhds one_lt_two] with x hx
    -- For `β = true`, `cond β x (1 - x)` is `x` and the integral of `coneIntegrand` is `cone`.
    simp only [R, I]
    rw [hΛ_eq x hx, ← h_cone x (one_pos.trans_le hx) 𝔠 y g]
    exact h_tate_eq true x hx
  -- At `e + 1` it is the constant term of a function that vanishes.
  have h_lower : -(k : ℤ) < e + 1 := by omega
  have h_tate_zero : 𝒵 (e + 1 : ℤ) = 0 := by
    have h_int := hy.mul (adaptedFrame 𝔠.readsAt A).blockRelations.isIntMatrix_dualI
    simp [← h_constantTerm_eq, planeConstantTerm, h_zero v' hv' _ h_int]
  -- Every factor other than `I` is non-zero there.
  have h_R_zero : R (e + 1 : ℤ) = 0 :=
    (h_product (mem_Ioi.2 (mod_cast h_lower))).symm.trans h_tate_zero
  have hε_ne : ε true ≠ 0 := norm_pos_iff.1 ((ha_pos true).trans_eq (hε_norm true).symm)
  have hP_pos : 0 < P (e + 1 : ℤ) := mul_pos (Real.rpow_pos_of_pos ideleAbs_pos _)
    (Finset.prod_pos fun w _ ↦ Real.rpow_pos_of_pos (by simp [FinPlace.q_bounds]) _)
  show I = 0
  simpa only [R, mul_eq_zero, Complex.ofReal_eq_zero, hε_ne, hP_pos.ne', hΛ_ne _ h_lower,
    (hB_pos _).ne', false_or] using h_R_zero

/-- Descent along any positive number `j` of hyperbolic planes `H`. Let the hermitian space `W'`
have the rank and number of negative signs of `W ⊕ H ^ j`, and let `V'` have the number of negative
signs of `V ⊕ H ^ j`; its rank is then that of `V ⊕ H ^ j` too, by `σ` and `σ'`. Let `W` be of even
rank and `-k ≤ rk V - rk W / 2`, where `k ≤ μ w` at every infinite place `w` and `μ` is the weight
of the split tame character `𝔠`.

If at every point of the unitary group of `W'` the theta integral of `(W', V')` vanishes on all
Schwartz vectors and all data `stdRowDatum σ' 𝔠.semilocalChar y'`, then at every point of the
unitary group of `W` that of `(W, V)` vanishes on all Schwartz vectors and all data
`stdRowDatum σ 𝔠.semilocalChar y`. Integrality at the ramified places of `𝔠` is the only condition
on the matrices `y'` and `y`; their rows are indexed by `b`, and `σ`, `σ'` order these rows and
those indexed by the basis of `V`, respectively `V'`, into a square matrix. -/
theorem ThetaLargeVanishes.of_add_planes {k : ℕ} {W' : Space E n' s'} {V' : Space E r' t'}
    {σ' : b ⊕ r' ≃ n'} (h_zero : ThetaLargeVanishes 𝔠 W' V' σ')
    (hk_le : ∀ w : InfinitePlace E, k ≤ μ w) {j : ℕ} (hj : 1 ≤ j) (W : Space E n s)
    (V : Space E r t) (σ : b ⊕ r ≃ n) (hn_even : 2 ∣ card n)
    (h_range : -(k : ℤ) ≤ card r - card n / 2) (h_rank : card n' = card n + 2 * j)
    (h_negCount_W : negCount s' = j + negCount s) (h_negCount_V : negCount t' = j + negCount t) :
    ThetaLargeVanishes 𝔠 W V σ := by
  induction j, hj using Nat.le_induction generalizing n r with
  | base =>
    have h_card_W : card b + card r = card n := card_sum.symm.trans (card_congr σ)
    have h_card_W' : card b + card r' = card n' := card_sum.symm.trans (card_congr σ')
    obtain ⟨W₁, A, _⟩ := exists_isBaseAdapted Unit W s' (by simp [h_rank]) (by simp [h_negCount_W])
    have h_rank_V : card r' = card r + 2 := by omega
    obtain ⟨V₁, X, _⟩ :=
      exists_isBaseAdapted Unit V t' (by simp [h_rank_V]) (by simp [h_negCount_V])
    exact (h_zero.congr_spaces W₁ V₁).of_add_plane A X σ hn_even hk_le h_range
  | succ j _ ih =>
    -- Descend to `(H ⊕ W, H ⊕ V)`, then remove the last plane.
    have h_card : card (b ⊕ r) = card n := card_congr σ
    let τ : b ⊕ (Unit ⊕ Unit) ⊕ r ≃ (Unit ⊕ Unit) ⊕ n := equivOfCardEq (by simp +arith [← h_card])
    -- One plane raises each rank by two and each number of negative signs by one.
    have h_card_W : card ((Unit ⊕ Unit) ⊕ n) = card n + 2 := by simp +arith
    have h_card_V : card ((Unit ⊕ Unit) ⊕ r) = card r + 2 := by simp +arith
    have h_neg_W : negCount (Sum.elim (hyperbolicSigns Unit) s) = negCount s + 1 :=
      negCount_sumElim_hyperbolicSigns_unit s
    have h_neg_V : negCount (Sum.elim (hyperbolicSigns Unit) t) = negCount t + 1 :=
      negCount_sumElim_hyperbolicSigns_unit t
    have h_above : ThetaLargeVanishes 𝔠 (hyperbolicSum Unit W) (hyperbolicSum Unit V) τ :=
      ih (hyperbolicSum Unit W) (hyperbolicSum Unit V) τ (by omega) (by omega) (by omega)
        (by omega) (by omega)
    exact h_above.of_add_plane (removePlanes Unit W) (removePlanes Unit V) σ hn_even hk_le h_range

end New.Exchange
