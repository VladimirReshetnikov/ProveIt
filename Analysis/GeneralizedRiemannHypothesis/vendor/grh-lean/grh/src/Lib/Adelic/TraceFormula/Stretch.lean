import Lib.Adelic.Reduction.FirstMinimumShortBases

/-!
# Rational points that pair short lattice vectors non-trivially

Let `y, y'` be vectors of the lattice of `V.move x` whose lengths have product at most `δ`, and let
`γ` be a rational point such that `x⁻¹ γ x` has finite part in a compact set. If `⟨y', γ y⟩` is not
`0`, then `(c δ)^f` times the product of `‖x⁻¹ γ x‖` over the `f` infinite places is at least `1`,
for a constant `c` that depends only on `V` and the compact set, because a non-zero algebraic
integer has norm at least `1`.

* `New.Space.exists_one_le_pow_mul_prod_norm`: the lower bound.

Notions from other files:
* `Space E n s`: a matrix `V.J` of a hermitian form on `E^n`, for `E` a field with a CM type
  (`CMType E`) whose embedding `Φ w` into `ℂ` gives the infinite place `w`, with an adelic basis
  `V.x` in which the form is `diag s` at infinity and `1` at the finite places; `V.move g` has the
  basis `V.x g`.
* `V.vecAtPoint y` is the adelic vector of coordinates of `y` in the basis `V.x`; `V.archCoords y`
  is its archimedean part, `V.coordsAt w y` its part at the infinite place `w`, and `V.baseLattice`
  is the lattice of the `y` for which its finite part is integral.
* `G E s` is the adelic unitary group, the product of the part at infinity and the finite part
  `Gf E n`; `V.ratEmbed γ` is the element of `G E s` given by a rational point `γ` of `U V.J`, the
  unitary group of the form `V.J` over `E`, in the basis `V.x`.
-/

open NumberField Matrix Fintype Norms.L2Operator

namespace New.Space

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n] {s : n → ℤˣ}
  (V : Space E n s)

/-- For `x` in the adelic unitary group `G E s` and a rational point `γ` of the unitary group of
the form `V.J`, the adelic coordinates `vecAtPoint` of `γ b` in `V.move x` (the space `V` with its
basis moved by `x`) are those of `b` multiplied by the matrix `adeleMatrix` of `x⁻¹ γ x`, where `γ`
is embedded in `G E s` by `ratEmbed`. -/
lemma vecAtPoint_move_mulVec (x : G E s) (γ : U V.J) (b : n → E) :
    (V.move x).vecAtPoint ((γ : Matrix n n E) *ᵥ b) =
      (x⁻¹ * V.ratEmbed γ * x).adeleMatrix *ᵥ (V.move x).vecAtPoint b := by
  rw [vecAtPoint_move, vecAtPoint_move, ← ratEmbed_mulVec_vecAtPoint, mulVec_mulVec, mulVec_mulVec,
    ← G.adeleMatrix_mul, ← G.adeleMatrix_mul, mul_inv_cancel_right]

/-- Let `x` lie in the adelic unitary group `G E s` (first factor: the part at infinity) and let
`γ` be a rational point of `U V.J`, embedded by `ratEmbed`. At an infinite place `w` the length of
`γ b` in the coordinates `coordsAt w` of `V.move x` (the space `V` with its basis moved by `x`) is
at most the length of `b` times the operator norm of the component at `w` of `x⁻¹ γ x`. -/
lemma norm_coordsAt_mulVec_le (x : G E s) (γ : U V.J) (w : InfinitePlace E) (b : n → E) :
    ‖(V.move x).coordsAt w ((γ : Matrix n n E) *ᵥ b)‖ ≤
      ‖((x⁻¹ * V.ratEmbed γ * x).1 w : Matrix n n ℂ)‖ * ‖(V.move x).coordsAt w b‖ := by
  set t : G E s := x⁻¹ * V.ratEmbed γ * x
  have h_mulVec : (V.move x).coordsAt w ((γ : Matrix n n E) *ᵥ b) =
      WithLp.toLp 2 ((t.1 w : Matrix n n ℂ) *ᵥ WithLp.ofLp ((V.move x).coordsAt w b)) := by
    ext i
    simp only [coordsAt, vecAtPoint_move_mulVec, mulVec, dotProduct, Prod.fst_sum, Prod.fst_mul,
      Finset.sum_apply, Pi.mul_apply, G.adeleMatrix_fst, t]
  rw [h_mulVec]
  exact l2_opNorm_mulVec _ _

/-- If `⟨y', γ y⟩ ≠ 0` for short lattice vectors `y` and `y'`, then `x⁻¹ γ x` is large at infinity.
Here `x` lies in the adelic unitary group `G E s`, whose two factors are the part at infinity and
the finite part, and `γ` is a rational point of `U V.J`, embedded in `G E s` by `ratEmbed`. For a
compact set `Ω` of finite parts there is `c ≥ 0` with the following property. Let `y` and `y'` lie
in the lattice of `V.move x` (the form of `V` with the basis moved by `x`), let their lengths
`‖archCoords‖` there have product at most `δ`, let the finite part of `x⁻¹ γ x` lie in `Ω`, and
let `⟨y', γ y⟩ ≠ 0`. Then `(c δ)^f` times the product of the operator norms of `x⁻¹ γ x` at the
infinite places is at least `1`, where `f` is the number of these places. -/
theorem exists_one_le_pow_mul_prod_norm {Ω : Set (Gf E n)} (hΩ : IsCompact Ω) :
    ∃ c ≥ (0 : ℝ), ∀ (x : G E s) (γ : U V.J) (y y' : n → E) (δ : ℝ),
      y ∈ (V.move x).baseLattice → y' ∈ (V.move x).baseLattice →
      ‖(V.move x).archCoords y‖ * ‖(V.move x).archCoords y'‖ ≤ δ →
      (x⁻¹ * V.ratEmbed γ * x).2 ∈ Ω → star y' ⬝ᵥ V.J *ᵥ ((γ : Matrix n n E) *ᵥ y) ≠ 0 →
      1 ≤ (c * δ) ^ Core.numInfPlaces E *
        ∏ w : InfinitePlace E, ‖((x⁻¹ * V.ratEmbed γ * x).1 w : Matrix n n ℂ)‖ := by
  -- The integer `c` clears denominators, so `c ⟨y', γ y⟩` is a non-zero algebraic integer, of norm
  -- at least `1`. Cauchy–Schwarz bounds it at each infinite place.
  obtain ⟨c, hc, h_denom⟩ := V.exists_smul_mulVec_mem_latticeBall hΩ
  refine ⟨c, c.cast_nonneg, fun x γ y y' δ hy hy' hδ hγ h_ne ↦ ?_⟩
  set t : G E s := x⁻¹ * V.ratEmbed γ * x
  set γy : n → E := (γ : Matrix n n E) *ᵥ y
  set z : E := star y' ⬝ᵥ V.J *ᵥ γy with hz
  -- `h_denom` needs one bound on the operator norms at all infinite places; take their supremum.
  have h_norm_le (w : InfinitePlace E) :
      ‖(t.1 w : Matrix n n ℂ)‖ ≤ ‖fun v : InfinitePlace E ↦ (t.1 v : Matrix n n ℂ)‖ :=
    norm_le_pi_norm (fun v : InfinitePlace E ↦ (t.1 v : Matrix n n ℂ)) w
  have h_mem : (c : E) • γy ∈ (V.move x).baseLattice := (h_denom hγ h_norm_le y hy).1
  have h_int : IsIntegral ℤ ((c : E) * z) := by
    simpa only [hz, move_J, mulVec_smul, dotProduct_smul, smul_eq_mul] using
      (V.move x).isIntegral_form hy' h_mem
  have h_place (w : InfinitePlace E) :
      ‖Φ w (c * z)‖ ≤ c * δ * ‖(t.1 w : Matrix n n ℂ)‖ :=
    calc ‖Φ w (c * z)‖
        = c * ‖Φ w z‖ := by rw [map_mul, map_natCast, norm_mul, Complex.norm_natCast]
      _ ≤ c * (‖(V.move x).coordsAt w y'‖ * ‖(V.move x).coordsAt w γy‖) := by
          gcongr
          exact (V.move x).norm_form_le w y' γy
      _ ≤ c * (‖(V.move x).archCoords y'‖ *
            (‖(t.1 w : Matrix n n ℂ)‖ * ‖(V.move x).archCoords y‖)) := by
          grw [V.norm_coordsAt_mulVec_le x γ w y, (V.move x).norm_coordsAt_le w y',
            (V.move x).norm_coordsAt_le w y]
      _ = c * (‖(V.move x).archCoords y‖ * ‖(V.move x).archCoords y'‖) *
            ‖(t.1 w : Matrix n n ℂ)‖ := by ring
      _ ≤ c * δ * ‖(t.1 w : Matrix n n ℂ)‖ := by gcongr
  calc 1 ≤ ∏ w : InfinitePlace E, ‖Φ w (c * z)‖ :=
        one_le_prod_norm_Φ h_int (mul_ne_zero (Nat.cast_ne_zero.2 hc) h_ne)
    _ ≤ ∏ w : InfinitePlace E, c * δ * ‖(t.1 w : Matrix n n ℂ)‖ :=
        Finset.prod_le_prod₀ (fun w _ ↦ norm_nonneg _) fun w _ ↦ h_place w
    _ = (c * δ) ^ Core.numInfPlaces E * ∏ w : InfinitePlace E, ‖(t.1 w : Matrix n n ℂ)‖ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

end New.Space
