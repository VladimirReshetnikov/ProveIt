import Lib.General.NumberTheory.GaussValuation

/-!
# Coefficient rings inside the ring of all integral elements

Elementary facts on the inclusion of a coefficient ring into `ℤ̄_ℓ`, and a divisibility statement
for geometric sums in a ring with a divisibility-reflecting map to `ℤ̄_ℓ`.

* `New.CoeffRing.toIntQpBar`: the inclusion, which reflects divisibility
  (`New.CoeffRing.dvd_of_toIntQpBar_dvd`).
* `New.Selmer.pow_dvd_geom_sum`: for `α` near `1`, a high power of `ℓ` divides `∑ i < ℓ ^ N, α ^ i`.

Notions from other files:
* `New.CoeffRing`: rings of integers of finite Galois extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`;
  `New.CoeffRing.normLength` rescales `ℕ∞`-valued lengths over such a ring, a uniformiser `ϖ` having
  length `v(ϖ)`, so that lengths over different rings are comparable.
* `New.ellVal`: the valuation `v` on `ℚ̄_ℓ` with `v ℓ = 1`, cut off below at `0`; `New.intQpBar ℓ`
  is the ring `ℤ̄_ℓ` of integral elements; throughout, the instance `ThePrime ℓ` fixes `ℓ` as the
  prime in play.
-/

noncomputable section

namespace New

open Finset IsDiscreteValuationRing

open scoped NNReal NNRat

variable {ℓ : ℕ} [ThePrime ℓ]

/-- The inclusion of a coefficient ring `O` (the ring of integers of a finite Galois extension of
`ℚ_ℓ` inside `ℚ̄_ℓ`) into the ring `ℤ̄_ℓ` of all integral elements. -/
def CoeffRing.toIntQpBar (O : CoeffRing ℓ) : O.val →+* intQpBar ℓ :=
  (Subalgebra.val O.val).toRingHom.codRestrict (intQpBar ℓ)
    fun x : O.val ↦ CoeffRing.norm_le_one x

@[simp] lemma CoeffRing.coe_toIntQpBar {O : CoeffRing ℓ} (x : O.val) :
    (O.toIntQpBar x).val = x.val := rfl

/-- For coefficient rings `O ≤ O'`, including `O` into `O'` and then into `ℤ̄_ℓ` is the inclusion
of `O` into `ℤ̄_ℓ`. -/
lemma CoeffRing.toIntQpBar_comp_inclusion {O O' : CoeffRing ℓ} (hO : O ≤ O') :
    O'.toIntQpBar.comp (Subalgebra.inclusion hO).toRingHom = O.toIntQpBar := rfl

lemma CoeffRing.dvd_iff_ellVal_le {O : CoeffRing ℓ} {x y : O.val} :
    x ∣ y ↔ ellVal x.val ≤ ellVal y.val := by
  have h_norm : ellVal x.val ≤ ellVal y.val ↔ ‖y.val‖ ≤ ‖x.val‖ := by
    simpa using ellVal_le_add_iff (c := 0) (norm_le_one y)
  rw [dvd_iff_norm_le, h_norm]

/-- The inclusion `toIntQpBar` of a coefficient ring (the integers of a finite Galois extension of
`ℚ_ℓ`) into the ring `ℤ̄_ℓ` of integral elements of `ℚ̄_ℓ` reflects divisibility. -/
lemma CoeffRing.dvd_of_toIntQpBar_dvd (O : CoeffRing ℓ) (z z' : O.val)
    (h_dvd : O.toIntQpBar z ∣ O.toIntQpBar z') : z ∣ z' := by
  rwa [Selmer.dvd_iff_ellVal_le, coe_toIntQpBar, coe_toIntQpBar, ← dvd_iff_ellVal_le] at h_dvd

/-- Let `O ≤ O'` be coefficient rings, `P` a polynomial over `O` and `x` a point with coordinates
in `O'`. The exponent of a uniformiser `ϖ` in `P(x) ∈ O'`, rescaled by `normLength` (that is,
multiplied by `v(ϖ)`), is the normalised valuation `v = ellVal` of the value in `ℤ̄_ℓ` that is
obtained by mapping `P` and `x` there with the inclusions `toIntQpBar`. -/
lemma CoeffRing.normLength_addVal_eval₂ {O O' : CoeffRing ℓ} (hO : O ≤ O') {σ : Type}
    (P : MvPolynomial σ O.val) (x : σ → O'.val) :
    O'.normLength (addVal O'.val (P.eval₂ (Subalgebra.inclusion hO).toRingHom x)) =
      ellVal (MvPolynomial.eval (fun j : σ ↦ O'.toIntQpBar (x j)) (P.map O.toIntQpBar)).val := by
  rw [normLength_addVal, ← coe_toIntQpBar, MvPolynomial.eval₂_comp_left, toIntQpBar_comp_inclusion,
    MvPolynomial.eval_map, Function.comp_def]

/-- Finitely many elements of `ℤ̄_ℓ` lie in all sufficiently large coefficient rings `O` (rings of
integers of finite Galois extensions of `ℚ_ℓ` in `ℚ̄_ℓ`, ordered by inclusion), that is, they are
in the image of the inclusion `O.toIntQpBar`. -/
lemma CoeffRing.eventually_exists_toIntQpBar_eq {σ : Type} [Finite σ] (x : σ → intQpBar ℓ) :
    ∀ᶠ O : CoeffRing ℓ in Filter.atTop,
      ∃ x' : σ → O.val, ∀ j : σ, O.toIntQpBar (x' j) = x j := by
  have h_norm (j : σ) : ‖(x j).val‖ ≤ 1 :=
    (Valuation.mem_valuationSubring_iff _ _).1 (x j).property
  have h_mem : ∀ᶠ O : CoeffRing ℓ in Filter.atTop, ∀ j : σ, (x j).val ∈ O.val :=
    Filter.eventually_all.2 fun j : σ ↦ eventually_mem (h_norm j)
  filter_upwards [h_mem] with O hO
  exact ⟨fun j : σ ↦ ⟨(x j).val, hO j⟩, fun j : σ ↦ Subtype.ext (coe_toIntQpBar _)⟩

namespace Selmer

/-- Let `f` be a ring map from `O` to `ℤ̄_ℓ = intQpBar ℓ`, the integral elements of `ℚ̄_ℓ`, that
reflects divisibility. If `r ≤ 1`, `v(f(α - 1)) ≥ r` for the valuation `v = ellVal` with
`v(ℓ) = 1`, and `M ≤ N r`, then `ℓ ^ M` divides `∑ i < ℓ ^ N, α ^ i`. -/
lemma pow_dvd_geom_sum {O : Type*} [CommRing O] (f : O →+* intQpBar ℓ)
    (hf : ∀ z z' : O, f z ∣ f z' → z ∣ z') {r : ℚ≥0} {M N : ℕ} (hr : r ≤ 1)
    (hMN : (M : ℚ≥0) ≤ N * r) {α : O} (hα : (r : ℝ≥0) ≤ ellVal (f (α - 1)).val) :
    (ℓ ^ M : O) ∣ ∑ i ∈ range (ℓ ^ N), α ^ i := by
  rw [map_sub, map_one] at hα
  apply hf
  rw [dvd_iff_ellVal_le]
  calc
    ellVal (f (ℓ ^ M)).val = M := by simp
    _ ≤ N * (r : ℝ≥0) := by exact_mod_cast hMN
    _ ≤ ellVal (∑ i ∈ range (ℓ ^ N), f α ^ i).val := le_ellVal_geom_sum hr hα N
    _ = ellVal (f (∑ i ∈ range (ℓ ^ N), α ^ i)).val := by simp only [map_pow, map_sum]

end Selmer

end New

end
