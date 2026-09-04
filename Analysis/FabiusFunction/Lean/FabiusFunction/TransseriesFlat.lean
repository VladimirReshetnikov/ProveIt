import FabiusFunction.TransseriesPolyLogScale

/-!
# Flatness and the invisible-function problem

The transseries volume's `q0:def:flat` and `q0:prop:invisible`: a function is
*flat* relative to a scale when it is `O` of every term of that scale, and a
Poincaré expansion cannot see a flat function at all.

Everything here is stated for the abstract scale of `TransseriesScale.lean`, so
it applies to every scale the volume uses, and the concrete statements about
`e^{-x}` and the power scale `X^{-n}` are corollaries at the end.

The three clauses of `q0:prop:invisible` become:

* `flatSubmodule` — the flat functions form a `𝕜`-submodule of `α → 𝕜`;
* `IsFlat.mul_absorbsScale` — closed under multiplication by anything that
  *absorbs the scale*, the abstract form of "at most polynomial growth", and
  `absorbsScale_of_isBigO_pow` says a function bounded by a power really does
  absorb the power scale;
* `isPoincareExpansion_iff_isFlat_sub` — two functions have the same expansion
  on a scale exactly when they differ by a flat function.

The last of these is the sharp form of the volume's "no refinement of the
coefficients can recover the difference": it is an iff, so the flat functions
are *precisely* the invisible ones, not merely some of them.  Note that it
needs no hypothesis on the scale beyond `IsPoincareExpansion` itself — in
particular neither `IsAsymptoticScale` nor `l.NeBot`, both of which the
uniqueness theorem for coefficients does need.
-/

set_option autoImplicit false

open Filter Asymptotics Finset

namespace Fabius

variable {α 𝕜 : Type*} [NormedField 𝕜] {l : Filter α} {φ : ℕ → α → 𝕜}
  {f g ε δ h : α → 𝕜} {a : ℕ → 𝕜}

/-! ### Flatness -/

/-- **`q0:def:flat`.**  `ε` is flat relative to the scale `φ` when it is `O` of
every term of the scale.  On the power scale this is `ε = O(x^{-∞})`. -/
def IsFlat (l : Filter α) (φ : ℕ → α → 𝕜) (ε : α → 𝕜) : Prop :=
  ∀ n, ε =O[l] φ n

theorem isFlat_zero : IsFlat l φ (0 : α → 𝕜) := fun _ => isBigO_zero _ _

theorem IsFlat.add (hε : IsFlat l φ ε) (hδ : IsFlat l φ δ) : IsFlat l φ (ε + δ) :=
  fun n => (hε n).add (hδ n)

theorem IsFlat.neg (hε : IsFlat l φ ε) : IsFlat l φ (-ε) := fun n => (hε n).neg_left

theorem IsFlat.sub (hε : IsFlat l φ ε) (hδ : IsFlat l φ δ) : IsFlat l φ (ε - δ) :=
  fun n => (hε n).sub (hδ n)

theorem IsFlat.const_smul (c : 𝕜) (hε : IsFlat l φ ε) : IsFlat l φ (c • ε) :=
  fun n => (hε n).const_smul_left c

/-- **`q0:prop:invisible`, first clause.**  The functions flat relative to a
given scale form a submodule. -/
def flatSubmodule (l : Filter α) (φ : ℕ → α → 𝕜) : Submodule 𝕜 (α → 𝕜) where
  carrier := {ε | IsFlat l φ ε}
  add_mem' hε hδ := hε.add hδ
  zero_mem' := isFlat_zero
  smul_mem' c _ hε := hε.const_smul c

@[simp] theorem mem_flatSubmodule_iff : ε ∈ flatSubmodule l φ ↔ IsFlat l φ ε := Iff.rfl

/-! ### Closure under multiplication -/

/-- `h` **absorbs the scale** `φ` when multiplying by `h` can be compensated by
moving far enough along the scale: for every `n` some later term `φ m` satisfies
`h · φ m = O(φ n)`.  This is the abstract content of "at most polynomial
growth" in `q0:prop:invisible`; see `absorbsScale_of_isBigO_pow`. -/
def AbsorbsScale (l : Filter α) (φ : ℕ → α → 𝕜) (h : α → 𝕜) : Prop :=
  ∀ n, ∃ m, (fun x => h x * φ m x) =O[l] φ n

/-- **`q0:prop:invisible`, second clause.**  Flatness survives multiplication by
anything that absorbs the scale. -/
theorem IsFlat.mul_absorbsScale (hh : AbsorbsScale l φ h) (hε : IsFlat l φ ε) :
    IsFlat l φ (fun x => h x * ε x) := by
  intro n
  obtain ⟨m, hm⟩ := hh n
  exact (((isBigO_refl h l).mul (hε m)).trans hm)

/-- A constant absorbs every scale, so `IsFlat.const_smul` is a special case of
`IsFlat.mul_absorbsScale`. -/
theorem absorbsScale_const (c : 𝕜) : AbsorbsScale l φ (fun _ => c) :=
  fun n => ⟨n, (isBigO_refl (φ n) l).const_mul_left c⟩

/-! ### Invisibility -/

/-- **`q0:prop:invisible`, third clause, one direction.**  Adding a flat
function does not change a Poincaré expansion. -/
theorem IsPoincareExpansion.add_isFlat (hf : IsPoincareExpansion l φ f a)
    (hε : IsFlat l φ ε) : IsPoincareExpansion l φ (f + ε) a := by
  intro N
  have := (hf N).add (hε N)
  refine this.congr_left fun x => ?_
  simp only [Pi.add_apply]
  ring

/-- Two functions with the same expansion on the same scale differ by a flat
function. -/
theorem isFlat_sub_of_isPoincareExpansion (hf : IsPoincareExpansion l φ f a)
    (hg : IsPoincareExpansion l φ g a) : IsFlat l φ (f - g) := by
  intro N
  have := (hf N).sub (hg N)
  refine this.congr_left fun x => ?_
  simp only [Pi.sub_apply]
  ring

/-- **`q0:prop:invisible`, third clause, sharp form.**  Given one function with
the expansion `a`, the functions with that same expansion are *exactly* the ones
differing from it by a flat function.  So a Poincaré expansion determines `f`
modulo `flatSubmodule l φ` and no finer. -/
theorem isPoincareExpansion_iff_isFlat_sub (hf : IsPoincareExpansion l φ f a) :
    IsPoincareExpansion l φ g a ↔ IsFlat l φ (g - f) := by
  refine ⟨fun hg => isFlat_sub_of_isPoincareExpansion hg hf, fun hflat => ?_⟩
  have := hf.add_isFlat hflat
  refine fun N => (this N).congr_left fun x => ?_
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- The zero sequence expands every flat function, and only flat functions:
flatness *is* having the identically zero Poincaré expansion. -/
theorem isPoincareExpansion_zero_iff : IsPoincareExpansion l φ ε 0 ↔ IsFlat l φ ε := by
  constructor <;> intro h N
  · exact (h N).congr_left fun x => by simp
  · exact (h N).congr_left fun x => by simp

/-! ### The power scale and `e^{-x}` -/

section PowerScale

open Real

/-- The power scale `X ↦ X^{-n}` of the volume, written with `plMonomial` so
that the results of `TransseriesPolyLogScale.lean` apply to it. -/
noncomputable def powScale (n : ℕ) (X : ℝ) : ℝ := plMonomial (-(n : ℝ)) 0 X

theorem powScale_eq_rpow (n : ℕ) (X : ℝ) : powScale n X = X ^ (-(n : ℝ)) := by
  rw [powScale, plMonomial, Real.rpow_zero, mul_one]

/-- **`q0:prop:invisible`, second clause, concrete form.**  A function bounded by
a fixed power absorbs the power scale, so multiplication by it preserves
flatness.  The compensation is exact rather than merely an inequality: moving
`N` places further along the scale cancels the growth on the nose. -/
theorem absorbsScale_of_isBigO_pow {h : ℝ → ℝ} {N : ℕ}
    (hh : h =O[atTop] fun X => X ^ N) : AbsorbsScale atTop powScale h := by
  intro n
  refine ⟨n + N, ?_⟩
  have hcancel : (fun X : ℝ => X ^ N * powScale (n + N) X) =ᶠ[atTop] powScale n := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    rw [powScale_eq_rpow, powScale_eq_rpow, ← Real.rpow_natCast X N, ← Real.rpow_add hX]
    push_cast
    ring_nf
  exact (hh.mul (isBigO_refl (powScale (n + N)) atTop)).trans hcancel.isBigO

/-- **`q0:prop:invisible`, first clause, concrete form.**  `e^{-x}` is flat
relative to the power scale: `e^{-x} = O(x^{-∞})`. -/
theorem isFlat_exp_neg : IsFlat atTop powScale fun x : ℝ => Real.exp (-x) := by
  intro n
  refine ((isLittleO_iff_tendsto' ?_).2 ?_).isBigO
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX hzero
    rw [powScale_eq_rpow] at hzero
    exact absurd hzero (Real.rpow_pos_of_pos (lt_trans one_pos hX) _).ne'
  · have hlim := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    rw [powScale_eq_rpow, Real.rpow_neg hX.le, div_inv_eq, ← Real.rpow_natCast X n]
    ring

/-- Consequently `e^{-x}` is invisible to the power scale: for every `f` with a
Poincaré expansion there, `f` and `f + e^{-x}` have exactly the same
coefficients, at every order. -/
theorem isPoincareExpansion_add_exp_neg {f : ℝ → ℝ} {a : ℕ → ℝ}
    (hf : IsPoincareExpansion atTop powScale f a) :
    IsPoincareExpansion atTop powScale (fun x => f x + Real.exp (-x)) a :=
  hf.add_isFlat isFlat_exp_neg

end PowerScale

end Fabius
