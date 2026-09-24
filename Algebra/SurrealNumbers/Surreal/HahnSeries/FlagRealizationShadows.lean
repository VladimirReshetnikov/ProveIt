import Mathlib.Topology.Algebra.Order.Field
import Surreal.Algebra.MarkovResolvent
import Surreal.Algebra.StochasticIdempotent
import Surreal.HahnSeries.AlgebraicallyClosed
import Surreal.HahnSeries.MarkovResidueShadow
import Surreal.HahnSeries.PolynomialNewtonProfile

/-!
# Shadows of the projection-flag generator, its completion, and initial spectra

This file proves the residue clauses of `markov:thm:flag-realization`, the shadow-invariance
clause of `markov:lem:completion` and `markov:lem:initial-spectrum` (in the Newton-profile form
of `markov:rem:newton`) of `docs/surreal/markov-generators-at-every-scale/article.tex`.

**Setting.** `Γ` is any linearly ordered abelian group and `F = Lex ℝ⟦Γ⟧` is `ℝ((t^Γ))`. The
source's assumptions that `Γ` is nonzero and divisible are used only in two corollaries:
`exists_shadow_flagGen_eq` (every plateau is attained, under `Nontrivial Γ` and
`DenselyOrdered Γ`) and `exists_prod_X_add_C_of_monic` (splitting over an algebraically closed
Hahn field, under `DivisibleBy Γ ℕ`). `constHom : ℝ →+* F` embeds the real constants,
`liftFlag` lifts a real flag entrywise, `mono α c = ct^α`, `res` is the `t^0` coefficient and
`shadow L α c = K_α(c) = res R_L(ct^α)` (`Surreal/HahnSeries/MarkovResidueShadow.lean`). As in
`Surreal/Algebra/MarkovResolvent.lean`, indices are shifted by one: `P j` is the source's `P_j`,
but `α j` is the source's `α_{j+1}` and `flagStep P j = P j - P (j + 1)` is the source's
`E_{j+1}`. `flagGen P α m` is the generator `markov:eq:simple-inverse` with `τ_j = t^{α_j}`.

**`markov:thm:flag-realization`.**
* `res_mono_div_mono_add`: `res(ct^γ/(ct^γ + at^α))` is `1`, `0` or `c/(c + a)` according as
  `γ < α`, `γ > α` or `γ = α`.
* `shadowAt_flagGenerator`: for any `τ` and any `s ≠ 0` with `s + τ_j ≠ 0`,
  `res R_H(s) = P_m + ∑ res(s/(s + τ_j))E_j`; `shadow_flagGen` is the case `s = ct^γ`.
* `shadow_flagGen_plateau` (with `shadow_flagGen_initial`, `shadow_flagGen_between` and
  `shadow_flagGen_final`), as implications: if `γ` lies below `α_1`, strictly between `α_j` and
  `α_{j+1}`, or above `α_m`, then the shadow at `γ` is `I`, `P_j` or `P_m` respectively, for
  every `c > 0`. `exists_shadow_flagGen_eq_of_ne`: for increasing scales, every scale other than
  the `α_j` has shadow `P_k` for some `k ≤ m`.
* `exists_shadow_flagGen_eq`: that every `P_k` is actually attained needs a scale in each of these
  intervals. This holds when `Γ` is nontrivial and densely ordered, as for the source's nonzero
  divisible `Γ`, but not in general (for `Γ = ℤ` and scales `0, 1` no scale lies strictly between
  them). For every `Γ` and `m ≥ 1`, each `P_k` is still a limit of a crossover (see below).
* `shadow_flagGen_crossover`: `markov:eq:simple-inverse-shadow`,
  `K_{α_j}(c) = P_j + c/(c + 1)(P_{j-1} - P_j)`. Its limits as `c → ∞` and `c → 0⁺` are the
  adjacent plateaux `P_{j-1}` and `P_j` (`tendsto_shadow_flagGen_atTop`,
  `tendsto_shadow_flagGen_zero`).
* `shadow_flagGen_injective` and `shadow_flagGen_const_iff`: when `P_{j-1} ≠ P_j`, the crossover
  at `α_j` is nontrivial (`c ↦ K_{α_j}(c)` is injective), and for a flag of distinct matrices
  the shadow at `γ` is independent of `c` exactly when `γ` is none of the `α_j`, so there are no
  other crossovers.
* `flagGen_mulVec_one` and `flagGen_offDiag_nonpos`: `H` is a Hahn row Laplacian. The exact
  resolvent `markov:eq:simple-inverse-resolvent` is `Markov.resolvent_flagGenerator`.

The distinctness and rank-one hypotheses are used only where they are needed: distinctness for
nontriviality, `rank P_m = 1` for the completion.

**`markov:lem:completion`.**
* `shadowAt_completion`: the residue form of `markov:eq:completion-convex`. For every Hahn row
  Laplacian `H`, real probability row `ν`, `J = 𝟙ν` and positive `s, ε`,
  `res R_L(s) = (res(s/(s + ε))I + res(ε/(s + ε))J) res R_H(s + ε)` for `L = H + ε(I - J)`.
* `shadow_completion_of_final`: if the shadow of `H` is `𝟙π₀` at every scale `≥ β`, then `L`
  with `ε = t^β` has the same shadow as `H` at every scale and every `c > 0`.
  `shadow_completion` is the source's form: final shadow `𝟙π₀` above `α_m` and `β > α_m`. As in
  the source, below `β` the first factor has residue `I` and `s + ε` has the leading term of `s`
  (`MarkovShadow.shadowAt_mono_mul_one_add` replaces the leading-forest argument); from `β` on,
  both shadows are `𝟙π₀` and `J𝟙π₀ = 𝟙π₀`.
* `shadow_flagGen_completion`: the case of the flag generator, where `P_m = 𝟙π₀` is derived from
  `rank P_m = 1` by `exists_eq_onesRow_of_rank_eq_one` (through `markov:lem:splitting`).
  `completion_mulVec_one` and `flagGen_completion_offDiag_neg`: the completion is a row
  Laplacian with strictly negative off-diagonal entries.

The clause of `markov:lem:completion` for the `H` of `markov:thm:general-realization` is
`shadow_completion` applied to that `H`, once it is constructed; that theorem is pending.

**`markov:lem:initial-spectrum`.** Over any field `K`, for a finite family `λ_r ∈ K⟦Γ⟧` and
`D = ∏_r (X + λ_r)`, with `m_α` the weighted Gauss valuation `weightedGaussVal 0 α D` and `D_α`
the initial polynomial `gaussInitial 0 α D` at center zero (the Newton profile of
`markov:rem:newton`):
* `weightedGaussVal_prod_X_add_C`: `markov:eq:sum-min`, `m_α = ∑_r min(α, v(λ_r))`.
* `gaussInitial_prod_X_add_C`: `markov:eq:initial-factorization`,
  `D_α = C_α X^{#{v(λ_r) > α}} ∏_{v(λ_r) = α}(X + ρ_r)`, where `C_α` is the product of the
  leading coefficients of the `λ_r` with `v(λ_r) < α` and `ρ_r` is the coefficient of `t^α` in
  `λ_r`, that is `res(t^{-α}λ_r)` (`coeff_single_neg_mul`). `C_α ≠ 0` and `ρ_r ≠ 0`
  (`prod_leadingCoeff_ne_zero`, `coeff_ne_zero_of_orderTop_eq`).
* `newtonBreakpoint_prod_X_add_C_iff`: at least two indices are active at `α` exactly when some
  `λ_r` has valuation `α`, including `α = 0`.
* `weightedGaussVal_zero_eq_inf` and `coeff_gaussInitial_zero`: for any nonzero polynomial,
  `m_α = min_j (v(D_j) + jα)` and `D_α = ∑_{j active} lc(D_j)X^j`. With `D_j = σ_{d-j}` these
  are the source's `markov:eq:m-alpha` and `markov:eq:initial-polynomials` as soon as
  `v(σ_k) = h_k` and `lc(σ_k) = b_k`.

* `exists_prod_X_add_C_of_monic`: when `K` is algebraically closed of characteristic zero and `Γ`
  is divisible, `K⟦Γ⟧` is algebraically closed (`Surreal.HahnSeries.hahnIsAlgClosed`), so every
  monic `D` of degree `d` is `∏_{r < d} (X + λ_r)` and the results above apply to it.

Pending for `markov:lem:initial-spectrum`: identifying such a `D` with `det(sI + L)/s` for an
actual rate matrix `L` (after mapping `L` from `Lex ℝ⟦Γ⟧` to `ℂ⟦Γ⟧`), and the identification of
the forest data `h_k`, `b_k` with `v(σ_k)`, `lc(σ_k)` (`markov:eq:profile-properties`). The lemma
is proved for every explicitly factored `D`, with no assumption that `λ_r ≠ 0`.
-/

namespace Surreal.FlagShadows

open Matrix Finset Filter Topology
open scoped _root_.HahnSeries
open Surreal.MarkovShadow (mono res shadowAt shadow)
open Surreal.MarkovForest (rowLaplacian)

noncomputable section

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

section Scalar

/-- The real constants `r ↦ rt^0` of `ℝ((t^Γ))`, as a ring homomorphism. -/
def constHom : ℝ →+* Lex ℝ⟦Γ⟧ where
  toFun r := mono 0 r
  map_zero' := congrArg toLex (_root_.HahnSeries.C (Γ := Γ) (R := ℝ)).map_zero
  map_one' := rfl
  map_add' x y := congrArg toLex ((_root_.HahnSeries.C (Γ := Γ) (R := ℝ)).map_add x y)
  map_mul' x y := congrArg toLex ((_root_.HahnSeries.C (Γ := Γ) (R := ℝ)).map_mul x y)

theorem constHom_apply (r : ℝ) : constHom (Γ := Γ) r = mono 0 r :=
  rfl

theorem res_constHom (r : ℝ) : res (constHom (Γ := Γ) r) = r := by
  rw [constHom_apply, MarkovShadow.res_apply, MarkovShadow.ofLex_mono,
    _root_.HahnSeries.coeff_single_same]

theorem res_mul_constHom (x : Lex ℝ⟦Γ⟧) (r : ℝ) : res (x * constHom r) = res x * r := by
  rw [mul_comm, constHom_apply, MarkovShadow.res_mono_zero_mul, mul_comm]

theorem orderTop_constHom_nonneg (r : ℝ) : 0 ≤ (ofLex (constHom (Γ := Γ) r)).orderTop := by
  rw [constHom_apply, MarkovShadow.ofLex_mono]
  exact _root_.HahnSeries.orderTop_single_le

theorem constHom_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ constHom (Γ := Γ) r := by
  rcases hr.lt_or_eq with h | h
  · exact (MarkovShadow.mono_pos h).le
  · rw [← h, map_zero]

theorem constHom_pos {r : ℝ} (hr : 0 < r) : 0 < constHom (Γ := Γ) r :=
  MarkovShadow.mono_pos hr

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
theorem mono_add_mono (α : Γ) (a b : ℝ) : mono α a + mono α b = mono α (a + b) := by
  show toLex (_root_.HahnSeries.single α a + _root_.HahnSeries.single α b) =
    toLex (_root_.HahnSeries.single α (a + b))
  rw [_root_.HahnSeries.single_add]

omit [IsOrderedAddMonoid Γ] in
theorem orderTop_mono_pos {α : Γ} {c : ℝ} (hc : c ≠ 0) (hα : 0 < α) :
    0 < (ofLex (mono α c)).orderTop := by
  rw [MarkovShadow.orderTop_mono hc]
  exact WithTop.coe_pos.mpr hα

/-- For `α < β`, the monomial `t^β` is smaller than `t^α`. -/
theorem mono_one_lt_mono_one {α β : Γ} (h : α < β) : mono β (1 : ℝ) < mono α 1 := by
  have hε : (ofLex (1 : Lex ℝ⟦Γ⟧)).orderTop < (ofLex (mono (β - α) (1 : ℝ))).orderTop := by
    rw [ofLex_one, _root_.HahnSeries.orderTop_one, MarkovShadow.orderTop_mono one_ne_zero]
    exact WithTop.coe_pos.mpr (sub_pos.mpr h)
  have h1 := _root_.HahnSeries.abs_lt_abs_of_orderTop_ofLex hε
  rw [abs_one, abs_of_pos (MarkovShadow.mono_pos one_pos)] at h1
  have hsplit : mono β (1 : ℝ) = mono (β - α) 1 * mono α 1 := by
    rw [MarkovShadow.mono_mul_mono, sub_add_cancel, one_mul]
  rw [hsplit]
  exact mul_lt_of_lt_one_left (MarkovShadow.mono_pos one_pos) h1

/-- For positive `x, y`, the ratio `x/(x + y)` lies in `[0, 1]`, hence in `𝒪`. -/
theorem orderTop_div_add_nonneg {x y : Lex ℝ⟦Γ⟧} (hx : 0 < x) (hy : 0 < y) :
    0 ≤ (ofLex (x / (x + y))).orderTop :=
  MarkovForest.orderTop_nonneg_of_nonneg_of_le_one (div_nonneg hx.le (add_pos hx hy).le)
    ((div_le_one (add_pos hx hy)).mpr (le_add_of_nonneg_right hy.le))

/-- If `x` is infinitesimal relative to `y`, then `res(x/(x + y)) = 0`. -/
theorem res_div_add_eq_zero {x y ε : Lex ℝ⟦Γ⟧} (hx : 0 < x) (hy : 0 < y)
    (hε : 0 < (ofLex ε).orderTop) (h : x = ε * y) : res (x / (x + y)) = 0 := by
  have hb : 0 ≤ (ofLex (y / (x + y))).orderTop := by
    rw [add_comm]
    exact orderTop_div_add_nonneg hy hx
  have heq : x / (x + y) = ε * (y / (x + y)) := by
    rw [← mul_div_assoc, ← h]
  rw [heq]
  exact MarkovShadow.res_mul_eq_zero hε hb

/-- If `y` is infinitesimal relative to `x`, then `res(x/(x + y)) = 1`. -/
theorem res_div_add_eq_one {x y ε : Lex ℝ⟦Γ⟧} (hx : 0 < x) (hy : 0 < y)
    (hε : 0 < (ofLex ε).orderTop) (h : y = ε * x) : res (x / (x + y)) = 1 := by
  have hxy : x + y ≠ 0 := (add_pos hx hy).ne'
  have heq : x / (x + y) = 1 - y / (y + x) := by
    rw [add_comm y x, eq_sub_iff_add_eq, ← add_div, div_self hxy]
  rw [heq, map_sub, MarkovShadow.res_one, res_div_add_eq_zero hy hx hε h, sub_zero]

/-- The scalar residues in the proof of `markov:thm:flag-realization`: for real `c, a > 0`,
`res(ct^γ/(ct^γ + at^α))` is `1` for `γ < α`, `0` for `α < γ` and `c/(c + a)` for `γ = α`. -/
theorem res_mono_div_mono_add (γ α : Γ) {c a : ℝ} (hc : 0 < c) (ha : 0 < a) :
    res (mono γ c / (mono γ c + mono α a)) =
      if γ < α then 1 else if α < γ then 0 else c / (c + a) := by
  split_ifs with h1 h2
  · refine res_div_add_eq_one (MarkovShadow.mono_pos hc) (MarkovShadow.mono_pos ha)
      (ε := mono (α - γ) (a / c)) (orderTop_mono_pos (div_pos ha hc).ne' (sub_pos.mpr h1)) ?_
    rw [MarkovShadow.mono_mul_mono, sub_add_cancel, div_mul_cancel₀ a hc.ne']
  · refine res_div_add_eq_zero (MarkovShadow.mono_pos hc) (MarkovShadow.mono_pos ha)
      (ε := mono (γ - α) (c / a)) (orderTop_mono_pos (div_pos hc ha).ne' (sub_pos.mpr h2)) ?_
    rw [MarkovShadow.mono_mul_mono, sub_add_cancel, div_mul_cancel₀ c ha.ne']
  · have hγ : γ = α := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
    have hca : c + a ≠ 0 := (add_pos hc ha).ne'
    have hsplit : mono α c = mono 0 (c / (c + a)) * mono α (c + a) := by
      rw [MarkovShadow.mono_mul_mono, zero_add, div_mul_cancel₀ c hca]
    rw [hγ, mono_add_mono, hsplit, mul_div_assoc, div_self (MarkovShadow.mono_ne_zero hca),
      mul_one]
    exact res_constHom _

end Scalar

section Flag

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A real flag lifted entrywise into `ℝ((t^Γ))`. -/
def liftFlag (P : ℕ → Matrix n n ℝ) (j : ℕ) : Matrix n n (Lex ℝ⟦Γ⟧) :=
  (constHom (Γ := Γ)).mapMatrix (P j)

theorem resMap_constHom (A : Matrix n n ℝ) :
    res.mapMatrix ((constHom (Γ := Γ)).mapMatrix A) = A := by
  ext i j
  exact res_constHom (A i j)

theorem resMap_smul_constHom (x : Lex ℝ⟦Γ⟧) (A : Matrix n n ℝ) :
    res.mapMatrix (x • (constHom (Γ := Γ)).mapMatrix A) = res x • A := by
  ext i j
  exact res_mul_constHom x (A i j)

theorem orderTop_smul_constHom_nonneg {x : Lex ℝ⟦Γ⟧} (hx : 0 ≤ (ofLex x).orderTop)
    (A : Matrix n n ℝ) (i j : n) :
    0 ≤ (ofLex ((x • (constHom (Γ := Γ)).mapMatrix A) i j)).orderTop :=
  MarkovShadow.orderTop_mul_nonneg hx (orderTop_constHom_nonneg (A i j))

theorem constHom_mapMatrix_onesRow (ν : n → ℝ) :
    (constHom (Γ := Γ)).mapMatrix (Markov.onesRow ν) =
      Markov.onesRow fun b => constHom (ν b) := by
  ext
  rfl

variable {P : ℕ → Matrix n n ℝ} {m : ℕ}

theorem isFlag_liftFlag (hP : Markov.IsFlag P m) : Markov.IsFlag (liftFlag (Γ := Γ) P) m := by
  refine ⟨?_, fun i j hi hj => ?_⟩
  · show (constHom (Γ := Γ)).mapMatrix (P 0) = 1
    rw [hP.1, map_one]
  · show (constHom (Γ := Γ)).mapMatrix (P i) * (constHom (Γ := Γ)).mapMatrix (P j) =
      (constHom (Γ := Γ)).mapMatrix (P (max i j))
    rw [← map_mul, hP.2 i j hi hj]

theorem flagStep_liftFlag (P : ℕ → Matrix n n ℝ) (j : ℕ) :
    Markov.flagStep (liftFlag (Γ := Γ) P) j =
      (constHom (Γ := Γ)).mapMatrix (Markov.flagStep P j) := by
  simp only [Markov.flagStep, liftFlag, map_sub]

/-- The residue of `markov:eq:simple-inverse-resolvent`: for any `τ` and any `s ≠ 0` with
`s + τ_j ≠ 0`, `res R_H(s) = P_m + ∑_j res(s/(s + τ_j))E_j`. -/
theorem shadowAt_flagGenerator (hP : Markov.IsFlag P m) (τ : ℕ → Lex ℝ⟦Γ⟧) {s : Lex ℝ⟦Γ⟧}
    (hs : s ≠ 0) (hτ : ∀ j < m, s + τ j ≠ 0) :
    shadowAt (Markov.flagGenerator (liftFlag P) τ m) s =
      P m + ∑ j ∈ range m, res (s / (s + τ j)) • Markov.flagStep P j := by
  rw [MarkovShadow.shadowAt, Markov.resolvent_flagGenerator τ (isFlag_liftFlag hP) hs hτ,
    Markov.flagResolvent, map_add, map_sum, liftFlag, resMap_constHom]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [flagStep_liftFlag]
  exact resMap_smul_constHom _ _

/-- `markov:eq:simple-inverse`: the flag generator `H = ∑_j t^{α_j}(P_{j-1} - P_j)` of a real
flag, with the Lean index shift `α j = α_{j+1}`. -/
def flagGen (P : ℕ → Matrix n n ℝ) (α : ℕ → Γ) (m : ℕ) : Matrix n n (Lex ℝ⟦Γ⟧) :=
  Markov.flagGenerator (liftFlag P) (fun j => mono (α j) 1) m

/-- The shadow of the flag generator at every scale: `K_γ(c) = P_m + ∑_j r_j E_j` with
`r_j = 1, 0, c/(c + 1)` for `γ < α_j`, `γ > α_j`, `γ = α_j`. -/
theorem shadow_flagGen (hP : Markov.IsFlag P m) (α : ℕ → Γ) (γ : Γ) {c : ℝ} (hc : 0 < c) :
    shadow (flagGen P α m) γ c = P m + ∑ j ∈ range m,
      (if γ < α j then (1 : ℝ) else if α j < γ then 0 else c / (c + 1)) •
        Markov.flagStep P j := by
  have hs := MarkovShadow.mono_pos (α := γ) hc
  rw [MarkovShadow.shadow, flagGen, shadowAt_flagGenerator hP _ hs.ne'
    (fun j _ => (add_pos hs (MarkovShadow.mono_pos one_pos)).ne')]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [res_mono_div_mono_add γ (α j) hc one_pos]

omit [Fintype n] [DecidableEq n] in
/-- Telescoping the tail of the flag increments: `∑_{k ≤ j < m} E_j = P_k - P_m`. -/
theorem sum_tail_flagStep (P : ℕ → Matrix n n ℝ) {k m : ℕ} (hkm : k ≤ m) :
    ∑ j ∈ range m, (if k ≤ j then Markov.flagStep P j else 0) = P k - P m := by
  induction m, hkm using Nat.le_induction with
  | base =>
    rw [Finset.sum_eq_zero fun j hj => if_neg (by simp only [mem_range] at hj; omega), sub_self]
  | succ m hkm ih =>
    rw [Finset.sum_range_succ, ih, if_pos hkm, Markov.flagStep]
    abel

variable {α : ℕ → Γ}

/-- `markov:thm:flag-realization`, plateaux: if `α j < γ` for `j < k` (the source's
`α_1, …, α_k`) and `γ < α j` for `k ≤ j < m`, then `K_γ(c) = P_k` for every `c > 0`. No
monotonicity of the scales is needed. -/
theorem shadow_flagGen_plateau (hP : Markov.IsFlag P m) {γ : Γ} {k : ℕ} (hkm : k ≤ m)
    (hlow : ∀ j < k, α j < γ) (hhigh : ∀ j, k ≤ j → j < m → γ < α j) {c : ℝ} (hc : 0 < c) :
    shadow (flagGen P α m) γ c = P k := by
  rw [shadow_flagGen hP α γ hc]
  have h : ∀ j ∈ range m, (if γ < α j then (1 : ℝ) else if α j < γ then 0 else c / (c + 1)) •
      Markov.flagStep P j = if k ≤ j then Markov.flagStep P j else 0 := by
    intro j hj
    by_cases hkj : k ≤ j
    · rw [if_pos (hhigh j hkj (mem_range.mp hj)), if_pos hkj, one_smul]
    · have hj' := hlow j (by omega)
      rw [if_neg (not_lt.mpr hj'.le), if_pos hj', if_neg hkj, zero_smul]
  rw [Finset.sum_congr rfl h, sum_tail_flagStep P hkm]
  abel

/-- The initial plateau: below every `α_j` the shadow is `I`. -/
theorem shadow_flagGen_initial (hP : Markov.IsFlag P m) {γ : Γ} (hγ : ∀ j < m, γ < α j) {c : ℝ}
    (hc : 0 < c) : shadow (flagGen P α m) γ c = 1 := by
  rw [shadow_flagGen_plateau hP (Nat.zero_le m) (fun j hj => absurd hj (Nat.not_lt_zero j))
    (fun j _ hj => hγ j hj) hc, hP.1]

/-- The final plateau: above every `α_j` the shadow is `P_m`. -/
theorem shadow_flagGen_final (hP : Markov.IsFlag P m) {γ : Γ} (hγ : ∀ j < m, α j < γ) {c : ℝ}
    (hc : 0 < c) : shadow (flagGen P α m) γ c = P m :=
  shadow_flagGen_plateau hP le_rfl hγ (fun _ hj hj' => absurd hj' (not_lt.mpr hj)) hc

/-- The intermediate plateaux: strictly between `α k` and `α (k + 1)` (the source's `α_{k+1}`
and `α_{k+2}`) the shadow is `P_{k+1}`. -/
theorem shadow_flagGen_between (hP : Markov.IsFlag P m)
    (hα : ∀ i j, i < j → j < m → α i < α j) {k : ℕ} (hk : k + 1 < m) {γ : Γ}
    (h1 : α k < γ) (h2 : γ < α (k + 1)) {c : ℝ} (hc : 0 < c) :
    shadow (flagGen P α m) γ c = P (k + 1) := by
  refine shadow_flagGen_plateau hP hk.le (fun j hj => ?_) (fun j hj hj' => ?_) hc
  · rcases (Nat.lt_succ_iff.mp hj).lt_or_eq with h | h
    · exact (hα j k h (by omega)).trans h1
    · rw [h]
      exact h1
  · rcases hj.lt_or_eq with h | h
    · exact h2.trans (hα (k + 1) j h hj')
    · rw [← h]
      exact h2

/-- `markov:eq:simple-inverse-shadow`: at the crossover scale `α k` (the source's `α_{k+1}`),
`K_{α_k}(c) = P_{k+1} + c/(c + 1)(P_k - P_{k+1})` for every real `c > 0`. -/
theorem shadow_flagGen_crossover (hP : Markov.IsFlag P m)
    (hα : ∀ i j, i < j → j < m → α i < α j) {k : ℕ} (hk : k < m) {c : ℝ} (hc : 0 < c) :
    shadow (flagGen P α m) (α k) c = P (k + 1) + (c / (c + 1)) • (P k - P (k + 1)) := by
  rw [shadow_flagGen hP α (α k) hc]
  have h : ∀ j ∈ range m,
      (if α k < α j then (1 : ℝ) else if α j < α k then 0 else c / (c + 1)) •
        Markov.flagStep P j =
      (if j = k then (c / (c + 1)) • Markov.flagStep P j else 0) +
        (if k + 1 ≤ j then Markov.flagStep P j else 0) := by
    intro j hj
    rcases lt_trichotomy j k with hjk | hjk | hjk
    · have h' := hα j k hjk hk
      rw [if_neg (not_lt.mpr h'.le), if_pos h', if_neg hjk.ne, if_neg (by omega), zero_smul,
        add_zero]
    · rw [hjk, if_neg (lt_irrefl _), if_neg (lt_irrefl _), if_pos rfl, if_neg (by omega),
        add_zero]
    · have h' := hα k j hjk (mem_range.mp hj)
      rw [if_pos h', if_neg hjk.ne', if_pos (by omega), one_smul, zero_add]
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_ite_eq' (range m) k,
    if_pos (mem_range.mpr hk), sum_tail_flagStep P (by omega : k + 1 ≤ m), Markov.flagStep]
  abel

/-- The crossover at `α k` tends to the preceding plateau `P_k` as `c → ∞`. -/
theorem tendsto_shadow_flagGen_atTop (hP : Markov.IsFlag P m)
    (hα : ∀ i j, i < j → j < m → α i < α j) {k : ℕ} (hk : k < m) :
    Tendsto (shadow (flagGen P α m) (α k)) atTop (𝓝 (P k)) := by
  have hE : ∀ c : ℝ, 0 < c →
      shadow (flagGen P α m) (α k) c = P k - (c + 1)⁻¹ • (P k - P (k + 1)) := by
    intro c hc
    have hc1 : c + 1 ≠ 0 := (by linarith : (0 : ℝ) < c + 1).ne'
    have hdiv : c / (c + 1) = 1 - (c + 1)⁻¹ := by
      rw [eq_sub_iff_add_eq, inv_eq_one_div, ← add_div, div_self hc1]
    rw [shadow_flagGen_crossover hP hα hk hc, hdiv, sub_smul, one_smul]
    abel
  have h0 : Tendsto (fun c : ℝ => (c + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_id)
  have hlim := (tendsto_const_nhds : Tendsto (fun _ : ℝ => P k) atTop (𝓝 (P k))).sub
    (h0.smul_const (P k - P (k + 1)))
  rw [zero_smul, sub_zero] at hlim
  exact hlim.congr' (by filter_upwards [eventually_gt_atTop 0] with c hc using (hE c hc).symm)

/-- The crossover at `α k` tends to the following plateau `P_{k+1}` as `c → 0⁺`. -/
theorem tendsto_shadow_flagGen_zero (hP : Markov.IsFlag P m)
    (hα : ∀ i j, i < j → j < m → α i < α j) {k : ℕ} (hk : k < m) :
    Tendsto (shadow (flagGen P α m) (α k)) (𝓝[>] 0) (𝓝 (P (k + 1))) := by
  have h0 : Tendsto (fun c : ℝ => c / (c + 1)) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun c : ℝ => c / (c + 1)) 0 :=
      continuousAt_id.div (continuousAt_id.add continuousAt_const) (by norm_num)
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hlim := (tendsto_const_nhds : Tendsto (fun _ : ℝ => P (k + 1)) (𝓝[>] 0)
    (𝓝 (P (k + 1)))).add (h0.smul_const (P k - P (k + 1)))
  rw [zero_smul, add_zero] at hlim
  exact hlim.congr' (by
    filter_upwards [self_mem_nhdsWithin] with c hc
    exact (shadow_flagGen_crossover hP hα hk hc).symm)

/-- `markov:thm:flag-realization`, nontriviality: when `P_k ≠ P_{k+1}`, the crossover at `α k`
takes different values at different `c > 0`. -/
theorem shadow_flagGen_injective (hP : Markov.IsFlag P m)
    (hα : ∀ i j, i < j → j < m → α i < α j) {k : ℕ} (hk : k < m) (hne : P k ≠ P (k + 1))
    {c e : ℝ} (hc : 0 < c) (he : 0 < e)
    (h : shadow (flagGen P α m) (α k) c = shadow (flagGen P α m) (α k) e) : c = e := by
  rw [shadow_flagGen_crossover hP hα hk hc, shadow_flagGen_crossover hP hα hk he,
    add_right_inj, ← sub_eq_zero, ← sub_smul, smul_eq_zero] at h
  rcases h with h | h
  · rw [sub_eq_zero, div_eq_div_iff (by linarith : (0 : ℝ) < c + 1).ne'
      (by linarith : (0 : ℝ) < e + 1).ne'] at h
    linear_combination h
  · exact absurd (sub_eq_zero.mp h) hne

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
/-- For strictly increasing scales, a scale that is none of the `α_j` lies in one plateau
interval. -/
theorem exists_plateau_index {γ : Γ} :
    ∀ {m : ℕ}, (∀ i j, i < j → j < m → α i < α j) → (∀ j < m, α j ≠ γ) →
      ∃ k ≤ m, (∀ j < k, α j < γ) ∧ ∀ j, k ≤ j → j < m → γ < α j
  | 0, _, _ => ⟨0, le_rfl, fun j hj => absurd hj (Nat.not_lt_zero j),
      fun _ _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | m + 1, hα, hγ => by
    obtain ⟨k, hkm, hlow, hhigh⟩ := exists_plateau_index (m := m)
      (fun i j hij hj => hα i j hij (by omega)) (fun j hj => hγ j (by omega))
    by_cases hk : k < m
    · refine ⟨k, by omega, hlow, fun j hkj hj => ?_⟩
      by_cases hjm : j < m
      · exact hhigh j hkj hjm
      · rw [show j = m by omega]
        exact (hhigh k le_rfl hk).trans (hα k m hk (by omega))
    · rcases lt_or_gt_of_ne (hγ m (by omega)) with h | h
      · refine ⟨m + 1, le_rfl, fun j hj => ?_, fun j hj hj' => by omega⟩
        by_cases hjm : j < m
        · exact hlow j (by omega)
        · rw [show j = m by omega]
          exact h
      · refine ⟨m, by omega, fun j hj => hlow j (by omega), fun j hj hj' => ?_⟩
        rw [show j = m by omega]
        exact h

/-- `markov:thm:flag-realization`, plateau values: for strictly increasing scales, a scale `γ`
that is none of the `α_j` has shadow `K_γ(c) = P_k` for some `k ≤ m` and every `c > 0`. -/
theorem exists_shadow_flagGen_eq_of_ne (hP : Markov.IsFlag P m)
    (hα : ∀ i j, i < j → j < m → α i < α j) {γ : Γ} (hγ : ∀ j < m, α j ≠ γ) :
    ∃ k ≤ m, ∀ c : ℝ, 0 < c → shadow (flagGen P α m) γ c = P k := by
  obtain ⟨k, hkm, hlow, hhigh⟩ := exists_plateau_index hα hγ
  exact ⟨k, hkm, fun c hc => shadow_flagGen_plateau hP hkm hlow hhigh hc⟩

/-- `markov:thm:flag-realization`, attainment of the plateaux: if `Γ` is nontrivial and densely
ordered (as the source's nonzero divisible `Γ` is) and the scales are strictly increasing, then
for every `k ≤ m` some scale `γ` has `K_γ(c) = P_k` for every `c > 0`. -/
theorem exists_shadow_flagGen_eq [Nontrivial Γ] [DenselyOrdered Γ] (hP : Markov.IsFlag P m)
    (hα : ∀ i j, i < j → j < m → α i < α j) {k : ℕ} (hkm : k ≤ m) :
    ∃ γ : Γ, ∀ c : ℝ, 0 < c → shadow (flagGen P α m) γ c = P k := by
  have hmono : ∀ i j, i ≤ j → j < m → α i ≤ α j := fun i j hij hj =>
    hij.lt_or_eq.elim (fun h => (hα i j h hj).le) (fun h => (congrArg α h).le)
  obtain ⟨γ, hlo, hhi⟩ : ∃ γ : Γ, (k = 0 ∨ α (k - 1) < γ) ∧ (k = m ∨ γ < α k) := by
    rcases Nat.eq_zero_or_pos k with h0 | h0 <;> rcases hkm.lt_or_eq with hm | hm
    · obtain ⟨γ, hγ⟩ := exists_lt (α k)
      exact ⟨γ, Or.inl h0, Or.inr hγ⟩
    · exact ⟨0, Or.inl h0, Or.inl hm⟩
    · obtain ⟨γ, h1, h2⟩ := exists_between (hα (k - 1) k (by omega) hm)
      exact ⟨γ, Or.inr h1, Or.inr h2⟩
    · obtain ⟨γ, hγ⟩ := exists_gt (α (k - 1))
      exact ⟨γ, Or.inr hγ, Or.inl hm⟩
  refine ⟨γ, fun c hc => shadow_flagGen_plateau hP hkm (fun j hj => ?_) (fun j hkj hj => ?_) hc⟩
  · rcases hlo with h | h
    · omega
    · exact (hmono j (k - 1) (by omega) (by omega)).trans_lt h
  · rcases hhi with h | h
    · omega
    · exact h.trans_le (hmono k j hkj hj)

/-- `markov:thm:flag-realization`: for a flag of distinct matrices and strictly increasing
scales, the shadow at `γ` is independent of `c > 0` exactly when `γ` is none of the `α_j`.
Hence the crossovers are exactly the prescribed scales; at every other scale the shadow is one
of the `P_k` (`exists_shadow_flagGen_eq_of_ne`). -/
theorem shadow_flagGen_const_iff (hP : Markov.IsFlag P m)
    (hα : ∀ i j, i < j → j < m → α i < α j) (hdist : ∀ j < m, P j ≠ P (j + 1)) (γ : Γ) :
    (∀ c e : ℝ, 0 < c → 0 < e → shadow (flagGen P α m) γ c = shadow (flagGen P α m) γ e) ↔
      ∀ j < m, α j ≠ γ := by
  constructor
  · intro hconst j hj hjγ
    rw [← hjγ] at hconst
    have h12 := shadow_flagGen_injective hP hα hj (hdist j hj) one_pos two_pos
      (hconst 1 2 one_pos two_pos)
    norm_num at h12
  · intro hγ c e hc he
    obtain ⟨k, hkm, hlow, hhigh⟩ := exists_plateau_index hα hγ
    rw [shadow_flagGen_plateau hP hkm hlow hhigh hc, shadow_flagGen_plateau hP hkm hlow hhigh he]

/-- `markov:thm:flag-realization`: a stochastic flag gives a generator with zero row sums. -/
theorem flagGen_mulVec_one (hstoch : ∀ j ≤ m, P j ∈ rowStochastic ℝ n) :
    flagGen P α m *ᵥ (fun _ => (1 : Lex ℝ⟦Γ⟧)) = 0 := by
  rw [flagGen]
  refine Markov.flagGenerator_mulVec_one _ fun j hj => ?_
  ext a
  have h := (mem_rowStochastic_iff_sum.mp (hstoch j hj)).2 a
  simp only [mulVec, dotProduct, mul_one, liftFlag, RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [← map_sum, h, map_one]

/-- `markov:thm:flag-realization`: for a nonnegative flag and increasing scales, the generator
has nonpositive off-diagonal entries (`markov:eq:inverse-signs`). -/
theorem flagGen_offDiag_nonpos (hP : Markov.IsFlag P m) (hnonneg : ∀ j ≤ m, ∀ a b, 0 ≤ P j a b)
    (hα : ∀ i j, i < j → j < m → α i < α j) {a b : n} (hab : a ≠ b) :
    flagGen P α m a b ≤ 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [flagGen, Markov.flagGenerator]
  · exact Markov.flagGenerator_offDiag_nonpos _ (isFlag_liftFlag hP) hm
      (fun j hj a b => constHom_nonneg (hnonneg j hj a b))
      (fun j hj => mono_one_lt_mono_one (hα j (j + 1) (Nat.lt_succ_self j) hj))
      (MarkovShadow.mono_pos one_pos) hab

end Flag

section Completion

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem onesRow_mul_onesRow_of_sum {ν π : n → ℝ} (hν : ∑ b, ν b = 1) :
    Markov.onesRow ν * Markov.onesRow π = Markov.onesRow π := by
  ext a b
  simp [Markov.onesRow, Matrix.mul_apply, ← Finset.sum_mul, hν]

/-- A rank-one row-stochastic idempotent has identical probability rows: `P = 𝟙π₀`. -/
theorem exists_eq_onesRow_of_rank_eq_one {P : Matrix n n ℝ} (hP : P ∈ rowStochastic ℝ n)
    (hPP : P * P = P) (hr : P.rank = 1) :
    ∃ π₀ : n → ℝ, (∀ b, 0 ≤ π₀ b) ∧ ∑ b, π₀ b = 1 ∧ P = Markov.onesRow π₀ := by
  obtain ⟨U, V, -, hV0, hU1, hV1, hUV, -⟩ := StochasticIdempotent.exists_splitting hP hPP
  obtain ⟨a0, hall⟩ : ∃ a0 : Fin P.rank, ∀ a, a = a0 :=
    ⟨⟨0, by omega⟩, fun a => Fin.ext (show (a : ℕ) = 0 by have := a.isLt; omega)⟩
  refine ⟨V a0, hV0 a0, hV1 a0, ?_⟩
  ext i j
  have hU : U i a0 = 1 := by
    rw [← hU1 i, Fintype.sum_eq_single a0 fun a ha => absurd (hall a) ha]
  show P i j = V a0 j
  rw [congrFun (congrFun hUV i) j, Matrix.mul_apply,
    Fintype.sum_eq_single a0 fun a ha => absurd (hall a) ha, hU, one_mul]

variable {H : Matrix n n (Lex ℝ⟦Γ⟧)}

/-- The completed generator `L = H + ε(I - 𝟙ν)` still has zero row sums. -/
theorem completion_mulVec_one (hH1 : H *ᵥ (fun _ => 1) = 0) {ν : n → ℝ} (hν : ∑ b, ν b = 1)
    (ε : Lex ℝ⟦Γ⟧) :
    (H + ε • (1 - Markov.onesRow fun b => constHom (ν b))) *ᵥ (fun _ => 1) = 0 := by
  have hJ : (Markov.onesRow fun b => constHom (Γ := Γ) (ν b)) *ᵥ (fun _ => 1) = fun _ => 1 := by
    ext a
    simp only [mulVec, dotProduct, Markov.onesRow, of_apply, mul_one]
    rw [← map_sum, hν, map_one]
  have hε : (ε • (1 - Markov.onesRow fun b => constHom (Γ := Γ) (ν b))) *ᵥ (fun _ => 1) =
      ε • ((1 - Markov.onesRow fun b => constHom (Γ := Γ) (ν b)) *ᵥ (fun _ => 1)) := by
    ext a
    show ∑ b, ε * (1 - Markov.onesRow fun b => constHom (Γ := Γ) (ν b)) a b * 1 =
      ε * ∑ b, (1 - Markov.onesRow fun b => constHom (Γ := Γ) (ν b)) a b * 1
    rw [Finset.mul_sum]
    simp only [mul_assoc]
  rw [add_mulVec, hε, sub_mulVec, one_mulVec, hJ, hH1, sub_self]
  ext a
  show (0 : Lex ℝ⟦Γ⟧) + ε * 0 = 0
  rw [mul_zero, add_zero]

/-- The residue form of `markov:eq:completion-convex`: for a Hahn row Laplacian `H`, a real
probability row `ν`, `J = 𝟙ν`, `L = H + ε(I - J)` and positive `s, ε`,
`res R_L(s) = (res(s/(s + ε))I + res(ε/(s + ε))J) res R_H(s + ε)`. -/
theorem shadowAt_completion (hH1 : H *ᵥ (fun _ => 1) = 0) (hH : ∀ a b, a ≠ b → H a b ≤ 0)
    {ν : n → ℝ} (hν : ∑ b, ν b = 1) {s ε : Lex ℝ⟦Γ⟧} (hs : 0 < s) (hε : 0 < ε) :
    shadowAt (H + ε • (1 - Markov.onesRow fun b => constHom (ν b))) s =
      (res (s / (s + ε)) • (1 : Matrix n n ℝ) + res (ε / (s + ε)) • Markov.onesRow ν) *
        shadowAt H (s + ε) := by
  have hq : ∀ i j, i ≠ j → 0 ≤ -H i j := fun i j h => neg_nonneg.mpr (hH i j h)
  have hHq : rowLaplacian (fun i j => -H i j) = H := MarkovShadow.rowLaplacian_neg hH1
  have hsε : 0 < s + ε := add_pos hs hε
  have hν' : ∑ b, constHom (Γ := Γ) (ν b) = 1 := by rw [← map_sum, hν, map_one]
  have hM : IsUnit ((s + ε) • (1 : Matrix n n (Lex ℝ⟦Γ⟧)) + H).det := by
    rw [← hHq]
    exact MarkovShadow.isUnit_det hq hsε
  have hA : (s / (s + ε)) • (1 : Matrix n n (Lex ℝ⟦Γ⟧)) +
      (ε / (s + ε)) • Markov.onesRow (fun b => constHom (ν b)) =
      (s / (s + ε)) • (constHom (Γ := Γ)).mapMatrix 1 +
        (ε / (s + ε)) • (constHom (Γ := Γ)).mapMatrix (Markov.onesRow ν) := by
    rw [map_one, constHom_mapMatrix_onesRow]
  have hAbd : ∀ i j, 0 ≤ (ofLex (((s / (s + ε)) • (constHom (Γ := Γ)).mapMatrix
      (1 : Matrix n n ℝ) + (ε / (s + ε)) • (constHom (Γ := Γ)).mapMatrix (Markov.onesRow ν) :
        Matrix n n (Lex ℝ⟦Γ⟧)) i j)).orderTop :=
    fun i j => (le_min (orderTop_smul_constHom_nonneg (orderTop_div_add_nonneg hs hε) _ i j)
      (orderTop_smul_constHom_nonneg (by rw [add_comm]; exact orderTop_div_add_nonneg hε hs)
        _ i j)).trans _root_.HahnSeries.min_orderTop_le_orderTop_add
  have hRbd : ∀ i j, 0 ≤ (ofLex (Markov.resolvent H (s + ε) i j)).orderTop := by
    rw [← hHq]
    exact MarkovShadow.orderTop_resolvent_nonneg hq hsε
  have hR : Markov.resolvent (H + ε • (1 - Markov.onesRow fun b => constHom (ν b))) s =
      ((s / (s + ε)) • (constHom (Γ := Γ)).mapMatrix (1 : Matrix n n ℝ) +
        (ε / (s + ε)) • (constHom (Γ := Γ)).mapMatrix (Markov.onesRow ν)) *
        Markov.resolvent H (s + ε) := by
    rw [← hA]
    exact Markov.resolvent_completion hH1 hν' hs.ne' hsε.ne' hM
  rw [MarkovShadow.shadowAt, hR, MarkovShadow.resMap_mul hAbd hRbd, map_add,
    resMap_smul_constHom, resMap_smul_constHom]
  rfl

/-- `markov:lem:completion`, shadow invariance: let `H` be a Hahn row Laplacian whose shadow is
`𝟙π₀` at every scale `γ ≥ β` and every `c > 0`, and let `ν` be a real probability row. Then
`L = H + t^β(I - 𝟙ν)` has the same shadow as `H` at every scale and every `c > 0`. -/
theorem shadow_completion_of_final (hH1 : H *ᵥ (fun _ => 1) = 0)
    (hH : ∀ a b, a ≠ b → H a b ≤ 0) {ν : n → ℝ} (hν : ∑ b, ν b = 1) {β : Γ} {π₀ : n → ℝ}
    (hfinal : ∀ γ, β ≤ γ → ∀ c : ℝ, 0 < c → shadow H γ c = Markov.onesRow π₀) (γ : Γ) {c : ℝ}
    (hc : 0 < c) :
    shadow (H + mono β 1 • (1 - Markov.onesRow fun b => constHom (ν b))) γ c = shadow H γ c := by
  have hq : ∀ i j, i ≠ j → 0 ≤ -H i j := fun i j h => neg_nonneg.mpr (hH i j h)
  have hHq : rowLaplacian (fun i j => -H i j) = H := MarkovShadow.rowLaplacian_neg hH1
  have hs : 0 < mono γ c := MarkovShadow.mono_pos hc
  have hε : 0 < mono β (1 : ℝ) := MarkovShadow.mono_pos one_pos
  have hsum : res (mono γ c / (mono γ c + mono β 1)) +
      res (mono β (1 : ℝ) / (mono γ c + mono β 1)) = 1 := by
    rw [← map_add, ← add_div, div_self (add_pos hs hε).ne', MarkovShadow.res_one]
  rw [MarkovShadow.shadow, shadowAt_completion hH1 hH hν hs hε]
  rcases lt_or_ge γ β with hγβ | hγβ
  · have h1 : res (mono γ c / (mono γ c + mono β 1)) = 1 := by
      rw [res_mono_div_mono_add γ β hc one_pos, if_pos hγβ]
    have h0 : res (mono β (1 : ℝ) / (mono γ c + mono β 1)) = 0 := by linarith
    have hη : 0 < (ofLex (mono (β - γ) c⁻¹)).orderTop :=
      orderTop_mono_pos (inv_ne_zero hc.ne') (sub_pos.mpr hγβ)
    have hsplit : mono γ c + mono β (1 : ℝ) = mono γ c * (1 + mono (β - γ) c⁻¹) := by
      rw [mul_add, mul_one, MarkovShadow.mono_mul_mono, add_sub_cancel, mul_inv_cancel₀ hc.ne']
    rw [h1, h0, one_smul, zero_smul, add_zero, Matrix.one_mul, hsplit, ← hHq]
    exact MarkovShadow.shadowAt_mono_mul_one_add hq hc hη
  · obtain ⟨a, ha, hsa⟩ : ∃ a : ℝ, 0 < a ∧
        shadowAt H (mono γ c + mono β 1) = shadow H β a := by
      rcases hγβ.lt_or_eq with hlt | heq
      · refine ⟨1, one_pos, ?_⟩
        have hη : 0 < (ofLex (mono (γ - β) c)).orderTop :=
          orderTop_mono_pos hc.ne' (sub_pos.mpr hlt)
        have hsplit : mono γ c + mono β (1 : ℝ) = mono β 1 * (1 + mono (γ - β) c) := by
          rw [mul_add, mul_one, MarkovShadow.mono_mul_mono, add_sub_cancel, one_mul, add_comm]
        rw [hsplit, ← hHq]
        exact MarkovShadow.shadowAt_mono_mul_one_add hq one_pos hη
      · refine ⟨c + 1, by linarith, ?_⟩
        have hsplit : mono γ c + mono β (1 : ℝ) = mono β (c + 1) * (1 + 0) := by
          rw [add_zero, mul_one, ← heq, mono_add_mono]
        have h0 : 0 < (ofLex (0 : Lex ℝ⟦Γ⟧)).orderTop := by
          rw [ofLex_zero, _root_.HahnSeries.orderTop_zero]
          exact WithTop.coe_lt_top 0
        rw [hsplit, ← hHq]
        exact MarkovShadow.shadowAt_mono_mul_one_add hq (by linarith) h0
    rw [hsa, hfinal β le_rfl a ha, hfinal γ hγβ c hc, Matrix.add_mul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.one_mul, onesRow_mul_onesRow_of_sum hν, ← add_smul, hsum,
      one_smul]

/-- `markov:lem:completion` in the source's form: if the Hahn row Laplacian `H` has final
shadow `𝟙π₀` at all scales strictly above `α_m`, and `β > α_m`, then `L = H + t^β(I - 𝟙ν)` has
the same shadow as `H` at every scale and every `c > 0`. -/
theorem shadow_completion (hH1 : H *ᵥ (fun _ => 1) = 0) (hH : ∀ a b, a ≠ b → H a b ≤ 0)
    {ν : n → ℝ} (hν : ∑ b, ν b = 1) {αm β : Γ} (hβ : αm < β) {π₀ : n → ℝ}
    (hfinal : ∀ γ, αm < γ → ∀ c : ℝ, 0 < c → shadow H γ c = Markov.onesRow π₀) (γ : Γ) {c : ℝ}
    (hc : 0 < c) :
    shadow (H + mono β 1 • (1 - Markov.onesRow fun b => constHom (ν b))) γ c = shadow H γ c :=
  shadow_completion_of_final hH1 hH hν (fun γ hγ c hc => hfinal γ (hβ.trans_le hγ) c hc) γ hc

variable {P : ℕ → Matrix n n ℝ} {m : ℕ} {α : ℕ → Γ}

/-- `markov:lem:completion` for the flag generator of `markov:thm:flag-realization`: for a
stochastic flag with `rank P_m = 1`, increasing scales, `β` above every `α_j` and a real
probability row `ν`, the completion `H + t^β(I - 𝟙ν)` has the same shadow as `H` at every
scale and every `c > 0`. -/
theorem shadow_flagGen_completion (hP : Markov.IsFlag P m)
    (hstoch : ∀ j ≤ m, P j ∈ rowStochastic ℝ n) (hα : ∀ i j, i < j → j < m → α i < α j)
    (hrank : (P m).rank = 1) {β : Γ} (hβ : ∀ j < m, α j < β) {ν : n → ℝ} (hν : ∑ b, ν b = 1)
    (γ : Γ) {c : ℝ} (hc : 0 < c) :
    shadow (flagGen P α m + mono β 1 • (1 - Markov.onesRow fun b => constHom (ν b))) γ c =
      shadow (flagGen P α m) γ c := by
  obtain ⟨π₀, -, -, hπ⟩ := exists_eq_onesRow_of_rank_eq_one (hstoch m le_rfl)
    (by rw [hP.2 m m le_rfl le_rfl, max_self]) hrank
  refine shadow_completion_of_final (π₀ := π₀) (flagGen_mulVec_one hstoch)
    (fun a b hab => flagGen_offDiag_nonpos hP
      (fun j hj => (mem_rowStochastic_iff_sum.mp (hstoch j hj)).1) hα hab) hν
    (fun γ' hγ' c' hc' => ?_) γ hc
  rw [shadow_flagGen_final hP (fun j hj => (hβ j hj).trans_le hγ') hc', hπ]

/-- `markov:lem:completion` for the flag generator: with a strictly positive `ν`, every
off-diagonal entry of the completion is strictly negative. -/
theorem flagGen_completion_offDiag_neg (hP : Markov.IsFlag P m)
    (hstoch : ∀ j ≤ m, P j ∈ rowStochastic ℝ n) (hα : ∀ i j, i < j → j < m → α i < α j)
    (β : Γ) {ν : n → ℝ} (hνpos : ∀ b, 0 < ν b) {a b : n} (hab : a ≠ b) :
    (flagGen P α m + mono β 1 • (1 - Markov.onesRow fun b => constHom (ν b)) :
      Matrix n n (Lex ℝ⟦Γ⟧)) a b < 0 :=
  Markov.completion_offDiag_neg (MarkovShadow.mono_pos one_pos) (fun b => constHom_pos (hνpos b))
    (fun _ _ hab => flagGen_offDiag_nonpos hP
      (fun j hj => (mem_rowStochastic_iff_sum.mp (hstoch j hj)).1) hα hab) hab

end Completion

section InitialSpectrum

open Polynomial

variable {K : Type*} [Field K] {ι : Type*}

/-- The normalized residue `res(t^{-α}x)` is the coefficient of `t^α` in `x`. -/
theorem coeff_single_neg_mul (α : Γ) (x : K⟦Γ⟧) :
    (_root_.HahnSeries.single (-α) (1 : K) * x).coeff 0 = x.coeff α := by
  rw [_root_.HahnSeries.coeff_single_mul, zero_sub, neg_neg, one_mul]

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
theorem coeff_ne_zero_of_orderTop_eq {x : K⟦Γ⟧} {α : Γ} (h : x.orderTop = α) :
    x.coeff α ≠ 0 :=
  _root_.HahnSeries.coeff_orderTop_ne h

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
/-- The constant `C_α` of `markov:eq:initial-factorization` is nonzero. -/
theorem prod_leadingCoeff_ne_zero (α : Γ) (s : Finset ι) (ev : ι → K⟦Γ⟧) :
    ∏ r ∈ s.filter (fun r => (ev r).orderTop < α), (ev r).leadingCoeff ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro r hr
  refine _root_.HahnSeries.leadingCoeff_ne_zero.mpr fun h0 => ?_
  have h := (Finset.mem_filter.mp hr).2
  rw [h0, _root_.HahnSeries.orderTop_zero] at h
  exact not_top_lt h

/-- The initial factor of `X + x` at center zero and weight `α`: a nonzero constant, `X`, or
`X + ρ` according as `v(x) < α`, `v(x) > α` or `v(x) = α`. -/
theorem gaussInitial_X_add_C (α : Γ) (x : K⟦Γ⟧) :
    Surreal.HahnSeries.gaussInitial 0 α (X + C x) =
      if x.orderTop < α then C x.leadingCoeff
      else if (α : WithTop Γ) < x.orderTop then X else X + C (x.coeff α) := by
  have hX : (X + C x : K⟦Γ⟧[X]) = X - C (-x) := by rw [map_neg, sub_neg_eq_add]
  rw [hX]
  split_ifs with h1 h2
  · rw [Surreal.HahnSeries.gaussInitial_X_sub_C_of_lt 0 α (-x)
      (by rwa [sub_zero, _root_.HahnSeries.orderTop_neg]), sub_zero,
      _root_.HahnSeries.leadingCoeff_neg, neg_neg]
  · rw [Surreal.HahnSeries.gaussInitial_X_sub_C_of_le 0 α (-x)
      (by rw [sub_zero, _root_.HahnSeries.orderTop_neg]; exact h2.le), sub_zero,
      _root_.HahnSeries.coeff_neg, _root_.HahnSeries.coeff_eq_zero_of_lt_orderTop h2, neg_zero,
      map_zero, sub_zero]
  · have h3 : x.orderTop = α := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
    rw [Surreal.HahnSeries.gaussInitial_X_sub_C_of_le 0 α (-x)
      (by rw [sub_zero, _root_.HahnSeries.orderTop_neg, h3]), sub_zero,
      _root_.HahnSeries.coeff_neg, map_neg, sub_neg_eq_add]

/-- `markov:eq:sum-min`: the Newton profile at center zero of `D = ∏_r (X + λ_r)` is
`m_α = ∑_r min(α, v(λ_r))`. -/
theorem weightedGaussVal_prod_X_add_C (α : Γ) (s : Finset ι) (ev : ι → K⟦Γ⟧) :
    Surreal.HahnSeries.weightedGaussVal 0 α (∏ r ∈ s, (X + C (ev r))) =
      ∑ r ∈ s, min (α : WithTop Γ) (ev r).orderTop := by
  rw [Surreal.HahnSeries.weightedGaussVal_prod]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hX : (X + C (ev r) : K⟦Γ⟧[X]) = X - C (-ev r) := by rw [map_neg, sub_neg_eq_add]
  rw [hX, Surreal.HahnSeries.weightedGaussVal_X_sub_C, sub_zero, _root_.HahnSeries.orderTop_neg]

/-- `markov:eq:initial-factorization`: the initial polynomial at center zero of
`D = ∏_r (X + λ_r)` is `C_α X^{#{v(λ_r) > α}} ∏_{v(λ_r) = α}(X + ρ_r)`, with `C_α` the product of
the leading coefficients of the `λ_r` with `v(λ_r) < α` and `ρ_r` the coefficient of `t^α` in
`λ_r`. -/
theorem gaussInitial_prod_X_add_C (α : Γ) (s : Finset ι) (ev : ι → K⟦Γ⟧) :
    Surreal.HahnSeries.gaussInitial 0 α (∏ r ∈ s, (X + C (ev r))) =
      C (∏ r ∈ s.filter (fun r => (ev r).orderTop < α), (ev r).leadingCoeff) *
        X ^ (s.filter fun r => (α : WithTop Γ) < (ev r).orderTop).card *
        ∏ r ∈ s.filter (fun r => (ev r).orderTop = α), (X + C ((ev r).coeff α)) := by
  have hA : (s.filter fun r => ¬(ev r).orderTop < α).filter
      (fun r => (α : WithTop Γ) < (ev r).orderTop) =
      s.filter fun r => (α : WithTop Γ) < (ev r).orderTop := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr fun r _ => ⟨fun h => h.2, fun h => ⟨not_lt.mpr h.le, h⟩⟩
  have hB : (s.filter fun r => ¬(ev r).orderTop < α).filter
      (fun r => ¬(α : WithTop Γ) < (ev r).orderTop) =
      s.filter fun r => (ev r).orderTop = α := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr fun r _ =>
      ⟨fun h => le_antisymm (not_lt.mp h.2) (not_lt.mp h.1),
        fun h => ⟨by rw [h]; exact lt_irrefl _, by rw [h]; exact lt_irrefl _⟩⟩
  rw [Surreal.HahnSeries.gaussInitial_prod,
    Finset.prod_congr rfl fun r _ => gaussInitial_X_add_C α (ev r), Finset.prod_ite,
    Finset.prod_ite, hA, hB, Finset.prod_const, map_prod, mul_assoc]

/-- `markov:lem:initial-spectrum`, criticality: at least two indices are active at `α` for
`D = ∏_r (X + λ_r)` exactly when some `λ_r` has valuation `α`. -/
theorem newtonBreakpoint_prod_X_add_C_iff (α : Γ) (s : Finset ι) (ev : ι → K⟦Γ⟧) :
    Surreal.HahnSeries.newtonBreakpoint (∏ r ∈ s, (X + C (ev r))) α ↔
      ∃ r ∈ s, (ev r).orderTop = α := by
  have hD : (∏ r ∈ s, (X + C (ev r)) : K⟦Γ⟧[X]) ≠ 0 :=
    (monic_prod_of_monic _ _ fun r _ => monic_X_add_C (ev r)).ne_zero
  have hprod : (C 1 * ∏ r ∈ s, (X - C (-ev r)) : K⟦Γ⟧[X]) = ∏ r ∈ s, (X + C (ev r)) := by
    rw [map_one, one_mul]
    exact Finset.prod_congr rfl fun r _ => by rw [map_neg, sub_neg_eq_add]
  have h := Surreal.HahnSeries.shell_count_gaussInitial_split 0 α 1 one_ne_zero s
    (fun r => -ev r)
  rw [hprod] at h
  rw [← Surreal.HahnSeries.newtonSpan_pos_iff_breakpoint _ hD, Surreal.HahnSeries.newtonSpan,
    ← h, Finset.card_pos, Finset.filter_nonempty_iff]
  simp only [sub_zero, _root_.HahnSeries.orderTop_neg]

/-- At center zero, the Newton profile of any polynomial is `min_j (v(D_j) + jα)`. -/
theorem weightedGaussVal_zero_eq_inf (α : Γ) (P : K⟦Γ⟧[X]) :
    Surreal.HahnSeries.weightedGaussVal 0 α P =
      P.support.inf fun j => (P.coeff j).orderTop + ((j • α : Γ) : WithTop Γ) := by
  simpa only [taylor_zero] using Surreal.HahnSeries.weightedGaussVal_eq_inf 0 α P

/-- At center zero, the initial polynomial of a nonzero polynomial has coefficient `lc(D_j)` at
every active index `j` and zero elsewhere: `D_α = ∑_{j active} lc(D_j)X^j`. -/
theorem coeff_gaussInitial_zero (α : Γ) {P : K⟦Γ⟧[X]} (hP : P ≠ 0) (j : ℕ) :
    (Surreal.HahnSeries.gaussInitial 0 α P).coeff j =
      if (P.coeff j).orderTop + ((j • α : Γ) : WithTop Γ) =
          Surreal.HahnSeries.weightedGaussVal 0 α P
        then (P.coeff j).leadingCoeff else 0 := by
  split_ifs with h
  · have hE : Surreal.HahnSeries.centeredGaussExpansion 0 α P ≠ 0 :=
      (map_ne_zero_iff _ (Surreal.HahnSeries.centeredGaussExpansion_injective 0 α)).mpr hP
    have hc : P.coeff j ≠ 0 := by
      intro h0
      rw [h0, _root_.HahnSeries.orderTop_zero, WithTop.top_add, eq_comm,
        Surreal.HahnSeries.weightedGaussVal_eq_top_iff] at h
      exact hP h
    have ho : (Surreal.HahnSeries.centeredGaussExpansion 0 α P).order =
        (P.coeff j).order + j • α := by
      apply WithTop.coe_injective
      rw [_root_.HahnSeries.order_eq_orderTop_of_ne_zero hE, WithTop.coe_add,
        _root_.HahnSeries.order_eq_orderTop_of_ne_zero hc, h,
        Surreal.HahnSeries.weightedGaussVal_apply]
    rw [Surreal.HahnSeries.coeff_gaussInitial, taylor_zero, ho, add_sub_cancel_right,
      _root_.HahnSeries.leadingCoeff_eq]
  · by_contra hne
    have h' := (Surreal.HahnSeries.coeff_gaussInitial_ne_zero_iff 0 α P hP j).mp hne
    rw [taylor_zero] at h'
    exact h h'

/-- The factorization hypothesis of `markov:lem:initial-spectrum` at the polynomial level: when
`K` is algebraically closed of characteristic zero and `Γ` is divisible, `K⟦Γ⟧` is algebraically
closed (`Surreal.HahnSeries.hahnIsAlgClosed`), so every monic `D` of degree `d` is
`∏_{r < d} (X + λ_r)`; the `-λ_r` are the roots of `D` counted with multiplicity. -/
theorem exists_prod_X_add_C_of_monic [CharZero K] [IsAlgClosed K] [DivisibleBy Γ ℕ]
    {D : K⟦Γ⟧[X]} (hD : D.Monic) :
    ∃ (d : ℕ) (ev : Fin d → K⟦Γ⟧), d = D.natDegree ∧ D = ∏ r, (X + C (ev r)) := by
  refine ⟨D.roots.toList.length, fun r => -D.roots.toList[r.1], ?_, ?_⟩
  · rw [Multiset.length_toList, IsAlgClosed.card_roots_eq_natDegree]
  · have hf : (fun a : K⟦Γ⟧ => X + C (-a)) = fun a => X - C a :=
      funext fun a => by rw [map_neg, sub_eq_add_neg]
    rw [Fin.prod_univ_fun_getElem D.roots.toList (fun a => X + C (-a)), hf,
      Multiset.prod_map_toList, prod_multiset_X_sub_C_of_monic_of_roots_card_eq hD
        IsAlgClosed.card_roots_eq_natDegree]

end InitialSpectrum

end

end Surreal.FlagShadows
