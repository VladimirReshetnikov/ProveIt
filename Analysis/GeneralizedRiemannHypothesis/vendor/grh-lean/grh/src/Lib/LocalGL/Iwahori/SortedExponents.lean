import Lib.LocalGL.Iwahori.QuadraticRelation
import Lib.LocalGL.Shintani.LiftingGreenCharacters

/-!
# Sorted exponents at pro-p Iwahori level

Let `ρ` be a smooth representation of `GL_N(F)`, where `F` has compact ring of integers and a
uniformiser `ϖ` with `v ϖ = exp (-1)`. An exponent is sorted when the absolute values `‖θ i ϖ‖` of
its characters do not increase. This file shows that the characters of an exponent that is nonzero
on a suitable pro-p Iwahori fixed vector (see `New.IsExponent.exists_sorted`) can be reordered so
that it is sorted, and that for unitary `ρ` an eigenvector in a span of translates with
finite-dimensional pro-p Iwahori fixed part gives an exponent. Let `ρ` be unitary, and let the
vectors fixed by `New.proIwahori` in the span of the translates of any vector form a
finite-dimensional space. For such `ρ`, this file constructs eigenvectors with sorted characters. It
does so from a vector of parahoric type and from a vector with a nonzero projection along characters
of determinants.

## Main definitions and results

* `New.IsExponent.exists_sorted`: the characters of an exponent nonzero on a pro-p Iwahori fixed
  `τ`-eigenvector `x` of the integral torus, which permutations preserving `τ` scale, can be
  reordered so that the absolute values `‖θ i ϖ‖` do not increase.
* `New.IsIwahoriEigen.exists_isExponent`: in the unitary case an eigenvector in a span of translates
  with finite-dimensional pro-p Iwahori fixed part gives an exponent.
* `New.exists_sorted_isIwahoriEigen_of_diagGL_smul`, `New.exists_sorted_of_detChar`: eigenvectors
  with sorted characters, from a vector of parahoric type and from a vector with a nonzero
  projection along characters of determinants.

Notions from other files:
* `New.proIwahori`: The pro-p Iwahori subgroup I₁ of GL_n(𝒪): matrices that are upper triangular
  with ones on the diagonal modulo the maximal ideal.
* `New.dominantTorus`: Dominant elements of the diagonal torus: the `t` with `v (t i) ≤ v (t j)` for
  `i ≤ j`.
* `New.IsExponent`: `l (ρ(t) (mean of x over proIwahori)) = ξ(t) l(x)` for all dominant diagonal `t`
  and all `x`.
* `New.IsIwahoriEigen`: x is a nonzero vector fixed by the pro-p Iwahori subgroup I₁ with
  `U_t x = ξ(t) x` for all dominant t, where `U_t` is `ρ(t)` followed by the mean over I₁.
* `New.torusChar`: For characters θ_i of Fˣ, the character t ↦ ∏ θ_i(t_i) |t_i|^(N-1-i) of the
  diagonal torus.

## Relation to the literature

Known; see `Lib.LocalGL.Iwahori.SphericalExponents` for sources.
-/

/-!
## Sorting exponents, and sorted exponents from a parahoric type

The vector `x` is fixed by `New.proIwahori`, and the integral torus acts on it by `τ`. Every
permutation matrix whose permutation preserves the values of `τ` on units at each index acts on `x`
by a scalar. By the roots of an exponent for `torusChar θ` we mean the values `θ i ϖ`.

* `New.IsExponent.exists_sorted`: an exponent that is nonzero at `x` can be moved, along a
  permutation, to one whose roots `θ i ϖ` do not increase in absolute value.
* `New.IsIwahoriEigen.exists_isExponent`: for unitary `ρ`, an eigenvector of the operators
  `iwahoriHeckeHom ρ t` gives an exponent.
* `New.exists_sorted_isIwahoriEigen_of_diagGL_smul`: let `ρ` be unitary, and let the
  `New.proIwahori`-invariants in the span of the translates of `x` have finite dimension. Then a
  nonzero such `x` gives an exponent, and an eigenvector for a reordering of its characters sorted
  by the absolute values `‖θ i ϖ‖`.
-/

section SortedExponents

open Matrix WithZero Valued Equiv Module Units Pi Submodule ComplexOrder Submonoid.LocalizationMap
  Filter.Germ

namespace New

variable {F : Type*} [Field F] [Valued F ℤᵐ⁰] {N : ℕ}
  {ρ : Rep ℂ (GL (Fin N) F)} [IsSmoothRep ρ.ρ]
  {ϖ : Fˣ} {θ : Fin N → Fˣ →* ℂˣ} {l : ρ →ₗ[ℂ] ℂ} {x : ρ} {τ : (Fin N → Fˣ) → ℂ}

/-- If `j` is the successor of `i` in `Fin n`, then `i.rev` is the successor of `j.rev`. -/
theorem _root_.Fin.rev_val_eq_rev_val_add_one_of_covBy {n : ℕ} {i j : Fin n} (h : i ⋖ j) :
    i.rev.val = j.rev.val + 1 := by
  have h_succ : i.val + 1 = j.val := Nat.covBy_iff_add_one_eq.mp (Fin.covBy_iff.mp h)
  rw [Fin.val_rev, Fin.val_rev]
  omega

/-- Exchanging two neighbouring components of `θ` in `torusChar θ` amounts to exchanging the entries
of the argument, up to the factor `normAbsChar (t i / t j)`. Here `normAbsChar` is the absolute
value `|·|` whose powers occur in `torusChar θ t = ∏ i, θ i (t i) * |t i| ^ (N - 1 - i)`. -/
lemma torusChar_comp_swap [CompactSpace 𝒪[F]]
    (θ : Fin N → Fˣ →* ℂˣ) {i j : Fin N} (hcov : i ⋖ j) (t : Fin N → Fˣ) :
    torusChar (θ ∘ Equiv.swap i j) t =
      torusChar θ (t ∘ Equiv.swap i j) * normAbsChar (t i / t j) := by
  have hrev : i.rev.val = j.rev.val + 1 := Fin.rev_val_eq_rev_val_add_one_of_covBy hcov
  -- Both sides are characters of `t`, so it is enough to compare them on each `mulSingle a u`.
  -- The powers of `normAbsChar` in `torusChar` at `i` and `j` differ by one (`hrev`).
  ext
  induction t using mulSingle_induction with
  | one => simp
  | mul f g hf hg => simp [mul_comp, field, hf, hg]
  | mulSingle a u =>
    simp [field, mulSingle_comp_equiv, mulSingle_apply]
    grind [val_one, hcov.ne]

/-- A transvection moves past a diagonal matrix with its entry rescaled; if the rescaled
transvection lies in `proIwahori`, it is absorbed by the mean. -/
lemma transvectionGL_apply_diagGL_compactMean [CompactSpace 𝒪[F]]
    {a b : Fin N} {t : Fin N → Fˣ} {c : F} {z : ρ} {h : a ≠ b}
    (hc : transvectionGL h ((t b).val / (t a).val * c) ∈ proIwahori) :
    ρ (transvectionGL h c) (ρ (diagGL t) (compactMean ρ.ρ proIwahori z)) =
      ρ (diagGL t) (compactMean ρ.ρ proIwahori z) := by
  have h_comm : transvectionGL h c * diagGL t = diagGL t * transvectionGL h (t b / t a * c) := by
    ext
    simp [transvection, Matrix.one_apply]
    grind [ne_zero]
  rw [← Module.End.mul_apply, ← map_mul ρ.ρ, h_comm]
  simp [hc]

/-- After the exchange of two neighbours `i`, `j`, an exponent still satisfies its defining
identity, for the exchanged character, at the dominant `t` with `t i / t j` of order at most `1`. -/
lemma IsExponent.apply_permGL_swap_diagGL_compactMean [CompactSpace 𝒪[F]] {ξ : (Fin N → Fˣ) →* ℂˣ}
    (hl : IsExponent ρ ξ l)
    (hϖ : v ϖ.val = exp (-1)) {i j : Fin N} (hcov : i ⋖ j) {t : Fin N → Fˣ} (ht : t ∈ dominantTorus)
    (ht₁ : log (v (t j / t i).val) ≤ 1) (z : ρ) :
    l (ρ (permGL (Equiv.swap i j)) (ρ (diagGL t) (compactMean ρ.ρ proIwahori z))) =
      ξ (t ∘ Equiv.swap i j) * l (ρ (permGL (Equiv.swap i j)) (compactMean ρ.ρ proIwahori z)) := by
  refine .trans ?_ (hl.apply_monomial_translate hϖ (compactMean_mem_levelSpace z)
    mem_proIwahori_iff_blockParahoric.mpr (swap i j) ?_)
  · -- `ρ (swap i j) ρ (diagGL t)` is `ρ (diagGL (t ∘ swap i j)) ρ (swap i j)`
    simp [diagGL_mul_permGL, Function.comp_def]
  · -- the order condition of `IsExponent.apply_monomial_translate` for `σ = swap i j`: only the
    -- pair `(i, j)` is reversed, and there the orders differ by at most one (`ht₁`)
    simp_all [dominantTorus, log_le_iff_le_exp, Monotone]
    grind

/-- The torus element with `ϖ` at the indices before `j` and `1` from `j` on. -/
private def stepTorus (ϖ : Fˣ) (j : Fin N) : Fin N → Fˣ := fun a ↦ if a < j then ϖ else 1

/-- For a uniformiser `ϖ`, `stepTorus ϖ j` is dominant: the order of its entries drops by one
from `j - 1` to `j` and nowhere else. -/
private lemma stepTorus_mem_dominantTorus (hϖ : v ϖ.val = exp (-1)) (j : Fin N) :
    stepTorus ϖ j ∈ dominantTorus := by
  simp +decide [dominantTorus, stepTorus, apply_ite, ite_apply, hϖ, Monotone]
  omega

omit [Valued F ℤᵐ⁰] in
/-- For `i < j`, exchanging the entries `i` and `j` of `stepTorus ϖ j` moves one factor `ϖ`
from the index `i` to the index `j`. -/
private lemma stepTorus_comp_swap {i j : Fin N} (hij : i < j) :
    stepTorus ϖ j ∘ Equiv.swap i j = stepTorus ϖ j * mulSingle j ϖ * mulSingle i ϖ⁻¹ := by
  ext
  simp [stepTorus, mulSingle_apply]
  grind

/-- Let `ϖ` be a uniformiser, `j = i + 1`, and `t` dominant with `v (t i) < v (t j)`. Then
`t / stepTorus ϖ j` is still dominant. -/
private lemma div_stepTorus_mem_dominantTorus (hϖ : v ϖ.val = exp (-1)) {i j : Fin N}
    (hcov : i ⋖ j) {t : Fin N → Fˣ} (ht : t ∈ dominantTorus) (h_lt : v (t i).val < v (t j).val) :
    t / stepTorus ϖ j ∈ dominantTorus := by
  -- In terms of the integers `log (v (t a))`: adding `1` to the entries before `j` keeps them
  -- monotone.
  simp [dominantTorus, stepTorus, ← log_le_log, ← log_lt_log, apply_ite, hϖ, Monotone]
    at ht h_lt hcov ⊢
  have h_from_j (b : Fin N) (hb : j ≤ b) : (v (t j).val).log ≤ (v (t b).val).log := ht hb
  have h_to_i (a : Fin N) (ha : a ≤ i) : (v (t a).val).log ≤ (v (t i).val).log := ht ha
  grind

variable [CompactSpace 𝒪[F]]

/-- Let `l` be an exponent and `j = i + 1`. On a vector `z` fixed by the transvections `1 + a E_ij`
with `a` integral, the form `l ∘ ρ (swap i j)` does not see the mean over `New.proIwahori`. -/
private lemma IsExponent.apply_permGL_swap_compactMean_of_forall_transvectionGL
    {ξ : (Fin N → Fˣ) →* ℂˣ} (hl : IsExponent ρ ξ l) {i j : Fin N} (hcov : i ⋖ j) {z : ρ}
    (hz : ∀ a : F, v a ≤ 1 → ρ (transvectionGL hcov.ne a) z = z) :
    l (ρ (permGL (Equiv.swap i j)) (compactMean ρ.ρ proIwahori z)) =
      l (ρ (permGL (Equiv.swap i j)) z) := by
  -- Each `k ∈ proIwahori` is, up to a transvection that fixes `z`, conjugated into
  -- `proIwahori` by the swap.
  refine map_compactMean_of_factor hl.apply_proIwahori fun k hk ↦ ?_
  obtain ⟨c, hc⟩ : ∃ c : 𝒪[F], MulAut.conj (permGL (Equiv.swap i j))
      (k * transvectionGL hcov.ne c.val) ∈ proIwahori := exists_swap_conj_mem_proIwahori hcov hk
  have h_fix : ρ ((k * transvectionGL hcov.ne c.val)⁻¹ * k) z = z := by
    simp [hz _ c.prop, Representation.inv_apply_eq_iff]
  exact ⟨_, hc, h_fix⟩

/-- The quadratic relation at the vector `U_w z`, for `w = stepTorus ϖ j` and `j = i + 1`. Here
`U_w` is the mean over `New.proIwahori` followed by `ρ (diagGL w)`, and `q` is the order of the
residue field. Let `l` be an exponent for `ξ` that takes the value `κ` at the translates of `U_w z`
by the diagonal `d` with `-u⁻¹` at `i`, `u` at `j` and `1` elsewhere, for units `u`. Then
`q l (s (mean of U_w z)) = ξ (w ∘ swap i j) l (s (mean of z)) + (q - 1) κ`, with `s = ρ (swap i j)`.
-/
private lemma IsExponent.quadratic_relation_stepTorus {ξ : (Fin N → Fˣ) →* ℂˣ}
    (hl : IsExponent ρ ξ l) (hϖ : v ϖ.val = exp (-1)) {i j : Fin N} (hcov : i ⋖ j) (z : ρ) (κ : ℂ)
    (hκ : ∀ u : Fˣ, v u.val = 1 → letI d := mulSingle i (-u⁻¹) * mulSingle j u
      (∀ a : Fin N, v (d a).val = 1) →
        l (ρ (diagGL d) (ρ (diagGL (stepTorus ϖ j)) (compactMean ρ.ρ proIwahori z))) = κ) :
    Nat.card 𝓀[F] • l (ρ (permGL (Equiv.swap i j)) (compactMean ρ.ρ proIwahori
        (ρ (diagGL (stepTorus ϖ j)) (compactMean ρ.ρ proIwahori z)))) =
      ξ (stepTorus ϖ j ∘ Equiv.swap i j) *
          l (ρ (permGL (Equiv.swap i j)) (compactMean ρ.ρ proIwahori z)) +
        (Nat.card 𝓀[F] - 1) • κ := by
  have hij : i < j := hcov.lt
  -- The order of `w i / w j` is `1`, so `IsExponent.apply_permGL_swap_diagGL_compactMean` turns the
  -- first term on the right into `l (s (U_w z))`.
  have h_order : log (v (stepTorus ϖ j j / stepTorus ϖ j i).val) ≤ 1 := by
    simp [stepTorus, hij, hϖ]
  rw [← hl.apply_permGL_swap_diagGL_compactMean hϖ hcov (stepTorus_mem_dominantTorus hϖ j) h_order
    z]
  -- The transvections `1 + c E_ji` with `c` integral fix `U_w z`.
  have h_fix (c : F) (hc : v c ≤ 1) :
      ρ (transvectionGL hcov.ne' c) (ρ (diagGL (stepTorus ϖ j)) (compactMean ρ.ρ proIwahori z)) =
        ρ (diagGL (stepTorus ϖ j)) (compactMean ρ.ρ proIwahori z) := by
    -- the rescaled entry is `ϖ c`, of valuation less than `1`
    have h_small : v ((stepTorus ϖ j i).val / (stepTorus ϖ j j).val * c) < 1 := by
      have h_lt : exp (-1 : ℤ) * v c < 1 :=
        (mul_le_of_le_one_right' hc).trans_lt (exp_lt_exp.2 neg_one_lt_zero)
      simpa [stepTorus, hij, hϖ] using h_lt
    exact transvectionGL_apply_diagGL_compactMean
      (transvectionGL_mem_proIwahori hcov.ne' (.inl h_small))
  exact quadratic_relation hcov κ hl.apply_proIwahori h_fix fun u hu ↦
    hκ u hu (v_mulSingle_neg_inv_mul_mulSingle_eq_one hu)

/-- Let `l` be an exponent for `torusChar θ`, let `j = i + 1` and let `z` lie in the kernel of
`l`. Then the form `l ∘ ρ (swap i j) ∘ (mean over New.proIwahori)` is an eigenform at `z` of
the operator `U_t` (the mean followed by `ρ (diagGL t)`) for dominant `t`, with the exchanged
character `torusChar (θ ∘ swap i j)`. -/
private lemma IsExponent.swap_compactMean_apply_diagGL_of_apply_eq_zero
    (hl : IsExponent ρ (torusChar θ) l) (hϖ : v ϖ.val = exp (-1)) {i j : Fin N} (hcov : i ⋖ j)
    {t : Fin N → Fˣ} (ht : t ∈ dominantTorus) {z : ρ} (hz : l z = 0) :
    l (ρ (permGL (Equiv.swap i j)) (compactMean ρ.ρ proIwahori
        (ρ (diagGL t) (compactMean ρ.ρ proIwahori z)))) =
      torusChar (θ ∘ Equiv.swap i j) t *
        l (ρ (permGL (Equiv.swap i j)) (compactMean ρ.ρ proIwahori z)) := by
  -- Induction on the order of `t i / t j`. At order `0` the mean drops out; each step splits off
  -- one factor `w = stepTorus ϖ j`, for which the quadratic relation gives the eigenvalue.
  have hij : i < j := hcov.lt
  let l_mean : ρ →ₗ[ℂ] ℂ := l ∘ₗ ρ (permGL (Equiv.swap i j)) ∘ₗ compactMean ρ.ρ proIwahori
  let U (t : Fin N → Fˣ) : Module.End ℂ ρ := ρ (diagGL t) * compactMean ρ.ρ proIwahori
  let w : Fin N → Fˣ := stepTorus ϖ j
  have hw : w ∈ dominantTorus := stepTorus_mem_dominantTorus hϖ j
  show l_mean (U t z) = torusChar (θ ∘ Equiv.swap i j) t * l_mean z
  induction h_gap : (v (t j / t i).val).log.toNat generalizing t z with
  | zero =>
    -- Order `0`: `t i` and `t j` have the same valuation, so the transvections at `(i, j)` fix
    -- `U_t z` and the mean drops out.
    have h_v_eq : v (t i).val = v (t j).val := by simpa [(ht hij.le).ge_iff_eq] using h_gap
    have h_fix (c : F) (hc : v c ≤ 1) : ρ (transvectionGL hcov.ne c) (U t z) = U t z :=
      transvectionGL_apply_diagGL_compactMean
        (by simp [h_v_eq, hc, hij, transvectionGL_mem_proIwahori])
    calc l_mean (U t z) = l (ρ (permGL (Equiv.swap i j)) (U t z)) :=
          hl.apply_permGL_swap_compactMean_of_forall_transvectionGL hcov h_fix
      _ = torusChar θ (t ∘ Equiv.swap i j) * l_mean z :=
          hl.apply_permGL_swap_diagGL_compactMean hϖ hcov ht (by simp [h_v_eq]) z
      _ = _ := by simp [torusChar_comp_swap θ hcov t, normAbsChar, h_v_eq]
  | succ m ih =>
    -- Split off one factor `w`: `t / w` is still dominant, and the order drops by one.
    have h_log : log (v (t j).val) - log (v (t i).val) = m + 1 := by
      rw [← log_div (by simp) (by simp), ← map_div₀, ← val_div_eq_div_val]
      omega
    have htw : t / w ∈ dominantTorus := div_stepTorus_mem_dominantTorus hϖ hcov ht <|
      (log_lt_log (by simp) (by simp)).mp (by omega)
    have h_gap' : (v ((t / w) j / (t / w) i).val).log.toNat = m := by
      simp [w, stepTorus, hϖ, hij]
      omega
    have hl_Uw : l (U w z) = 0 := by simp [U, hl hw, hz]
    have h_eig_w : l_mean (U w z) = torusChar (θ ∘ Equiv.swap i j) w * l_mean z := by
      -- the quadratic relation with `κ = 0`: `l` vanishes at the diagonal translates of `U_w z`
      have h_quad : Nat.card 𝓀[F] • l_mean (U w z) =
          torusChar θ (w ∘ Equiv.swap i j) * l_mean z + (Nat.card 𝓀[F] - 1) • 0 :=
        hl.quadratic_relation_stepTorus hϖ hcov z 0 fun u _ hd ↦
          (hl.apply_diagGL_unit hd (U w z)).trans (by rw [hl_Uw, mul_zero])
      simpa [torusChar_comp_swap θ hcov w, w, stepTorus, field, hϖ, hij, eq_div_iff, NeZero.ne,
        mul_comm, normAbsChar] using h_quad
    -- `U_t` is `U_{t / w}` after `U_w`
    calc l_mean (U t z) = l_mean (U (t / w) (U w z)) := by
          simp only [l_mean, U, LinearMap.comp_apply, Module.End.mul_apply, div_mul_cancel,
            compactMean_diagGL_compactMean_diagGL htw hw (compactMean_mem_levelSpace z)]
      _ = torusChar (θ ∘ Equiv.swap i j) (t / w) * l_mean (U w z) := ih htw hl_Uw h_gap'
      _ = torusChar (θ ∘ Equiv.swap i j) t * l_mean z := by simp [h_eig_w, field]

/-- Let `l` be an exponent for `ξ`, and let each integral diagonal matrix `diagGL t` act on `x` by
the scalar `τ t`. For an index `b`, a unit `ε` and a permutation `σ'`, either `ξ` at `mulSingle b ε`
equals `τ` at `mulSingle (σ' b) ε`, or `l` vanishes at `ρ (permGL σ'⁻¹) x`. -/
private lemma IsExponent.apply_mulSingle_eq_or_apply_permGL_inv_eq_zero
    {ξ : (Fin N → Fˣ) →* ℂˣ} (hl : IsExponent ρ ξ l)
    (hτ : ∀ t : Fin N → Fˣ, diagGL t ∈ intGL (Fin N) 𝒪[F] → ρ (diagGL t) x = τ t • x)
    (b : Fin N) {ε : Fˣ} (hε : v ε.val = 1) (σ' : Perm (Fin N)) :
    (ξ (mulSingle b ε) : ℂ) = τ (mulSingle (σ' b) ε) ∨ l (ρ (permGL σ'⁻¹) x) = 0 := by
  -- Move the diagonal unit past `permGL σ'⁻¹`; compare `IsExponent.apply_diagGL_unit` with `hτ`.
  have h_comm : l (ρ (diagGL (mulSingle b ε) * permGL σ'⁻¹) x) =
      l (ρ (permGL σ'⁻¹ * diagGL (mulSingle b ε ∘ ⇑σ'⁻¹)) x) := by rw [diagGL_mul_permGL]
  simpa [apply_ite, hl.apply_diagGL_unit, hε, hτ, mulSingle_apply, mulSingle_comp_equiv,
    diagGL_mem_intGL] using h_comm

/-- Let `l` be an exponent for `ξ`, let `j = i + 1`, let `x` be fixed by `New.proIwahori`, and put
`y = ρ (permGL (σ * swap i j)⁻¹) x`. If `l` vanishes at `y` but not at `ρ (swap i j) y`, then
`l ∘ ρ (swap i j)` does not vanish at the mean of `y` over `New.proIwahori`. -/
private lemma IsExponent.apply_permGL_swap_compactMean_ne_zero {ξ : (Fin N → Fˣ) →* ℂˣ}
    (hl : IsExponent ρ ξ l) (hx : x ∈ levelSpace ρ.ρ proIwahori) {σ : Perm (Fin N)}
    {i j : Fin N} (hcov : i ⋖ j) (hl_y : l (ρ (permGL (σ * Equiv.swap i j)⁻¹) x) = 0)
    (hl_swap_y : l (ρ (permGL (Equiv.swap i j)) (ρ (permGL (σ * Equiv.swap i j)⁻¹) x)) ≠ 0) :
    l (ρ (permGL (Equiv.swap i j))
      (compactMean ρ.ρ proIwahori (ρ (permGL (σ * Equiv.swap i j)⁻¹) x))) ≠ 0 := by
  -- If `σ * swap i j` keeps `i` before `j`, the transvections at `(i, j)` fix `y` and the mean
  -- drops out. Otherwise the quadratic relation, with `κ = 0` by `hl_y`, gives
  -- `q l (s (mean of y)) = l (s y)` with `s = ρ (swap i j)`.
  set y : ρ := ρ (permGL (σ * Equiv.swap i j)⁻¹) x
  obtain h_lt | h_gt := ((σ * Equiv.swap i j).injective.ne hcov.ne).lt_or_gt
  · rwa [hl.apply_permGL_swap_compactMean_of_forall_transvectionGL hcov
      (transvectionGL_apply_permGL_inv hx h_lt)]
  · have h_diag (u : Fˣ) (hu : v u.val = 1) :
        l (ρ (diagGL (mulSingle i (-u⁻¹) * mulSingle j u)) y) = 0 := by
      rw [hl.apply_diagGL_unit (v_mulSingle_neg_inv_mul_mulSingle_eq_one hu), hl_y, mul_zero]
    have h_quad : Nat.card 𝓀[F] • l (ρ (permGL (Equiv.swap i j)) (compactMean ρ.ρ proIwahori y)) =
        l (ρ (permGL (Equiv.swap i j)) y) + (Nat.card 𝓀[F] - 1) • (0 : ℂ) :=
      quadratic_relation hcov 0 hl.apply_proIwahori (transvectionGL_apply_permGL_inv hx h_gt) h_diag
    have h_rhs_ne : l (ρ (permGL (Equiv.swap i j)) y) + (Nat.card 𝓀[F] - 1) • (0 : ℂ) ≠ 0 := by
      simpa using hl_swap_y
    exact right_ne_zero_of_smul (h_quad.trans_ne h_rhs_ne)

attribute [-simp] WithZero.inv_exp
attribute [local simp] WithZero.exp_neg

/-- Sorting an exponent. Let `ϖ` be a uniformiser, let `x` be fixed by `New.proIwahori` (`hx`), let
the integral torus act on `x` by `τ` (`hτ`), and let every permutation matrix whose permutation
preserves `τ` on units act on `x` by a scalar (`hP`). Let `l` be an exponent for `torusChar θ` with
`l x ≠ 0`. Here an exponent (`IsExponent`) for `ξ` is a form with
`l (ρ t (mean of y over I₁)) = ξ t * l y` for dominant diagonal `t`, and `torusChar θ t = ∏ i, θ i
(t i) * |t i| ^ (N - 1 - i)`. Then there is a permutation `σ` such that (a) some exponent for
`torusChar (θ ∘ σ)` is nonzero at `ρ (permGL σ⁻¹) x`, and (b) `‖θ (σ i) ϖ‖` does not increase in
`i`.

A special case of the Bernstein–Zelevinsky results on cuspidal exponents: a torus exponent nonzero
on a pro-p-Iwahori-fixed vector with a type can be permuted so that |θ_i(ϖ)| is non-increasing. -/
lemma IsExponent.exists_sorted (hϖ : v ϖ.val = exp (-1)) (hx : x ∈ levelSpace ρ.ρ proIwahori)
    (hτ : ∀ t : Fin N → Fˣ, diagGL t ∈ intGL (Fin N) 𝒪[F] → ρ (diagGL t) x = τ t • x)
    (hP : ∀ σ : Perm (Fin N),
      (∀ (i : Fin N) (ε : Fˣ), v ε.val = 1 → τ (mulSingle i ε) = τ (mulSingle (σ i) ε)) →
      ∃ c : ℂ, ρ (permGL σ) x = c • x)
    (hl : IsExponent ρ (torusChar θ) l) (hlx : l x ≠ 0) :
    ∃ σ : Perm (Fin N),
      (∃ l : ρ →ₗ[ℂ] ℂ, IsExponent ρ (torusChar (θ ∘ σ)) l ∧ l (ρ (permGL σ⁻¹) x) ≠ 0) ∧
      Antitone ((fun i : Fin N ↦ ‖(θ i ϖ : ℂ)‖) ∘ σ) := by
  -- By bubble sort (`exists_antitone_of_swap`) it is enough to exchange two neighbours `i` and
  -- `j = i + 1` whose roots are out of order. Let `s` be `l` after the exchange and `S` its mean.
  -- On the kernel of `l`, `S` is an eigenform for the exchanged character, so `S ∘ (U w - ξ w)`
  -- is an exponent for it; were it zero at the permuted vector `y`, the roots would be in order.
  refine exists_antitone_of_swap _ _ ⟨1, l, hl, by simpa⟩ ?_
  rintro σ i j hcov hf ⟨l, hl, hl_ne⟩
  have hij : i < j := hcov.lt
  have hne : i ≠ j := hcov.ne
  have hrev : i.rev.val = j.rev.val + 1 := Fin.rev_val_eq_rev_val_add_one_of_covBy hcov
  let π : Perm (Fin N) := σ * swap i j
  set y : ρ := ρ (permGL π⁻¹) x
  set ξ : (Fin N → Fˣ) →* ℂˣ := torusChar (θ ∘ σ)
  have χ_eq (t : Fin N → Fˣ) : torusChar (θ ∘ π) t = ξ (t ∘ swap i j) * normAbsChar (t i / t j) :=
    torusChar_comp_swap (θ ∘ σ) hcov t
  let s : ρ →ₗ[ℂ] ℂ := l ∘ₗ ρ (permGL (swap i j))
  -- (`swap_inv` is kept out so that `(swap i j)⁻¹` cancels against `swap i j`)
  have hsy : s y ≠ 0 := by simpa [y, π, s, -swap_inv]
  let S : ρ →ₗ[ℂ] ℂ := s ∘ₗ compactMean ρ.ρ proIwahori
  -- `U t` takes the mean first and then applies `ρ (diagGL t)`, as in `IsExponent`
  let U (t : Fin N → Fˣ) : Module.End ℂ ρ := ρ (diagGL t) * compactMean ρ.ρ proIwahori
  -- the dominant element whose order drops by one from `i` to `j` and nowhere else
  let w : Fin N → Fˣ := stepTorus ϖ j
  have hw : w ∈ dominantTorus := stepTorus_mem_dominantTorus hϖ j
  have w_swap : w ∘ swap i j = w * mulSingle j ϖ * mulSingle i ϖ⁻¹ := stepTorus_comp_swap hij
  -- The mean drops out on vectors fixed by the transvections at `(i, j)`.
  have S_eq {z : ρ} (hz : ∀ a : F, v a ≤ 1 → ρ (transvectionGL hne a) z = z) : S z = s z :=
    hl.apply_permGL_swap_compactMean_of_forall_transvectionGL hcov hz
  -- On the kernel of `l`, `S` is an eigenform for `torusChar (θ ∘ π)`.
  have S_U (t : Fin N → Fˣ) (ht : t ∈ dominantTorus) (z : ρ) (hz : l z = 0) :
      S (U t z) = torusChar (θ ∘ π) t * S z :=
    hl.swap_compactMean_apply_diagGL_of_apply_eq_zero hϖ hcov ht hz
  let q : ℕ := Nat.card 𝓀[F]
  refine ⟨S ∘ₗ (U w - (ξ w : ℂ) • 1), fun d hd z ↦ ?_, fun h_zero ↦ ?_⟩
  · -- `U w - ξ w` maps every vector into the kernel of `l`
    have h_ker : l ((U w - (ξ w : ℂ) • 1) z) = 0 := by simp [U, hl hw]
    refine .trans ?_ (S_U d hd _ h_ker)
    simp [S, U, compactMean_diagGL_compactMean_diagGL, mul_comm, hd, hw]
  replace h_zero : S (U w y) = ξ w * S y := by simpa [sub_eq_zero] using h_zero
  -- The exchange of `σ i` and `σ j` preserves `τ` on units, so it acts on `x` by a scalar (`hP`):
  -- otherwise `l y = 0`, and the two roots would be equal.
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ρ (permGL (swap (σ i) (σ j))) x = c • x := by
    refine hP _ fun a ε hε ↦ by_contra fun hτ_ne ↦ ?_
    -- `ξ` agrees with `τ` moved along `σ`, as `l` is nonzero there, hence not along `π`
    have hξ : ξ (mulSingle (σ⁻¹ a) ε) = τ (mulSingle a ε) := by
      simpa using
        (hl.apply_mulSingle_eq_or_apply_permGL_inv_eq_zero hτ (σ⁻¹ a) hε σ).resolve_right hl_ne
    have hly : l y = 0 :=
      (hl.apply_mulSingle_eq_or_apply_permGL_inv_eq_zero hτ (σ⁻¹ a) hε π).resolve_left <| by
        rw [hξ]
        simpa [π, mul_swap_eq_swap_mul] using hτ_ne
    have hSy : S y ≠ 0 := hl.apply_permGL_swap_compactMean_ne_zero hx hcov hly hsy
    -- `S_U` and `h_zero` both evaluate `S (U w y)`
    have h_eq : (θ (σ j) ϖ : ℂ) = θ (σ i) ϖ := by
      -- (`Fin.val_rev` is kept out so that `hrev` applies to `i.rev`)
      simpa [χ_eq, ξ, w, w_swap, stepTorus, hϖ, hij, hrev, hSy, field, pow_succ, mul_assoc,
        NeZero.ne, -Fin.val_rev] using (S_U w hw y hly).symm.trans h_zero
    simp [h_eq] at hf
  -- Hence `y` is also a multiple of `ρ (permGL σ⁻¹) x`, so both transvections at `i`, `j` fix it.
  have tv_y {a b : Fin N} (hab : σ a < σ b ∨ π a < π b) (h : a ≠ b) (d : F) (hd : v d ≤ 1) :
      ρ (transvectionGL h d) y = y := by
    obtain hab | hab := hab
    · -- (`map_inv` is kept out so that `ρ (permGL σ⁻¹)` stays in the form of the lemma)
      simp [y, π, mul_swap_eq_swap_mul σ, -map_inv, transvectionGL_apply_permGL_inv hx hab, hc, hd]
    · exact transvectionGL_apply_permGL_inv hx hab d hd
  -- By `swap_mul_transvectionGL`, `l (ρ d (U w y)) = ξ w * s y` for the torus elements `d` of the
  -- quadratic relation.
  have hκ : ∀ u : Fˣ, v u.val = 1 → letI d := mulSingle i (-u⁻¹) * mulSingle j u
      (∀ a : Fin N, v (d a).val = 1) → l (ρ (diagGL d) (U w y)) = ξ w * s y := fun u hu hd ↦ by
    have h_fact : l (ρ (permGL (swap i j) * transvectionGL hne u.val) y) =
        l (ρ (transvectionGL hne u.val⁻¹ * diagGL (mulSingle i (-u⁻¹) * mulSingle j u) *
          transvectionGL hne.symm u.val⁻¹) y) := by rw [swap_mul_transvectionGL]
    simpa [hl.apply_diagGL_unit, apply_ite, U, s, hl hw, field, π, hne.symm, hl.apply_proIwahori,
      hu, hd, tv_y, hij, hne, mulSingle_apply, transvectionGL_mem_proIwahori] using h_fact.symm
  have h_quad : q • S (U w y) = ξ (w ∘ swap i j) * S y + (q - 1) • (ξ w * s y) :=
    hl.quadratic_relation_stepTorus hϖ hcov y (ξ w * s y) hκ
  -- With `h_zero` this reads `q * a = q * b + (q - 1) * a` for the roots `a` at `i` and `b` at `j`
  -- up to a common factor, so `a = q * b`, against `‖a‖ < ‖b‖`.
  have h_root : (θ (σ i) ϖ : ℂ) = q * θ (σ j) ϖ := by
    -- (`Fin.val_rev` is kept out so that `hrev` applies to `i.rev`)
    simpa [S_eq (tv_y _ hne), hne, h_zero, χ_eq, w_swap, w, stepTorus, hij, hrev, hsy, π, ξ, q, hϖ,
      field, pow_succ, ← sub_eq_iff_eq_add, -Fin.val_rev, normAbsChar] using h_quad
  simp [NeZero.ne, h_root, q] at hf

/-- Let `x` be fixed by `New.proIwahori`, let `l` be an exponent for `torusChar θ` that vanishes at
every permuted vector `ρ (permGL σ) x`, and let `s` be strictly dominant. Then for every `z` in the
span of the translates of `x`, `l` vanishes at `ρ (diagGL (s ^ n)) z` for all large `n`. -/
private lemma IsExponent.eventually_apply_diagGL_pow_eq_zero (hl : IsExponent ρ (torusChar θ) l)
    (hϖ : v ϖ.val = exp (-1)) (hx : x ∈ levelSpace ρ.ρ proIwahori) {s : Fin N → Fˣ}
    (hs : StrictMono fun i : Fin N ↦ v (s i).val)
    (h_perm : ∀ σ : Perm (Fin N), l (ρ (permGL σ) x) = 0) {z : ρ} (hz : z ∈ cyclicSpan ρ.ρ x) :
    ∀ᶠ n : ℕ in Filter.atTop, l (ρ (diagGL (s ^ n)) z) = 0 := by
  induction hz using span_induction with
  | zero => simp
  | add z₁ z₂ _ _ h₁ h₂ =>
    filter_upwards [h₁, h₂] with n h₁n h₂n using by rw [map_add, map_add, h₁n, h₂n, add_zero]
  | smul a z _ h => filter_upwards [h] with n hn using by rw [map_smul, map_smul, hn, smul_zero]
  | mem z hz_mem =>
    -- Write `g = u t σ k` with `u` unitriangular and `k ∈ proIwahori`. For large `n`, `s ^ n`
    -- conjugates `u` into `proIwahori` and `s ^ n * t` is dominant.
    obtain ⟨g, rfl⟩ := hz_mem
    obtain ⟨u, hu, ⟨t, σ, hk⟩, -⟩ := exists_iwasawa_bruhat g
    have iwasawa : ρ g x = ρ u (ρ (diagGL t) (ρ (permGL σ) x)) := by
      simpa [Representation.inv_apply_eq_iff] using hx ⟨_, hk⟩
    filter_upwards [eventually_v_mul_pow_le_one hs u,
      eventually_pow_mul_mem_dominantTorus hs t] with n h_small h_dom
    have conj_mem : MulAut.conj (diagGL (s ^ n)) u ∈ proIwahori := by
      -- (`map_pow` is kept out here and below: it would turn `diagGL (s ^ n)` into a power of
      -- operators, a form that the lemmas used are not stated for)
      simp_all [mem_proIwahori_iff_of_unitriangular, diagGL, field, -map_pow, Matrix.one_apply]
    calc l (ρ (diagGL (s ^ n)) (ρ g x))
        = l (ρ (MulAut.conj (diagGL (s ^ n)) u) (ρ (diagGL (s ^ n * t) * permGL σ) x)) := by
          simp [iwasawa, -map_pow]
      _ = l (ρ (diagGL (s ^ n * t) * permGL σ) x) := hl.apply_proIwahori _ conj_mem _
      _ = torusChar θ (s ^ n * t) * l (ρ (permGL σ) x) :=
        hl.apply_monomial_translate hϖ hx mem_proIwahori_iff_blockParahoric.2 σ
          fun a b hab ↦ .inl (h_dom hab.le)
      _ = 0 := by rw [h_perm, mul_zero]

omit [CompactSpace 𝒪[F]] in
/-- Let `s` be strictly dominant. Every torus element `t` becomes dominant when multiplied by a
power of `s`: `t * s ^ k` is dominant for some `k`, in the form that
`MonoidHom.toLocalizationMap` asks for. -/
private lemma exists_mul_powers_eq_of_strictMono {s : Fin N → Fˣ}
    (hs : StrictMono fun i : Fin N ↦ v (s i).val) (t : Fin N → Fˣ) :
    ∃ p : dominantTorus (n := Fin N) (F := F) ×
        Submonoid.powers (⟨s, hs.monotone⟩ : dominantTorus),
      t * (p.2.val : Fin N → Fˣ) = (p.1 : Fin N → Fˣ) := by
  obtain ⟨k, hk⟩ := (eventually_pow_mul_mem_dominantTorus hs t).exists
  exact ⟨(⟨s ^ k * t, hk⟩, ⟨⟨s, hs.monotone⟩ ^ k, k, rfl⟩), mul_comm t (s ^ k)⟩

/-- An eigenvector gives an exponent. Let `ρ` be a smooth representation of `GL_N(F)` with a
positive definite invariant form `B` (`hB`), and suppose the I₁-invariants (`New.proIwahori`) in the
span of the translates of `x` are finite-dimensional. If this span contains a non-zero I₁-fixed `y`
with `U_t y = ξ(t) y` for all dominant `t` (`U_t` = mean over I₁ after `ρ (diagGL t)`), then it
contains a `w` with `B w w ≠ 0` such that `B w` is an exponent for `ξ`, i.e.
`B w (ρ(t) (mean of z over I₁)) = ξ(t) B w z` for all `z` and dominant `t`; as `B` is positive
definite, `B w w ≠ 0` says `w ≠ 0`. -/
lemma IsIwahoriEigen.exists_isExponent {B : ρ →ₗ⋆[ℂ] ρ →ₗ[ℂ] ℂ} (hB : IsUnitary ρ.ρ B)
    [Module.Finite ℂ ((cyclicSpan ρ.ρ x).submoduleOf (levelSpace ρ.ρ proIwahori))]
    {ξ : (Fin N → Fˣ) →* ℂˣ} {y : ρ} (h_eig : IsIwahoriEigen ρ ξ y) (hy : y ∈ cyclicSpan ρ.ρ x) :
    ∃ w ∈ cyclicSpan ρ.ρ x, B w w ≠ 0 ∧ IsExponent ρ ξ (B w) := by
  -- The forms `B w`, `w` a fixed vector in `cyclicSpan ρ.ρ x`, make a finite-dimensional space `S`
  -- of forms on the fixed vectors, stable under the duals of the commuting `iwahoriHeckeHom ρ t`.
  -- Evaluation at `y` is a nonzero `ξ`-eigenfunctional on `S`, so `S` contains a `ξ`-eigenform
  -- (`exists_eigenvector_of_functional`).
  obtain ⟨hy₀, hy_fix, hy_eig⟩ := h_eig
  have hB_pos : ∀ z : ρ, z ≠ 0 → 0 < B z z := hB.1
  let W : Submodule ℂ ρ := levelSpace ρ.ρ proIwahori
  let S : Submodule ℂ (Dual ℂ W) := ((cyclicSpan ρ.ρ x).submoduleOf W).map (B.domRestrict₁₂ W W)
  have h_stable (t : dominantTorus) : ∀ φ ∈ S, (iwahoriHeckeHom ρ t).dualMap φ ∈ S := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨⟨_, compactMean_mem_levelSpace _⟩, compactMean_mem_cyclicSpan (diagGL t)⁻¹ hw, ?_⟩
    ext
    simp [hB.adjoint_eq_inv, hB.compactMean_adjoint, ← hB.compactMean_adjoint w, iwahoriHeckeHom,
      LinearMap.domRestrict₁₂_apply]
  let ev : Dual ℂ W →ₗ[ℂ] ℂ := .applyₗ ⟨y, hy_fix⟩
  have ev_ne : ¬S ≤ ev.ker := fun h ↦ (hB_pos y hy₀).ne' (h ⟨⟨y, hy_fix⟩, hy, rfl⟩)
  have ev_eig (t : dominantTorus) (φ : Dual ℂ W) :
      ev ((iwahoriHeckeHom ρ t).dualMap φ) = ξ t * ev φ := by
    have h_U : iwahoriHeckeHom ρ t ⟨y, hy_fix⟩ = (ξ t : ℂ) • ⟨y, hy_fix⟩ :=
      Subtype.ext (hy_eig _ t.prop)
    show φ (iwahoriHeckeHom ρ t ⟨y, hy_fix⟩) = ξ t * φ ⟨y, hy_fix⟩
    rw [h_U, map_smul, _root_.smul_eq_mul]
  -- the operators `iwahoriHeckeHom ρ t` commute, and so do their duals
  have h_comm (s t : dominantTorus) (φ : Dual ℂ W) (_ : φ ∈ S) :
      (iwahoriHeckeHom ρ s).dualMap ((iwahoriHeckeHom ρ t).dualMap φ) =
        (iwahoriHeckeHom ρ t).dualMap ((iwahoriHeckeHom ρ s).dualMap φ) := by
    ext z
    simp only [LinearMap.dualMap_apply]
    simp only [← End.mul_apply, ← map_mul, mul_comm]
  obtain ⟨_, ⟨w, hw, rfl⟩, hw₀, hw_eig⟩ :=
    exists_eigenvector_of_functional _ h_stable h_comm ev ev_ne ev_eig
  have hw_ne : (w : ρ) ≠ 0 := fun h ↦ by simp_all
  refine ⟨w, hw, (hB_pos w hw_ne).ne', fun t ht z ↦ ?_⟩
  simpa [← hB.compactMean_adjoint, iwahoriHeckeHom, LinearMap.domRestrict₁₂_apply] using
    LinearMap.congr_fun (hw_eig ⟨t, ht⟩) ⟨_, compactMean_mem_levelSpace z⟩

/-- Let `ρ` be unitary (`hB`), `ϖ` a uniformiser, and `x ≠ 0` fixed by `New.proIwahori`, where the
span of the translates of `x` has finite-dimensional `proIwahori`-invariants. Let the integral torus
act on `x` by `τ` (`hτ`), and let each permutation matrix whose permutation preserves `τ` on units
act on `x` by a scalar (`hP`). Then some `θ` has (a) an exponent for `torusChar θ` nonzero at `x`,
that is, a form `l` with `l (ρ t (mean of y over I₁)) = torusChar θ t * l y` for dominant diagonal
`t`; (b) `θ i ε = τ (mulSingle i ε)` for units `ε`; (c) a `σ` with `‖θ (σ i) ϖ‖` not increasing, and
a nonzero `I₁`-fixed `y` in the span of translates of `x` with
`(mean over I₁) (ρ t y) = torusChar (θ ∘ σ) t • y` for dominant `t`. -/
lemma exists_sorted_isIwahoriEigen_of_diagGL_smul (hϖ : v ϖ.val = exp (-1))
    (hx : x ∈ levelSpace ρ.ρ proIwahori)
    (hτ : ∀ t : Fin N → Fˣ, diagGL t ∈ intGL (Fin N) 𝒪[F] → ρ (diagGL t) x = τ t • x)
    (hP : ∀ σ : Perm (Fin N),
      (∀ (i : Fin N) (ε : Fˣ), v ε.val = 1 → τ (mulSingle i ε) = τ (mulSingle (σ i) ε)) →
      ∃ c : ℂ, ρ (permGL σ) x = c • x)
    {B : ρ →ₗ⋆[ℂ] ρ →ₗ[ℂ] ℂ} (hB : IsUnitary ρ.ρ B)
    [Module.Finite ℂ ((cyclicSpan ρ.ρ x).submoduleOf (levelSpace ρ.ρ proIwahori))] (hx_ne : x ≠ 0) :
    ∃ θ : Fin N → Fˣ →* ℂˣ,
      (∃ l : ρ →ₗ[ℂ] ℂ, IsExponent ρ (torusChar θ) l ∧ l x ≠ 0) ∧
      (∀ (i : Fin N) (ε : Fˣ), v ε.val = 1 → θ i ε = τ (mulSingle i ε)) ∧
      ∃ σ : Perm (Fin N), Antitone ((fun i : Fin N ↦ ‖(θ i ϖ : ℂ)‖) ∘ σ) ∧
        ∃ y ∈ cyclicSpan ρ.ρ x, IsIwahoriEigen ρ (torusChar (θ ∘ σ)) y := by
  -- A common eigenvector of the `U_t` in `cyclicSpan ρ.ρ x` on which diagonal units act through `τ`
  -- gives a character `torusChar θ` and an exponent `B w`, which is not zero at `x`. Sort it by
  -- `IsExponent.exists_sorted`; the sorted eigenform gives an eigenvector for the sorted character.
  -- `s` is strictly dominant and `iwahoriHeckeHom ρ s` is injective
  obtain ⟨s, hs, hs_inj⟩ := exists_iwahoriHeckeHom_injective ρ hϖ
  let C : Submodule ℂ (levelSpace ρ.ρ proIwahori) :=
    (cyclicSpan ρ.ρ x).submoduleOf (levelSpace ρ.ρ proIwahori)
  have stable (t : dominantTorus) : C ∈ (iwahoriHeckeHom ρ t).invtSubmodule :=
    fun _ ↦ compactMean_mem_cyclicSpan _
  -- the fixed vectors on which each `mulSingle i ε`, `ε` a unit, acts by its value under `τ`
  have h_dom (i : Fin N) (ε : Fˣ) (h : v ε.val = 1) : mulSingle i ε ∈ dominantTorus := by
    simp [dominantTorus, apply_ite, h, Monotone, mulSingle_apply]
  let E : Submodule ℂ (levelSpace ρ.ρ proIwahori) := ⨅ (i : Fin N) (ε : Fˣ) (h : v ε.val = 1),
    (iwahoriHeckeHom ρ ⟨mulSingle i ε, h_dom i ε h⟩).eigenspace (τ (mulSingle i ε))
  have hxE : ⟨x, hx⟩ ∈ E := by
    aesop (add simp [iwahoriHeckeHom, apply_ite]) (add simp [mulSingle_apply, diagGL_mem_intGL])
  have stable_E (t : dominantTorus) (y : levelSpace ρ.ρ proIwahori) (hy : y ∈ E) :
      iwahoriHeckeHom ρ t y ∈ E := by
    simp only [E, Submodule.mem_iInf, End.mem_eigenspace_iff] at hy ⊢
    intro i ε hε
    rw [← End.mul_apply, ← map_mul, mul_comm, map_mul, End.mul_apply, hy i ε hε, map_smul]
  have hx_mem : (⟨x, hx⟩ : levelSpace ρ.ρ proIwahori) ∈ C ⊓ E := ⟨self_mem_cyclicSpan, hxE⟩
  obtain ⟨χ, y, ⟨hy, hyE⟩, y_ne, hy_eigen⟩ := exists_eigencharacter (S := C ⊓ E) (iwahoriHeckeHom ρ)
    (fun t y ⟨hy_C, hy_E⟩ ↦ ⟨stable t hy_C, stable_E t y hy_E⟩)
    fun h ↦ hx_ne (congrArg Subtype.val (h hx_mem))
  -- the torus is the localisation of `dominantTorus` away from `s`, and `χ s ≠ 0`, so `χ` extends
  -- to it
  obtain ⟨θ, hθ⟩ : ∃ θ : Fin N → Fˣ →* ℂˣ,
      ∀ t : dominantTorus, χ t = torusChar θ (t : Fin N → Fˣ) := by
    let loc : AwayMap (⟨s, hs.monotone⟩ : dominantTorus) (Fin N → Fˣ) :=
      dominantTorus.subtype.toLocalizationMap (fun _ ↦ Group.isUnit _)
        (exists_mul_powers_eq_of_strictMono hs) (by simp)
    have hχs : IsUnit (χ ⟨s, hs.monotone⟩) := by simpa [hy_eigen, y_ne] using hs_inj.ne y_ne
    refine ⟨torusChar.symm (AwayMap.lift _ loc hχs).toHomUnits, fun t ↦ ?_⟩
    rw [apply_symm_apply]
    exact (AwayMap.lift_eq _ loc hχs t).symm
  have hθτ (i : Fin N) (ε : Fˣ) (hε : v ε.val = 1) : θ i ε = τ (mulSingle i ε) := by
    simp +contextual [E, smul_left_inj, hy_eigen, hθ, y_ne, normAbsChar] at hyE
    exact hyE i ε hε
  have y_eig : IsIwahoriEigen ρ (torusChar θ) (y : ρ) := by
    refine ⟨by simpa using y_ne, y.prop, fun t ht ↦ ?_⟩
    rw [← hθ ⟨t, ht⟩]
    exact congrArg Subtype.val (hy_eigen ⟨t, ht⟩)
  obtain ⟨w, hw, w_ne, hl⟩ := y_eig.exists_isExponent hB hy
  have hwx : B w x ≠ 0 := by
    intro hwx_zero
    -- Then `B w` kills all permuted vectors: where it does not, the permutation preserves `τ` on
    -- units, so it acts on `x` by a scalar (`hP`).
    have h_perm_zero (σ : Perm (Fin N)) : B w (ρ (permGL σ) x) = 0 := by
      by_contra h
      -- move the diagonal unit past `permGL σ` and compare `IsExponent.apply_diagGL_unit`, `hθτ`
      -- and `hτ`
      have h_type : ∀ (i : Fin N) (ε : Fˣ), v ε.val = 1 →
          τ (mulSingle i ε) = τ (mulSingle (σ i) ε) := by
        intro i ε hε
        have h_comm : B w (ρ (diagGL (mulSingle (σ i) ε) * permGL σ) x) =
            B w (ρ (permGL σ * diagGL (mulSingle (σ i) ε ∘ ⇑σ)) x) := by rw [diagGL_mul_permGL]
        simpa [hτ, hε, h, hθτ, hl.apply_diagGL_unit, apply_ite, mulSingle_comp_equiv,
          mulSingle_apply, diagGL_mem_intGL, normAbsChar] using h_comm.symm
      obtain ⟨c, hc⟩ := hP σ h_type
      simp [hc, hwx_zero] at h
    -- So `B w` kills `ρ (diagGL (s ^ n)) z` for `z` in `cyclicSpan ρ.ρ x` and large `n`.
    have h_vanish (z : ρ) (hz : z ∈ cyclicSpan ρ.ρ x) :
        ∀ᶠ n in Filter.atTop, B w (ρ (diagGL (s ^ n)) z) = 0 :=
      hl.eventually_apply_diagGL_pow_eq_zero hϖ hx hs h_perm_zero hz
    -- for the mean of `w` the value is `torusChar θ (s ^ n) * B w w ≠ 0`
    obtain ⟨n, hn⟩ := (h_vanish _ (compactMean_mem_cyclicSpan (K := proIwahori) 1 hw)).exists
    -- (`map_pow` is kept out so that `hl` applies to `diagGL (s ^ n)`)
    simp [hl (pow_mem hs.monotone n), w_ne, -map_pow] at hn
  obtain ⟨σ, ⟨l, exp_l, l_ne⟩, anti⟩ := hl.exists_sorted hϖ hx hτ hP hwx
  -- `l` is an eigenfunctional that is nonzero on the fixed vectors of `cyclicSpan ρ.ρ x`
  let l' : levelSpace ρ.ρ proIwahori →ₗ[ℂ] ℂ := l.domRestrict (levelSpace ρ.ρ proIwahori)
  -- the mean of `ρ (permGL σ⁻¹) x` lies in `C`, and `l'` does not vanish there
  have h_mean_mem : (⟨_, compactMean_mem_levelSpace (ρ (permGL σ⁻¹) x)⟩ :
      levelSpace ρ.ρ proIwahori) ∈ C := compactMean_mem_cyclicSpan (permGL σ⁻¹) self_mem_cyclicSpan
  have l'_ne : ¬C ≤ l'.ker := fun h ↦ l_ne (exp_l.apply_compactMean.symm.trans (h h_mean_mem))
  have l'_eig (t : dominantTorus) (z : levelSpace ρ.ρ proIwahori) :
      l' (iwahoriHeckeHom ρ t z) = torusChar (θ ∘ σ) t * l' z := by
    simpa [l', iwahoriHeckeHom, exp_l.apply_compactMean] using exp_l t.prop z
  have h_comm (s t : dominantTorus) (z : levelSpace ρ.ρ proIwahori) (_ : z ∈ C) :
      iwahoriHeckeHom ρ s (iwahoriHeckeHom ρ t z) =
        iwahoriHeckeHom ρ t (iwahoriHeckeHom ρ s z) := by
    simp only [← End.mul_apply, ← map_mul, mul_comm]
  obtain ⟨y', hy', y'_ne, hy'_eigen⟩ :=
    exists_eigenvector_of_functional (iwahoriHeckeHom ρ) stable h_comm l' l'_ne l'_eig
  exact ⟨θ, ⟨_, hl, hwx⟩, hθτ, σ, anti, y', hy', by simpa, y'.prop,
    fun t ht ↦ congrArg Subtype.val (hy'_eigen ⟨t, ht⟩)⟩

end New

end SortedExponents

/-!
## Sorted exponents from distinct characters of determinants

Let `x` be a vector of a smooth unitary representation of `GL_N(F)` that is fixed by the principal
congruence subgroup, so that `GL_N` of the residue field acts on the span of its translates by
`GL_N` of the valuation ring. If `x` has a nonzero projection along a product, in the sense of
parabolic induction (`New.Hall`), of distinct characters of determinants (`New.detChar`), then the
span of its translates contains a sorted eigenvector for the pro-`p` Iwahori operators, provided
that the pro-`p` Iwahori invariants of every cyclic subrepresentation have finite dimension
(`New.exists_sorted_of_detChar`). The proof passes to a vector on which a parahoric subgroup acts by
a character and applies `New.exists_sorted_isIwahoriEigen_of_diagGL_smul`.
-/

section ExponentOfLabel

open Matrix Valued IsLocalRing MulChar Fintype Submodule Pi Function Polynomial
open scoped WithZero

attribute [local instance low] Fintype.ofFinite

/-- An index set ordered by `e` can be cut into consecutive blocks of prescribed sizes `m a`: there
is a map `b` to the blocks that grows with `e` (`Monovary e b`) and whose fibre over `a` has `m a`
elements. -/
lemma New.exists_monovary_card_fiber {n : Type*} {N r : ℕ} [Fintype n] (e : n ≃ Fin N)
    {m : Fin r → ℕ} (hm : ∑ a : Fin r, m a = N) :
    ∃ b : n → Fin r, Monovary e b ∧ (fun a : Fin r ↦ card {i // b i = a}) = m := by
  -- Sort a map `Fin N → Fin r` whose fibres have the sizes `m a`.
  let u : Fin N ≃ Σ a : Fin r, Fin (m a) := equivOfCardEq (by simp [hm])
  let τ : Equiv.Perm (Fin N) := Tuple.sort (Sigma.fst ∘ u)
  have h_mono : Monovary e (Sigma.fst ∘ u ∘ τ ∘ e) :=
    (monotone_id.monovary (Tuple.monotone_sort (Sigma.fst ∘ u))).comp_right e
  refine ⟨Sigma.fst ∘ u ∘ τ ∘ e, h_mono, funext fun a ↦ ?_⟩
  -- The fibre over `a` corresponds to the summand `Fin (m a)`.
  have h_fiber : {i // (Sigma.fst ∘ u ∘ τ ∘ e) i = a} ≃ Fin (m a) :=
    (Equiv.subtypeEquivOfSubtype (e.trans (τ.trans u))).trans (.sigmaSubtype a)
  simpa using card_congr h_fiber

/-- Reading a matrix of `GL (Fin N)` of the valuation ring along `e : n ≃ Fin N` gives a matrix of
`GL n` of the valuation ring. -/
private lemma New.reindexGL_symm_mem_intGL {F : Type*} [Field F] [Valued F ℤᵐ⁰] {N : ℕ}
    {n : Type*} [Fintype n] [DecidableEq n] (e : n ≃ Fin N) {g : GL (Fin N) F}
    (hg : g ∈ intGL (Fin N) 𝒪[F]) : (reindexGL e).symm g ∈ intGL n 𝒪[F] := by
  obtain ⟨k, rfl⟩ := hg
  exact ⟨(reindexGL e).symm k, rfl⟩

/-- Let `x` be fixed by the integral matrices that reduce to `1`, and `s` a lift of `GL n` of the
residue field to the valuation ring. Let the sum in `h_sum_ne`, against the product of the
characters `χ a ∘ det` in the sizes of the fibres of `b` (`rankPart k` takes the part on `GL_k`,
`evalGL g` the value at `g`), be nonzero. Then the span of the translates of `x` contains a nonzero
`y` on which each integral `g` whose reduction lies in `parabolic b` acts by the product of the
`χ a` of the determinants of its diagonal blocks. -/
private lemma New.exists_reindexGL_apply_eq_smul_of_finsum_ne_zero {F : Type*} [Field F]
    [Valued F ℤᵐ⁰] [CompactSpace 𝒪[F]] {N : ℕ} {ρ : Rep ℂ (GL (Fin N) F)} {x : ρ}
    {n : Type*} [Fintype n] [DecidableEq n] (e : n ≃ Fin N) {r : ℕ}
    {χ : Fin r → MulChar (IsLocalRing.ResidueField 𝒪[F]) ℂ} (b : n → Fin r)
    (hx : ∀ k : intGL n 𝒪[F], intGL.map (residue 𝒪[F]) k = 1 → ρ (reindexGL e k.val) x = x)
    {s : GL n (IsLocalRing.ResidueField 𝒪[F]) → intGL n 𝒪[F]}
    (h_lift : ∀ g : GL n (IsLocalRing.ResidueField 𝒪[F]), intGL.map (residue 𝒪[F]) (s g) = g)
    (h_sum_ne : ∑ᶠ g : GL n (IsLocalRing.ResidueField 𝒪[F]),
        star ((∏ a : Fin r, (detChar (χ a)).rankPart (card {i // b i = a})).evalGL g) •
          ρ (reindexGL e (s g).val) x ≠ 0) :
    ∃ y ∈ cyclicSpan ρ.ρ x, y ≠ 0 ∧
      ∀ (g : intGL n 𝒪[F]) (hg : intGL.map (residue 𝒪[F]) g ∈ parabolic b),
        ρ (reindexGL e g) y =
          (∏ a : Fin r, χ a (blockHom b a ⟨intGL.map (residue 𝒪[F]) g, hg⟩).val.det) • y := by
  -- By Frobenius reciprocity (`sum_evalGL_prod_eq_zero_iff`) the sum `y` over some coset of
  -- `parabolic b` is nonzero; translating `y` by `g` permutes the coset and brings out the
  -- character.
  -- The action on `x` depends only on the reduction modulo the maximal ideal.
  have h_act (g z : intGL n 𝒪[F]) (w : GL n (IsLocalRing.ResidueField 𝒪[F]))
      (hw : w = intGL.map (residue 𝒪[F]) g * intGL.map (residue 𝒪[F]) z) :
      ρ (reindexGL e g.val) (ρ (reindexGL e z.val) x) = ρ (reindexGL e (s w).val) x := by
    simpa [inv_mul_eq_one, h_lift, hw, Representation.inv_apply_eq_iff] using
      hx ((s w)⁻¹ * (g * z))
  obtain ⟨g₀, hy_ne⟩ :
      ∃ g₀ : GL n (IsLocalRing.ResidueField 𝒪[F]),
        ∑ p : parabolic b, (∏ a : Fin r, star ((detChar (χ a)).evalGL (blockHom b a p))) •
          ρ (reindexGL e (s (p * g₀)).val) x ≠ 0 := by
    simpa [finsum_eq_sum_of_fintype] using
      (sum_evalGL_prod_eq_zero_iff b (fun a ↦ lift_detChar (χ := χ a) (faithfulChar 𝓀[F]) rfl)
        (fun g ↦ ρ (reindexGL e (s g).val))
        fun g z ↦ h_act (s g) (s z) (g * z) (by rw [h_lift, h_lift])).not.mp h_sum_ne
  set y : ρ := ∑ p : parabolic b, (∏ a : Fin r, star ((detChar (χ a)).evalGL (blockHom b a p))) •
    ρ (reindexGL e (s (p * g₀)).val) x
  refine ⟨y, ?_, hy_ne, fun g hg ↦ ?_⟩
  · -- each summand is a multiple of a translate of `x`
    exact _root_.sum_mem fun p _ ↦ smul_mem _ _ (subset_span ⟨_, rfl⟩)
  · -- reindex the sum over the coset by `p ↦ ḡ⁻¹ * p`, `ḡ` the reduction of `g`
    simp only [y, Finset.smul_sum, smul_smul, map_sum, map_smul]
    refine .symm (sum_equiv (.mulLeft ⟨intGL.map (residue 𝒪[F]) g, hg⟩⁻¹) _ _ fun p ↦ ?_)
    rw [h_act _ _ (p * g₀) (by simp [h_lift, mul_assoc])]
    simp [inv_apply', evalGL_detChar, star_apply', Finset.prod_mul_distrib]

/-- Let `g` be a matrix of `GL (Fin N)` of the valuation ring whose entry `(i, j)` has valuation
less than `1` whenever `c (e⁻¹ j) < c (e⁻¹ i)`. Then `g`, read as a matrix indexed by `n` and
reduced modulo the maximal ideal, is block upper triangular for `c`. -/
private lemma New.blockTriangular_intGL_map_reindexGL_symm_of_valuation_lt_one {F : Type*}
    [Field F] [Valued F ℤᵐ⁰] [CompactSpace 𝒪[F]] {N : ℕ} {n : Type*} [Fintype n] [DecidableEq n]
    (e : n ≃ Fin N) {k : ℕ} (c : n → Fin k) (g : GL (Fin N) F) (hg : g ∈ intGL (Fin N) 𝒪[F])
    (h_low : ∀ i j : Fin N, c (e.symm j) < c (e.symm i) → v (g i j) < 1) :
    BlockTriangular (intGL.map (residue 𝒪[F])
      (⟨(reindexGL e).symm g, reindexGL_symm_mem_intGL e hg⟩ : intGL n 𝒪[F])).val c := by
  -- Entries of valuation less than `1` reduce to `0`. (`residue_eq_zero_iff` is left out so that
  -- `residue_eq_zero_iff_valuation_lt_one` gives the form with the valuation.)
  simpa [reindexGL, BlockTriangular, intGL.map_apply, residue_eq_zero_iff_valuation_lt_one,
    -residue_eq_zero_iff, e.forall_congr_left] using h_low

/-- Let `b` grow with the order `e` (`Monovary e b`), and let each integral `g` whose reduction
lies in `parabolic b` act on `y` by the product of the `χ a` of the determinants of its diagonal
blocks. Then each integral `g` whose reduction is upper triangular for the order `e` acts on `y` by
the product of the `χ (b i)` of the diagonal entries of its reduction. -/
private lemma New.reindexGL_apply_eq_prod_smul_of_blockTriangular {F : Type*} [Field F]
    [Valued F ℤᵐ⁰] [CompactSpace 𝒪[F]] {N : ℕ} {ρ : Rep ℂ (GL (Fin N) F)} {y : ρ}
    {n : Type*} [Fintype n] [DecidableEq n] (e : n ≃ Fin N) {r : ℕ}
    {χ : Fin r → MulChar (IsLocalRing.ResidueField 𝒪[F]) ℂ} {b : n → Fin r} (hb : Monovary e b)
    (h_block : ∀ (g : intGL n 𝒪[F]) (hg : intGL.map (residue 𝒪[F]) g ∈ parabolic b),
      ρ (reindexGL e g) y =
        (∏ a : Fin r, χ a (blockHom b a ⟨intGL.map (residue 𝒪[F]) g, hg⟩).val.det) • y)
    (g : intGL n 𝒪[F]) (hg : BlockTriangular (intGL.map (residue 𝒪[F]) g).val e) :
    ρ (reindexGL e g) y = (∏ i : n, χ (b i) (intGL.map (residue 𝒪[F]) g i i)) • y := by
  -- Blocks of smaller level come first in the order `e`, so the reduction lies in `parabolic b`.
  have h_lt (i j : n) (h_lt_b : b j < b i) : e j < e i := by grind [hb h_lt_b, e.injective]
  have hg_par : intGL.map (residue 𝒪[F]) g ∈ parabolic b := fun i j h ↦ hg (h_lt i j h)
  rw [h_block g hg_par, ← prod_fiberwise b]
  congr 1
  refine Finset.prod_congr rfl fun a _ ↦ ?_
  -- The block of level `a` is upper triangular for the order of `n` read from `e` (the order that
  -- `det_of_isUpperTriangular` uses), so its determinant is the product of its diagonal entries.
  let order_e : LinearOrder n := e.linearOrder
  rw [det_of_isUpperTriangular hg.submatrix, map_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  -- an index `i` of the block of level `a` has `b i = a`, and the block's entries are those of `g`
  rw [i.prop]
  rfl

/-- Let every integral `g` that is upper triangular modulo the maximal ideal act on `y` by the
product of the `f i` of the residues of its diagonal entries, where `R : F → 𝓀[F]` extends the
residue map. Then `y` is fixed by `New.proIwahori`. -/
private lemma New.mem_levelSpace_proIwahori_of_forall_apply_eq_prod_smul {F : Type*} [Field F]
    [Valued F ℤᵐ⁰] [CompactSpace 𝒪[F]] {N : ℕ} {ρ : Rep ℂ (GL (Fin N) F)} {y : ρ}
    {R : F → 𝓀[F]} (hR : ∀ a : 𝒪[F], R a = residue 𝒪[F] a)
    (f : Fin N → MulChar (IsLocalRing.ResidueField 𝒪[F]) ℂ)
    (h_upper : ∀ g : GL (Fin N) F, g ∈ intGL (Fin N) 𝒪[F] → (∀ i j : Fin N, j < i → v (g i j) < 1) →
      ρ g y = (∏ i : Fin N, f i (R (g i i))) • y) :
    y ∈ levelSpace ρ.ρ proIwahori := by
  -- An element of `New.proIwahori` is integral and upper triangular modulo the maximal ideal, with
  -- diagonal entries congruent to `1`.
  rintro ⟨g, hg⟩
  obtain ⟨hg_par, hg_diag⟩ := mem_proIwahori_iff_blockParahoric.mp hg
  obtain ⟨hg_int, hg_low⟩ := mem_blockParahoric.mp hg_par
  have h_diag (i : Fin N) : R (g i i) = 1 :=
    (hR ⟨g i i, (mem_intGL.mp hg_int).1 i i⟩).trans
      (residue_eq_one_iff_valuation_sub_one_lt_one.mpr (hg_diag i))
  simp [h_upper g hg_int hg_low, h_diag]

/-- Let `R : F → 𝓀[F]` extend the residue map, let `b` grow with the order `e`, and let each
integral `g : intGL n 𝒪[F]` whose reduction lies in `parabolic b` act on `y` by the product of the
`χ a` of the determinants of its diagonal blocks. Then each `g` in `GL (Fin N)` of the valuation
ring that is upper triangular modulo the maximal ideal acts on `y` by the product of the
`χ (b (e⁻¹ i))` of the residues `R (g i i)` of its diagonal entries. -/
private lemma New.apply_eq_prod_smul_of_valuation_lt_one {F : Type*} [Field F] [Valued F ℤᵐ⁰]
    [CompactSpace 𝒪[F]] {N : ℕ} {ρ : Rep ℂ (GL (Fin N) F)} {y : ρ}
    {n : Type*} [Fintype n] [DecidableEq n] (e : n ≃ Fin N) {r : ℕ}
    {χ : Fin r → MulChar (IsLocalRing.ResidueField 𝒪[F]) ℂ} {b : n → Fin r} (hb : Monovary e b)
    {R : F → 𝓀[F]} (hR : ∀ a : 𝒪[F], R a = residue 𝒪[F] a)
    (h_block : ∀ (g : intGL n 𝒪[F]) (hg : intGL.map (residue 𝒪[F]) g ∈ parabolic b),
      ρ (reindexGL e g) y =
        (∏ a : Fin r, χ a (blockHom b a ⟨intGL.map (residue 𝒪[F]) g, hg⟩).val.det) • y)
    (g : GL (Fin N) F) (hg : g ∈ intGL (Fin N) 𝒪[F])
    (h_low : ∀ i j : Fin N, j < i → v (g i j) < 1) :
    ρ g y = (∏ i : Fin N, χ (b (e.symm i)) (R (g i i))) • y := by
  -- Read as a matrix indexed by `n`, `g` is upper triangular modulo the maximal ideal for the order
  -- `e`.
  have h_low_e : ∀ i j : Fin N, e (e.symm j) < e (e.symm i) → v (g i j) < 1 := by simpa using h_low
  have h_act : ρ (reindexGL e ((reindexGL e).symm g)) y =
      (∏ i : n, χ (b i) (intGL.map (residue 𝒪[F])
        (⟨(reindexGL e).symm g, reindexGL_symm_mem_intGL e hg⟩ : intGL n 𝒪[F]) i i)) • y :=
    reindexGL_apply_eq_prod_smul_of_blockTriangular e hb h_block _
      (blockTriangular_intGL_map_reindexGL_symm_of_valuation_lt_one e e g hg h_low_e)
  rw [(reindexGL e).apply_symm_apply] at h_act
  -- Reindex the product along `e` and write the residues through `R`.
  simpa [← e.symm.prod_comp, reindexGL, intGL.map_apply, ← hR] using h_act

/-- If `χ` is injective and the characters `χ a` and `χ a'` of the residue field agree at the
residue of every unit of the valuation ring, then `a = a'`. -/
private lemma New.eq_of_forall_mulChar_residue_eq {F : Type*} [Field F] [Valued F ℤᵐ⁰]
    [CompactSpace 𝒪[F]] {r : ℕ} {χ : Fin r → MulChar (IsLocalRing.ResidueField 𝒪[F]) ℂ}
    (hχ : Injective χ) {a a' : Fin r}
    (h_eq : ∀ u : 𝒪[F]ˣ, χ a (residue 𝒪[F] u) = χ a' (residue 𝒪[F] u)) : a = a' := by
  refine hχ (ext fun w ↦ ?_)
  -- Every unit of the residue field is the residue of a unit of the valuation ring.
  obtain ⟨u, rfl⟩ : ∃ u : 𝒪[F]ˣ, Units.map (residue 𝒪[F] : 𝒪[F] →* 𝓀[F]) u = w :=
    surjective_units_map_of_local_ringHom _ residue_surjective inferInstance w
  exact h_eq u

/-- If `f i = g (c i)` for every `i` and the fibre of `c` over `a` has `m a` elements, then the
monic polynomial with the roots `f i` is `∏ a, (X - g a) ^ m a`. -/
lemma Polynomial.prod_X_sub_C_eq_prod_pow_of_card_fiber {A ι κ : Type*} [CommRing A] [Fintype ι]
    [Fintype κ] [DecidableEq κ] {f : ι → A} {g : κ → A} {c : ι → κ} {m : κ → ℕ}
    (h_card : ∀ a : κ, card {i : ι // c i = a} = m a) (h_val : ∀ i : ι, f i = g (c i)) :
    ∏ i : ι, (X - C (f i)) = ∏ a : κ, (X - C (g a)) ^ m a := by
  simp_rw [h_val, ← h_card]
  simpa using (prod_fiberwise' c fun a ↦ X - C (g a)).symm

/-- Let `ρ` be smooth and unitary (`B` is an invariant scalar product), with finite-dimensional
`New.proIwahori`-invariants in each cyclic subrepresentation, and let `ϖ` be a uniformiser. Let the
characters `χ a` of the residue field be distinct and `∑ m a = N`, and let `Y` be the Hall-algebra
(`New.Hall`) product of the class functions `χ a ∘ det` on matrices of size `m a`. Let `x` be fixed
by the integral matrices that reduce to `1`, let `s` be a section of the reduction map, and suppose
`∑ conj (Y g) • ρ (s g) x ≠ 0`; here matrices are indexed by `n` and moved to `Fin N` along `e`.
Then the span of the translates of `x` contains a nonzero `New.proIwahori`-fixed `y` with
`(mean over I₁) (ρ t y) = torusChar θ t • y` for all dominant diagonal `t` (`New.IsIwahoriEigen`),
where `torusChar θ t = ∏ i, θ i (t i) * |t i| ^ (N - 1 - i)`, and `‖θ i ϖ‖` does not increase with
`i`. There is also a labelling `c` of the indices, taking each label `a` exactly `m a` times, such
that `θ i t` is `χ (c i)` of the residue of `t` for every unit `t`. -/
lemma New.exists_sorted_of_detChar {F : Type*} [Field F] [Valued F ℤᵐ⁰] [CompactSpace 𝒪[F]]
    {N : ℕ} {ρ : Rep ℂ (GL (Fin N) F)} [IsSmoothRep ρ.ρ] {ϖ : Fˣ} {B : ρ →ₗ⋆[ℂ] ρ →ₗ[ℂ] ℂ} {x : ρ}
    (hϖ : v ϖ.val = WithZero.exp (-1))
    [∀ z : ρ, Module.Finite ℂ ((cyclicSpan ρ.ρ z).submoduleOf (levelSpace ρ.ρ proIwahori 1))]
    (hB : IsUnitary ρ.ρ B) {n : Type*} {r : ℕ} {χ : Fin r → MulChar 𝓀[F] ℂ} [Fintype n]
    [DecidableEq n] (e : n ≃ Fin N) (hχ : Injective χ) {m : Fin r → ℕ} (hm : ∑ a : Fin r, m a = N)
    (hx : ∀ k : intGL n 𝒪[F], intGL.map (residue 𝒪[F]) k = 1 → ρ (reindexGL e k.val) x = x)
    {s : GL n 𝓀[F] → intGL n 𝒪[F]} (h_lift : ∀ g : GL n 𝓀[F], intGL.map (residue 𝒪[F]) (s g) = g)
    (h_sum_ne : ∑ᶠ g : GL n 𝓀[F],
        star ((∏ a : Fin r, (detChar (χ a)).rankPart (m a)).evalGL g) •
          ρ (reindexGL e (s g).val) x ≠ 0) :
    ∃ y ∈ cyclicSpan ρ.ρ x, ∃ (θ : Fin N → Fˣ →* ℂˣ) (c : Fin N → Fin r),
      IsIwahoriEigen ρ (torusChar θ) y ∧
      (Antitone fun i : Fin N ↦ ‖(θ i ϖ : ℂ)‖) ∧
      (∀ a : Fin r, card {i : Fin N // c i = a} = m a) ∧
      ∀ (t : Fˣ) (ht_unit : v t.val = 1) (i : Fin N),
        (θ i t : ℂ) = χ (c i) (residue 𝒪[F] ⟨t, ht_unit.le⟩) := by
  -- Cut the indices into blocks `b` of sizes `m a` and pass to a nonzero vector `y` in the span of
  -- the translates of `x` on which the preimage of `parabolic b` in `GL(𝒪)` acts by
  -- `∏ χ_a(det g_a)`. Then `exists_sorted_isIwahoriEigen_of_diagGL_smul` applies to `y`.
  obtain ⟨b, hb, rfl⟩ := exists_monovary_card_fiber e hm
  obtain ⟨y, hy_mem, hy_ne, h_block⟩ :=
    exists_reindexGL_apply_eq_smul_of_finsum_ne_zero e b hx h_lift h_sum_ne
  -- Transfer the action to `GL (Fin N) F`, with `R` an extension of the residue map to `F`.
  obtain ⟨R, hR_apply⟩ : ∃ R : F → 𝓀[F], ∀ a : 𝒪[F], R a = residue 𝒪[F] a :=
    ⟨extend Subtype.val (residue 𝒪[F]) 0, Subtype.val_injective.extend_apply _ _⟩
  -- An integral `g` that is upper triangular modulo the maximal ideal acts on `y` by the product of
  -- the `χ (b (e.symm i))` of the residues of its diagonal entries.
  have h_upper (g : GL (Fin N) F) (hg : g ∈ intGL (Fin N) 𝒪[F])
      (h_low : ∀ i j : Fin N, j < i → v (g i j) < 1) :
      ρ g y = (∏ i : Fin N, χ (b (e.symm i)) (R (g i i))) • y :=
    apply_eq_prod_smul_of_valuation_lt_one e hb hR_apply h_block g hg h_low
  -- An integral `g` that is block triangular for `b` modulo the maximal ideal scales `y`.
  have h_scalar (g : GL (Fin N) F) (hg : g ∈ intGL (Fin N) 𝒪[F])
      (h_low : ∀ i j : Fin N, b (e.symm j) < b (e.symm i) → v (g i j) < 1) :
      ∃ c : ℂ, ρ g y = c • y := by
    have h_par : intGL.map (residue 𝒪[F])
        (⟨(reindexGL e).symm g, reindexGL_symm_mem_intGL e hg⟩ : intGL n 𝒪[F]) ∈ parabolic b :=
      blockTriangular_intGL_map_reindexGL_symm_of_valuation_lt_one e b g hg h_low
    exact ⟨_, by simpa using h_block _ h_par⟩
  have hy_fixed : y ∈ levelSpace ρ.ρ proIwahori :=
    mem_levelSpace_proIwahori_of_forall_apply_eq_prod_smul hR_apply _ h_upper
  -- The integral torus acts on `y` by `τ`.
  let τ (t : Fin N → Fˣ) : ℂ := ∏ i : Fin N, χ (b (e.symm i)) (R (diagGL t i i))
  have hτ (t : Fin N → Fˣ) (ht : diagGL t ∈ intGL (Fin N) 𝒪[F]) : ρ (diagGL t) y = τ t • y :=
    h_upper _ ht (by simp +contextual [ne_of_gt])
  have hτ_single (i : Fin N) (ε : Fˣ) : τ (mulSingle i ε) = χ (b (e.symm i)) (R ε) := by
    have h_R_one : R 1 = 1 := by simpa using hR_apply 1
    simp [τ, mulSingle_apply, apply_ite, h_R_one]
  -- As the `χ a` are distinct, `τ` separates the blocks.
  have h_sep (i j : Fin N) (hij : ∀ ε : Fˣ, v ε.val = 1 → τ (mulSingle i ε) = τ (mulSingle j ε)) :
      b (e.symm i) = b (e.symm j) := by
    refine eq_of_forall_mulChar_residue_eq hχ fun a ↦ ?_
    let u : Fˣ := Units.map (𝒪[F].subtype : 𝒪[F] →+* F).toMonoidHom a
    have hu : v u.val = 1 := (Valuation.integer.integers _).valuation_unit a
    simpa [hτ_single, ← hR_apply, u] using hij u hu
  -- So a permutation that preserves `τ` on units preserves the blocks, and acts on `y` by a scalar.
  have h_perm (σ : Equiv.Perm (Fin N))
      (hσ : ∀ (i : Fin N) (ε : Fˣ), v ε.val = 1 → τ (mulSingle i ε) = τ (mulSingle (σ i) ε)) :
      ∃ c : ℂ, ρ (permGL σ) y = c • y := by
    refine h_scalar _ (permGL_mem_intGL σ) fun i j hij ↦ ?_
    -- the entry `(i, j)` of the permutation matrix is `0`: `j` and `σ j` lie in one block
    have h_ne : σ.symm i ≠ j := by grind [h_sep j (σ j) (hσ j)]
    simp [h_ne]
  -- `exists_sorted_isIwahoriEigen_of_diagGL_smul` gives `θ`, a permutation `σ` sorting it, an
  -- eigenvector for `θ ∘ σ`.
  obtain ⟨θ, -, hθ, σ, h_anti, z, hz, hz_eig⟩ :=
    exists_sorted_isIwahoriEigen_of_diagGL_smul hϖ hy_fixed hτ h_perm hB hy_ne
  refine ⟨z, span_le.mpr (Set.range_subset_iff.mpr fun g ↦ apply_mem_cyclicSpan g y hy_mem) hz,
    θ ∘ σ, b ∘ e.symm ∘ σ, hz_eig, h_anti, fun a ↦ ?_, fun t ht i ↦ ?_⟩
  · -- `σ` followed by `e⁻¹` carries the fibres of `b ∘ e.symm ∘ σ` onto those of `b`
    exact card_congr ((σ.trans e.symm).subtypeEquiv fun _ ↦ Iff.rfl)
  · rw [← hR_apply ⟨t, ht.le⟩]
    simp [hθ _ t ht, hτ_single]

end ExponentOfLabel
