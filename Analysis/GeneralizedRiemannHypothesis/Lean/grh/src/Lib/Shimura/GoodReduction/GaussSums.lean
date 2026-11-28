import Lib.Shimura.GoodReduction.TorsionSizes
import Lib.Shimura.Uniformisation.HolomorphicFamilies

/-!
# Hermitian tori with multiplications, Gauss sums and unfolding of the Poincaré kernel

Let `V / L` be a complex torus with multiplications `F` by a ring `R` with involution and a
polarising hermitian form `B`. The hypothesis `New.ThetaTori.IsHermitianAction` gives the
compatibilities between these data.

## Main definitions and results

* `New.ThetaTori.IsHermitianAction`: `B` is positive hermitian, its Riemann form is integral on `L`,
  `F (star a)` is adjoint to `F a`, and `star β = 1 - β`.
* `New.ThetaTori.IsHermitianAction.isAppellHumbert`: the canonical multiplier
  `New.ThetaTori.IsHermitianAction.multiplier` of `F β` gives Appell–Humbert data.
* `New.ThetaTori.IsHermitianAction.MulKernel`, `New.ThetaTori.IsHermitianAction.card_mulKernel`: the
  kernel `a⁻¹ L / L` of `a ≠ 0` on the torus has order `|det (F a)|²`.
* `New.ThetaTori.IsHermitianAction.normShift_sum_eq_char_smul`: averaging normalised translates over
  this kernel against a character gives an eigenvector.
* `New.ThetaTori.IsHermitianAction.sum_conj_pow_four_eq_sum_pow_four`: a quadratic Gauss sum over
  `κ⁻¹ L / L` has a real fourth power.
* `New.ThetaTori.IsHermitianAction.isSelfAdjoint_quotMean_pow`: the mean of `x ↦ K(c̄ x, c x)` times
  `conj (det c̄)` has a real fourth power; unfolding writes the mean as a Gauss sum times a Gaussian
  integral.

Notions from other files:
* `New.RealComplexForm.riemannForm`: The Riemann form of B: the alternating real form
  E(u, v) = Im(B(u,v) − B(v,u))/(2π).
* `New.ThetaTori.normalizedShift`: The twisted translation `New.RealComplexForm.thetaShift`,
  f ↦ (z ↦ exp(−B(x, z) − B(x, x)/2) f(z + x)), divided by the canonical multiplier at x.
* `New.IsAppellHumbert`: Appell–Humbert data: Re B is symmetric, and on L one has |χ| = 1 and
  χ(l + m) = χ(l)χ(m)·exp(πi E(m, l)), E the Riemann form of B.
* `New.IsAppellHumbert.poincareSeries`:
  K(x, y) = ∑_{l ∈ L} exp(B(x, y − x + l) − B(l,y) − B(l,l)/2)/χ(l), the sum of the terms
  `New.IsAppellHumbert.poincareTerm`.

## Relation to the literature

Known; see `Lib.Shimura.GoodReduction.MultiplicativeNorm` for sources.
-/

noncomputable section

section HermitianAction

open Complex ComplexConjugate QuotientAddGroup LinearMap LinearEquiv NeZero Algebra.IsAlgebraic

namespace New.ThetaTori

variable {V R : Type} [FinComplexSpace V] [CommRing R] [StarRing R]
  (L : Submodule ℤ V) (B : LatticeForm L) (F : R →+* V →L[ℂ] V)
  (β : R) [IsDomain R] [Module.Finite ℤ R]

/-! ### Hermitian data and invertibility of multiplications -/

/-- B : LatticeForm L is a positive definite hermitian form on V, ℂ-valued and ℂ-linear in its
second argument, with Riemann form integral on L, the action F of R on the finite-dimensional
complex space V (`FinComplexSpace V`) preserves L with ā adjoint to a, and β̄ = 1 − β. -/
structure IsHermitianAction where
  /-- Every multiplication `F a` maps the lattice `L` into itself. -/
  map_mem (a : R) : ∀ l ∈ L, F a l ∈ L
  /-- The form `B` is hermitian. -/
  conj_symm (x y : V) : B x y = conj (B y x)
  /-- The form `B` is positive definite. -/
  pos : ∀ x ≠ (0 : V), 0 < (B x x).re
  /-- The adjoint of `F a` for `B` is `F (star a)`. -/
  adjoint (a : R) (x y : V) : B (F a x) y = B x (F (star a) y)
  /-- The Riemann form of `B` takes integer values on `L`. -/
  riemannForm_integral : ∀ᵉ (l ∈ L) (m ∈ L), ∃ n : ℤ, B.riemannForm l m = n
  /-- The element `β` and its conjugate add up to `1`. -/
  star_eq_one_sub : star β = 1 - β

variable {L B F β} {x y : V} {f : V → ℂ} (h : IsHermitianAction L B F β) (a : R) [NeZero a]

/-- `star a` is nonzero when `a` is. -/
instance : NeZero (star a) := ⟨by simp [NeZero.ne a]⟩

omit [StarRing R] [IsDomain R] [Module.Finite ℤ R] in
/-- The multiplications `F r` and `F s` commute, as `R` is commutative. -/
lemma action_comm (r s : R) (x : V) : F r (F s x) = F s (F r x) := by
  simpa using DFunLike.congr_fun (congrArg F (mul_comm r s)) x

omit [StarRing R] in
/-- A nonzero element of the domain `R`, finite over `ℤ`, acts injectively on `V`. -/
lemma action_injective : (⇑(F a)).Injective := by
  -- `a` divides a nonzero integer `r`, and `F r` is multiplication by `r` on a complex space.
  obtain ⟨b, r, hr, hab⟩ := exists_smul_eq_mul ℤ 1 (NeZero.ne a)
  intro x y hxy
  have h_key : F (r • 1) (x - y) = F (a * b) (x - y) := by rw [hab]
  -- the left side is `r • (x - y)` and the right side is `F b (F a x - F a y) = 0`
  have h_smul : (r : ℂ) • (x - y) = 0 := by
    simpa [hxy, action_comm a, ← Int.cast_smul_eq_zsmul ℂ] using h_key

  exact sub_eq_zero.mp ((smul_eq_zero.mp h_smul).resolve_left (Int.cast_ne_zero.mpr hr))

omit [StarRing R] in
/-- A nonzero element of `R` acts invertibly on the finite-dimensional space `V`. -/
@[simp]
lemma action_isInvertible : (F a).IsInvertible :=
  ⟨(ofInjectiveEndo _ (action_injective a)).toContinuousLinearEquiv, rfl⟩

namespace IsHermitianAction

/-! ### Multiplier, normalised translations and kernels -/

/-- The canonical multiplier x ↦ exp(πi E(βx, x)) of the hermitian data, where E is the Riemann
form of B. The hermitian data only fix `B`, `F` and `β`. -/
@[simp]
abbrev multiplier (_ : IsHermitianAction L B F β) : V → ℂ := canonicalMultiplier B (F β)

/-- Normalised translation by x, acting on functions V → ℂ: the twisted translation
`New.RealComplexForm.thetaShift` for B, divided by exp(πi E(βx, x)), E the Riemann form of B. The
hermitian data only fix `B`, `F` and `β`. -/
@[simp]
abbrev normShift (_ : IsHermitianAction L B F β) : V → (V → ℂ) →ₗ[ℂ] V → ℂ :=
  normalizedShift B (F β)

/-- The lattice a⁻¹L: the additive subgroup of the vectors y of V with ay in L, where a acts
through F. The hermitian data only fix `L` and `F`. -/
def divLattice (_ : IsHermitianAction L B F β) (a : R) : AddSubgroup V :=
  L.toAddSubgroup.comap (F a).toAddMonoidHom

/-- The kernel a⁻¹L / L of multiplication by a on the torus V/L. -/
abbrev MulKernel : Type := h.divLattice a ⧸ L.toAddSubgroup.addSubgroupOf (h.divLattice a)

omit [IsDomain R] [Module.Finite ℤ R] [NeZero a] in
@[simp]
lemma map_divLattice_mem (z : h.divLattice a) : F a z ∈ L := z.prop

omit [IsDomain R] [Module.Finite ℤ R] [NeZero a] in
/-- The chosen representative of a class in a⁻¹L / L lies in L only for the zero class. -/
lemma out_mem_iff_eq_zero (z : h.MulKernel a) : z.out.val ∈ L ↔ z = 0 := by
  conv_rhs => rw [← out_eq' z, eq_zero_iff]
  rfl

section

omit [IsDomain R] [Module.Finite ℤ R]

/-- For hermitian data `h` and the Riemann form `E` of `B`: `E(β u, w) = E(u, w) - E(u, β w)`, so
that `F β` behaves as one half of the identity. -/
lemma riemannForm_apply_beta_eq_sub (h : IsHermitianAction L B F β) (u w : V) :
    B.riemannForm (F β u) w = B.riemannForm u w - B.riemannForm u (F β w) := by
  -- Move `F β` across the form by adjointness, and use `star β = 1 - β`.
  simp [riemannForm, h.adjoint, h.star_eq_one_sub]
  ring

/-- For hermitian data `h`, the canonical multiplier of `F β` (`h.multiplier`) and `B` are
Appell–Humbert data (`New.IsAppellHumbert`). -/
lemma isAppellHumbert (h : IsHermitianAction L B F β) : IsAppellHumbert B h.multiplier := by
  grind [isAppellHumbert_canonicalMultiplier, riemannForm_apply_beta_eq_sub, IsHermitianAction,
    conj_re]

/-- Let `x` lie in the dual lattice of `B` (`E(x, l)` is an integer for `l ∈ L`, `E` the Riemann
form) and let `F (star a) y ∈ L`. Then the phase `exp (2πi E(F a x, y))` is `1`. -/
lemma riemannPhase_eq_one (h : IsHermitianAction L B F β) {a : R} (hx : x ∈ B.dualLattice)
    (hy : F (star a) y ∈ L) :
    B.riemannPhase (F a x) y = 1 := by
  -- By adjointness the exponent is `2πi` times the integer `B.riemannForm x (F (star a) y)`.
  obtain ⟨n, hn⟩ : ∃ n : ℤ, B.riemannForm x (F (star a) y) = n := hx _ hy
  have h_adj : B.riemannForm (F a x) y = n := by grind [riemannForm_def, h.adjoint, star_star]
  simp [h_adj, mul_comm _ (n : ℂ)]

/-- For `u, w ∈ L` the normalised translations by `u` and `w` compose to that by `u + w`: on `L`
the phase in their composition law is `1`. -/
lemma normShift_normShift_of_mem (h : IsHermitianAction L B F β) {u w : V} (hu : u ∈ L)
    (hw : w ∈ L) (g : V → ℂ) : h.normShift u (h.normShift w g) = h.normShift (u + w) g := by
  rw [h.isAppellHumbert.normalizedShift_normalizedShift h.riemannForm_apply_beta_eq_sub,
    h.riemannPhase_eq_one (h.riemannForm_integral u hu) (h.map_mem _ w hw), one_smul]

/-- Let `f` be fixed by the normalised translations by `a l`, `l ∈ L`. For `z ∈ a⁻¹ L`, the chosen
representative of the class of `z` in `a⁻¹ L / L` gives the same translate of `f` as `z`. -/
lemma normShift_map_out (h : IsHermitianAction L B F β) {a : R}
    (hf : ∀ l ∈ L, h.normShift (F a l) f = f) (z : h.divLattice a) :
    h.normShift (F a ((z : h.MulKernel a).out : V)) f = h.normShift (F a (z : V)) f := by
  -- the representative is `z + l` with `l ∈ L`, and the translation by `a l` fixes `f`
  obtain ⟨l, hl⟩ : ∃ l : L.toAddSubgroup.addSubgroupOf (h.divLattice a),
      (z : h.MulKernel a).out = z + l := mk_out_eq_add (L.toAddSubgroup.addSubgroupOf _) z
  have hz_mem : F a (z : V) ∈ L := z.property
  have hl_mem : ((l : h.divLattice a) : V) ∈ L := l.property
  rw [hl, AddSubgroup.coe_add, map_add,
    ← normShift_normShift_of_mem h hz_mem (h.map_mem a _ hl_mem), hf _ hl_mem]

/-- The canonical multiplier written with `B` and `F (star β)`, without the Riemann form: it equals
`exp (B x (F (star β) x) - B x x / 2)`. -/
lemma multiplier_eq_exp (h : IsHermitianAction L B F β) :
    h.multiplier x = exp (B x (F (star β) x) - B x x / 2) := by
  grind [canonicalMultiplier, h.isAppellHumbert.sub_eq_riemannForm, h.star_eq_one_sub, h.adjoint]

/-- Hermitian data stay hermitian data when `B` is multiplied by a positive integer `m`. -/
lemma nsmul (h : IsHermitianAction L B F β) {m : ℕ} (hm : m ≠ 0) :
    IsHermitianAction L (m • B) F β := by
  refine ⟨h.map_mem, fun x y ↦ ?_, fun x hx ↦ ?_, fun a x y ↦ ?_,
    (h.isAppellHumbert.nsmul m).le_dualLattice, h.star_eq_one_sub⟩
  · -- `m • B` is hermitian
    simp [← h.conj_symm]
  · -- `m • B` is positive definite
    simp [hm.pos, h.pos x hx]
  · -- `F (star a)` is adjoint to `F a` for `m • B`
    simp [h.adjoint]

end

variable [IsFullRankLattice L]

include h

/-! ### Finite kernels and their eigenvectors -/

/-- For hermitian data `h` and a full-rank lattice `L`, the kernel `a⁻¹ L / L` of multiplication by
`a ≠ 0` has order `det (F a) * conj (det (F a))`. -/
lemma card_mulKernel : Nat.card (h.MulKernel a) = (F a).det * conj (F a).det :=
  relIndex_comap_eq_det_mul_conj_det (h.map_mem a) (action_injective a)

instance : Fintype (h.MulKernel a) :=
  -- The index is `|det (F a)|²`, which is not zero as `F a` is injective.
  AddSubgroup.fintypeOfIndexNeZero (ne_of_apply_ne _ ((h.card_mulKernel a).trans_ne
    (by simp [det_eq_zero_iff_ker_ne_bot, ker_eq_bot, action_injective])))

/-- Let `h` be hermitian data and `a ≠ 0`. Let `f` be fixed by the normalised translations by `a l`,
`l ∈ L`, let `ξ` be a character of the finite kernel `a⁻¹ L / L`, and let
`s = ∑_k ξ(−k) • (normalised translate of f by a k.out)`, where `k.out` is the chosen
representative of the class `k`; the terms do not depend on that choice. For `y ∈ a⁻¹ L`, the
normalised translation by `a y` multiplies `s` by `ξ(y)`. -/
lemma normShift_sum_eq_char_smul (hf : ∀ l ∈ L, h.normShift (F a l) f = f)
    (ξ : AddChar (h.MulKernel a) ℂ) (y : h.divLattice a) {s : V → ℂ}
    (hs : s = ∑ k : h.MulKernel a, ξ (-k) • h.normShift (F a k.out) f) :
    h.normShift (F a y) s = ξ y • s := by
  -- Reindex the sum by `k ↦ y + k` and compare term by term.
  rw [hs, map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (.addLeft ↑y) _ _ fun k ↦ ?_
  -- `y + k.out` represents `y + k`; its translate is that by `k.out` followed by that by `y`.
  have h_class : ((y + k.out : h.divLattice a) : h.MulKernel a) = y + k := by simp
  have h_term : h.normShift (F a ((y : h.MulKernel a) + k).out) f =
      h.normShift (F a y) (h.normShift (F a k.out) f) := by
    rw [← h_class, normShift_map_out h hf, AddSubgroup.coe_add, map_add,
      normShift_normShift_of_mem h (h.map_divLattice_mem a y) (h.map_divLattice_mem a k.out)]
  show h.normShift (F a y) (ξ (-k) • h.normShift (F a k.out) f) =
    ξ y • ξ (-(y + k)) • h.normShift (F a ((y : h.MulKernel a) + k).out) f
  rw [h_term, _root_.map_smul, smul_smul, ← ξ.map_add_eq_mul, neg_add, add_neg_cancel_left]

end IsHermitianAction

end New.ThetaTori

end HermitianAction

/-!
## Gauss sums and the mean of the Poincaré kernel

Here `K = h.isAppellHumbert.poincareSeries` is the Poincaré kernel for the multiplier
`h.multiplier`, and `New.quotMean` is the mean over `V / L` (total mass one).
-/

namespace New.ThetaTori.IsHermitianAction

open Complex ComplexConjugate Matrix Module MeasureTheory ComplexOrder QuotientAddGroup Fintype Fock

variable {V R : Type} [FinComplexSpace V] [CommRing R] [StarRing R]
  {L : Submodule ℤ V} {B : LatticeForm L} {F : R →+* V →L[ℂ] V} {β : R}
  (h : IsHermitianAction L B F β) {x y : V}

/-- The fourth power of a Gauss sum is real. Let `h` be hermitian data, `κ ≠ 0`, and let `q` be a
function on the finite group `κ⁻¹ L / L` with `q z = exp (B x (F r x))` for every lift `x ∈ κ⁻¹ L`
of `z`. Then the sums of `q` and of its complex conjugate have the same fourth power. -/
lemma sum_conj_pow_four_eq_sum_pow_four [IsFullRankLattice L] [IsDomain R] [Module.Finite ℤ R]
    {κ r : R} [NeZero κ] (q : h.MulKernel κ → ℂ)
    (hq : ∀ x : h.divLattice κ, q x = exp (B x (F r x))) :
    (∑ z : h.MulKernel κ, conj (q z)) ^ 4 = (∑ z : h.MulKernel κ, q z) ^ 4 := by
  -- With `N` the order of the group, `q z ^ N ^ 2 = 1`, so `conj (q z) = q z ^ (N ^ 2 - 1)`. Write
  -- `N ^ 2 - 1` as a sum of four squares; the quaternion matrix `M` with `M Mᵀ = N ^ 2 - 1`
  -- permutes the quadruples `p`, and it turns the product of the `q (p i)` into its
  -- `(N ^ 2 - 1)`-th power.
  set N : ℕ := card (h.MulKernel κ) with hN
  have q_pow (z : h.MulKernel κ) : q z ^ N ^ 2 = 1 := by
    obtain ⟨x, rfl⟩ := mk_surjective z
    -- Both `N • x` and `0` are lifts of `0`.
    have h_one : exp (B (N • x) (F r (N • x))) = 1 := by
      simpa [hN, hq, ← mk_zero] using (hq (N • x)).symm
    simpa [hq, sq, ← exp_nsmul, pow_mul] using h_one
  have q_conj (z : h.MulKernel κ) : conj (q z) = q z ^ (N ^ 2 - 1) := by
    -- `q z` is a root of unity, so its conjugate is its inverse `q z ^ (N ^ 2 - 1)`
    have h_mul : q z ^ (N ^ 2 - 1) * q z = 1 := by simpa [pow_sub_one_mul, hN] using q_pow z
    rw [← inv_eq_conj (norm_eq_one_of_pow_eq_one (q_pow z) (by simp [hN])),
      inv_eq_of_mul_eq_one_left h_mul]
  obtain ⟨a, b, c, d, h_sq⟩ := (N ^ 2 - 1).sum_four_squares
  let M : Matrix (Fin 4) (Fin 4) ℤ := !![(a : ℤ), b, c, d; -b, a, -d, c; -c, d, a, -b; -d, -c, b, a]
  -- On a group killed by `N`, `M Mᵀ = N ^ 2 - 1` acts as `-1`, so `-Mᵀ` is a right inverse of `M`.
  have M_surj : Function.Surjective fun p : Fin 4 → h.MulKernel κ ↦ M • p := by
    refine fun p ↦ ⟨-Mᵀ • p, funext fun j ↦ ?_⟩
    calc (M • -Mᵀ • p) j = (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) • -p j := by
          fin_cases j <;> simp [M, Fin.sum_univ_four] <;> module
      -- `↓`: rewrite by `h_sq` before simp takes the sum of squares apart
      _ = p j := by simp [↓h_sq, hN, sq, sub_nsmul, NeZero.one_le, mul_smul]
  have prod_M (p : Fin 4 → h.MulKernel κ) : ∏ i, q (p i) ^ (N ^ 2 - 1) = ∏ i, q ((M • p) i) := by
    obtain ⟨y, rfl⟩ := mk_surjective.comp_left p
    -- Expand both exponents; since `Mᵀ M = N ^ 2 - 1` as well, the mixed terms cancel.
    simp [← mk_zsmul, ← mk_add, hq, ← h_sq, ← Complex.exp_nsmul, ← exp_sum, M, Fin.sum_univ_four]
    grind
  simp only [q_conj, sum_pow, prod_M]
  exact Finset.sum_bijective (fun p ↦ M • p) (Finite.surjective_iff_bijective.mp M_surj)
    (by simp) (by simp)

include h

/-- For hermitian data `h` and `x, y ∈ L`, the number `B x y - B y x` lies in `2 π i ℤ`, so adding
it does not change an exponential: `s = t + B x y - B y x` gives `exp s = exp t`. -/
lemma exp_eq_of_mem_lattice {s t : ℂ} (hx : x ∈ L) (hy : y ∈ L) (hst : s = t + B x y - B y x) :
    exp s = exp t := by
  grind [exp_eq_exp_iff_exists_int, h.riemannForm_integral, h.isAppellHumbert.sub_eq_riemannForm,
    ofReal_intCast]

/-- For hermitian data `h`, the Poincaré kernel `K` (`h.isAppellHumbert.poincareSeries`) under
translation of its first argument by a lattice vector `l`:
`K(x + l, y) = χ(l)⁻¹ exp (-(B l x + B l l / 2)) K(x, y)`, with `χ = h.multiplier`. -/
lemma poincareSeries_add (l : V) (hl : l ∈ L) :
    h.isAppellHumbert.poincareSeries (x + l) y =
      (h.multiplier l)⁻¹ * exp (-(B l x + B l l / 2)) * h.isAppellHumbert.poincareSeries x y := by
  -- Shift the summation index by `l`; each term then changes by the same factor.
  calc
    _ = ∑' m : L, h.isAppellHumbert.poincareTerm (x + l) y (m + ⟨l, hl⟩) :=
      ((Equiv.addRight (⟨l, hl⟩ : L)).tsum_eq _).symm
    _ = ∑' m : L,
        (h.multiplier l)⁻¹ * exp (-(B l x + B l l / 2)) * h.isAppellHumbert.poincareTerm x y m := by
      refine tsum_congr fun m ↦ ?_
      simp [IsAppellHumbert.poincareTerm, h.isAppellHumbert.semicharacter, hl, ← exp_add, field]
      -- what remains is an identity of exponents, with `B u v - B v u` written by the Riemann form
      grind [h.isAppellHumbert.sub_eq_riemannForm]
    _ = _ := tsum_mul_left

/-- For hermitian data `h`, the function `x ↦ K(ā (x + w), a (x + w))` is continuous and
`L`-periodic, where `K` is the Poincaré kernel and `ā = star a`. -/
lemma isContPeriodic_poincareSeries [IsFullRankLattice L] (a : R) (w : V) :
    IsContPeriodic L.toAddSubgroup fun x : V ↦
      h.isAppellHumbert.poincareSeries (F (star a) (x + w)) (F a (x + w)) := by
  obtain ⟨-, h_cont, h_theta, -⟩ := h.isAppellHumbert.poincareSeries_mem_thetaSpace_and_quotMean
    h.pos
  refine ⟨by fun_prop, fun l hl x ↦ ?_⟩
  -- Both arguments move by lattice vectors: use `poincareSeries_add` in the first, the theta
  -- relation in the second. As `star a` is adjoint to `a`, the two factors of automorphy cancel.
  simp only [add_rotate l, map_add _ (x + w), h.poincareSeries_add, (h_theta _).2, h.map_mem _ l hl]
  simp [canonicalMultiplier, riemannForm, action_comm, h.adjoint, exp_neg, exp_add, field]

/-- For hermitian data `h` and `κ = c - star c`, let `α = star β * κ - c`. On `κ⁻¹ L` the number
`exp (B x (F (κ * α) x))` depends only on the class of `x` modulo `L`. -/
private lemma exp_mul_sub_eq_of_sub_mem {c κ : R} (hκ : κ = c - star c) (x : h.divLattice κ)
    (y : V) (hxy : (x : V) - y ∈ L) :
    exp (B x (F (κ * (star β * κ - c)) x)) = exp (B y (F (κ * (star β * κ - c)) y)) := by
  -- the two exponents differ by `B u v - B v u` for two lattice vectors `u`, `v`
  have h_mem : F (star β * κ - c) (F κ x - F (β * κ) ((x : V) - y)) ∈ L :=
    h.map_mem _ _ (sub_mem x.property (h.map_mem (β * κ) _ hxy))
  refine h.exp_eq_of_mem_lattice hxy h_mem ?_
  simp [hκ, h.adjoint, action_comm, h.star_eq_one_sub]
  ring

variable [IsFullRankLattice L] [IsDomain R] [Module.Finite ℤ R]

-- `seal Finset.sum` keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- For hermitian data `h` and `κ = c - star c ≠ 0`, with `α = star β * κ - c`: the Poincaré
kernel `K(c̄ x, c x)` is the sum over `l ∈ L` of the Gauss sums
`∑ z, exp (B z (F (κ α) z)) * exp (B w (F (κ c) w))`, `w = l + x + z`, over representatives `z` of
`κ⁻¹ L / L`. -/
private lemma hasSum_poincareSeries_mulKernel {c κ : R} [NeZero κ] (hκ : κ = c - star c) (x : V) :
    HasSum (fun l : L ↦ ∑ z : h.MulKernel κ,
        exp (B z.out (F (κ * (star β * κ - c)) z.out)) *
          exp (B ((l : V) + x + z.out) (F (κ * c) ((l : V) + x + z.out))))
      (h.isAppellHumbert.poincareSeries (F (star c) x) (F c x)) := by
  obtain ⟨h_summable, -, -, -, -⟩ := h.isAppellHumbert.poincareSeries_mem_thetaSpace_and_quotMean
    h.pos
  -- `(l, z) ↦ z.out + l` identifies `L × κ⁻¹ L / L` with `κ⁻¹ L` (representatives of the classes)
  let e_rep : L × h.MulKernel κ ≃ h.divLattice κ :=
    ((preimageMkEquivAddSubgroupProdSet (L.toAddSubgroup.addSubgroupOf (h.divLattice κ))
        Set.univ).trans
      (.prodCongr (L.toAddSubgroup.addSubgroupOfEquivOfLe (h.map_mem κ)).toEquiv
        (Equiv.Set.univ _))).symm.trans (Equiv.Set.univ _)
  -- and multiplication by `κ` identifies `κ⁻¹ L` with `L`
  let e_mul : h.divLattice κ ≃ L :=
    (LinearEquiv.ofInjectiveEndo _ (action_injective κ)).subtypeEquivOfSubtype
  -- the series of `K(c̄ x, c x)`, reindexed by `(l, z) ↦ κ (z.out + l)`, summed over the fibres
  have h_reindexed : HasSum (fun p : L × h.MulKernel κ ↦
      h.isAppellHumbert.poincareTerm (F (star c) x) (F c x) (e_mul (e_rep p)))
      (h.isAppellHumbert.poincareSeries (F (star c) x) (F c x)) :=
    (e_rep.trans e_mul).hasSum_iff.mpr (h_summable _ _).hasSum
  refine h_reindexed.prod_fiberwise fun l ↦ (hasSum_fintype _).congr_fun fun z ↦ ?_
  -- The term of index `κ w`, `w = z.out + l`, is `exp (B w (F (κ α) w)) * exp (B v (F (κ c) v))`,
  -- `v = w + x`: compare the exponents.
  change h.isAppellHumbert.poincareTerm _ _ ⟨F κ (z.out + l), _⟩ = _
  -- `↓`: apply the class invariance of the Gauss factor before simp unfolds the exponentials
  simp [↓h.exp_mul_sub_eq_of_sub_mem hκ _ (z.out + l), ← exp_add, h.multiplier_eq_exp, ← exp_sub,
    hκ, h.adjoint, action_comm, IsAppellHumbert.poincareTerm]
  grind

/-- Let `h` say that `B` is a positive definite hermitian form whose Riemann form is integral on the
full-rank lattice `L`, and that `F` is an action of `R` preserving `L` with `F (star a)` adjoint to
`F a` and `star β = 1 - β`. Let `K(x, y) = ∑_{l ∈ L} exp(B(x, y - x + l) - B(l, y) - B(l,
l)/2) / χ(l)` be the Poincaré series of the Appell–Humbert data `h.isAppellHumbert`, and let
`κ = c - star c` be non-zero. Then the mean over `V / L` of `x ↦ K(c̄ x, c x)`, where `c̄ = star c`,
times the complex conjugate of the determinant of `F c̄` on `V`, has a real fourth power. -/
lemma isSelfAdjoint_quotMean_pow (c : R) {κ : R} [NeZero κ] (hκ : κ = c - star c) :
    IsSelfAdjoint
      ((quotMean L.toAddSubgroup
          (fun x : V ↦ h.isAppellHumbert.poincareSeries (F (star c) x) (F c x)) *
        conj (F (star c)).det) ^ 4) := by
  -- Write the terms of the series as `l = κ z`, `z ∈ κ⁻¹ L`. Unfolding turns the mean into a Gauss
  -- sum over `h.MulKernel κ` times a Gaussian integral over `V`, divided by the covolume of `L`.
  -- The integral is `1 / conj (det (M κ) * det c̄)`, with `M κ` the matrix of `B x (κ y)`; the
  -- Gauss sum and `det (M κ)` have real fourth powers.
  borelize V
  -- `μ` is Lebesgue measure on `V` in the coordinates `e` of a basis `b`, divided by `π ^ dim V`.
  let b : Basis (Fin (finrank ℂ V)) ℂ V := finBasis ℂ V
  let e : (Fin (finrank ℂ V) → ℂ) ≃L[ℂ] V := b.equivFun.symm.toContinuousLinearEquiv
  let μ : Measure V := (normalizedVolume _).map e
  have : DiscreteTopology L.toAddSubgroup := inferInstanceAs (DiscreteTopology L)
  have : IsFiniteMeasure (L.toAddSubgroup.quotMeasure μ) :=
    isFiniteMeasure_addOrbitMeasure μ isCocompact_of_isFullRankLattice
  -- `M a` is the matrix of the form `(x, y) ↦ B x (a y)` in the basis `b`.
  let M (a : R) : Matrix (Fin (finrank ℂ V)) (Fin (finrank ℂ V)) ℂ :=
    (.pi (fun i ↦ B (b i)) ∘ₗ (F a).toLinearMap ∘ₗ e.toLinearEquiv.toLinearMap).toMatrix'
  have M_adj (a : R) : (M a)ᴴ = M (star a) := by ext; simp [M, e, ← h.conj_symm, h.adjoint]
  have M_form (a : R) (x : Fin (finrank ℂ V) → ℂ) :
      star x ⬝ᵥ M a *ᵥ x = conj (B (F a (e x)) (e x)) := by
    simp [M, e, dotProduct, ← h.conj_symm]
  have M_mul : M (κ * star c) = M κ * (F (star c)).toMatrix b b := by
    -- `F (κ c̄) = F κ ∘ F c̄`, and the matrix of a composite is the product
    refine .trans ?_ (LinearMap.toMatrix'_mul ..)
    ext; simp [M, e]
  -- Since `κ c̄ + κ̄ c = κ̄ κ`, this hermitian form is `B (κ x) (κ x)`.
  have h_pos : ((M (κ * star c))ᴴ + (M (κ * star c))ᴴᴴ).PosDef := by
    refine .of_dotProduct_mulVec_pos (isHermitian_add_transpose_self _) fun x _ ↦ ?_
    have hx : F κ (e x) ≠ 0 := by simpa [map_eq_zero_iff, action_injective]
    refine (zero_lt_real.mpr (h.pos _ hx)).trans_eq ?_
    simp [re_eq_add_conj, h.adjoint, ← h.conj_symm, M_adj, M_form, hκ, add_mulVec]
    ring
  obtain ⟨h_det_M, h_det_c⟩ : (M κ).det ≠ 0 ∧ (F (star c)).det ≠ 0 := by
    simpa [M_mul, and_comm] using IsAccretive.det_ne_zero h_pos
  -- `M κ` is skew-hermitian, as `κ̄ = -κ`.
  have h_real : conj (M κ).det ^ 4 = (M κ).det ^ 4 := by
    have h_star : star κ = -κ := by rw [hκ, star_sub, star_star, neg_sub]
    have h_skew : (M κ)ᴴ = -M κ := by rw [M_adj, h_star]; ext; simp [M]
    have h_four : (M κ)ᴴ ^ 4 = M κ ^ 4 := by rw [h_skew, Even.neg_pow (by decide)]
    simpa [det_pow] using congrArg det h_four
  -- `g c` is the Gaussian, and `g α` below gives the terms of the Gauss sum.
  let g (a : R) (x : V) : ℂ := exp (B x (F (κ * a) x))
  have h_gauss : ∫ x, g c x ∂μ = (conj (M κ).det)⁻¹ * (conj (F (star c)).det)⁻¹ := by
    -- This is `integral_gauss` for `(M (κ * star c))ᴴ = -M (κ * c)`.
    refine .trans ?_ ((integral_gauss h_pos 0).trans (by simp [M_mul]))
    simp (disch := fun_prop) [μ, integral_map, g, ← h.conj_symm, M_adj, M_form, hκ]
  have h_gauss_ne : ∫ x, g c x ∂μ ≠ 0 := by simp [h_gauss, h_det_M, h_det_c]
  have h_intg (z : V) (c' : ℂ) : Integrable (fun x ↦ c' * g c (x + z)) μ :=
    ((Integrable.of_integral_ne_zero h_gauss_ne).comp_add_right z).const_mul c'
  let α : R := star β * κ - c
  have h_sum (x : V) : HasSum (fun l : L ↦ ∑ z : h.MulKernel κ, g α z.out * g c (l + x + z.out))
      (h.isAppellHumbert.poincareSeries (F (star c) x) (F c x)) :=
    h.hasSum_poincareSeries_mulKernel hκ x
  -- Unfold: the mean of a sum over `L` is the integral over `V` divided by the covolume.
  rw [quotMean_tsum_eq_integral _ μ (integrable_finsetSum _ fun _ _ ↦ h_intg ..)
    (by simpa using h.isContPeriodic_poincareSeries c 0) h_sum]
  have h_sum_real :
      (∑ z : h.MulKernel κ, conj (g α z.out)) ^ 4 = (∑ z : h.MulKernel κ, g α z.out) ^ 4 :=
    -- on `κ⁻¹ L` the factor `g α` depends only on the class modulo `L`
    h.sum_conj_pow_four_eq_sum_pow_four (fun z ↦ g α z.out) fun x ↦
      h.exp_mul_sub_eq_of_sub_mem hκ _ x (eq_iff_sub_mem.mp (out_eq' (x : h.MulKernel κ)))
  -- Each translated Gaussian has the integral `h_gauss`, so the integral of the sum is the Gauss
  -- sum times that integral.
  have h_int_sum : ∫ x, ∑ z : h.MulKernel κ, g α z.out * g c (x + z.out) ∂μ =
      (∑ z : h.MulKernel κ, g α z.out) * ∫ x, g c x ∂μ := by
    rw [integral_finsetSum _ fun z _ ↦ h_intg z.out (g α z.out), Finset.sum_mul]
    simp [integral_const_mul, integral_add_right_eq_self (g c)]
  -- `conj (det c̄)` cancels; the covolume is real, and the Gauss sum and `det (M κ)` have real
  -- fourth powers.
  rw [h_int_sum, h_gauss, smul_mul_assoc, mul_assoc, inv_mul_cancel_right₀ (by simpa using h_det_c)]
  simp [IsSelfAdjoint, mul_pow, h_sum_real, h_real]

end New.ThetaTori.IsHermitianAction

end
