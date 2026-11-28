import Lib.ClassField.GaloisCohomology.KummerCyclicClasses
import Lib.PadicHodge.Crystalline.Basic

/-!
# Tame inertia, Frobenius on roots of unity over ℚ_p, the cyclotomic character, Weil pairs

This file studies how inertia and Frobenius elements act on roots of unity and on roots of a
uniformiser over a henselian local field, and in particular over `ℚ_p`. Over `ℚ_ℓ`, with `G_ℓ`
(`New.Gp ℓ`) its absolute Galois group, a Frobenius for `q` raises roots of unity of order prime to
`ℓ` to the `q`-th power, and inertia fixes them. For Weil pairs, degrees add under products and are
determined by the Galois element.

## Main definitions and results

* `New.Cohomology.exists_inertia_smul_eq_of_orbit_subset`,
  `New.IsLocalGalois.exists_inertia_smul_eq_of_pow_eq`: inertia is transitive on the roots of an
  Eisenstein polynomial, in particular on the `n`-th roots of `π`.
* `New.IsLocalGalois.tame_inertia`: the tame theorem. Characters of inertia of order prime to the
  residue characteristic are governed by the action on an `n`-th root `y` of a uniformiser `π`.
  Its three parts are `New.IsLocalGalois.stabilizer_le_ker_of_pow_eq_one`,
  `New.IsLocalGalois.exists_map_eq_pow_of_isPrimitiveRoot` and
  `New.IsLocalGalois.map_conj_eq_pow_of_isFrob`.
* `New.Selmer.apply_eq_pow_of_isFrob`: a Frobenius for `q` (`New.IsFrob`) raises a root of unity of
  order prime to `ℓ` to the `q`-th power.
* `New.Selmer.exists_inertia_cyclotomicGp_eq`: every natural number prime to `p` is a value of the
  `p`-adic cyclotomic character on inertia. Inertia permutes the primitive `p ^ (k + 1)`-th roots of
  unity transitively, and `New.Selmer.exists_cyclotomicGp_eq_of_isClosed` passes to the limit by
  compactness.
* `New.Period.IsWeilPair.eq_pow_of_isFrob`: for a homomorphism `j` from a group `Γ` to the absolute
  Galois group of `ℚ_p` and a Weil pair `(j s, m)`, the element `j s` determines `p ^ m`.

Notions from other files:
* `New.IsLocalGalois`: Γ = Gal(Ω/k), with Ω algebraically closed of characteristic 0, stabilises A,
  and A ∩ k is a discrete valuation ring with finite residue field. So k is a henselian local field.
* `New.IsUniformiser`: `π` is a uniformiser of `K` for `A`: an element of `K` lies in the maximal
  ideal of `A` exactly when its valuation is at most that of `π`.
* `New.IsFrob`: `σ` stabilises the valuation subring `A` and `σ • x ≡ x ^ q` modulo the maximal
  ideal for all `x ∈ A`.

## Relation to the literature

Known; see `Lib.ClassField.Places.LocalFields` for sources.
-/

/-!
## Tame characters of inertia and roots of a uniformiser

`A` is a valuation ring of the algebraically closed field `Ω`; `A x` means `A.valuation x`, and
`valuationVia k A π` is `A` of the image of `π` in `Ω`, and `A.valuation` is written
multiplicatively: value `1` means a unit of `A`, value below `1` the maximal ideal.
-/

namespace New

open Polynomial IsSepClosed MulAction Subgroup Cohomology Set QuotientGroup Finset

variable {Γ k Ω : Type*} [Group Γ] [Field k] [Field Ω] [Algebra k Ω] [MulSemiringAction Γ Ω]
  {A : ValuationSubring Ω} {π : kˣ} (hπ : IsUniformiser A π.val) {s : Γ} (hs : s ∈ inertiaGroup Γ A)
  {n : ℕ} (hn : A.valuation n = 1) {y : Ω} (hy : y ^ n = algebraMap k Ω π)

namespace Cohomology

/-! ### Inertia and roots of order prime to the residue characteristic -/

/-- For `s` in inertia and a unit `w` of `A`, `s • w / w ≡ 1` modulo the maximal ideal. -/
lemma valuation_smul_div_sub_one_lt_one (hs : s ∈ inertiaGroup Γ A) {w : Ω} (hw : A w = 1) :
    A (s • w / w - 1) < 1 := by
  have hw_ne : w ≠ 0 := by aesop
  obtain ⟨-, h_frob⟩ := hs
  simpa [div_sub_one hw_ne, hw] using h_frob w

/-- Let `s` lie in the inertia group of `A` and let `n` be a unit of `A`. If `w ^ n = u` is a unit
of `A` fixed by `s`, then `s` fixes `w`. -/
lemma inertia_fixes_root_of_unit (hs : s ∈ inertiaGroup Γ A) {n : ℕ} (hn : A.valuation n = 1)
    {w u : Ω} (hw : w ^ n = u) (hu : A.valuation u = 1) (h_fix : s • u = u) :
    s • w = w := by
  -- `s • w / w` is an `n`-th root of unity congruent to `1`, and `n` is a unit, so it is `1`.
  subst hw
  have w_unit : A.valuation w = 1 := by simpa [show n ≠ 0 by aesop] using hu
  have root : (s • w / w) ^ n = 1 := by simp [div_pow, ← smul_pow', h_fix, show w ≠ 0 by aesop]
  exact eq_of_div_eq_one
    (eq_of_val_sub_lt_one hn root (one_pow n) (valuation_smul_div_sub_one_lt_one hs w_unit))

/-- If `n` is a unit of `A` and `y ^ n = π`, then `y ≠ 0` and `n ≠ 0`. -/
lemma ne_zero_of_tame_root {n : ℕ} (hn : A.valuation n = 1) {y : Ω}
    (hy : y ^ n = algebraMap k Ω π) : y ≠ 0 ∧ NeZero n := by
  have n_ne : n ≠ 0 := by aesop
  exact ⟨by rintro rfl; simpa [n_ne] using hy.symm, ⟨n_ne⟩⟩

include hs hn hy

/-- Let `n` be a unit of `A`, that is, prime to the residue characteristic, and `y ^ n = π`
(the section hypotheses `hn`, `hy`). An element `s` of inertia (`hs`) multiplies all `n`-th roots
of `π` by the same `s • y / y`. -/
lemma smul_root_eq_ratio_mul {b : Ω} (hb : b ^ n = algebraMap k Ω π) : s • b = s • y / y * b := by
  -- `y / b` is an `n`-th root of unity, so inertia fixes it.
  have root : (y / b) ^ n = 1 := by simp [div_pow, hy, hb]
  have fixed : s • y / s • b = y / b := by
    simpa [smul_div₀'] using inertia_fixes_root_of_unit hs hn root (by simp) (by simp)
  grind [smul_ne_zero_iff_ne, ne_zero_of_tame_root hn hy, ne_zero_of_tame_root hn hb]

/-- Let `s` lie in the inertia group of `A` (`hs`), `n` be a unit of `A` (`hn`) and `y ^ n = π`
with `π` in `kˣ` (`hy`). Then `s ^ i • y / y = (s • y / y) ^ i` for every natural number `i`. -/
lemma inertia_pow_smul_div [SMulCommClass Γ k Ω] (i : ℕ) : s ^ i • y / y = (s • y / y) ^ i := by
  induction i with
  | zero => simp [ne_zero_of_tame_root hn hy]
  | succ i ih =>
    -- `s ^ i • y` is another `n`-th root of `π`, so `s` multiplies it by `s • y / y`.
    have root : (s ^ i • y) ^ n = algebraMap k Ω π := by simp [← smul_pow', hy]
    rw [pow_succ', mul_smul, smul_root_eq_ratio_mul hs hn hy root, mul_div_assoc, ih, pow_succ']

end Cohomology

include hπ

variable [TopologicalSpace Γ] [G : IsLocalGalois Γ k A]

/-! ### Transitivity of inertia on roots of a uniformiser -/

/-- For `y ≠ 0` whose orbit under inertia has `m` elements (the index of its stabiliser), the
valuation of `y ^ m` is an integral power of that of the uniformiser `π` (the section hypothesis
`hπ : IsUniformiser A π`). -/
lemma IsLocalGalois.exists_valuation_pow_inertia_index (hy_ne : y ≠ 0) :
    ∃ d : ℤ, A y ^ (stabilizer (inertiaGroup Γ A) y).index = valuationVia k A π ^ d := by
  -- The left side is the valuation of an element `c` of the fixed field of inertia
  -- (`exists_val_eq_pow_index`), and such an element has an integral order `d`.
  have h_decomp (g : inertiaGroup Γ A) : (g : Γ) ∈ decompGroup Γ A := g.property.left
  obtain ⟨⟨c, hc_fix⟩, hc : A c = A y ^ (stabilizer (inertiaGroup Γ A) y).index⟩ :=
    exists_val_eq_pow_index h_decomp y
  -- If `c = 0`, then `A y ^ index ≤ A 0 = 0`, so `A y = 0`, against `y ≠ 0`.
  have hc_ne : c ≠ 0 := by rintro rfl; simpa [hy_ne] using hc.ge
  obtain ⟨d, hd⟩ : ∃ d : ℤ, ordRat k A (.ofMul (.mk0 c hc_ne)) = d :=
    G.exists_ordRat_eq_intCast fun g hg ↦ DiscreteUnits.ext (hc_fix ⟨g, hg⟩)
  have h_val : A c ^ 1 = valuationVia k A π ^ d :=
    (hπ.valuation_pow_eq_zpow_iff_mul_ordRat_eq G (x := .ofMul (.mk0 c hc_ne)) 1 d).mpr
      (by simpa using hd)
  exact ⟨d, by simpa [hc] using h_val⟩

/-- Eisenstein's criterion over the fixed field of inertia: if `x ^ n` has the valuation of the
uniformiser `π` (the section hypothesis `hπ`) and the inertia orbit of `x` lies in a set `T` of at
most `n` elements, then every `y` in `T` is `g • x` for some `g` in inertia. -/
lemma Cohomology.exists_inertia_smul_eq_of_orbit_subset {x y : Ω} {T : Finset Ω} {n : ℕ}
    (hT_card : #T ≤ n) (hx : valuationVia k A π = A x ^ n)
    (h_orbit : ∀ g : inertiaGroup Γ A, g.val • x ∈ T) (hy : y ∈ T) :
    ∃ g ∈ inertiaGroup Γ A, g • x = y := by
  -- `A x ^ n` is the valuation of `π`, which is below `1`; so `x ≠ 0` and `A x ≠ 1`.
  have val_lt : valuationVia k A π < 1 := hπ.valuationVia_lt_one
  -- (`n = 0` is impossible: then `π` would have valuation `1`.)
  have ⟨x_ne, val_ne⟩ : x ≠ 0 ∧ A.valuation x ≠ 1 := by
    cases n with
    | zero => aesop
    | succ n => aesop
  have orbit_sub : orbit (inertiaGroup Γ A) x ⊆ T := forall_mem_range.mpr h_orbit
  -- `A.valuation x ^ #orbit` is a power of `A.valuation π = A.valuation x ^ n`, so `n` divides the
  -- orbit size.
  have dvd : n ∣ (orbit (inertiaGroup Γ A) x).ncard := by
    obtain ⟨d, hd⟩ := G.exists_valuation_pow_inertia_index hπ x_ne
    -- `A x ^ index = A x ^ (n * d)`; as `A x` is neither `0` nor `1`, `index = n * d`.
    have h_index : ((orbit (inertiaGroup Γ A) x).ncard : ℤ) = n * d := by
      rw [← index_stabilizer]
      refine zpow_right_injective₀ (zero_lt_iff.2 (by simpa using x_ne)) val_ne ?_
      simp only [zpow_natCast, hd, hx, zpow_mul]
    exact Int.ofNat_dvd.1 ⟨d, h_index⟩
  have card_le : (T : Set Ω).ncard ≤ (orbit (inertiaGroup Γ A) x).ncard :=
    mod_cast hT_card.trans <|
      n.le_of_dvd ((nonempty_orbit x).ncard_pos (T.finite_toSet.subset orbit_sub)) dvd
  have orbit_eq : orbit (inertiaGroup Γ A) x = T := eq_of_subset_of_ncard_le orbit_sub card_le
  obtain ⟨g, hg⟩ : ∃ g : inertiaGroup Γ A, g • x = y := orbit_eq.ge hy
  exact ⟨g, g.property, hg⟩

/-- Let `Γ` be the Galois group of `Ω / k`, where `Ω` is algebraically closed of characteristic 0,
`Γ` stabilises the valuation subring `A`, and `A ∩ k` is a discrete valuation ring with finite
residue field (`IsLocalGalois`), and let `π` be a uniformiser of `k` for `A`. For `n > 0`, if
`x ^ n = π` and `y ^ n = x ^ n`, then some element `g` of the inertia group of `A` satisfies
`g • x = y`, so inertia acts transitively on the `n`-th roots of `π`.

This is the surjectivity in the structure theorem for tame inertia, at each finite level `n > 0`, in
characteristic 0. -/
lemma IsLocalGalois.exists_inertia_smul_eq_of_pow_eq {x y : Ω} {n : ℕ} (hn_pos : 0 < n)
    (hx : x ^ n = algebraMap k Ω π) (hy : y ^ n = x ^ n) :
    ∃ g ∈ inertiaGroup Γ A, g • x = y := by
  classical
  -- The orbit of `x` lies in the set of the at most `n` roots of `X ^ n - x ^ n`.
  let R := (nthRoots n (x ^ n)).toFinset
  have card_le : #R ≤ n := (Multiset.toFinset_card_le _).trans (card_nthRoots n (x ^ n))
  have h_val : valuationVia k A π = A x ^ n := by simp [valuationVia, ← hx]
  have h_orbit (g : inertiaGroup Γ A) : (g : Γ) • x ∈ R := by simp [R, hn_pos, hx, ← smul_pow']
  exact exists_inertia_smul_eq_of_orbit_subset hπ card_le h_val h_orbit (by simp [R, hn_pos, hy])

/-- Let `f` be a homomorphism on inertia with open kernel of index dividing `n ^ M`, with
`f g ^ n = 1` for all `g`; let `n` be a unit of `A` and `y₁ ^ (n ^ M * n) = π` for the
uniformiser `π` (the section hypothesis `hπ`). Then every element of inertia that fixes `y₁` lies
in the kernel of `f`. -/
private lemma IsLocalGalois.stabilizer_le_ker_of_pow_eq {P : Type*} [Monoid P] {n : ℕ}
    (hn : A.valuation n = 1) (f : inertiaGroup Γ A →* P) (hf : f.ker.IsOpen)
    (hP : ∀ g : inertiaGroup Γ A, f g ^ n = 1) {M : ℕ} (card_dvd : f.ker.index ∣ n ^ M) {y₁ : Ω}
    (hy : y₁ ^ (n ^ M * n) = algebraMap k Ω π) :
    stabilizer (inertiaGroup Γ A) y₁ ≤ f.ker := by
  have h_fact : Fact f.ker.IsOpen := ⟨hf⟩
  obtain ⟨y₁_ne, ⟨N_ne⟩⟩ :=
    ne_zero_of_tame_root (A := A) (n := n ^ M * n) (by aesop) hy
  have hn_ne : NeZero n := ⟨right_ne_zero_of_mul N_ne⟩
  -- By Galois theory it is enough that an `r` fixing `y₁` fixes the fixed field of `f.ker`.
  intro r hr
  refine (fixingSubgroup_fixedFieldOf f.ker).le fun ⟨x, hx⟩ ↦ ?_
  apply eq_of_sub_eq_zero
  by_contra h_ne
  -- Otherwise `r x - x`, which `f.ker` fixes, has an orbit of size dividing `n ^ M * n`. As
  -- `y₁ ^ (n ^ M * n) = π`, it has the valuation of a power of `y₁`.
  have ker_le : f.ker ≤ stabilizer (inertiaGroup Γ A) (r • x - x) :=
    fun g hg ↦ mem_stabilizer_iff.2 (sub_mem (smul_mem_fixedPoints_of_normal r hx) hx ⟨g, hg⟩)
  obtain ⟨m, hm⟩ : (stabilizer (inertiaGroup Γ A) (r • x - x)).index ∣ n ^ M * n :=
    (index_dvd_of_le ker_le).trans (card_dvd.mul_right n)
  obtain ⟨d, hd⟩ := G.exists_valuation_pow_inertia_index hπ h_ne
  let w : Ω := (r • x - x) / y₁ ^ (m * d)
  have w_unit : A.valuation w = 1 := by
    simp_all [w, valuationVia, ← hy, zpow_mul, ← zpow_natCast, zpow_comm, zpow_left_inj₀,
      zpow_ne_zero]
  -- Each `r ^ i • w / w` is `1` modulo the maximal ideal, but their sum over `i < n`
  -- telescopes to a multiple of `r ^ n • x - x = 0`. So `n` would not be a unit.
  have pow_fix : r ^ n • x = x := hx ⟨r ^ n, by simp [hP]⟩
  have sum_eq : ∑ i ∈ range n, ((r ^ i).1 • w / w - 1) = -n := by
    -- `↓` rewrites the subgroup action before simp splits the sum
    simp [w, smul_div₀', ← sum_div, smul_sub, smul_smul, smul_eq_self_of_mem_zpowers _ hr,
      ← pow_succ, ↓← Subgroup.smul_def, sum_range_sub (r ^ · • x), pow_fix]
  have h_sum_lt : A.valuation (∑ i ∈ range n, ((r ^ i).1 • w / w - 1)) < 1 :=
    A.valuation.map_sum_lt' one_pos fun i _ ↦ valuation_smul_div_sub_one_lt_one (r ^ i).2 w_unit
  simp only [sum_eq, Valuation.map_neg, hn, lt_self_iff_false] at h_sum_lt

/-! ### The tame theorem -/

omit hπ [TopologicalSpace Γ] in
/-- A `q`-Frobenius normalises inertia: it stabilises `A`, so it conjugates inertia into itself. -/
lemma IsFrob.conj_mem_inertiaGroup {q : ℕ} {φ : Γ} (hφ : IsFrob A q φ) (s : inertiaGroup Γ A) :
    φ * s * φ⁻¹ ∈ inertiaGroup Γ A := by
  have h_conj := s.property.conj φ
  open Pointwise in rw [MulAction.mem_stabilizer_iff.mp hφ.1] at h_conj
  exact h_conj

omit hπ in
/-- If `f` is trivial on the stabiliser of `y` in inertia (where `y ^ n = π`), then `f g = f s ^ i`
whenever `g` moves `y` by the `i`-th power of the ratio by which `s` moves it. -/
private lemma map_eq_pow_of_smul_div_eq (hn : A.valuation n = 1) (hy : y ^ n = algebraMap k Ω π)
    {P : Type*} [Monoid P] {f : inertiaGroup Γ A →* P}
    (h_stab : stabilizer (inertiaGroup Γ A) y ≤ f.ker) (s g : inertiaGroup Γ A) (i : ℕ)
    (h_eq : (g : Γ) • y / y = ((s : Γ) • y / y) ^ i) : f g = f s ^ i := by
  obtain ⟨y_ne, _⟩ := ne_zero_of_tame_root hn hy
  refine (f.eq_iff.mpr (h_stab ?_)).trans (map_pow f s i)
  simp_all [mul_smul, ← inertia_pow_smul_div s.property hn hy, Subgroup.smul_def]

omit hπ in
/-- First part of the tame theorem. Let `k` be a local field (`New.IsLocalGalois Γ k A`), `π` a
uniformiser of `k`, `n` a unit of `A` and `y ^ n = π`. A homomorphism `f` on inertia with open
kernel and `f g ^ n = 1` for all `g` is trivial on the stabiliser of `y` in inertia, so `f g`
depends only on `g y / y`. -/
lemma IsLocalGalois.stabilizer_le_ker_of_pow_eq_one (hπ : IsUniformiser A π.val)
    (hn : A.valuation n = 1) (hy : y ^ n = algebraMap k Ω π) {P : Type*} [Monoid P]
    (f : inertiaGroup Γ A →* P) (hf : f.ker.IsOpen) (hP : ∀ g : inertiaGroup Γ A, f g ^ n = 1) :
    stabilizer (inertiaGroup Γ A) y ≤ f.ker := by
  obtain ⟨y_ne, _⟩ := ne_zero_of_tame_root hn hy
  -- The image of `f` has order dividing some `n ^ M`; pass to a root `y₁` with `y₁ ^ n ^ M = y`.
  obtain ⟨M, card_dvd⟩ : ∃ M : ℕ, f.ker.index ∣ n ^ M := by
    have h_finite := quotient_finite_of_isOpen _ hf
    -- Every element of the finite quotient by `f.ker` has order dividing `n`.
    exact IsPGroup.exists_card_dvd_pow fun g ↦ ⟨1, g.ind' (by simp [← mk_pow, hP])⟩
  obtain ⟨y₁, rfl⟩ := exists_pow_nat_eq y (n ^ M)
  rw [← pow_mul] at hy
  have hN : A.valuation ↑(n ^ M * n) = 1 := by aesop
  obtain ⟨y₁_ne, ⟨N_ne⟩⟩ := ne_zero_of_tame_root hN hy
  -- An `r` that fixes `y₁` fixes every `x` in the fixed field of `f.ker`, so by Galois theory it
  -- lies in `f.ker`.
  have deep : stabilizer (inertiaGroup Γ A) y₁ ≤ f.ker :=
    IsLocalGalois.stabilizer_le_ker_of_pow_eq hπ hn f hf hP card_dvd hy
  -- Now let `r` fix `y`; write `r y₁ / y₁ = ξ ^ n` and take `t` in inertia with `t y₁ = ξ y₁`.
  intro r hr
  obtain ⟨ξ, hξ⟩ : ∃ ξ : Ω, ξ ^ n = r • y₁ / y₁ := exists_pow_nat_eq _ n
  have h_pow_eq : (ξ * y₁) ^ (n ^ M * n) = y₁ ^ (n ^ M * n) := by
    simp_all [mul_pow, pow_mul' ξ, div_pow]
  obtain ⟨t, t_ine, ht⟩ := G.exists_inertia_smul_eq_of_pow_eq hπ N_ne.pos hy h_pow_eq
  -- Then `r` and `t ^ n` move `y₁` alike, so `f r = f t ^ n = 1`.
  have same : f r = f (⟨t, t_ine⟩ ^ n) := by
    refine f.eq_iff.mpr (deep ?_)
    -- `t ^ n` multiplies `y₁` by `(t y₁ / y₁) ^ n = ξ ^ n = r y₁ / y₁`, as `r` does.
    have h_ratio : (t ^ n) • y₁ / y₁ = r • y₁ / y₁ := by
      rw [inertia_pow_smul_div t_ine hN hy n, ht, mul_div_cancel_right₀ ξ y₁_ne, hξ]
    simpa [mul_smul, inv_smul_eq_iff] using ((div_left_inj' y₁_ne).mp h_ratio).symm
  rw [MonoidHom.mem_ker, same, map_pow, hP]

omit hπ in
/-- Second part of the tame theorem. Assume `IsLocalGalois Γ k A`: `Γ` is the Galois group of an
algebraically closed field `Ω` of characteristic 0 over `k`, it stabilises the valuation subring
`A`, and `A ∩ k` is a discrete valuation ring with finite residue field. Let `π` be a uniformiser of
`k` for `A`, `n` a natural number that is a unit of `A`, `y ^ n = π`, and `f` a monoid homomorphism
on the inertia group of `A` with open kernel and `f g ^ n = 1` for all `g`. If `s` is in inertia and
`s • y / y` is a primitive `n`-th root of unity, then every value `f g` is a power `f s ^ i`. -/
lemma IsLocalGalois.exists_map_eq_pow_of_isPrimitiveRoot (hπ : IsUniformiser A π.val)
    (hn : A.valuation n = 1) (hy : y ^ n = algebraMap k Ω π) {P : Type*} [Monoid P]
    (f : inertiaGroup Γ A →* P) (hf : f.ker.IsOpen) (hP : ∀ g : inertiaGroup Γ A, f g ^ n = 1)
    (s : inertiaGroup Γ A) (hs_prim : IsPrimitiveRoot (s • y / y) n) (g : inertiaGroup Γ A) :
    ∃ i : ℕ, f g = f s ^ i := by
  obtain ⟨y_ne, _⟩ := ne_zero_of_tame_root hn hy
  -- `g y / y` is an `n`-th root of unity, hence a power of the primitive one `s y / y`.
  have h_root : ((g : Γ) • y / y) ^ n = 1 := by simp [div_pow, ← smul_pow', hy]
  obtain ⟨i, -, h_pow⟩ := hs_prim.eq_pow_of_pow_eq_one h_root
  exact ⟨i, map_eq_pow_of_smul_div_eq hn hy (stabilizer_le_ker_of_pow_eq_one hπ hn hy f hf hP) s g i
    h_pow.symm⟩

omit hπ in
/-- Third part of the tame theorem. Assume `IsLocalGalois Γ k A`: `Γ` is the Galois group of an
algebraically closed field `Ω` of characteristic 0 over `k`, it stabilises the valuation subring
`A`, and `A ∩ k` is a discrete valuation ring with finite residue field. Let `π` be a uniformiser of
`k` for `A`, `n` a natural number that is a unit of `A`, `y ^ n = π`, and `f` a monoid homomorphism
on the inertia group of `A` with open kernel and `f g ^ n = 1` for all `g`. If `s` is in inertia and
`φ` is a `q`-Frobenius (it stabilises `A` and `φ • x ≡ x ^ q` modulo the maximal ideal for all
`x ∈ A`), then `φ s φ⁻¹` is in inertia and `f (φ s φ⁻¹) = f s ^ q`. -/
lemma IsLocalGalois.map_conj_eq_pow_of_isFrob (hπ : IsUniformiser A π.val)
    (hn : A.valuation n = 1) (hy : y ^ n = algebraMap k Ω π) {P : Type*} [Monoid P]
    (f : inertiaGroup Γ A →* P) (hf : f.ker.IsOpen) (hP : ∀ g : inertiaGroup Γ A, f g ^ n = 1)
    (s : inertiaGroup Γ A) {q : ℕ} {φ : Γ} (hφ : IsFrob A q φ) :
    f ⟨φ * s * φ⁻¹, hφ.conj_mem_inertiaGroup s⟩ = f s ^ q := by
  obtain ⟨y_ne, _⟩ := ne_zero_of_tame_root hn hy
  refine map_eq_pow_of_smul_div_eq hn hy (stabilizer_le_ker_of_pow_eq_one hπ hn hy f hf hP) s _ q ?_
  have h_root : ((s : Γ) • y / y) ^ n = 1 := by simp [div_pow, ← smul_pow', hy]
  -- `φ s φ⁻¹ y / y = φ (s y / y)`, and `φ` raises `n`-th roots of unity to the power `q`.
  simp [smul_root_eq_ratio_mul (b := _ • y) s.property hn hy, ← smul_pow', *, mul_smul,
    ← cyclotomicCharMod_eq_iff.mp (hφ.cyclotomicCharMod_eq hn)]

include hn hy in
/-- The tame theorem. Let `k` be a local field (the section instance `IsLocalGalois Γ k A`), `n` be
a unit of `A`, `y ^ n = π` a uniformiser of `k`, and `f` a homomorphism on inertia with open kernel
and `f g ^ n = 1` for all `g`. Then (a) `f` is trivial on the stabiliser of `y`, so `f g` depends
only on `g y / y`; and for `s` in inertia, (b) if `s y / y` is a primitive `n`-th root of unity,
every `f g` is a power of `f s`; (c) if `φ` is a `q`-Frobenius, `φ s φ⁻¹` is in inertia and
`f (φ s φ⁻¹) = f s ^ q`. The three parts are `New.IsLocalGalois.stabilizer_le_ker_of_pow_eq_one`,
`New.IsLocalGalois.exists_map_eq_pow_of_isPrimitiveRoot` and
`New.IsLocalGalois.map_conj_eq_pow_of_isFrob`.

Here `hπ`, `hn` and `hy` are the section hypotheses. The theorem treats one `n` at a time and does
not construct the map onto the inverse limit of roots of unity.

This is a finite-level form of the structure of tame inertia (Serre, Local Fields, IV §2), stated
for homomorphisms with open kernel that are killed by `n`. -/
lemma IsLocalGalois.tame_inertia {P : Type*} [Monoid P] (f : inertiaGroup Γ A →* P)
    (hf : f.ker.IsOpen) (hP : ∀ g : inertiaGroup Γ A, f g ^ n = 1) :
    -- (a)
    stabilizer (inertiaGroup Γ A) y ≤ f.ker ∧
    ∀ s : inertiaGroup Γ A,
      -- (b)
      (IsPrimitiveRoot (s • y / y) n → ∀ g : inertiaGroup Γ A, ∃ i : ℕ, f g = f s ^ i) ∧
      -- (c)
      ∀ (q : ℕ) (φ : Γ), IsFrob A q φ → ∃ h_mem :
      φ * s * φ⁻¹ ∈ inertiaGroup Γ A, f ⟨φ * s * φ⁻¹, h_mem⟩ = f s ^ q :=
  ⟨stabilizer_le_ker_of_pow_eq_one hπ hn hy f hf hP, fun s ↦
    ⟨exists_map_eq_pow_of_isPrimitiveRoot hπ hn hy f hf hP s, fun _ _ hφ ↦
      ⟨hφ.conj_mem_inertiaGroup s, map_conj_eq_pow_of_isFrob hπ hn hy f hf hP s hφ⟩⟩⟩

end New

namespace New.Selmer

/-!
## Roots of unity of order prime to ℓ over ℚ_ℓ

`G_ℓ` (`New.Gp ℓ`) is the absolute Galois group of `ℚ_ℓ`, and `New.intQpBar ℓ` is the valuation ring
of the algebraic closure of `ℚ_ℓ`; `intQpBar ℓ x` is the valuation of `x` for this ring.
-/

section FrobeniusOnRoots

variable {ℓ : ℕ} [Fact ℓ.Prime] {φ : Gp ℓ} {q M : ℕ} {z : PadicAlgCl ℓ}

/-- `ℓ` is a uniformiser of `ℚ_ℓ` for the valuation ring `intQpBar ℓ` of `ℚ̄_ℓ`: an element of `ℚ_ℓ`
has valuation below `1` exactly when its valuation is at most that of `ℓ`. -/
lemma isUniformiser_ell : IsUniformiser (intQpBar ℓ) (Units.mk0 (ℓ : ℚ_[ℓ]) NeZero.out).val := by
  -- In `ℚ_[ℓ]`, norm `< 1` means norm `≤ ℓ⁻¹`.
  intro x
  -- `-map_natCast`: `ℓ` must stay in `ℚ_ℓ`, where `simp` knows that its norm is `ℓ⁻¹`.
  simpa [valuation_intQpBar_lt_one_iff, valuation_intQpBar_le_iff, -map_natCast] using
    x.norm_lt_pow_iff_norm_le_pow_sub_one 0

/-- A natural number prime to `ℓ` is a unit of the valuation ring of `ℚ̄_ℓ`. -/
lemma valuation_natCast_eq_one (hM : ¬ℓ ∣ M) : intQpBar ℓ M = 1 := by
  -- The norm of `M` in `ℚ̄_ℓ` is its norm in `ℚ_ℓ`.
  rw [eq_iff_le_not_lt, valuation_intQpBar_lt_one_iff,
    ← map_natCast (algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)) M, PadicAlgCl.norm_extends]
  simpa using hM

/-- Let `φ` in `G_ℓ` be a Frobenius for `q` in the sense of `New.IsFrob`. Then `φ` sends every
`M`-th root of unity `z` to `z ^ q`, provided `M` is prime to `ℓ`. -/
lemma apply_eq_pow_of_isFrob (hφ : IsFrob (intQpBar ℓ) q φ) (hM : ¬ℓ ∣ M) (hz : z ^ M = 1) :
    φ z = z ^ q := by
  have hM_neZero : NeZero M := ⟨fun h ↦ hM (by simp [h])⟩
  -- The cyclotomic character modulo `M` takes the value `q` at `φ`.
  exact cyclotomicCharMod_eq_iff.mp (hφ.cyclotomicCharMod_eq (valuation_natCast_eq_one hM)) z hz

/-- Every element `g` of `G_ℓ` raises an `M`-th root of unity `z`, with `M` prime to `ℓ`, to some
power `ℓ ^ n`. -/
lemma exists_apply_eq_pow (hM : ¬ℓ ∣ M) (hz : z ^ M = 1) (g : Gp ℓ) :
    ∃ n : ℕ, g z = z ^ ℓ ^ n := by
  -- The condition on `g` is closed, so it is enough to check it on the products `φ ^ n * i` with
  -- `φ` a Frobenius and `i` in inertia, which are dense; these are Frobenii for `ℓ ^ n`.
  obtain ⟨⟨φ, hφ⟩, h_dense, -⟩ := (isLocalGalois_padic (p := ℓ)).frobenius_spec
  refine (h_dense hφ).induction_on g
    (isClosed_setOf_smul z fun w : PadicAlgCl ℓ ↦ ∃ n : ℕ, w = z ^ ℓ ^ n) ?_
  rintro ⟨n, i, hi⟩
  have h_frob : IsFrob (intQpBar ℓ) (ℓ ^ n) (φ ^ n * i) := by
    simpa [residueCard_padic] using (hφ.pow n).mul_iff.mpr hi
  exact ⟨n, apply_eq_pow_of_isFrob h_frob hM hz⟩

end FrobeniusOnRoots

/-!
## The p-adic cyclotomic character on inertia

`[ThePrime p]` fixes `p` as a prime; `New.cyclotomicGp` is the `p`-adic cyclotomic character of
`Gal(ℚ̄_p/ℚ_p)` and `New.inertiaGroup _ (New.intQpBar p)` its inertia group.
-/

section CyclotomicRamification

open Finset PadicInt Cohomology Units Period HasEnoughRootsOfUnity

variable {p : ℕ} [ThePrime p]

/-- Let `S ⊆ G_p` be closed and `a` a natural number. If for every `k` each primitive
`p ^ (k + 1)`-th root of unity `ζ` is sent to `ζ ^ a` by some element of `S`, then the `p`-adic
cyclotomic character `cyclotomicGp` takes the value `a` at some `g ∈ S`. -/
lemma exists_cyclotomicGp_eq_of_isClosed {S : Set (Gp p)} (a : ℕ) (hS : IsClosed S)
    (h_pow : ∀ (k : ℕ) (ζ : PadicAlgCl p), IsPrimitiveRoot ζ (p ^ (k + 1)) → ∃ g ∈ S, g ζ = ζ ^ a) :
    ∃ g ∈ S, (cyclotomicGp g).val = a := by
  -- The image of `S` under the cyclotomic character is closed, and `a` is a limit of its points.
  have h_closed : IsClosed ((fun g : Gp p ↦ (cyclotomicGp g).val) '' S) :=
    (continuous_val.comp (continuous_cyclotomicChar p)).isClosedMap _ hS
  refine (Metric.mem_of_closed' h_closed).mpr fun ε hε ↦ ?_
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (p : ℝ) ^ (-(k : ℤ)) < ε := exists_pow_neg_lt p hε
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot (PadicAlgCl p) (p ^ (k + 1))
  obtain ⟨g, hg, hgζ⟩ : ∃ g ∈ S, g ζ = ζ ^ a := h_pow k ζ hζ
  -- As `g ζ = ζ ^ a`, the character of `g` is `a` modulo `p ^ (k + 1)`, hence modulo `p ^ k`.
  refine ⟨_, ⟨g, hg, rfl⟩, hk.trans_le' ?_⟩
  rw [dist_eq_norm', norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
  exact (pow_dvd_cyclotomicChar_sub_iff k).mpr
    (cyclotomicCharMod_eq_of_dvd ⟨p, rfl⟩ (cyclotomicCharMod_eq_of_isPrimitiveRoot hζ hgζ))

/-- Every natural number `a` prime to `p` is the value of the `p`-adic cyclotomic character at some
element of the inertia group of `G_p`; that is, the extension of `ℚ_p` by all `p`-power roots of
unity is totally ramified. -/
lemma exists_inertia_cyclotomicGp_eq (a : ℕ) (h_cop : p.Coprime a) :
    ∃ g ∈ inertiaGroup (Gp p) (intQpBar p), (cyclotomicGp g).val = a := by
  classical
  refine exists_cyclotomicGp_eq_of_isClosed a isClosed_inertiaGroup fun s ξ hξ ↦ ?_
  -- `ξ - 1` is a uniformiser of `ℚ_p(ξ)`: its `totient (p ^ (s + 1))`-th power has the valuation of
  -- `p`. Its conjugates lie in the set `T` of the `totient (p ^ (s + 1))` elements `ζ - 1`, `ζ` a
  -- primitive root. So the inertia orbit of `ξ - 1` is all of `T`
  -- (`exists_inertia_smul_eq_of_orbit_subset`) and contains `ξ ^ a - 1`.
  let T : Finset (PadicAlgCl p) :=
    (primitiveRoots (p ^ (s + 1)) (PadicAlgCl p)).image fun ζ : PadicAlgCl p ↦ ζ - 1
  have card_T : #T ≤ (p ^ (s + 1)).totient := card_image_le.trans_eq hξ.card_primitiveRoots
  have mem_T : ξ ^ a - 1 ∈ T := by
    simpa [T, NeZero.pos] using hξ.pow_of_coprime a (h_cop.symm.pow_right _)
  suffices ∃ g ∈ inertiaGroup (Gp p) (intQpBar p), g • (ξ - 1) = ξ ^ a - 1 by simpa
  refine exists_inertia_smul_eq_of_orbit_subset isUniformiser_ell card_T ?_ (fun g ↦ ?_) mem_T
  · simp [← map_pow, le_antisymm_iff, valuation_intQpBar_le_iff, norm_zeta_sub_one_pow hξ]
  · simp [T, hξ.map_of_injective, AlgEquiv.injective, NeZero.pos]

end CyclotomicRamification

end New.Selmer

/-!
## Weil pairs: products, powers and uniqueness of the degree

`New.Period.IsWeilPair s m` says that `s` in the absolute Galois group of `ℚ_p` acts on the residue
field of `ℚ̄_p` as `x ↦ x ^ (1 / p ^ m)`. The lemmas concern elements `j s`, where `j` is a
homomorphism from a group `Γ` to this Galois group.
-/

namespace New.Period.IsWeilPair

variable {p : ℕ} [ι : ThePrime p] {m m' : ℕ} {Γ : Type*} {s t : Γ} [Group Γ] {j : Γ →* Gp p}

/-- Weil pairs multiply: the degrees add. -/
lemma mul (h : IsWeilPair (j s) m) (h' : IsWeilPair (j t) m') :
    IsWeilPair (j (s * t)) (m + m') := by
  simpa [IsWeilPair, p.pow_add', h'.mul_iff] using h

/-- If `(j s, m)` is a Weil pair, then so is `(j (s ^ n), n * m)`. -/
lemma pow (h : IsWeilPair (j s) m) (n : ℕ) : IsWeilPair (j (s ^ n)) (n * m) := by
  -- A Frobenius for `p ^ m` raised to the `n`-th power is a Frobenius for `(p ^ m) ^ n`.
  rw [IsWeilPair, map_pow, ← inv_pow, mul_comm n m, pow_mul]
  exact IsFrob.pow h n

/-- If `(j s, m)` is a Weil pair and `(j s)⁻¹` acts on the residue field as `x ↦ x ^ q`, then
`q = p ^ m`. -/
lemma eq_pow_of_isFrob (h : IsWeilPair (j s) m) {q : ℕ} (hq : IsFrob (intQpBar p) q (j s)⁻¹) :
    q = p ^ m := by
  -- The `l`-adic cyclotomic character of `(j s)⁻¹`, for a prime `l > p`, is both `q` and `p ^ m`
  -- (`IsFrob.cyclotomicChar_eq`: on `l`-power roots of unity a Frobenius for `q` acts as
  -- `x ↦ x ^ q`).
  obtain ⟨l, hpl, hl⟩ : ∃ l : ℕ, p.succ ≤ l ∧ l.Prime := p.succ.exists_infinite_primes
  have hl_fact : Fact l.Prime := ⟨hl⟩
  have h_not_dvd : ¬p ∣ l := (Nat.prime_dvd_prime_iff_eq ι.out hl).not.mpr (by omega)
  have hval : (intQpBar p).valuation l = 1 := Selmer.valuation_natCast_eq_one h_not_dvd
  exact_mod_cast (hq.cyclotomicChar_eq l hval).symm.trans (h.cyclotomicChar_eq l hval)

end New.Period.IsWeilPair

/-!
## Inertia and roots of unity of order prime to p

Over `ℚ_p`, inertia fixes the roots of unity of order prime to `p`
(`New.Selmer.apply_eq_self_of_mem_inertiaGroup`). For `f ≠ 0` the natural number `p ^ f - 1` is such
an order: it is nonzero (a `NeZero` instance) and prime to `p` (`New.Selmer.not_dvd_pow_sub_one`).
-/

namespace New.Selmer

open NeZero ZMod

variable {p : ℕ} [ThePrime p] {f : ℕ} [NeZero f] {g : Gp p}

omit [NeZero f] in
/-- Every element of the inertia group of `ℚ̄_p` over `ℚ_p` fixes the `f`-th roots of unity in
`ℚ̄_p`, for `f` prime to `p`. -/
lemma apply_eq_self_of_mem_inertiaGroup (hf_coprime : ¬p ∣ f)
    (hg : g ∈ inertiaGroup (Gp p) (intQpBar p)) (ζ : PadicAlgCl p) (hζ : ζ ^ f = 1) : g ζ = ζ := by
  -- An element of inertia is a Frobenius for `1`.
  simpa using apply_eq_pow_of_isFrob (q := 1) hg hf_coprime hζ

instance : NeZero (p ^ f - 1) := by simp [of_pos, Fact.out, ne]

/-- For `f ≠ 0`, the prime `p` does not divide `p ^ f - 1`. -/
lemma not_dvd_pow_sub_one : ¬p ∣ p ^ f - 1 := by simp [← natCast_eq_zero_iff, pos, ne, natCast_self]

end New.Selmer
