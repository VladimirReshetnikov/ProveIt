import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.PrincipalIdealDomain
import Surreal.HahnSeries.AdmissibleCones
import Surreal.HahnSeries.EscapeChain
import Surreal.HahnSeries.TorsionCovariance

/-!
# The finite lattice estimate and uniform unit twisting

This file formalizes the two lemmas that precede the exact multivariate extension domain
`ent:mv:thm:domain` of `docs/surcomplex/entire-functions-at-arbitrary-rank/article.tex`:
the finite lattice estimate `ent:mv:lem:lattice` and uniform unit twisting `ent:mv:lem:twist`,
together with the leading-term reduction displayed between them, and the convex hull
`H = conv_Δ(Γ)` of `ent:def:hull` (`ent:eq:convex-hull`) on which the lattice estimate is
stated.

Proved here:

* `convHull Γ` is `ent:eq:convex-hull` for an additive subgroup `Γ` of a linearly ordered
  abelian group `Δ`. For `Γ ≠ 0` its membership is literally the source's
  `|s| ≤ γ` for some `γ ∈ Γ_{>0}` (`mem_convHull_iff_of_ne_bot`); for `Γ = 0` the carrier
  used here is `{0}`, not the empty set of the literal formula. It is a subgroup containing `Γ`
  (`le_convHull`), it is convex (`ordConnected_convHull`), it lies in every convex subgroup
  containing `Γ` (`convHull_le`), so it is the convex hull, and `Γ` is cofinal in it
  (`exists_ge_of_mem_convHull`). This is the claim in the paragraph of `ent:mv:subsec:setting`
  after `ent:mv:def:entire` ("a convex subgroup, with no divisibility needed, and `Γ` is
  cofinal in it"); the divisibility asserted in `ent:def:hull` under the report's standing
  hypotheses is not addressed.
* `ent:mv:lem:lattice` (`lattice_estimate`): for `Γ ≠ 0`, finitely many `δ_j ∈ Δ` (indexed by
  any finite type, the source's `Fin d`), and `𝓛 = {m ∈ ℤ^d : ∑ m_j π_H(δ_j) = 0}` with
  `π_H : Δ → Δ ⧸ H` the quotient map, there are a positive integer `c_𝓛` and `η ∈ Γ_{>0}`
  with `|∑ m_j δ_j| ≤ c_𝓛 ‖m‖₁ η` for all `m ∈ 𝓛`. Only the abelian-group quotient is used:
  the membership `m ∈ 𝓛` is an equation in `Δ ⧸ H`, and no ordered quotient is needed.
  The hypothesis `Γ ≠ 0` is the standing hypothesis of `ent:mv:subsec:setting` (`Γ` is a
  nonzero ordered abelian group); without it there is no `η ∈ Γ_{>0}` and the conclusion fails.
  The estimate is proved with `c_𝓛 = 1` (`lattice_estimate_one`) and in a general form
  (`exists_abs_sum_zsmul_le`): `H` may be any additive subgroup of `Δ` whose elements are
  bounded in absolute value by elements of an arbitrary set `Γ` containing a positive element;
  neither convexity of `H`, nor `Γ ⊆ H`, nor any group structure on `Γ` is needed. The proof
  differs from the source's rational left inverse: the saturation
  `𝓛' = {m : ∃ n > 0, n ∑ m_j δ_j ∈ H}` has torsion-free, hence free, quotient `ℤ^d/𝓛'`, so
  `ℤ^d → ℤ^d/𝓛'` splits and a projection `p` onto `𝓛'` fixes `𝓛 ⊆ 𝓛'`; then
  `m = ∑ m_j p(e_j)` for `m ∈ 𝓛`, and `η` bounds the finitely many `|⟨p(e_j), δ⟩|`.
* `ent:mv:lem:twist` (`stronglySummable_mul_prod_pow_iff`): for a family `(b_i)` in
  `k((t^Δ))` over an arbitrary index type, exponent vectors `α(i) ∈ ℕ^σ` with `σ` finite, and
  `u_j ∈ 1 + 𝔪_Δ` (encoded as `0 < (u_j - 1).orderTop`), `(b_i)` is strongly summable if and
  only if `(b_i ∏_j u_j^{α(i)_j})` is. The forward direction
  (`stronglySummable_mul_prod_pow`) holds over any commutative ring: every product
  `∏ u_j^{α_j}` has support in the well-ordered monoid `S^*` (`twistMonoid`), and the existing
  `Surreal.HolonomicTorsion.stronglySummable_mul_of_support_subset` handles one fixed
  well-ordered support bound. The converse uses `u_j⁻¹ ∈ 1 + 𝔪_Δ`
  (`inv_sub_one_orderTop_pos`). Multiplying each term by a nonzero scalar (possibly depending
  on the index) preserves and reflects strong summability (`stronglySummable_smul_iff`, over
  any semiring without zero divisors and any partially ordered exponent set;
  `stronglySummable_C_mul_iff` for the constants `C c_i` in `R⟦Δ⟧`).
* The leading-term reduction after `ent:mv:lem:twist`: every nonzero `z ∈ k((t^Δ))` is
  `c t^δ u` with `c = lc(z)`, `δ = v(z)` and `u ∈ 1 + 𝔪_Δ` (`exists_single_mul_eq`; `c ≠ 0`
  is Mathlib's `HahnSeries.leadingCoeff_ne_zero`), and the decomposition is unique
  (`single_mul_eq_single_mul_iff`). Consequently
  `(a_α z^α)` is strongly summable if and only if `(a_α t^{⟨α, δ⟩})` is, for an arbitrary
  coefficient family (`stronglySummable_mul_prod_pow_iff_of_eq`, and
  `stronglySummable_mul_prod_pow_iff_order` with `δ_j = v(z_j)`), stated for an arbitrary
  index type with exponent map `α`, and in the source form indexed by `ℕ^σ` with the weight
  `Surreal.AdmissibleCone.pairing` (`stronglySummable_monomial_iff`).

Strong summability is `Surreal.Holonomic.StronglySummable` (a Mathlib `SummableFamily` with
the given terms), whose two clauses are those of the source. The valuation is
`HahnSeries.order`, and `t^δ` is `HahnSeries.single δ 1`.

Pending: the theorem `ent:mv:thm:domain` itself, which also needs the ordered quotient
`Δ/H` (only its underlying group is used here), the tail lemma `ent:mv:lem:tails` and
entireness of the coefficient family; and `ent:mv:cor:tails`, which rests on it.
-/

namespace Surreal.LatticeEstimate

open _root_.HahnSeries Surreal.Holonomic

noncomputable section

/-! ### The convex hull and the saturation of a subgroup -/

section Hull

variable {Δ : Type*} [AddCommGroup Δ]

/-- The saturation `{x : n • x ∈ H for some n > 0}` of an additive subgroup. -/
def saturation (H : AddSubgroup Δ) : AddSubgroup Δ where
  carrier := {x | ∃ n : ℕ, 0 < n ∧ n • x ∈ H}
  add_mem' := by
    rintro x y ⟨n, hn, hx⟩ ⟨m, hm, hy⟩
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    rw [nsmul_add]
    refine H.add_mem ?_ ?_
    · rw [← smul_smul]
      exact H.nsmul_mem hx m
    · rw [mul_comm, ← smul_smul]
      exact H.nsmul_mem hy n
  zero_mem' := ⟨1, one_pos, by rw [smul_zero]; exact H.zero_mem⟩
  neg_mem' := by
    rintro x ⟨n, hn, hx⟩
    exact ⟨n, hn, by rw [smul_neg]; exact H.neg_mem hx⟩

theorem mem_saturation {H : AddSubgroup Δ} {x : Δ} :
    x ∈ saturation H ↔ ∃ n : ℕ, 0 < n ∧ n • x ∈ H :=
  Iff.rfl

theorem le_saturation (H : AddSubgroup Δ) : H ≤ saturation H :=
  fun x hx => ⟨1, one_pos, by rwa [one_smul]⟩

/-- An integer multiple lies in a subgroup exactly when the multiple by the absolute value
does. -/
theorem zsmul_mem_iff_natAbs_nsmul_mem (H : AddSubgroup Δ) (z : ℤ) (x : Δ) :
    z • x ∈ H ↔ z.natAbs • x ∈ H := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · rw [Int.natAbs_natCast, natCast_zsmul]
  · rw [Int.natAbs_neg, Int.natAbs_natCast, neg_smul, natCast_zsmul, H.neg_mem_iff]

variable [LinearOrder Δ] [IsOrderedAddMonoid Δ]

/-- `ent:eq:convex-hull`: the convex hull `conv_Δ(Γ) = {s : |s| ≤ γ for some γ ∈ Γ}` of an
additive subgroup. For `Γ ≠ 0` the bound may be taken positive
(`mem_convHull_iff_of_ne_bot`), which is the source's formula. -/
def convHull (Γ : AddSubgroup Δ) : AddSubgroup Δ where
  carrier := {s | ∃ γ ∈ Γ, |s| ≤ γ}
  add_mem' := by
    rintro a b ⟨γ, hγ, ha⟩ ⟨γ', hγ', hb⟩
    exact ⟨γ + γ', Γ.add_mem hγ hγ', (abs_add_le a b).trans (add_le_add ha hb)⟩
  zero_mem' := ⟨0, Γ.zero_mem, by rw [abs_zero]⟩
  neg_mem' := by
    rintro a ⟨γ, hγ, ha⟩
    exact ⟨γ, hγ, by rwa [abs_neg]⟩

theorem mem_convHull {Γ : AddSubgroup Δ} {s : Δ} : s ∈ convHull Γ ↔ ∃ γ ∈ Γ, |s| ≤ γ :=
  Iff.rfl

omit [IsOrderedAddMonoid Δ] in
/-- Subgroups of a linearly ordered group are closed under absolute value. -/
theorem abs_mem {Γ : AddSubgroup Δ} {x : Δ} (hx : x ∈ Γ) : |x| ∈ Γ := by
  rcases abs_choice x with h | h <;> rw [h]
  · exact hx
  · exact Γ.neg_mem hx

/-- A nonzero subgroup of an ordered group has a positive element. -/
theorem exists_pos_of_ne_bot {Γ : AddSubgroup Δ} (hΓ : Γ ≠ ⊥) : ∃ γ ∈ Γ, 0 < γ := by
  obtain ⟨⟨x, hx⟩, hx0⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hΓ
  refine ⟨|x|, abs_mem hx, abs_pos.mpr fun h => hx0 ?_⟩
  exact Subtype.ext h

/-- `ent:eq:convex-hull` verbatim: for `Γ ≠ 0`, `s ∈ conv_Δ(Γ)` iff `|s| ≤ γ` for some
`γ ∈ Γ_{>0}`. -/
theorem mem_convHull_iff_of_ne_bot {Γ : AddSubgroup Δ} (hΓ : Γ ≠ ⊥) {s : Δ} :
    s ∈ convHull Γ ↔ ∃ γ ∈ Γ, 0 < γ ∧ |s| ≤ γ := by
  refine ⟨fun ⟨γ, hγ, hs⟩ => ?_, fun ⟨γ, hγ, _, hs⟩ => ⟨γ, hγ, hs⟩⟩
  obtain ⟨γ₀, hγ₀, hpos⟩ := exists_pos_of_ne_bot hΓ
  refine ⟨max γ γ₀, ?_, hpos.trans_le (le_max_right _ _), hs.trans (le_max_left _ _)⟩
  rcases max_choice γ γ₀ with h | h <;> rw [h]
  · exact hγ
  · exact hγ₀

theorem le_convHull (Γ : AddSubgroup Δ) : Γ ≤ convHull Γ :=
  fun x hx => ⟨|x|, abs_mem hx, le_rfl⟩

/-- `Γ` is cofinal in its convex hull. -/
theorem exists_ge_of_mem_convHull {Γ : AddSubgroup Δ} {s : Δ} (hs : s ∈ convHull Γ) :
    ∃ γ ∈ Γ, s ≤ γ := by
  obtain ⟨γ, hγ, h⟩ := hs
  exact ⟨γ, hγ, (le_abs_self s).trans h⟩

/-- The convex hull is convex. -/
theorem ordConnected_convHull (Γ : AddSubgroup Δ) : (convHull Γ : Set Δ).OrdConnected := by
  refine ⟨fun a ha b hb x hx => ?_⟩
  obtain ⟨γ, hγ, hγa⟩ := ha
  obtain ⟨γ', hγ', hγb⟩ := hb
  refine ⟨max γ γ', ?_, (abs_le_max_abs_abs hx.1 hx.2).trans (max_le_max hγa hγb)⟩
  rcases max_choice γ γ' with h | h <;> rw [h]
  · exact hγ
  · exact hγ'

/-- The convex hull lies in every convex subgroup containing `Γ`. -/
theorem convHull_le {Γ K : AddSubgroup Δ} (hK : (K : Set Δ).OrdConnected) (hΓK : Γ ≤ K) :
    convHull Γ ≤ K := by
  rintro s ⟨γ, hγ, hs⟩
  exact hK.out (K.neg_mem (hΓK hγ)) (hΓK hγ) ⟨(abs_le.mp hs).1, (abs_le.mp hs).2⟩

end Hull

/-! ### The finite lattice estimate -/

section Lattice

variable {Δ : Type*} [AddCommGroup Δ] [LinearOrder Δ] [IsOrderedAddMonoid Δ]

omit [IsOrderedAddMonoid Δ] in
/-- Finitely many elements, each bounded by an element of `Γ`, are bounded by one positive
element of `Γ`, provided `Γ` has a positive element. -/
theorem exists_pos_forall_le {ι : Type*} [Fintype ι] {Γ : Set Δ} (hpos : ∃ γ ∈ Γ, 0 < γ)
    (f : ι → Δ) (hf : ∀ j, ∃ γ ∈ Γ, f j ≤ γ) : ∃ η ∈ Γ, 0 < η ∧ ∀ j, f j ≤ η := by
  classical
  choose g hgΓ hg using hf
  obtain ⟨γ₀, hγ₀, hpos₀⟩ := hpos
  set S : Finset Δ := insert γ₀ (Finset.univ.image g)
  have hS : S.Nonempty := Finset.insert_nonempty _ _
  refine ⟨S.max' hS, ?_, hpos₀.trans_le (S.le_max' _ (Finset.mem_insert_self _ _)),
    fun j => (hg j).trans (S.le_max' _ (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem g (Finset.mem_univ j))))⟩
  rcases Finset.mem_insert.mp (S.max'_mem hS) with h | h
  · rw [h]
    exact hγ₀
  · obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h
    rw [← hj]
    exact hgΓ j

/-- `ent:mv:lem:lattice`, general form with `c_𝓛 = 1`. Let `H` be any additive subgroup of
`Δ` whose elements are bounded in absolute value by elements of a set `Γ` that contains a
positive element. For finitely many `δ_j ∈ Δ` there is `η ∈ Γ_{>0}` with
`|∑ m_j δ_j| ≤ ‖m‖₁ η` whenever `∑ m_j δ_j ∈ H`. -/
theorem exists_abs_sum_zsmul_le (H : AddSubgroup Δ) {Γ : Set Δ} (hpos : ∃ γ ∈ Γ, 0 < γ)
    (hbd : ∀ h ∈ H, ∃ γ ∈ Γ, |h| ≤ γ) {ι : Type*} [Fintype ι] (δ : ι → Δ) :
    ∃ η ∈ Γ, 0 < η ∧ ∀ m : ι → ℤ, ∑ j, m j • δ j ∈ H →
      |∑ j, m j • δ j| ≤ (∑ j, (m j).natAbs) • η := by
  classical
  set φ : (ι → ℤ) →ₗ[ℤ] Δ := Fintype.linearCombination ℤ δ
  have hφapp : ∀ m, φ m = ∑ j, m j • δ j := fun m => Fintype.linearCombination_apply ℤ δ m
  set L : Submodule ℤ (ι → ℤ) := (AddSubgroup.toIntSubmodule (saturation H)).comap φ
  have hL : ∀ m, m ∈ L ↔ φ m ∈ saturation H := fun m => Iff.rfl
  letI : Module ℤ ((ι → ℤ) ⧸ L) := Submodule.Quotient.module L
  haveI htf : Module.IsTorsionFree ℤ ((ι → ℤ) ⧸ L) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r q hq => ?_
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective L q
    have hq' : (Submodule.Quotient.mk (r • m) : (ι → ℤ) ⧸ L) = 0 := hq
    rw [Submodule.Quotient.mk_eq_zero] at hq'
    rw [Submodule.Quotient.mk_eq_zero]
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    obtain ⟨n, hn, hmem⟩ := (hL _).mp hq'
    rw [map_smul, smul_comm, zsmul_mem_iff_natAbs_nsmul_mem, smul_smul] at hmem
    exact (hL m).mpr ⟨r.natAbs * n, Nat.mul_pos (Int.natAbs_pos.mpr hr) hn, hmem⟩
  haveI : Module.Finite ℤ ((ι → ℤ) ⧸ L) := Module.Finite.quotient ℤ L
  haveI : Module.Free ℤ ((ι → ℤ) ⧸ L) := Module.free_of_finite_type_torsion_free'
  haveI : Module.Projective ℤ ((ι → ℤ) ⧸ L) := Module.Projective.of_free
  obtain ⟨s, hs⟩ := Module.projective_lifting_property L.mkQ LinearMap.id L.mkQ_surjective
  set p : (ι → ℤ) →ₗ[ℤ] (ι → ℤ) := LinearMap.id - s ∘ₗ L.mkQ with hpdef
  have hpL : ∀ m, p m ∈ L := by
    intro m
    have h1 : L.mkQ (s (L.mkQ m)) = L.mkQ m := LinearMap.congr_fun hs (L.mkQ m)
    have h2 : L.mkQ (p m) = 0 := by
      simp only [hpdef, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub,
        h1, sub_self]
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h2
  have hpfix : ∀ m ∈ L, p m = m := by
    intro m hm
    have h0 : L.mkQ m = 0 := by
      rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    simp only [hpdef, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h0,
      map_zero, sub_zero]
  set x : ι → Δ := fun j => φ (p fun k => if j = k then 1 else 0)
  have hxbd : ∀ j, ∃ γ ∈ Γ, |x j| ≤ γ := by
    intro j
    obtain ⟨n, hn, hmem⟩ := (hL _).mp (hpL fun k => if j = k then 1 else 0)
    obtain ⟨γ, hγ, hle⟩ := hbd _ hmem
    refine ⟨γ, hγ, le_trans ?_ hle⟩
    rw [abs_nsmul]
    exact le_self_nsmul (abs_nonneg _) hn.ne'
  obtain ⟨η, hη, hηpos, hηle⟩ := exists_pos_forall_le hpos _ hxbd
  refine ⟨η, hη, hηpos, fun m hm => ?_⟩
  have hmL : m ∈ L := (hL m).mpr (le_saturation H (by rw [hφapp]; exact hm))
  have hsum : ∑ j, m j • δ j = ∑ j, m j • x j := by
    rw [← hφapp]
    conv_lhs => rw [← hpfix m hmL]
    exact LinearMap.pi_apply_eq_sum_univ (φ ∘ₗ p) m
  rw [hsum, Finset.sum_smul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_zsmul, ← Int.natCast_natAbs, natCast_zsmul]
  exact nsmul_le_nsmul_right (hηle j) _

/-- `ent:mv:lem:lattice` with `c_𝓛 = 1`, for the convex hull `H = conv_Δ(Γ)` of a nonzero
subgroup `Γ` and the lattice `𝓛 = {m : ∑ m_j π_H(δ_j) = 0}`. -/
theorem lattice_estimate_one {Γ : AddSubgroup Δ} (hΓ : Γ ≠ ⊥) {ι : Type*} [Fintype ι]
    (δ : ι → Δ) :
    ∃ η ∈ Γ, 0 < η ∧ ∀ m : ι → ℤ, ∑ j, m j • (δ j : Δ ⧸ convHull Γ) = 0 →
      |∑ j, m j • δ j| ≤ (∑ j, (m j).natAbs) • η := by
  obtain ⟨η, hη, hηpos, h⟩ :=
    exists_abs_sum_zsmul_le (convHull Γ) (Γ := (Γ : Set Δ)) (exists_pos_of_ne_bot hΓ)
      (fun _ hh => hh) δ
  refine ⟨η, hη, hηpos, fun m hm => h m ?_⟩
  rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_sum]
  simpa only [QuotientAddGroup.mk_zsmul] using hm

/-- `ent:mv:lem:lattice`: for a nonzero subgroup `Γ ⊆ Δ` (the standing hypothesis of
`ent:mv:subsec:setting`), its convex hull `H = conv_Δ(Γ)`, `δ_1, …, δ_d ∈ Δ`,
`δ̄_j = π_H(δ_j)` and `𝓛 = {m ∈ ℤ^d : ∑ m_j δ̄_j = 0}`, there are a positive integer
`c_𝓛` and `η ∈ Γ_{>0}` with `|∑ m_j δ_j| ≤ c_𝓛 ‖m‖₁ η` for `m ∈ 𝓛`. -/
theorem lattice_estimate {Γ : AddSubgroup Δ} (hΓ : Γ ≠ ⊥) {ι : Type*} [Fintype ι]
    (δ : ι → Δ) :
    ∃ c : ℕ, 0 < c ∧ ∃ η ∈ Γ, 0 < η ∧ ∀ m : ι → ℤ,
      ∑ j, m j • (δ j : Δ ⧸ convHull Γ) = 0 →
        |∑ j, m j • δ j| ≤ (c * ∑ j, (m j).natAbs) • η := by
  obtain ⟨η, hη, hηpos, h⟩ := lattice_estimate_one hΓ δ
  exact ⟨1, one_pos, η, hη, hηpos, fun m hm => by rw [one_mul]; exact h m hm⟩

end Lattice

/-! ### Uniform unit twisting -/

section Twist

variable {Δ : Type*} [AddCommGroup Δ] [LinearOrder Δ] [IsOrderedAddMonoid Δ]

/-- Scalars do not change supports: multiplying each term by a nonzero scalar preserves and
reflects strong summability (`ent:mv:lem:twist`, last sentence). -/
theorem stronglySummable_smul_iff {Γ R : Type*} [PartialOrder Γ] [Semiring R] [NoZeroDivisors R]
    {ι : Type*} {c : ι → R} (hc : ∀ i, c i ≠ 0) (b : ι → R⟦Γ⟧) :
    StronglySummable (fun i => c i • b i) ↔ StronglySummable b := by
  have hco : ∀ i g, (c i • b i).coeff g ≠ 0 ↔ (b i).coeff g ≠ 0 := fun i g => by
    rw [coeff_smul, smul_eq_mul]
    exact ⟨right_ne_zero_of_mul, mul_ne_zero (hc i)⟩
  have hs : ∀ i, (c i • b i).support = (b i).support := fun i => Set.ext fun g => hco i g
  simp only [stronglySummable_iff, hs, hco]

/-- `ent:mv:lem:twist`, last sentence, with the scalars embedded as constants `C c_i`. -/
theorem stronglySummable_C_mul_iff {R : Type*} [Semiring R] [NoZeroDivisors R] {ι : Type*}
    {c : ι → R} (hc : ∀ i, c i ≠ 0) (b : ι → R⟦Δ⟧) :
    StronglySummable (fun i => C (c i) * b i) ↔ StronglySummable b := by
  simp only [C_mul_eq_smul]
  exact stronglySummable_smul_iff hc b

section OneAdd

/-! Elements of `1 + 𝔪_Δ`, encoded as `0 < (u - 1).orderTop`. -/

variable {R : Type*} [Ring R]

omit [IsOrderedAddMonoid Δ] in
/-- Every exponent in the support of an element of `𝔪_Δ` is positive. This is a local copy of
`Surreal.FirstError.pos_of_mem_support` (stated there over a commutative ring), kept here over
an arbitrary ring. -/
theorem pos_of_mem_support {x : R⟦Δ⟧} (hx : 0 < x.orderTop) {g : Δ} (hg : g ∈ x.support) :
    0 < g := by
  have h := hx.trans_le (orderTop_le_of_coeff_ne_zero hg)
  exact_mod_cast h

omit [IsOrderedAddMonoid Δ] in
/-- A Hahn series whose coefficients vanish up to `g` has `orderTop` above `g`. -/
theorem lt_orderTop_of_forall {x : R⟦Δ⟧} {g : Δ} (h : ∀ j ≤ g, x.coeff j = 0) :
    (g : WithTop Δ) < x.orderTop := by
  by_contra hle
  rw [not_lt] at hle
  rcases eq_or_ne x 0 with rfl | hx
  · rw [orderTop_zero] at hle
    exact WithTop.top_ne_coe (le_antisymm hle le_top)
  rw [← order_eq_orderTop_of_ne_zero hx, WithTop.coe_le_coe] at hle
  exact (coeff_order_eq_zero.not.mpr hx) (h _ hle)

variable [Nontrivial R]

omit [IsOrderedAddMonoid Δ] in
/-- Elements of `1 + 𝔪_Δ` have `orderTop` zero. -/
theorem orderTop_eq_zero_of_one_add {u : R⟦Δ⟧} (hu : 0 < (u - 1).orderTop) :
    u.orderTop = 0 := by
  have h : u = 1 + (u - 1) := (add_sub_cancel 1 u).symm
  rw [h, orderTop_add_eq_left (by rw [orderTop_one]; exact hu), orderTop_one]

omit [IsOrderedAddMonoid Δ] in
/-- Elements of `1 + 𝔪_Δ` are nonzero. -/
theorem ne_zero_of_one_add {u : R⟦Δ⟧} (hu : 0 < (u - 1).orderTop) : u ≠ 0 := by
  intro h
  have h0 := orderTop_eq_zero_of_one_add hu
  rw [h, orderTop_zero] at h0
  exact WithTop.top_ne_zero h0

omit [IsOrderedAddMonoid Δ] in
/-- Elements of `1 + 𝔪_Δ` have valuation zero. -/
theorem order_eq_zero_of_one_add {u : R⟦Δ⟧} (hu : 0 < (u - 1).orderTop) : u.order = 0 := by
  have h := order_eq_orderTop_of_ne_zero (ne_zero_of_one_add hu)
  rw [orderTop_eq_zero_of_one_add hu] at h
  exact_mod_cast h

omit [IsOrderedAddMonoid Δ] in
/-- Elements of `1 + 𝔪_Δ` have leading coefficient one. -/
theorem leadingCoeff_eq_one_of_one_add {u : R⟦Δ⟧} (hu : 0 < (u - 1).orderTop) :
    u.leadingCoeff = 1 := by
  have h : (u - 1).coeff 0 = 0 := coeff_eq_zero_of_lt_orderTop (by simpa using hu)
  rw [coeff_sub, coeff_one, if_pos rfl, sub_eq_zero] at h
  rw [leadingCoeff_eq, order_eq_zero_of_one_add hu, h]

variable [NoZeroDivisors R]

/-- The valuation of `c t^δ u` with `c ≠ 0` and `u ∈ 1 + 𝔪_Δ` is `δ`. -/
theorem order_single_mul_of_one_add {δ : Δ} {c : R} (hc : c ≠ 0) {u : R⟦Δ⟧}
    (hu : 0 < (u - 1).orderTop) : (single δ c * u).order = δ := by
  rw [order_mul (single_ne_zero hc) (ne_zero_of_one_add hu), order_single hc,
    order_eq_zero_of_one_add hu, add_zero]

/-- The leading coefficient of `c t^δ u` with `u ∈ 1 + 𝔪_Δ` is `c`. -/
theorem leadingCoeff_single_mul_of_one_add {δ : Δ} {c : R} {u : R⟦Δ⟧}
    (hu : 0 < (u - 1).orderTop) : (single δ c * u).leadingCoeff = c := by
  rw [leadingCoeff_mul, leadingCoeff_of_single, leadingCoeff_eq_one_of_one_add hu, mul_one]

end OneAdd

section CommRing

variable {R : Type*} [CommRing R] {σ : Type*}

/-- The monoid `S^*` generated by `S = ⋃_j supp(u_j - 1)` in the proof of `ent:mv:lem:twist`.
-/
def twistMonoid (u : σ → R⟦Δ⟧) : AddSubmonoid Δ :=
  AddSubmonoid.closure (⋃ j, (u j - 1).support)

/-- For `u_j ∈ 1 + 𝔪_Δ` with finitely many `j`, the monoid `S^*` is well ordered. -/
theorem isPWO_twistMonoid [Finite σ] {u : σ → R⟦Δ⟧} (hu : ∀ j, 0 < (u j - 1).orderTop) :
    ((twistMonoid u : AddSubmonoid Δ) : Set Δ).IsPWO := by
  cases nonempty_fintype σ
  refine Set.IsPWO.addSubmonoid_closure ?_ ?_
  · intro g hg
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hg
    exact (pos_of_mem_support (hu j) hj).le
  · have h := (Finset.isPWO_bUnion Finset.univ (f := fun j => (u j - 1).support)).mpr
      fun j _ => (u j - 1).isPWO_support
    simpa using h

omit [IsOrderedAddMonoid Δ] in
/-- `supp(u_j) ⊆ {0} ∪ supp(u_j - 1) ⊆ S^*`. -/
theorem support_subset_twistMonoid (u : σ → R⟦Δ⟧) (j : σ) :
    (u j).support ⊆ twistMonoid u := by
  intro g hg
  have hsplit : (u j).coeff g = (1 : R⟦Δ⟧).coeff g + (u j - 1).coeff g := by
    rw [← coeff_add, add_sub_cancel]
  by_cases h1 : (u j - 1).coeff g = 0
  · rw [h1, add_zero, coeff_one] at hsplit
    have hg0 : g = 0 := by
      by_contra hne
      rw [if_neg hne] at hsplit
      exact hg hsplit
    rw [hg0]
    exact (twistMonoid u).zero_mem
  · exact AddSubmonoid.subset_closure (Set.mem_iUnion.mpr ⟨j, h1⟩)

/-- The Hahn series supported in an additive submonoid `M` form a multiplicative submonoid. -/
def supportSubmonoid (M : AddSubmonoid Δ) : Submonoid R⟦Δ⟧ where
  carrier := {x | x.support ⊆ M}
  mul_mem' := by
    intro x y hx hy g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := support_mul_subset hg
    exact M.add_mem (hx ha) (hy hb)
  one_mem' := by
    intro g hg
    have hg' : (1 : R⟦Δ⟧).coeff g ≠ 0 := hg
    rw [coeff_one] at hg'
    have hg0 : g = 0 := by
      by_contra hne
      exact hg' (if_neg hne)
    rw [hg0]
    exact M.zero_mem

/-- Every finite product `∏_j u_j^{α_j}` has support in the one monoid `S^*`. -/
theorem support_prod_pow_subset [Fintype σ] (u : σ → R⟦Δ⟧) (α : σ → ℕ) :
    (∏ j, u j ^ α j).support ⊆ twistMonoid u :=
  Submonoid.prod_mem (supportSubmonoid (twistMonoid u)) fun j _ =>
    Submonoid.pow_mem _ (support_subset_twistMonoid u j) _

/-- `ent:mv:lem:twist`, forward direction, over any commutative ring: if `(b_i)` is strongly
summable and `u_j ∈ 1 + 𝔪_Δ`, then `(b_i ∏_j u_j^{α(i)_j})` is strongly summable. -/
theorem stronglySummable_mul_prod_pow [Fintype σ] {u : σ → R⟦Δ⟧}
    (hu : ∀ j, 0 < (u j - 1).orderTop) {ι : Type*} (α : ι → σ → ℕ) {b : ι → R⟦Δ⟧}
    (hb : StronglySummable b) : StronglySummable fun i => b i * ∏ j, u j ^ α i j :=
  HolonomicTorsion.stronglySummable_mul_of_support_subset hb (isPWO_twistMonoid hu)
    fun i => support_prod_pow_subset u (α i)

/-- A finite product of powers of monomials is a monomial. -/
theorem prod_single_pow (s : Finset σ) (δ : σ → Δ) (c : σ → R) (n : σ → ℕ) :
    ∏ j ∈ s, single (δ j) (c j) ^ n j = single (∑ j ∈ s, n j • δ j) (∏ j ∈ s, c j ^ n j) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.sum_empty, Finset.prod_empty, single_zero_one]
  · intro j s hj ih
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj, ih, single_pow,
      single_mul_single]

end CommRing

section Field

variable {k : Type*} [Field k] {σ : Type*}

/-- `1 + 𝔪_Δ` is closed under inversion. -/
theorem inv_sub_one_orderTop_pos {u : k⟦Δ⟧} (hu : 0 < (u - 1).orderTop) :
    0 < (u⁻¹ - 1).orderTop := by
  have hne := ne_zero_of_one_add hu
  have h0 : u⁻¹.orderTop = 0 := by
    have h := orderTop_mul u u⁻¹
    rw [mul_inv_cancel₀ hne, orderTop_one, orderTop_eq_zero_of_one_add hu, zero_add] at h
    exact h.symm
  have e : u⁻¹ - 1 = -((u - 1) * u⁻¹) := by
    rw [sub_mul, mul_inv_cancel₀ hne, one_mul, neg_sub]
  rw [e, orderTop_neg, orderTop_mul, h0, add_zero]
  exact hu

/-- `ent:mv:lem:twist`: for `u_1, …, u_d ∈ 1 + 𝔪_Δ` and exponent vectors `α(i) ∈ ℕ^d`, a family
`(b_i)` in `k((t^Δ))` is strongly summable if and only if `(b_i ∏_j u_j^{α(i)_j})` is. -/
theorem stronglySummable_mul_prod_pow_iff [Fintype σ] {ι : Type*} (b : ι → k⟦Δ⟧)
    (α : ι → σ → ℕ) {u : σ → k⟦Δ⟧} (hu : ∀ j, 0 < (u j - 1).orderTop) :
    StronglySummable (fun i => b i * ∏ j, u j ^ α i j) ↔ StronglySummable b := by
  refine ⟨fun h => ?_, stronglySummable_mul_prod_pow hu α⟩
  have h' := stronglySummable_mul_prod_pow (u := fun j => (u j)⁻¹)
    (fun j => inv_sub_one_orderTop_pos (hu j)) α h
  convert h' using 1
  funext i
  rw [mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_eq_one fun j _ => by
    rw [← mul_pow, mul_inv_cancel₀ (ne_zero_of_one_add (hu j)), one_pow], mul_one]

/-! ### The leading-term reduction -/

/-- The leading-term decomposition after `ent:mv:lem:twist`, existence: every nonzero
`z ∈ k((t^Δ))` is `c t^δ u` with `c = lc(z)`, `δ = v(z)` and `u ∈ 1 + 𝔪_Δ`. The conclusion
does not restate `c ≠ 0`; that is Mathlib's `HahnSeries.leadingCoeff_ne_zero`. -/
theorem exists_single_mul_eq {z : k⟦Δ⟧} (hz : z ≠ 0) :
    ∃ u : k⟦Δ⟧, 0 < (u - 1).orderTop ∧ z = single z.order z.leadingCoeff * u := by
  have hc : z.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hz
  refine ⟨single (-z.order) z.leadingCoeff⁻¹ * z, ?_, ?_⟩
  · have h := lt_orderTop_of_forall (x := single (-z.order) z.leadingCoeff⁻¹ * z - 1)
      (g := 0) fun j hj => ?_
    · simpa using h
    rw [coeff_sub, coeff_single_mul, coeff_one, sub_neg_eq_add]
    rcases hj.lt_or_eq with hlt | rfl
    · rw [coeff_eq_zero_of_lt_order (add_lt_of_neg_left _ hlt), mul_zero, if_neg hlt.ne,
        sub_zero]
    · rw [zero_add, if_pos rfl, ← leadingCoeff_eq, inv_mul_cancel₀ hc, sub_self]
  · rw [← mul_assoc, single_mul_single, add_neg_cancel, mul_inv_cancel₀ hc, single_zero_one,
      one_mul]

/-- The leading-term decomposition after `ent:mv:lem:twist`, uniqueness: `c t^δ u` with
`c ≠ 0` and `u ∈ 1 + 𝔪_Δ` determines `δ`, `c` and `u`. -/
theorem single_mul_eq_single_mul_iff {δ δ' : Δ} {c c' : k} (hc : c ≠ 0) (hc' : c' ≠ 0)
    {u u' : k⟦Δ⟧} (hu : 0 < (u - 1).orderTop) (hu' : 0 < (u' - 1).orderTop) :
    single δ c * u = single δ' c' * u' ↔ δ = δ' ∧ c = c' ∧ u = u' := by
  refine ⟨fun h => ?_, fun ⟨h1, h2, h3⟩ => by rw [h1, h2, h3]⟩
  have h1 := congrArg order h
  rw [order_single_mul_of_one_add hc hu, order_single_mul_of_one_add hc' hu'] at h1
  have h2 := congrArg leadingCoeff h
  rw [leadingCoeff_single_mul_of_one_add hu, leadingCoeff_single_mul_of_one_add hu'] at h2
  subst h1 h2
  exact ⟨rfl, rfl, mul_left_cancel₀ (single_ne_zero hc) h⟩

/-- The consequence of `ent:mv:lem:twist`: if `z_j = c_j t^{δ_j} u_j` with `c_j ≠ 0` and
`u_j ∈ 1 + 𝔪_Δ`, then `(a_i z^{α(i)})` is strongly summable if and only if
`(a_i t^{⟨α(i), δ⟩})` is, for an arbitrary coefficient family `(a_i)`. -/
theorem stronglySummable_mul_prod_pow_iff_of_eq [Fintype σ] {ι : Type*} (a : ι → k⟦Δ⟧)
    (α : ι → σ → ℕ) {z u : σ → k⟦Δ⟧} {c : σ → k} {δ : σ → Δ} (hc : ∀ j, c j ≠ 0)
    (hu : ∀ j, 0 < (u j - 1).orderTop) (hz : ∀ j, z j = single (δ j) (c j) * u j) :
    StronglySummable (fun i => a i * ∏ j, z j ^ α i j) ↔
      StronglySummable (fun i => a i * single (∑ j, α i j • δ j) 1) := by
  have e : ∀ i, a i * ∏ j, z j ^ α i j =
      C (∏ j, c j ^ α i j) * (a i * single (∑ j, α i j • δ j) 1) * ∏ j, u j ^ α i j := by
    intro i
    simp only [hz, mul_pow, Finset.prod_mul_distrib, prod_single_pow]
    rw [show single (∑ j, α i j • δ j) (∏ j, c j ^ α i j) =
        C (∏ j, c j ^ α i j) * single (∑ j, α i j • δ j) 1 by
      rw [C_apply, single_mul_single, zero_add, mul_one]]
    ring
  simp only [e]
  exact (stronglySummable_mul_prod_pow_iff _ α hu).trans (stronglySummable_C_mul_iff
    (fun i => Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (hc j)) _)

/-- The consequence of `ent:mv:lem:twist` with `δ_j = v(z_j)`: for nonzero `z_j`, the family
`(a_i z^{α(i)})` is strongly summable if and only if `(a_i t^{⟨α(i), v(z)⟩})` is. -/
theorem stronglySummable_mul_prod_pow_iff_order [Fintype σ] {ι : Type*} (a : ι → k⟦Δ⟧)
    (α : ι → σ → ℕ) {z : σ → k⟦Δ⟧} (hz : ∀ j, z j ≠ 0) :
    StronglySummable (fun i => a i * ∏ j, z j ^ α i j) ↔
      StronglySummable (fun i => a i * single (∑ j, α i j • (z j).order) 1) := by
  choose u hu hzu using fun j => exists_single_mul_eq (hz j)
  exact stronglySummable_mul_prod_pow_iff_of_eq a α
    (fun j => leadingCoeff_ne_zero.mpr (hz j)) hu hzu

/-- The source form of the consequence of `ent:mv:lem:twist`, indexed by `α ∈ ℕ^σ`: for
nonzero `z_j` with `δ_j = v(z_j)`, `(a_α z^α)_α` is strongly summable if and only if
`(a_α t^{⟨α, δ⟩})_α` is. -/
theorem stronglySummable_monomial_iff [Fintype σ] (a : (σ → ℕ) → k⟦Δ⟧) {z : σ → k⟦Δ⟧}
    (hz : ∀ j, z j ≠ 0) :
    StronglySummable (fun α : σ → ℕ => a α * ∏ j, z j ^ α j) ↔
      StronglySummable (fun α : σ → ℕ =>
        a α * single (Surreal.AdmissibleCone.pairing α fun j => (z j).order) 1) :=
  stronglySummable_mul_prod_pow_iff_order a id hz

end Field

end Twist

end

end Surreal.LatticeEstimate
