import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.LinearCombination
import Surreal.HahnSeries.CoefficientMapping

/-!
# Independent sign changes of multiquadratic extensions

This file proves `tail:lem:signs` of
`docs/surreal/tail-spans-and-differential-transcendence/article.tex`.

Let `M` be a field with `2 ≠ 0` (characteristic different from two), `E` an
arbitrary extension field, and `a : I → M` a family with independent square
classes: no product over a nonempty finite set of indices is a square in `M`.
Choose `r i ∈ E` with `r i ^ 2 = a i`. The index set `I` is arbitrary.

* The monomials `∏ i ∈ U, r i`, for `U` ranging over all finite subsets of `I`,
  are linearly independent over `M` (`linearIndependent_mono`).
* For every set `S ⊆ I`, the field `M(r i : i ∈ S)` is spanned by the monomials
  with `U ⊆ S` (`mem_adjoin_iff_mem_monoSpan`), so these monomials form an
  `M`-basis of it (`adjoinBasis`). For finite `J`, `M(r i : i ∈ J)` has degree
  `2 ^ |J|` over `M` (`finrank_adjoin`).
* For every sign assignment `ε i ∈ {1, -1}`, the map `r i ↦ ε i r i` extends to an
  `M`-algebra automorphism of `L = M(r i : i ∈ I)` (`signAut`, `signAut_apply`,
  `exists_signAut`). It multiplies the basis monomial `r_U` by `∏ i ∈ U, ε i`.
* The automorphism acts coefficientwise on the Hahn series `L((t^Γ))` as a ring
  automorphism fixing the coefficientwise image of `M((t^Γ))`
  (`hahnSignAut`, `hahnSignAut_mapCoefficients_algebraMap`, `exists_signAut_hahn`).

The proof is the elementary induction of the source, without Galois theory. For a
finite set `J`, every element of `M(r_J)` whose square lies in `M` is a scalar
multiple of a single monomial (`exists_eq_smul_mono_of_sq`). Consequently a
relation `x + y r_i = 0` with `x, y ∈ M(r_J)` and `i ∉ J` forces `y = 0`, since
otherwise `r_i` would be `c r_U` and `a_i ∏_{j ∈ U} a_j` a square. The
characteristic hypothesis is used exactly once, to cancel the factor `2` in the
cross term of `(A + B r_i)²`. The source's counterexample over `𝔽₂(u, v)` shows
that it cannot be dropped. The source's square roots are taken in an algebraic
closure; here any extension field is allowed, and the value group `Γ` may be any
linearly ordered cancellative additive commutative monoid.

As `tail:rem:noorder` stresses, no compatibility with an ordering is asserted.
-/

namespace Surreal.TailSigns

open Module Submodule

noncomputable section

section Products

variable {I R : Type*} [CommMonoid R]

/-- The product of two finite products over `U` and `V`: the common indices appear
squared and the remaining indices form the symmetric difference. -/
theorem prod_mul_prod_eq [DecidableEq I] (f : I → R) (U V : Finset I) :
    (∏ i ∈ U, f i) * ∏ i ∈ V, f i =
      (∏ i ∈ U ∩ V, f i ^ 2) * ∏ i ∈ (U ∪ V) \ (U ∩ V), f i := by
  rw [← Finset.prod_union_inter,
    ← Finset.prod_sdiff (Finset.inter_subset_left.trans Finset.subset_union_left :
      U ∩ V ⊆ U ∪ V),
    Finset.prod_pow, mul_assoc, ← sq, mul_comm]

end Products

variable {M E I : Type*} [Field M] [Field E] [Algebra M E]

/-- A family `(a_i)` has independent square classes if no product over a nonempty
finite set of indices is a square. -/
def IndependentSquareClasses (a : I → M) : Prop :=
  ∀ J : Finset I, J.Nonempty → ¬ IsSquare (∏ i ∈ J, a i)

/-- Every member of a family with independent square classes is nonzero, so the
family lies in `Mˣ` as in the source. -/
theorem IndependentSquareClasses.ne_zero {a : I → M} (ha : IndependentSquareClasses a)
    (i : I) : a i ≠ 0 := by
  intro h
  apply ha {i} (Finset.singleton_nonempty i)
  rw [Finset.prod_singleton, h]
  exact ⟨0, by rw [mul_zero]⟩

/-- The square-root monomial `r_U = ∏ i ∈ U, r i`. -/
def mono (r : I → E) (U : Finset I) : E :=
  ∏ i ∈ U, r i

theorem mono_empty (r : I → E) : mono r ∅ = 1 :=
  Finset.prod_empty

theorem mono_singleton (r : I → E) (i : I) : mono r {i} = r i :=
  Finset.prod_singleton r i

theorem mono_insert [DecidableEq I] (r : I → E) {i : I} {U : Finset I} (h : i ∉ U) :
    mono r (insert i U) = r i * mono r U :=
  Finset.prod_insert h

variable (M) in
/-- The `M`-span of the monomials `r_U` with `U ⊆ S`. -/
def monoSpan (r : I → E) (S : Set I) : Submodule M E :=
  span M (mono r '' {U : Finset I | (U : Set I) ⊆ S})

variable {a : I → M} {r : I → E}

theorem mono_mem_monoSpan {S : Set I} {U : Finset I} (h : (U : Set I) ⊆ S) :
    mono r U ∈ monoSpan M r S :=
  subset_span ⟨U, h, rfl⟩

theorem one_mem_monoSpan {S : Set I} : (1 : E) ∈ monoSpan M r S := by
  rw [← mono_empty r]
  exact mono_mem_monoSpan (by simp)

theorem mono_sq (hr : ∀ i, r i ^ 2 = algebraMap M E (a i)) (U : Finset I) :
    mono r U ^ 2 = algebraMap M E (∏ i ∈ U, a i) := by
  rw [mono, ← Finset.prod_pow, map_prod]
  exact Finset.prod_congr rfl fun i _ => hr i

/-- The multiplication rule `r_U r_V = (∏_{U ∩ V} a) r_{U Δ V}`. -/
theorem mono_mul_mono [DecidableEq I] (hr : ∀ i, r i ^ 2 = algebraMap M E (a i))
    (U V : Finset I) :
    mono r U * mono r V =
      algebraMap M E (∏ i ∈ U ∩ V, a i) * mono r ((U ∪ V) \ (U ∩ V)) := by
  rw [mono, mono, mono, prod_mul_prod_eq, map_prod]
  congr 1
  exact Finset.prod_congr rfl fun i _ => hr i

theorem mul_mem_monoSpan (hr : ∀ i, r i ^ 2 = algebraMap M E (a i)) {S : Set I} {x y : E}
    (hx : x ∈ monoSpan M r S) (hy : y ∈ monoSpan M r S) : x * y ∈ monoSpan M r S := by
  classical
  have key : ∀ U V : Finset I, (U : Set I) ⊆ S → (V : Set I) ⊆ S →
      mono r U * mono r V ∈ monoSpan M r S := by
    intro U V hU hV
    rw [mono_mul_mono hr, ← Algebra.smul_def]
    refine Submodule.smul_mem _ _ (mono_mem_monoSpan ?_)
    have hUV : ((U ∪ V : Finset I) : Set I) ⊆ S := by
      rw [Finset.coe_union]
      exact Set.union_subset hU hV
    exact (Finset.coe_subset.mpr Finset.sdiff_subset).trans hUV
  unfold monoSpan at hx hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨U, hU, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨V, hV, rfl⟩ := hy
      exact key U V hU hV
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
    | smul c y _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h
  | zero => rw [zero_mul]; exact zero_mem _
  | add x z _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | smul c x _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h

/-- The field `M(r i : i ∈ S)` is exactly the span of the monomials `r_U`, `U ⊆ S`. -/
theorem mem_adjoin_iff_mem_monoSpan (hr : ∀ i, r i ^ 2 = algebraMap M E (a i)) (S : Set I)
    {x : E} : x ∈ IntermediateField.adjoin M (r '' S) ↔ x ∈ monoSpan M r S := by
  have halg : ∀ y ∈ r '' S, IsAlgebraic M y := by
    rintro _ ⟨i, -, rfl⟩
    exact IsAlgebraic.of_pow two_pos (by rw [hr i]; exact isAlgebraic_algebraMap _)
  rw [← IntermediateField.mem_toSubalgebra,
    IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg]
  let A : Subalgebra M E := (monoSpan M r S).toSubalgebra one_mem_monoSpan
    (fun _ _ hx hy => mul_mem_monoSpan hr hx hy)
  have h1 : Algebra.adjoin M (r '' S) ≤ A := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨i, hi, rfl⟩
    show r i ∈ monoSpan M r S
    rw [← mono_singleton r i]
    exact mono_mem_monoSpan (by simpa using hi)
  have h2 : monoSpan M r S ≤ Subalgebra.toSubmodule (Algebra.adjoin M (r '' S)) := by
    rw [monoSpan, Submodule.span_le]
    rintro _ ⟨U, hU, rfl⟩
    exact Subalgebra.prod_mem _ fun i hi =>
      Algebra.subset_adjoin ⟨i, hU (Finset.mem_coe.mpr hi), rfl⟩
  exact ⟨fun hx => h1 hx, fun hx => h2 hx⟩

theorem inv_mem_monoSpan (hr : ∀ i, r i ^ 2 = algebraMap M E (a i)) {S : Set I} {y : E}
    (hy : y ∈ monoSpan M r S) : y⁻¹ ∈ monoSpan M r S := by
  rw [← mem_adjoin_iff_mem_monoSpan hr] at hy ⊢
  exact (IntermediateField.adjoin M (r '' S)).inv_mem hy

/-- Every element of the span over `insert i S` has the form `A + B r_i` with `A, B`
in the span over `S`. -/
theorem exists_eq_add_mul_of_mem_insert (S : Set I) (i : I) {u : E}
    (hu : u ∈ monoSpan M r (insert i S)) :
    ∃ A ∈ monoSpan M r S, ∃ B ∈ monoSpan M r S, u = A + B * r i := by
  classical
  unfold monoSpan at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨U, hU, rfl⟩ := hx
    by_cases hiU : i ∈ U
    · refine ⟨0, zero_mem _, mono r (U.erase i), mono_mem_monoSpan ?_, ?_⟩
      · intro j hj
        rw [Finset.coe_erase] at hj
        exact (Set.mem_insert_iff.mp (hU hj.1)).resolve_left
          fun h => hj.2 (Set.mem_singleton_iff.mpr h)
      · rw [zero_add, mul_comm, ← mono_insert r (Finset.notMem_erase i U),
          Finset.insert_erase hiU]
    · refine ⟨mono r U, mono_mem_monoSpan ?_, 0, zero_mem _, by rw [zero_mul, add_zero]⟩
      intro j hj
      refine (Set.mem_insert_iff.mp (hU hj)).resolve_left fun h => ?_
      subst h
      exact hiU hj
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by rw [zero_mul, add_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨A, hA, B, hB, rfl⟩ := hx
    obtain ⟨C, hC, D, hD, rfl⟩ := hy
    exact ⟨A + C, add_mem hA hC, B + D, add_mem hB hD, by ring⟩
  | smul c x _ hx =>
    obtain ⟨A, hA, B, hB, rfl⟩ := hx
    exact ⟨c • A, Submodule.smul_mem _ c hA, c • B, Submodule.smul_mem _ c hB,
      by rw [smul_add, smul_mul_assoc]⟩

/-- If square roots in `M(r_J)` of elements of `M` are monomials up to scalars, then
`r_i` for `i ∉ J` is independent of `M(r_J)`: `x + y r_i = 0` forces `y = 0`. -/
theorem eq_zero_of_add_mul_eq_zero (hr : ∀ i, r i ^ 2 = algebraMap M E (a i))
    (ha : IndependentSquareClasses a) {J : Finset I} {i : I} (hi : i ∉ J)
    (hB : ∀ u ∈ monoSpan M r (J : Set I), (∃ m : M, u ^ 2 = algebraMap M E m) →
      ∃ c : M, ∃ U ⊆ J, u = c • mono r U)
    {x y : E} (hx : x ∈ monoSpan M r (J : Set I)) (hy : y ∈ monoSpan M r (J : Set I))
    (hxy : x + y * r i = 0) : y = 0 := by
  classical
  by_contra hy0
  have hri : r i = -x * y⁻¹ := by
    rw [← div_eq_mul_inv]
    exact eq_div_of_mul_eq hy0 (by linear_combination hxy)
  have hmem : r i ∈ monoSpan M r (J : Set I) := by
    rw [hri]
    exact mul_mem_monoSpan hr (neg_mem hx) (inv_mem_monoSpan hr hy)
  obtain ⟨c, U, hU, hcU⟩ := hB (r i) hmem ⟨a i, hr i⟩
  have hiU : i ∉ U := fun h => hi (hU h)
  have hsq : a i = c ^ 2 * ∏ j ∈ U, a j := by
    apply (algebraMap M E).injective
    rw [← hr i, hcU, smul_pow, mono_sq hr, Algebra.smul_def, map_mul]
  apply ha (insert i U) (Finset.insert_nonempty i U)
  rw [Finset.prod_insert hiU, hsq]
  exact ⟨c * ∏ j ∈ U, a j, by ring⟩

/-- For finite `J`, an element of `M(r_J)` whose square lies in `M` is a scalar
multiple of one monomial `r_U`, `U ⊆ J`. This is the eigenvector step of
`tail:lem:signs`. -/
theorem exists_eq_smul_mono_of_sq (hr : ∀ i, r i ^ 2 = algebraMap M E (a i))
    (ha : IndependentSquareClasses a) (h2 : (2 : M) ≠ 0) (J : Finset I) :
    ∀ u ∈ monoSpan M r (J : Set I), (∃ m : M, u ^ 2 = algebraMap M E m) →
      ∃ c : M, ∃ U ⊆ J, u = c • mono r U := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    rintro u hu -
    have hc : ∃ c : M, u = c • mono r ∅ := by
      unfold monoSpan at hu
      induction hu using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨U, hU, rfl⟩ := hx
        have hU0 : U = ∅ := by simpa using hU
        exact ⟨1, by rw [hU0, one_smul]⟩
      | zero => exact ⟨0, by rw [zero_smul]⟩
      | add x y _ _ hx hy =>
        obtain ⟨c, rfl⟩ := hx
        obtain ⟨d, rfl⟩ := hy
        exact ⟨c + d, by rw [add_smul]⟩
      | smul d x _ hx =>
        obtain ⟨c, rfl⟩ := hx
        exact ⟨d * c, by rw [smul_smul]⟩
    obtain ⟨c, hc⟩ := hc
    exact ⟨c, ∅, Finset.empty_subset _, hc⟩
  | insert i J hi ih =>
    intro u hu hsq
    obtain ⟨m, hm⟩ := hsq
    rw [Finset.coe_insert] at hu
    obtain ⟨A, hA, B, hB, rfl⟩ := exists_eq_add_mul_of_mem_insert (J : Set I) i hu
    have hA' := (mem_adjoin_iff_mem_monoSpan hr (J : Set I)).mpr hA
    have hB' := (mem_adjoin_iff_mem_monoSpan hr (J : Set I)).mpr hB
    set F := IntermediateField.adjoin M (r '' (J : Set I))
    have hX : A ^ 2 + B ^ 2 * algebraMap M E (a i) - algebraMap M E m ∈ F :=
      sub_mem (add_mem (pow_mem hA' 2) (mul_mem (pow_mem hB' 2) (F.algebraMap_mem _)))
        (F.algebraMap_mem _)
    have hY : 2 * (A * B) ∈ F := mul_mem (ofNat_mem F 2) (mul_mem hA' hB')
    have hY0 : 2 * (A * B) = 0 :=
      eq_zero_of_add_mul_eq_zero hr ha hi ih
        ((mem_adjoin_iff_mem_monoSpan hr _).mp hX) ((mem_adjoin_iff_mem_monoSpan hr _).mp hY)
        (by linear_combination hm - B ^ 2 * hr i)
    have h2E : (2 : E) ≠ 0 := by
      rw [← map_ofNat (algebraMap M E) 2]
      exact (map_ne_zero _).mpr h2
    rcases mul_eq_zero.mp ((mul_eq_zero.mp hY0).resolve_left h2E) with hA0 | hB0
    · subst hA0
      have hα : algebraMap M E (a i) ≠ 0 := (map_ne_zero _).mpr (ha.ne_zero i)
      have hBsq : B ^ 2 = algebraMap M E (m / a i) := by
        rw [map_div₀, eq_div_iff hα]
        linear_combination hm - B ^ 2 * hr i
      obtain ⟨c, U, hU, hcU⟩ := ih B hB ⟨m / a i, hBsq⟩
      refine ⟨c, insert i U, Finset.insert_subset_insert i hU, ?_⟩
      rw [zero_add, hcU, mono_insert r (fun h => hi (hU h)), smul_mul_assoc,
        mul_comm (mono r U)]
    · obtain ⟨c, U, hU, hcU⟩ := ih A hA ⟨m, by rw [hB0, zero_mul, add_zero] at hm; exact hm⟩
      exact ⟨c, U, hU.trans (Finset.subset_insert i J), by rw [hB0, zero_mul, add_zero, hcU]⟩

/-- Linear independence of the monomials `r_U` over a finite powerset. -/
theorem sum_powerset_eq_zero (hr : ∀ i, r i ^ 2 = algebraMap M E (a i))
    (ha : IndependentSquareClasses a) (h2 : (2 : M) ≠ 0) (J : Finset I) :
    ∀ g : Finset I → M, ∑ U ∈ J.powerset, g U • mono r U = 0 →
      ∀ U ∈ J.powerset, g U = 0 := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    intro g hg U hU
    rw [Finset.powerset_empty, Finset.sum_singleton, mono_empty] at hg
    rw [Finset.powerset_empty, Finset.mem_singleton] at hU
    subst hU
    simpa using hg
  | insert i J hi ih =>
    intro g hg
    rw [Finset.sum_powerset_insert hi] at hg
    have hmul : ∑ U ∈ J.powerset, g (insert i U) • mono r (insert i U) =
        (∑ U ∈ J.powerset, g (insert i U) • mono r U) * r i := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun U hU => ?_
      rw [mono_insert r (fun h => hi (Finset.mem_powerset.mp hU h)), smul_mul_assoc,
        mul_comm (mono r U)]
    rw [hmul] at hg
    have hmem : ∀ h : Finset I → M,
        ∑ U ∈ J.powerset, h U • mono r U ∈ monoSpan M r (J : Set I) :=
      fun h => Submodule.sum_mem _ fun U hU => Submodule.smul_mem _ _
        (mono_mem_monoSpan (Finset.coe_subset.mpr (Finset.mem_powerset.mp hU)))
    have hy := eq_zero_of_add_mul_eq_zero hr ha hi
      (exists_eq_smul_mono_of_sq hr ha h2 J) (hmem g) (hmem _) hg
    rw [hy, zero_mul, add_zero] at hg
    have g1 := ih g hg
    have g2 := ih (fun U => g (insert i U)) hy
    intro W hW
    rw [Finset.mem_powerset] at hW
    by_cases hiW : i ∈ W
    · rw [← Finset.insert_erase hiW]
      exact g2 (W.erase i) (Finset.mem_powerset.mpr (Finset.subset_insert_iff.mp hW))
    · exact g1 W (Finset.mem_powerset.mpr ((Finset.subset_insert_iff_of_notMem hiW).mp hW))

/-- `tail:lem:signs`, independence: the monomials `r_U = ∏ i ∈ U, r i`, indexed by
all finite subsets `U` of the arbitrary index set `I`, are linearly independent
over `M`. -/
theorem linearIndependent_mono (hr : ∀ i, r i ^ 2 = algebraMap M E (a i))
    (ha : IndependentSquareClasses a) (h2 : (2 : M) ≠ 0) :
    LinearIndependent M (mono r) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg U hU
  have hsub : ∀ V ∈ s, V ⊆ s.sup id := fun V hV => Finset.le_sup (f := id) hV
  have e1 : ∑ V ∈ s, (if V ∈ s then g V else 0) • mono r V =
      ∑ V ∈ (s.sup id).powerset, (if V ∈ s then g V else 0) • mono r V :=
    Finset.sum_subset (fun V hV => Finset.mem_powerset.mpr (hsub V hV))
      (fun V _ hV => by rw [if_neg hV, zero_smul])
  have key := sum_powerset_eq_zero hr ha h2 (s.sup id) (fun V => if V ∈ s then g V else 0)
    (by rw [← e1, ← hg]; exact Finset.sum_congr rfl fun V hV => by rw [if_pos hV])
    U (Finset.mem_powerset.mpr (hsub U hU))
  simpa [hU] using key

/-- The monomial basis of an intermediate field `F` known to be the span of the
monomials `r_U`, `U ⊆ S`. -/
def monoBasis (hr : ∀ i, r i ^ 2 = algebraMap M E (a i)) (ha : IndependentSquareClasses a)
    (h2 : (2 : M) ≠ 0) (F : IntermediateField M E) (S : Set I)
    (hF : ∀ x, x ∈ F ↔ x ∈ monoSpan M r S) :
    Basis {U : Finset I // (U : Set I) ⊆ S} M F :=
  Basis.mk (v := fun U => ⟨mono r U.1, (hF _).mpr (mono_mem_monoSpan U.2)⟩)
    (LinearIndependent.of_comp F.val.toLinearMap
      ((linearIndependent_mono hr ha h2).comp Subtype.val Subtype.val_injective))
    (by
      intro x _
      have hx : (x : E) ∈ span M (mono r '' {U : Finset I | (U : Set I) ⊆ S}) := (hF x).mp x.2
      have hmap : (span M (Set.range fun U : {U : Finset I // (U : Set I) ⊆ S} =>
          (⟨mono r U.1, (hF _).mpr (mono_mem_monoSpan U.2)⟩ : F))).map F.val.toLinearMap =
          span M (mono r '' {U : Finset I | (U : Set I) ⊆ S}) := by
        rw [Submodule.map_span, ← Set.range_comp]
        congr 1
        ext y
        constructor
        · rintro ⟨U, rfl⟩
          exact ⟨U.1, U.2, rfl⟩
        · rintro ⟨U, hU, rfl⟩
          exact ⟨⟨U, hU⟩, rfl⟩
      rw [← hmap] at hx
      obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hx
      have hyx' : y = x := Subtype.ext hyx
      rwa [← hyx'])

theorem monoBasis_apply (hr : ∀ i, r i ^ 2 = algebraMap M E (a i))
    (ha : IndependentSquareClasses a) (h2 : (2 : M) ≠ 0) (F : IntermediateField M E)
    (S : Set I) (hF : ∀ x, x ∈ F ↔ x ∈ monoSpan M r S) (U : {U : Finset I // (U : Set I) ⊆ S}) :
    (monoBasis hr ha h2 F S hF U : E) = mono r U.1 := by
  rw [monoBasis, Basis.mk_apply]

/-- `tail:lem:signs`, basis: the monomials `∏ i ∈ U, r i`, `U ⊆ S`, form an `M`-basis of
`M(r i : i ∈ S)`, for an arbitrary set `S` of indices. -/
def adjoinBasis (hr : ∀ i, r i ^ 2 = algebraMap M E (a i)) (ha : IndependentSquareClasses a)
    (h2 : (2 : M) ≠ 0) (S : Set I) :
    Basis {U : Finset I // (U : Set I) ⊆ S} M (IntermediateField.adjoin M (r '' S)) :=
  monoBasis hr ha h2 _ S fun _ => mem_adjoin_iff_mem_monoSpan hr S

theorem adjoinBasis_apply (hr : ∀ i, r i ^ 2 = algebraMap M E (a i))
    (ha : IndependentSquareClasses a) (h2 : (2 : M) ≠ 0) (S : Set I)
    (U : {U : Finset I // (U : Set I) ⊆ S}) :
    (adjoinBasis hr ha h2 S U : E) = ∏ i ∈ U.1, r i :=
  monoBasis_apply hr ha h2 _ S _ U

/-- `tail:lem:signs`, degree: for finite `J`, the extension `M(r i : i ∈ J) / M` has
degree `2 ^ |J|`. -/
theorem finrank_adjoin (hr : ∀ i, r i ^ 2 = algebraMap M E (a i))
    (ha : IndependentSquareClasses a) (h2 : (2 : M) ≠ 0) (J : Finset I) :
    Module.finrank M (IntermediateField.adjoin M (r '' (J : Set I))) = 2 ^ J.card := by
  rw [Module.finrank_eq_nat_card_basis (adjoinBasis hr ha h2 (J : Set I)),
    Nat.card_congr (Equiv.subtypeEquivRight fun U => by
      rw [Finset.coe_subset, ← Finset.mem_powerset] :
        {U : Finset I // (U : Set I) ⊆ J} ≃ {U // U ∈ J.powerset}),
    Nat.card_eq_finsetCard, Finset.card_powerset]

section Signs

variable (hr : ∀ i, r i ^ 2 = algebraMap M E (a i)) (ha : IndependentSquareClasses a)
  (h2 : (2 : M) ≠ 0) (F : IntermediateField M E) (S : Set I)
  (hF : ∀ x, x ∈ F ↔ x ∈ monoSpan M r S) (ε : I → M)

/-- The `M`-linear sign change multiplying the basis monomial `r_U` by `∏ i ∈ U, ε i`. -/
def signLinear : F →ₗ[M] F :=
  (monoBasis hr ha h2 F S hF).constr M fun U => (∏ i ∈ U.1, ε i) • monoBasis hr ha h2 F S hF U

theorem signLinear_basis (U : {U : Finset I // (U : Set I) ⊆ S}) :
    signLinear hr ha h2 F S hF ε (monoBasis hr ha h2 F S hF U) =
      (∏ i ∈ U.1, ε i) • monoBasis hr ha h2 F S hF U :=
  Basis.constr_basis _ _ _ _

theorem monoBasis_mul [DecidableEq I] (U V : {U : Finset I // (U : Set I) ⊆ S}) :
    monoBasis hr ha h2 F S hF U * monoBasis hr ha h2 F S hF V =
      (∏ i ∈ U.1 ∩ V.1, a i) • monoBasis hr ha h2 F S hF
        ⟨(U.1 ∪ V.1) \ (U.1 ∩ V.1), by
          refine (Finset.coe_subset.mpr Finset.sdiff_subset).trans ?_
          rw [Finset.coe_union]
          exact Set.union_subset U.2 V.2⟩ := by
  apply Subtype.ext
  rw [IntermediateField.coe_mul, IntermediateField.coe_smul, monoBasis_apply, monoBasis_apply,
    monoBasis_apply, mono_mul_mono hr, Algebra.smul_def]

variable {ε}

theorem signLinear_mul (hε : ∀ i, ε i = 1 ∨ ε i = -1) (x y : F) :
    signLinear hr ha h2 F S hF ε (x * y) =
      signLinear hr ha h2 F S hF ε x * signLinear hr ha h2 F S hF ε y := by
  classical
  have hsq : ∀ i, ε i ^ 2 = 1 := fun i => by rcases hε i with h | h <;> simp [h]
  set φ := signLinear hr ha h2 F S hF ε
  have key : (LinearMap.mul M F).compr₂ φ = (LinearMap.mul M F).compl₁₂ φ φ := by
    refine LinearMap.ext_basis (monoBasis hr ha h2 F S hF) (monoBasis hr ha h2 F S hF)
      fun U V => ?_
    rw [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply',
      LinearMap.mul_apply', monoBasis_mul, map_smul, signLinear_basis, signLinear_basis,
      signLinear_basis, smul_mul_smul_comm, monoBasis_mul, smul_smul, smul_smul]
    congr 1
    rw [prod_mul_prod_eq, Finset.prod_eq_one fun i _ => hsq i, one_mul, mul_comm]
  exact LinearMap.congr_fun₂ key x y

theorem signLinear_one : signLinear hr ha h2 F S hF ε 1 = 1 := by
  have h1 : (1 : F) = monoBasis hr ha h2 F S hF ⟨∅, by simp⟩ := by
    apply Subtype.ext
    rw [monoBasis_apply, mono_empty]
    rfl
  rw [h1, signLinear_basis, Finset.prod_empty, one_smul]

theorem signLinear_signLinear (hε : ∀ i, ε i = 1 ∨ ε i = -1) (x : F) :
    signLinear hr ha h2 F S hF ε (signLinear hr ha h2 F S hF ε x) = x := by
  have hsq : ∀ i, ε i ^ 2 = 1 := fun i => by rcases hε i with h | h <;> simp [h]
  have key : (signLinear hr ha h2 F S hF ε).comp (signLinear hr ha h2 F S hF ε) =
      LinearMap.id := by
    refine (monoBasis hr ha h2 F S hF).ext fun U => ?_
    rw [LinearMap.comp_apply, signLinear_basis, map_smul, signLinear_basis, smul_smul,
      ← Finset.prod_mul_distrib, Finset.prod_eq_one fun i _ => by rw [← sq, hsq],
      one_smul, LinearMap.id_apply]
  exact LinearMap.congr_fun key x

/-- The sign changes as an `M`-algebra endomorphism. -/
def signAlgHom (hε : ∀ i, ε i = 1 ∨ ε i = -1) : F →ₐ[M] F :=
  AlgHom.ofLinearMap (signLinear hr ha h2 F S hF ε) (signLinear_one hr ha h2 F S hF)
    (signLinear_mul hr ha h2 F S hF hε)

/-- `tail:lem:signs`, sign automorphisms: the `M`-automorphism of `F` sending `r_U` to
`(∏ i ∈ U, ε i) r_U` (`signAut_monoBasis`). It is an involution (`signAut_signAut`). -/
def signAut (hε : ∀ i, ε i = 1 ∨ ε i = -1) : F ≃ₐ[M] F :=
  AlgEquiv.ofAlgHom (signAlgHom hr ha h2 F S hF hε) (signAlgHom hr ha h2 F S hF hε)
    (AlgHom.ext fun x => signLinear_signLinear hr ha h2 F S hF hε x)
    (AlgHom.ext fun x => signLinear_signLinear hr ha h2 F S hF hε x)

theorem signAut_monoBasis (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (U : {U : Finset I // (U : Set I) ⊆ S}) :
    signAut hr ha h2 F S hF hε (monoBasis hr ha h2 F S hF U) =
      (∏ i ∈ U.1, ε i) • monoBasis hr ha h2 F S hF U :=
  signLinear_basis hr ha h2 F S hF ε U

/-- The sign automorphism is an involution. -/
theorem signAut_signAut (hε : ∀ i, ε i = 1 ∨ ε i = -1) (x : F) :
    signAut hr ha h2 F S hF hε (signAut hr ha h2 F S hF hε x) = x :=
  signLinear_signLinear hr ha h2 F S hF hε x

/-- `tail:lem:signs`: the sign automorphism sends `r i` to `ε i r i` for `i ∈ S`. -/
theorem signAut_apply (hε : ∀ i, ε i = 1 ∨ ε i = -1) {i : I} (hi : i ∈ S) (hri : r i ∈ F) :
    (signAut hr ha h2 F S hF hε ⟨r i, hri⟩ : E) = ε i • r i := by
  have h1 : (⟨r i, hri⟩ : F) = monoBasis hr ha h2 F S hF ⟨{i}, by simpa using hi⟩ := by
    apply Subtype.ext
    rw [monoBasis_apply, mono_singleton]
  rw [h1, signAut_monoBasis, IntermediateField.coe_smul, monoBasis_apply, Finset.prod_singleton,
    mono_singleton]

end Signs

/-- `L = M(r i : i ∈ I)` is the span of all monomials. -/
theorem mem_adjoin_range_iff (hr : ∀ i, r i ^ 2 = algebraMap M E (a i)) {x : E} :
    x ∈ IntermediateField.adjoin M (Set.range r) ↔ x ∈ monoSpan M r Set.univ := by
  rw [← Set.image_univ]
  exact mem_adjoin_iff_mem_monoSpan hr Set.univ

/-- `tail:lem:signs`: every sign assignment `r i ↦ ε i r i`, `ε i ∈ {1, -1}`, extends to an
`M`-automorphism of `L = M(r i : i ∈ I)`. -/
theorem exists_signAut (hr : ∀ i, r i ^ 2 = algebraMap M E (a i))
    (ha : IndependentSquareClasses a) (h2 : (2 : M) ≠ 0) (ε : I → M)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    ∃ σ : IntermediateField.adjoin M (Set.range r) ≃ₐ[M]
        IntermediateField.adjoin M (Set.range r),
      ∀ i (hri : r i ∈ IntermediateField.adjoin M (Set.range r)),
        (σ ⟨r i, hri⟩ : E) = ε i • r i :=
  ⟨signAut hr ha h2 _ Set.univ (fun _ => mem_adjoin_range_iff hr) hε,
    fun _ hri => signAut_apply hr ha h2 _ Set.univ _ hε (Set.mem_univ _) hri⟩

section Hahn

open Surreal.HahnSeries

variable {Γ : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]

/-- The coefficientwise extension of a ring automorphism to Hahn series. -/
def hahnAut {K : Type*} [CommRing K] (σ : K ≃+* K) : HahnSeries Γ K ≃+* HahnSeries Γ K :=
  RingEquiv.ofRingHom (mapCoefficients (σ : K →+* K)) (mapCoefficients (σ.symm : K →+* K))
    (RingHom.ext fun x => by ext g; simp)
    (RingHom.ext fun x => by ext g; simp)

@[simp] theorem coeff_hahnAut {K : Type*} [CommRing K] (σ : K ≃+* K) (x : HahnSeries Γ K)
    (g : Γ) : (hahnAut σ x).coeff g = σ (x.coeff g) :=
  rfl

variable (hr : ∀ i, r i ^ 2 = algebraMap M E (a i)) (ha : IndependentSquareClasses a)
  (h2 : (2 : M) ≠ 0) (F : IntermediateField M E) (S : Set I)
  (hF : ∀ x, x ∈ F ↔ x ∈ monoSpan M r S) {ε : I → M} (hε : ∀ i, ε i = 1 ∨ ε i = -1)

/-- `tail:lem:signs`, Hahn extension: the sign automorphism acting coefficientwise on
`F((t^Γ))`. -/
def hahnSignAut : HahnSeries Γ F ≃+* HahnSeries Γ F :=
  hahnAut (signAut hr ha h2 F S hF hε : F ≃+* F)

theorem coeff_hahnSignAut (x : HahnSeries Γ F) (g : Γ) :
    (hahnSignAut hr ha h2 F S hF hε x).coeff g = signAut hr ha h2 F S hF hε (x.coeff g) :=
  rfl

/-- The coefficientwise extension restricts to the sign automorphism on constants
and, more generally, on single terms `c t^g`: it sends `single g c` to
`single g (σ c)`, where `σ` is the sign automorphism of `F`. -/
theorem hahnSignAut_single (g : Γ) (c : F) :
    hahnSignAut hr ha h2 F S hF hε (HahnSeries.single g c) =
      HahnSeries.single g (signAut hr ha h2 F S hF hε c) := by
  ext g'
  rw [coeff_hahnSignAut, HahnSeries.coeff_single, HahnSeries.coeff_single]
  split_ifs <;> simp

/-- `tail:lem:signs`, Hahn extension: the coefficientwise sign automorphism fixes the
image of `M((t^Γ))`. -/
theorem hahnSignAut_mapCoefficients_algebraMap (x : HahnSeries Γ M) :
    hahnSignAut hr ha h2 F S hF hε (mapCoefficients (algebraMap M F) x) =
      mapCoefficients (algebraMap M F) x := by
  ext g
  rw [coeff_hahnSignAut, coeff_mapCoefficients, AlgEquiv.commutes]

end Hahn

section HahnRange

open Surreal.HahnSeries

variable {Γ : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]

/-- `tail:lem:signs`, sign changes for `L = M(r i : i ∈ I)`: every assignment
`r i ↦ ε i r i` with `ε i ∈ {1, -1}` extends to an `M`-automorphism `σ` of `L`, and `σ`
extends coefficientwise to a ring automorphism of `L((t^Γ))` fixing the coefficientwise
image of `M((t^Γ))`. -/
theorem exists_signAut_hahn (hr : ∀ i, r i ^ 2 = algebraMap M E (a i))
    (ha : IndependentSquareClasses a) (h2 : (2 : M) ≠ 0) (ε : I → M)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    ∃ σ : IntermediateField.adjoin M (Set.range r) ≃ₐ[M]
        IntermediateField.adjoin M (Set.range r),
      (∀ i (hri : r i ∈ IntermediateField.adjoin M (Set.range r)),
        (σ ⟨r i, hri⟩ : E) = ε i • r i) ∧
      ∃ τ : HahnSeries Γ (IntermediateField.adjoin M (Set.range r)) ≃+*
          HahnSeries Γ (IntermediateField.adjoin M (Set.range r)),
        (∀ x g, (τ x).coeff g = σ (x.coeff g)) ∧
        ∀ x : HahnSeries Γ M,
          τ (mapCoefficients (algebraMap M _) x) = mapCoefficients (algebraMap M _) x :=
  ⟨signAut hr ha h2 _ Set.univ (fun _ => mem_adjoin_range_iff hr) hε,
    fun _ hri => signAut_apply hr ha h2 _ Set.univ _ hε (Set.mem_univ _) hri,
    hahnSignAut hr ha h2 _ Set.univ (fun _ => mem_adjoin_range_iff hr) hε,
    fun _ _ => rfl,
    hahnSignAut_mapCoefficients_algebraMap hr ha h2 _ Set.univ _ hε⟩

end HahnRange

end

end Surreal.TailSigns
