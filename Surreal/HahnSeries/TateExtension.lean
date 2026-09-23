import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Monoid.Prod
import Surreal.Algebra.TateCubicNode
import Surreal.HahnSeries.BoundedOrbitLocus
import Surreal.HahnSeries.ThetaDomain
import Surreal.HahnSeries.WorkspaceEmbedding

/-!
# Exponent embeddings and the extension obstruction for Hahn--Tate uniformization

This file formalizes `tate:thm:extension` (with `tate:eq:functorial`, `tate:eq:Hpullback` and
the example `tate:ex:extension`) and the group-theoretic core of
`tate:node:thm:obstruction` (with `tate:node:eq:kernel-extra`), together with the algebraic
parts of `tate:thm:tropical`, `tate:node:prop:residue` and `tate:eq:circlelayers`, all in
`docs/surcomplex/hahn-tate-uniformization/article.tex`.

## Exponent embeddings (`tate:thm:extension`)

`Γ` and `Γ' = Δ` are arbitrary linearly ordered abelian groups and `k` is an arbitrary field
(the source uses `ℂ`, or a field of characteristic zero). An ordered group embedding
`ι : Γ ↪ Γ'` is a strictly monotone additive map `e`, and `ι_*` is
`Surreal.HahnSeries.workspaceEmbedding e he`, an injective `k`-algebra homomorphism of the
Hahn fields, hence a field embedding.
* Strong sums: `ι_*` preserves and reflects strong summability of arbitrary families
  (`exists_summableFamily_workspaceEmbedding_iff`; reflection is `comapExponentsFamily`) and
  commutes with strong sums (`workspaceEmbedding_hahnStrongSum`, where `hahnStrongSum` is the
  strong sum, `0` for a non-summable family).
* `tate:eq:Hpullback`: `ι⁻¹(H_{ι(α)}) = H_α` for every `α` (`comap_admissibleGroup`); hence
  `ι_* u ∈ U_{ι_* q} ↔ u ∈ U_q` (`workspaceEmbedding_mem_admissibleDomain_iff`).
* `tate:eq:functorial` for `Θ`: the theta family is summable after the embedding exactly when
  before (`thetaSummable_workspaceEmbedding_iff`) and `ι_*(Θ_q(u)) = Θ_{ι_* q}(ι_* u)`
  (`workspaceEmbedding_theta`), for all `q, u`.
* Tate coefficients: `ι_*` commutes with `s_j`, `a₄`, `a₆` (`workspaceEmbedding_tateSum`,
  `workspaceEmbedding_tateA4`, `workspaceEmbedding_tateA6`), maps `E_q` to `E_{ι_* q}`
  (`map_tateCurve`), and `(ι_* x, ι_* y)` lies on `E_{ι_* q}` iff `(x, y)` lies on `E_q`.
* `tate:eq:functorial` for `X`, `Y` and `Φ`: the bilateral summands of `tate:eq:X`,
  `tate:eq:Y` (`xTerm`, `yTerm`) are summable after the embedding exactly when before, and for
  the formula-level definitions `coordX`, `coordY` (strong sums, `0` off the summability
  domain) and `tatePhi` (`tate:eq:phi`, with `O` encoded as `none` for `u ∈ q^ℤ`) one has
  `ι_*(X_q(u)) = X_{ι_* q}(ι_* u)`, the same for `Y`, and
  `ι_*(Φ_q(u)) = Φ_{ι_* q}(ι_* u)` (`map_tatePhi`), for every `u`, in particular on `U_q`.
* Last sentence: in the larger field the exact theta domain of `ι_* q` is `v⁻¹(H_{ι(α)})`
  (`thetaSummable_workspaceEmbedding_left_iff`), and in the example it is not all of
  `K_{Γ'}^×` (`admissibleDomain_ne_nonzero`).
* `tate:ex:extension`: `ℝ` is embedded as the second summand of `ℝ ⊕lex ℝ`
  (`secondSummand`), `q = t^1` goes to `t^{(0,1)}`; over `k((t^ℝ))` every nonzero parameter
  is admitted (`mem_admissibleDomain_real`), over `k((t^{ℝ ⊕lex ℝ}))` no parameter of
  valuation `(1,0)` is admitted (`notMem_admissibleDomain_of_order_eq`), and `1 + t^{(1,0)}`
  is admitted (`one_add_single_mem_admissibleDomain`).

## The extension obstruction and the value and residue sequences

The source's proofs use only that `Φ_q : U_q → E_q(K)` is a surjective homomorphism with
kernel `q^ℤ` and that `v` is onto. They are proved here for an arbitrary group `G`, a
homomorphism `v : G → V` to a commutative group, a subgroup `H ≤ V`, `U = v⁻¹(H)` and any
`Φ : U → E` with these properties (`IsPeriodUniformization`); additive groups such as
`E_q(K)` enter through `Multiplicative`.
* `tate:node:thm:obstruction`: for any homomorphism `Ψ : G → E` extending `Φ`,
  `q ∈ ker Ψ`, `ker Ψ ∩ U = q^ℤ` (`ker_inf_comap`), and `tate:node:eq:kernel-extra` is exact:
  the kernel of `kerValue : ker Ψ → V/H` is `q^ℤ` (`ker_kerValue`) and `kerValue` is onto when
  `v` is (`kerValue_surjective`). Hence `ker Ψ = q^ℤ ↔ H = V` (`ker_eq_zpowers_iff`), and for
  `H ≠ V` no extension has kernel `q^ℤ` (`not_exists_extension`).
* `tate:thm:tropical`: `trop : E → H/v(q)^ℤ` with `trop(Φ(u)) = v(u) mod v(q)^ℤ`
  (`trop_apply`, `tate:eq:tropical`) is onto (`trop_surjective`); `Φ` is injective on
  `O_v^× = ker v` when `v(q)` has infinite order (`unitsMap_injective`) and
  `ker trop = Φ(O_v^×)` (`ker_trop`), which is `tate:eq:tropical-seq`. Every class of the
  additive quotient `H_α/ℤα` has a unique representative in `[0, α)`
  (`existsUnique_representative`, from `tate:lem:normalize`); the same holds for the
  multiplicative quotient `H_α/α^ℤ` inside `Multiplicative Γ`, the codomain of `trop` at the
  Hahn instance (`existsUnique_representative_mul`).
* `tate:node:prop:residue`, with the sequence `tate:node:eq:residueexact`: for
  `r : O_v^× → R`, `res ∘ Φ⁻¹ : E^v_0 = Φ(O_v^×) → R` (`residueMap`) is onto when `r` is
  (`residueMap_surjective`), its kernel is `E^v_1 = Φ(ker r)` (`ker_residueMap`), and
  `E^v_1 ≅ ker r` (`fineLayerEquiv`).
* Hahn instance, `K = k⟦Γ⟧`: the valuation `unitsValuation : K^× → Γ` (multiplicatively) is
  onto, `admissibleUnits q` is `U_q`, `v(q) > 0` gives infinite order, and the residue
  `hahnResidue` (leading coefficient on `O_v^×`) is onto `k^×` with kernel `1 + 𝔪_v`
  (`mem_ker_hahnResidue_iff`). This gives `hahn_ker_eq_zpowers_iff`,
  `hahn_not_exists_extension`, `hahn_kerValue_surjective`, `hahn_trop_surjective`,
  `hahn_ker_trop`, `hahn_unitsMap_injective`, `hahn_existsUnique_trop_representative` and
  `hahn_residue_exact` (`tate:node:eq:residueexact`) for every `Φ : U_q → E` with the
  properties of `Φ_q`.
* `tate:eq:circlelayers`: for any abelian group `A`, subgroup `B` and `a` with
  `B ∩ ℤa = 0`, the sequence `0 → B → A/ℤa → (A/B)/ℤā → 0` is exact (`layerIncl_injective`,
  `range_layerIncl`, `layerProj_surjective`). With `A = H_α` and `B = H_α^-`, this is
  `circleLayers_exact`. Here `tate:eq:Hminus` is the definition `minusLayer` (the existing
  `coarseSubgroup` of `Γ`, viewed inside `H_α`), with `H_α^- ⊆ H_α`
  (`coarseSubgroup_le_admissibleGroup`), `H_α^- ∩ ℤα = 0` (`minusLayer_inf_zmultiples`),
  and `H_α^-` the largest proper convex subgroup of `H_α` (`isGreatest_minusLayer`).

## Pending

`Φ_q` is not formalized as a map to the group `E_q(K)`: the coordinate-domain theorem
`tate:thm:coordinates` for `coordX`, `coordY`, the curve equation of `(X_q(u), Y_q(u))`, and
the homomorphism, surjectivity and kernel clauses of `tate:thm:main`. Consequently the
statements about `tatePhi` are identities of formulas, and the instances of
`tate:node:thm:obstruction`, `tate:thm:tropical` and `tate:node:prop:residue` at the actual
Tate curve are conditional on a `Φ` with the properties of `Φ_q`. Also pending: the
translation-invariant circular order of `tate:thm:tropical`, the claim after `tate:eq:Hminus`
that `H_α/H_α^-` is Archimedean (and its Hölder embedding in `ℝ`; only its nonvanishing,
`H_α^- ≠ H_α`, is proved, as part of `isGreatest_minusLayer`), the
identification of `E^v_0`, `E^v_1` with the reduction strata in `tate:node:prop:residue`'s
subsection, the remark there that `E_1(K) ⊊ E^v_1`, and the clause of `tate:ex:extension`
that `Φ_q(1 + t^{(1,0)})` reduces to `O` for the coarse valuation.
-/

namespace Surreal.TateExtension

open _root_.HahnSeries Surreal.HahnSeries Surreal.Tate Surreal.TateNode

noncomputable section

/-! ### Strong sums along an exponent embedding -/

section StrongSums

variable {Γ Δ k : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [AddCommGroup Δ] [LinearOrder Δ] [IsOrderedAddMonoid Δ] [Field k]
  (e : Γ →+ Δ) (he : StrictMono e)

/-- The valuation is transported by the exponent embedding: `v(ι_* x) = ι(v(x))`, including
`x = 0` (where Mathlib's `order` is `0`). -/
theorem order_workspaceEmbedding (x : k⟦Γ⟧) :
    (workspaceEmbedding e he x).order = e x.order := by
  by_cases hx : x = 0
  · rw [hx, map_zero, order_zero, order_zero, map_zero]
  have hx' : workspaceEmbedding e he x ≠ 0 :=
    (map_ne_zero_iff _ (workspaceEmbedding_injective e he)).mpr hx
  apply WithTop.coe_injective
  rw [order_eq_orderTop_of_ne_zero hx', orderTop_workspaceEmbedding,
    ← order_eq_orderTop_of_ne_zero hx, WithTop.map_coe]

/-- Reflection of strong summability: if the transported family `ι_* ∘ f` is strongly
summable, so is `f`. -/
def comapExponentsFamily {ι : Type*} (f : ι → k⟦Γ⟧) (s : SummableFamily Δ k ι)
    (hs : ∀ i, s i = workspaceEmbedding e he (f i)) : SummableFamily Γ k ι where
  toFun := f
  isPWO_iUnion_support' := by
    rw [Set.IsPWO, Set.partiallyWellOrderedOn_iff_exists_lt]
    intro g hg
    have key : ∀ n, e (g n) ∈ ⋃ i, (s i).support := fun n => by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hg n)
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      rw [hs, support_workspaceEmbedding]
      exact Set.mem_image_of_mem e hi
    obtain ⟨m, n, hmn, hle⟩ := s.isPWO_iUnion_support.exists_lt key
    exact ⟨m, n, hmn, he.le_iff_le.mp hle⟩
  finite_co_support' g := by
    refine (s.finite_co_support' (e g)).subset fun i hi => ?_
    change (s i).coeff (e g) ≠ 0
    rw [hs, workspaceEmbedding_coeff]
    exact hi

/-- `tate:thm:extension`: the embedding `ι_*` preserves and reflects strong summability of an
arbitrary family. -/
theorem exists_summableFamily_workspaceEmbedding_iff {ι : Type*} (f : ι → k⟦Γ⟧) :
    (∃ s : SummableFamily Δ k ι, ⇑s = fun i => workspaceEmbedding e he (f i)) ↔
      ∃ s : SummableFamily Γ k ι, ⇑s = f := by
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨comapExponentsFamily e he f s fun i => congrFun hs i, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨mapExponentsFamily e he s, rfl⟩

end StrongSums

section StrongSum

section Generic

variable {Γ R : Type*} [PartialOrder Γ] [AddCommMonoid R]

open Classical in
/-- The strong Hahn sum of a family when it is strongly summable, and `0` otherwise. -/
def hahnStrongSum {ι : Type*} (f : ι → R⟦Γ⟧) : R⟦Γ⟧ :=
  if h : ∃ s : SummableFamily Γ R ι, ⇑s = f then h.choose.hsum else 0

theorem hahnStrongSum_eq_hsum {ι : Type*} {f : ι → R⟦Γ⟧} {s : SummableFamily Γ R ι}
    (hs : ⇑s = f) : hahnStrongSum f = s.hsum := by
  have h : ∃ s : SummableFamily Γ R ι, ⇑s = f := ⟨s, hs⟩
  rw [hahnStrongSum, dif_pos h, SummableFamily.coe_injective (h.choose_spec.trans hs.symm)]

theorem hahnStrongSum_of_not {ι : Type*} {f : ι → R⟦Γ⟧}
    (h : ¬∃ s : SummableFamily Γ R ι, ⇑s = f) : hahnStrongSum f = 0 :=
  dif_neg h

end Generic

variable {Γ k : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field k]

/-- `Θ_q(u)` is the strong sum of the theta family. -/
theorem theta_eq_hahnStrongSum (q u : k⟦Γ⟧) : theta q u = hahnStrongSum (thetaTerm q u) := by
  by_cases h : ThetaSummable q u
  · obtain ⟨s, hs⟩ := h
    rw [theta_eq_hsum hs, hahnStrongSum_eq_hsum hs]
  · rw [theta, dif_neg h, hahnStrongSum_of_not h]

end StrongSum

/-! ### Functoriality of the Tate formulas (`tate:thm:extension`) -/

section Extension

variable {Γ Δ k : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [AddCommGroup Δ] [LinearOrder Δ] [IsOrderedAddMonoid Δ] [Field k]
  (e : Γ →+ Δ) (he : StrictMono e)

/-- `tate:thm:extension`: `ι_*` commutes with strong sums of arbitrary families; both sides
are `0` when the family is not strongly summable. -/
theorem workspaceEmbedding_hahnStrongSum {ι : Type*} (f : ι → k⟦Γ⟧) :
    workspaceEmbedding e he (hahnStrongSum f) =
      hahnStrongSum fun i => workspaceEmbedding e he (f i) := by
  by_cases h : ∃ s : SummableFamily Γ k ι, ⇑s = f
  · obtain ⟨s, rfl⟩ := h
    rw [hahnStrongSum_eq_hsum rfl, ← hsum_mapExponentsFamily]
    exact (hahnStrongSum_eq_hsum (s := mapExponentsFamily e he s) rfl).symm
  · rw [hahnStrongSum_of_not h, map_zero, hahnStrongSum_of_not]
    rwa [exists_summableFamily_workspaceEmbedding_iff]

include he in
/-- `tate:thm:extension`, equation `tate:eq:Hpullback`: `ι⁻¹(H_{ι(α)}) = H_α`, for every
`α`. -/
theorem comap_admissibleGroup (α : Γ) :
    (admissibleGroup (e α)).comap e = admissibleGroup α := by
  ext γ
  rw [AddSubgroup.mem_comap, mem_admissibleGroup, mem_admissibleGroup]
  refine exists_congr fun N => ?_
  rw [← map_nsmul, ← map_neg, he.le_iff_le, he.le_iff_le]

theorem workspaceEmbedding_thetaTerm (q u : k⟦Γ⟧) (n : ℤ) :
    workspaceEmbedding e he (thetaTerm q u n) =
      thetaTerm (workspaceEmbedding e he q) (workspaceEmbedding e he u) n := by
  simp only [thetaTerm, map_mul, map_zpow₀, map_neg, map_one]

/-- `tate:thm:extension` for `Θ`: the theta family of `(ι_* q, ι_* u)` is strongly summable
exactly when that of `(q, u)` is. -/
theorem thetaSummable_workspaceEmbedding_iff (q u : k⟦Γ⟧) :
    ThetaSummable (workspaceEmbedding e he q) (workspaceEmbedding e he u) ↔
      ThetaSummable q u := by
  have h : thetaTerm (workspaceEmbedding e he q) (workspaceEmbedding e he u) =
      fun n => workspaceEmbedding e he (thetaTerm q u n) :=
    funext fun n => (workspaceEmbedding_thetaTerm e he q u n).symm
  rw [ThetaSummable, ThetaSummable, h, exists_summableFamily_workspaceEmbedding_iff]

/-- `tate:thm:extension`, equation `tate:eq:functorial` for `Θ`:
`ι_*(Θ_q(u)) = Θ_{ι_* q}(ι_* u)`, unconditionally (both sides are `0` off the domain). -/
theorem workspaceEmbedding_theta (q u : k⟦Γ⟧) :
    workspaceEmbedding e he (theta q u) =
      theta (workspaceEmbedding e he q) (workspaceEmbedding e he u) := by
  rw [theta_eq_hahnStrongSum, theta_eq_hahnStrongSum, workspaceEmbedding_hahnStrongSum]
  congr 1
  funext n
  exact workspaceEmbedding_thetaTerm e he q u n

/-- `tate:thm:extension`: an old parameter is admissible after the embedding exactly when it
was admissible before: `ι_* u ∈ U_{ι_* q} ↔ u ∈ U_q`. -/
theorem workspaceEmbedding_mem_admissibleDomain_iff (q u : k⟦Γ⟧) :
    workspaceEmbedding e he u ∈ admissibleDomain (workspaceEmbedding e he q) ↔
      u ∈ admissibleDomain q := by
  simp only [admissibleDomain, Set.mem_setOf_eq, order_workspaceEmbedding,
    map_ne_zero_iff _ (workspaceEmbedding_injective e he)]
  rw [← AddSubgroup.mem_comap, comap_admissibleGroup e he]

/-- `tate:thm:extension`, last sentence: for `α = v(q) > 0`, in the larger field the exact
theta domain of `q' = ι_* q` is `v⁻¹(H_{ι(α)})`: for `u ∈ K_{Γ'}^×` the theta family of
`(q', u)` is strongly summable exactly when `v(u) ∈ H_{ι(α)}` (`tate:thm:theta` over `Γ'`). -/
theorem thetaSummable_workspaceEmbedding_left_iff {q : k⟦Γ⟧} (hq : 0 < q.order) {u : k⟦Δ⟧}
    (hu : u ≠ 0) :
    ThetaSummable (workspaceEmbedding e he q) u ↔ u.order ∈ admissibleGroup (e q.order) := by
  have hq' : 0 < (workspaceEmbedding e he q).order := by
    rw [order_workspaceEmbedding, ← e.map_zero]
    exact he hq
  rw [thetaSummable_iff hq' hu, order_workspaceEmbedding]

theorem workspaceEmbedding_cutPeriod (q : k⟦Γ⟧) :
    workspaceEmbedding e he (cutPeriod q) = cutPeriod (workspaceEmbedding e he q) := by
  by_cases hq : 0 < q.orderTop
  · rw [cutPeriod_of_pos hq,
      cutPeriod_of_pos ((orderTop_workspaceEmbedding_pos_iff e he q).mpr hq)]
  · rw [cutPeriod, cutPeriod, if_neg hq,
      if_neg (mt (orderTop_workspaceEmbedding_pos_iff e he q).mp hq), map_zero]

/-- `tate:thm:extension` for the Tate sums `s_j(q)` of `tate:eq:sk`. -/
theorem workspaceEmbedding_tateSum (j : ℕ) (q : k⟦Γ⟧) :
    workspaceEmbedding e he (tateSum j q) = tateSum j (workspaceEmbedding e he q) := by
  have h : mapExponentsFamily e he (tateFamily j q) =
      tateFamily j (workspaceEmbedding e he q) := by
    ext1 n
    rw [mapExponentsFamily_apply, tateFamily_apply, tateFamily_apply, map_smul, map_div₀,
      map_sub, map_one, map_pow, workspaceEmbedding_cutPeriod]
  rw [tateSum, tateSum, ← hsum_mapExponentsFamily, h]

/-- `tate:thm:extension` for `a₄(q)` of `tate:eq:ak`. -/
theorem workspaceEmbedding_tateA4 (q : k⟦Γ⟧) :
    workspaceEmbedding e he (tateA4 q) = tateA4 (workspaceEmbedding e he q) := by
  rw [tateA4, tateA4, map_mul, map_neg, map_ofNat, workspaceEmbedding_tateSum]

/-- `tate:thm:extension` for `a₆(q)` of `tate:eq:ak`. -/
theorem workspaceEmbedding_tateA6 (q : k⟦Γ⟧) :
    workspaceEmbedding e he (tateA6 q) = tateA6 (workspaceEmbedding e he q) := by
  rw [tateA6, tateA6, map_div₀, map_neg, map_add, map_mul, map_mul, map_ofNat, map_ofNat,
    map_ofNat, workspaceEmbedding_tateSum, workspaceEmbedding_tateSum]

/-- `tate:thm:extension` for the curve `tate:eq:curve`: `ι_*(E_q) = E_{ι_* q}`. -/
theorem map_tateCurve (q : k⟦Γ⟧) :
    (tateCurve q).map ((workspaceEmbedding e he : k⟦Γ⟧ →ₐ[k] k⟦Δ⟧) : k⟦Γ⟧ →+* k⟦Δ⟧) =
      tateCurve (workspaceEmbedding e he q) := by
  ext <;> simp [tateCurve, workspaceEmbedding_tateA4, workspaceEmbedding_tateA6]

/-- `tate:thm:extension`: `(ι_* x, ι_* y)` lies on `E_{ι_* q}` exactly when `(x, y)` lies on
`E_q`. -/
theorem tateCurve_equation_workspaceEmbedding_iff (q x y : k⟦Γ⟧) :
    (tateCurve (workspaceEmbedding e he q)).toAffine.Equation (workspaceEmbedding e he x)
        (workspaceEmbedding e he y) ↔ (tateCurve q).toAffine.Equation x y := by
  rw [tateCurve_equation_iff, tateCurve_equation_iff, ← workspaceEmbedding_tateA4,
    ← workspaceEmbedding_tateA6, ← map_pow, ← map_mul, ← map_add, ← map_pow, ← map_mul,
    ← map_add, ← map_add, (workspaceEmbedding_injective e he).eq_iff]

/-- The `n`th summand `q^n u/(1 - q^n u)²` of the bilateral family of `tate:eq:X`. -/
def xTerm (q u : k⟦Γ⟧) (n : ℤ) : k⟦Γ⟧ := q ^ n * u / (1 - q ^ n * u) ^ 2

/-- The `n`th summand `(q^n u)²/(1 - q^n u)³` of the bilateral family of `tate:eq:Y`. -/
def yTerm (q u : k⟦Γ⟧) (n : ℤ) : k⟦Γ⟧ := (q ^ n * u) ^ 2 / (1 - q ^ n * u) ^ 3

/-- `tate:eq:X`: `X_q(u) = ∑_{n ∈ ℤ} q^n u/(1 - q^n u)² - 2 s₁(q)`, with the bilateral sum
taken as a strong sum (`0` when the family is not strongly summable). -/
def coordX (q u : k⟦Γ⟧) : k⟦Γ⟧ := hahnStrongSum (xTerm q u) - 2 * tateSum 1 q

/-- `tate:eq:Y`: `Y_q(u) = ∑_{n ∈ ℤ} (q^n u)²/(1 - q^n u)³ + s₁(q)`, with the same
convention. -/
def coordY (q u : k⟦Γ⟧) : k⟦Γ⟧ := hahnStrongSum (yTerm q u) + tateSum 1 q

open Classical in
/-- `tate:eq:phi` at the level of formulas: `Φ_q(u)` is the point at infinity `O` (encoded
as `none`) for `u ∈ q^ℤ` and the affine point `(X_q(u), Y_q(u))` otherwise. -/
def tatePhi (q u : k⟦Γ⟧) : Option (k⟦Γ⟧ × k⟦Γ⟧) :=
  if ∃ n : ℤ, q ^ n = u then none else some (coordX q u, coordY q u)

theorem workspaceEmbedding_xTerm (q u : k⟦Γ⟧) (n : ℤ) :
    workspaceEmbedding e he (xTerm q u n) =
      xTerm (workspaceEmbedding e he q) (workspaceEmbedding e he u) n := by
  simp only [xTerm, map_div₀, map_mul, map_zpow₀, map_pow, map_sub, map_one]

theorem workspaceEmbedding_yTerm (q u : k⟦Γ⟧) (n : ℤ) :
    workspaceEmbedding e he (yTerm q u n) =
      yTerm (workspaceEmbedding e he q) (workspaceEmbedding e he u) n := by
  simp only [yTerm, map_div₀, map_mul, map_zpow₀, map_pow, map_sub, map_one]

/-- `tate:thm:extension` for the bilateral family of `X`: it is strongly summable after the
embedding exactly when it was before. -/
theorem xTerm_summable_workspaceEmbedding_iff (q u : k⟦Γ⟧) :
    (∃ s : SummableFamily Δ k ℤ,
        ⇑s = xTerm (workspaceEmbedding e he q) (workspaceEmbedding e he u)) ↔
      ∃ s : SummableFamily Γ k ℤ, ⇑s = xTerm q u := by
  rw [← exists_summableFamily_workspaceEmbedding_iff e he]
  simp only [workspaceEmbedding_xTerm]

/-- `tate:thm:extension` for the bilateral family of `Y`. -/
theorem yTerm_summable_workspaceEmbedding_iff (q u : k⟦Γ⟧) :
    (∃ s : SummableFamily Δ k ℤ,
        ⇑s = yTerm (workspaceEmbedding e he q) (workspaceEmbedding e he u)) ↔
      ∃ s : SummableFamily Γ k ℤ, ⇑s = yTerm q u := by
  rw [← exists_summableFamily_workspaceEmbedding_iff e he]
  simp only [workspaceEmbedding_yTerm]

/-- `tate:thm:extension`, `tate:eq:functorial` for `X`: `ι_*(X_q(u)) = X_{ι_* q}(ι_* u)`. -/
theorem workspaceEmbedding_coordX (q u : k⟦Γ⟧) :
    workspaceEmbedding e he (coordX q u) =
      coordX (workspaceEmbedding e he q) (workspaceEmbedding e he u) := by
  rw [coordX, coordX, map_sub, map_mul, map_ofNat, workspaceEmbedding_tateSum,
    workspaceEmbedding_hahnStrongSum]
  simp only [workspaceEmbedding_xTerm]

/-- `tate:thm:extension`, `tate:eq:functorial` for `Y`: `ι_*(Y_q(u)) = Y_{ι_* q}(ι_* u)`. -/
theorem workspaceEmbedding_coordY (q u : k⟦Γ⟧) :
    workspaceEmbedding e he (coordY q u) =
      coordY (workspaceEmbedding e he q) (workspaceEmbedding e he u) := by
  rw [coordY, coordY, map_add, workspaceEmbedding_tateSum, workspaceEmbedding_hahnStrongSum]
  simp only [workspaceEmbedding_yTerm]

/-- `ι_*` preserves and reflects membership in `q^ℤ`. -/
theorem exists_zpow_workspaceEmbedding_iff (q u : k⟦Γ⟧) :
    (∃ n : ℤ, workspaceEmbedding e he q ^ n = workspaceEmbedding e he u) ↔
      ∃ n : ℤ, q ^ n = u := by
  simp only [← map_zpow₀, (workspaceEmbedding_injective e he).eq_iff]

/-- `tate:thm:extension`, equation `tate:eq:functorial`: `ι_*(Φ_q(u)) = Φ_{ι_* q}(ι_* u)`,
with `ι_*` acting on both coordinates of an affine point and fixing `O`. It holds for every
`u`, in particular on `U_q`. -/
theorem map_tatePhi (q u : k⟦Γ⟧) :
    (tatePhi q u).map (Prod.map (workspaceEmbedding e he) (workspaceEmbedding e he)) =
      tatePhi (workspaceEmbedding e he q) (workspaceEmbedding e he u) := by
  rw [tatePhi, tatePhi]
  by_cases h : ∃ n : ℤ, q ^ n = u
  · rw [if_pos h, if_pos ((exists_zpow_workspaceEmbedding_iff e he q u).mpr h),
      Option.map_none]
  · rw [if_neg h, if_neg (mt (exists_zpow_workspaceEmbedding_iff e he q u).mp h),
      Option.map_some, Prod.map_apply, workspaceEmbedding_coordX, workspaceEmbedding_coordY]

end Extension

/-! ### The example `tate:ex:extension` -/

section Example

variable {k : Type*} [Field k]

/-- `tate:ex:extension`: `ℝ` embedded as the second summand of `ℝ ⊕lex ℝ`. -/
def secondSummand : ℝ →+ Lex (ℝ × ℝ) where
  toFun r := toLex (0, r)
  map_zero' := rfl
  map_add' a b := by rw [← toLex_add, Prod.mk_add_mk, add_zero]

theorem strictMono_secondSummand : StrictMono secondSummand := fun _ _ h =>
  Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, h⟩)

/-- The first coordinate of `ℝ ⊕lex ℝ`, a monotone additive map. -/
def lexFst : Lex (ℝ × ℝ) →+ ℝ where
  toFun x := (ofLex x).1
  map_zero' := rfl
  map_add' _ _ := rfl

theorem monotone_lexFst : Monotone lexFst := Prod.Lex.monotone_fst_ofLex

/-- `tate:ex:extension`, first claim: over the rank-one base `k((t^ℝ))` every positive `α`
has `H_α = ℝ`. -/
theorem admissibleGroup_real_eq_top {α : ℝ} (hα : 0 < α) : admissibleGroup α = ⊤ := by
  rw [eq_top_iff]
  intro γ _
  obtain ⟨N, hN⟩ := Archimedean.arch |γ| hα
  exact ⟨N, (abs_le.mp hN).1, (abs_le.mp hN).2⟩

/-- `tate:ex:extension`, first claim: over `k((t^ℝ))`, for `v(q) > 0` every nonzero parameter
is admitted. -/
theorem mem_admissibleDomain_real {q u : k⟦ℝ⟧} (hq : 0 < q.order) (hu : u ≠ 0) :
    u ∈ admissibleDomain q :=
  ⟨hu, by rw [admissibleGroup_real_eq_top hq]; exact AddSubgroup.mem_top _⟩

/-- In the example, `q = t^1` over `ℝ` becomes `t^{(0,1)}`. -/
theorem workspaceEmbedding_secondSummand_single_one :
    workspaceEmbedding secondSummand strictMono_secondSummand (single (1 : ℝ) (1 : k)) =
      single (toLex ((0 : ℝ), (1 : ℝ))) 1 :=
  workspaceEmbedding_single _ _ _ _

/-- `tate:ex:extension`, second claim: over `k((t^{ℝ ⊕lex ℝ}))`, a parameter of valuation
`(1,0)` is not admitted for `q = t^{(0,1)}`. -/
theorem notMem_admissibleDomain_of_order_eq {u : k⟦Lex (ℝ × ℝ)⟧}
    (hu : u.order = toLex (1, 0)) :
    u ∉ admissibleDomain (single (toLex ((0 : ℝ), (1 : ℝ))) (1 : k)) := by
  rintro ⟨-, N, -, hN⟩
  rw [hu, order_single one_ne_zero] at hN
  have h := monotone_lexFst hN
  rw [map_nsmul] at h
  change (1 : ℝ) ≤ N • (0 : ℝ) at h
  rw [nsmul_zero] at h
  exact absurd h (not_le.mpr one_pos)

/-- `tate:ex:extension`, third claim: `1 + t^{(1,0)}` is admitted for `q = t^{(0,1)}`. -/
theorem one_add_single_mem_admissibleDomain :
    1 + single (toLex ((1 : ℝ), (0 : ℝ))) (1 : k) ∈
      admissibleDomain (single (toLex ((0 : ℝ), (1 : ℝ))) (1 : k)) := by
  have hpos : (0 : Lex (ℝ × ℝ)) < toLex (1, 0) :=
    Prod.Lex.toLex_lt_toLex.mpr (Or.inl one_pos)
  have hlt : (1 : k⟦Lex (ℝ × ℝ)⟧).orderTop <
      (single (toLex ((1 : ℝ), (0 : ℝ))) (1 : k)).orderTop := by
    rw [orderTop_one, orderTop_single one_ne_zero]
    exact WithTop.coe_lt_coe.mpr hpos
  have htop := orderTop_add_eq_left hlt
  rw [orderTop_one] at htop
  have hne : 1 + single (toLex ((1 : ℝ), (0 : ℝ))) (1 : k) ≠ 0 := by
    intro h0
    rw [h0, orderTop_zero] at htop
    exact WithTop.top_ne_coe htop
  refine ⟨hne, ?_⟩
  have hord : (1 + single (toLex ((1 : ℝ), (0 : ℝ))) (1 : k)).order = 0 := by
    apply WithTop.coe_injective
    rw [order_eq_orderTop_of_ne_zero hne, htop, WithTop.coe_zero]
  rw [hord]
  exact zero_mem _

/-- `tate:thm:extension`, last sentence, in the example: the admissible domain of
`q = t^{(0,1)}` in the larger field is not all of `K_{Γ'}^×`. -/
theorem admissibleDomain_ne_nonzero :
    admissibleDomain (single (toLex ((0 : ℝ), (1 : ℝ))) (1 : k)) ≠ {u | u ≠ 0} := by
  intro h
  have hmem : single (toLex ((1 : ℝ), (0 : ℝ))) (1 : k) ∈ {u : k⟦Lex (ℝ × ℝ)⟧ | u ≠ 0} :=
    single_ne_zero one_ne_zero
  rw [← h] at hmem
  exact notMem_admissibleDomain_of_order_eq (order_single one_ne_zero) hmem

end Example

/-! ### The extension obstruction (`tate:node:thm:obstruction`), abstractly -/

section Obstruction

variable {G V E : Type*} [Group G] [CommGroup V] [Group E]

/-- The properties of `Φ_q` used by the proofs of `tate:node:thm:obstruction` and
`tate:thm:tropical`, for a homomorphism `v : G → V` (the source's valuation `K^× → Γ`,
written multiplicatively), a subgroup `H ≤ V` (the source's `H_α`) and `U = v⁻¹(H)`:
`q ∈ U`, `Φ : U → E` is a surjective homomorphism, and its kernel is `q^ℤ`. Additive groups
such as `E_q(K)` enter through `Multiplicative`. -/
structure IsPeriodUniformization (v : G →* V) (H : Subgroup V) (q : G)
    (Φ : H.comap v →* E) : Prop where
  mem : q ∈ H.comap v
  surjective : Function.Surjective Φ
  map_eq_one_iff : ∀ u : H.comap v, Φ u = 1 ↔ (u : G) ∈ Subgroup.zpowers q

variable {v : G →* V} {H : Subgroup V} {q : G} {Φ : H.comap v →* E}

/-- The map `ker Ψ → V/H`, `x ↦ v(x) mod H`, of `tate:node:eq:kernel-extra`. -/
def kerValue (v : G →* V) (H : Subgroup V) (Ψ : G →* E) : Ψ.ker →* V ⧸ H :=
  (QuotientGroup.mk' H).comp (v.comp Ψ.ker.subtype)

theorem kerValue_apply (Ψ : G →* E) (x : Ψ.ker) :
    kerValue v H Ψ x = QuotientGroup.mk (v x) :=
  rfl

namespace IsPeriodUniformization

variable (hΦ : IsPeriodUniformization v H q Φ) {Ψ : G →* E}
  (hΨ : ∀ u : H.comap v, Ψ u = Φ u)
include hΦ hΨ

/-- An extension of `Φ` kills the period. -/
theorem period_mem_ker : q ∈ Ψ.ker := by
  rw [MonoidHom.mem_ker, show q = ((⟨q, hΦ.mem⟩ : H.comap v) : G) from rfl, hΨ,
    hΦ.map_eq_one_iff]
  exact Subgroup.mem_zpowers q

/-- `tate:node:thm:obstruction`: `ker Ψ ∩ U_q = ker Φ_q = q^ℤ`. -/
theorem ker_inf_comap : Ψ.ker ⊓ H.comap v = Subgroup.zpowers q := by
  refine le_antisymm (fun x hx => ?_) ?_
  · obtain ⟨hx, hxU⟩ := Subgroup.mem_inf.mp hx
    rw [← hΦ.map_eq_one_iff ⟨x, hxU⟩, ← hΨ]
    exact hx
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_inf.mpr ⟨hΦ.period_mem_ker hΨ, hΦ.mem⟩

/-- `tate:node:thm:obstruction`, exactness of `tate:node:eq:kernel-extra` at `ker Ψ`: the
kernel of `ker Ψ → V/H` is `q^ℤ`. -/
theorem ker_kerValue : (kerValue v H Ψ).ker = (Subgroup.zpowers q).subgroupOf Ψ.ker := by
  ext x
  rw [MonoidHom.mem_ker, kerValue_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
    ← hΦ.ker_inf_comap hΨ, Subgroup.mem_inf]
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

/-- `tate:node:thm:obstruction`, surjectivity in `tate:node:eq:kernel-extra`: given `a`,
choose `d ∈ U` with `Φ(d) = Ψ(a)`; then `a d⁻¹ ∈ ker Ψ` has the valuation of `a` modulo
`H`. -/
theorem kerValue_surjective (hv : Function.Surjective v) :
    Function.Surjective (kerValue v H Ψ) := by
  intro y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨a, rfl⟩ := hv y
  obtain ⟨d, hd⟩ := hΦ.surjective (Ψ a)
  refine ⟨⟨a * (d : G)⁻¹, ?_⟩, ?_⟩
  · rw [MonoidHom.mem_ker, map_mul, map_inv, hΨ, hd, mul_inv_cancel]
  · rw [kerValue_apply, QuotientGroup.eq]
    show (v (a * (d : G)⁻¹))⁻¹ * v a ∈ H
    rw [map_mul, map_inv, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
    exact d.2

/-- `tate:node:thm:obstruction`: an extension `Ψ` of `Φ` has kernel exactly `q^ℤ` if and
only if `H = V` (in the source, `H_α = Γ`). -/
theorem ker_eq_zpowers_iff (hv : Function.Surjective v) :
    Ψ.ker = Subgroup.zpowers q ↔ H = ⊤ := by
  constructor
  · intro h
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, hx⟩ := hΦ.kerValue_surjective hΨ hv (y : V ⧸ H)
    have hxq : (x : G) ∈ Subgroup.zpowers q := h ▸ x.2
    have hxU : v x ∈ H := (Subgroup.zpowers_le.mpr hΦ.mem) hxq
    rw [kerValue_apply, QuotientGroup.eq] at hx
    simpa using H.mul_mem hxU hx
  · intro h
    rw [← hΦ.ker_inf_comap hΨ, h, Subgroup.comap_top, inf_top_eq]

end IsPeriodUniformization

/-- `tate:node:thm:obstruction`: if `H ≠ V` (`H_α ≠ Γ`), no homomorphism `Ψ : G → E`
extends `Φ` and has kernel `q^ℤ`. -/
theorem IsPeriodUniformization.not_exists_extension (hΦ : IsPeriodUniformization v H q Φ)
    (hv : Function.Surjective v) (hH : H ≠ ⊤) :
    ¬∃ Ψ : G →* E, (∀ u : H.comap v, Ψ u = Φ u) ∧ Ψ.ker = Subgroup.zpowers q := by
  rintro ⟨Ψ, hΨ, hker⟩
  exact hH ((hΦ.ker_eq_zpowers_iff hΨ hv).mp hker)

end Obstruction

/-! ### The valuation quotient (`tate:thm:tropical`), abstractly -/

section Tropical

variable {G V E : Type*} [Group G] [CommGroup V] [Group E] {v : G →* V}
  {H : Subgroup V} {q : G} {Φ : H.comap v →* E}

/-- `v` restricted to `U = v⁻¹(H)`, with values in `H`. -/
def restrictValuation (v : G →* V) (H : Subgroup V) : H.comap v →* H :=
  (v.comp (H.comap v).subtype).codRestrict H fun u => u.2

/-- `U → H/v(q)^ℤ`, `u ↦ v(u) mod v(q)^ℤ`; in the source, `u ↦ v(u) + ℤα ∈ H_α/ℤα`. -/
def valueClass (v : G →* V) (H : Subgroup V) (q : G) :
    H.comap v →* H ⧸ (Subgroup.zpowers (v q)).subgroupOf H :=
  (QuotientGroup.mk' _).comp (restrictValuation v H)

theorem valueClass_eq_one_iff (u : H.comap v) :
    valueClass v H q u = 1 ↔ v u ∈ Subgroup.zpowers (v q) := by
  rw [valueClass, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf]
  rfl

theorem IsPeriodUniformization.ker_le_ker_valueClass (hΦ : IsPeriodUniformization v H q Φ) :
    Φ.ker ≤ (valueClass v H q).ker := by
  intro u hu
  rw [MonoidHom.mem_ker, valueClass_eq_one_iff]
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp ((hΦ.map_eq_one_iff u).mp hu)
  exact Subgroup.mem_zpowers_iff.mpr ⟨n, by rw [← map_zpow, hn]⟩

/-- `tate:thm:tropical`: the valuation quotient `trop_q : E → H/v(q)^ℤ` (in the source
`E_q(K) → H_α/ℤα`), characterized by `trop_q(Φ(u)) = v(u) mod v(q)^ℤ` (`trop_apply`). -/
def trop (hΦ : IsPeriodUniformization v H q Φ) :
    E →* H ⧸ (Subgroup.zpowers (v q)).subgroupOf H :=
  Φ.liftOfSurjective hΦ.surjective ⟨valueClass v H q, hΦ.ker_le_ker_valueClass⟩

/-- `tate:eq:tropical`: `trop_q(Φ_q(u)) = v(u) + ℤα`. -/
theorem trop_apply (hΦ : IsPeriodUniformization v H q Φ) (u : H.comap v) :
    trop hΦ (Φ u) = valueClass v H q u :=
  Φ.liftOfRightInverse_comp_apply _ _ _ u

/-- `tate:thm:tropical`: `trop_q` is surjective (every `γ ∈ H_α` is a value). -/
theorem trop_surjective (hΦ : IsPeriodUniformization v H q Φ) (hv : Function.Surjective v) :
    Function.Surjective (trop hΦ) := by
  intro y
  obtain ⟨⟨h, hh⟩, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨g, rfl⟩ := hv h
  exact ⟨Φ ⟨g, hh⟩, trop_apply hΦ _⟩

theorem ker_le_comap (v : G →* V) (H : Subgroup V) : v.ker ≤ H.comap v := fun x hx => by
  rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
  exact H.one_mem

/-- The first map `O_v^× → E` of `tate:eq:tropical-seq`: `Φ` restricted to `ker v`. -/
def unitsMap (Φ : H.comap v →* E) : v.ker →* E :=
  Φ.comp (Subgroup.inclusion (ker_le_comap v H))

/-- `tate:thm:tropical`, exactness at `O_v^×`: `Φ` is injective on `ker v`, because a
nontrivial power of `q` is not a unit (the hypothesis says that `v(q)` has infinite order,
which holds for `v(q) = α > 0` in an ordered group). -/
theorem IsPeriodUniformization.unitsMap_injective (hΦ : IsPeriodUniformization v H q Φ)
    (hq : ∀ n : ℤ, v q ^ n = 1 → n = 0) : Function.Injective (unitsMap Φ) := by
  rw [injective_iff_map_eq_one]
  intro u hu
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp ((hΦ.map_eq_one_iff _).mp hu)
  rw [Subgroup.coe_inclusion] at hn
  have h1 : v q ^ n = 1 := by rw [← map_zpow, hn]; exact MonoidHom.mem_ker.mp u.2
  rw [hq n h1, zpow_zero] at hn
  exact Subtype.ext hn.symm

/-- `tate:thm:tropical`, exactness at `E`: `ker trop_q = Φ(O_v^×)`. -/
theorem IsPeriodUniformization.ker_trop (hΦ : IsPeriodUniformization v H q Φ) :
    (trop hΦ).ker = (unitsMap Φ).range := by
  ext P
  rw [MonoidHom.mem_ker, MonoidHom.mem_range]
  constructor
  · intro h
    obtain ⟨d, rfl⟩ := hΦ.surjective P
    rw [trop_apply, valueClass_eq_one_iff] at h
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h
    have hq1 : Φ ⟨q, hΦ.mem⟩ = 1 := (hΦ.map_eq_one_iff _).mpr (Subgroup.mem_zpowers q)
    have hx : (d : G) * q ^ (-m) ∈ v.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_zpow, ← hm, zpow_neg, mul_inv_cancel]
    refine ⟨⟨_, hx⟩, ?_⟩
    have hel : Subgroup.inclusion (ker_le_comap v H) ⟨_, hx⟩ = d * ⟨q, hΦ.mem⟩ ^ (-m) :=
      Subtype.ext (by simp)
    rw [unitsMap, MonoidHom.comp_apply, hel, map_mul, map_zpow, hq1, one_zpow, mul_one]
  · rintro ⟨u, rfl⟩
    rw [unitsMap, MonoidHom.comp_apply, trop_apply, valueClass_eq_one_iff,
      Subgroup.coe_inclusion, MonoidHom.mem_ker.mp u.2]
    exact Subgroup.one_mem _

/-- The restriction of a homomorphism `ρ : G → R` to `ker v` (in the source, to the units
`O_v^×` of the valuation ring). -/
def restrictKer (v : G →* V) {R : Type*} [Group R] (ρ : G →* R) : v.ker →* R :=
  ρ.comp v.ker.subtype

/-- `tate:node:prop:residue`, abstractly: when `Φ` is injective on `O_v^× = ker v`, the map
`res ∘ Φ⁻¹ : E^v_0 = Φ(O_v^×) → R` for a homomorphism `r : O_v^× → R` (in the source the
residue map onto `k^×`). -/
def residueMap (hinj : Function.Injective (unitsMap Φ)) {R : Type*} [Group R]
    (r : v.ker →* R) : (unitsMap Φ).range →* R :=
  r.comp (MonoidHom.ofInjective hinj).symm.toMonoidHom

theorem residueMap_apply (hinj : Function.Injective (unitsMap Φ)) {R : Type*} [Group R]
    (r : v.ker →* R) {P : E} (hP : P ∈ (unitsMap Φ).range) {u : v.ker}
    (hu : unitsMap Φ u = P) : residueMap hinj r ⟨P, hP⟩ = r u := by
  rw [residueMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  congr 1
  rw [MulEquiv.symm_apply_eq]
  exact Subtype.ext (hu.symm.trans (MonoidHom.ofInjective_apply hinj).symm)

/-- `tate:node:prop:residue`, exactness of `tate:node:eq:residueexact` at the residue group:
`res ∘ Φ⁻¹` is onto when the residue is. -/
theorem residueMap_surjective (hinj : Function.Injective (unitsMap Φ)) {R : Type*} [Group R]
    {r : v.ker →* R} (hr : Function.Surjective r) :
    Function.Surjective (residueMap hinj r) := by
  intro c
  obtain ⟨u, rfl⟩ := hr c
  exact ⟨_, residueMap_apply hinj r (MonoidHom.mem_range.mpr ⟨u, rfl⟩) rfl⟩

/-- `tate:node:prop:residue`: the layer `E^v_1 = Φ(ker r)`. -/
def fineLayer (Φ : H.comap v →* E) {R : Type*} [Group R] (r : v.ker →* R) : Subgroup E :=
  r.ker.map (unitsMap Φ)

/-- `tate:node:prop:residue`, exactness of `tate:node:eq:residueexact` at `E^v_0`: the kernel
of `res ∘ Φ⁻¹` is `E^v_1 = Φ(ker r)`. -/
theorem ker_residueMap (hinj : Function.Injective (unitsMap Φ)) {R : Type*} [Group R]
    (r : v.ker →* R) :
    (residueMap hinj r).ker = (fineLayer Φ r).subgroupOf (unitsMap Φ).range := by
  ext ⟨P, hP⟩
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hP
  rw [MonoidHom.mem_ker, residueMap_apply hinj r _ hu, Subgroup.mem_subgroupOf, fineLayer,
    Subgroup.mem_map]
  constructor
  · intro h
    exact ⟨u, h, hu⟩
  · rintro ⟨w, hw, hwu⟩
    rw [← hinj (hwu.trans hu.symm)]
    exact hw

/-- `tate:node:prop:residue`: `E^v_1 = Φ(ker r) ≅ ker r` (in the source, `(1 + 𝔪_v, ·)`). -/
def fineLayerEquiv (hinj : Function.Injective (unitsMap Φ)) {R : Type*} [Group R]
    (r : v.ker →* R) : r.ker ≃* fineLayer Φ r :=
  r.ker.equivMapOfInjective _ hinj

end Tropical

/-! ### The Hahn instance -/

section HahnInstance

variable {Γ k : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field k]

/-- The valuation `v : K^× → Γ` of `K = k⟦Γ⟧`, as a homomorphism to `Multiplicative Γ`. -/
def unitsValuation : (k⟦Γ⟧)ˣ →* Multiplicative Γ where
  toFun u := Multiplicative.ofAdd (u : k⟦Γ⟧).order
  map_one' := by rw [Units.val_one, order_one, ofAdd_zero]
  map_mul' a b := by rw [Units.val_mul, order_mul a.ne_zero b.ne_zero, ofAdd_add]

theorem unitsValuation_apply (u : (k⟦Γ⟧)ˣ) :
    unitsValuation u = Multiplicative.ofAdd (u : k⟦Γ⟧).order :=
  rfl

/-- `v` is onto: `v(t^γ) = γ`. -/
theorem unitsValuation_surjective :
    Function.Surjective (unitsValuation : (k⟦Γ⟧)ˣ →* Multiplicative Γ) := fun y =>
  ⟨Units.mk0 (single (Multiplicative.toAdd y) (1 : k)) (single_ne_zero one_ne_zero), by
    rw [unitsValuation_apply, Units.val_mk0, order_single one_ne_zero, ofAdd_toAdd]⟩

/-- `tate:eq:U`: `U_q = v⁻¹(H_α)` as a subgroup of `K^×`. -/
abbrev admissibleUnits (q : k⟦Γ⟧) : Subgroup (k⟦Γ⟧)ˣ :=
  (AddSubgroup.toSubgroup (admissibleGroup q.order)).comap unitsValuation

theorem mem_admissibleUnits {q : k⟦Γ⟧} {u : (k⟦Γ⟧)ˣ} :
    u ∈ admissibleUnits q ↔ (u : k⟦Γ⟧) ∈ admissibleDomain q :=
  ⟨fun h => ⟨u.ne_zero, h⟩, fun h => h.2⟩

theorem self_mem_admissibleUnits {q : (k⟦Γ⟧)ˣ} (hq : 0 ≤ (q : k⟦Γ⟧).order) :
    q ∈ admissibleUnits (q : k⟦Γ⟧) :=
  self_mem_admissibleGroup hq

/-- For `v(q) > 0`, no nontrivial power of `q` is a unit of the valuation ring. -/
theorem unitsValuation_zpow_eq_one {q : (k⟦Γ⟧)ˣ} (hq : 0 < (q : k⟦Γ⟧).order) (n : ℤ)
    (h : unitsValuation q ^ n = 1) : n = 0 := by
  rw [unitsValuation_apply, ← ofAdd_zsmul, ofAdd_eq_one] at h
  exact (IsAddTorsionFree.zsmul_eq_zero_iff_left hq.ne').mp h

/-- `tate:node:thm:obstruction` over `𝕂 = k⟦Γ⟧`, for any `Φ : U_q → E` with the properties of
`Φ_q` (surjective homomorphism with kernel `q^ℤ`; `Φ_q` itself is not formalized): an
extension `Ψ : 𝕂^× → E` of `Φ` has kernel `q^ℤ` exactly when `H_α = Γ`. -/
theorem hahn_ker_eq_zpowers_iff {E : Type*} [Group E] {q : (k⟦Γ⟧)ˣ}
    {Φ : _ →* E}
    (hΦ : IsPeriodUniformization unitsValuation
      (AddSubgroup.toSubgroup (admissibleGroup (q : k⟦Γ⟧).order)) q Φ)
    {Ψ : (k⟦Γ⟧)ˣ →* E} (hΨ : ∀ u : admissibleUnits (q : k⟦Γ⟧), Ψ u = Φ u) :
    Ψ.ker = Subgroup.zpowers q ↔ admissibleGroup (q : k⟦Γ⟧).order = ⊤ := by
  rw [hΦ.ker_eq_zpowers_iff hΨ unitsValuation_surjective, map_eq_top_iff]

/-- `tate:node:thm:obstruction` over `𝕂 = k⟦Γ⟧`: if `H_α ≠ Γ`, no homomorphism
`Ψ : 𝕂^× → E` extends `Φ` and has kernel `q^ℤ`. -/
theorem hahn_not_exists_extension {E : Type*} [Group E] {q : (k⟦Γ⟧)ˣ}
    {Φ : _ →* E}
    (hΦ : IsPeriodUniformization unitsValuation
      (AddSubgroup.toSubgroup (admissibleGroup (q : k⟦Γ⟧).order)) q Φ)
    (hH : admissibleGroup (q : k⟦Γ⟧).order ≠ ⊤) :
    ¬∃ Ψ : (k⟦Γ⟧)ˣ →* E, (∀ u : admissibleUnits (q : k⟦Γ⟧), Ψ u = Φ u) ∧
      Ψ.ker = Subgroup.zpowers q :=
  hΦ.not_exists_extension unitsValuation_surjective (by rwa [ne_eq, map_eq_top_iff])

/-- `tate:thm:tropical` over `K = k⟦Γ⟧`, exactness at `O_v^×`: for `v(q) > 0`, `Φ` is
injective on the valuation-zero units. -/
theorem hahn_unitsMap_injective {E : Type*} [Group E] {q : (k⟦Γ⟧)ˣ}
    (hq : 0 < (q : k⟦Γ⟧).order) {Φ : _ →* E}
    (hΦ : IsPeriodUniformization unitsValuation
      (AddSubgroup.toSubgroup (admissibleGroup (q : k⟦Γ⟧).order)) q Φ) :
    Function.Injective (unitsMap Φ) :=
  hΦ.unitsMap_injective (unitsValuation_zpow_eq_one hq)

/-- `tate:thm:tropical` over `K = k⟦Γ⟧`: `trop_q : E → H_α/α^ℤ` (written multiplicatively) is
onto, since every `γ ∈ H_α` is the valuation of `t^γ`. -/
theorem hahn_trop_surjective {E : Type*} [Group E] {q : (k⟦Γ⟧)ˣ} {Φ : _ →* E}
    (hΦ : IsPeriodUniformization unitsValuation
      (AddSubgroup.toSubgroup (admissibleGroup (q : k⟦Γ⟧).order)) q Φ) :
    Function.Surjective (trop hΦ) :=
  trop_surjective hΦ unitsValuation_surjective

/-- `tate:thm:tropical` over `K = k⟦Γ⟧`, exactness of `tate:eq:tropical-seq` at `E`:
`ker trop_q = Φ(O_v^×)`. -/
theorem hahn_ker_trop {E : Type*} [Group E] {q : (k⟦Γ⟧)ˣ} {Φ : _ →* E}
    (hΦ : IsPeriodUniformization unitsValuation
      (AddSubgroup.toSubgroup (admissibleGroup (q : k⟦Γ⟧).order)) q Φ) :
    (trop hΦ).ker = (unitsMap Φ).range :=
  hΦ.ker_trop

/-- `tate:node:thm:obstruction` over `𝕂 = k⟦Γ⟧`, surjectivity in
`tate:node:eq:kernel-extra`: `ker Ψ → Γ/H_α` (written multiplicatively) is onto. -/
theorem hahn_kerValue_surjective {E : Type*} [Group E] {q : (k⟦Γ⟧)ˣ} {Φ : _ →* E}
    (hΦ : IsPeriodUniformization unitsValuation
      (AddSubgroup.toSubgroup (admissibleGroup (q : k⟦Γ⟧).order)) q Φ)
    {Ψ : (k⟦Γ⟧)ˣ →* E} (hΨ : ∀ u : admissibleUnits (q : k⟦Γ⟧), Ψ u = Φ u) :
    Function.Surjective
      (kerValue unitsValuation (AddSubgroup.toSubgroup (admissibleGroup (q : k⟦Γ⟧).order)) Ψ) :=
  hΦ.kerValue_surjective hΨ unitsValuation_surjective

/-- The leading coefficient `K^× → k^×`, a homomorphism. -/
def unitsLeadingCoeff : (k⟦Γ⟧)ˣ →* kˣ where
  toFun u := Units.mk0 (u : k⟦Γ⟧).leadingCoeff (leadingCoeff_ne_zero.mpr u.ne_zero)
  map_one' := Units.ext (by rw [Units.val_mk0, Units.val_one, Units.val_one, leadingCoeff_one])
  map_mul' a b := Units.ext (by
    rw [Units.val_mk0, Units.val_mul, Units.val_mul, Units.val_mk0, Units.val_mk0,
      leadingCoeff_mul])

/-- The residue `O_v^× → k^×` of `tate:node:prop:residue`, a homomorphism
`ker unitsValuation →* kˣ`: on valuation-zero units the leading coefficient is the constant
coefficient. -/
def hahnResidue :=
  restrictKer (unitsValuation (Γ := Γ) (k := k)) unitsLeadingCoeff

theorem order_eq_zero_of_unitsValuation_eq_one {u : (k⟦Γ⟧)ˣ} (hu : unitsValuation u = 1) :
    (u : k⟦Γ⟧).order = 0 := by
  rw [unitsValuation_apply, ofAdd_eq_one] at hu
  exact hu

/-- `tate:node:prop:residue`: the residue on `O_v^×` is onto `k^×`. -/
theorem hahnResidue_surjective : Function.Surjective (hahnResidue (Γ := Γ) (k := k)) := by
  intro c
  have hc : single (0 : Γ) (c : k) ≠ 0 := single_ne_zero c.ne_zero
  have hmem : unitsValuation (Units.mk0 _ hc) = 1 := by
    rw [unitsValuation_apply, Units.val_mk0, order_single c.ne_zero, ofAdd_zero]
  refine ⟨⟨_, MonoidHom.mem_ker.mpr hmem⟩, Units.ext ?_⟩
  change (single (0 : Γ) (c : k)).leadingCoeff = c
  rw [leadingCoeff_eq, order_single c.ne_zero, coeff_single_same]

/-- `tate:node:prop:residue`: the kernel of the residue on `O_v^×` is `1 + 𝔪_v`. -/
theorem mem_ker_hahnResidue_iff (u) :
    u ∈ (hahnResidue (Γ := Γ) (k := k)).ker ↔
      0 < (((u : (k⟦Γ⟧)ˣ) : k⟦Γ⟧) - 1).orderTop := by
  have h0 := order_eq_zero_of_unitsValuation_eq_one (MonoidHom.mem_ker.mp u.2)
  set x : k⟦Γ⟧ := ((u : (k⟦Γ⟧)ˣ) : k⟦Γ⟧) with hx
  have hres : u ∈ (hahnResidue (Γ := Γ) (k := k)).ker ↔ x.coeff 0 = 1 := by
    rw [MonoidHom.mem_ker, Units.ext_iff]
    change x.leadingCoeff = 1 ↔ _
    rw [leadingCoeff_eq, h0]
  rw [hres]
  constructor
  · intro h1
    refine Surreal.HahnSeries.orderTop_pos_of_support_pos fun g hg => ?_
    by_contra hle
    rw [not_lt] at hle
    apply (mem_support _ _).mp hg
    rw [coeff_sub, coeff_one]
    rcases hle.lt_or_eq with hlt | rfl
    · rw [if_neg hlt.ne, coeff_eq_zero_of_lt_order (by rw [h0]; exact hlt), sub_zero]
    · rw [if_pos rfl, h1, sub_self]
  · intro hpos
    have h := coeff_eq_zero_of_lt_orderTop hpos
    rw [coeff_sub, coeff_one, if_pos rfl, sub_eq_zero] at h
    exact h

/-- `tate:node:prop:residue` over `K = k⟦Γ⟧`: for `v(q) > 0` and `Φ` with the properties of
`Φ_q`, the sequence `0 → E^v_1 → E^v_0 → k^× → 0` of `tate:node:eq:residueexact` is exact:
`res ∘ Φ⁻¹ : E^v_0 → k^×` is onto and its kernel is `E^v_1` (the first map is the inclusion).
Here `E^v_0 = Φ(O_v^×)`, `E^v_1 = Φ(ker res)` and `ker res = 1 + 𝔪_v`
(`mem_ker_hahnResidue_iff`); the isomorphism `E^v_1 ≅ ker res` is `fineLayerEquiv`. -/
theorem hahn_residue_exact {E : Type*} [Group E] {q : (k⟦Γ⟧)ˣ}
    (hq : 0 < (q : k⟦Γ⟧).order) {Φ : _ →* E}
    (hΦ : IsPeriodUniformization unitsValuation
      (AddSubgroup.toSubgroup (admissibleGroup (q : k⟦Γ⟧).order)) q Φ) :
    Function.Surjective (residueMap (hahn_unitsMap_injective hq hΦ) hahnResidue) ∧
      (residueMap (hahn_unitsMap_injective hq hΦ) hahnResidue).ker =
        (fineLayer Φ hahnResidue).subgroupOf (unitsMap Φ).range :=
  ⟨residueMap_surjective _ hahnResidue_surjective, ker_residueMap _ _⟩

end HahnInstance

/-! ### Representatives and the circle layers (`tate:thm:tropical`, `tate:eq:circlelayers`) -/

section CircleLayers

section Generic

variable {A : Type*} [AddCommGroup A] (B : AddSubgroup A) (a : A)

/-- The first map `B → A/ℤa` of `tate:eq:circlelayers`. -/
def layerIncl : B →+ A ⧸ AddSubgroup.zmultiples a :=
  (QuotientAddGroup.mk' _).comp B.subtype

/-- The second map `A/ℤa → (A/B)/ℤā` of `tate:eq:circlelayers`. -/
def layerProj :
    A ⧸ AddSubgroup.zmultiples a →+ (A ⧸ B) ⧸ AddSubgroup.zmultiples (a : A ⧸ B) :=
  QuotientAddGroup.map _ _ (QuotientAddGroup.mk' B) fun x hx => by
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    rw [AddSubgroup.mem_comap, QuotientAddGroup.mk'_apply, QuotientAddGroup.mk_zsmul]
    exact AddSubgroup.zsmul_mem_zmultiples _ n

theorem layerIncl_injective (h : B ⊓ AddSubgroup.zmultiples a = ⊥) :
    Function.Injective (layerIncl B a) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  rw [layerIncl, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.eq_zero_iff] at hx
  have hmem : (x : A) ∈ B ⊓ AddSubgroup.zmultiples a := AddSubgroup.mem_inf.mpr ⟨x.2, hx⟩
  rw [h, AddSubgroup.mem_bot] at hmem
  exact Subtype.ext hmem

theorem layerProj_surjective : Function.Surjective (layerProj B a) := by
  intro y
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective y
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  exact ⟨(x : A ⧸ AddSubgroup.zmultiples a), rfl⟩

theorem range_layerIncl : (layerIncl B a).range = (layerProj B a).ker := by
  ext y
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  rw [AddMonoidHom.mem_range, AddMonoidHom.mem_ker, layerProj, QuotientAddGroup.map_mk,
    QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨b, hb⟩
    rw [layerIncl, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq,
      AddSubgroup.mem_zmultiples_iff] at hb
    obtain ⟨n, hn⟩ := hb
    refine ⟨n, ?_⟩
    rw [← QuotientAddGroup.mk_zsmul, hn, QuotientAddGroup.mk_add,
      (QuotientAddGroup.eq_zero_iff (-B.subtype b)).mpr (neg_mem b.2), zero_add]
  · rintro ⟨n, hn⟩
    rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq] at hn
    refine ⟨⟨_, hn⟩, ?_⟩
    rw [layerIncl, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq]
    show -(-(n • a) + x) + x ∈ _
    rw [neg_add, neg_neg, add_assoc, neg_add_cancel, add_zero]
    exact AddSubgroup.zsmul_mem_zmultiples a n

end Generic

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

open Surreal.ValuedIteration

/-- The period `α` as an element of `H_α`. -/
def periodIn {α : Γ} (hα : 0 < α) : admissibleGroup α :=
  ⟨α, self_mem_admissibleGroup hα.le⟩

/-- `tate:eq:Hminus`: `H_α^- = {γ ∈ H_α : n|γ| < α for all n ≥ 1}` is the subgroup
`coarseSubgroup hα` of `Γ` (which lies in `H_α`), viewed inside `H_α`. -/
def minusLayer {α : Γ} (hα : 0 < α) : AddSubgroup (admissibleGroup α) :=
  (coarseSubgroup hα).addSubgroupOf (admissibleGroup α)

/-- `tate:eq:Hminus`: `H_α^- ⊆ H_α`. -/
theorem coarseSubgroup_le_admissibleGroup {α : Γ} (hα : 0 < α) :
    coarseSubgroup hα ≤ admissibleGroup α := fun γ hγ => by
  have h1 := (mem_coarseSubgroup hα).mp hγ 1 one_pos
  rw [one_nsmul] at h1
  exact ⟨1, by rw [one_nsmul]; exact (abs_lt.mp h1).1.le,
    by rw [one_nsmul]; exact (abs_lt.mp h1).2.le⟩

/-- `H_α^- ∩ ℤα = 0`. -/
theorem minusLayer_inf_zmultiples {α : Γ} (hα : 0 < α) :
    minusLayer hα ⊓ AddSubgroup.zmultiples (periodIn hα) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx2⟩ := AddSubgroup.mem_inf.mp hx
  obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx2
  rw [AddSubgroup.mem_bot]
  by_cases hm : m = 0
  · rw [hm, zero_zsmul]
  exfalso
  have h1 := (mem_coarseSubgroup hα).mp (AddSubgroup.mem_addSubgroupOf.mp hx1) 1 one_pos
  change 1 • |m • α| < α at h1
  rw [one_nsmul, abs_zsmul, abs_of_pos hα] at h1
  have h2 : (1 : ℤ) • α ≤ |m| • α := zsmul_le_zsmul_left hα.le (Int.one_le_abs hm)
  rw [one_zsmul] at h2
  exact absurd (h2.trans_lt h1) (lt_irrefl α)

/-- `tate:eq:Hminus`, maximality: `H_α^-` is the largest proper convex subgroup of `H_α`, for
the order of `H_α` induced from `Γ`. -/
theorem isGreatest_minusLayer {α : Γ} (hα : 0 < α) :
    IsGreatest {G : AddSubgroup (admissibleGroup α) |
      (G : Set (admissibleGroup α)).OrdConnected ∧ G ≠ ⊤} (minusLayer hα) := by
  have key : ∀ y : admissibleGroup α, y ∈ minusLayer hα ↔ (y : Γ) ∈ coarseSubgroup hα :=
    fun _ => AddSubgroup.mem_addSubgroupOf
  refine ⟨⟨⟨fun a ha b hb x hx => ?_⟩, fun h => ?_⟩, fun G hG => ?_⟩
  · rw [SetLike.mem_coe, key] at ha hb ⊢
    exact (ordConnected_coarseSubgroup hα).out ha hb ⟨hx.1, hx.2⟩
  · have hmem : periodIn hα ∈ minusLayer hα := by
      rw [h]
      exact AddSubgroup.mem_top _
    exact notMem_coarseSubgroup hα ((key _).mp hmem)
  · obtain ⟨hconv, hne⟩ := hG
    intro x hx
    refine (key x).mpr ((mem_coarseSubgroup hα).mpr fun n _ => ?_)
    by_contra hlt
    rw [not_lt] at hlt
    obtain ⟨y, hyG, hy⟩ : ∃ y ∈ G, (y : Γ) = |(x : Γ)| := by
      rcases abs_choice (x : Γ) with h | h
      · exact ⟨x, hx, h.symm⟩
      · exact ⟨-x, neg_mem hx, by rw [h]; rfl⟩
    have hle : periodIn hα ≤ n • y := by
      rw [← Subtype.coe_le_coe, AddSubgroup.coe_nsmul, hy]
      exact hlt
    have hper : periodIn hα ∈ G := hconv.out G.zero_mem (nsmul_mem hyG n) ⟨hα.le, hle⟩
    apply hne
    rw [AddSubgroup.eq_top_iff']
    intro z
    obtain ⟨N, hN1, hN2⟩ := (mem_admissibleGroup (α := α)).mp z.2
    have hNG : N • periodIn hα ∈ G := nsmul_mem hper N
    exact hconv.out (neg_mem hNG) hNG ⟨hN1, hN2⟩

/-- `tate:eq:circlelayers`: the sequence
`0 → H_α^- → H_α/ℤα → (H_α/H_α^-)/ℤᾱ → 0` is exact. -/
theorem circleLayers_exact {α : Γ} (hα : 0 < α) :
    Function.Injective (layerIncl (minusLayer hα) (periodIn hα)) ∧
      (layerIncl (minusLayer hα) (periodIn hα)).range =
        (layerProj (minusLayer hα) (periodIn hα)).ker ∧
      Function.Surjective (layerProj (minusLayer hα) (periodIn hα)) :=
  ⟨layerIncl_injective _ _ (minusLayer_inf_zmultiples hα), range_layerIncl _ _,
    layerProj_surjective _ _⟩

/-- `tate:thm:tropical`: every class of `H_α/ℤα` has a unique representative in `[0, α)`
(this is `tate:lem:normalize`). -/
theorem existsUnique_representative {α : Γ} (hα : 0 < α)
    (c : admissibleGroup α ⧸ AddSubgroup.zmultiples (periodIn hα)) :
    ∃! r : admissibleGroup α, 0 ≤ (r : Γ) ∧ (r : Γ) < α ∧
      (r : admissibleGroup α ⧸ AddSubgroup.zmultiples (periodIn hα)) = c := by
  obtain ⟨β, rfl⟩ := QuotientAddGroup.mk_surjective c
  obtain ⟨m, ⟨h0, h1⟩, huniq⟩ := (mem_admissibleGroup_iff_existsUnique hα).mp β.2
  refine ⟨β + m • periodIn hα, ⟨h0, h1, ?_⟩, ?_⟩
  · rw [QuotientAddGroup.eq]
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨-m, ?_⟩
    rw [neg_zsmul, neg_add, add_comm (-β), neg_add_cancel_right]
  · rintro r ⟨hr0, hr1, hr⟩
    rw [QuotientAddGroup.eq] at hr
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hr
    have hr' : r = β + (-n) • periodIn hα := by
      rw [neg_zsmul, hn]
      abel
    have hval : ((r : admissibleGroup α) : Γ) = (β : Γ) + (-n) • α := by
      rw [hr']
      rfl
    rw [hval] at hr0 hr1
    rw [hr', huniq (-n) ⟨hr0, hr1⟩]

/-- `tate:thm:tropical`, unique representatives for the multiplicative quotient
`H_α/α^ℤ ⊆ (Multiplicative Γ)/α^ℤ`, the codomain of `trop` at the Hahn instance: every class
has a unique representative `r ∈ H_α` with `0 ≤ r < α` (`tate:lem:normalize`). -/
theorem existsUnique_representative_mul {α : Γ} (hα : 0 < α)
    (c : AddSubgroup.toSubgroup (admissibleGroup α) ⧸
      (Subgroup.zpowers (Multiplicative.ofAdd α)).subgroupOf
        (AddSubgroup.toSubgroup (admissibleGroup α))) :
    ∃! r : AddSubgroup.toSubgroup (admissibleGroup α),
      0 ≤ Multiplicative.toAdd (r : Multiplicative Γ) ∧
        Multiplicative.toAdd (r : Multiplicative Γ) < α ∧ QuotientGroup.mk r = c := by
  obtain ⟨β, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨m, ⟨h0, h1⟩, huniq⟩ :=
    (mem_admissibleGroup_iff_existsUnique hα).mp ((Multiplicative.mem_toSubgroup _ _).mp β.2)
  obtain ⟨a, ha⟩ : ∃ a : AddSubgroup.toSubgroup (admissibleGroup α),
      (a : Multiplicative Γ) = Multiplicative.ofAdd α :=
    ⟨⟨_, (Multiplicative.mem_toSubgroup _ _).mpr (self_mem_admissibleGroup hα.le)⟩, rfl⟩
  have hcoe : Multiplicative.toAdd ((β * a ^ m : AddSubgroup.toSubgroup (admissibleGroup α)) :
      Multiplicative Γ) = Multiplicative.toAdd (β : Multiplicative Γ) + m • α := by
    rw [Subgroup.coe_mul, Subgroup.coe_zpow, ha, toAdd_mul, toAdd_zpow, toAdd_ofAdd]
  refine ⟨β * a ^ m, ⟨hcoe ▸ h0, hcoe ▸ h1, ?_⟩, ?_⟩
  · rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff]
    refine ⟨-m, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_zpow, ha, mul_inv_rev,
      mul_assoc, inv_mul_cancel, mul_one, zpow_neg]
  · rintro r ⟨hr0, hr1, hr⟩
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff] at hr
    obtain ⟨n, hn⟩ := hr
    have hr' : (r : Multiplicative Γ) = β * Multiplicative.ofAdd α ^ (-n) := by
      rw [zpow_neg, hn, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv,
        mul_inv_cancel_left]
    have hval : Multiplicative.toAdd (r : Multiplicative Γ) =
        Multiplicative.toAdd (β : Multiplicative Γ) + (-n) • α := by
      rw [hr', toAdd_mul, toAdd_zpow, toAdd_ofAdd]
    rw [hval] at hr0 hr1
    apply Subtype.ext
    rw [hr', huniq (-n) ⟨hr0, hr1⟩, Subgroup.coe_mul, Subgroup.coe_zpow, ha]

end CircleLayers

/-! ### Normalized values of `trop_q` at the Hahn instance -/

section HahnRepresentative

variable {Γ k : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field k]

/-- `tate:thm:tropical` over `K = k⟦Γ⟧`: for `α = v(q) > 0`, every value `trop_q(P)` has a
unique representative `r ∈ H_α` with `0 ≤ r < α` (`H_α` written multiplicatively). -/
theorem hahn_existsUnique_trop_representative {E : Type*} [Group E] {q : (k⟦Γ⟧)ˣ}
    (hq : 0 < (q : k⟦Γ⟧).order) {Φ : _ →* E}
    (hΦ : IsPeriodUniformization unitsValuation
      (AddSubgroup.toSubgroup (admissibleGroup (q : k⟦Γ⟧).order)) q Φ) (P : E) :
    ∃! r : AddSubgroup.toSubgroup (admissibleGroup (q : k⟦Γ⟧).order),
      0 ≤ Multiplicative.toAdd (r : Multiplicative Γ) ∧
        Multiplicative.toAdd (r : Multiplicative Γ) < (q : k⟦Γ⟧).order ∧
          QuotientGroup.mk r = trop hΦ P :=
  existsUnique_representative_mul hq (trop hΦ P)

end HahnRepresentative

end

end Surreal.TateExtension
