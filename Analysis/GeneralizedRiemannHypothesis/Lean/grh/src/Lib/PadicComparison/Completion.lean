import Lib.General.Algebra.CohomologyBaseChange

/-!
# Derived completeness, adic approximation of comparisons and completed base change

This file shows that comparison maps of cohomology are bijective, by reduction modulo a scalar and
successive approximation. `New.Variety.H N F n` is `Extⁿ(N, F)` in the category `AbFunctor C` of
functors `C ⥤ Ab`. `New.Variety.moduleCoeff Φ` is a module-valued functor `Φ` (`act a` is
multiplication by `a` on it, `push N q n` is the map on `Hⁿ` induced by `q`, and `a • x` on `Hⁿ` is
`push N (act a) n x`), read as such a functor of coefficients.

## Main definitions and results

* `New.Variety.IsDerivedComplete`: derived π-completeness, the bijectivity of `New.shiftDiff π` on
  sequences. It passes to powers `ι → X`, to retracts up to a power of π, to cohomology
  (`New.Variety.IsDerivedComplete.cohomology`) and, in finite rank, to base change
  (`New.Variety.IsDerivedComplete.baseChange`).
* `New.Variety.Comparison.IsBijective.of_mod`: a comparison of complete cohomology groups that is
  bijective modulo `a` is bijective.
* `New.Variety.IsCompletionBijective`, `New.Variety.moduleCompletionIso`: linear maps that are
  bijective on p-adic completions, and the p-adic completion of an algebra, as a module.
* `New.Variety.HasFlatBaseChange.isBijective_of_isReductionMod`: `Hⁿ(N, S ⊗ Θ) → Hⁿ(N, X)` is
  bijective if `S ⊗ Θ → X` is so modulo p. The cohomology of `N` must commute with flat base change.
  `W` must be a discrete valuation ring with uniformiser p, and `S` must be flat over `W`. The lemma
  also needs completeness and no p-torsion of `W`, `S` and every value of `Θ` and `X`, and finite
  rank of `Hⁿ(N, Θ)` for each n where the kernel of the map on `Hⁿ` is p-divisible.

Notions from other files:
* `New.shiftDiff`: The operator (x_j) ↦ (x_j − π x_{j+1}) on sequences in a module.
* `New.Variety.Comparison.IsBijective`: For a functor φ: C' → C, a map β: F∘φ → F' and α: N' → N∘φ,
  the map Ext^n(N, F) → Ext^n(N', F') is bijective for every n.
* `New.Variety.IsReductionMod`: The map f is surjective, and f(x) = 0 exactly when x is a multiple
  m·y of m.
* `New.Variety.HasFlatBaseChange`: a functor N to abelian groups has it if M ⊗_S Hⁿ(N, Φ) → Hⁿ(N, M
  ⊗_S Φ) is bijective for all n, all functors Φ to S-modules and all S-flat M.
* `New.Variety.Comparison.restrict`: The cohomological comparison datum along a functor φ: C' → C
  from an abelian-group-valued functor N to N∘φ, with identity coefficient map.

## Relation to the literature

Known result: Derived completeness for a principal ideal, covering Nakayama, finiteness and
completed base change. Only modules and Ext groups are treated, and completeness is defined as
bijectivity of x_n - a x_(n+1) on sequences. Base change is proved for modules of finite rank over a
discrete valuation ring, with bounded torsion shown by hand. Source: Stacks Project 091N, 091P,
0G1U, 09BA, 0CQY; B. Bhatt, Torsion completions are bounded, JPAA (2019); L. Positselski,
Contraadjusted modules, contramodules, and reduced cotorsion modules, arXiv 1605.03934.
-/

noncomputable section

section Completion

namespace New.Variety

open CoeffAction CategoryTheory Function Ideal TensorProduct Functor ModuleCat ULift H Finset Fact

variable {C C' : Type 1} [Category C] [Category C'] {S : Type} [CommRing S]
  {N G : AbFunctor C} {N' G' : AbFunctor C'} {φ : C' ⥤ C} {α : N' ⟶ φ ⋙ N} {Φ : C ⥤ ModuleCat S}
  {Φ' : C' ⥤ ModuleCat S} {β : φ ⋙ Φ ⟶ Φ'} {a : S} {q : moduleCoeff Φ ⟶ G} {p : ℕ}
  {B : Type _} [CommRing B] [Algebra S B] {W : Type _} [CommRing W] {π : W}
  {X E Y F : Type*} [Algebra W S] [AddCommGroup X] [Module W X] [AddCommGroup E] [Module W E]
  [AddCommGroup Y]

/-! ### Derived completeness -/

variable (π X) in
/-- `X` is derived π-complete: the map `(x j) ↦ (x j - π • x (j + 1))` on sequences in `X` is
bijective. -/
abbrev IsDerivedComplete : Prop := Bijective (shiftDiff X π)

/-- A π-adically complete module is derived π-complete. -/
lemma IsDerivedComplete.of_isAdicComplete (h_complete : IsAdicComplete (span {π}) X) :
    IsDerivedComplete π X :=
  ⟨out, out⟩

/-- Successive approximation. Let `f : E → X` be a linear map of derived π-complete modules and
`g : F → X` a family whose image lies in `f E + π • g F`. Then the image of `g` lies in `f E`. -/
lemma IsDerivedComplete.exists_apply_eq_of_approx (hX : IsDerivedComplete π X)
    (hE : IsDerivedComplete π E) (f : E →ₗ[W] X) (g : F → X)
    (h_approx : ∀ x : F, ∃ (e : E) (y : F), g x = f e + π • g y) (x : F) :
    ∃ e : E, f e = g x :=
  mem_range_of_approx (s := ⟨hE.surjective⟩) (i := ⟨hX.injective⟩) f (fun e ↦ map_smul f π e) g
    h_approx x

lemma IsDerivedComplete.pi {ι : Type*} (h : IsDerivedComplete π X) :
    IsDerivedComplete π (ι → X) :=
  -- `shiftDiff` acts on sequences in `ι → X` coordinate by coordinate
  (swap_bijective.comp h.comp_left).comp swap_bijective

/-- A retract, up to a power of `π`, of a derived π-complete module is derived π-complete. -/
lemma IsDerivedComplete.of_retract (hE : IsDerivedComplete π E) (m : ℕ) (a : E →ₗ[W] X)
    (b : X →ₗ[W] E) (hab : ∀ x : X, a (b x) = π ^ m • x) :
    IsDerivedComplete π X := by
  -- If `u` solves `u j - π • u (j + 1) = b (y j)`, then `sol y u` is the one solution of
  -- `x j - π • x (j + 1) = y j`.
  let sol (y : ℕ → X) (u : ℕ → E) (j : ℕ) : X := ∑ i ∈ range m, π ^ i • y (j + i) + a (u (j + m))
  -- The sum telescopes to `x j - π ^ m • x (j + m)`, and `a (b (x (j + m))) = π ^ m • x (j + m)`.
  have sol_shiftDiff (x : ℕ → X) : sol (shiftDiff X π x) (b ∘ x) = x := by
    simp [sol, hab, smul_smul, ← pow_succ, add_assoc, sum_range_sub' _, shiftDiff, smul_sub]
  refine ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩
  · -- `b` is linear, so `b ∘ x` and `b ∘ y` have the same image under `shiftDiff`
    have hb : b ∘ x = b ∘ y := hE.injective <| funext fun j ↦ by
      simpa [shiftDiff] using congrArg b (congrFun hxy j)
    rw [← sol_shiftDiff x, hxy, hb, sol_shiftDiff]
  · obtain ⟨u, hu⟩ := hE.surjective (b ∘ y)
    -- `sol` is linear and commutes with the shift, so with `shiftDiff`.
    have h_comm : shiftDiff X π (sol y u) = sol (shiftDiff X π y) (shiftDiff E π u) := by
      simp [sol, smul_sum, smul_comm π, sub_add_sub_comm, add_right_comm _ 1, shiftDiff, smul_sub,
        funext_iff]
    exact ⟨sol y u, by rw [h_comm, hu, sol_shiftDiff]⟩

lemma IsDerivedComplete.congr (e : E ≃ₗ[W] X) (hE : IsDerivedComplete π E) :
    IsDerivedComplete π X :=
  hE.of_retract 0 e e.symm (by simp)

/-- The partial sums `t 0 = 0`, `t (j + 1) = t j + π ^ j • y j (t j)` of a series whose `j`-th term
may depend on the partial sum before it. -/
private def partialSums (π : W) (y : ℕ → X → X) : ℕ → X
  | 0 => 0
  | j + 1 => partialSums π y j + π ^ j • y j (partialSums π y j)

/-- Let `W` be a discrete valuation ring with uniformiser `π` and `S` a `W`-algebra. Assume that
`W`, `S` and the `W`-module `X` are derived π-complete and that `X` has finite rank. Then
`S ⊗[W] X` is derived π-complete. On `S`-modules `π` acts through its image in `S`. -/
lemma IsDerivedComplete.baseChange [IsDomain W] [IsDiscreteValuationRing W] (hπ : Irreducible π)
    (hX : IsDerivedComplete π X) (hW : IsDerivedComplete π W)
    (hS : IsDerivedComplete (algebraMap W S π) S)
    (h_rank : Module.rank W X < Cardinal.aleph0) :
    IsDerivedComplete (algebraMap W S π) (S ⊗[W] X) := by
  classical
  -- A maximal independent family gives `τ : W ^ s → X` whose range contains `π ^ (2 * m) • X`
  -- for some `m`. So `S ⊗ X` is a retract of `S ^ s` up to `π ^ (2 * m)`.
  obtain ⟨s, hs, hs_max⟩ : ∃ s : Set X, LinearIndepOn W id s ∧
      ∀ x ∉ s, ∃ b : W, b ≠ 0 ∧ b • x ∈ Submodule.span W (id '' s) :=
    exists_maximal_linearIndepOn W (id : X → X)
  obtain ⟨(fintype_s : Fintype s)⟩ :=
    Cardinal.lt_aleph0_iff_fintype.mp (hs.cardinal_le_rank.trans_lt h_rank)
  let τ : (s → W) →ₗ[W] X := Fintype.linearCombination W Subtype.val
  -- A Baire-type argument. Otherwise choose a bad `y j` for the partial sum `t j` in turn and sum
  -- the series `u 0 = ∑ π ^ j • y j`. By maximality some `π ^ n • u 0` is in the range of `τ`, and
  -- `u 0 = t n + π ^ n • (y n + π • u (n + 1))` contradicts the choice of `y n`.
  obtain ⟨m, r, h_bound⟩ : ∃ (m : ℕ) (r : X), ∀ y : X, ∃ z : X,
      π ^ m • (r + π ^ m • (y + π • z)) ∈ τ.range := by
    by_contra! bad
    have h_bad : ∀ (m : ℕ) (r : X), ∃ y : X, ∀ z : X,
        π ^ m • (r + π ^ m • (y + π • z)) ∉ τ.range := bad
    choose y hy using h_bad
    let t : ℕ → X := partialSums π y
    obtain ⟨u, hu⟩ : ∃ u : ℕ → X, shiftDiff X π u = fun j ↦ y j (t j) := hX.surjective _
    have u_succ (j : ℕ) : y j (t j) + π • u (j + 1) = u j := by simp [← congrFun hu, shiftDiff]
    have partial_sum (j : ℕ) : t j + π ^ j • u j = u 0 := by
      induction j with
      | zero => simp [t, partialSums]
      | succ j ih => simp [← ih, ← u_succ j, t, partialSums, pow_succ, mul_smul, add_assoc]
    obtain ⟨b, hb_ne, hb⟩ : ∃ b : W, b ≠ 0 ∧ b • u 0 ∈ Submodule.span W (id '' s) := by
      by_cases hu_mem : u 0 ∈ s
      · exact ⟨1, one_ne_zero, Submodule.smul_mem _ 1 (Submodule.subset_span ⟨u 0, hu_mem, rfl⟩)⟩
      · exact hs_max (u 0) hu_mem
    obtain ⟨n, c, rfl⟩ : ∃ (n : ℕ) (c : Wˣ), b = c * π ^ n :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb_ne hπ
    -- `π ^ n • u 0` is in the range of `τ`, and `u 0 = t n + π ^ n • (y n (t n) + π • u (n + 1))`
    have h_mem : π ^ n • (t n + π ^ n • (y n (t n) + π • u (n + 1))) ∈ τ.range := by
      simpa [u_succ, partial_sum, τ, mul_smul] using hb
    exact hy n (t n) (u (n + 1)) h_mem
  -- Subtracting the claim for `0` from that for `y` gives
  -- `π ^ (2 * m) • X ⊆ range τ + π • π ^ (2 * m) • X`; approximate.
  have step (y : X) : ∃ (u : s → W) (z : X), π ^ (m + m) • y = τ u + π • π ^ (m + m) • z := by
    have h_bound' : ∀ y : X, ∃ (z : X) (u : s → W), τ u = π ^ m • (r + π ^ m • (y + π • z)) :=
      h_bound
    choose z u hu using h_bound'
    exact ⟨u y - u 0, z 0 - z y,
      by linear_combination (norm := module) hu 0 - hu y - τ.map_sub (u y) (u 0)⟩
  have mem_range (y : X) : (π ^ (m + m) • 1 : X →ₗ[W] X) y ∈ τ.range :=
    hX.exists_apply_eq_of_approx hW.pi τ (fun y ↦ π ^ (m + m) • y) step y
  -- `σ` is defined by `τ (σ y) = π ^ (m + m) • y`
  let σ : X →ₗ[W] (s → W) :=
    .codRestrictOfInjective _ τ hs.fintypeLinearCombination_injective mem_range
  have τ_σ (y : X) : τ (σ y) = π ^ (m + m) • y := by simp [σ]
  have h_free : IsDerivedComplete (algebraMap W S π) (S ⊗[W] (s → W)) :=
    hS.pi.congr (piScalarRight W S S s).symm
  refine h_free.of_retract (m + m) (τ.baseChange S) (σ.baseChange S) fun x ↦ ?_
  induction x with
  | tmul c y => simp [τ_σ, ← map_pow]
  | add x y hx hy => rw [LinearMap.map_add, LinearMap.map_add, hx, hy, smul_add]

/-- If every value of `Φ` is derived `a`-complete, so is the cohomology `Hⁿ(N, Φ)`. -/
lemma IsDerivedComplete.cohomology (h_complete : ∀ A : C, IsDerivedComplete a (Φ.obj A))
    (N : AbFunctor C) (n : ℕ) : IsDerivedComplete a (H N (moduleCoeff Φ) n) := by
  -- `shiftDiff` is induced by an endomorphism `δ` of the coefficients `∏ Φ` (product over `ℕ`).
  -- It is an isomorphism by `h_complete`, and cohomology commutes with products (`H.pi_bijective`).
  let P : AbFunctor C := piAbFunctor fun _ : ℕ ↦ moduleCoeff Φ
  let π (j : ℕ) : P ⟶ moduleCoeff Φ := piAbFunctor.π (fun _ ↦ moduleCoeff Φ) j
  let δ : P ⟶ P := piAbFunctor.lift fun j ↦ π j - π (j + 1) ≫ End.asHom (act a)
  have δ_iso : IsIso δ :=
    (isoOfAppBijective δ fun A ↦ ((h_complete A).congr moduleEquiv.symm :)).isIso_hom
  have square (x : H N P n) :
      (shiftDiff _ a fun j ↦ push N (π j) n x) = fun j ↦ push N (π j) n (push N δ n x) := by
    funext j
    -- `δ ≫ π j = π j - π (j + 1) ≫ act a`, and `push` is additive in the map of coefficients
    have h_sub : pushHom N P (moduleCoeff Φ) n (π j - π (j + 1) ≫ End.asHom (act a)) x =
        pushHom N P (moduleCoeff Φ) n (π j) x -
          pushHom N P (moduleCoeff Φ) n (π (j + 1) ≫ End.asHom (act a)) x := by
      rw [_root_.map_sub, AddMonoidHom.sub_apply]
    simp only [shiftDiff, smul_eq_push, ← push_comp, π, δ]
    exact h_sub.symm
  have push_δ : Bijective (push N δ n) := push_bijective_of_isIso δ_iso n
  have push_π : Bijective fun (x : H N P n) (j : ℕ) ↦ push N (π j) n x := pi_bijective n
  exact (Comparison.bijective_iff_of_comm_sq square push_π push_π).1 push_δ

/-! ### Reduction modulo a scalar and the adic step -/

/-- The sequence `0 → Φ → Φ → G → 0` formed by multiplication by `a` and by `q` is short exact. -/
abbrev ModShortExact (a : S) (q : moduleCoeff Φ ⟶ G) : Prop :=
  ∃ zero_comp : End.asHom (act a) ≫ q = 0,
    (ShortComplex.mk (End.asHom (act a)) q zero_comp).ShortExact

/-- If every `Φ A` is `m`-torsion-free and `q` is a reduction modulo `m` at every `A`, then
`0 → Φ → Φ → F → 0` is short exact (after the universe lift of `Ab`), the first map being
multiplication by `m`. -/
lemma modShortExact_of_isSMulRegular_of_isReductionMod {F : C ⥤ Ab}
    {q : Φ ⋙ forget₂ (ModuleCat S) Ab ⟶ F} {m : ℕ} (h_regular : ∀ A : C, IsSMulRegular (Φ.obj A) m)
    (h_reduction : ∀ A : C, IsReductionMod m (q.app A : Φ.obj A → F.obj A)) :
    ModShortExact (m : S) (whiskerRight q AddCommGrpCat.uliftFunctor) := by
  -- Read multiplication by the natural number `m` as the action of the scalar `(m : S)`.
  obtain ⟨h_inj, h_surj, h_exact⟩ : (∀ A : C, Injective fun x : Φ.obj A ↦ (m : S) • x) ∧
      (∀ A : C, Surjective (q.app A : Φ.obj A → F.obj A)) ∧
      ∀ A : C, Exact (fun x : Φ.obj A ↦ (m : S) • x) (q.app A : Φ.obj A → F.obj A) := by
    simpa [IsSMulRegular, IsReductionMod, forall_and, ← Nat.cast_smul_eq_nsmul S] using
      And.intro h_regular h_reduction
  -- Short exact objectwise, hence as functors to `Ab`; the universe lift is an exact functor.
  obtain ⟨w, h_short⟩ :=
    shortExact_of_app (α := whiskerRight ((m : S) • 𝟙 Φ) (forget₂ (ModuleCat S) Ab)) (g := q)
      h_inj h_exact h_surj
  exact ⟨_,
    h_short.map_of_exact ((whiskeringRight C Ab AddCommGrpCat).obj AddCommGrpCat.uliftFunctor)⟩

/-- `modShortExact_of_isSMulRegular_of_isReductionMod` with both conditions in one hypothesis. -/
lemma modShortExact_of_isReductionMod {F : C ⥤ Ab} {q : Φ ⋙ forget₂ (ModuleCat S) Ab ⟶ F} {m : ℕ}
    (h : ∀ A : C,
      IsSMulRegular (Φ.obj A) m ∧ IsReductionMod m (q.app A : Φ.obj A → F.obj A)) :
    ModShortExact (m : S) (whiskerRight q AddCommGrpCat.uliftFunctor) :=
  modShortExact_of_isSMulRegular_of_isReductionMod (fun A ↦ (h A).left) fun A ↦ (h A).right

/-- A class killed by reduction modulo a is a multiple of a. -/
lemma ModShortExact.exists_smul_eq_of_push_eq_zero (h_exact : ModShortExact a q) {n : ℕ}
    (x : H N (moduleCoeff Φ) n) (hx : push N q n x = 0) :
    ∃ y : H N (moduleCoeff Φ) n, a • y = x := by
  obtain ⟨zero_comp, h_short⟩ := h_exact
  exact x.covariant_sequence_exact₂ N h_short hx

/-- `M` is `c`-divisible: multiplication by `c` on `M` is surjective. -/
def IsSMulDivisible {R : Type*} (M : Type*) [SMul R M] (c : R) : Prop :=
  Surjective (c • · : M → M)

/-- A submodule `K` of a derived π-complete module on which multiplication by `π` is onto is
zero. -/
lemma IsDerivedComplete.eq_zero_of_mem_of_isSMulDivisible (hX : IsDerivedComplete π X)
    {K : Submodule W X} (hK : IsSMulDivisible K π) {x : X} (hx : x ∈ K) : x = 0 := by
  -- approximation with `f = 0`: every `y` in `K` is `0 + π • z` with `z` in `K`
  have h_approx (y : K) : ∃ (e : X) (z : K), (y : X) = (0 : X →ₗ[W] X) e + π • (z : X) := by
    obtain ⟨z, hz⟩ := hK y
    exact ⟨0, z, by simp [← hz]⟩
  obtain ⟨e, he⟩ := hX.exists_apply_eq_of_approx hX 0 K.subtype h_approx ⟨x, hx⟩
  simpa using he.symm

/-- The adic step. Let `α : N' ⟶ φ ⋙ N`, let `0 → Φ → Φ → G → 0` and `0 → Φ' → Φ' → G' → 0` be exact
with first maps multiplication by `a`, and let `β : φ ⋙ Φ ⟶ Φ'` induce `γ : φ ⋙ G ⟶ G'` on the
quotients (`β` followed by `q'` equals `q` followed by `γ`); with `α`, these induce comparison maps
`Hⁿ(N, Φ) → Hⁿ(N', Φ')` and `Hⁿ(N, G) → Hⁿ(N', G')`. Assume every `Hⁿ(N', Φ')` is derived
`a`-complete, and `Hⁿ(N, Φ)` is derived `a`-complete whenever the kernel of the degree-`n`
comparison map for `β` is `a`-divisible. If the comparison maps for `γ` are bijective in every
degree `n`, then so are those for `β`. -/
lemma Comparison.IsBijective.of_mod {q' : moduleCoeff Φ' ⟶ G'} {γ : φ ⋙ G ⟶ G'}
    (h_exact : ModShortExact a q) (h_exact' : ModShortExact a q')
    (h_comm : coeffMap β ≫ q' = φ.whiskerLeft q ≫ γ)
    (h_source : ∀ n : ℕ,
      IsSMulDivisible (pullₗ β α n).ker a → IsDerivedComplete a (H N (moduleCoeff Φ) n))
    (h_target : ∀ n : ℕ, IsDerivedComplete a (H N' (moduleCoeff Φ') n))
    (hγ : (of φ γ).IsBijective α) :
    (ofModuleHom φ β).IsBijective α := by
  obtain ⟨zero_comp, h_short⟩ := h_exact
  obtain ⟨zero_comp', h_short'⟩ := h_exact'
  -- Compare the long exact sequences of `0 → Φ → Φ → G → 0` and `0 → Φ' → Φ' → G' → 0`.
  have h_linear :
      φ.whiskerLeft (act (F := moduleCoeff Φ) a).asHom ≫ coeffMap β =
        coeffMap β ≫ End.asHom (act a) := by
    ext
    apply_rules [up_inj.mpr, LinearMap.map_smul]
  have ladder : (LongExactSeq.covariant h_short N).Hom (LongExactSeq.covariant h_short' N')
      ((ofModuleHom φ β).pull α) ((ofModuleHom φ β).pull α) ((of φ γ).pull α) :=
    pull_hom_covariant h_short h_short' ⟨coeffMap β, coeffMap β, γ, h_linear.symm, h_comm⟩ α
  -- The kernel is `a`-divisible, as the comparison mod `a` is injective in degree `n` and
  -- surjective in degree `n - 1`.
  have ker_div (n : ℕ) : IsSMulDivisible (pullₗ β α n).ker a := by
    -- In the rotated sequences the map `g` is multiplication by `a`: an element of the kernel
    -- that maps to `g 0 = 0` is `a` times an element of the kernel.
    have h_preimage :
        ∀ x : (LongExactSeq.covariant h_short N).rotate.C n,
          (ofModuleHom φ β).pull α n x = (LongExactSeq.covariant h_short' N').rotate.g n 0 →
            ∃ z, (ofModuleHom φ β).pull α n z = 0 ∧
              (LongExactSeq.covariant h_short N).rotate.g n z = x := by
      refine ladder.rotate.exists_preimage (n := n) ?_ (hγ n).injective 0
      -- the comparison mod `a` is surjective in degree `n - 1`, and the identity in degree `-1`
      cases n with
      | zero => exact fun b ↦ ⟨b, rfl⟩
      | succ m => exact (hγ m).surjective
    intro b
    obtain ⟨z, hz_ker, hz⟩ := h_preimage b.val (b.prop.trans (map_zero _).symm)
    exact ⟨⟨z, hz_ker⟩, Subtype.ext hz⟩
  have complete (n : ℕ) : IsDerivedComplete a (H N (moduleCoeff Φ) n) := h_source n (ker_div n)
  -- The kernel is a divisible submodule of a complete module, hence zero.
  have inj (n : ℕ) : Injective (pullₗ β α n) := (injective_iff_map_eq_zero _).mpr fun x hx ↦
    (complete n).eq_zero_of_mem_of_isSMulDivisible (ker_div n) hx
  -- The comparison is onto mod `a`, by injectivity in degree `n + 1`; approximate.
  have surj_mod (n : ℕ) (y : H N' (moduleCoeff Φ') n) :
      ∃ (x : H N (moduleCoeff Φ) n) (z : H N' (moduleCoeff Φ') n), y = pullₗ β α n x + a • z := by
    -- lift a preimage `w` of the reduction of `y` with the ladder, whose `f` is multiplication
    -- by `a`
    obtain ⟨w, hw⟩ := (hγ n).surjective ((LongExactSeq.covariant h_short' N').g n y)
    obtain ⟨x, ⟨z, hz⟩, -⟩ := ladder.exists_preimage_mod_f (inj (n + 1)) y w hw
    exact ⟨x, z, hz⟩
  exact fun n ↦ ⟨inj n,
    (h_target n).exists_apply_eq_of_approx (complete n) (pullₗ β α n) (fun y ↦ y) (surj_mod n)⟩

/-! ### p-adic completion of algebras and modules -/

/-- A `p`-torsion-free, `p`-adically complete algebra (`IsCompleteTorsionFree B`, with fields
`complete` and `regular`) is derived `p`-complete. Here `p` is the prime fixed by `ThePrime p`. -/
lemma IsCompleteTorsionFree.isDerivedComplete [ThePrime p] (hB : IsCompleteTorsionFree B) :
    IsDerivedComplete (p : S) B :=
  .of_isAdicComplete (isAdicComplete_over_base hB.complete)

lemma IsCompleteTorsionFree.isSMulRegular_natCast [ThePrime p] (hB : IsCompleteTorsionFree B) :
    IsSMulRegular B (p : S) :=
  fun _ _ hxy ↦ hB.regular (mod_cast hxy)

open AdicCompletion Adic Submodule.Quotient LinearMap IsScalarTower Comparison LinearEquiv

/-- The linear map `j` induces a bijection of the `p`-adic completions. -/
abbrev IsCompletionBijective (p : ℕ) (j : X →ₗ[W] E) : Prop :=
  Bijective (AdicCompletion.map (span {(p : W)}) j)

/-- An algebra map that is onto modulo `p` and injective modulo every power of `p` is bijective
on the `p`-adic completions. -/
lemma IsCompletionBijective.of_dvd_sub_of_pow_dvd {B' : Type*} [CommRing B'] [Algebra S B']
    (κ : B →ₐ[S] B') (h_approx : ∀ y : B', ∃ x : B, (p : B') ∣ y - κ x)
    (h_dvd : ∀ (n : ℕ) (x : B), (p : B') ^ n ∣ κ x → (p : B) ^ n ∣ x) :
    IsCompletionBijective p κ.toLinearMap := by
  -- modulo each `p ^ n`, `κ` is injective
  have h_inj (n : ℕ) : Injective (κ.toLinearMap.reduceModIdeal (span {(p : S)} ^ n)) := by
    refine (injective_iff_map_eq_zero _).mpr ?_
    rintro ⟨b⟩
    simpa [quot_mk_eq_mk, span_singleton_pow, mem_span_singleton, Ideal.map_span] using h_dvd n b
  refine ⟨fun x y e ↦ AdicCompletion.ext fun n ↦ h_inj n (congrArg (fun z ↦ z.val n) e :),
    map_surjective_of_mkQ_comp_surjective ?_⟩
  -- modulo `p`, `κ` is onto
  rintro ⟨b'⟩
  simpa [quot_mk_eq_mk, Submodule.Quotient.eq, mem_span_singleton, dvd_sub_comm, Ideal.map_span]
    using h_approx b'

/-- Every element of the `p`-adic completion of `B` is congruent modulo `p` to the image of an
element of `B`. -/
private lemma exists_dvd_sub_algebraMap (y : PrincipalCompletion B p) :
    ∃ x : B, (p : PrincipalCompletion B p) ∣ y - algebraMap B (PrincipalCompletion B p) x := by
  obtain ⟨x, hx⟩ := exists_approx y 1
  -- the coercion of `x` into the completion is, by definition, the algebra map
  exact ⟨x, by simpa using hx⟩

/-- The map from `B` to its `p`-adic completion `PrincipalCompletion B p` is bijective on the
`p`-adic completions. -/
lemma isCompletionBijective_completion :
    IsCompletionBijective p (toAlgHom S B (PrincipalCompletion B p)).toLinearMap :=
  .of_dvd_sub_of_pow_dvd _ (fun y ↦ exists_dvd_sub_algebraMap y) fun _ _ ↦ pow_dvd_iff.mp

/-- If `j : X → E` is bijective on the `p`-adic completions, every linear map from `X` to a
`p`-adically complete module extends uniquely along `j`. -/
lemma IsCompletionBijective.linearMap_comp_bijective {j : X →ₗ[W] E}
    (h_bij : IsCompletionBijective p j) [Module W Y] [IsAdicComplete (span {(p : W)}) Y] :
    Bijective fun f : E →ₗ[W] Y ↦ f ∘ₗ j := by
  -- The inverse extends `g`: map `E` to its completion, identify that with the completion of `X`
  -- by `h_bij`, apply the completion of `g`, and use that `Y` is its own completion.
  let I : Ideal W := span {(p : W)}
  let extend (g : X →ₗ[W] Y) : E →ₗ[W] Y :=
    (ofLinearEquiv I Y).symm.toLinearMap ∘ₗ
      (AdicCompletion.map I g ∘ₗ (ofBijective _ h_bij).symm.toLinearMap).restrictScalars W ∘ₗ of I E
  refine bijective_iff_has_inverse.mpr ⟨extend, fun f ↦ ?_, fun g ↦ ?_⟩
  · ext y
    simp [extend, I, ← map_of, ← AdicCompletion.map_comp_apply, symm_apply_eq]
  · ext x
    simp [extend, I, ← map_of, symm_apply_eq]

/-- A reduction modulo `p` of the `p`-adic completion of `B` restricts to a reduction modulo `p`
of `B`. -/
lemma IsReductionMod.comp_algebraMap {q : PrincipalCompletion B p →+ X}
    (h_red : IsReductionMod p q) :
    IsReductionMod p (q.comp (algebraMap B (PrincipalCompletion B p)).toAddMonoidHom) := by
  obtain ⟨h_surj, h_exact⟩ : Surjective q ∧ Exact (fun x ↦ p • x) q := h_red
  refine ⟨h_surj.forall.mpr fun y ↦ ?_, fun x ↦ ?_⟩
  · -- `y` is an element of `B` plus a multiple of `p`, which `q` kills
    obtain ⟨x, z, hz⟩ : ∃ (x : B) (z : PrincipalCompletion B p),
        y - algebraMap B (PrincipalCompletion B p) x = p * z :=
      exists_dvd_sub_algebraMap y
    have hq : q (p * z) = 0 := (h_exact _).mpr ⟨z, nsmul_eq_mul p z⟩
    exact ⟨x, by simp [eq_add_of_sub_eq hz, hq]⟩
  · -- `p` divides `x` in the completion exactly when it does in `B`
    simpa [h_exact _, dvd_def, eq_comm] using pow_dvd_iff (π := (p : B)) (n := 1) (y := x)

/-- Completed base change. Let `W` be a discrete valuation ring with uniformiser `p`, `S` a flat
`W`-algebra, `Θ` a functor to `W`-algebras and `X` a functor to `S`-algebras. Assume that `W`,
`S`, every `Θ A` and every `X A` are `p`-torsion-free and `p`-complete, and that the cohomology
of `N` commutes with flat base change. Let `j : S ⊗ Θ ⟶ X` be bijective modulo `p`, and let
`Hⁿ(N, Θ)` have finite rank over `W` whenever the kernel of `Hⁿ(j)` is `p`-divisible. Then
`Hⁿ(j) : Hⁿ(N, S ⊗ Θ) → Hⁿ(N, X)` is bijective for all `n`. -/
lemma HasFlatBaseChange.isBijective_of_isReductionMod [ThePrime p]
    [IsDomain W] [IsDiscreteValuationRing W]
    [Module.Flat W S] {Θ : C ⥤ CommAlg W} {X : C ⥤ CommAlg S} (hN : HasFlatBaseChange N)
    (hW : IsCompleteTorsionFree W) (hS : IsCompleteTorsionFree S)
    (hΘ : ∀ A : C, IsCompleteTorsionFree (Θ.obj A)) (hp : Irreducible (p : W))
    (j : 𝟭 C ⋙ asModules Θ ⋙ tensorWith S S ⟶ asModules X)
    (h_rank : ∀ n : ℕ, IsSMulDivisible (pullₗ j (𝟙 N) n).ker (p : S) →
      Module.rank W (H N (moduleCoeff (asModules Θ)) n) < Cardinal.aleph0)
    (hX : ∀ A : C, IsCompleteTorsionFree (X.obj A))
    -- `j` is bijective mod `p`: it carries a reduction mod `p` back to a reduction mod `p`
    (hj : ∀ (A : C) {Y : Type} [AddCommGroup Y] (q : X.obj A →+ Y),
      IsReductionMod p q → IsReductionMod p (q ∘ j.app A)) :
    (ofModuleHom (𝟭 C) j).IsBijective (𝟙 N) := by
  -- Apply `Comparison.IsBijective.of_mod` with `a = p`. Both `S ⊗ Θ` and `X` are
  -- `p`-torsion-free, and both reduce mod `p` to the same functor, `X` mod `p`.
  let modp : ModuleCat S ⥤ ModuleCat S :=
    { obj M := ModuleCat.of S (QuotSMulTop (p : S) M)
      map f := ofHom (QuotSMulTop.map (p : S) f.hom) }
  let reduce : 𝟭 (ModuleCat S) ⟶ modp := { app _ := ↟(Submodule.mkQ _) }
  let q : asModules X ⟶ asModules X ⋙ modp := (asModules X).whiskerLeft reduce
  have isMod_q (A : C) : IsReductionMod p (q.app A).hom.toAddMonoidHom := by
    -- `q.app A` is the quotient map by `p`, and `p • x = (p : S) • x`
    refine ⟨Submodule.mkQ_surjective _, ?_⟩
    have h_exact_mkQ : Exact (fun x : X.obj A ↦ (p : S) • x) (q.app A).hom.toAddMonoidHom :=
      exact_lsmul_mkQ_smul_top (X.obj A) (p : S)
    simpa [← Nat.cast_smul_eq_nsmul S] using h_exact_mkQ
  have reg_ten (A : C) : IsSMulRegular (S ⊗[W] Θ.obj A) p := fun _ _ e ↦
    (hΘ A).isSMulRegular_natCast.lTensor S (mod_cast e)
  have h_exact_source : ModShortExact (p : S) (coeffMap (j ≫ q)) :=
    modShortExact_of_isSMulRegular_of_isReductionMod reg_ten fun A ↦ hj A _ (isMod_q A)
  have h_exact_target : ModShortExact (p : S) (coeffMap q) :=
    modShortExact_of_isSMulRegular_of_isReductionMod (fun A ↦ (hX A).regular) isMod_q
  -- mod `p` both sides are `X` mod `p` and the comparison is the identity
  refine .of_mod (q := coeffMap (j ≫ q)) (q' := coeffMap q) h_exact_source h_exact_target rfl
    (fun n h_div ↦ ?_) (.cohomology (fun A ↦ (hX A).isDerivedComplete) N)
    (IsCohomEquiv.of_isIso (𝟙 N)).bij
  -- The source is `S ⊗ Hⁿ(N, Θ)` by flat base change, and `Hⁿ(N, Θ)` is complete of finite rank.
  have h_ten : IsDerivedComplete (p : S) (S ⊗[W] H N (moduleCoeff (asModules Θ)) n) := by
    simpa using IsDerivedComplete.baseChange hp
      (.cohomology (fun A ↦ (hΘ A).isDerivedComplete) N n) hW.isDerivedComplete
      (mod_cast hS.isDerivedComplete) (h_rank n h_div)
  exact h_ten.congr (.ofBijective _ (hN W S S (asModules Θ) n))

variable (S p)

/-- The natural transformation from the identity functor on commutative S-algebras to the p-adic
completion functor, given by the canonical map from B to its completion. -/
def algCompletion.of : 𝟭 (CommAlg S) ⟶ algCompletion S p where
  app B := CommAlgCat.ofHom (toAlgHom S B (PrincipalCompletion B p))
  naturality := by
    delta algCompletion
    aesop

/-- The functor sending an S-module to its p-adic completion. -/
def moduleCompletion : ModuleCat S ⥤ ModuleCat S :=
  CategoryTheory.Functor.mk _ fun f ↦
    ofHom (LinearMap.restrictScalars S (AdicCompletion.map (span {↑p}) f.1))

/-- The `p`-adic completion functor on `S`-modules is additive. -/
instance : (moduleCompletion S p).Additive := ⟨hom_ext (map_ext'' _ rfl)⟩

/-- For commutative S-algebras B, the p-adic completion of the S-module B is naturally
isomorphic to the S-module underlying the p-adic completion of the algebra B. -/
def moduleCompletionIso :
    asModules (𝟭 (CommAlg S)) ⋙ moduleCompletion S p ≅ asModules (algCompletion S p) :=
  -- The map from `B` to its completion `PrincipalCompletion B p` is bijective on completions of
  -- modules,
  isoOfAppBijective (whiskerRight (whiskerRight (algCompletion.of S p) _) (moduleCompletion S p))
    (fun B ↦ isCompletionBijective_completion (B := B)) ≪≫
    -- and the complete module `PrincipalCompletion B p` is its own completion.
    Iso.symm
    (NatIso.ofComponents fun _ ↦
      (@ofLinearEquiv S _ _ _ _ _ (isAdicComplete_over_base Adic.isAdicComplete)).toModuleIso)

end New.Variety

end Completion

/-! ## Comparisons with identity coefficient map as restrictions -/

section CoefficientComparison

open CategoryTheory Functor

/-- Let `θ : Ψ ⋙ G ≅ M` be an isomorphism of coefficient functors. The comparison maps
`Hⁿ(N, G∘Ψ) → Hⁿ(N', G∘Ψ∘φ)` along `α : N' ⟶ φ ⋙ N`, with identity map `𝟙 (φ ⋙ Ψ)` of coefficients
(the statement `CoeffCompBijective (𝟙 (φ ⋙ Ψ)) α G`), are bijective for all `n` if and only if
restriction along `φ` with coefficients `M`, `Hⁿ(N, M) → Hⁿ(N', M∘φ)`, is bijective for all `n`. -/
lemma New.Variety.Comparison.coeffCompBijective_id_iff_restrict {C C' : Type 1} {D : Type*}
    {S : Type} [Category C] [Category C'] [Category D] [CommRing S] {φ : C' ⥤ C}
    {N : C ⥤ AddCommGrpCat}
    {N' : AbFunctor C'} {α : N' ⟶ φ ⋙ N} {Ψ : C ⥤ D} {G : D ⥤ ModuleCat S} {M : C ⥤ ModuleCat S}
    (θ : Ψ ⋙ G ≅ M) :
    CoeffCompBijective (S := S) (𝟙 (φ ⋙ Ψ)) α G ↔ (restrict φ (moduleCoeff M)).IsBijective α := by
  -- `θ` gives isomorphisms of coefficients on `C` and, through `φ`, on `C'`. Both comparison maps
  -- are identities, so they are compatible with these isomorphisms.
  let γ : (Ψ ⋙ G) ⋙ moduleCoeff (𝟭 (ModuleCat S)) ⟶ M ⋙ moduleCoeff (𝟭 (ModuleCat S)) :=
    whiskerRight θ.hom (moduleCoeff (𝟭 _))
  apply isBijective_iff_of_coeff_iso γ (φ.whiskerLeft γ)
  -- what is left is the compatibility of the two identity comparison maps with `γ`, componentwise
  aesop

end CoefficientComparison

end
