import Lib.General.LinearAlgebra.MatrixPolynomials
import Lib.General.NumberTheory.FrobeniusOrbits
import Lib.LocalGL.Green.HallAlgebra

/-!
# Cuspidal class functions on GL_n over a finite field: μ, supports, values, inner products

Let `k` be a finite field. `New.Hall k` is the ring of functions on the similarity classes
`New.SimClass k` of endomorphisms over `k`, with the parabolic induction product. In it,
𝟙 = `New.Hall.constOne` is the constant function 1, μ = `New.Hall.moebius` is its inverse, and
C_η = `New.Hall.greenCuspidal k η`. The file proves that C_η is cuspidal and that cuspidal functions
vanish off classes whose characteristic polynomial is a power of an irreducible polynomial. It
computes μ and C_η at multiplication by a field generator, and writes the inner product of C_η with
B·μ as a mean over the units of a field extension.

## Main definitions and results

* `New.Hall.crapo_complementation`, `New.Hall.isSemisimple_of_moebius_ne_zero`: μ is a Möbius
  function on the lattice of stable subspaces, so it vanishes off semisimple classes.
* `New.Hall.greenCuspidal_mul_constOne`, `New.Hall.isCuspidal_greenCuspidal`: C_η ∗ 𝟙 = −β_η, and
  C_η is cuspidal.
* `New.Hall.IsCuspidal.exists_charpoly_eq_pow`: a cuspidal function vanishes at the class of `g`
  unless the characteristic polynomial of `g` is a power of an irreducible one.
* `New.greenCuspidal_simClassOf_eq_mul`: the value of `New.Hall.greenCuspidal k η` at the class of
  `g` depends on `η` only at the elements whose Frobenius orbit gives all eigenvalues of `g`.
* `New.rankInner_greenCuspidal_mulMoebius`: the inner product on GL_{[L:k]}(k) of C_η
  (`New.Hall.greenCuspidal`) with B·μ (`New.Hall.mulMoebius`) is the mean over z ∈ L^× of conj η(φz)
  times B at multiplication by z.

Notions from other files:
* `New.Hall.IsCuspidal`: F is cuspidal when its average over block triangular endomorphisms with
  diagonal blocks a, b vanishes whenever both a and b have nonzero dimension.
* `New.Hall.brauerLift`: The class function β_η sending an endomorphism to the sum of η over the
  roots in K of its characteristic polynomial, counted with multiplicity.
* `New.Hall.greenCuspidal`: The class function C_η = (β_η·μ) ∗ 𝟙: the pointwise product of the
  eigenvalue sum β_η with the inverse μ of 𝟙, multiplied in the induction product by the constant
  function 𝟙.

## Relation to the literature

Known result: Brauer lift is a virtual character; cuspidal times Steinberg is induced from a torus.
Brauer induction is not used here. The character induced from the Coxeter torus is instead divided
by the Steinberg character, read as a Möbius function on semisimple classes compatibly with the
Galois action, and only the vanishing half of Crapo's theorem is used. Source: Green 1955, Thm 1; T.
A. Springer, Sém. Bourbaki 441 (1973/74), 1.1-1.7; R. Carter, Finite groups of Lie type (1985), for
Steinberg times a torus character; P. Hall's lemma, D. Krasula, arXiv 2403.05656, Lemma 23, and H.
Crapo's complementation theorem, for the vanishing of the Möbius number off semisimple modules.

See also `Lib.LocalGL.Green.TauFunctions`.
-/

/-! ## Crapo's lemma, the inverse μ of 𝟙, and cuspidality of C_η -/

namespace New.Hall

open Module Finset StableSubspace Submodule LinearMap ComplexConjugate End Polynomial

open scoped Classical in
/-- A form of Crapo's complementation theorem. Let `μ` be a function on a finite modular lattice
whose sum over the elements below `X` vanishes for every `X ≠ ⊥`. If `μ ⊤ ≠ 0`, every element
has a complement. -/
lemma crapo_complementation {L : Type*} [Lattice L] [BoundedOrder L] [IsModularLattice L]
    [Fintype L] {μ : L → ℂ} (h_sum : ∀ X ≠ ⊥, ∑ U : L with U ≤ X, μ U = 0) (h_ne : μ ⊤ ≠ 0)
    (W : L) : IsComplemented W := by
  -- Take `C` maximal among the elements disjoint from `W`; we show that `W ⊔ C = ⊤`.
  obtain ⟨C, hC, h_max⟩ : ∃ C : L, Maximal (Disjoint W) C :=
    exists_maximal_of_wellFoundedGT (Disjoint W) ⟨⊥, disjoint_bot_right⟩
  refine ⟨C, hC, codisjoint_iff_le_sup.mpr ?_⟩
  by_contra h_top
  apply h_ne
  -- By induction on `U`, `μ U = 0` unless `U ≤ W ⊔ C`.
  suffices h_vanish : ∀ U : L, ¬U ≤ W ⊔ C → μ U = 0 from h_vanish ⊤ h_top
  intro U hU
  induction U using WellFoundedLT.induction with | ind U ih => ?_
  -- If `U ⊓ (W ⊔ C) = ⊥` then `W` is disjoint from `C ⊔ U` (modularity), so `U ≤ C` by maximality.
  have meet_ne : U ⊓ (W ⊔ C) ≠ ⊥ := by
    grind [disjoint_iff, le_sup_left, le_sup_right,
      hC.disjoint_sup_right_of_disjoint_sup_left (c := U)]
  -- The sums of `μ` below `U` and below `U ⊓ (W ⊔ C)` vanish; by `ih` their difference is `μ U`.
  have h_sub : ({A | A ≤ U ⊓ (W ⊔ C)} : Finset L) ⊆ ({A | A ≤ U} : Finset L) := by
    grind [le_inf_iff]
  rw [← h_sum U (ne_bot_of_le_ne_bot meet_ne inf_le_left), ← sum_sdiff h_sub, h_sum _ meet_ne,
    sum_eq_single U]
  · rw [add_zero]
  · -- an `A < U` outside `U ⊓ (W ⊔ C)` is not below `W ⊔ C`, so `μ A = 0` by `ih`
    grind [Ne.lt_of_le, le_inf_iff]
  · -- `U` itself lies in the difference, as `¬U ≤ W ⊔ C`
    grind [le_inf_iff]

variable {k V K : Type*} [Field k] [Finite k] [AddCommGroup V] [Module k V] [Module.Finite k V]
  {g : End k V} {o : SimClass k} (B : Hall k) [Field K] [Algebra k K] (η : K → ℂ)

/-! ### The inverse of the constant function -/

/-- `μ` is inverse to `New.Hall.constOne`; at `g` this reads: the sum of `μ (g|W)` over the stable
subspaces `W` is `1` in dimension `0` and `0` otherwise. -/
lemma moebius_mul_constOne : moebius * constOne = (1 : Hall k) := by grind [isUnit_constOne]

/-- At the class of `g`, the sum of `μ (g|W)` over the `g`-stable subspaces `W` is the value of the
unit `1` of `New.Hall k` at the class of `g`. -/
lemma sum_moebius_simClassOf_endOnSub :
    ∑ W : StableSubspace g, moebius (simClassOf W.endOnSub) = (1 : Hall k) (simClassOf g) := by
  rw [← moebius_mul_constOne]
  simp [mul_simClassOf, finsum_eq_sum_of_fintype]

/-- An endomorphism at whose class `μ` does not vanish is semisimple. -/
lemma isSemisimple_of_moebius_ne_zero (h_mu_ne : moebius (simClassOf g) ≠ 0) : g.IsSemisimple := by
  classical
  -- Apply `crapo_complementation` to the (modular, finite) lattice of `g`-stable subspaces, with
  -- the function `U ↦ μ (simClassOf (endOnSub U))`: every stable subspace has a stable complement.
  have h_modular : IsModularLattice g.invtSubmodule :=
    ⟨fun y ↦ sup_inf_le_assoc_of_le (y : Submodule k V)⟩
  let fintype_invt : Fintype g.invtSubmodule := fintypeStableSubspace
  refine isSemisimple_iff'.mpr
    (crapo_complementation (μ := fun U ↦ moebius (simClassOf (endOnSub U))) (fun X hX ↦ ?_) ?_)
  · -- The sum over `U ≤ X` is that of `sum_moebius_simClassOf_endOnSub` for `endOnSub X`, which is
    -- `0` for `X ≠ ⊥`; `sum_comap` matches the stable subspaces of `X` with the stable `U ≤ X`.
    have h_subtype : ∀ v : (X : Submodule k V),
        (X : Submodule k V).subtype (endOnSub X v) = g ((X : Submodule k V).subtype v) := by aesop
    have h_reindex (F : StableSubspace (endOnSub X) → ℂ) :
        ∑ W, F W = ∑ U : StableSubspace g, if (U : Submodule k V) ≤ X then
          F (comap (X : Submodule k V).subtype h_subtype U) else 0 := by
      simpa [sum_filter] using sum_comap (g := endOnSub X) (X : Submodule k V).subtype h_subtype F
    -- The sum of the statement, over `g.invtSubmodule`, is the same sum over `StableSubspace g`.
    show ∑ U ∈ univ.filter fun U : StableSubspace g ↦ U.val ≤ X.val,
      moebius (simClassOf U.endOnSub) = 0
    simpa +contextual [hX, h_reindex, sum_filter] using sum_moebius_simClassOf_endOnSub
      (g := endOnSub X)
  · -- The restriction of `g` to `⊤` is similar to `g`.
    have h_top : simClassOf (endOnSub (⊤ : g.invtSubmodule)) = simClassOf g :=
      simClassOf_eq_of_equiv topEquiv fun _ ↦ rfl
    rwa [h_top]

@[simp]
lemma moebius_eq_one_of_dim_eq_zero (h_dim : o.dim = 0) : moebius o = 1 := by
  simpa [h_dim] using congrFun (moebius_mul_constOne (k := k)) o

/-- Let μ (`moebius`) be the inverse of the constant class function 1 for the parabolic-induction
product on similarity classes over the finite field k. For any class function `B`, the average of
the pointwise product `B μ` over the block triangular endomorphisms with diagonal blocks `a`, `b` is
`μ a * μ b * B (b ⊕ a)`. Here `b ⊕ a` is the block diagonal map of the chosen representatives of `b`
and `a`. -/
@[simp ↓]
lemma blockAverage_mulMoebius (a b : SimClass k) :
    B.mulMoebius.blockAverage a b =
      moebius a * moebius b * B (simClassOf (b.out.snd.prodMap a.out.snd)) := by
  -- First `δ moebius = moebius ⊗ moebius` for `δ = blockAverage`: cancel the unit `constOne` in
  -- each of the two variables. By the Mackey formula `blockAverage_mul` and `δ 𝟙 = 𝟙 ⊗ 𝟙`, the left
  -- side becomes `δ (moebius * 𝟙) = δ 1`; this and the right side `(moebius * 𝟙) ⊗ (moebius * 𝟙)`
  -- are `1 ⊗ 1`.
  have delta_eq : blockAverage moebius a = moebius a • moebius := by
    refine isUnit_constOne.mul_right_cancel (ext fun _ y ↦ ?_)
    let F : Hall k := fun c ↦ (blockAverage moebius c * constOne : Hall k) (simClassOf y)
    let F' : Hall k := fun c ↦ (moebius c • moebius * constOne : Hall k) (simClassOf y)
    suffices key : F * constOne = F' * constOne from
      congrFun (isUnit_constOne.mul_right_cancel key) a
    ext _ x
    have h_mackey : (moebius * constOne).blockAverage (simClassOf x) (simClassOf y) =
        ∑ A : StableSubspace x, (moebius.blockAverage (simClassOf A.endOnSub) *
          constOne.blockAverage (simClassOf A.endOnQuot)) (simClassOf y) :=
      blockAverage_mul moebius constOne x y
    simp_all [F, F', blockAverage_simClassOf, ite_and, ← mul_sum, mul_simClassOf,
      finsum_eq_sum_of_fintype, sum_moebius_simClassOf_endOnSub]
  -- So it suffices that `B` agrees at a block triangular map and at `b ⊕ a` whenever `moebius` does
  -- not vanish at the former.
  have h_mu_ab : moebius a * moebius b = moebius.blockAverage a b := by simp [delta_eq]
  rw [h_mu_ab, blockAverage, blockAverage, mul_comm, ← finMean_const_mul]
  congr! 2 with x
  simp only [mul_eq_mul_right_iff, or_iff_not_imp_right]
  intro h_ne
  -- Then that map, say `g`, is semisimple, so the second factor has a stable complement `C`.
  have h_inv_prod : (⊥ : Submodule k (Fin b.out.fst → k)).prod ⊤ ∈
      invtSubmodule (blockTriangularEnd a.out.snd b.out.snd x) := fun v ↦ by aesop
  obtain ⟨C, C_inv, hC⟩ : ∃ C : Submodule k ((Fin b.out.fst → k) × (Fin a.out.fst → k)),
      C ∈ invtSubmodule (blockTriangularEnd a.out.snd b.out.snd x) ∧
        IsCompl ((⊥ : Submodule k (Fin b.out.fst → k)).prod ⊤) C :=
    isSemisimple_iff.mp (isSemisimple_of_moebius_ne_zero h_ne) _ h_inv_prod
  -- As `C` is stable, the projection `p` onto `⊥ × ⊤` along `C` satisfies `p ∘ g ∘ p = p ∘ g`.
  have proj_comm :
      projection _ C hC ∘ₗ blockTriangularEnd a.out.snd b.out.snd x ∘ₗ projection _ C hC =
      projection _ C hC ∘ₗ blockTriangularEnd a.out.snd b.out.snd x :=
    (isIdempotentElem_projection hC).ker_mem_invtSubmodule_iff.mp (by simpa using C_inv)
  have proj_mem : ∀ v, projection _ C hC v ∈ (⊥ : Submodule k (Fin b.out.fst → k)).prod ⊤ :=
    projection_apply_mem hC
  -- The first coordinate, paired with the projection `p`, conjugates `g` to `b ⊕ a`.
  refine congrArg B (simClassOf_eq_of_equiv
    (.ofInjectiveEndo (.prod (fst k (Fin b.out.fst → k) (Fin a.out.fst → k))
      (snd k (Fin b.out.fst → k) (Fin a.out.fst → k) ∘ₗ projection _ _ hC)) ?_) ?_)
  · -- the map is injective
    simp_all [injective_iff_map_eq_zero, Prod.ext_iff, mem_prod, DFunLike.ext_iff,
      projection_apply_of_mem_left]
  · -- and it conjugates the block triangular map to `b ⊕ a`; `↓`: membership in `⊥.prod ⊤` has
    -- to be split before the other lemmas act
    simp_all [Prod.ext_iff, ↓mem_prod, DFunLike.ext_iff, projection_apply_of_mem_left]

/-- `μ` takes real values: each value is its own complex conjugate. -/
@[simp]
lemma conj_moebius : ∀ c : SimClass k, conj (moebius c) = moebius c := by
  -- The values of `constOne` and `1` are real, so `conj moebius` is an inverse of `constOne` as
  -- well.
  let μ' : Hall k := fun c ↦ conj (moebius c)
  have h_inv : μ' * constOne = moebius * constOne := ext fun _ y ↦ by
    simp [μ', ← map_sum, mul_simClassOf, finsum_eq_sum_of_fintype, sum_moebius_simClassOf_endOnSub]
  exact congrFun (isUnit_constOne.mul_right_cancel h_inv)

/-! ### The cuspidal function attached to `η` -/

/-- The induction product of `New.Hall.greenCuspidal k η` with the constant function
`New.Hall.constOne` is minus the eigenvalue sum `New.Hall.brauerLift k η`. -/
@[simp]
lemma greenCuspidal_mul_constOne : greenCuspidal k η * constOne = -brauerLift k η := by
  -- It suffices that `greenCuspidal k η = -(moebius * brauerLift k η)`; multiply by `constOne`.
  suffices key : greenCuspidal k η + moebius * brauerLift k η = 0 by grind [moebius_mul_constOne]
  ext _ g
  -- `β = brauerLift k η` is additive, `β (g|W) + β (g|V/W) = β g`, so the two sums over stable `W`
  -- add up to `β g * ∑ W, moebius (g|W) = β g * 1 g`, which is `0` (in dimension `0` since
  -- `β g = 0`).
  calc
    _ = brauerLift k η (simClassOf g) *
        ∑ W : StableSubspace g, moebius (simClassOf W.endOnSub) := by
      -- termwise: `β (g|W) μ (g|W) + μ (g|W) β (g|V/W) = β g μ (g|W)`
      suffices h_terms : ∀ W : StableSubspace g,
          (brauerLift k η).mulMoebius (simClassOf W.endOnSub) +
              moebius (simClassOf W.endOnSub) * ((W.endOnQuot.charpoly.aroots K).map η).sum =
            (((charpoly g).aroots K).map η).sum * moebius (simClassOf W.endOnSub) by
        simpa [← sum_add_distrib, mul_sum, greenCuspidal, mul_simClassOf,
          finsum_eq_sum_of_fintype] using sum_congr rfl fun W _ ↦ h_terms W
      intro W
      simp [← charpoly_endOnSub_mul_endOnQuot _ W, field, charpoly_monic, Monic.ne_zero, aroots_mul]
    _ = 0 := by simp +contextual [← g.charpoly_natDegree, sum_moebius_simClassOf_endOnSub,
      charpoly_monic]

/-- The value of `New.Hall.greenCuspidal k η` in dimension zero is zero. -/
lemma greenCuspidal_eq_zero_of_dim_lt_one (c : SimClass k) :
    c.dim < 1 → greenCuspidal k η c = 0 := by
      simp_all [eq_simClassOf_zero_of_dim_eq_zero, greenCuspidal]

/-- `New.Hall.greenCuspidal k η` is cuspidal: its block averages vanish when both blocks have
positive size. -/
lemma isCuspidal_greenCuspidal : (greenCuspidal k η).IsCuspidal := by
  intro a b ha hb
  -- Write `δ = blockAverage`, `β = brauerLift k η`. By the Mackey formula `blockAverage_mul`,
  -- `δ C_η = δ (β moebius) * δ 𝟙`, a sum over stable subspaces of `a` and of `b`.
  rw [← simClassOf_out a, ← simClassOf_out b, greenCuspidal, blockAverage_mul]
  -- By `blockAverage_mulMoebius` and additivity of `β`,
  -- `δ (β moebius) = β moebius ⊗ moebius + moebius ⊗ β moebius`. Each of the two parts has a factor
  -- `∑ W, moebius (c|W) = 1 c` with `c = a` or `c = b`, which is `0` as `c.dim ≠ 0`.
  -- `-simClassOf_out`: otherwise `simp` undoes the first rewrite, which wrote `a`, `b` as classes
  simp_all [blockAverage, -simClassOf_out, charpoly_prodMap, mul_add, ← mul_sum, ← sum_mul,
    mul_assoc, mul_simClassOf, finsum_eq_sum_of_fintype, charpoly_monic, Monic.ne_zero,
    aroots_mul, sum_add_distrib, sum_moebius_simClassOf_endOnSub]

end New.Hall

namespace New

/-!
## Supports of cuspidal class functions

Idea: the Fitting decomposition for an irreducible factor of the characteristic polynomial makes all
block triangular maps with the two given diagonal blocks similar.
-/

section CuspidalSupport

open Polynomial Hall LinearMap Module Multiset Submodule StableSubspace

variable {k K V : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
  (η η' : K → ℂ) [AddCommGroup V] [Module k V] [Module.Finite k V] {g : End k V}

omit [Finite k] in
/-- If `P(g)` is nilpotent, with `P` monic irreducible, the characteristic polynomial of `g` is a
power of `P`. -/
lemma charpoly_eq_pow_of_isNilpotent {P : k[X]} (hP_irred : Irreducible P) (hP_monic : Monic P)
    (h_nilp : IsNilpotent (aeval g P)) :
    charpoly g = P ^ (finrank k V / P.natDegree) := by
  -- `charpoly g` divides `(charpoly P(g)).comp P`, and `charpoly P(g) = X ^ finrank k V`
  have h_dvd : charpoly g ∣ P ^ finrank k V := by
    -- `↓`: `aeval_algHom_apply` has to act before `toMatrixAlgEquiv` is unfolded
    simpa [↓aeval_algHom_apply, toMatrixAlgEquiv, h_nilp.charpoly_eq_X_pow_finrank] using
      charpoly_dvd_charpoly_aeval_comp (Y := g.toMatrixAlgEquiv (finBasis k V)) P
  -- a monic divisor of a power of the prime `P` is a power of `P`; compare degrees
  obtain ⟨j, -, hj⟩ : ∃ j ≤ finrank k V, Associated (charpoly g) (P ^ j) :=
    (dvd_prime_pow hP_irred.prime _).mp h_dvd
  have h_eq : charpoly g = P ^ j :=
    eq_of_monic_of_associated (charpoly_monic g) (hP_monic.pow j) hj
  have h_deg : finrank k V = j * P.natDegree := by
    rw [← charpoly_natDegree g, h_eq, natDegree_pow]
  rw [h_eq, h_deg, Nat.mul_div_cancel _ hP_irred.natDegree_pos]

/-- Let `F` be a cuspidal element of `Hall k`, the complex-valued functions on similarity classes of
endomorphisms of finite-dimensional `k`-spaces. Cuspidal means that the average of `F` over block
triangular endomorphisms with diagonal blocks `a`, `b` vanishes whenever both blocks have nonzero
dimension. If `F` does not vanish at the similarity class of `g`, then the characteristic polynomial
of `g` is `P ^ j` for some irreducible `P ∈ k[X]` and some `j`. -/
lemma Hall.IsCuspidal.exists_charpoly_eq_pow {F : Hall k} (h_cusp : IsCuspidal F)
    (hF_ne : F (simClassOf g) ≠ 0) :
    ∃ (P : k[X]) (j : ℕ), Irreducible P ∧ charpoly g = P ^ j := by
  -- Let `P` be an irreducible factor of the characteristic polynomial of `g`, and `C` the Fitting
  -- component `ker P(g) ^ N`. Every block triangular map with diagonal blocks `g|C`, `g|V/C` is
  -- conjugate to `g`. As `F` is cuspidal, `F g ≠ 0` forces a block to be empty; it is not `C`,
  -- since `P(g)` is not invertible, so `P(g) ^ N = 0`.
  by_cases h_unit : IsUnit (charpoly g)
  · -- a monic unit is `1 = X ^ 0`
    exact ⟨X, 0, irreducible_X, g.charpoly_monic.eq_one_of_isUnit h_unit⟩
  obtain ⟨P, hP_monic, hP_irred, hdvd⟩ : ∃ P : k[X], P.Monic ∧ Irreducible P ∧
      P ∣ (g.toMatrixAlgEquiv (Free.chooseBasis k V)).charpoly :=
    (g.toMatrixAlgEquiv _).charpoly.exists_monic_irreducible_factor h_unit
  have not_unit : ¬IsUnit (aeval g P) := by
    simpa [aeval_algHom_apply] using fun h_inv ↦
      hP_irred.dvd_iff_not_isCoprime.mp hdvd (isUnit_aeval_iff_isCoprime.mp h_inv).symm
  obtain ⟨N, hN, hN₀⟩ : ∃ N : ℕ, IsCompl (aeval g P ^ N).ker (aeval g P ^ N).range ∧ N ≠ 0 :=
    ((aeval g P).eventually_isCompl_ker_pow_range_pow.and (Filter.eventually_ne_atTop 0)).exists
  have comm (Y : End k V) (hY : ∀ x : V, Y (g x) = g (Y x)) (x : V) :
      Y ((aeval g P ^ N) x) = (aeval g P ^ N) (Y x) :=
    -- `Y` commutes with `g`, hence with the polynomial `P(g) ^ N` in `g`
    LinearMap.congr_fun ((Algebra.commute_of_mem_adjoin_singleton_of_commute
      (aeval_mem_adjoin_singleton k g) (LinearMap.ext hY : Commute Y g)).pow_right N).eq x
  have ker_stable : ∀ x ∈ ker (aeval g P ^ N), g x ∈ ker (aeval g P ^ N) := by
    simp +contextual [← comm g]
  let C : StableSubspace g := ⟨ker (aeval g P ^ N), ker_stable⟩
  -- The Sylvester map `y ↦ a y - y b` (`a = g|C`, `b = g|V/C`) is injective: an intertwiner `y`
  -- commutes with `P(g) ^ N` and takes values in its kernel `C`, so it kills the range of
  -- `P(g) ^ N`, a complement of `C`.
  let sylvester : End k ((_ ⧸ C.val) →ₗ[k] C.val) :=
    C.endOnSub.compRight k - lcomp k _ C.endOnQuot
  have sylvester_inj : Function.Injective sylvester := by
    refine (injective_iff_map_eq_zero _).mpr fun y hy ↦
      linearMap_qext _
        (ext_on_codisjoint hN.codisjoint ((ker_mkQ _).ge.trans (ker_le_ker_comp _ y)) ?_)
    rintro _ ⟨v, rfl⟩
    have intertwines (x : V) : ((y ⟦g x⟧ : C.val) : V) = g (y ⟦x⟧) := by
      have h_at_x : (C.endOnSub.compRight k) y ⟦x⟧ = (lcomp k C.val C.endOnQuot) y ⟦x⟧ :=
        LinearMap.congr_fun (sub_eq_zero.mp hy) ⟦x⟧
      exact (congrArg Subtype.val h_at_x).symm
    exact Subtype.ext ((comm (C.val.subtype ∘ₗ y ∘ₗ mkQ _) intertwines v).trans (y _).prop)
  -- So it is surjective, and a solution `y` of `a y - y b = x` conjugates
  -- `blockTriangularEnd a b x` into `g`.
  have cls_blk (x : (V ⧸ C.val) →ₗ[k] C.val) :
      simClassOf (blockTriangularEnd C.endOnSub C.endOnQuot x) = simClassOf g := by
    obtain ⟨y, rfl⟩ : ∃ y : (V ⧸ C.val) →ₗ[k] C.val, sylvester y = x :=
      surjective_of_injective sylvester_inj x
    refine simClassOf_eq_of_equiv
      (.skewProd (quotKerEquivRange _) 1 y ≪≫ₗ prodEquivOfIsCompl _ _ hN.symm) ?_
    suffices h_eq : ∀ v c : V, (aeval g P ^ N) c = 0 →
        (aeval g P ^ N) (g v) + (g (y (Submodule.Quotient.mk v) : V) -
            (y (Submodule.Quotient.mk (g v)) : V) + g c + (y (Submodule.Quotient.mk (g v)) : V)) =
          g ((aeval g P ^ N) v) + (g c + g (y (Submodule.Quotient.mk v) : V)) by
      simpa [Submodule.Quotient.forall, sylvester, endOnSub, endOnQuot, C] using h_eq
    intro v c _
    -- `P(g) ^ N` commutes with `g`
    rw [comm g (fun _ ↦ rfl) v]
    abel
  -- The block average of `F` at `(a, b)` is thus `F g ≠ 0`, so `C = ⊥` (excluded by `not_unit`,
  -- as `N ≠ 0`) or `C = ⊤`.
  have nilp : aeval g P ^ N = 0 := by
    -- `↓`: `finrank_eq_zero` has to act before the dimension facts are simplified further
    simpa [C, cls_blk, hF_ne, not_unit, hN₀, blockAverage_simClassOf, ← isUnit_iff_ker_eq_bot,
      finrank_zero_iff, ↓finrank_eq_zero] using
      h_cusp (simClassOf C.endOnSub) (simClassOf C.endOnQuot)
  exact ⟨P, _, hP_irred, charpoly_eq_pow_of_isNilpotent hP_irred hP_monic ⟨N, nilp⟩⟩

/-- Let k be a finite field, `q = |k|`, `d = finrank k V`, and let `greenCuspidal k η` be the class
function (β_η·μ) ∗ 𝟙, where β_η is the eigenvalue sum of η, μ is the inverse of the constant
function 𝟙 for the parabolic-induction product ∗, and β_η·μ is pointwise. Suppose `η'` is `a` times
`η` at every `z` in `K` with `z ^ q ^ d = z` whose Frobenius orbit `z, z ^ q, …, z ^ q ^ (d - 1)`
lists the eigenvalues of `g` in `K`. Then the value of `greenCuspidal` at the class of `g` for `η'`
is `a` times the value for `η`. -/
lemma greenCuspidal_simClassOf_eq_mul {a : ℂ}
    (h_scale : ∀ z : K,
      g.charpoly.aroots K =
        Multiset.map (fun i : ℕ ↦ z ^ Nat.card k ^ i) (Multiset.range (finrank k V)) →
      z ^ Nat.card k ^ finrank k V = z → a * η z = η' z) :
    greenCuspidal k η' (simClassOf g) = a * greenCuspidal k η (simClassOf g) := by
  -- If the two sides differ, some `greenCuspidal k θ (simClassOf g)` is nonzero. Then `charpoly g`
  -- is a power of an irreducible `P`, and every eigenvalue of `g` satisfies `h_scale`.
  by_cases! h_zero : ∀ θ : K → ℂ, greenCuspidal k θ (simClassOf g) = 0
  · simp [h_zero]
  obtain ⟨θ, hθ⟩ : ∃ θ : K → ℂ, greenCuspidal k θ (simClassOf g) ≠ 0 := h_zero
  obtain ⟨P, j, hP, hg⟩ : ∃ (P : k[X]) (j : ℕ), Irreducible P ∧ charpoly g = P ^ j :=
    (isCuspidal_greenCuspidal θ).exists_charpoly_eq_pow hθ
  -- By `aroots_pow_eq_frobenius_orbit`, the roots of `P ^ j` are the Frobenius orbit of any one
  -- root `z`.
  have h_root (z : K) (hz : aeval z g.charpoly = 0) : a * η z = η' z := by
    grind [aroots_pow_eq_frobenius_orbit, pow_ne_zero, charpoly_natDegree]
  -- `greenCuspidal k η` reads `η` only at eigenvalues of restrictions to stable subspaces `W`.
  have h_terms (W : StableSubspace g) (z : K) (hz : z ∈ (charpoly W.endOnSub).aroots K) :
      η' z = a * η z := by
    -- `z` is a root of `charpoly (g|W)`, a factor of `charpoly g`
    obtain ⟨-, hz_root⟩ : charpoly W.endOnSub ≠ 0 ∧ aeval z (charpoly W.endOnSub) = 0 :=
      mem_aroots.mp hz
    refine (h_root z ?_).symm
    rw [← charpoly_endOnSub_mul_endOnQuot _ W, map_mul, hz_root, zero_mul]
  suffices h_sum_eq : ∑ W : StableSubspace g,
      (Multiset.map (fun x ↦ η' x) ((charpoly W.endOnSub).aroots K)).sum *
        moebius (simClassOf W.endOnSub) =
      ∑ W : StableSubspace g,
        (Multiset.map (fun x ↦ a * η x) ((charpoly W.endOnSub).aroots K)).sum *
          moebius (simClassOf W.endOnSub) by
    simpa [greenCuspidal, mul_simClassOf, mulMoebius, Finset.mul_sum, ← mul_assoc,
      ← sum_map_mul_left, finsum_eq_sum_of_fintype] using h_sum_eq
  refine Finset.sum_congr rfl fun W _ ↦ ?_
  rw [Multiset.map_congr rfl (h_terms W)]

end CuspidalSupport

/-!
## Values of μ and C_η at multiplication by a field generator

Let z generate a finite extension F = k[z] of k; class functions are evaluated at multiplication by
z.
-/

section CuspidalAtScalars

open Module Matrix Finset Hall Polynomial Fintype Algebra minpoly Lagrange Submodule StableSubspace
  GeneralLinearGroup

attribute [local instance low] Fintype.ofFinite

variable {k K F V : Type*} [Field k] [Finite k] [Field K] [Algebra k K] [Field F] [Finite F]
  [Algebra k F]
  (z : PowerBasis k F) [AddCommGroup V] [Module k V] [Module F V] [IsScalarTower k F V]
  [Module.Finite k V] [Module.Finite F V]

/-- The order of GL_n(k), for a finite field k with q elements, is the product of q^i (q^{i+1} − 1)
over 0 ≤ i < n, as an identity in any field. -/
lemma card_GL_eq_prod {n R : Type*} [Fintype n] [DecidableEq n] [Field R] :
    Nat.card (GL n k) =
      ∏ i ∈ range (Fintype.card n), (Nat.card k ^ i * (Nat.card k ^ (i + 1) - 1) : R) := by
  -- Mathlib gives `∏ i, (q ^ n - q ^ i)`; regroup the factors by induction on `d`.
  suffices h_prod : ∀ d : ℕ,
      ∏ i : Fin d, ((Fintype.card k : R) ^ d - (Fintype.card k : R) ^ (i : ℕ)) =
      (∏ i ∈ range d, (Fintype.card k : R) ^ i) *
        ∏ i ∈ range d, ((Fintype.card k : R) ^ (i + 1) - 1) by
    have h_card : Nat.card (GL n k) = Nat.card (GL (Fin (card n)) k) :=
      Nat.card_congr (Units.mapEquiv (reindexRingEquiv k (equivFin n)).toMulEquiv).toEquiv
    rw [h_card, card_GL_field]
    simpa [Nat.pow_le_pow_right card_pos, prod_mul_distrib] using h_prod (card n)
  intro d
  induction d with
  | zero => rw [Fin.prod_univ_zero, prod_range_zero, prod_range_zero, one_mul]
  | succ m ih =>
    simp_all [Fin.prod_univ_succ, prod_range_succ, pow_succ, ← sub_mul, prod_mul_distrib]
    ring

open Classical in
/-- Let `g` be an endomorphism of a finite space `V` and `U ≠ V` a `g`-stable subspace. The sum of
μ at the classes of `g` on `V/W`, over the `g`-stable subspaces `W ⊇ U`, is `0`. -/
private lemma sum_moebius_endOnQuot_eq_zero_of_ne_top [Finite V] {g : Module.End k V}
    (U : StableSubspace g) (hU : (U : Submodule k V) ≠ ⊤) :
    ∑ W : StableSubspace g with (U : Submodule k V) ≤ W.1,
      moebius (simClassOf W.endOnQuot) = 0 := by
  -- The stable subspaces above `U` are those of `V/U`, so this sum is
  -- `(constOne * moebius)(V/U) = 0`.
  have h_mkQ_comm (x : V) :
      (U : Submodule k V).mkQ (g x) = U.endOnQuot ((U : Submodule k V).mkQ x) := rfl
  have h_quo : ∑ W : StableSubspace g with (U : Submodule k V).mkQ.ker ≤ W.1,
      moebius (simClassOf W.endOnQuot) =
        (constOne * moebius : Hall k) (simClassOf U.endOnQuot) := by
    refine (sum_comap (U : Submodule k V).mkQ (g' := U.endOnQuot) h_mkQ_comm _).trans ?_
    simp [mul_simClassOf, finsum_eq_sum_of_fintype]
  rw [mul_comm constOne, moebius_mul_constOne] at h_quo
  simpa [hU, finrank_zero_iff] using h_quo

/-- Let `F = k[z]` be a finite field extension of the finite field `k`, given by a power basis `z`,
and let `Q` be the number of elements of `F`. Let `V` be an `F`-space of dimension `d`, let
`N = ∏_{0≤i<d} (X − Q^i)`, and let `g` be multiplication by `z` on `V`, viewed as a `k`-linear
endomorphism. Then `moebius` (the inverse μ of the constant function 𝟙 under the induction product
on functions of similarity classes) takes the value `N(0)` at the class of `g`, and
`greenCuspidal k η` (the class function `C_η = (β_η·μ) ∗ 𝟙`) takes the value `−N′(1)` times the sum
of `η` over the roots in `K` of the minimal polynomial of `z`. -/
lemma moebius_and_greenCuspidal_lsmul (η : K → ℂ) :
    let N : ℂ[X] := nodal (range (finrank F V)) fun i : ℕ ↦ ((Nat.card F ^ i : ℕ) : ℂ)
    let g : Module.End k V := lsmul k k V z.gen
    moebius (simClassOf g) = N.eval 0 ∧
    greenCuspidal k η (simClassOf g) =
      -(((minpoly k z.gen).aroots K).map η).sum * N.derivative.eval 1 := by
  classical
  -- With `m = finrank F V`, `Q = |F|`: the polynomial `M = ∑_W μ(V/W) X ^ dim W` is monic of degree
  -- `m` and vanishes at `Q ^ j`, `j < m`, so `M = N`; both values are read off from `M`.
  intro N g
  have h_finite_V : Finite V := finite_of_finite k
  -- As `z.gen` generates `F`, a `g`-stable `k`-subspace is an `F`-subspace.
  let S (W : StableSubspace g) : Submodule F V :=
    { toAddSubmonoid := (W : Submodule k V).toAddSubmonoid
      smul_mem' := fun c x hx ↦ by
        obtain ⟨p, rfl⟩ : ∃ p : k[X], c = aeval z.gen p := z.exists_eq_aeval' c
        exact aeval_apply_smul_mem_of_le_comap' hx _ _ W.property }
  let M : ℂ[X] := ∑ W, monomial (finrank F (S W)) (moebius (simClassOf W.endOnQuot))
  -- `M` and `N` agree in degrees `≥ m`: there only `W = ⊤` contributes to `M`, giving `X ^ m`.
  have h_coeff (n : ℕ) (hn : finrank F V ≤ n) : (N - M).coeff n = 0 := by
    let W_top : StableSubspace g := ⟨⊤, fun _ _ ↦ Submodule.mem_top⟩
    have hS_top : S W_top = ⊤ := Submodule.ext fun _ ↦ by simp [S, W_top]
    have hN_monic : N.IsMonicOfDegree (finrank F V) := ⟨by simp [N], nodal_monic⟩
    rw [coeff_sub, ← (isMonicOfDegree_monomial_one _).coeff_eq hN_monic hn, finsetSum_coeff,
      Fintype.sum_eq_single W_top, hS_top, finrank_top]
    · simp [coeff_monomial, finrank_zero_iff, W_top]
    · intro W hW
      have h_lt : finrank F (S W) < finrank F V :=
        (S W).finrank_lt fun h ↦ hW (Subtype.ext (top_unique h.ge))
      rw [coeff_monomial, ite_eq_right (h_lt.trans_le hn).ne]
  -- `|W| ^ j` counts the `j`-tuples `v` in `W`; for `j < m` no `v` spans `V`.
  have h_root (j : ℕ) (hj : j < finrank F V) : M.eval ((Nat.card F ^ j : ℕ) : ℂ) = 0 := by
    have h_count (W : StableSubspace g) : ((Nat.card F ^ j : ℕ) : ℂ) ^ finrank F (S W) =
        ∑ v : Fin j → V, if span F (.range v) ≤ S W then 1 else 0 := by
      rw [← Nat.cast_pow, pow_right_comm, ← natCard_eq_pow_finrank]
      simp_rw [Nat.card_eq_fintype_card, Nat.cast_pow, Fintype.card_subtype, ← sum_boole,
        Fintype.sum_pow, Fintype.prod_boole, span_le, Set.range_subset_iff, SetLike.mem_coe]
      congr!
    simp_rw [M, eval_finsetSum, eval_monomial, h_count, mul_sum]
    rw [sum_comm]
    refine Finset.sum_eq_zero fun v _ ↦ ?_
    -- The span `U` of `v` is a stable subspace other than `V`, as `j < m`.
    let U : StableSubspace g := ⟨(span F (.range v)).restrictScalars k, by aesop⟩
    have hU_ne : (U : Submodule k V) ≠ ⊤ := by simp [U, mt finrank_le_of_span_eq_top, hj]
    have h_le_iff (W : StableSubspace g) :
        span F (.range v) ≤ S W ↔ (U : Submodule k V) ≤ W := Iff.rfl
    simpa [sum_filter, h_le_iff] using sum_moebius_endOnQuot_eq_zero_of_ne_top U hU_ne
  -- `N - M` has degree `< m` and vanishes at the `m` distinct points `Q ^ j`.
  have h_deg : (N - M).degree < #(range (finrank F V)) := by
    simpa [Finset.card_range, degree_lt_iff_coeff_zero] using h_coeff
  have hN : N = M :=
    eq_of_degree_sub_lt_of_eval_index_eq _
      (Nat.cast_injective.comp (Nat.pow_right_injective Finite.one_lt_card)).injOn h_deg
      fun j hj ↦ (eval_nodal_at_node hj).trans (h_root j (mem_range.mp hj)).symm
  rw [hN]
  constructor
  · -- In `moebius = 1 * moebius` and in `M(0)` only `W = ⊥` contributes.
    have hS_subsingleton (W : StableSubspace g) :
        Subsingleton (S W) ↔ Subsingleton (W : Submodule k V) := Iff.rfl
    rw [← one_mul moebius]
    simp [M, zero_pow_eq, finrank_zero_iff, mul_simClassOf, finsum_eq_sum_of_fintype,
      eval_finsetSum, hS_subsingleton]
  · -- On `W` the characteristic polynomial is the `dim W`-th power of the minimal polynomial.
    have h_brauer (W : StableSubspace g) : brauerLift k η (simClassOf W.endOnSub) =
        finrank F (S W) * (((minpoly k z.gen).aroots K).map η).sum := by
      change brauerLift k η (simClassOf (lsmul k k (S W) z.gen)) = _
      simp [z.finrank, ← finrank_mul_finrank k F, z.dim_pos.ne', monic z.isIntegral_gen,
        charpoly_eq_pow_of_isNilpotent (irreducible z.isIntegral_gen), Multiset.map_nsmul,
        Multiset.sum_nsmul]
    -- `moebius` is inverse to `constOne`; expand the product over `W` and compare with `M'(1)`.
    have h_cusp : greenCuspidal k η = -brauerLift k η * moebius := by
      grind [moebius_mul_constOne, greenCuspidal_mul_constOne η]
    -- `h_brauer` is applied before `simp` unfolds `brauerLift` (hence `↓`).
    simp [M, h_cusp, ↓h_brauer, derivative_monomial, mul_sum, mul_simClassOf,
      finsum_eq_sum_of_fintype, eval_finsetSum]
    -- The two sums agree term by term up to the order of the factors.
    ac_rfl

/-- Let F = k[z] have Q elements and let V be an F-space of dimension d. At multiplication by z
on V, μ = 𝟙⁻¹ takes the value N(0), where N = ∏_{0≤i<d} (X − Q^i). -/
lemma moebius_simClassOf_lsmul :
    moebius (simClassOf (lsmul k k V z.gen)) =
      (nodal (range (finrank F V)) fun i : ℕ ↦ ((Nat.card F ^ i : ℕ) : ℂ)).eval 0 :=
  (moebius_and_greenCuspidal_lsmul (K := k) z fun _ : k ↦ (0 : ℂ)).1

/-- Let F = k[z] have Q elements and let V be an F-space of dimension d. At multiplication by z
on V, C_η takes the value −N′(1) times the sum of η over the roots in K of the minimal polynomial
of z, where N = ∏_{0≤i<d} (X − Q^i). -/
private lemma greenCuspidal_simClassOf_lsmul (η : K → ℂ) :
    greenCuspidal k η (simClassOf (lsmul k k V z.gen)) =
      -(((minpoly k z.gen).aroots K).map η).sum *
        (nodal (range (finrank F V)) fun i : ℕ ↦ ((Nat.card F ^ i : ℕ) : ℂ)).derivative.eval 1 :=
  (moebius_and_greenCuspidal_lsmul z η).2

/-- Let k be a finite field, μ (`moebius`) the inverse of the constant class function 𝟙 for the
parabolic-induction product ∗, and C_η = `greenCuspidal k η` = (β_η·μ) ∗ 𝟙 for η : K → ℂ, where β_η
is the eigenvalue sum of η. Let F = k[z] and V a non-zero finite-dimensional F-space. Then the value
of the pointwise product C_η·μ at multiplication by z on V, times #V - 1, is the sum of η over the
roots in K of the minimal polynomial of z, times the order of the centraliser of z in GL_k(V). -/
lemma mulMoebius_greenCuspidal_lsmul (η : K → ℂ) [Nontrivial V] :
    (greenCuspidal k η).mulMoebius (simClassOf (lsmul k k V z.gen)) * (Nat.card V - 1 : ℕ) =
      (((minpoly k z.gen).aroots K).map η).sum *
        Nat.card {e : V ≃ₗ[k] V // ∀ x : V, e (z.gen • x) = z.gen • e x} := by
  -- As `z.gen` generates `F`, the `k`-automorphisms of `V` that commute with it are `F`-linear.
  have h_F_linear (f : V ≃ₗ[k] V) (hf : ∀ x : V, f (z.gen • x) = z.gen • f x) (c : F) :
      ∀ x : V, f (c • x) = c • f x := by
    induction eq_top_iff.mp z.adjoin_gen_eq_top c using adjoin_induction with
    | mem a ha => rwa [Set.mem_singleton_iff.mp ha]
    | algebraMap r => simp
    | add a b _ _ ha hb => simp [add_smul, ha, hb]
    | mul a b _ _ ha hb => simp [mul_smul, ha, hb]
  -- The `F`-linear automorphisms of `V` are the `k`-linear ones that commute with `z.gen`.
  let restrictScalarsEquiv : LinearMap.GeneralLinearGroup F V ≃
      {e : V ≃ₗ[k] V // ∀ x, e (z.gen • x) = z.gen • e x} :=
    .mk (fun g ↦ ⟨g.toLinearEquiv.restrictScalars k, by simp⟩) fun ⟨f, hf⟩ ↦
      .ofLinearEquiv { f with map_smul' := h_F_linear f hf }
  have h_card : Nat.card (GL (Fin (finrank F V)) F) =
      Nat.card {e : V ≃ₗ[k] V // ∀ x, e (z.gen • x) = z.gen • e x} :=
    Nat.card_congr ((toLin' (finBasis F V)).toEquiv.trans restrictScalarsEquiv)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, finrank F V = m + 1 := Nat.exists_eq_add_one.mpr finrank_pos
  -- With `N = (∏_{i<m} (X - Q ^ (i + 1))) (X - 1)`, `moebius_simClassOf_lsmul` and
  -- `greenCuspidal_simClassOf_lsmul` give the left side through `N'(1) = ∏_{i<m} (1 - Q ^ (i + 1))`
  -- and `N(0) = ∏_{i≤m} (-Q ^ i)`; compare with `card_GL_eq_prod`.
  simp_rw [mulMoebius, moebius_simClassOf_lsmul z, greenCuspidal_simClassOf_lsmul z η]
  rw [natCard_eq_pow_finrank (K := F) (V := V), eq_comm, ← h_card, card_GL_eq_prod, hm, nodal,
    prod_range_succ']
  -- With `s` the sum of `η` over the roots and `Q = |F|`, both sides are the following product.
  have h_regroup (s Q : ℂ) : s * ((-1) ^ m * ((∏ x ∈ range m, Q ^ x) * Q ^ m *
        ((∏ x ∈ range m, (1 - Q ^ x * Q)) * (1 - Q ^ m * Q)))) =
      (s * ∏ x ∈ range m, (1 - Q ^ x * Q)) * ((-1) ^ m * ((∏ x ∈ range m, Q ^ x) * Q ^ m)) *
        (1 - Q ^ m * Q) := by
    ring
  -- Write every factor in the form `1 - Q ^ j`; the two exclusions keep `simp` from undoing this.
  simpa [eval_prod, pow_succ, prod_range_succ, ← neg_sub (1 : ℂ), -neg_sub,
    -Nat.card_eq_fintype_card, prod_neg, prod_mul_distrib] using h_regroup _ _

end CuspidalAtScalars

/-!
## The inner product of C_η with B·μ

Let L be a finite extension of the finite field k, and let φ be a k-embedding of L into a field K.
Let η be a function K → ℂ.
-/

section CuspidalInnerProduct

open Polynomial Finset Hall Module LinearMap minpoly IntermediateField
  GeneralLinearGroup IsGalois LinearEquiv FiniteField ComplexConjugate Fintype IsTorsionBySet

attribute [local instance low] Fintype.ofFinite

variable {k : Type*} [Field k] [Finite k] {K : Type*} [Field K] [Algebra k K] (η : K → ℂ)

omit [Finite k] in
/-- Let `L` be a finite field that is a `k`-algebra, and `g` a semisimple `k`-linear endomorphism of
`L` whose characteristic polynomial is a power `P ^ j` of an irreducible `P`. Then `g` is conjugate
to a multiplication: there are a `k`-linear automorphism `e` of `L` and `y ∈ L` with
`e ∘ (y * ·) ∘ e⁻¹ = g`. Both `g` and a root of `P` in `L` make `L` a vector space over `k[X]/(P)`,
of the same dimension. -/
lemma exists_conj_mulLeft_eq {L : Type*} [Field L] [Finite L] [Algebra k L] {g : End k L} {P : k[X]}
    {j : ℕ} (hg : g.IsSemisimple) (hP : Irreducible P) (h_charpoly : g.charpoly = P ^ j) :
    ∃ (e : L ≃ₗ[k] L) (y : L), e.conjAlgEquiv k (Algebra.lmul k L y) = g := by
  -- The minimal polynomial is squarefree and divides `P ^ j`, so `P` kills `g`.
  have h_minpoly_dvd : minpoly k g ∣ P :=
    hg.minpoly_squarefree.isRadical j P ((minpoly_dvd_charpoly g).trans h_charpoly.dvd)
  have h_aeval : Polynomial.aeval g P = 0 := dvd_iff.mp h_minpoly_dvd
  -- `V` is `L` as a `k[X]`-module through `g`, hence a vector space over the field `k[X]/(P)`.
  let V : Type _ := AEval' g
  have : Fact (Irreducible P) := ⟨hP⟩
  have : Module.Finite k (AdjoinRoot P) := (AdjoinRoot.powerBasis hP.ne_zero).finite
  have : Finite V := inferInstanceAs (Finite L)
  let module_V : Module (AdjoinRoot P) V :=
    IsTorsionBy.module fun x ↦ LinearMap.congr_fun h_aeval x
  have h_tower_V : IsScalarTower k (AdjoinRoot P) V := IsTorsionBySet.isScalarTower _
  have tower_V : finrank k (AdjoinRoot P) * finrank (AdjoinRoot P) V = finrank k L :=
    finrank_mul_finrank k (AdjoinRoot P) V
  -- So the degree of `P` divides that of `L`, and the finite field `k[X]/(P)` embeds in `L`.
  let algebra_L : Algebra (AdjoinRoot P) L :=
    (nonempty_algHom_of_finrank_dvd (L := L) ⟨_, tower_V.symm⟩).some.toAlgebra
  have tower_L : finrank k (AdjoinRoot P) * finrank (AdjoinRoot P) L = finrank k L :=
    finrank_mul_finrank k (AdjoinRoot P) L
  -- The two structures on `L` have the same dimension; `t` carries `g` to the product by the root.
  let t : V ≃ₗ[AdjoinRoot P] L :=
    ofFinrankEq _ _ (mul_left_cancel₀ finrank_pos.ne' (tower_V.trans tower_L.symm))
  refine ⟨t.symm.restrictScalars k, algebraMap _ L (AdjoinRoot.root P), ext fun x ↦ ?_⟩
  have root_smul (x : V) : t.symm (AdjoinRoot.root P • t x) = AdjoinRoot.root P • x :=
    t.symm_apply_eq.mpr (t.map_smul _ x).symm
  exact (root_smul x).trans (AEval'.X_smul_of g x)

/-- Let k be a finite field, K a field over k, η : K → ℂ, and C_η = `greenCuspidal k η` = (β_η·μ)
∗ 𝟙. Here β_η is the eigenvalue sum of η, μ (`moebius`) is the inverse of the constant class
function 𝟙 for the parabolic-induction product ∗, and B·μ is the pointwise product. For a finite
extension L of k with a k-embedding φ : L → K and any class function B, the average over
GL_{[L:k]}(k) of conj C_η times B·μ (`rankInner`) is the mean (`finMean`) over z ∈ L^× of conj η(φz)
times B at the class of multiplication by z on L. -/
lemma rankInner_greenCuspidal_mulMoebius {L : Type*} [Field L] [Finite L] [Algebra k L]
    (φ : L →ₐ[k] K) (B : Hall k) :
    rankInner (finrank k L) (greenCuspidal k η) B.mulMoebius =
      finMean fun z : Lˣ ↦ conj (η (φ z)) * B (simClassOf (mulLeft k z.val)) := by
  classical
  -- `ρ e z` is the conjugate by `e` of multiplication by `z`. The function
  -- `(greenCuspidal k η).mulMoebius` is induced from `η ∘ φ` (`induced`); the claim is then
  -- Frobenius reciprocity, `μ` being real.
  let ρ (e : L ≃ₗ[k] L) : L →ₐ[k] End k L := (e.conjAlgEquiv k).toAlgHom.comp (Algebra.lmul k L)
  let algebra_LK : Algebra L K := φ.toAlgebra
  have : Finite (L ≃ₗ[k] L) := DFunLike.finite (L ≃ₗ[k] L)
  have cls_conj (e : L ≃ₗ[k] L) (z : L) : simClassOf (ρ e z) = simClassOf (mulLeft k z) :=
    simClassOf_eq_of_equiv e.symm fun x ↦ by simp [ρ]
  have induced (g : End k L) : (greenCuspidal k η).mulMoebius (simClassOf g) =
      (∑ z, η (φ z) * Nat.card {e // ρ e z = g}) / Nat.card Lˣ := by
    rcases em' (∃ (a : L ≃ₗ[k] L) (y : L), ρ a y = g) with h_not_conj | ⟨a, y, rfl⟩
    · -- Off the conjugates of multiplications both sides vanish.
      suffices vanish : (greenCuspidal k η).mulMoebius (simClassOf g) = 0 by simp_all
      by_contra h_ne
      obtain ⟨hC, hμ⟩ : greenCuspidal k η (simClassOf g) ≠ 0 ∧ moebius (simClassOf g) ≠ 0 :=
        mul_ne_zero_iff.mp h_ne
      obtain ⟨P, j, hP, h_charpoly⟩ : ∃ (P : k[X]) (j : ℕ), Irreducible P ∧ charpoly g = P ^ j :=
        (isCuspidal_greenCuspidal η).exists_charpoly_eq_pow hC
      exact h_not_conj (exists_conj_mulLeft_eq (isSemisimple_of_moebius_ne_zero hμ) hP h_charpoly)
    -- At `ρ a y`, `mulMoebius_greenCuspidal_lsmul` for the field `k(y)` gives `#Lˣ` times the value
    -- as the sum of `η` over the roots of `minpoly k y` (simple, and in `L`) times the order of the
    -- centraliser of `y`; compare with the right side term by term.
    have h_card_ne : (Nat.card Lˣ : ℂ) ≠ 0 := by simp
    -- Multiplication by `y` on `L` is the action of the generator of the field `k⟮y⟯`.
    have h_mulLeft : mulLeft k y = Algebra.lsmul k k L (adjoin.powerBasis (integral k y)).gen := rfl
    have h_gen : (adjoin.powerBasis (integral k y)).gen = AdjoinSimple.gen k y := rfl
    rw [eq_div_iff h_card_ne, cls_conj, Nat.card_units, h_mulLeft,
      mulMoebius_greenCuspidal_lsmul (adjoin.powerBasis (integral k y)), h_gen, minpoly_gen,
      ← (splits _ y).map_aroots_algebraMap, Multiset.map_map,
      ← sum_mk _ (nodup_roots (.map (separable k y))), sum_mul]
    refine sum_subset_zero_on_sdiff le_top (fun z hz ↦ ?_) fun z hz ↦ ?_
    · -- If `z` is not a root of `minpoly k y`, no `ρ e z` is `ρ a y`.
      have h_aeval_ne (e : L ≃ₗ[k] L) :
          aeval (ρ e z) (minpoly k y) ≠ aeval (ρ a y) (minpoly k y) := by
        simp_all [aeval_algHom_apply, ne_zero_of_finite]
      have h_ne (e : L ≃ₗ[k] L) : ρ e z ≠ ρ a y :=
        ne_of_apply_ne (fun f ↦ aeval f (minpoly k y)) (h_aeval_ne e)
      simp [h_ne]
    · -- If `y = c z`, then `e ↦ a * e * c` maps the centraliser of `y` onto the `e` with
      -- `ρ e z = ρ a y`.
      obtain ⟨-, h_root⟩ : minpoly k y ≠ 0 ∧ aeval z (minpoly k y) = 0 := mem_aroots.mp hz
      obtain ⟨c, rfl⟩ : ∃ c : Gal(L/k), c z = y :=
        exists_algEquiv_of_root (IsAlgebraic.of_finite k _) h_root
      rw [Nat.card_congr ((Equiv.mulLeft a * .mulRight c).subtypeEquiv fun e ↦ ?_)]
      · rfl
      · rw [LinearMap.ext_iff]
        have h_comm_iff (v : L) :
            e (AdjoinSimple.gen k (c z) • v) = AdjoinSimple.gen k (c z) • e v ↔
              ρ ((Equiv.mulLeft a * Equiv.mulRight (c : L ≃ₗ[k] L)) e) z ((a * e) v) =
                ρ a (c z) ((a * e) v) := by
          simp [ρ, Algebra.smul_def, mul_eq_trans]
        exact (a * e).forall_congr h_comm_iff
  have unit_eq (e : L ≃ₗ[k] L) (z : Lˣ) (g : (End k L)ˣ) : ρ e z = g.val ↔ z.map (ρ e) = g :=
    .symm Units.ext_iff
  -- Write both sides as sums, drop `z = 0` (it gives no unit `g`) and sum over `g` first.
  refine star_injective ?_
  simp only [rankInner_eq_classInner_simClassOf, classInner, finMean]
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  simp [induced, cls_conj, unit_eq, sum_eq_add_sum_subtype_ne _ (0 : L), mul_left_comm, Ne.symm,
    mul_div, ← unitsEquivNeZero.sum_comp, Fintype.card_subtype, ← sum_boole, ← sum_comm_cycle,
    ← sum_div, mul_sum, field, card_congr (generalLinearEquiv k L).toEquiv, mul_comm _ (η _)]

/-- The characteristic of a finite field is prime. -/
instance : Fact (ringChar k).Prime := ⟨CharP.prime_ringChar k⟩

end CuspidalInnerProduct

end New
