import Lib.Cohomology.WoodsHole
import Lib.PadicComparison.CrystallineFrobenius
import Lib.PadicHodge.Limit.CrystallineLimit
import Lib.Shimura.CongruenceRelation.EichlerShimura
import Lib.Shimura.Transfer.Lefschetz

/-!
# Eigenquotients for Hecke eigensystems and the Galois representations they cut out

Let `ρ i` be finitely many finite-dimensional `ℚ_ℓ`-representations of `Γ`, with operators `T i s`
and scalars `θ s` in `ℚ̄_ℓ`. The eigenquotient is the largest quotient of `ℚ̄_ℓ ⊗ ⨁ V i` on which
each `T i s` acts by `θ s`. It is given in a basis by `r : Γ → GL_N(ℚ̄_ℓ)` and maps `F i`. If the
`ρ i` are crystalline, then it is crystalline, and a relation between `T` and Frobenius gives a
polynomial that kills Frobenius on it. Suppose moreover that the `T i s` commute with each other and
with `Γ`, and that `γ : ℚ̄_ℓ → ℂ_ℓ` agrees with `a ∈ Gal(ℚ̄_ℓ/ℚ_ℓ)`. If `u` is not a Hodge–Tate jump
of `r` at `γ`, then some polynomial in `T` that is `1` at the conjugate eigenvalues `a ∘ θ` kills
the vectors of weight `u`. These results are applied to the `ℓ`-adic cohomology of a
`New.Variety.Model` to obtain a Galois representation from a system `θ` of Hecke eigenvalues.

## Overview of this theory

Let `E` be a CM field strictly containing `K₀ = ℚ(√-d)`, with `d ≡ 3` mod 4. Let `v₀` be the base
infinite place of a CM type `Φ` of `E`, and let `𝔑` be a nonzero neat level in `𝓞_E`. A finite place
`w` of `E` over a place `u` of `K₀` is *safe* if `u` is split and prime to `d`, and `𝔑` is prime to
`w` and `ū`. The unitary similitude group, of rank `n ≥ 1`, has signature `(1, n - 1)` at `v₀` and
is definite at the other infinite places.

* `New.Variety.exists_model`: an integral model `Z` of Kuga–Sato type for this group, with level
  covers and the congruence relation at safe places. It lives over a localisation `R ⊆ E` of `𝓞_E`
  whose maximal ideals lie over primes good for the PEL data. The inputs are PEL data
  (`New.Variety.exists_pel`) and a family of abelian schemes over such `R`
  (`New.Variety.ThetaNull.nonempty_universalFamily`), for which no universal property is proved. If
  `E` contains a primitive root of unity of order `7! = 5040`, the PEL data exist for a suitable CM
  type and for every nonzero `𝔑` divisible by an integer `N ≠ 0`, which can be taken prime to any
  given finite set of places.
* `New.Variety.exists_isCoefficientSystem`: let `n` be odd, `κ` a weight, and `Φ` a CM type in which
  `Φ v₀` differs on `K₀` from every other `Φ v`. Take a Hecke eigenform of neat level on the
  definite side, with coefficients in an extension of the weight `κ` to `GL_n(E)` that the theorem
  supplies. At one split place it is of cuspidal type. At another split place it is spherical, and
  there the level is pro-`p` Iwahori, `p` being the residue characteristic of that place. Then its
  Hecke eigenvalues `θ` at safe places occur, in the sense of `New.Variety.OccursInWeight`, in
  weight `z + μ` for each jump `z` of `κ` at `Φ v₀`. The jumps are integers given by `New.jumps`.
  Here `μ ∈ ℕ` does not depend on the form or the level.
* `New.Variety.Model.exists_galois_rep`: let `ℓ` be a prime, `ιℓ : ℂ ≃ ℚ̄_ℓ`, and `θ` a system of
  Hecke eigenvalues at safe places. Let `R` be a localisation of `𝓞_E` at elements prime to the safe
  places. Take a model `Z` over `R` and weights `h ≥ 0` in which `θ` occurs. Then there is a
  continuous `ρ : Gal(Ē/E) → GL_m(ℚ̄_ℓ)` of undetermined dimension `m`; the proof cuts it out of the
  cohomology of `Z`. At safe places `ρ` is unramified or crystalline, and the Hecke polynomial of
  `ιℓ ∘ θ` kills geometric Frobenius. If the place over `ℓ` induced by `ιℓ` and the given embedding
  of `E` into `ℂ` is safe, the jumps (Hodge–Tate weights) of `ρ` at that embedding include the given
  weights. Other embeddings and multiplicities are not controlled.

This theory proves the cases that are used of PEL integral models (Kottwitz) and of the geometric
step in the Galois representations of cuspidal forms on `GL_n` (Shin). A direct comparison of two
finite counts replaces the description of automorphic forms on unitary groups via `GL_n` (Labesse).
No moduli functor is represented, nothing is transferred to `GL_n`, and no dimension is computed
here.

1. `ComplexTheta`, `AbelianScheme`, `ThetaGroup`, `Uniformisation`: theta functions and the complex
   uniformisation.
2. `GoodReduction`, `ThetaNormality`, `ArcExtension`: good reduction along a valuation ring of `ℂ`.
3. `ThetaModuli`, `Deformation`: the closure of the theta-null points of the PEL abelian varieties
   carries a family of abelian schemes and is smooth.
4. `HeckeTower` (the list of properties of a model), `CongruenceRelation`, `IntegralModel`: level
   covers, the congruence relation and the model.
5. `TraceFormula`, `Transfer`: the comparison with the definite unitary group. Last, `Eigenspace`:
   the Galois representation.

## Main definitions and results

* `New.Variety.IsEigenQuotient`, `New.Variety.exists_isEigenQuotient`: the definition; existence and
  continuity.
* `New.Variety.IsEigenQuotient.isCrystalline`: `r` is crystalline if the `ρ i` are.
* `New.Variety.IsEigenQuotient.isKilledBy`: a relation between `T` and Frobenius gives a polynomial
  that kills Frobenius on `r`.
* `New.Variety.IsEigenQuotient.exists_sum_baseChange_eq_zero_of_jump_eq_zero`: let the `ρ i` be
  crystalline and the `T i s` commute with each other and with `Γ`. If `u` is not a Hodge–Tate jump
  of `r` at an embedding `γ` given by `a ∈ Gal(ℚ̄_ℓ/ℚ_ℓ)`, some polynomial in `T` that is `1` at
  `a ∘ θ` kills the vectors of weight `u`.

Notions from other files:
* `New.Period.IsCrystalline`: T is crystalline: the elements of B⊗T fixed by all of Γ span B⊗T over
  B.
* `New.HasHodgeTateWeight`: The element y of C_p⊗T (over Z_p) has Hodge–Tate weight u:
  (j(g)⊗ρ(g))y = χ(j(g))^(−u)·y for all g in Γ, with χ the cyclotomic character.
* `New.Period.jump`: The multiplicity of the Hodge–Tate jump u at γ: the dimension over Q̄_p (zero
  if infinite) of the space `New.Period.hodgeTateMaps` of forms of weight u: γ-semilinear f :
  T → C_p with f(gx) = χ(g)^(−u)·g f(x) for g near 1.
* `New.Period.IsKilledBy`: The polynomial P over R kills (s, m): T is potentially crystalline and
  P(β_{s,m}) = 0 on B⊗T, the coefficients acting through T.
* `New.Period.linearFrob`: β_{s,m}: a chosen B-linear endomorphism of B⊗T agreeing with φ^m
  j(s) ⊗ ρ(s) on D_pcris(T), if one exists (arbitrary otherwise).

## Relation to the literature

Known result: Galois representation cut out of cohomology by a Hecke eigensystem, and the
Eichler-Shimura relation. Here the representation is a quotient of total cohomology rather than an
isotypic part. No dimension or semisimplicity is stated, only good reduction, annihilation by the
Hecke polynomial and the occurrence of given Hodge-Tate weights. Source: Deligne, Formes modulaires
et représentations l-adiques, Sém. Bourbaki 355 (1969), Thm 4.9; Harris and Taylor, The geometry and
cohomology of some simple Shimura varieties (2001), ch. VII; Wedhorn, Congruence relations on some
Shimura varieties, J. reine angew. Math. 524 (2000).
-/

/-!
## The largest quotient on which Hecke operators act by an eigensystem

In `New.Variety.IsEigenQuotient.isCrystalline`, `New.Variety.IsEigenQuotient.isKilledBy` and
`New.Variety.IsEigenQuotient.exists_sum_baseChange_eq_zero_of_jump_eq_zero`, the instance
`[OverGp Γ ℓ]` gives a map `toGp : Γ → Gal(ℚ̄_ℓ/ℚ_ℓ)` with open image. B denotes the period ring
`New.Period.Bmax`. In the notions glossed in the head, `T` is the module (`V i` or `ℚ̄_ℓ ^ N`), `j`
is `toGp`, and `(s, m)` is `(g, f)`.
-/

section EigenQuotient

namespace New.Variety

open Polynomial TensorProduct Period Submodule Module LinearMap IsScalarTower nonZeroDivisors
  ModuleCat.Algebra DFinsupp

variable {ℓ : ℕ} {Γ ι : Type*}
  {σ : Sort _} [ThePrime ℓ] [Group Γ] {V : ι → ModuleCat ℚ_[ℓ]}
  (ρ : ∀ i : ι, Representation ℚ_[ℓ] Γ (V i)) (T : ∀ i : ι, σ → End ℚ_[ℓ] (V i))
  (θ : σ → PadicAlgCl ℓ) {N : ℕ} (r : Γ →* GL (Fin N) (PadicAlgCl ℓ))
  (F : ∀ i : ι, V i →ₗ[ℚ_[ℓ]] Fin N → PadicAlgCl ℓ)

/-- `r` is the largest quotient on which `T` acts by `θ`: the `ℚ_ℓ`-linear maps
`F i : V i → ℚ̄_ℓ ^ N` intertwine `ρ i` with `matrixRep r` (the matrices `r g` acting on
`ℚ̄_ℓ ^ N`), have values that span, turn `T i s` into the scalar `θ s`, and are universal among the
families of maps to `ℚ̄_ℓ`-vector spaces that do so. -/
structure IsEigenQuotient : Prop where
  /-- The `F i` are equivariant. -/
  map_equivariant : ∀ (i : ι) (g : Γ) (x : V i), matrixRep r g (F i x) = F i (ρ i g x)
  /-- The values of the `F i` span `ℚ̄_ℓ ^ N`. -/
  span_range_eq_top : span (PadicAlgCl ℓ) (Set.range fun x : Σ i : ι, V i ↦ F x.1 x.2) = ⊤
  /-- `F i` turns `T i s` into the scalar `θ s`. -/
  map_T_eq_smul : ∀ (i : ι) (s : σ) (x : V i), F i (T i s x) = θ s • F i x
  /-- Every family `f` of maps to a `ℚ̄_ℓ`-vector space that turns each `T i s` into `θ s` factors
  through `F`. -/
  exists_factor : ∀ (M : Type) [AddCommGroup M] [Module (PadicAlgCl ℓ) M] [Module ℚ_[ℓ] M]
      [IsScalarTower ℚ_[ℓ] (PadicAlgCl ℓ) M] (f : ∀ i : ι, V i →ₗ[ℚ_[ℓ]] M),
    (∀ (i : ι) (s : σ) (x : V i), f i (T i s x) = θ s • f i x) →
    ∃ φ : (Fin N → PadicAlgCl ℓ) →ₗ[PadicAlgCl ℓ] M, ∀ (i : ι) (x : V i), φ (F i x) = f i x

variable {ρ T}

/-- If the operators `T i s` commute with `Γ`, the largest quotient on which they act by `θ`
exists, and it is continuous if the `ρ i` are. Continuity of `ρ i` is assumed in the form in
which it is used: `g ↦ f (ρ i g x)` is continuous for every `x` and every `ℚ_ℓ`-linear
`f : V i → ℚ̄_ℓ ^ N`, so no topology on `V i` is needed. -/
lemma exists_isEigenQuotient [Fintype ι] [∀ i, Module.Finite ℚ_[ℓ] (V i)]
    [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (h_comm : ∀ (i : ι) (s : σ) (g : Γ), Commute (T i s) (ρ i g))
    (hρ_cont : ∀ (i : ι) (x : V i) {N : ℕ} (f : V i →ₗ[ℚ_[ℓ]] Fin N → PadicAlgCl ℓ),
      Continuous fun g : Γ ↦ f (ρ i g x)) :
    ∃ (N : ℕ) (r : Γ →* GL (Fin N) (PadicAlgCl ℓ))
        (F : (i : ι) → V i →ₗ[ℚ_[ℓ]] Fin N → PadicAlgCl ℓ),
      IsEigenQuotient (N := N) ρ T θ r F ∧ Continuous r := by
  classical
  -- Take the quotient of `ℚ̄_ℓ ⊗ ⨁ V i` by the span `S` of the `G i (T i s x) - θ s • G i x`, in a
  -- basis. The universal property gives the action of `Γ`, because `Γ` commutes with `T`.
  let G (i : ι) : V i →ₗ[ℚ_[ℓ]] PadicAlgCl ℓ ⊗[ℚ_[ℓ]] Π₀ i, V i :=
    mk ℚ_[ℓ] (PadicAlgCl ℓ) (Π₀ i, V i) 1 ∘ₗ lsingle (M := fun j : ι ↦ V j) i
  let S : Submodule (PadicAlgCl ℓ) (PadicAlgCl ℓ ⊗[ℚ_[ℓ]] Π₀ i, V i) :=
    span (PadicAlgCl ℓ) {G i (T i s x) - θ s • G i x | (i) (s) (x)}
  let e := (finBasis (PadicAlgCl ℓ) ((PadicAlgCl ℓ ⊗[ℚ_[ℓ]] Π₀ i, V i) ⧸ S)).equivFun
  let F (i : ι) : V i →ₗ[ℚ_[ℓ]] Fin _ → PadicAlgCl ℓ :=
    (e.toLinearMap ∘ₗ S.mkQ).restrictScalars ℚ_[ℓ] ∘ₗ G i
  -- All of `IsEigenQuotient` except equivariance, phrased with the trivial representations.
  obtain ⟨-, h_span, h_eig, h_univ⟩ : IsEigenQuotient (Γ := Γ) 1 T θ 1 F := by
    refine ⟨by simp, ?_, ?_, fun M instAddCommGroup instModule instModuleQ instTower f hf ↦ ?_⟩
    · -- The quotient map by the span of the values kills every `F i x`, so it is zero.
      rw [← ker_mkQ (span ..), ker_eq_top, ← cancel_right e.surjective]
      ext i x
      exact (Submodule.Quotient.mk_eq_zero _).2 (subset_span ⟨⟨i, x⟩, rfl⟩)
    · -- `F i` turns `T i s` into `θ s`, since each `G i (T i s x) - θ s • G i x` lies in `S`.
      have h_mem_S (i : ι) (s : σ) (x : V i) : G i (T i s x) - θ s • G i x ∈ S :=
        subset_span ⟨i, s, x, rfl⟩
      simp [F, ← map_smul, ← Quotient.mk_smul, Submodule.Quotient.eq, h_mem_S]
    · -- The map induced by `f` on `ℚ̄_ℓ ⊗ ⨁ V i` kills `S`.
      have h_S_le : S ≤ ker ((lsum ℕ f).liftBaseChange (PadicAlgCl ℓ)) := by
        refine span_le.2 ?_
        rintro _ ⟨i, s, x, rfl⟩
        simp [G, hf]
      exact ⟨S.liftQ ((lsum ℕ f).liftBaseChange _) h_S_le ∘ₗ e.symm, by simp [F, G]⟩
  clear_value F
  -- `R g` is the map that the universal property attaches to the family `F i ∘ ρ i g`.
  have h_eig_comp (g : Γ) (i : ι) (s : σ) (x : V i) :
      F i (ρ i g (T i s x)) = θ s • F i (ρ i g x) := by
    rw [← h_eig, ← End.mul_apply (T i s), (h_comm i s g).eq, End.mul_apply]
  have h_act (g : Γ) : ∃ R : End (PadicAlgCl ℓ) (Fin _ → PadicAlgCl ℓ),
      ∀ (i : ι) (x : V i), R (F i x) = F i (ρ i g x) :=
    h_univ _ (fun i ↦ F i ∘ₗ ρ i g) (h_eig_comp g)
  choose R hR using h_act
  -- `R` is multiplicative: both sides agree on the values `F i x`, which span.
  have h_R_one : R 1 = 1 := ext_on_range h_span (by simp [hR])
  have h_R_mul (g g' : Γ) : R (g * g') = R g * R g' := ext_on_range h_span (by simp [hR])
  let R' : Γ →* End (PadicAlgCl ℓ) (Fin _ → PadicAlgCl ℓ) := ⟨⟨R, h_R_one⟩, h_R_mul⟩
  refine ⟨finrank (PadicAlgCl ℓ) (_ ⧸ S), (toMatrixAlgEquiv'.toMonoidHom.comp R').toHomUnits, F,
    ⟨by simp [R', hR, toMatrixAlgEquiv'], h_span, h_eig, h_univ⟩, ?_⟩
  -- The vectors `y` with `g ↦ R g y` continuous form a subspace containing all `F i x`.
  have h_gen (x : Σ i : ι, V i) : Continuous fun g : Γ ↦ R g (F x.1 x.2) :=
    (hρ_cont x.1 x.2 (F x.1)).congr fun g ↦ (hR g x.1 x.2).symm
  have h_cont (y : Fin _ → PadicAlgCl ℓ) : Continuous fun g : Γ ↦ R g y := by
    have h_top : ⊤ ≤ (continuousSubmodule ..).comap (pi R) :=
      h_span.ge.trans (span_le.2 (Set.range_subset_iff.2 h_gen))
    exact h_top (mem_top (x := y))
  exact .of_coeHom_comp (.matrix_transpose (continuous_pi fun l ↦ h_cont _))

variable {θ r F} (h : IsEigenQuotient ρ T θ r F) {s : Finset ℕ} {m : ℕ → ℤ} {d : ℕ → ℕ}
  (t : ℕ → σ) [OverGp Γ ℓ] (hρ : ∀ i : ι, IsCrystalline (ρ i))

include h hρ

/-- Let `r` with the maps `F i` be the largest quotient on which `T` acts by `θ` (hypothesis `h`).
If every `ρ i` is crystalline (hypothesis `hρ`), then so is the representation `g ↦ r g` on
`ℚ̄_ℓ ^ N`. -/
lemma IsEigenQuotient.isCrystalline : IsCrystalline (matrixRep r) := by
  -- It is enough that each `1 ⊗ y` lies in the span of the fixed periods. These `y` are closed
  -- under addition, and the vectors `c • F i x` generate additively.
  obtain ⟨h_equiv, h_span, -⟩ := h
  refine isAdmissible_of_one_tmul_mem_span fun y ↦
    closure_induction (hx := eq_top_iff'.1 h_span y) (by simp)
      (by simp +contextual [tmul_add, add_mem]) ?_
  rintro c _ ⟨⟨i, x⟩, rfl⟩
  -- `c • F i` is an equivariant map from the crystalline representation `ρ i`.
  exact (hρ i).periodTensorMap_mem_span_fixedPeriods (ρ' := matrixRep r) (f := c • F i)
    (by simp [← h_equiv]) (1 ⊗ₜ x)

/-- Let `r` with the maps `F i` be the largest quotient on which `T` acts by `θ` (hypothesis `h`),
and let the `ρ i` be crystalline (hypothesis `hρ`). Let `toGp` (from the instance `[OverGp Γ ℓ]`)
have open image. Let `toGp g` act on the residue field as `x ↦ x ^ (1 / ℓ ^ f)`. If
`∑ k ∈ s, m k • T (t k) ∘ β(g ^ d k)` vanishes on each `B ⊗ V i`, with `β` the linearised Frobenius
`linearFrob`, then the polynomial `∑ k ∈ s, m k θ (t k) X ^ d k` kills `β(g)` for `r`. -/
lemma IsEigenQuotient.isKilledBy {f : ℕ} {g : Γ} (hg : IsWeilPair (toGp g) f)
    (h_rel : ∀ (i : ι) (y : Bmax ⊗[ℤ_[ℓ]] V i),
      ∑ k ∈ s,
        m k •
          baseChange Bmax ((T i (t k)).restrictScalars ℤ_[ℓ])
            (linearFrob (ρ i) (g ^ d k) (d k * f) y) = 0) :
    IsKilledBy (matrixRep r) g f (∑ k ∈ s, C (m k * θ (t k)) * X ^ d k) := by
  -- Vectors `c • F i x` generate additively, so test the operator on `φ.baseChange _ (a ⊗ₜ x)`
  -- with `φ = c • F i`; there it equals the image under `φ` of the relation `h_rel`.
  have h_pcr : IsPotentiallyCrystalline (matrixRep r) :=
    (h.isCrystalline hρ).isPotentiallyCrystalline
  obtain ⟨h_equiv, h_span, h_eig, -⟩ := h
  refine ⟨h_pcr, AlgebraTensorModule.ext fun a y ↦ ?_⟩
  have hy : y ∈ span (PadicAlgCl ℓ) (Set.range fun x : Σ i : ι, V i ↦ F x.1 x.2) :=
    h_span.ge mem_top
  refine closure_induction (hx := hy) (by simp)
    (by simp +contextual only [tmul_add, map_add, implies_true]) ?_
  rintro c _ ⟨⟨i, x⟩, rfl⟩
  let φ : V i →ₗ[ℤ_[ℓ]] Fin N → PadicAlgCl ℓ := (c • F i).restrictScalars ℤ_[ℓ]
  have h_tmul : a ⊗ₜ[ℤ_[ℓ]] (c • F i x) =
      φ.baseChange Bmax (a ⊗ₜ x) :=
    (φ.baseChange_tmul a x).symm
  -- `linearFrob` is natural for the equivariant map `φ`, and multiplicative in `(g, f)`.
  have h_frob (n : ℕ) (z : Bmax ⊗[ℤ_[ℓ]] V i) :
      (linearFrob (matrixRep r) g f ^ n) (φ.baseChange _ z) =
        φ.baseChange _ (linearFrob (ρ i) (g ^ n) (n * f) z) := by
    rw [← linearFrob_pow h_pcr hg,
      baseChange_linearFrob (hρ i).isPotentiallyCrystalline (hg.pow n) h_pcr φ
        (by simp [φ, ← h_equiv])]
  -- `φ` turns `T i (t k)` into the scalar `θ (t k)`.
  have h_coef (k : ℕ) (z : Bmax ⊗[ℤ_[ℓ]] V i) :
      coeffEnd (PadicAlgCl ℓ) _ (m k * θ (t k)) (φ.baseChange Bmax z) =
        φ.baseChange _ (m k • baseChange _ ((T i (t k)).restrictScalars ℤ_[ℓ]) z) := by
    refine z.inductionOn ?_ (by simp +contextual only [map_add, smul_add, implies_true])
    simp [h_eig, φ, smul_comm c, smul_smul]
  -- The operator at `φ (a ⊗ₜ x)` is the image under `φ` of the relation `h_rel` at `a ⊗ₜ x`.
  simp only [h_tmul, LinearMap.zero_apply]
  rw [← map_zero (φ.baseChange Bmax), ← h_rel i (a ⊗ₜ x)]
  simp only [eval₂_finsetSum, C_mul_X_pow_eq_monomial, eval₂_monomial, LinearMap.sum_apply,
    End.mul_apply, h_frob, h_coef, map_sum]

/-- Let `r` with the maps `F i` be the largest quotient on which `T` acts by `θ` (`h`), the `ρ i`
crystalline (`hρ`), `toGp` (from `[OverGp Γ ℓ]`) of open image, and the `T i s` commuting with each
other and with `Γ`. Let `γ : ℚ̄_ℓ → ℂ_ℓ` agree with `a ∈ Gal(ℚ̄_ℓ/ℚ_ℓ)`. If `u` is not a Hodge–Tate
jump of `r` at `γ`, some combination `c` of words in `σ` has (a) `c(a ∘ θ) = 1` and
(b) `c(T)` killing the vectors of Hodge–Tate weight `u` in each `ℂ_ℓ ⊗ V i`. -/
lemma IsEigenQuotient.exists_sum_baseChange_eq_zero_of_jump_eq_zero [Fintype ι]
    [∀ i, Module.Finite ℚ_[ℓ] (V i)] {γ : PadicAlgCl ℓ →ₐ[ℤ_[ℓ]] ℂ_[ℓ]} {u : ℤ}
    {a : Gp ℓ} (ha : ∀ x : PadicAlgCl ℓ, γ x = a x)
    (hTρ : ∀ (i : ι) (s : σ) (g : Γ), Commute (T i s) (ρ i g))
    (hTT : ∀ (i : ι) (s t : σ), Commute (T i s) (T i t)) (h_jump : jump (matrixRep r) γ u = 0) :
    ∃ c : List σ →₀ PadicAlgCl ℓ,
      -- (a) the combination `c` of words takes the value `1` at `a ∘ θ`
      (c.sum fun (L : List σ) (z : PadicAlgCl ℓ) ↦ z * (L.map (a ∘ θ)).prod) = 1 ∧
      -- (b) at `T i` it kills the vectors of weight `u`
      ∀ (i : ι) (y : ℂ_[ℓ] ⊗[ℤ_[ℓ]] V i),
        HasHodgeTateWeight (ρ i) u y →
        (c.sum fun (L : List σ) (z : PadicAlgCl ℓ) ↦
            z • ((L.map (T i)).prod.restrictScalars ℤ_[ℓ]).baseChange ℂ_[ℓ]) y = 0 := by
  classical
  -- Words in `T` act by composition on the finite-dimensional space of families of forms of weight
  -- `u`. There is no joint eigenvector for `a ∘ θ`, so `exists_words_comb_eq_zero` gives `c`
  -- killing this space. Then pair `c(T) y` with a basis of forms, each of some weight.
  obtain ⟨h_equiv, h_span, -, h_univ⟩ := h
  let Φ (v : ℤ) (L : List σ) :
      End (PadicAlgCl ℓ) (∀ i, hodgeTateMaps (ρ i) (toAlgHom ..) v) :=
    piMap fun i ↦ hodgeTateMaps.pull (L.map (T i)).prod
      (by simp [← End.mul_apply, (Commute.list_prod_left ..).eq, *])
  have h_alg : Algebra.IsAlgebraic ℤ_[ℓ] ℚ_[ℓ] := IsLocalization.isAlgebraic ℚ_[ℓ] ℤ_[ℓ]⁰
  have h_no_eigen (f : ∀ i : ι, hodgeTateMaps (ρ i) (toAlgHom ℤ_[ℓ] ℚ_[ℓ] ℂ_[ℓ]) u)
      (hf : ∀ s : σ, Φ u [s] f = (a ∘ θ) s • f) : f = 0 := by
    -- By the universal property of the quotient, `f` factors through a `γ`-semilinear form `φ`,
    -- which has weight `u` for `r` and so vanishes.
    obtain ⟨φ, hφ⟩ : ∃ φ : (Fin N → PadicAlgCl ℓ) →ₛₗ[(γ : PadicAlgCl ℓ →+* ℂ_[ℓ])] ℂ_[ℓ],
        ∀ (i : ι) (x : V i), φ (F i x) = (f i).val x := by
      -- let `ℚ̄_ℓ` act on `ℂ_ℓ` through `γ`, so that a `γ`-semilinear form is linear
      let := γ.toModule
      have h_eig (i : ι) (s : σ) (x : V i) : (f i).val (T i s x) = γ (θ s) * (f i).val x := by
        have h_f_apply : ((Φ u [s] f) i).val x = (((a ∘ θ) s • f) i).val x := by rw [hf s]
        simpa [Φ, hodgeTateMaps.pull, ha, Algebra.smul_def] using! h_f_apply
      -- the instances are passed by hand, since `ℂ_ℓ` carries another action of `ℚ̄_ℓ`
      obtain ⟨φ, hφ⟩ := @h_univ ℂ_[ℓ] _ _ _ (.of_algHom (γ.extendScalarsOfIsLocalization _ _⁰))
        (fun i ↦ ⟨(f i).val.toAddHom, by simp [Algebra.smul_def]⟩) h_eig
      exact ⟨⟨φ.1, φ.2⟩, hφ⟩
    have h_mem : φ ∈ hodgeTateMaps (matrixRep r) γ u :=
      mem_hodgeTateMaps_of_span h_span fun ⟨i, x⟩ ↦ by simpa [↓h_equiv, ← hφ] using! (f i).prop x
    ext
    simp [← hφ, jump_eq_zero_iff.1 h_jump φ h_mem]
  have h_comm (s t : σ) : Commute (Φ u [s]) (Φ u [t]) := by
    -- Both sides apply the same form to `x` moved by `T j s` and `T j t`, which commute.
    ext i f j x
    exact congrArg _ (LinearMap.congr_fun (hTT j s t).eq.symm x)
  obtain ⟨c, h_one, h_kill⟩ := exists_words_comb_eq_zero (Φ u) (by aesop) h_comm h_no_eigen
  refine ⟨c, h_one, fun i y hy ↦ ?_⟩
  -- A basis `b` of the forms on `V i`, with `b l` of weight `w l` (`hb`).
  obtain ⟨-, w, -, -, b, hb, -⟩ :=
    (hρ i).isPotentiallyCrystalline.exists_isHodgeTateFrame (finBasis ..) (toAlgHom ..)
  -- `Λ` is the pairing of `e ⊗ₜ x` with a form `z`, with value `e * z x`.
  let Λ : ℂ_[ℓ] ⊗[ℤ_[ℓ]] V i →ₗ[ℂ_[ℓ]]
      (V i →ₛₗ[(toAlgHom ℤ_[ℓ] ℚ_[ℓ] ℂ_[ℓ] : ℚ_[ℓ] →+* ℂ_[ℓ])] ℂ_[ℓ]) →ₗ[ℂ_[ℓ]] ℂ_[ℓ] :=
    liftBaseChange ℂ_[ℓ]
      (.restrictScalars ℤ_[ℓ] (S := ℚ_[ℓ]) ⟨(b.constr ℕ b).flip.toAddHom, by simp⟩)
  set cT := c.sum fun (L : List σ) (z : PadicAlgCl ℓ) ↦
    z • ((L.map (T i)).prod.restrictScalars ℤ_[ℓ]).baseChange ℂ_[ℓ]
  have h_basis (l : Fin (finrank ℚ_[ℓ] (V i))) : Λ (cT y) (b l) = 0 := by
    -- Move `c(T)` to the form: `z = b l ∘ c(T)` has the weight `w l` of `b l`.
    let z : hodgeTateMaps (ρ i) (toAlgHom ℤ_[ℓ] ℚ_[ℓ] ℂ_[ℓ]) (w l) :=
      c.sum (fun L e ↦ e • Φ (w l) L) (Pi.single i ⟨b l, hb l⟩) i
    have h_adj : Λ.flip (b l) ∘ₗ cT = Λ.flip z :=
      AlgebraTensorModule.ext (by simp [Λ, z, cT, Φ, hodgeTateMaps.pull, Finsupp.sum])
    rw [← flip_apply, ← comp_apply, h_adj]
    obtain rfl | hw := eq_or_ne (w l) u
    · -- For `w l = u`, the combination `c(Φ u)` is zero, so `z = 0`.
      have h_z : z = 0 := by simp only [z, h_kill, LinearMap.zero_apply, Pi.zero_apply]
      simp [h_z]
    -- For `w l ≠ u` the pairing of `y` with `z` transforms by two different powers of the
    -- cyclotomic character, so it vanishes by Tate's theorem.
    obtain ⟨_, e, x, rfl⟩ := y.exists_sum_tmul_eq
    refine tate_eq_zero_of_cyclotomicGp_twist (neg_injective.ne hw) (nhds_one_le_map_nearOne Γ
      ((Filter.eventually_all.mpr fun k ↦ z.prop (x k)).mono fun g hg ↦ ?_))
    -- Pair both sides of the weight condition `hy g` with `z`.
    have h_pair : Λ (tensorAction ℂ_[ℓ] (toGp g) (ρ i g) (∑ k, e k ⊗ₜ[ℤ_[ℓ]] x k)) z =
        Λ ((cyclotomicGp (toGp g) ^ (-u)).val • ∑ k, e k ⊗ₜ[ℤ_[ℓ]] x k) z :=
      congrArg (fun y' ↦ Λ y' z) (hy g)
    simpa [Λ, hg, Finset.smul_sum, tensorAction] using h_pair
  -- Every linear form on `ℂ_ℓ ⊗ V i` is the pairing with some form.
  refine (forall_dual_apply_eq_zero_iff ℂ_[ℓ] _).1 fun φ ↦ ?_
  -- The form on `V i` that `φ` restricts to, as a `ℚ_ℓ`-semilinear map.
  let ψ : V i →ₛₗ[(toAlgHom ℤ_[ℓ] ℚ_[ℓ] ℂ_[ℓ] : ℚ_[ℓ] →+* ℂ_[ℓ])] ℂ_[ℓ] :=
    ⟨(((liftBaseChangeEquiv _).symm φ).extendScalarsOfIsLocalization ℤ_[ℓ]⁰ ℚ_[ℓ]).toAddHom,
      by simp [Algebra.smul_def]⟩
  have hφ : φ = Λ.flip ψ := by
    ext
    simp [Λ, ψ]
  rw [hφ, flip_apply, b.ext (f₁ := Λ (cT y)) (f₂ := 0) h_basis, LinearMap.zero_apply]

end New.Variety

end EigenQuotient

/-!
## The Galois representation attached to a Hecke eigensystem of a model

The result `New.Variety.Model.exists_galois_rep` builds a Galois representation from a system `θ` of
Hecke eigenvalues. In the proof, this representation is the largest quotient
(`New.Variety.IsEigenQuotient`) of the `ℓ`-adic cohomology of the base of a `New.Variety.Model` on
which the Hecke operators act by `θ`. The Hecke polynomial comes from the congruence relation of the
model. The jumps come from the Lefschetz formula and the Hodge–Tate map.
-/

section GaloisRep

open Matrix Polynomial New GaloisRep Period Variety Finset Module IsLocalization Submodule
  ellAdicCohom LinearMap Flat Filter IsEigenQuotient ModuleCat.Algebra Int

open scoped NumberField

/-- If `R` is the localization of `𝓞 E` at a set `M` of denominators prime to `w`, then `R` is
integral at every place `A` of `Ω` above `w`. -/
lemma New.Variety.algebraMap_mem_of_isLocalization {E : Type} [Field E] [NumberField E]
    [Algebra E Ω] {R : Subalgebra (𝓞 E) E} {M : Submonoid (𝓞 E)} [IsLocalization M R]
    {w : FinPlace E} (hM : M ≤ w.asIdeal.primeCompl) {A : ClosurePlace} (hA : IsPlaceOver A w)
    (x : R) :
    algebraMap (CommRingCat.of R) Ω x ∈ A := by
  -- `x * m = c` with `c` in `𝓞 E` and a denominator `m ∈ M`, which is a unit at `A`
  obtain ⟨⟨c, m⟩, hx : x * algebraMap (𝓞 E) R m = algebraMap (𝓞 E) R c⟩ := surj M x
  have hm_unit : 1 ≤ A.valuation (algebraMap R Ω (algebraMap (𝓞 E) R m)) :=
    not_lt.mp fun hm_lt ↦ hM m.prop ((hA m).mp hm_lt)
  have h_le : A.valuation (algebraMap R Ω (x * algebraMap (𝓞 E) R m)) ≤ 1 := by
    rw [A.valuation_le_one_iff, hx]
    exact Cohomology.algebraMap_ringOfIntegers_mem A c
  refine A.mem_of_valuation_le_one _ (le_of_mul_le_of_one_le_left ?_ hm_unit)
  rwa [← map_mul, ← map_mul]

/-- Let `X` be a Kuga–Sato tower over `R` with base `Z`, at a neat level (`hN`), with `R` mapping
into `A` (`hR`). Let `T n` act on `V^n(Z)`, `n ≤ 2 * X.dimension`. Assume (`hT_word`) that for each
word `L` and each `b` spanned by `GUPlus`, at all large levels the coset sum of leg pull-backs over
`b * τ_L` equals the coset sum over `b` of pull-backs composed with `T_L`. Let `ε` identify `ℂ` with
the algebraic closure of `ℚ_[ℓ]` compatibly with `A`. If the combination of words `c(T)` kills all
vectors of Hodge–Tate weight `h` (`hc_kill`), then for every `b` in the Hecke algebra the product
`b * c(τ)` is `h`-null (`New.Variety.IsNullHecke`: its Lefschetz sums in weight `h` vanish). Here
`c(τ) = ∑ L, ε⁻¹ (c L) • τ_L` is the same combination of the Hecke elements. -/
lemma New.Variety.Model.isNullHecke_mul_of_kills_weight {E : Type} [Field E] [CMBase E] {a d₀ : ℕ}
    [HasQuadSubfield d₀ E] {𝔑 : 𝓞 E} {ν : ℕ} {R : Subalgebra (𝓞 E) E}
    (X : Model (Fin a) d₀ 𝔑 ν R) {ℓ : ℕ} [NeZero a] (hN : IsNeat (Fin a) 𝔑) [ThePrime ℓ]
    [Algebra E Ω] {A : ClosurePlace} [place : PadicPlaceEmbedding E A ℓ]
    (hR : ∀ x : CommRingCat.of R, algebraMap (CommRingCat.of R) Ω x ∈ A) (ε : ℂ ≃+* PadicAlgCl ℓ)
    (hε : ∀ y : E, ε (algebraMap E ℂ y) = place.e (algebraMap E Ω y))
    (T : ∀ n : Set.Iic (X.dimension + X.dimension),
      SafePlace 𝔑 × ℕ → End ℚ_[ℓ] ((ellAdicCohom (.of R) Ω n).obj (.op X.base)))
    (hT_word : ∀ (n : Set.Iic (X.dimension + X.dimension)) (L : List (SafePlace 𝔑 × ℕ)),
      ∀ b ∈ spanOn ℂ (GUPlus E (Fin a)),
        ∀ᶠ i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E (Fin a)) in atTop,
        ∀ {N : Type 2} [AddCommGroup N] [Module ℂ N]
          (Ψ : ((ellAdicCohom (.of R) Ω n).obj (.op X.base) →ₗ[ℚ_[ℓ]]
            (ellAdicCohom (.of R) Ω n).obj (.op (X.cover i))) →+ N),
          cosetSum (fun q ↦ Ψ (X.legPullback (ellAdicCohom (.of R) Ω n) i q))
              (b * (L.map tauHecke).prod.val) =
            cosetSum (fun q ↦
              Ψ (X.legPullback (ellAdicCohom (.of R) Ω n) i q ∘ₗ (L.map (T n)).prod)) b)
    {h : ℕ} {c : List (SafePlace 𝔑 × ℕ) →₀ PadicAlgCl ℓ}
    (hc_kill : ∀ (n : Set.Iic (X.dimension + X.dimension))
      (y : TensorProduct ℤ_[ℓ] ℂ_[ℓ] ((ellAdicCohom (.of R) Ω n).obj (.op X.base))),
      HasHodgeTateWeight (galoisAction (.of R) Ω (decompGroup Gal(Ω/E) A) X.base n) h y →
        (c.sum fun (L : List (SafePlace 𝔑 × ℕ)) (z : PadicAlgCl ℓ) ↦
          z • ((L.map (T n)).prod.restrictScalars ℤ_[ℓ]).baseChange ℂ_[ℓ]) y = 0)
    (b : heckeAlgebra (Fin a) ℂ 𝔑) :
    IsNullHecke ν h (b * ∑ L ∈ c.support, ε.symm (c L) • (L.map tauHecke).prod) := by
  have Z_smooth := X.smooth
  have Z_proper := X.proper
  have W_projective := X.projective
  have W_reduced := X.isReduced
  have W_smooth i := (X.covering i).smoothOfRelativeDimension_baseChange X.dimension
  have Z_charted : IsCharted X.base Ω := ⟨(hasAtlas_algPointsOf X.dimension).exists_isCharting⟩
  -- `ε` as the embedding of `ℂ` into the algebraic closure of `ℚ_[ℓ]`, for instance search
  let emb : EmbeddedInQpBar ℓ ℂ := { ε.toRingHom.toAlgebra with }
  -- By the Lefschetz formula it suffices to kill `∑_g (b c(τ))_g λ_h (u_g^* m_α^* x)` for
  -- Hodge classes `x`, where `m_α = X.mulMap α`, on levels `i` so deep that the words in `c` act
  -- through `T` (`hi`).
  have h_deep := c.support.eventually_all.mpr fun L _ ↦
    eventually_all.mpr fun n ↦ hT_word n L b.val b.prop.left
  refine X.isNullHecke_of_isNullFamily hN (h_deep.mono fun i hi α ↦
    woods_hole (hasAtlas_algPointsOf _) (hasAtlas_algPointsOf _) (X.projective i) fun hh q hq x ↦
      ?_)
  -- Hodge–Tate: `λ_h (u^* m_α^* x) = Θ (u^* v)` with `v` of weight `h`
  obtain ⟨v, Θ, hv_weight, hΘ⟩ := exists_hasHodgeTateWeight hR hε X.dimension ε.symm ε.right_inv
    (W := X.cover i) (x.map (freeAb.map ((algPoints E (CommRingCat.of R)).map (X.mulMap α))))
  let n : Set.Iic (X.dimension + X.dimension) := ⟨q + h, add_le_add hq hh⟩
  have h_word (L : List (SafePlace 𝔑 × ℕ)) (hL : L ∈ c.support) :=
    hi L hL n (.mk' (fun u ↦ Θ ((u.restrictScalars ℤ_[ℓ]).baseChange ℂ_[ℓ] v)) (by simp))
  -- the sum is `∑_L c_L ∑_g (b L(τ))_g Θ (u_g^* v) = ∑_g b_g Θ (u_g^* c(T) v) = 0`
  refine .trans ?_
    ((sum_congr rfl fun L hL ↦ congrArg (ε.symm (c L) • ·) (h_word L hL)).trans ?_)
  · simp [n, legPullback, ← hΘ, HodgeH.map_comp, cosetFn, cosetSum]
  · simpa [legPullback, Finsupp.linearCombination, Finsupp.sum, c.support.sum_comm,
      smul_comm (ε.symm _), cosetSum, baseChange_comp, smul_sum] using
      congr(cosetSum (fun g ↦ Θ (baseChange _ _ $(hc_kill n v hv_weight))) b.val)

open scoped Classical in
/-- Let `T` be Hecke operators on the cohomology groups `V^n(Z)` of the model `X` that
act through the legs of the levels `l w` (`hT`) and commute with the Galois action (`hT_gal`). Let
`A` be a place of `Ω` at which `R` is integral (`hR`) and the cohomology is crystalline
(`h_crys`), and let `(r, F)` be the largest quotient on which `T` acts by `ιℓ ∘ θ`, as a
representation of the decomposition group of `A` (`New.Variety.IsEigenQuotient`). If every member
of `J` is a weight `h ≥ 0` in which `θ` occurs, then every member of `J` is a Hodge–Tate jump of
`r` at `A` for the embedding `algebraMap E ℂ`. -/
lemma New.Variety.Model.jumpsRelAt_of_isEigenQuotient {E : Type} [Field E] [CMBase E] {a d₀ : ℕ}
    [HasQuadSubfield d₀ E] {𝔑 : 𝓞 E} {ν : ℕ} {R : Subalgebra (𝓞 E) E}
    (X : Model (Fin a) d₀ 𝔑 ν R) {ℓ : ℕ} [NeZero a] (hN : IsNeat (Fin a) 𝔑) [ThePrime ℓ]
    [Algebra E Ω] [PadicIso ℓ] (θ : SafePlace 𝔑 → ℕ → ℂ) (J : Multiset ℤ)
    (hJ_nonneg : ∀ u ∈ J, 0 ≤ u)
    (hJ_occurs : ∀ h : ℕ, (h : ℤ) ∈ J → OccursInWeight a ν θ h) {A : ClosurePlace}
    (hR : ∀ x : CommRingCat.of R, algebraMap (CommRingCat.of R) Ω x ∈ A)
    {l : SafePlace 𝔑 → Finset (nonZeroDivisors (𝓞 E) × GUPlus E (Fin a))}
    {T : ∀ n : Set.Iic (X.dimension + X.dimension),
      SafePlace 𝔑 × ℕ → End ℚ_[ℓ] ((ellAdicCohom (.of R) Ω n).obj (.op X.base))}
    (hT : ∀ n : Set.Iic (X.dimension + X.dimension),
      X.IsHeckeAction (ellAdicCohom (.of R) Ω n) l (T n))
    (hT_gal : ∀ (n : Set.Iic (X.dimension + X.dimension)) (s : SafePlace 𝔑 × ℕ) (g : Gal(Ω/E)),
      Commute (T n s) (galoisAction (.of R) Ω Gal(Ω/E) X.base n g))
    {N : ℕ} {r : Gal(Ω/E) →* GL (Fin N) (PadicAlgCl ℓ)}
    {F : ∀ n : Set.Iic (X.dimension + X.dimension),
      (ellAdicCohom (.of R) Ω n).obj (.op X.base) →ₗ[ℚ_[ℓ]] Fin N → PadicAlgCl ℓ}
    (h_cut : Variety.IsEigenQuotient
      (fun n : Set.Iic (X.dimension + X.dimension) ↦
        galoisAction (.of R) Ω (decompGroup Gal(Ω/E) A) X.base n) T
      (ιℓ ∘ ↿θ) (r.comp (decompGroup Gal(Ω/E) A).subtype) F)
    (h_crys : ∀ [PadicPlaceEmbedding E A ℓ] (n : ℕ),
      IsCrystalline (galoisAction (.of R) Ω (decompGroup Gal(Ω/E) A) X.base n)) :
    JumpsRelAt r A OccursIn (fun τ : E →+* ℂ ↦ if algebraMap E ℂ = τ then J else 0) := by
  have Z_smooth := X.smooth
  have Z_proper := X.proper
  have Z_charted : IsCharted X.base Ω := ⟨(hasAtlas_algPointsOf X.dimension).exists_isCharting⟩
  intro place γ s hs u hu h_jump
  -- Jumps. If `h` were no jump, some polynomial `c` with `c(θ) = 1` would have `c(T)` killing all
  -- vectors of weight `h`; then every `b * c(τ)` is `h`-null, against `OccursInWeight`.
  obtain ⟨h_emb, hu_mem⟩ : algebraMap E ℂ =
      RingHom.comp ιℓ.symm (RingHom.comp ((s⁻¹ : Gp ℓ) : PadicAlgCl ℓ →+* PadicAlgCl ℓ)
        (place.e.comp (algebraMap E Ω))) ∧ u ∈ J := by
    simpa [apply_ite] using hu
  lift u to ℕ using hJ_nonneg u hu_mem with h
  let ε : ℂ ≃+* PadicAlgCl ℓ := ιℓ.trans s.toRingEquiv
  have hε (y : E) : ε (algebraMap E ℂ y) = place.e (algebraMap E Ω y) := by simp [h_emb, ε]
  obtain ⟨c, hc_one, hc_kill⟩ : ∃ c : List (SafePlace 𝔑 × ℕ) →₀ PadicAlgCl ℓ,
      (c.sum fun L z ↦ z * (L.map (s ∘ ιℓ ∘ ↿θ)).prod) = 1 ∧
      ∀ (n : Set.Iic (X.dimension + X.dimension))
        (y : TensorProduct ℤ_[ℓ] ℂ_[ℓ] ((ellAdicCohom (.of R) Ω n).obj (.op X.base))),
        HasHodgeTateWeight (galoisAction (.of R) Ω (decompGroup Gal(Ω/E) A) X.base n) h y →
          (c.sum fun L z ↦ z • ((L.map (T n)).prod.restrictScalars ℤ_[ℓ]).baseChange ℂ_[ℓ]) y =
            0 :=
    exists_sum_baseChange_eq_zero_of_jump_eq_zero h_cut (h_crys ·) hs (fun n s g ↦ hT_gal n s g)
      (fun n ↦ (hT n).commute) h_jump
  have hc_one' : ∑ L ∈ c.support, ε.symm (c L) * (L.map ↿θ).prod = 1 := by
    apply ε.injective
    simpa [ε, map_list_prod, Finsupp.sum] using hc_one
  exact hJ_occurs h hu_mem c.support (ε.symm ∘ c) hc_one' fun b ↦
    X.isNullHecke_mul_of_kills_weight hN hR ε hε T
      (fun n L _ hb ↦ (hT n).eventually_cosetSum_mul_prod ℂ L hb) hc_kill b

/-- Eichler–Shimura away from `ℓ`. Let the Hecke operators `T` on the cohomology groups `V^n(Z)` of
the model `X` act through the legs of the levels `l w` (`hT_pull`), whose pull-backs along the leg
`X.leg i ⟦1⟧` are injective (`h_inj`), and let `(r, F)` be the largest quotient on which `T` acts by
`ιℓ ∘ θ`. Let `A` lie above the safe place `w`, with `R` integral at `A` and `ℓ` a unit at `A`. Then
the Hecke polynomial of `θ` at `w` kills `r s` for every geometric Frobenius `s` at `A`. -/
lemma New.Variety.Model.aeval_heckePoly_eq_zero_of_isEigenQuotient {E : Type} [Field E] [CMBase E]
    {a d₀ : ℕ} [HasQuadSubfield d₀ E] {𝔑 : 𝓞 E} {ν : ℕ} {R : Subalgebra (𝓞 E) E}
    (X : Model (Fin a) d₀ 𝔑 ν R) {ℓ : ℕ} [NeZero a] [ThePrime ℓ] [Algebra E Ω]
    (M : Submonoid (𝓞 E)) [IsLocalization M R] [PadicIso ℓ] (θ : SafePlace 𝔑 → ℕ → ℂ)
    {w : SafePlace 𝔑} {A : ClosurePlace} (hA : IsPlaceOver A w.val.val)
    (hR : ∀ x : CommRingCat.of R, algebraMap (CommRingCat.of R) Ω x ∈ A)
    {l : SafePlace 𝔑 → Finset (nonZeroDivisors (𝓞 E) × GUPlus E (Fin a))}
    (hl : ∀ (w : SafePlace 𝔑) (U : Submodule (ResField w.val.val) (Fin a → ResField w.val.val)),
      invHeckeIsogeny w.val U ∈ X.legIndices (l w))
    (h_inj : ∀ (n : ℕ) (i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E (Fin a))),
      Function.Injective ((ellAdicCohom (.of R) Ω n).map (X.leg i ⟦1⟧).op))
    {T : ∀ n : Set.Iic (X.dimension + X.dimension),
      SafePlace 𝔑 × ℕ → End ℚ_[ℓ] ((ellAdicCohom (.of R) Ω n).obj (.op X.base))}
    (hT_pull : ∀ (n : Set.Iic (X.dimension + X.dimension)) (w : SafePlace 𝔑) (j : ℕ)
      (x : (ellAdicCohom (.of R) Ω n).obj (.op X.base)),
      ((ellAdicCohom (.of R) Ω n).map (X.leg (l w) ⟦1⟧).op).hom (T n (w, j) x) =
        ∑ c ∈ Finset.univ.filter
            fun c : Submodule (ResField w.val.val) (Fin a → ResField w.val.val) ↦
              finrank (ResField w.val.val) c = j,
          ((ellAdicCohom (.of R) Ω n).map
            (X.leg (l w) ⟦invHeckeIsogeny w.val c⟧).op).hom x)
    {N : ℕ} {r : Gal(Ω/E) →* GL (Fin N) (PadicAlgCl ℓ)}
    {F : ∀ n : Set.Iic (X.dimension + X.dimension),
      (ellAdicCohom (.of R) Ω n).obj (.op X.base) →ₗ[ℚ_[ℓ]] Fin N → PadicAlgCl ℓ}
    (h_eig : Variety.IsEigenQuotient
      (fun n : Set.Iic (X.dimension + X.dimension) ↦ galoisAction (.of R) Ω Gal(Ω/E) X.base n) T
        (ιℓ ∘ ↿θ) r F)
    {s : Gal(Ω/E)} (hs : IsFrob A w.val.val.q s⁻¹) (hℓ : A.valuation ℓ = 1) :
    Polynomial.aeval (r s : Matrix (Fin N) (Fin N) (PadicAlgCl ℓ))
      (heckePoly w.val.val.q a fun j : ℕ ↦ ιℓ (θ w j)) = 0 := by
  have Z_smooth := X.smooth
  have Z_proper := X.proper
  have W_projective := X.projective
  have W_reduced := X.isReduced
  have W_smooth i := (X.covering i).smoothOfRelativeDimension_baseChange X.dimension
  have R_noetherian : IsNoetherianRing R := isNoetherianRing M R inferInstance
  have Z_charted_int : IsCharted X.base R := ⟨(hasAtlas_algPointsOf X.dimension).exists_isCharting⟩
  have Z_charted : IsCharted X.base Ω := ⟨(hasAtlas_algPointsOf X.dimension).exists_isCharting⟩
  have W_charted i : IsCharted (X.cover i) Ω :=
    ⟨(hasAtlas_algPointsOf X.dimension).exists_isCharting⟩
  obtain ⟨hF_gal, hF_span, hF_hecke, -⟩ := h_eig
  -- the residue characteristic `t` with `N w = t ^ f`, and the congruence relation above `A`
  obtain ⟨t, f, -, ht_mem, ht_prime, hq⟩ := w.val.val.asIdeal.exists_prime_and_absNorm_eq_pow
  have t_prime : Fact t.Prime := ⟨ht_prime⟩
  have ht_val : A.valuation t < 1 := hA.valuation_natCast_lt_one_iff.mpr ht_mem
  have h_cong := X.congruence _ w.prop _ (algebraMap R Ω ⁻¹' A.nonunits) (fun c ↦ (hA c).mpr) (hl w)
  rw [heckePoly]
  norm_cast at h_cong ⊢
  -- on `F n x` the polynomial is `F n` of a combination of `T` and Frobenius, which vanishes after
  -- pull-back to the level `l w` by `congruence_relation`
  refine toLinAlgEquiv'.injective (ext_on_range hF_span fun ⟨n, x⟩ ↦ ?_)
  simp [↓C_mul', -cast_mul]
  -- `matrixRep r` and the eigenvalues, in the form that `hF_gal` and `hF_hecke` use
  have h_rep (g : Gal(Ω/E)) :
      toLinAlgEquiv' (r g : Matrix (Fin N) (Fin N) (PadicAlgCl ℓ)) = matrixRep r g := rfl
  have h_eigenvalue (j : ℕ) : ιℓ (θ w j) = (ιℓ ∘ ↿θ) (w, j) := rfl
  conv_lhs =>
    enter [2, j]
    rw [mul_smul, cast_smul_eq_zsmul, h_rep, ← map_pow (matrixRep r), hF_gal, h_eigenvalue,
      ← hF_hecke _ (w, j), ← map_zsmul]
  rw [← map_sum, congrArg (F n) (h_inj n (l w) ?_), map_zero]
  have hs_t : IsFrob A (t ^ f) s⁻¹ := by
    rw [← hq]
    exact hs
  simpa [hT_pull, sum_filter, sum_comm, (finrank_le _).trans_eq, smul_sum] using
    congruence_relation hR (by simpa [ValuationSubring.valuation_eq_one_iff]) ht_val hs_t _
      _ _ (h_cong hq) x

/-- Eichler–Shimura at `ℓ`. Let `T` act on `V^n(Z) = H^n(X.base)` as follows: over `Bmax`, `T(w, j)`
followed by pull-back along `X.leg (l w) ⟦1⟧` equals the sum of pull-backs along the legs at
`invHeckeIsogeny w c`, over subspaces `c` of dimension `j` (`hT_pull_cris`). Pull-backs along
`X.leg i ⟦1⟧` are injective (`h_inj`). Let `(r, F)` be the largest quotient on which `T` acts by
`ιℓ ∘ θ` for the decomposition group of `A` over the safe place `w`, with `R` integral at `A` and
crystalline cohomology. Then for `s` a geometric Frobenius at `A` and `(s, k)` a Weil pair, the
Hecke polynomial of `ιℓ ∘ θ` at `w` kills `decompRep r A` at `(s, k)`. -/
lemma New.Variety.Model.isKilledBy_heckePoly_of_isEigenQuotient {E : Type} [Field E] [CMBase E]
    {a d₀ : ℕ} [HasQuadSubfield d₀ E] {𝔑 : 𝓞 E} {ν : ℕ} {R : Subalgebra (𝓞 E) E}
    (X : Model (Fin a) d₀ 𝔑 ν R) {ℓ : ℕ} [NeZero a] [ThePrime ℓ] [Algebra E Ω]
    (M : Submonoid (𝓞 E)) [IsLocalization M R] [PadicIso ℓ] (θ : SafePlace 𝔑 → ℕ → ℂ)
    {w : SafePlace 𝔑} {A : ClosurePlace} (hA : IsPlaceOver A w.val.val)
    (hR : ∀ x : CommRingCat.of R, algebraMap (CommRingCat.of R) Ω x ∈ A)
    {l : SafePlace 𝔑 → Finset (nonZeroDivisors (𝓞 E) × GUPlus E (Fin a))}
    (hl : ∀ (w : SafePlace 𝔑) (U : Submodule (ResField w.val.val) (Fin a → ResField w.val.val)),
      invHeckeIsogeny w.val U ∈ X.legIndices (l w))
    (h_inj : ∀ (n : ℕ) (i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E (Fin a))),
      Function.Injective ((ellAdicCohom (.of R) Ω n).map (X.leg i ⟦1⟧).op))
    {T : ∀ n : Set.Iic (X.dimension + X.dimension),
      SafePlace 𝔑 × ℕ → End ℚ_[ℓ] ((ellAdicCohom (.of R) Ω n).obj (.op X.base))}
    (hT_pull_cris : ∀ (n : Set.Iic (X.dimension + X.dimension)) (w : SafePlace 𝔑) (j : ℕ)
      (x : TensorProduct ℤ_[ℓ] Bmax ((ellAdicCohom (.of R) Ω n).obj (.op X.base))),
      (((ellAdicCohom (.of R) Ω n).map (X.leg (l w) ⟦1⟧).op).hom.restrictScalars ℤ_[ℓ]).baseChange
          Bmax (((T n (w, j)).restrictScalars ℤ_[ℓ]).baseChange Bmax x) =
        ∑ c ∈ Finset.univ.filter
            fun c : Submodule (ResField w.val.val) (Fin a → ResField w.val.val) ↦
              finrank (ResField w.val.val) c = j,
          (((ellAdicCohom (.of R) Ω n).map
            (X.leg (l w) ⟦invHeckeIsogeny w.val c⟧).op).hom.restrictScalars
              ℤ_[ℓ]).baseChange Bmax x)
    {N : ℕ} {r : Gal(Ω/E) →* GL (Fin N) (PadicAlgCl ℓ)}
    {F : ∀ n : Set.Iic (X.dimension + X.dimension),
      (ellAdicCohom (.of R) Ω n).obj (.op X.base) →ₗ[ℚ_[ℓ]] Fin N → PadicAlgCl ℓ}
    (h_cut : Variety.IsEigenQuotient
      (fun n : Set.Iic (X.dimension + X.dimension) ↦
        galoisAction (.of R) Ω (decompGroup Gal(Ω/E) A) X.base n) T
      (ιℓ ∘ ↿θ) (r.comp (decompGroup Gal(Ω/E) A).subtype) F)
    (h_crys : ∀ [PadicPlaceEmbedding E A ℓ] (n : ℕ),
      IsCrystalline (galoisAction (.of R) Ω (decompGroup Gal(Ω/E) A) X.base n))
    {s : Gal(Ω/E)} (hs : IsFrob A w.val.val.q s⁻¹) [place : PadicPlaceEmbedding E A ℓ]
    {hs' : s ∈ decompGroup Gal(Ω/E) A} {k : ℕ} (h_weil : IsWeilPair (place.toGp ⟨s, hs'⟩) k) :
    IsKilledBy (decompRep r A) ⟨s, hs'⟩ k (heckePoly w.val.val.q a fun j : ℕ ↦ ιℓ (θ w j)) := by
  have Z_smooth := X.smooth
  have Z_proper := X.proper
  have W_projective := X.projective
  have W_reduced := X.isReduced
  have W_smooth i := (X.covering i).smoothOfRelativeDimension_baseChange X.dimension
  have R_noetherian : IsNoetherianRing R := isNoetherianRing M R inferInstance
  have Z_charted_int : IsCharted X.base R := ⟨(hasAtlas_algPointsOf X.dimension).exists_isCharting⟩
  have Z_charted : IsCharted X.base Ω := ⟨(hasAtlas_algPointsOf X.dimension).exists_isCharting⟩
  have W_charted i : IsCharted (X.cover i) Ω :=
    ⟨(hasAtlas_algPointsOf X.dimension).exists_isCharting⟩
  -- the residue characteristic `t` with `N w = t ^ f`, and the congruence relation above `A`
  obtain ⟨t, f, -, ht_mem, ht_prime, hq⟩ := w.val.val.asIdeal.exists_prime_and_absNorm_eq_pow
  have t_prime : Fact t.Prime := ⟨ht_prime⟩
  have ht_val : A.valuation t < 1 := hA.valuation_natCast_lt_one_iff.mpr ht_mem
  have h_cong := X.congruence _ w.prop _ (algebraMap R Ω ⁻¹' A.nonunits) (fun c ↦ (hA c).mpr) (hl w)
  rw [heckePoly]
  norm_cast at h_cong ⊢
  -- the same as away from `ℓ`, with the crystalline Frobenius
  have hk : w.val.val.q = ℓ ^ k := by
    refine h_weil.eq_pow_of_isFrob ?_
    rw [← map_inv]
    exact place.isFrob_iff.mpr hs
  refine h_cut.isKilledBy (w, ·) (h_crys ·) h_weil fun n y ↦ ?_
  have h_rel :=
    (isCrystalline_and_linearFrob_rel E hR n _ _ _ _ (h_cong hk) fun _ ↦ h_weil.pow _).2
  apply lTensor_preserves_injective_linearMap
    (((ellAdicCohom (.of R) Ω n).map (X.leg (l w) ⟦1⟧).op).hom.restrictScalars ℤ_[ℓ])
    (h_inj n (l w))
  simpa [← baseChange_eq_lTensor, hT_pull_cris, sum_filter, sum_comm, (finrank_le _).trans_eq,
    ↓LinearMap.sum_apply, smul_sum] using! LinearMap.congr_fun h_rel y

open scoped Classical in
/-- The Galois representation cut out of the cohomology of the model `X` by the system `θ` of Hecke
eigenvalues. Let `R` be the localization of `𝓞 E` at `M`, prime to every safe place, and `J` a set
of weights `h ≥ 0` in which `θ` occurs (`New.Variety.OccursInWeight`: no combination `c` of Hecke
words with `c(θ) = 1` makes every `b * c(τ)` `h`-null). Some continuous `ℓ`-adic representation `ρ`
then satisfies `IsSphericalAbove` at each safe place `w`: `ρ` is unramified or crystalline above
`w`, has each `h ∈ J` as a jump at `algebraMap E ℂ`, and the Hecke polynomial of `θ` at `w` kills
geometric Frobenius. -/
lemma New.Variety.Model.exists_galois_rep {E : Type} [Field E] [CMBase E] {a d₀ : ℕ}
    [HasQuadSubfield d₀ E] {𝔑 : 𝓞 E} {ν : ℕ} {R : Subalgebra (𝓞 E) E}
    (X : Model (Fin a) d₀ 𝔑 ν R) {ℓ : ℕ} [NeZero a] (hN : IsNeat (Fin a) 𝔑) [ThePrime ℓ]
    [Algebra E Ω] (M : Submonoid (𝓞 E))
    (hM : ∀ w : FinPlace E, IsSafe 𝔑 w → M ≤ w.asIdeal.primeCompl) [IsLocalization M R]
    [PadicIso ℓ] (θ : SafePlace 𝔑 → ℕ → ℂ) (J : Multiset ℤ) (hJ_nonneg : ∀ u ∈ J, 0 ≤ u)
    (hJ_occurs : ∀ h : ℕ, (h : ℤ) ∈ J → OccursInWeight a ν θ h) :
    ∃ ρ : PadicRep Gal(Ω/E) ℓ,
      Continuous ρ.rep ∧
      ∀ w : SafePlace 𝔑,
        IsSphericalAbove ρ.rep OccursIn
          (fun τ : E →+* ℂ ↦ if algebraMap E ℂ = τ then J else 0) w.val.val
          (heckePoly w.val.val.q a fun j : ℕ ↦ ιℓ (θ w j)) := by
  -- Let `T` be the Hecke operators on the cohomology `V^n(Z)`, `n ≤ 2 * X.dimension`, and `r` the
  -- largest quotient of their sum on which `T` acts by `ιℓ ∘ θ`. Each local clause except the
  -- jumps, which come from `OccursInWeight`, is known for `V^n(Z)` and passes to this quotient.
  have Z_smooth := X.smooth
  have Z_proper := X.proper
  have W_projective := X.projective
  have W_reduced := X.isReduced
  have W_smooth i := (X.covering i).smoothOfRelativeDimension_baseChange X.dimension
  have R_noetherian : IsNoetherianRing R := isNoetherianRing M R inferInstance
  have Z_charted_int : IsCharted X.base R := ⟨(hasAtlas_algPointsOf X.dimension).exists_isCharting⟩
  have Z_charted : IsCharted X.base Ω := ⟨(hasAtlas_algPointsOf X.dimension).exists_isCharting⟩
  have W_charted i : IsCharted (X.cover i) Ω :=
    ⟨(hasAtlas_algPointsOf X.dimension).exists_isCharting⟩
  -- pull-back along the leg `u₁ = X.leg i ⟦1⟧` is injective with image containing the invariants
  choose h_inj h_descent using fun n i ↦ transfer (X.covering i) ℓ n
  -- a level `l w` that carries all the Hecke legs `u_U` at `w`, for subspaces `U` over the residue
  -- field; there `u₁^* T (w, j) = ∑ u_U^*` over the `U` of dimension `j` (`hT_pull`)
  have h_level (w : SafePlace 𝔑) : ∃ i, ∀ U, invHeckeIsogeny w.val U ∈ X.legIndices i :=
    (eventually_all.mpr fun U ↦ (X.eventually_translate ∅ (invHeckeIsogeny_mem_GUPlus w.val U)).mono
      fun _ hi ↦ hi.left).exists
  choose l hl using h_level
  choose T hT using fun n : Set.Iic (X.dimension + X.dimension) ↦
    exists_isHeckeAction (h_inj n) (h_descent n) hl
  have hT_pull (n : Set.Iic (X.dimension + X.dimension)) := (hT n).legPullback_comp
  -- the same after extending scalars to `Bmax`; both identities are then put in pointwise form
  have hT_pull_cris n w j :=
    congr((baseChangeHom ℤ_[ℓ] Bmax .. ∘ₗ restrictScalarsₗ ..) $(hT_pull n w j))
  simp [LinearMap.ext_iff, -Subtype.forall, legPullback, heckeSum, baseChange_comp, cosetSum,
    cosetFn] at hT_pull_cris hT_pull
  -- `T` commutes with the Galois action: check after the injective pull-back to the level `l w`
  have hT_gal (n : Set.Iic (X.dimension + X.dimension)) (s : SafePlace 𝔑 × ℕ) (g : Gal(Ω/E)) :
      Commute (T n s) (galoisAction (.of R) Ω Gal(Ω/E) X.base n g) :=
    ext fun x ↦ h_inj n (l s.1) (by simp [hT_pull, map_galoisAction])
  -- the largest quotient `(r, F)` on which `T` acts by `ιℓ ∘ θ`
  obtain ⟨N, r, F, h_eig, hr⟩ :=
    exists_isEigenQuotient (ιℓ ∘ ↿θ) hT_gal (continuous_galoisAction · E)
  -- the local clause at each safe place `w`: unramified or crystalline, the jumps, and
  -- Eichler–Shimura away from `ℓ` and at `ℓ`
  refine ⟨⟨r⟩, hr, fun w A hA ↦ ?_⟩
  have hR (x : CommRingCat.of R) : algebraMap (CommRingCat.of R) Ω x ∈ A :=
    algebraMap_mem_of_isLocalization (hM _ w.prop) hA x
  -- `isCrystalline_and_linearFrob_rel` for the empty relation: the cohomology is crystalline
  have h_crys [PadicPlaceEmbedding E A ℓ] (n : ℕ) :
      IsCrystalline (galoisAction (.of R) Ω (decompGroup Gal(Ω/E) A) X.base n) :=
    (isCrystalline_and_linearFrob_rel E hR n (X.mulMap ∘ ![]) 0 1 0
      (by simp [CongruenceRelation, Cancels]) nofun).1
  -- the quotient is also one for the decomposition group of `A`
  have h_cut : Variety.IsEigenQuotient
      (fun n : Set.Iic (X.dimension + X.dimension) ↦
        galoisAction (.of R) Ω (decompGroup Gal(Ω/E) A) X.base n) T
      (ιℓ ∘ ↿θ) (r.comp (decompGroup Gal(Ω/E) A).subtype) F :=
    { h_eig with map_equivariant := fun n g x ↦ h_eig.map_equivariant n g x }
  -- the residue characteristic `t` of `w`, which is not a unit at `A`
  obtain ⟨t, -, -, ht_mem, ht_prime, -⟩ := w.val.val.asIdeal.exists_prime_and_absNorm_eq_pow
  have t_prime : Fact t.Prime := ⟨ht_prime⟩
  have ht_val : A.valuation t < 1 := hA.valuation_natCast_lt_one_iff.mpr ht_mem
  refine ⟨⟨fun hℓ s hs ↦ ?_, isCrystalline h_cut (h_crys ·)⟩,
    X.jumpsRelAt_of_isEigenQuotient hN θ J hJ_nonneg hJ_occurs hR hT hT_gal h_cut h_crys,
    fun s hs ↦ ⟨X.aeval_heckePoly_eq_zero_of_isEigenQuotient M θ hA hR hl h_inj hT_pull h_eig hs,
      X.isKilledBy_heckePoly_of_isEigenQuotient M θ hA hR hl h_inj hT_pull_cris h_cut h_crys hs⟩⟩
  · -- unramified: inertia acts trivially on the `V^n`, whose images span
    refine Units.ext (toLin'.injective (ext_on_range h_eig.span_range_eq_top fun x ↦
      (h_eig.map_equivariant x.fst s x.snd).trans ?_))
    rw [galoisAction_eq_one_of_inertia hR (by simpa
      [ValuationSubring.valuation_eq_one_iff]) ht_val hs]
    simp

end GaloisRep
