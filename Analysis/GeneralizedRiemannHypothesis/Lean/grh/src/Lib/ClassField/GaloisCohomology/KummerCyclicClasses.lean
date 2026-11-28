import Lib.Adelic.Hecke.ClassSums
import Lib.ClassField.GaloisCohomology.ShapiroCorestriction
import Lib.ClassField.Places.LocalFields

/-!
# Cup products, Hilbert 90, Kummer cocycles and cyclic symbols in Galois cohomology

This file studies the Galois cohomology of `Ωˣ` for a group Γ acting on a field Ω. The group `Ωˣ` is
written additively (`New.DiscreteUnits`, with action `New.unitsRep`). In the last two sections Γ is
the profinite Galois group of Ω/K (`New.IsProGalois`). Take a continuous character χ : Γ → ℚ/ℤ with
kernel U and a Γ-invariant w in `Ωˣ`. The symbol (χ, w) = `New.cyclicClass ρ χ w` is the class in H²
of (g, h) ↦ carry(χ(g), χ(h))·w. The file first treats cup products of 1-cocycles, annihilators of
pairings, and a descent lemma for semilinear actions. Finally it shows that the classes vanishing on
U are the symbols (χ, w), and that (χ, w) = 0 exactly when w is a norm from U, that is, a field norm
from the field cut out by χ.

## Main definitions and results

* `New.cupProduct`, `New.cupProduct_flip`: the cup product of 1-cocycles, with values in `H²`, and
  its anticommutativity; `New.DiscreteModule.evalCup` is the case of the evaluation pairing.
* `New.Period.mem_span_fixed`: for a semilinear action, a vector fixed by a subgroup U of finite
  index is a linear combination of invariant vectors, provided every element outside U moves some
  U-fixed scalar. The invariant vectors are traces over the finitely many cosets, and Dedekind's
  independence of characters shows that their span contains the vector.
* `New.hilbert90_unitsRep`: Hilbert 90, every continuous 1-cocycle with values in `Ωˣ` is a
  coboundary.
* `New.exists_kummer_cocycle`: if `Γ` fixes the `n`-th roots of unity (`ζ ^ k` is
  `New.rootPowHom Ω n k` for a chosen primitive `n`-th root of unity `ζ`), an invariant `x = a ^ n`
  gives a homomorphism `f : Γ → ℤ/n` with `g a / a = ζ ^ f g`.
* `New.mk_eq_neg_cyclicClass_ofZModCocycle`: the cup product of `g ↦ g a / a` with `ξ : Γ → ℤ/n` is
  minus the cyclic class of `ξ / n` and `a ^ n`.
* `New.QZChar.cyclicClass_spec`: the classes in `H²(Γ, Ωˣ)` that die on `U` are the symbols `(χ, w)`
  of `New.cyclicClass` with `w` in `Kˣ` (embedded in `Ωˣ` by `New.DiscreteUnits.ofBase`), and
  `(χ, w) = 0` exactly when `w` is a norm from `U`. The two hard directions are
  `New.QZChar.exists_eq_cyclicClass_of_resH2_eq_zero` and
  `New.QZChar.exists_corestrictH0_eq_of_cyclicClass_eq_zero`.

Notions from other files:
* `New.DiscreteModule R Γ`: an `R`-module `V` with the discrete topology and a continuous `R`-linear
  action `ρ` of Γ; `New.Z1 ρ` and `New.Z2 ρ` are its continuous 1- and 2-cocycles.
* `New.unitsRep`: the ℤ-linear representation of Γ on Ω^× (written additively) coming from the
  action of Γ on the field Ω by ring automorphisms.
* `New.DiscreteModule.H2`: The continuous cohomology H²(Γ,A) of a discrete Γ-module A: 2-cocycles
  modulo the functions (g,h) ↦ g c(h) − c(gh) + c(g) with c continuous.
* `New.QZ` is ℚ/ℤ. `New.QZ.carry`: for a, b in ℚ/ℤ, the integer part (0 or 1) of the sum of their
  representatives in [0,1); `New.cyclicClass ρ χ w` is the class of the cocycle (g,h) ↦ carry(χ(g),
  χ(h))·w.
* `New.IsProGalois`: a profinite group acts on the Galois extension Ω/K as its Galois group, with
  open stabilisers.

## Relation to the literature

Known result: the parts of Galois cohomology in degrees ≤ 2 listed above, namely cup products,
Hilbert 90, Kummer cocycles and the symbols of cyclic extensions. Only explicit continuous cocycles
are used. Shapiro's lemma and corestriction (summation of functions on a coset space) come from
`Lib.ClassField.GaloisCohomology.ShapiroCorestriction`. Source: J.-P. Serre, Galois Cohomology
(1997); Neukirch–Schmidt–Wingberg, Cohomology of Number Fields (2nd ed. 2008), Ch. I, VI;
Atiyah–Wall in Cassels–Fröhlich (1967), IV §8.
-/

noncomputable section

/-!
## Elementary lemmas on the multiplicative group written additively

`New.DiscreteUnits Ω` is the group `Ωˣ` written additively, and `(x.toMul : Ω)` is the field element
underlying `x`.
-/

namespace New.DiscreteUnits

variable {Ω Γ K : Type*} [Field Ω] (x : DiscreteUnits Ω)
  (a : Ω) [Group Γ] [Field K] [Algebra K Ω] [MulSemiringAction Γ Ω] [SMulCommClass Γ K Ω]

@[ext]
lemma ext {x y : DiscreteUnits Ω} (h : x.toMul.val = y.toMul.val) : x = y := Units.ext h

/-- A non-zero element a of the field Ω, viewed as an element of the additively written
multiplicative group `New.DiscreteUnits` Ω. -/
def ofNeZero (ha : a ≠ 0) : DiscreteUnits Ω := Units.mk0 a ha

@[simp]
theorem val_ofNeZero (ha : a ≠ 0) : ((ofNeZero a ha).toMul : Ω) = a := rfl

@[simp]
lemma val_unitsRep (g : Γ) : (unitsRep g x).toMul.val = g • x.toMul := rfl

@[simp]
lemma val_ofBase (a : Additive Kˣ) :
    ((ofBase Γ Ω a : DiscreteUnits Ω).toMul : Ω) = algebraMap K Ω (a.toMul : K) :=
  rfl

/-- If Ω is algebraically closed and `n ≠ 0`, every `x` in `Ωˣ` (written additively) is `n • y`
for some `y`: the element `x` has an `n`-th root in `Ωˣ`. -/
lemma exists_nsmul (x : DiscreteUnits Ω) [IsAlgClosed Ω] {n : ℕ} (hn : n ≠ 0) :
    ∃ y : DiscreteUnits Ω, n • y = x := by
  -- an `n`-th root of `x` in the field is again a unit
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (x.toMul : Ω) hn.pos
  exact ⟨Additive.ofMul (Units.ofPow x.toMul z hn hz), ext hz⟩

end New.DiscreteUnits

/-!
## Cup products, Hom modules and orders of annihilators

Orders are `Nat.card`, which is `0` for infinite groups.

* `New.DiscreteModule.cartierDual`: additive maps `M → Ωˣ` for finite `M`, with
  `g • f = g ∘ f ∘ g⁻¹`.
-/

namespace New

open Function AddSubgroup QuotientAddGroup AddMonoidHom DFunLike Nat DiscreteModule

variable {R R' S : Type}
  (Γ : Type) [CommRing R] [CommRing R'] [CommRing S] [Group Γ] [TopologicalSpace Γ]
  {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [MulSemiringAction Γ Ω] [IsAlgClosed Ω]
  [IsProGalois Γ K Ω] {A B C : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- The multiplicative group Ω^×, written additively, as a discrete module with its continuous
action of Γ. -/
abbrev unitsModule : DiscreteModule ℤ Γ :=
  of (unitsRep (Γ := Γ) (Ω := Ω)) <|
    -- the orbit map of each unit is locally constant
    continuous_prod_of_discrete_right.2 fun x ↦
      ((isLocallyConstant_smul x.1).desc (fun g ↦ unitsRep g x) Units.val
        Units.val_injective).continuous

/-- Additive maps from a finite group `A` to `Ωˣ` (written additively) form a finite set. -/
instance [Finite A] : Finite (A →+ DiscreteUnits Ω) :=
  .of_equiv (Multiplicative A →* Ωˣ) toMultiplicativeLeft.symm

/-- For Ω algebraically closed, `Ωˣ` written additively is divisible by every non-zero integer,
since every unit has `n`-th roots (`New.DiscreteUnits.exists_nsmul`). -/
instance : DivisibleBy (DiscreteUnits Ω) ℤ :=
  @AddGroup.divisibleByIntOfDivisibleByNat _ _
    (divisibleByOfSMulRightSurj _ _ (swap (·.exists_nsmul)))

variable {Γ}
  (W : DiscreteModule S Γ) (M : DiscreteModule R Γ) (N : DiscreteModule R' Γ) (b : A →+ B →+ C)

/-! ### Annihilators -/

/-- For a biadditive pairing b : A × B → C and a subgroup L of A, the subgroup of y in B with
b(x, y) = 0 for all x in L. -/
def pairingAnnihilator (L : AddSubgroup A) : AddSubgroup B :=
  (b.comp (AddSubgroup.subtype L)).flip.ker.copy {y : B | ∀ x ∈ L,
    b x y = 0} (by aesop (add simp ext_iff))

/-- Let `β : A × B → C` be biadditive and let `e` identify ℚ/ℤ (`New.QZ`) with `C`. The index in
`B` of the right kernel `{y | ∀ x, β x y = 0}` divides the index in `A` of the left kernel
`{x | ∀ y, β x y = 0}`. -/
lemma index_ker_flip_dvd (e : QZ ≃+ C) (β : A →+ B →+ C) : β.flip.ker.index ∣ β.ker.index := by
  by_cases! h_inf : Infinite (A ⧸ β.ker)
  · -- an infinite index is `0`, which every number divides
    simp [index_eq_zero_iff_infinite.mpr h_inf]
  -- `f` maps `B` to the dual of the finite group `A ⧸ β.ker`, which has `β.ker.index` elements
  let f : B →+ (A ⧸ β.ker →+ QZ) := (kerLift β).flip.compr₂ e.symm
  have h_ker_le : f.ker ≤ β.flip.ker := fun y hy ↦ by simpa [f, ext_iff, forall_mk] using hy
  calc
    β.flip.ker.index ∣ f.ker.index := index_dvd_of_le h_ker_le
    _ ∣ Nat.card (A ⧸ β.ker →+ QZ) := card_dvd_of_injective (kerLift f) (kerLift_injective f)
    _ = β.ker.index := card_hom_QZ (A ⧸ β.ker)

/-- Let `b : A × B → C` be biadditive and let `e` identify ℚ/ℤ (`New.QZ`) with `C`. For a subgroup
`L` of `A` with annihilator `L^⊥ = pairingAnnihilator b L` in `B`,
`#L^⊥ · #L = #B · #(L ∩ left kernel of b)`, where `#` is `Nat.card` (`0` for infinite groups). -/
lemma card_pairingAnnihilator_mul_card (b : A →+ B →+ C) (e : QZ ≃+ C) (L : AddSubgroup A) :
    Nat.card (pairingAnnihilator b L) * Nat.card L = Nat.card B * Nat.card ↥(b.ker ⊓ L) := by
  -- Restrict `b` to `β : L × B → C`. Its two kernels have the same index (duality), the right
  -- kernel is the annihilator, and the left kernel is `b.ker ⊓ L` seen inside `L`.
  let β : L →+ B →+ C := b.comp L.subtype
  have h_index : β.flip.ker.index = b.ker.relIndex L :=
    dvd_antisymm (index_ker_flip_dvd e β) (index_ker_flip_dvd e β.flip)
  have h_left : Nat.card ↥(b.ker ⊓ L) * b.ker.relIndex L = Nat.card L := by
    simpa only [bot_inf_eq, relIndex_bot_left] using relIndex_inf_mul_relIndex ⊥ b.ker L
  rw [show pairingAnnihilator b L = β.flip.ker from β.flip.ker.copy_eq _ _, ← h_left,
    ← β.flip.ker.card_mul_index, h_index]
  ring

/-! ### Hom modules and cup products -/

/-- Additive maps between two groups carry the discrete topology. -/
instance : TopologicalSpace (A →+ B) := ⊥

instance : DiscreteTopology (A →+ B) := ⟨rfl⟩

/-- For a finite discrete Γ-module `M`, the discrete Γ-module `Hom(M, Ω^×)` of additive maps to
`New.unitsModule`, on which `g` acts by `(g f)(m) = g f(g⁻¹ m)`. -/
abbrev DiscreteModule.cartierDual [Finite M] : DiscreteModule ℤ Γ :=
  let W : DiscreteModule ℤ Γ := unitsModule Γ
  of (V := M →+ W)
      -- `g` sends `f` to `g ∘ f ∘ g⁻¹`.
      { toFun g :=
          toIntLinearMap
            (AddMonoidHom.mk'
              (fun f : M →+ W ↦ AddMonoidHom.comp (W.ρ g) (AddMonoidHom.comp f (M.ρ g⁻¹)))
              (by simp [ext_iff]))
        map_one' := by simp [ext_iff]
        map_mul' := by simp [ext_iff] } <| by
    -- A map from the finite set `M` is a finite tuple of values, each continuous in `g`.
    refine .congr ?_ fun _ ↦ leftInverse_invFun coe_injective _
    simp [continuous_prod_of_discrete_right]
    fun_prop

variable (b : M →+ N →+ W)
  (e : ∀ (g : Γ) (x : M.V) (y : N.V), b (M.ρ g x) (N.ρ g y) = W.ρ g (b x y))

/-- Let `M`, `N`, `W` be discrete Γ-modules and `b : M × N → W` a biadditive pairing that is
equivariant: `e` says `b (g x) (g y) = g (b x y)`. The cup product `Z¹(M) × Z¹(N) → H²(W)` sends
1-cocycles `x`, `y` to the class of the 2-cocycle `(g, h) ↦ b (x g) (g (y h))`. -/
def cupProduct : Z1 M.ρ →+ Z1 N.ρ →+ W.H2 :=
  (AddMonoidHom.mk'
      (fun x : Z1 M.ρ ↦
        AddMonoidHom.mk'
          (fun y : Z1 N.ρ ↦
            (⟨fun p ↦ b (x.1 p.1) (N.ρ p.1 (y.1 p.2)), by
              obtain ⟨hx_cont, hx⟩ := x.2
              obtain ⟨hy_cont, hy⟩ := y.2
              -- The cocycle identities and `e` make the terms cancel in pairs.
              exact ⟨by fun_prop, fun g h k ↦ by simp [hx, hy, ← e]⟩⟩ : Z2 W.ρ))
          (by simp [funext_iff]))
      (by simp [ext_iff, funext_iff])).compr₂ (QuotientAddGroup.mk' _)

/-- For a finite discrete Γ-module `M`, the cup product `Z¹(Hom(M, Ω^×)) × Z¹(M) → H²(Ω^×)` of the
evaluation pairing `(f, m) ↦ f m` (`Hom(M, Ω^×)` is `New.DiscreteModule.cartierDual`). -/
abbrev DiscreteModule.evalCup [Finite M] :
    ↥(Z1 M.cartierDual.ρ) →+ ↥(Z1 M.ρ) →+ (unitsModule Γ).H2 :=
  cupProduct (unitsModule Γ) M.cartierDual M (AddMonoidHom.id M.cartierDual.V) (by simp)

/-- Anticommutativity of the cup product. Let `Γ` be a group with a topology and let `W`, `M`, `N`
be discrete Γ-modules (`New.DiscreteModule`: a discrete module `V` with a continuous linear action
`ρ` of `Γ`). Let `b : M × N → W` be biadditive and equivariant, `b (g m) (g n) = g (b m n)`. Let
`x` and `y` be continuous 1-cocycles (`New.Z1`) with values in `M` and `N`. The cup product
`New.cupProduct W M N b h_equivariant x y` is the class in `H²(Γ, W)` of the 2-cocycle
`(g, h) ↦ b (x g) (g (y h))`. The flipped pairing `b.flip : (n, m) ↦ b m n` is equivariant too,
and the cup product of `y` and `x` for `b.flip` is minus the cup product of `x` and `y` for `b`. -/
lemma cupProduct_flip {R R' S Γ : Type} [CommRing R] [CommRing R'] [CommRing S] [Group Γ]
    [TopologicalSpace Γ] {W : DiscreteModule S Γ} {M : DiscreteModule R Γ}
    {N : DiscreteModule R' Γ} (b : M →+ N →+ W)
    (h_equivariant : ∀ (g : Γ) (m : M.V) (n : N.V), b (M.ρ g m) (N.ρ g n) = W.ρ g (b m n))
    (x : Z1 M.ρ) (y : Z1 N.ρ) :
    cupProduct W N M b.flip (fun (g : Γ) (n : N.V) (m : M.V) ↦ h_equivariant g m n) y x =
      -cupProduct W M N b h_equivariant x y := by
  obtain ⟨x, hx_cont : Continuous x,
    hx_mul : ∀ g h : Γ, x (g * h) = x g + M.ρ g (x h)⟩ := x
  obtain ⟨y, hy_cont : Continuous y,
    hy_mul : ∀ g h : Γ, y (g * h) = y g + N.ρ g (y h)⟩ := y
  -- the sum of the two cup products is the coboundary of `g ↦ -b (x g) (y g)`
  refine (Submodule.Quotient.eq _).mpr ⟨fun g ↦ -b (x g) (y g), by fun_prop, fun g h ↦ ?_⟩
  -- expand `b (x (g * h)) (y (g * h))` by the cocycle identities and `h_equivariant`
  have h_expand : b (x (g * h)) (y (g * h)) = b (x g) (y g) + b (x g) (N.ρ g (y h))
      + b (M.ρ g (x h)) (y g) + W.ρ g (b (x h) (y h)) := by
    simp only [hx_mul, hy_mul, map_add, AddMonoidHom.add_apply, h_equivariant]
    abel
  -- the coboundary condition at `(g, h)`, with both cup products written out
  show b.flip (y g) (M.ρ g (x h)) - -b (x g) (N.ρ g (y h))
      = W.ρ g (-b (x h) (y h)) - -b (x (g * h)) (y (g * h)) + -b (x g) (y g)
  rw [AddMonoidHom.flip_apply, h_expand, map_neg]
  abel

end New

/-! ## Galois descent from a subgroup of finite index -/

section GaloisDescentSpan

open Submodule Subgroup FixedPoints QuotientGroup Quotient MulDistribMulAction MulAction Pi

/-- Galois descent. Let `G` act on the field `A`, let `τ` be semilinear along `j : Γ →* G`, and let
`U` have finite index in `G` and be the fixer of its own fixed scalars. A vector `y` fixed by every
`g` with `j g ∈ U` lies in the `A`-span of the vectors fixed by all of `Γ`. -/
lemma New.Period.mem_span_fixed {G Γ A V R : Type*} [Group G] [Group Γ] [Field A]
    [AddCommGroup V] [Module A V] [MulSemiringAction G A] [Semiring R] [Module R V] (j : Γ →* G)
    {U : Subgroup G} [Finite (G ⧸ U)] (τ : Representation R Γ V)
    (h_semilin : ∀ (g : Γ) (a : A) (x : V), τ g (a • x) = (j g • a) • τ g x) {y : V}
    (hy : ∀ g : Γ, j g ∈ U → τ g y = y) (h_fixer : fixingSubgroup G (fixedPoints U A) ≤ U) :
    y ∈ span A {x : V | ∀ g : Γ, τ g x = x} := by
  classical
  -- Let `q` run over the cosets of `U' = j⁻¹ U`, and let `Λ` send coefficients `c` to
  -- `∑ q, c q • τ q y`. The vectors `(j q • b)_q`, for `U`-fixed scalars `b`, span all coefficients
  -- and go to invariant vectors; the unit vector at the trivial coset goes to `y`.
  set U' : Subgroup Γ := U.comap j
  have h_fintype : Fintype (Γ ⧸ U') := fintypeOfIndexNeZero ((U.index_comap j).trans_ne
    (mt index_eq_zero_of_relIndex_eq_zero index_ne_zero_of_finite))
  let Λ : (Γ ⧸ U' → A) →ₗ[A] V := (basisFun A _).constr A fun q ↦ τ q.out y
  let χ (q : Γ ⧸ U') : submonoid U A →* A := (toMonoidHom A (j q.out)).domRestrict _
  -- Representatives with the same character differ by an element whose image under `j` fixes
  -- all `U`-fixed scalars, so by an element of `U'`.
  have χ_inj : χ.Injective := by
    intro q r h_eq
    have h_fix : j (q.out⁻¹ * r.out) ∈ fixingSubgroup G (fixedPoints U A) := by
      refine (mem_fixingSubgroup_iff G).mpr fun b hb ↦ ?_
      rw [map_mul, map_inv, mul_smul, inv_smul_eq_iff]
      simpa [χ] using (DFunLike.congr_fun h_eq ⟨b, hb⟩).symm
    exact out_equiv_out.mp (leftRel_apply.mpr (mem_comap.mpr (h_fixer h_fix)))
  -- Dedekind's lemma: distinct characters are linearly independent.
  have h_span : span A (.range fun (b : submonoid U A) (q : Γ ⧸ U') ↦ χ q b) = ⊤ :=
    span_flip_eq_top_iff_linearIndependent.mpr ((linearIndependent_monoidHom _ A).comp χ χ_inj)
  -- The image of `(j q • b)_q` is the trace `∑ q, τ q (b • y)`, unchanged by left translation.
  have h_trace (b : submonoid U A) (g : Γ) : τ g (Λ fun q ↦ χ q b) = Λ fun q ↦ χ q b := by
    have h_Λ : (Λ fun q ↦ χ q b) = ∑ q : Γ ⧸ U', τ q.out ((b : A) • y) := by
      simp [Λ, χ, h_semilin]
    -- `γ ↦ τ γ (b • y)` is right `U'`-invariant, since `U'` fixes both `b` and `y`
    have h_right_inv : ∀ᵉ (x : Γ) (u ∈ U'), τ (x * u) ((b : A) • y) = τ x ((b : A) • y) := by
      intro x u hu
      have h_b_fixed : j u • (b : A) = b := b.property ⟨j u, hu⟩
      rw [map_mul, Module.End.mul_apply, h_semilin u, h_b_fixed, hy u hu]
    calc τ g (Λ fun q ↦ χ q b) = ∑ q : Γ ⧸ U', τ (g * q.out) ((b : A) • y) := by simp [h_Λ]
      _ = ∑ q : Γ ⧸ U', τ q.out ((b : A) • y) :=
          sum_mul_out U' (fun γ : Γ ↦ τ γ ((b : A) • y)) h_right_inv g
      _ = Λ fun q ↦ χ q b := h_Λ.symm
  have h_one : Λ (single ⟦1⟧ 1) = y := by
    obtain ⟨⟨u, hu⟩, h_out⟩ := mk_out_eq_mul U' 1
    simpa [Λ, h_out] using hy u hu
  -- The vectors `(χ q b)_q` span everything and go to invariants, so `y = Λ (single ⟦1⟧ 1)` is
  -- in the span of the invariants.
  have h_image_le : (span A (.range fun (b : submonoid U A) (q : Γ ⧸ U') ↦ χ q b)).map Λ ≤
      span A {x : V | ∀ g : Γ, τ g x = x} :=
    (map_span_le Λ _ _).mpr (Set.forall_mem_range.mpr fun b ↦ subset_span (h_trace b))
  exact h_image_le ⟨single ⟦1⟧ 1, h_span.ge Submodule.mem_top, h_one⟩

end GaloisDescentSpan

/-!
## Hilbert 90, Kummer cocycles and their cup products

`Ωˣ` is written additively (`New.DiscreteUnits`), so `n • a` is `a ^ n` and `g a - a` is `g a / a`;
`New.unitsModule Γ` is `Ωˣ` as a discrete `Γ`-module, with the action `New.unitsRep`. `New.Z1` of a
trivial module consists of the continuous homomorphisms.
-/

namespace New

open DFunLike Set Submodule DistribSMul Function QZ DiscreteUnits QZChar IntermediateField Period
  DiscreteModule NeZero

variable {Γ K Ω : Type _} [Group Γ] [TopologicalSpace Γ] [Field K] [Field Ω] [Algebra K Ω]
  [MulSemiringAction Γ Ω] [IsProGalois Γ K Ω]
  (f : Z1 (unitsRep (Γ := Γ) (Ω := Ω)))

/-- The fixed field of a normal subgroup `U` of `Γ` is Galois over `K`. -/
instance isGalois_fixedFieldOf (U : Subgroup Γ) [U.Normal] : IsGalois K (fixedFieldOf U) where
  to_normal := by
    -- Each automorphism comes from some `g` in `Γ`, and `g` preserves the fixed field of the
    -- normal subgroup `U`.
    refine normal_iff_forall_map_le'.mpr ((toAlgAut_surjective Γ).forall.mpr fun g ↦ ?_)
    exact image_subset_iff.mpr fun _ hx ↦ smul_mem_fixedPoints_of_normal g hx

/-- The cup product of a Kummer cocycle with a character mod `n`. Let `w` in `Ωˣ` be `Γ`-invariant
with `a ^ n = w`, and let `ξ : Γ → ℤ/n` be a continuous homomorphism. If the 2-cocycle `z` is
`(g, h) ↦ (g a / a) ^ ξ(h)`, then its class is minus the symbol `(ξ / n, w)`. Here
`New.QZChar.ofZModCocycle n ξ` is the character `ξ / n : Γ → ℚ/ℤ`, and `New.cyclicClass ρ χ w` is
the class of `(g, h) ↦ carry(χ(g), χ(h)) • w`. -/
lemma mk_eq_neg_cyclicClass_ofZModCocycle {n : ℕ} [NeZero n]
    {w : ↥(unitsRep (Γ := Γ) (Ω := Ω)).invariants} {a : DiscreteUnits Ω} (ha : n • a = ↑w)
    (ξ : ↥(Z1 (Representation.trivial ℤ Γ (ZMod n)))) (z : Z2 (unitsRep (Γ := Γ) (Ω := Ω)))
    (hz : ∀ g h : Γ, z.val (g, h) = (ξ.val h).val • (unitsRep g a - a)) :
    ⟦z⟧ = -cyclicClass (unitsRep (Γ := Γ) (Ω := Ω)) (ofZModCocycle n ξ) w := by
  -- `z` plus the cocycle `(g, h) ↦ carry (ξ g / n) (ξ h / n) • w` of the cyclic class is the
  -- coboundary of `g ↦ (ξ g).val • a`.
  obtain ⟨hξ_cont, hξ_cocycle⟩ := ξ.property
  refine (Submodule.Quotient.eq _).mpr
    ⟨(fun k : ZMod n ↦ k.val • a) ∘ ξ.val, continuous_bot.comp hξ_cont, fun g h ↦ ?_⟩
  -- `n` times the carry of `x / n` and `y / n` is the carry in the addition of residues mod `n`.
  have carry_eq (x y : ZMod n) :
      (ofZMod n x).carry (ofZMod n y) * n = x.val + y.val - (x + y).val := by
    qify [← map_add]
    grind [ofZMod_apply, fracRep_mk, NeZero.natCast_ne, Int.fract_div_natCast_eq_div_natCast_mod,
      Nat.mod_eq_of_lt]
  -- Write `w = n • a` and `ξ (g * h) = ξ g + ξ h`, then compare the coefficients of `g a` and `a`.
  suffices h_coeff : (ξ.val h).val • (unitsRep g a - a) +
      (ofZMod n (ξ.val g)).carry (ofZMod n (ξ.val h)) • n • a =
    (ξ.val h).val • unitsRep g a - (ξ.val g + ξ.val h).val • a + (ξ.val g).val • a by
    simpa [hz, ofZModCocycle, hξ_cocycle, ← ha] using h_coeff
  linear_combination (norm := module) carry_eq (ξ.val g) (ξ.val h) • a

include K

/-- Hilbert's Theorem 90. Let `Γ` act on `Ω` as the Galois group of `Ω / K` (`New.IsProGalois`).
Every continuous 1-cocycle `f` of `Γ` with values in `Ωˣ` is a coboundary: `f g = g m / m` for some
`m`, written additively as `unitsRep g m - m`. -/
lemma hilbert90_unitsRep : ∃ m : DiscreteUnits Ω, ∀ g : Γ, f.val g = unitsRep g m - m := by
  obtain ⟨hf_cont, hf_cocycle⟩ : Continuous f.val ∧
      ∀ g h : Γ, f.val (g * h) = f.val g + unitsRep g (f.val h) := f.property
  -- The continuous map `f` to a discrete space is constant on an open normal subgroup `U`. (The
  -- lemma is stated for maps on `Γ × Y`; here the second factor `Y = Γ` is not used.)
  obtain ⟨U, hU_const⟩ := exists_openNormalSubgroup_apply_eq (Y := Γ) hf_cont.fst'
  have hU (u : Γ) (hu : u ∈ U) : f.val u = 0 :=
    (hU_const u hu 1).trans (by simpa using hf_cocycle 1 1)
  -- The action `x ↦ f g * g • x` on `Ω` is semilinear, and `U` fixes `1`.
  let τ : Representation ℤ Γ Ω :=
    { toFun g := ((f.val g).toMul : Ω) • toLinearMap ℤ Ω g
      map_one' := by aesop
      map_mul' := by simp [ext_iff, hf_cocycle, mul_smul] }
  have τ_smul (g : Γ) (c y : Ω) : τ g (c • y) = (g • c) • τ g y := by simp [τ, field]
  have τ_one_of_mem (g : Γ) (hg : g ∈ (U : Subgroup Γ)) : τ g 1 = 1 := by simp [τ, hU g hg]
  -- By Galois descent a vector fixed by `U` lies in the `Ω`-span of the `τ`-invariant vectors. So
  -- there is an invariant `x ≠ 0`, and `f g * g • x = x` makes `f` the coboundary of `x⁻¹`.
  have one_mem : (1 : Ω) ∈ span Ω {y : Ω | ∀ g : Γ, τ g y = y} :=
    mem_span_fixed (MonoidHom.id Γ) τ τ_smul τ_one_of_mem
      (fixingSubgroup_fixedFieldOf (U : Subgroup Γ)).le
  obtain ⟨x, hx, hx0⟩ : ∃ x : Ω, (∀ g : Γ, τ g x = x) ∧ x ≠ 0 := by
    by_contra! h
    exact one_ne_zero ((mem_bot Ω).mp (mem_span.mp one_mem ⊥ h))
  refine ⟨-DiscreteUnits.ofNeZero x hx0, fun g ↦ ?_⟩
  -- In `Ω` the goal reads `f g = x / g • x`.
  have h_val : ((f.val g).toMul : Ω) = x / g • x :=
    (eq_div_iff ((smul_ne_zero_iff_ne g).mpr hx0)).mpr (hx g)
  simpa [DiscreteUnits.ext_iff, field] using h_val

/-- Kummer cocycle. Let `Ω` be algebraically closed of characteristic 0, and let `Γ`, the Galois
group of `Ω / K`, fix the `n`-th roots of unity (`h_cyc`: the cyclotomic character mod `n` is
trivial). For `x` in `Ωˣ` fixed by `Γ` there are an `n`-th root `a` of `x` and a continuous
homomorphism `f : Γ → ℤ/n` such that `g b / b = ζ ^ f(g)` for every `n`-th root `b` of `x`. Here
`ζ ^ k` is `New.rootPowHom Ω n k`, for a chosen primitive `n`-th root of unity `ζ`. -/
lemma exists_kummer_cocycle [IsAlgClosed Ω] [CharZero Ω] {n : ℕ} [NeZero n]
    (h_cyc : ∀ g : Γ, cyclotomicCharMod Ω n g = 1) (x : (unitsModule Γ).H0) :
    ∃ᵉ (a : (unitsModule Γ).V) (f : ↥(Z1 (Representation.trivial ℤ Γ (ZMod n)))),
      n • a = x.val ∧
      ∀ b : (unitsModule Γ).V, n • b = x.val → ∀ g : Γ,
        (rootPowHom Ω n).val (f.val g) = unitsRep g b - b := by
  let μ : ZMod n →+ DiscreteUnits Ω := (rootPowHom Ω n).val
  obtain ⟨hμ_inj, hμ_range⟩ : Injective μ ∧ ∀ y : DiscreteUnits Ω, y ∈ μ.range ↔ n • y = 0 :=
    (rootPowHom Ω n).property
  obtain ⟨a, ha⟩ : ∃ a : DiscreteUnits Ω, n • a = x.val := exists_nsmul x.val (NeZero.ne n)
  -- `Γ` fixes the `n`-th roots of unity.
  have h_fix (g : Γ) (y : DiscreteUnits Ω) (hy : n • y = 0) : unitsRep g y = y :=
    cyclotomicCharMod_eq_one_iff.mp (h_cyc g) y hy
  -- The coboundary `c g = g a - a` is a continuous cocycle killed by `n`, as `x` is invariant.
  set c : Z1 (unitsModule Γ).ρ := coboundary (unitsModule Γ) a
  obtain ⟨hc_cont, hc_cocycle⟩ : Continuous c.val ∧
      ∀ g h : Γ, c.val (g * h) = c.val g + unitsRep g (c.val h) := c.property
  have hc (g : Γ) : c.val g = unitsRep g a - a := rfl
  have hc_torsion (g : Γ) : n • c.val g = 0 := by
    rw [hc, smul_sub, ← map_nsmul, ha, x.property g, sub_self]
  -- So it has a logarithm along `μ`, and the logarithm is a homomorphism, since `Γ` fixes the
  -- root of unity `c h`.
  have h_log (g : Γ) : μ (invFun μ (c.val g)) = c.val g :=
    invFun_eq ((hμ_range _).mpr (hc_torsion g))
  have h_log_mul (g h : Γ) :
      invFun μ (c.val (g * h)) = invFun μ (c.val g) + invFun μ (c.val h) :=
    hμ_inj (by rw [map_add, h_log, h_log, h_log, hc_cocycle, h_fix g _ (hc_torsion h)])
  refine ⟨a, ⟨invFun μ ∘ c.val, continuous_bot.comp hc_cont, fun g h ↦ ?_⟩, ha, fun b hb g ↦ ?_⟩
  · -- The cocycle condition for the trivial action on `ℤ/n` says that `f` is a homomorphism.
    simpa only [comp_apply, Representation.trivial_apply] using h_log_mul g h
  · -- Another root `b` differs from `a` by a root of unity, so it has the same coboundary.
    have h_diff : unitsRep g (a - b) = a - b := h_fix g _ (by simp [smul_sub, ha, hb])
    have h_cob_eq : unitsRep g a - a = unitsRep g b - b := by
      rwa [map_sub, sub_eq_sub_iff_sub_eq_sub] at h_diff
    calc (rootPowHom Ω n).val ((invFun μ ∘ c.val) g) = c.val g := h_log g
      _ = unitsRep g a - a := hc g
      _ = unitsRep g b - b := h_cob_eq

end New

/-!
## Symbols of cyclic extensions and norms

Let `χ : Γ → ℚ/ℤ` be a continuous character with kernel `U`. The proofs use Hilbert's Theorem 90
(`New.hilbert90_unitsRep`) for `U` and Shapiro's lemma.
-/

section CyclicNorm

namespace New

open QZChar DiscreteUnits DiscreteModule Algebra IsGalois Function Quotient QuotientGroup
  MulSemiringAction

variable {Γ K Ω L : Type} [Group Γ] [TopologicalSpace Γ] [Field K] [Field Ω] [Algebra K Ω]
  [MulSemiringAction Γ Ω] [IsProGalois Γ K Ω] [Field L] [Algebra K L] [Algebra L Ω]
  [IsScalarTower K L Ω]

include K in
/-- Let `U` be the closed subgroup of `Γ` of the elements that fix `L`, embedded in `Ω` by
`algebraMap L Ω`. Then `U` acts on `Ω` as the Galois group of `Ω / L` (`New.IsProGalois`). -/
lemma IsProGalois.of_fixingSubgroup_eq {U : Subgroup Γ}
    (hU : fixingSubgroup Γ (Set.range (algebraMap L Ω)) = U) [IsClosed (U : Set Γ)] :
    IsProGalois U L Ω := by
  -- The topological conditions come from the closed subgroup `U` as the Galois group of its
  -- fixed field; it remains to see that `U` fixes `L` and that its fixed field is not larger.
  have h_fix : IsProGalois U (fixedFieldOf U) Ω := inferInstance
  subst hU
  refine { tower_top_of_isGalois K L Ω, h_fix with
    commutes.smul_comm := ?_, isInvariant.isInvariant := ?_ }
  · -- Elements of `U` fix `L`, so they commute with multiplication by elements of `L`.
    show ∀ (u : fixingSubgroup Γ (Set.range (algebraMap L Ω))) (l : L) (y : Ω),
      u • l • y = l • u • y
    simp_all [smul_def, mem_fixingSubgroup_iff]
  · exact (fixedFieldOf_fixingSubgroup (IsScalarTower.toAlgHom K L Ω).fieldRange).le

open LinearMap Mathlib.Tactic.LinearCombination QZ Submodule Group

attribute [local instance low] Fintype.ofFinite

/-- Let `f` be an injective homomorphism from a finite group `Q` to `ℚ/ℤ` (written
multiplicatively). There is `γ` in `Q` such that the carry of `f q` and `f γ` is `0` for `q = 1` and
`1` for every other `q`: take for `γ` the element whose value has the largest representative in
`[0, 1)`. -/
lemma exists_carry_eq_one_sub_ite {Q : Type*} [Group Q] [Finite Q] [DecidableEq Q]
    (f : Q →* Multiplicative QZ) (hf : Injective f) :
    ∃ γ : Q, ∀ q : Q, carry (f q).toAdd (f γ).toAdd = 1 - if q = 1 then 1 else 0 := by
  obtain ⟨γ, hγ⟩ : ∃ γ : Q, ∀ q : Q, (f q).toAdd.fracRep ≤ (f γ).toAdd.fracRep :=
    Finite.exists_max fun q ↦ (f q).toAdd.fracRep
  refine ⟨γ, fun q ↦ ?_⟩
  -- Both sides are integers, and by the choice of `γ` they differ by less than `1`.
  have hγ_q : (f (q * γ)).toAdd.fracRep ≤ (f γ).toAdd.fracRep := hγ (q * γ)
  suffices h_abs : |carry (f q).toAdd (f γ).toAdd - (1 - if q = 1 then 1 else 0)| < 1 from
    sub_eq_zero.mp (Int.abs_lt_one_iff.mp h_abs)
  qify
  grind [mul_eq_right, QZ.fracRep, Equiv.injective, toAdd_mul]

include K in
/-- Hilbert 90 for functions on cosets: for an open subgroup `U` of `Γ`, every continuous
1-cocycle with values in the functions `Γ ⧸ U → Ωˣ` is a coboundary. By Shapiro's lemma this is
Hilbert 90 for `U`. -/
private lemma hilbert90_funModule (U : OpenSubgroup Γ)
    (F : Z1 ((unitsModule Γ).funModule U.toSubgroup).ρ) :
    ∃ n : ((unitsModule Γ).funModule U.toSubgroup).V,
      ∀ g : Γ, F.val g = ((unitsModule Γ).funModule U.toSubgroup).ρ g n - n :=
  (hilbert90_unitsRep ((unitsModule Γ).shapiroZ1 U F)).elim (shapiro_H1 U F)

/-- The classes that vanish on the kernel of a character are symbols. Let `Γ` be the profinite
Galois group of the extension `Ω/K` (`IsProGalois`), and `H²(Γ, Ωˣ)` the continuous cohomology of
`Ωˣ`, written additively. Let `χ : Γ → ℚ/ℤ` be a continuous character with kernel `U`, an open
subgroup of `Γ`. If a class `x` in `H²(Γ, Ωˣ)` restricts to zero on `U`, then `x` is the symbol
`(χ, w)` (`New.cyclicClass`) of some `w` in `Kˣ`, where `w` is embedded in `Ωˣ` by
`New.DiscreteUnits.ofBase`. -/
lemma QZChar.exists_eq_cyclicClass_of_resH2_eq_zero (χ : ↥(QZChar Γ)) (x : (unitsModule Γ).H2)
    (hx : (unitsModule Γ).resH2 (OpenSubgroup.mk (ker χ) (isOpen_ker χ)) x = 0) :
    ∃ w : Kˣ, x = cyclicClass unitsRep χ (DiscreteUnits.ofBase Γ Ω (Additive.ofMul w)) := by
  classical
  -- By Shapiro's lemma a cocycle `z` of the class `x`, with values in the constant functions
  -- `Γ ⧸ U → Ωˣ`, is the coboundary of some `a`. The difference operator `D` along a suitable coset
  -- `γ` makes `D ∘ a` a 1-cocycle, by Hilbert 90 the coboundary of some `ε`, and `x` is the symbol
  -- of the sum of `ε` over `Γ ⧸ U`.
  let U : OpenSubgroup Γ := OpenSubgroup.mk (ker χ) (isOpen_ker χ)
  have h_finite : Finite (Γ ⧸ U.toSubgroup) := U.toSubgroup.quotient_finite_of_isOpen U.isOpen
  -- `f` is the injective character of `Γ ⧸ U` induced by `χ`; the symbol has cocycle `c g l • w`.
  let f (q : Γ ⧸ U.toSubgroup) : QZ := (kerLift (toHom χ) q).toAdd
  let c (p q : Γ ⧸ U.toSubgroup) : ℤ := carry (f p) (f q)
  have χ_eq (g : Γ) : χ.val g = f g := rfl
  have smul_eq (g : Γ) (q : Γ ⧸ U.toSubgroup) : g • q = mk' U g * q := rfl
  obtain ⟨γ, carry_max⟩ :
      ∃ γ : Γ ⧸ U.toSubgroup, ∀ q : Γ ⧸ U.toSubgroup, c q γ = 1 - if q = 1 then 1 else 0 :=
    exists_carry_eq_one_sub_ite _ (kerLift_injective (toHom χ))
  have carry_cocycle (p q r : Γ ⧸ U.toSubgroup) :
      c p (q * r) = c p q - (c q r - c (p * q) r) := by
    qify [c]
    grind [toAdd_mul]
  let M : DiscreteModule ℤ Γ := unitsModule Γ
  let N : DiscreteModule ℤ Γ := M.funModule U.toSubgroup
  -- `D F q = F (q * γ) - F q`
  let D : (Γ ⧸ U.toSubgroup → M) →ₗ[ℤ] Γ ⧸ U.toSubgroup → M := funLeft ℤ M (fun q ↦ q * γ) - 1
  have sum_shift (F : Γ ⧸ U.toSubgroup → M) : ∑ q, F (q * γ) = ∑ q, F q :=
    (mulRight_bijective γ).sum_comp F
  obtain ⟨z, rfl⟩ : ∃ z : Z2 M.ρ, ⟦z⟧ = x := Quot.exists_rep x
  -- The cocycle `z` dies on `U`, so with values in the functions it is the coboundary of some `a`.
  obtain ⟨a, a_cont : Continuous a,
      ha : ∀ g l : Γ, (fun _ ↦ z.val (g, l)) = N.ρ g (a l) - a (g * l) + a g⟩ :=
    (ker_mkQ _).le (shapiroH2_injective U (a₁ := (M.const U).mapH2 ⟦z⟧) hx)
  -- `D` kills the constant left side of `ha`, so `D ∘ a` is a 1-cocycle, hence a coboundary.
  have Da_cocycle (g l : Γ) : D (a (g * l)) = D (a g) + N.ρ g (D (a l)) := by
    funext q
    have hD_ha : D (fun _ ↦ z.val (g, l)) q = D (N.ρ g (a l) - a (g * l) + a g) q := by rw [ha g l]
    linear_combination (norm :=
      (simp [N, D, smul_eq, mul_assoc, sub_eq_zero]
       abel)) hD_ha
  -- Hilbert 90 for `U`, with Shapiro's lemma.
  obtain ⟨ε, hε : ∀ g : Γ, D (a g) = N.ρ g ε - ε⟩ :=
    hilbert90_funModule (K := K) U ⟨D ∘ a, by fun_prop, Da_cocycle⟩
  -- The sum of `D (a g)` is zero, so the sum of `ε` is invariant: it comes from `Kˣ`.
  have sum_invariant : M.sum U ε ∈ M.H0 := fun g : Γ ↦ by
    rw [← (M.sum U).isIntertwining, ← sub_eq_zero, ← map_sub, ← hε]
    simp [D, sum_shift, sum]
  obtain ⟨w, hw⟩ := (ofBase_bijective (K := K) Γ).surjective ⟨M.sum U ε, sum_invariant⟩
  -- `z` differs from the cocycle of the symbol of `M.sum U ε` by the coboundary of
  -- `g ↦ a g γ - g (s g)`.
  let s (g : Γ) : M := M.sum U (c g • ε)
  refine ⟨Additive.toMul w, ?_⟩
  rw [ofMul_toMul, hw]
  refine (Submodule.Quotient.eq _).mpr ⟨fun g ↦ a g γ - M.ρ g (s g), by fun_prop, fun g l ↦ ?_⟩
  -- Sum `hε l` against `c g`; summing by parts on the left, only `q = g⁻¹` and `q = 1` survive.
  have h_parts : ∑ q, c g q • D (a l) q = a l (g⁻¹ • γ) - a l γ := by
    linear_combination (norm :=
      simp [U, D, smul_eq, carry_cocycle, carry_max, smul_sub, mul_eq_one_iff_inv_eq, sub_smul])
      sum_shift (c g • a l)
  -- On the right, translate by `q ↦ l * q`.
  have h_translate : ∑ q, c g q • N.ρ l ε q = M.ρ l (c g l • M.sum U ε - s l + s (g * l)) := by
    rw [← (mulLeft_bijective (l : Γ ⧸ U.toSubgroup)).sum_comp]
    simp [N, s, carry_cocycle, smul_eq, Finset.smul_sum, sub_add, sub_smul, sum]
  -- `D (a l) = N.ρ l ε - ε` (`hε l`), and `s g` is the sum of `c g q • ε q`.
  have h_diff_eq : a l (g⁻¹ • γ) - a l γ = M.ρ l (c g l • M.sum U ε - s l + s (g * l)) - s g := by
    rw [← h_parts, ← h_translate, hε l]
    simp [N, s, smul_sub, sum]
  -- Evaluate `ha g l` at `γ` and replace `a l (g⁻¹ • γ)` by `h_diff_eq`.
  have ha_γ : z.val (g, l) = N.ρ g (a l) γ - a (g * l) γ + a g γ := congrFun (ha g l) γ
  linear_combination (norm :=
    (simp [N, c, χ_eq, sum, Finset.smul_sum, sub_eq_zero]
     abel)) ha_γ + c g l • sum_invariant (g * l) + congrArg (M.ρ g) h_diff_eq

include K in
/-- A symbol that vanishes is a norm. Let `Γ` be the profinite Galois group of the extension `Ω/K`
(`IsProGalois`), acting on `Ωˣ` (written additively), and let `χ : Γ → ℚ/ℤ` be a continuous
character with kernel `U`, an open subgroup of `Γ`. Let `w` be a `Γ`-invariant element of `Ωˣ`. If
the symbol `(χ, w)` (`New.cyclicClass`) is zero in `H²(Γ, Ωˣ)`, then `w` is the norm
`New.DiscreteModule.corestrictH0 U y` of some `U`-invariant element `y` of `Ωˣ`, that is, the sum of
`g y` over the cosets `gU`. -/
lemma QZChar.exists_corestrictH0_eq_of_cyclicClass_eq_zero (χ : ↥(QZChar Γ))
    (w : (unitsModule Γ).H0) (hw : cyclicClass (unitsModule Γ).ρ χ w = 0) :
    ∃ y : ↥((unitsModule Γ).restrictTo (OpenSubgroup.mk (ker χ) (isOpen_ker χ))).H0,
      corestrictH0 (OpenSubgroup.mk (ker χ) (isOpen_ker χ)) y = w.val := by
  classical
  -- If the symbol of `w` is the coboundary of `a`, a 1-cocycle `z` with values in the functions
  -- `Γ ⧸ U → Ωˣ` is built from `a`; by Hilbert 90 it is the coboundary of some `η`, and a
  -- `Γ`-invariant function built from `η` has sum `w`, which makes `w` a norm by Shapiro's lemma.
  let U : OpenSubgroup Γ := OpenSubgroup.mk (ker χ) (isOpen_ker χ)
  have h_finite : Finite (Γ ⧸ U.toSubgroup) := U.toSubgroup.quotient_finite_of_isOpen U.isOpen
  -- `f` is the injective character of `Γ ⧸ U` induced by `χ`; the symbol has cocycle `c g l • w`.
  let f (q : Γ ⧸ U.toSubgroup) : QZ := (kerLift (toHom χ) q).toAdd
  let c (p q : Γ ⧸ U.toSubgroup) : ℤ := carry (f p) (f q)
  have smul_eq (g : Γ) (q : Γ ⧸ U.toSubgroup) : g • q = mk' U g * q := rfl
  obtain ⟨γ, carry_max⟩ :
      ∃ γ : Γ ⧸ U.toSubgroup, ∀ q : Γ ⧸ U.toSubgroup, c q γ = 1 - if q = 1 then 1 else 0 :=
    exists_carry_eq_one_sub_ite _ (kerLift_injective (toHom χ))
  let M : DiscreteModule ℤ Γ := unitsModule Γ
  let N : DiscreteModule ℤ Γ := M.funModule U.toSubgroup
  -- `D F q = F (q * γ) - F q`
  let D : (Γ ⧸ U.toSubgroup → M) →ₗ[ℤ] Γ ⧸ U.toSubgroup → M := funLeft ℤ M (fun q ↦ q * γ) - 1
  have sum_shift (F : Γ ⧸ U.toSubgroup → M) : ∑ q, F (q * γ) = ∑ q, F q :=
    (mulRight_bijective γ).sum_comp F
  have carry_cocycle (p q r : Γ ⧸ U.toSubgroup) :
      c p (q * r) = c p q - (c q r - c (p * q) r) := by
    qify [c]
    grind [toAdd_mul]
  obtain ⟨a, a_cont : Continuous a,
      ha : ∀ g l : Γ, c g l • w.val = M.ρ g (a l) - a (g * l) + a g⟩ :=
    (ker_mkQ _).le hw
  have hw_fixed (g : Γ) : M.ρ g w.val = w.val := w.property g
  let z (g : Γ) (q : Γ ⧸ U.toSubgroup) : M := c g (g⁻¹ • q) • w.val - a g
  have z_cocycle (g l : Γ) : z (g * l) = z g + N.ρ g (z l) := by
    funext q
    have h_q : (l : Γ ⧸ U.toSubgroup) * (l⁻¹ • g⁻¹ • q) = g⁻¹ • q := by simp [smul_eq]
    -- `ha g l` and the carry cocycle at `(g, l, l⁻¹ • g⁻¹ • q)`
    linear_combination (norm :=
      (simp [z, N, h_q, hw_fixed, mul_smul, sub_smul]
       abel)) -ha g l - carry_cocycle g l (l⁻¹ • g⁻¹ • q) • w.val
  obtain ⟨η, hη : ∀ g : Γ, z g = N.ρ g η - η⟩ :=
    hilbert90_funModule (K := K) U ⟨z, by fun_prop, z_cocycle⟩
  -- By `carry_max` the function below is `w` at `q = 1` and `0` elsewhere, minus `D η`, so its
  -- sum is `w`. It is invariant, so its sum is a norm by `shapiro_H0`.
  have h_invariant : (fun q : Γ ⧸ U.toSubgroup ↦ w.val - c q γ • w.val) - D η ∈ N.H0 := by
    refine fun g ↦ funext fun q ↦ ?_
    have hD_hη : D (z g) q = D (N.ρ g η - η) q := by rw [hη g]
    -- `hη g` and the carry cocycle at `(g, g⁻¹ • q, γ)`
    linear_combination (norm :=
      (simp [z, N, D, smul_eq, mul_assoc, hw_fixed, sub_smul]
       abel)) hD_hη - carry_cocycle g (g⁻¹ • q) γ • w.val
  obtain ⟨y, hy⟩ : ∃ y : ↥(M.restrictTo U.toSubgroup).H0,
      (fun q : Γ ⧸ U.toSubgroup ↦ M.ρ q.out y) =
        (fun q : Γ ⧸ U.toSubgroup ↦ w.val - c q γ • w.val) - D η :=
    shapiro_H0 U ⟨_, h_invariant⟩
  -- Summing `hy` over the cosets: the left side is the norm of `y`, the right side is `w`.
  refine ⟨y, ?_⟩
  show M.sum U (fun q ↦ M.ρ q.out y) = w.val
  rw [hy]
  simp [U, D, carry_max, sum_shift, sum, sub_smul]

/-- Let `χ : Γ → ℚ/ℤ` be a continuous character and `U` its kernel, an open subgroup of `Γ`. A class
in `H²(Γ, Ωˣ)` dies on `U` exactly when it is a symbol `(χ, w)` with `w` in `Kˣ`; and for a
`Γ`-invariant `w` in `Ωˣ` the symbol `(χ, w)` is zero exactly when `w` is a norm
`New.DiscreteModule.corestrictH0 U y` of a `U`-invariant `y`. -/
lemma QZChar.cyclicClass_spec (χ : ↥(QZChar Γ)) :
    let U := OpenSubgroup.mk (ker χ) (isOpen_ker χ)
    -- (a) the classes that die on `U` are the symbols of `χ` with elements of `Kˣ`
    (∀ x : (unitsModule Γ).H2,
      (unitsModule Γ).resH2 U x = 0 ↔
        ∃ w : Kˣ, x = cyclicClass unitsRep χ (DiscreteUnits.ofBase Γ Ω (Additive.ofMul w))) ∧
    -- (b) a symbol of `χ` is zero exactly on the norms from `U`
    ∀ w : (unitsModule Γ).H0,
      cyclicClass (unitsModule Γ).ρ χ w = 0 ↔
        ∃ y : ↥((unitsModule Γ).restrictTo U).H0, corestrictH0 U y = w.val := by
  intro U
  refine ⟨fun x ↦ ⟨exists_eq_cyclicClass_of_resH2_eq_zero χ x, ?_⟩,
    fun w ↦ ⟨exists_corestrictH0_eq_of_cyclicClass_eq_zero (K := K) χ w, ?_⟩⟩
  · -- A symbol `(χ, w)` with `w` in `Kˣ` dies on `U`, which fixes `w` and kills `χ`.
    rintro ⟨w, rfl⟩
    refine resH2_cyclicClass_eq_zero (one_smul ℕ _) fun u : U.toSubgroup ↦ ?_
    exact ⟨(ofBase Γ Ω (.ofMul w)).property u, (one_smul ℕ (χ.val u)).trans u.property⟩
  · -- The symbol of `y` on `U` belongs to the zero character, so it is the restriction of the
    -- zero class, and the symbol of the norm of `y` is the index of `U` times that class.
    rintro ⟨y, hy⟩
    have h_zero : QZChar.comap (subgroupIncl U) χ = 0 :=
      Subtype.ext (funext fun u : U.toSubgroup ↦ u.property)
    rw [cyclicClass_corestrictH0 U χ y hy 0, smul_zero]
    rw [h_zero, map_zero, map_zero, AddMonoidHom.zero_apply]

variable [IsAlgClosed Ω] [Module.Finite K L] [Algebra.IsSeparable K L]

/-- Let the open subgroup `U` of `Γ` act on `Ω` as the Galois group of `Ω / L`, with `L / K` finite
separable and `Ω` algebraically closed. Then the norm from `U` to `Γ`
(`New.DiscreteModule.corestrictH0`) of a unit `y` of `L` is its field norm to `K`. -/
lemma corestrictH0_ofBase_eq_norm (U : OpenSubgroup Γ) [IsProGalois U.toSubgroup L Ω] (y : Lˣ) :
    (unitsModule Γ).corestrictH0 U (DiscreteUnits.ofBase U.toSubgroup Ω (Additive.ofMul y)) =
      DiscreteUnits.ofBase Γ Ω (Additive.ofMul (y.map (Algebra.norm K))) := by
  -- Both sides are products of conjugates of `y`: over the cosets `gU` on the left, over the
  -- `K`-embeddings of `L` on the right. Restriction to `L` matches the two index sets.
  obtain ⟨h_fix : U.toSubgroup = fixingSubgroup Γ (Set.range (algebraMap L Ω)),
    h_index : U.toSubgroup.index = Module.finrank K L⟩ :=
    eq_fixingSubgroup_of_isProGalois (L := L) (V := U.toSubgroup)
  let res (x : Γ ⧸ U.toSubgroup) : L →ₐ[K] Ω := (toAlgHom K Ω x.out).domRestrict L
  -- Two elements with the same restriction differ by an element fixing `L`, that is, of `U`.
  have res_inj : Injective res := fun x x' h_res ↦ by
    refine out_equiv_out.mp (leftRel_apply.mpr (h_fix.ge ?_))
    -- `res x l` is `x.out • l`, with `l` viewed in `Ω`.
    have h_smul_eq (l : L) : x'.out • algebraMap L Ω l = x.out • algebraMap L Ω l :=
      (DFunLike.congr_fun h_res l).symm
    simpa [mem_fixingSubgroup_iff, mul_smul, inv_smul_eq_iff] using h_smul_eq
  -- There are at most `[L : K] = [Γ : U]` embeddings.
  have res_bij : Bijective res :=
    res_inj.bijective_of_nat_card_le ((card_algHom_le_finrank K L Ω).trans h_index.ge)
  refine DiscreteUnits.ext ?_
  suffices h_prod : ∏ x : Γ ⧸ U.toSubgroup, x.out • algebraMap L Ω y = ∏ σ : L →ₐ[K] Ω, σ y by
    simpa [corestrictH0, norm_eq_prod_embeddings, sum] using h_prod
  exact Finset.prod_bijective res res_bij (by simp) fun x _ ↦ rfl

/-- If the kernel of the character `χ : Γ → ℚ/ℤ` is the Galois group of `Ω / L` (`J`), with `L / K`
finite separable and `Ω` algebraically closed, then the symbol `(χ, x)` (`New.cyclicClass`) of `x`
in `Kˣ` vanishes exactly when `x` is the norm of a unit of `L`. -/
lemma cyclicClass_eq_zero_iff_norm {χ : QZChar Γ} [J : IsProGalois (ker χ) L Ω] (x : Kˣ) :
    cyclicClass unitsRep χ (DiscreteUnits.ofBase Γ Ω (Additive.ofMul x)) = 0 ↔
      ∃ z : Lˣ, z.map (Algebra.norm K) = x := by
  -- By `cyclicClass_spec` the symbol vanishes exactly on norms from the kernel of `χ`, whose
  -- invariants are the units of `L`; `corestrictH0_ofBase_eq_norm` identifies this norm with the
  -- field norm.
  rw [(cyclicClass_spec χ).right]
  refine (ofBase_bijective (K := L) _).surjective.exists.trans ?_
  simp [corestrictH0_ofBase_eq_norm, DiscreteUnits.ext_iff, Units.ext_iff]

end New

end CyclicNorm

end
