import Lib.PadicHodge.Crystalline.FixedRatios

/-!
# Regularity of B_max, closure of admissibility, and crystalline descent from inertia

This file proves the regularity of the period ring `B = New.Period.Bmax` and shows that
representations admissible along a filter have bases of fixed elements. It proves closure
properties of crystalline and potentially crystalline representations under subobjects, quotients
of tensor products and twisted duals. It also shows that a potentially crystalline representation
is crystalline when the linear Frobenius operators are trivial on inertia.

## Main definitions and results

* `New.Period.fontaine_regularity`, `New.Period.IsAdmissible.exists_basis`: regularity of `B`; bases
  of fixed elements.
* `New.Period.IsAdmissible.of_jointly_injective`, `New.Period.IsKilledBy.of_jointly_injective`:
  subobjects of finite sums.
* `New.Period.linearFrob_apply`, `New.Period.linearFrob_mul`,
  `New.Period.linearFrob_twist_cyclotomicGp`,
  `New.Period.IsPotentiallyCrystalline.eventually_linearFrob_eq_one`: the operators are
  multiplicative and change by a power of `p` under Tate twists. They are trivial on inertia near
  `1` if `T` is finite free.
* `New.Period.IsAdmissible.of_bilinear`, `New.Period.linearFrob_baseChangePairing`: quotients of
  tensor products.
* `New.Period.IsAdmissible.of_pairing`: twisted duals.
* `New.Period.IsPotentiallyCrystalline.isCrystalline_of_inertia_fixes`: descent from inertia.

Notions from other files:
* `New.Period.BPlus`, `New.Period.Bmax`: B⁺ = A_max[1/p] and B = B⁺[1/μ], μ = [ε] − 1.
* `New.Period.nearOne`: The filter 'near 1' on Γ: the pull-back along j: Γ → G_p of the filter of
  neighbourhoods of the identity.
* `New.Period.IsWeilPair`: (s, m) is a Weil pair if s acts on the residue field of the integers of
  Q̄_p as x ↦ x^(1/p^m); m = 0 means that s is in inertia.

## Relation to the literature

Known result: Potentially crystalline representations, Hodge–Tate weights and Weil–Deligne
Frobenius. Here the representations are abstract modules over any p-adic coefficient ring, with
Colmez's B_max as period ring and "crystalline" defined by the invariants spanning. Polynomials
killing one linear Frobenius replace the Weil–Deligne representation. Source: J.-M. Fontaine,
Représentations p-adiques semi-stables (Exp. III §1, §5) and Représentations l-adiques
potentiellement semi-stables (Exp. VIII 2.3), Astérisque 223 (1994); O. Brinon, B. Conrad, CMI
Summer School notes on p-adic Hodge theory (2009), 2.3.1, 5.2.1, 6.3, 9.1–9.3.

See also `Lib.PadicHodge.PeriodRings.DeRhamPeriods` and `Lib.PadicHodge.Kisin.PeriodMatrixFrame`.
-/

/-!
## Closure properties of admissible representations

Closure properties of admissible representations for the period ring `B = New.Period.Bmax`. The
group `Γ` comes with a map `toGp` to `G_p` with open image (`New.Period.OverGp`).
`New.Period.fixedPeriods ρ B F` is the set of elements of `B ⊗ T` fixed by `g` along the filter `F`.
`New.Period.IsAdmissible` says that these elements span: this is crystalline for `F = ⊤` and
potentially crystalline (`New.Period.IsPotentiallyCrystalline`) for `F = nearOne Γ`. For a Weil pair
`(s, m)` (`New.Period.IsWeilPair`), `New.Period.linearFrob` is the operator `β` that extends
`φ ^ m s` linearly. `New.Period.IsKilledBy` says that `T` is potentially crystalline and `P(β) = 0`.
-/

namespace New.Period

open TensorProduct Filter Submodule Finsupp Module LinearMap Function Polynomial Lift Free
  Bmax Multiplicative IsPrincipal Multiset

attribute [local instance low] Fintype.ofFinite

variable {p : ℕ} [ThePrime p]
  {Γ R' : Type*} [Group Γ] [CommRing R'] [Algebra ℤ_[p] R'] [𝒥 : OverGp Γ p]
  {F : Filter Γ} (hF : nearOne Γ ≤ F) {s t : Γ} {m k : ℕ} {R T T' : Type _}
  {T'' : Type} [CommRing R] [AddCommGroup T] [Module R T] [Algebra ℤ_[p] R] [Module ℤ_[p] T]
  [IsScalarTower ℤ_[p] R T] [AddCommGroup T'] [Module R' T'] [Module ℤ_[p] T']
  [IsScalarTower ℤ_[p] R' T']
  {ρ σ : Representation R Γ T} {ρ' : Representation R' Γ T'} {ι κ : Type*}
  (h : IsPotentiallyCrystalline ρ) (hs : IsWeilPair (𝒥.toGp s) m) [Finite κ]
  {S : κ → Type _} [∀ i, AddCommGroup (S i)] [∀ i, Module R (S i)] [∀ i, Module ℤ_[p] (S i)]
  [∀ i, IsScalarTower ℤ_[p] R (S i)]
  {τ : ∀ i : κ, Representation R Γ (S i)} {P : R[X]} (hA : ∀ i : κ, IsAdmissible (τ i) F)
  (f : ∀ i : κ, T' →ₗ[ℤ_[p]] S i)
  (hf : ∀ i : κ, ∀ᶠ g : Γ in F, ∀ x : T', f i (ρ' g x) = τ i g (f i x))
  (hi : ∀ x : T', (∀ i : κ, f i x = 0) → x = 0)

/-- Let `x i` (`i : ι`) be elements of `Bmax ⊗ T` fixed along the filter `F` for the representation
`ρ` of `Γ` on `T`, and let `a : ι →₀ Bmax`. Then along `F` the group acts on `∑ a i • x i` through
the coefficients: `g` sends it to `∑ (toGp g • a i) • x i`. -/
lemma eventually_tensorAction_eq {x : ι → Bmax ⊗[ℤ_[p]] T}
    (hx : ∀ i : ι, x i ∈ fixedPeriods ρ Bmax F) (a : ι →₀ Bmax) :
    ∀ᶠ g : Γ in F,
      tensorAction Bmax (toGp g) (ρ g) (linearCombination Bmax x a) =
        linearCombination Bmax x (toGp g • a) := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a a' ha ha' => filter_upwards [ha, ha'] with g hg hg' using by simp_all
  | single i b => filter_upwards [hx i] with g hg using by simp_all [tensorAction_smul]

@[simp]
lemma coeffEnd_tmul (a : R) (b : Bmax) (x : T) : coeffEnd R T a (b ⊗ₜ x) = b ⊗ₜ (a • x) := rfl

/-- Let K be algebraically closed of characteristic 0 and φ: K[X] → A a ring homomorphism with
φ(X)^n = 1 for some n > 0. If φ(Q) = 0, then φ(P) = 0 for every P vanishing at all roots of
Q. -/
lemma map_eq_zero_of_roots {K A : Type*} [Field K] [IsAlgClosed K] [CharZero K] [Ring A]
    (φ : K[X] →+* A) {P Q : K[X]} (h_unity : ∃ n > (0 : ℕ), φ X ^ n = 1) (hQ : φ Q = 0)
    (h_roots : ∀ x : K, Q.IsRoot x → P.IsRoot x) :
    φ P = 0 := by
  obtain ⟨n, hn, hX⟩ := h_unity
  -- The kernel of `φ` is generated by a divisor `G` of `X ^ n - 1`, which has simple roots.
  let G : K[X] := generator (RingHom.ker φ)
  have ker_iff (f : K[X]) : φ f = 0 ↔ G ∣ f := mem_iff_generator_dvd (RingHom.ker φ)
  have h_sep : G.Separable :=
    (X_pow_sub_one_separable_iff.mpr (mod_cast hn.ne')).of_dvd ((ker_iff _).mp (by simp [hX]))
  -- The roots of `G` are roots of `Q`, so of `P`; being simple, they give `G ∣ P`.
  rw [ker_iff] at hQ ⊢
  by_cases hP : P = 0
  · simp [hP]
  rw [IsAlgClosed.dvd_iff_roots_le_roots h_sep.ne_zero hP,
    Multiset.le_iff_subset (nodup_roots h_sep)]
  exact fun y hy ↦ (mem_roots hP).mpr (h_roots y ((isRoot_of_mem_roots hy).dvd hQ))

/-- If `(toGp s, 0)` is a Weil pair, that is, `toGp s` lies in inertia, then so is
`(toGp s⁻¹, 0)`. -/
lemma IsWeilPair.inv : IsWeilPair (toGp s) 0 → IsWeilPair (toGp s⁻¹) 0 := by
  simp [isWeilPair_zero_iff]

open AlgebraTensorModule in
/-- Let `f i : T' → S i` (`i : κ`, `κ` finite) be `ℤ_[p]`-linear maps that are jointly injective:
only `0` is sent to `0` by all of them. Then the family of base changes `Bmax ⊗ T' → Bmax ⊗ S i`
has a `Bmax`-linear left inverse. -/
lemma exists_leftInverse_baseChange (f : ∀ i : κ, T' →ₗ[ℤ_[p]] S i)
    (h_inj : ∀ x : T', (∀ i : κ, f i x = 0) → x = 0) :
    ∃ Ψ : ((i : κ) → Bmax ⊗[ℤ_[p]] S i) →ₗ[Bmax] Bmax ⊗[ℤ_[p]] T',
      LeftInverse Ψ fun (x : Bmax ⊗[ℤ_[p]] T') (i : κ) ↦ (f i).baseChange Bmax x := by
  classical
  -- By flatness the base change of `LinearMap.pi f` is injective, so it has a `ℚ_[p]`-linear left
  -- inverse; `L y` is its value at `1 ⊗ₜ y`. The retraction is the `Bmax`-linear extension of `L`.
  let Φ : Bmax ⊗[ℤ_[p]] T' →ₗ[ℚ_[p]] Bmax ⊗[ℤ_[p]] ((i : κ) → S i) :=
    AlgebraTensorModule.lTensor ℚ_[p] Bmax (LinearMap.pi f)
  have hΦ : ker Φ = ⊥ := ker_eq_bot.mpr <| Flat.lTensor_preserves_injective_linearMap _ <| by
    simpa [injective_iff_map_eq_zero, funext_iff] using h_inj
  let L : ((i : κ) → S i) →ₗ[ℤ_[p]] Bmax ⊗[ℤ_[p]] T' := AlgebraTensorModule.curry Φ.leftInverse 1
  have hL (y : T') : L (fun i ↦ f i y) = 1 ⊗ₜ y := leftInverse_apply_of_inj hΦ (1 ⊗ₜ y)
  refine ⟨liftBaseChange _ L ∘ₗ piRightInv .., fun x ↦ ?_⟩
  induction x with
  | tmul b y => simp_all [smul_tmul']
  | add x x' hx hx' => simp_all [← Pi.add_def]

section

/-! ### Regularity, bases of fixed elements, subobjects

In this section `hF : nearOne Γ ≤ F`: every property that holds along `F` holds for all `g` with
`toGp g` near `1`. -/

/-- Part of Fontaine's regularity of `B = Bmax` (fixed fractions lie in `B`). Let
`nearOne Γ ≤ F`, let `w : ι →₀ Bmax` and `b ≠ 0` in `Bmax`. If the fraction `w / b` is fixed
along `F`, in the sense that `b • g w = (g b) • w` for `F`-almost all `g` (acting through
`toGp`), then `w = b • a` for some `a` fixed by `F`-almost all `g`. -/
lemma fontaine_regularity (hF : nearOne Γ ≤ F) {b : Bmax} (w : ι →₀ Bmax) (hb : b ≠ 0)
    (h_ratio : ∀ᶠ g : Γ in F, b • toGp g • w = (toGp g • b) • w) :
    ∃ a : ι →₀ Bmax, w = b • a ∧ ∀ᶠ g : Γ in F, toGp g • a = a := by
  -- Each coordinate `w i` is divisible by `b`: by `exists_witt_ratio`, `p ^ n * w i` is `b` times
  -- a Witt vector over a finite field, and `p` is a unit of `Bmax`.
  have h_dvd (i : ι) : w i ∈ Set.range fun x : Bmax ↦ b * x := by
    have h_coord : ∀ᶠ g : Γ in F, b * toGp g • w i = toGp g • b * w i :=
      h_ratio.mono fun g hg ↦ DFunLike.congr_fun hg i
    obtain ⟨f, n, c, hc⟩ := exists_witt_ratio hb (nhds_one_le_map_nearOne Γ (hF h_coord))
    have h_dvd_mul : b ∣ algebraMap BPlus Bmax ((p : BPlus) ^ n) * w i := by simp [hc]
    obtain ⟨q, hq⟩ : b ∣ w i := ((BPlus.isUnit_p.pow n).map _).dvd_mul_left.mp h_dvd_mul
    exact ⟨q, hq.symm⟩
  obtain ⟨a, rfl⟩ : w ∈ Set.range (mapRange (fun x : Bmax ↦ b * x) (mul_zero b)) :=
    (range_mapRange _ (mul_zero b)).ge h_dvd
  refine ⟨a, Finsupp.ext fun i ↦ by simp, h_ratio.mono fun g hg ↦ Finsupp.ext fun i ↦ ?_⟩
  -- Cancel `b` and `toGp g • b` in `hg`, coordinate by coordinate.
  have hgb : toGp g • b ≠ 0 := (smul_ne_zero_iff_ne _).mpr hb
  have hg_i : b * (toGp g • b * toGp g • a i) = b * (toGp g • b * a i) := by
    simpa [mul_left_comm b] using DFunLike.congr_fun hg i
  simpa [hb, hgb] using hg_i

include hF in
/-- Let `hF : nearOne Γ ≤ F`. Let `W` be a submodule of the free `Bmax`-module `ι →₀ Bmax` that is
saturated (`b • w ∈ W` with `b ≠ 0` implies `w ∈ W`) and stable along `F` (`toGp g • v ∈ W`
for `F`-almost all `g`, for each `v ∈ W`). If every element of `W` fixed along `F` lies in
`W'`, then `W ≤ W'`. -/
lemma le_of_fixed_mem_of_saturated {W W' : Submodule Bmax (ι →₀ Bmax)}
    (h_sat : ∀ b ≠ (0 : Bmax), ∀ w : ι →₀ Bmax, b • w ∈ W → w ∈ W)
    (h_stable : ∀ v ∈ W, ∀ᶠ g : Γ in F, toGp g • v ∈ W)
    (h_fixed : ∀ w ∈ W, (∀ᶠ g : Γ in F, toGp g • w = w) → w ∈ W') :
    W ≤ W' := by
  -- By elimination (`le_of_echelon`) it suffices, for `v ≠ 0` in `W` to which all vectors of `W`
  -- supported within `v` are proportional, to find a vector of `W ⊓ W'` supported within `v`
  -- that has a coordinate `1`.
  refine le_of_echelon (LinearEquiv.refl Bmax (ι →₀ Bmax)) fun v hv v_ne h_prop ↦ ?_
  obtain ⟨k, hk⟩ : ∃ k : ι, v k ≠ 0 := ne_iff.mp v_ne
  -- `toGp g • v` lies in `W` and vanishes where `v` does, so it is proportional to `v`.
  have h_smul : ∀ᶠ g : Γ in F, v k • toGp g • v = (toGp g • v k) • v := by
    filter_upwards [h_stable v hv] with g hg
    have h_supp : ∀ i : ι, v i = 0 → (toGp g • v) i = 0 := fun i hi ↦ by simp [hi]
    exact h_prop (toGp g • v) hg h_supp k
  -- Regularity gives `v = v k • u` with `u` fixed; `u ∈ W` by saturation and `u k = 1`.
  obtain ⟨u, hv_eq, h_fix⟩ := fontaine_regularity hF v hk h_smul
  have u_mem : u ∈ W := h_sat (v k) hk u (by rwa [← hv_eq])
  have hv_coord (i : ι) : v i = v k * u i := DFunLike.congr_fun hv_eq i
  have hu_k : u k = 1 := (left_eq_mul₀ hk).mp (hv_coord k)
  have hu_supp (i : ι) (hi : v i = 0) : u i = 0 :=
    (mul_eq_zero_iff_left hk).mp ((hv_coord i).symm.trans hi)
  exact ⟨u, ⟨u_mem, h_fixed u u_mem h_fix⟩, ⟨k, hu_k⟩, hu_supp⟩

/-- Let `nearOne Γ ≤ F` (`nearOne Γ`: the filter of `g` with `toGp g` near `1`). If `ρ` is
admissible along `F`, that is, the elements of `Bmax ⊗ T` fixed by `F`-almost all `g` span it over
`Bmax`, then `Bmax ⊗ T` has a `Bmax`-basis of such fixed elements.

A form, over `Bmax` and for invariants along `F`, of the statement in Fontaine's admissibility
formalism that the period module of an admissible representation has a basis of invariant
elements. -/
lemma IsAdmissible.exists_basis (hF : nearOne Γ ≤ F) (h : IsAdmissible ρ F) :
    ∃ s : Set (fixedPeriods ρ Bmax F), ∃ v : Basis s Bmax (Bmax ⊗[ℤ_[p]] T), ∀ i : s,
      v i ∈ fixedPeriods ρ Bmax F := by
  -- Take a maximal linearly independent family `s` of fixed elements. A fixed `y` outside `s` has
  -- `b • y = ∑ w i • i` with `b ≠ 0`; applying `g` shows that `w / b` is fixed, and regularity
  -- gives `w = b • a`, so `y = ∑ a i • i`.
  obtain ⟨s, hs, h_max⟩ :=
    exists_maximal_linearIndepOn Bmax fun y : fixedPeriods ρ Bmax F ↦ (y : Bmax ⊗[ℤ_[p]] T)
  let x : s → Bmax ⊗[ℤ_[p]] T := fun i ↦ (i : fixedPeriods ρ Bmax F)
  have hx (i : s) : x i ∈ fixedPeriods ρ Bmax F := (i : fixedPeriods ρ Bmax F).prop
  have hx_indep : LinearIndependent Bmax x := hs
  have h_span : ⊤ ≤ span Bmax (Set.range x) := by
    rw [← h, span_le]
    intro y hy
    by_cases y_mem : ⟨y, hy⟩ ∈ s
    · exact subset_span ⟨⟨⟨y, hy⟩, y_mem⟩, rfl⟩
    obtain ⟨b, hb, hby_mem⟩ := h_max ⟨y, hy⟩ y_mem
    obtain ⟨w, hw⟩ : ∃ w : s →₀ Bmax, linearCombination Bmax x w = b • y := by
      rwa [Set.image_eq_range, ← range_linearCombination] at hby_mem
    -- Apply `g` to `b • y = ∑ w i • i` and compare coefficients.
    have h_coef : ∀ᶠ g : Γ in F, b • toGp g • w = (toGp g • b) • w := by
      filter_upwards [hy, eventually_tensorAction_eq hx w] with g y_fix hg
      -- Both sides have the same image under the injective map `linearCombination Bmax x`.
      apply hx_indep
      simp [hw, y_fix, smul_comm b, ← hg, tensorAction_smul]
    obtain ⟨a, rfl, -⟩ := fontaine_regularity hF w hb h_coef
    have h_comb : linearCombination Bmax x a = y := by simpa [hb] using hw
    rw [SetLike.mem_coe, ← range_linearCombination]
    exact ⟨a, h_comb⟩
  exact ⟨s, Basis.mk hx_indep h_span, by simpa using hx⟩

/-- Let `F` be a filter on `Γ` with `nearOne Γ ≤ F`, where `nearOne Γ` is the pull-back along `toGp`
of the neighbourhoods of `1` in Gal(Q̄_p/Q_p). Let finitely many representations `τ i` on `S i` be
admissible along `F` (`hA`): the elements of `Bmax ⊗ S i` fixed by `toGp g ⊗ τ i g` for `F`-almost
all `g` span `Bmax ⊗ S i` over `Bmax`. Let `Bmax`-linear maps `Φ i : Bmax ⊗ T' → Bmax ⊗ S i`
commute, for `F`-almost all `g`, with the diagonal actions `b ⊗ x ↦ (toGp g • b) ⊗ ρ' g x` and
`b ⊗ y ↦ (toGp g • b) ⊗ τ i g y`; if `LinearMap.pi Φ` also has a `Bmax`-linear left inverse `Ψ`,
then `ρ'` is admissible along `F` in the same sense. -/
lemma IsAdmissible.of_retraction (hF : nearOne Γ ≤ F) (hA : ∀ i : κ, IsAdmissible (τ i) F)
    (Φ : ∀ i : κ, Bmax ⊗[ℤ_[p]] T' →ₗ[Bmax] Bmax ⊗ S i)
    (hΦ : ∀ i : κ, ∀ᶠ g : Γ in F, ∀ x : Bmax ⊗[ℤ_[p]] T',
      Φ i (tensorAction Bmax (toGp g) (ρ' g) x) = tensorAction Bmax (toGp g) (τ i g) (Φ i x))
    (Ψ : (∀ i : κ, Bmax ⊗ S i) →ₗ[Bmax] Bmax ⊗[ℤ_[p]] T') (hΨ : LeftInverse Ψ (LinearMap.pi Φ)) :
    IsAdmissible ρ' F := by
  -- Coordinates in bases of fixed elements turn `pi Φ` into an equivariant injection `Θ` into a
  -- free module; its range is saturated because `pi Φ` has a retraction, so
  -- `le_of_fixed_mem_of_saturated` applies.
  have h_bases (i : κ) : ∃ s : Set (fixedPeriods (τ i) Bmax F),
      ∃ v : Basis s Bmax (Bmax ⊗[ℤ_[p]] S i), ∀ j : s, v j ∈ fixedPeriods (τ i) Bmax F :=
    (hA i).exists_basis hF
  choose s v hv using h_bases
  let Θ : Bmax ⊗[ℤ_[p]] T' →ₗ[Bmax] (Σ i : κ, s i) →₀ Bmax :=
    (Pi.basis v).repr.toLinearMap ∘ₗ pi Φ
  have Θ_inj : Injective Θ := by simp [Θ, hΨ.injective]
  have Θ_smul (x : Bmax ⊗[ℤ_[p]] T') :
      ∀ᶠ g : Γ in F, Θ (tensorAction Bmax (toGp g) (ρ' g) x) = toGp g • Θ x := by
    filter_upwards [eventually_all.mpr hΦ, eventually_all.mpr fun i ↦
      eventually_tensorAction_eq (hv i) ((v i).repr (Φ i x))] with g h_eq h_coef
    ext ⟨i, l⟩
    have h_coef_l :
        (v i).repr (tensorAction Bmax (toGp g) (τ i g)
            (linearCombination Bmax (v i) ((v i).repr (Φ i x)))) l =
          (v i).repr (linearCombination Bmax (v i) (toGp g • (v i).repr (Φ i x))) l :=
      DFunLike.congr_fun (congrArg (v i).repr (h_coef i)) l
    simpa [Θ, h_eq] using h_coef_l
  -- The range of `Θ` is the kernel of a linear map, so it is saturated.
  have h_sat : ∀ b ≠ (0 : Bmax), ∀ w : (Σ i : κ, s i) →₀ Bmax,
      b • w ∈ Submodule.map Θ ⊤ → w ∈ Submodule.map Θ ⊤ := by
    simp_all [Θ, range_comp, range_eq_ker_of_leftInverse hΨ]
  have h_stable : ∀ w ∈ Submodule.map Θ ⊤, ∀ᶠ g : Γ in F, toGp g • w ∈ Submodule.map Θ ⊤ := by
    rintro _ ⟨y, -, rfl⟩
    filter_upwards [Θ_smul y] with g hg using ⟨_, trivial, hg⟩
  have h_fixed : ∀ w ∈ Submodule.map Θ ⊤, (∀ᶠ g : Γ in F, toGp g • w = w) →
      w ∈ Submodule.map Θ (span Bmax (fixedPeriods ρ' Bmax F)) := by
    rintro _ ⟨y, -, rfl⟩ h_fix
    have hy_fixed : y ∈ fixedPeriods ρ' Bmax F := by
      filter_upwards [Θ_smul y, h_fix] with g hg hg_fix using Θ_inj (hg.trans hg_fix)
    exact ⟨y, subset_span hy_fixed, rfl⟩
  have h_le : Submodule.map Θ ⊤ ≤ Submodule.map Θ (span Bmax (fixedPeriods ρ' Bmax F)) :=
    le_of_fixed_mem_of_saturated hF h_sat h_stable h_fixed
  exact top_unique ((map_le_map_iff_of_injective Θ_inj ⊤ _).mp h_le)

include hF hA hf hi in
/-- Let `Γ` come with a homomorphism `j : Γ → Gp p` of open image (`OverGp`), and let every set in
the filter `F` contain the preimage under `j` of a neighbourhood of `1` (`hF : nearOne Γ ≤ F`). A
representation `ρ` on `T` is admissible along `F` when the elements of `Bmax ⊗ T` fixed by
`j(g) ⊗ ρ(g)` for `F`-almost all `g` span `Bmax ⊗ T` over `Bmax`. If each `τ i` is admissible along
`F` (`hA`) and finitely many `ℤ_[p]`-linear maps `f i : T' → S i` are jointly injective (`hi`) and
equivariant for `F`-almost all `g` (`hf`), then `ρ'` is admissible along `F`.

A form of Fontaine's stability of admissible representations under finite direct sums and
subrepresentations. -/
lemma IsAdmissible.of_jointly_injective : IsAdmissible ρ' F := by
  obtain ⟨Ψ, hΨ⟩ := exists_leftInverse_baseChange f hi
  refine .of_retraction hF hA (fun i ↦ (f i).baseChange Bmax) (fun i ↦ ?_) Ψ hΨ
  filter_upwards [hf i] with g hg x using (tensorAction_periodTensorMap hg _ x).symm

end

/-- The action of `g` in `G_p` on `Bmax ⊗ T` is the action of the pair `(1, g)` of `FrobGal`. -/
private lemma tensorAction_gp_eq_tensorAction_frobGal (g : Gp p) (f : End R T)
    (x : Bmax ⊗[ℤ_[p]] T) :
    tensorAction Bmax g f x = tensorAction Bmax ((1, g) : FrobGal) f x := rfl

section

/-! ### The operators attached to Weil pairs

Here `hs : IsWeilPair (toGp s) m` says that `(toGp s, m)` is a Weil pair: `toGp s` acts on the
residue field of the integers of `Q̄_p` as `x ↦ x ^ (1 / p ^ m)`. -/

/-- Let `(toGp s, m)` be a Weil pair. If `b` in `Bmax` is fixed by `toGp g` for all `g` near `1`,
then `φ ^ m` composed with `toGp s`, the action of the pair `(ofAdd m, toGp s)` of `FrobGal`,
fixes `b`. -/
lemma IsWeilPair.smul_eq_of_fixed_nearOne (hs : IsWeilPair (toGp s) m) {b : Bmax}
    (h_fixed : ∀ᶠ g : Γ in nearOne Γ, toGp g • b = b) :
    (ofAdd m, toGp s) • b = b := by
  -- By `exists_witt_ratio` with denominator `1`, `p ^ n * b` is a Witt vector `w` over a finite
  -- field.
  have h_near : ∀ᶠ g : Gp p in map toGp (nearOne Γ), (1 : Bmax) * g • b = g • (1 : Bmax) * b := by
    simpa using h_fixed
  obtain ⟨f, n, w, hw⟩ := exists_witt_ratio one_ne_zero (nhds_one_le_map_nearOne Γ h_near)
  -- `(ofAdd m, toGp s)` maps `w` to such a vector `w'` with the same reduction (for a Weil pair,
  -- `φ ^ m ∘ toGp s` acts trivially on reductions), and these vectors are determined by their
  -- reductions.
  obtain ⟨w', hw'⟩ := w.exists_smul_algebraMap_eq (ofAdd m, toGp s)
  have h_red : toWittResidue (algebraMap _ _ w') = toWittResidue (algebraMap _ _ w) := by
    rw [← hw', toWittResidue_smul_of_isFrob hs]
  obtain rfl : w' = w := wittFq_map_residue_injective h_red
  have h_fix : (ofAdd m, toGp s) • (p ^ n * b) = p ^ n * b := by
    rw [hw, mul_one, smul_algebraMap_eq_algebraMap_smul, hw']
  -- Cancel `p ^ n`, which is fixed and not zero.
  simpa [(NeZero.of_faithfulSMul ℚ_[p] Bmax p).out] using h_fix

include h hs in
/-- Let `ρ` be potentially crystalline (`h`) and let `(toGp s, m)` be a Weil pair (`hs`), meaning
`toGp s` acts on the residue field of the valuation ring of Q̄_p as `x ↦ x ^ (1 / p ^ m)`. On
`Dpcris ρ`, the set of elements of `Bmax ⊗ T` fixed by `toGp g ⊗ ρ g` for all `g` near `1`, the map
`linearFrob ρ s m` acts as `φ ^ m s ⊗ ρ s`. Here the pair `(ofAdd m, toGp s)` of `FrobGal` acts on
`Bmax` as `φ ^ m ∘ toGp s`, `φ` being Frobenius, and `ρ s` acts on `T`. -/
@[local simp] lemma linearFrob_apply {d : Bmax ⊗[ℤ_[p]] T} (hd : d ∈ Dpcris ρ) :
    linearFrob ρ s m d = tensorAction Bmax ((ofAdd m, toGp s) : FrobGal) (ρ s) d := by
  -- It suffices to find one linear map with the property that defines `linearFrob`: prescribe it on
  -- a basis `v` of fixed elements.
  obtain ⟨I, v, hv⟩ := h.exists_basis le_rfl
  let β : End Bmax (Bmax ⊗[ℤ_[p]] T) :=
    v.constr ℕ fun i ↦ tensorAction Bmax (ofAdd m, toGp s) (ρ s) (v i)
  refine linearFrob_eq_tensorAction_of_exists ρ s m ⟨β, fun y hy ↦ ?_⟩ d hd
  -- The coordinates of `y` are fixed near `1`, so they are fixed by `(ofAdd m, toGp s)`.
  have h_coef (i : I) : (ofAdd m, toGp s) • v.repr y i = v.repr y i := by
    refine hs.smul_eq_of_fixed_nearOne ?_
    filter_upwards [hy, eventually_tensorAction_eq hv (v.repr y)] with g y_fix hg
    have h_repr :
        v.repr (tensorAction Bmax (toGp g) (ρ g) (linearCombination Bmax v (v.repr y))) i =
          v.repr (linearCombination Bmax v (toGp g • v.repr y)) i :=
      DFunLike.congr_fun (congrArg v.repr hg) i
    simpa [y_fix] using h_repr.symm
  calc β y = tensorAction Bmax (ofAdd m, toGp s) (ρ s) (linearCombination Bmax v (v.repr y)) := by
        simp [β, linearCombination, Finsupp.sum, h_coef, v.constr_apply, tensorAction_smul]
    _ = tensorAction Bmax (ofAdd m, toGp s) (ρ s) y := by rw [v.linearCombination_repr]

/-- Let `ρ` be potentially crystalline and `toGp s` in inertia (`(toGp s, 0)` a Weil pair). On
`Dpcris ρ`, the elements fixed by all `g` near `1`, the map `linearFrob ρ s 0` is the action of
`s`. -/
lemma linearFrob_zero_apply (h : IsPotentiallyCrystalline ρ) (hs : IsWeilPair (toGp s) 0)
    {d : Bmax ⊗[ℤ_[p]] T} (hd : d ∈ Dpcris ρ) :
    linearFrob ρ s 0 d = tensorAction Bmax (toGp s) (ρ s) d :=
  (linearFrob_apply h hs hd).trans (tensorAction_gp_eq_tensorAction_frobGal ..).symm

include h hs in
/-- Multiplicativity of the linear Frobenius: for `ρ` potentially crystalline (`h`) and Weil pairs
`(toGp s, m)` (`hs`) and `(toGp t, k)` (`ht`), one has `β_{st, m+k} = β_{s,m} β_{t,k}`, where
`β_{s,m}` is `linearFrob ρ s m`. -/
lemma linearFrob_mul (ht : IsWeilPair (toGp t) k) :
    linearFrob ρ (s * t) (m + k) = linearFrob ρ s m * linearFrob ρ t k := by
  -- Both sides are linear, so it suffices to compare them on `Dpcris ρ`, which spans, by
  -- `linearFrob_apply`; for this the image of `d` under `t` must lie in `Dpcris ρ` again.
  refine ext_on h fun d hd ↦ ?_
  -- Conjugation by `t` keeps elements near `1`, and the image of `d` under `t` is fixed by `g`
  -- as soon as `d` is fixed by `t⁻¹ * g * t`.
  have h_conj : Tendsto (fun g ↦ t⁻¹ * g * t) (nearOne Γ) (nearOne Γ) := by
    simpa [nearOne, tendsto_comap_iff, comp_def] using
      ((tendsto_comap (f := toGp) (x := nhds 1)).const_mul (toGp t)⁻¹).mul_const (toGp t)
  have h_mem : tensorAction Bmax (ofAdd k, toGp t) (ρ t) d ∈ Dpcris ρ := by
    filter_upwards [h_conj.eventually hd] with g hg
    calc tensorAction Bmax (toGp g) (ρ g) (tensorAction Bmax (ofAdd k, toGp t) (ρ t) d)
        = tensorAction Bmax (ofAdd k, toGp t) (ρ t)
            (tensorAction Bmax (toGp (t⁻¹ * g * t)) (ρ (t⁻¹ * g * t)) d) := by
          rw [tensorAction_gp_eq_tensorAction_frobGal, tensorAction_gp_eq_tensorAction_frobGal,
            tensorAction_tensorAction, tensorAction_tensorAction]
          simp [← map_mul, mul_assoc]
      _ = tensorAction Bmax (ofAdd k, toGp t) (ρ t) d := congrArg _ hg
  rw [Module.End.mul_apply, linearFrob_apply h (hs.mul ht) hd, linearFrob_apply h ht hd,
    linearFrob_apply h hs h_mem, tensorAction_tensorAction]
  simp

include h hs in
/-- For `ρ` potentially crystalline (`h`) and `(toGp s, m)` a Weil pair (`hs`),
`β_{s^n, n m} = β_{s,m}^n` for every natural number `n`, where `β_{s,m}` is `linearFrob ρ s m`. -/
lemma linearFrob_pow (n : ℕ) : linearFrob ρ (s ^ n) (n * m) = linearFrob ρ s m ^ n := by
  induction n with
  | zero =>
    -- An element of `Dpcris ρ` is fixed by all `g` near `1`, in particular by `1`.
    refine ext_on h fun d hd ↦ ?_
    have h_weil : IsWeilPair (toGp (1 : Γ)) 0 := by simp [isWeilPair_zero_iff]
    rw [pow_zero, zero_mul, pow_zero, Module.End.one_apply, linearFrob_zero_apply h h_weil hd]
    exact mem_of_mem_nhds (mem_comap'.mp hd) toGp.map_one
  | succ n ih => rw [pow_succ s n, add_one_mul, linearFrob_mul h (hs.pow n) hs, ih, pow_succ]

include h hs in
/-- Let `ρ`, `ρ'` be potentially crystalline (`h`, `h'`) and let `(toGp s, m)` be a Weil pair
(`hs`), meaning `toGp s` acts on the residue field of Q̄_p's valuation ring as
`x ↦ x ^ (1 / p ^ m)`. Here `linearFrob ρ s m` is the `Bmax`-linear endomorphism of `Bmax ⊗ T` that
equals `φ ^ m s ⊗ ρ s` on `Dpcris ρ` (the elements of `Bmax ⊗ T` fixed by `toGp g ⊗ ρ g` for all `g`
near `1`; potentially crystalline means that they span over `Bmax`), where `φ` is Frobenius. The
claim: if a `ℤ_[p]`-linear map `f : T → T'` satisfies `f ∘ ρ g = ρ' g ∘ f` for all `g` near `1` and
for `g = s` (`hf`), then its base change to `Bmax` intertwines `linearFrob ρ s m` and
`linearFrob ρ' s m`. -/
lemma baseChange_linearFrob (h' : IsPotentiallyCrystalline ρ') (f : T →ₗ[ℤ_[p]] T')
    (hf : ∀ᶠ g : Γ in nearOne Γ ⊔ pure s, ∀ x : T, f (ρ g x) = ρ' g (f x)) (x : Bmax ⊗[ℤ_[p]] T) :
    f.baseChange Bmax (linearFrob ρ s m x) = linearFrob ρ' s m (f.baseChange Bmax x) := by
  -- Both sides are linear in `x`, and on `Dpcris ρ`, which spans, `linearFrob` is given by
  -- `linearFrob_apply`.
  obtain ⟨hf_near, hf_s⟩ := eventually_sup.mp hf
  rw [eventually_pure] at hf_s
  induction eq_top_iff'.mp h x using span_induction with
  | mem d hd =>
    simp_all [fixedPeriods.periodTensorMap_mem hf_near, tensorAction_periodTensorMap hf_s,
      baseChange_eq_periodTensorMap]
  | zero => simp
  | add y z _ _ hy hz => simp [hy, hz]
  | smul a y _ hy => simp [hy]

include h hs in
/-- For `ρ` potentially crystalline (`h`) and `(toGp s, m)` a Weil pair (`hs`), the action of `a` in
`R` on `Bmax ⊗ T` (`coeffEnd`) commutes with `linearFrob ρ s m`. -/
lemma commute_coeffEnd_linearFrob (a : R) : Commute (coeffEnd R T a) (linearFrob ρ s m) :=
  ext (baseChange_linearFrob h hs h _ (by simp))

include h hs in
/-- Let `ρ` be potentially crystalline (`h`), `(toGp s, m)` a Weil pair (`hs`), and let `σ` be the
twist of `ρ` by the power `-d` of the cyclotomic character `χ = cyclotomicGp ∘ toGp` (`hσ`). Then
the operator `β_{s,m} = linearFrob σ s m` of `σ` equals `p ^ (m d)` times that of `ρ`. -/
lemma linearFrob_twist_cyclotomicGp (d : ℕ)
    (hσ : ∀ (g : Γ) (x : T), σ g x = ((χ g ^ (-d : ℤ) : ℤ_[p]ˣ) : ℤ_[p]) • ρ g x) :
    linearFrob σ s m = (p : Bmax) ^ (m * d) • linearFrob ρ s m := by
  -- Multiplication by the unit `u` of `exists_tate_twist_unit` carries `Dpcris ρ` into `Dpcris σ`,
  -- and `(ofAdd m, toGp s)` acting on `u • y` produces the factor `p ^ (m * d)`.
  obtain ⟨u, hu⟩ := exists_tate_twist_unit _ hσ
  refine ext_on h fun y hy ↦ ?_
  have h_mem : (u : Bmax) • y ∈ Dpcris σ := by
    filter_upwards [hy.out] with g hg
    refine (hu 0 g y).trans ?_
    simp [← tensorAction_gp_eq_tensorAction_frobGal, hg]
  have h_beta : linearFrob σ s m ((u : Bmax) • y) =
      ((u * Bmax.pUnit ^ (m * -(-d : ℤ)) : Bmaxˣ) : Bmax) •
        tensorAction Bmax (ofAdd m, toGp s) (ρ s) y :=
    (linearFrob_apply (h.tate_twist _ hσ) hs h_mem).trans (hu m s y)
  -- Cancel the unit `u` on both sides; `Bmax.pUnit` is `p`.
  show linearFrob σ s m y = (p : Bmax) ^ (m * d) • linearFrob ρ s m y
  simpa [mul_smul, zpow_mul, pow_mul, Bmax.coe_pUnit, h, hs, hy] using h_beta

end

include hs hf hi in
/-- Let `(toGp s, m)` be a Weil pair (`hs`), and let `F` be a filter with `nearOne Γ ⊔ pure s ≤ F`.
Let finitely many `ℤ_[p]`-linear maps `f i : T' → S i` be jointly injective (`hi`), semilinear along
`φ : R' → R` (`hφ`), and equivariant along `F` (`hf`). If the image `P` of `Q` under `φ` kills
`(s, m)` on every `S i` (`IsKilledBy`: the representation is potentially crystalline and
`P(β_{s,m}) = 0`), then `Q` kills `(s, m)` on `T'`.

A form of the exactness of Fontaine's Weil–Deligne functor, for subobjects. -/
lemma IsKilledBy.of_jointly_injective (h_le : nearOne Γ ⊔ pure s ≤ F)
    (h : ∀ i : κ, IsKilledBy (τ i) s m P) {φ : R' →+* R} {Q : R'[X]}
    (hP : Polynomial.map φ Q = P) (hφ : ∀ (i : κ) (a : R') (x : T'), f i (a • x) = φ a • f i x) :
    IsKilledBy ρ' s m Q := by
  have h_pot (i : κ) : IsPotentiallyCrystalline (τ i) := (h i).left
  have h_zero (i : κ) : eval₂ (coeffEnd R (S i)) (linearFrob (τ i) s m) P = 0 := (h i).right
  have h_pcr : IsPotentiallyCrystalline ρ' := IsAdmissible.of_jointly_injective le_rfl h_pot f
    (fun i ↦ (hf i).filter_mono (le_sup_left.trans h_le)) hi
  -- Each `1 ⊗ f i` intertwines `Q(β)` on `T'` with `φ(Q)(β)` on `S i`.
  have h_comm (i : κ) (Q : R'[X]) (x : Bmax ⊗[ℤ_[p]] T') :
      (f i).baseChange Bmax (eval₂ (coeffEnd R' T') (linearFrob ρ' s m) Q x) =
        eval₂ (coeffEnd R (S i)) (linearFrob (τ i) s m) (Q.map φ) ((f i).baseChange Bmax x) := by
    have h_frob (y : Bmax ⊗[ℤ_[p]] T') :
        (f i).baseChange Bmax (linearFrob ρ' s m y) =
          linearFrob (τ i) s m ((f i).baseChange Bmax y) :=
      baseChange_linearFrob h_pcr hs (h_pot i) (f i) (h_le (hf i)) y
    have h_coef (a : R') (y : Bmax ⊗[ℤ_[p]] T') :
        (f i).baseChange Bmax (coeffEnd R' T' a y) =
          coeffEnd R (S i) (φ a) ((f i).baseChange Bmax y) := by
      induction y with
      | tmul r z => simp [hφ]
      | add y y' hy hy' => simp [hy, hy']
    induction Q using recOnHorner generalizing x with
    | M0 => simp
    | MC Q a _ _ ih => simp [ih, h_coef]
    | MX Q _ ih => simp [ih, h_frob]
  -- The `1 ⊗ f i` are jointly injective, and `P(β) = 0` on each `S i`.
  obtain ⟨Ψ, hΨ⟩ := exists_leftInverse_baseChange f hi
  refine ⟨h_pcr, ext fun x ↦ hΨ.injective ?_⟩
  simp [h_comm, hP, h_zero]

/-- Let `ρ` be crystalline and let `toGp s` lie in inertia, that is, `(toGp s, 0)` is a Weil pair,
so `toGp s` acts trivially on the residue field of Q̄_p's valuation ring. Then `linearFrob ρ s 0` is
the identity. This is the `Bmax`-linear endomorphism of `Bmax ⊗ T` that agrees with `toGp s ⊗ ρ s`
on `Dpcris ρ`.

This is one direction of Fontaine's criterion that a potentially crystalline representation is
crystalline exactly when inertia acts trivially on its Weil–Deligne representation. -/
lemma IsCrystalline.linearFrob_eq_one (h : IsCrystalline ρ) (hs : IsWeilPair (toGp s) 0) :
    linearFrob ρ s 0 = 1 := by
  refine ext_on h fun d hd ↦ ?_
  have hd_all : ∀ g : Γ, tensorAction Bmax (toGp g) (ρ g) d = d := eventually_top.mp hd
  have hd_near : d ∈ Dpcris ρ := Eventually.of_forall (f := nearOne Γ) hd_all
  rw [linearFrob_zero_apply h.isPotentiallyCrystalline hs hd_near, hd_all, Module.End.one_apply]

variable [AddCommGroup T''] [Module R T''] [Module ℤ_[p] T''] [IsScalarTower ℤ_[p] R T''] (c : ℤ)
  {σ : Representation R Γ T''}
  (v : IsPotentiallyCrystalline σ) (B : (T'' →ₗ[ℤ_[p]] T →ₗ[ℤ_[p]] T' : Type))
  (hB_equiv : ∀ (g : Γ) (x : T'') (y : T), B (σ g x) (ρ g y) = ρ' g (B x y))

/-- Let `T` be finite and free over `R` and `ρ` potentially crystalline. Then for all `g` with
`toGp g` close enough to `1` (along `nearOne Γ`) and in inertia (`IsWeilPair (toGp g) 0`),
`β_{g,0} = linearFrob ρ g 0` is the identity of `Bmax ⊗ T`. This operator is the `Bmax`-linear
endomorphism of `Bmax ⊗ T` that agrees on `Dpcris ρ` with `toGp g ⊗ ρ g`.

This is a form of the finiteness of the inertia action on Fontaine's Weil–Deligne representation. -/
lemma IsPotentiallyCrystalline.eventually_linearFrob_eq_one [Module.Finite R T] [Free.{0} R T]
    (h : IsPotentiallyCrystalline ρ) :
    ∀ᶠ g : Γ in nearOne Γ, IsWeilPair (toGp g) 0 → linearFrob ρ g 0 = 1 := by
  -- Write the `1 ⊗ v l`, for a basis `v` of `T`, through finitely many fixed elements `d l i`,
  -- and take `g` that fixes all of them.
  let v : Basis (ChooseBasisIndex R T) R T := chooseBasis R T
  have h_span (l : ChooseBasisIndex R T) : ∃ (n : ℕ) (a : Fin n → Bmax) (d : Fin n → Dpcris ρ),
      ∑ i, a i • (d i : Bmax ⊗[ℤ_[p]] T) = 1 ⊗ₜ v l :=
    mem_span_set'.mp (h.ge (x := 1 ⊗ₜ v l) trivial)
  choose n a d hd using h_span
  filter_upwards [eventually_all.mpr fun l ↦ eventually_all.mpr fun i ↦ (d l i).prop]
    with g h_fix hg
  have beta_fixed (l : ChooseBasisIndex R T) (i : Fin (n l)) : linearFrob ρ g 0 (d l i) = d l i :=
    (linearFrob_zero_apply h hg (d l i).prop).trans (h_fix l i)
  have beta_basis (l : ChooseBasisIndex R T) : linearFrob ρ g 0 (1 ⊗ₜ v l) = 1 ⊗ₜ v l := by
    simp [← hd, beta_fixed]
  -- `linearFrob` is linear over `Bmax` and commutes with the action of `R` (`coeffEnd`), and the
  -- `1 ⊗ v l` generate `Bmax ⊗ T` over `Bmax` and `R`.
  have h_term (l : ChooseBasisIndex R T) (r : R) :
      linearFrob ρ g 0 (coeffEnd R T r (1 ⊗ₜ v l)) = coeffEnd R T r (1 ⊗ₜ v l) := by
    rw [← End.mul_apply, ← (commute_coeffEnd_linearFrob h hg r).eq, End.mul_apply, beta_basis]
  ext x
  have h_expand : (1 : Bmax) ⊗ₜ[ℤ_[p]] x = ∑ l, coeffEnd R T (v.repr x l) (1 ⊗ₜ v l) := by
    simp [← tmul_sum, v.sum_repr]
  show linearFrob ρ g 0 ((1 : Bmax) ⊗ₜ[ℤ_[p]] x) = (1 : Bmax) ⊗ₜ[ℤ_[p]] x
  simp only [h_expand, map_sum, h_term]

include hB_equiv

/-- For `B` equivariant (`hB_equiv`), the base change of `B` to `Bmax` sends a pair of elements
fixed along `F` to an element fixed along `F`, for the actions `toGp g ⊗ σ g`, `toGp g ⊗ ρ g`,
`toGp g ⊗ ρ' g` on `Bmax ⊗ T''`, `Bmax ⊗ T`, `Bmax ⊗ T'`. -/
lemma baseChangePairing_mem_fixedPeriods {x : Bmax ⊗[ℤ_[p]] T''} {y : Bmax ⊗[ℤ_[p]] T} :
    x ∈ fixedPeriods σ Bmax F →
    y ∈ fixedPeriods ρ Bmax F →
    baseChangePairing B x y ∈ fixedPeriods ρ' Bmax F := by
  intro hx hy
  filter_upwards [hx, hy] with g x_fix y_fix
  have h_map : baseChangePairing B (tensorAction Bmax (toGp g) (σ g) x)
      (tensorAction Bmax (toGp g) (ρ g) y) =
      tensorAction Bmax (toGp g) (ρ' g) (baseChangePairing B x y) :=
    baseChangePairing_map B (hB_equiv g) x y (smul_mul' (toGp g))
  rw [← h_map, x_fix, y_fix]

/-- Let `B : T'' → T → T'` be a `ℤ_[p]`-bilinear map, equivariant for `σ`, `ρ`, `ρ'` (`hB_equiv`),
whose values span `T'` over `ℤ_[p]` (`h_surj`). If `σ` and `ρ` are admissible along `F` (the
elements of `Bmax ⊗ T''` and `Bmax ⊗ T` fixed along `F` span them over `Bmax`), then so is `ρ'`.

A form of the stability of admissible representations under tensor products and quotients in
Fontaine's formalism. -/
lemma IsAdmissible.of_bilinear (hσ : IsAdmissible σ F) (hρ : IsAdmissible ρ F)
    (h_surj : Surjective (TensorProduct.lift B)) :
    IsAdmissible ρ' F := by
  -- Products of invariants are invariant, so the span of the invariants of `ρ'` contains the
  -- product `1 ⊗ B x y` of `1 ⊗ x` and `1 ⊗ y`, which are both spanned by invariants.
  have h_fixed_pair : ∀ x ∈ fixedPeriods σ Bmax F, ∀ y ∈ fixedPeriods ρ Bmax F,
      baseChangePairing B x y ∈ span Bmax (fixedPeriods ρ' Bmax F) :=
    fun x hx y hy ↦ subset_span (baseChangePairing_mem_fixedPeriods B hB_equiv hx hy)
  have h_pure (x : T'') (y : T) : (1 : Bmax) ⊗ₜ B x y ∈ span Bmax (fixedPeriods ρ' Bmax F) := by
    simpa [baseChangePairing] using BilinMap.apply_apply_mem_of_mem_span _ _ _
      (baseChangePairing B) h_fixed_pair (1 ⊗ₜ x) (1 ⊗ₜ y) (hσ.ge trivial) (hρ.ge trivial)
  refine isAdmissible_of_one_tmul_mem_span (h_surj.forall.mpr fun z ↦ ?_)
  induction z with
  | tmul x y => simpa using h_pure x y
  | add z z' hz hz' => simpa [tmul_add] using add_mem hz hz'

include h hs v in
/-- Let toGp have open image, let (toGp s, m) be a Weil pair, and let B: T'' × T → T' be an
equivariant ℤ_p-bilinear map of potentially crystalline representations. Its base change satisfies
B(β_{s,m}x, β_{s,m}y) = β_{s,m}B(x, y), where β_{s,m} is `linearFrob σ s m`, `linearFrob ρ s m`,
`linearFrob ρ' s m` on Bmax ⊗ T'', Bmax ⊗ T, Bmax ⊗ T' respectively.

Proves the form of the compatibility of the Weil–Deligne functor with tensor products that is used
here, for bilinear maps only. -/
lemma linearFrob_baseChangePairing (hρ' : IsPotentiallyCrystalline ρ') :
    (baseChangePairing B).compl₁₂ (linearFrob σ s m) (linearFrob ρ s m) =
      (baseChangePairing B).compr₂ (linearFrob ρ' s m) := by
  -- Check on fixed elements, where each `linearFrob` is the action of `(ofAdd m, toGp s)` by
  -- `linearFrob_apply`; the product of two fixed elements is fixed, and `baseChangePairing` is
  -- equivariant by `hB_equiv`.
  refine ext_on v fun x hx ↦ ext_on h fun y hy ↦ ?_
  simp only [compl₁₂_apply, compr₂_apply, linearFrob_apply v hs hx, linearFrob_apply h hs hy,
    linearFrob_apply hρ' hs (baseChangePairing_mem_fixedPeriods B hB_equiv hx hy)]
  exact baseChangePairing_map B (hB_equiv s) x y (smul_mul' (ofAdd m, toGp s))

omit hB_equiv

include hF
/-- Let `toGp` have open image and `nearOne Γ ≤ F`. Let `T` be finite free over `R` and admissible
along `F`, meaning the elements of `Bmax ⊗ T` fixed by `toGp g ⊗ ρ g` for `F`-almost all `g` span
`Bmax ⊗ T` over `Bmax`. Let the pairing `b` identify `T''` equivariantly with `Hom_R(T, R(c))`,
where `R(c)` is `R` with `Γ` acting through the power `χ ^ c` of the cyclotomic character. Then
`T''` is admissible along `F`. Moreover, for `s` in inertia (`(toGp s, 0)` a Weil pair), a
polynomial that kills `s` on `T` (its value at `linearFrob ρ s 0` vanishes on `Bmax ⊗ T`) kills
`s⁻¹` on `T''`.

Proves the form of Fontaine's stability of admissible representations under twisted duals that is
used here, and, for inertia only, of the compatibility of Weil–Deligne representations with duals
and Tate twists. -/
lemma IsAdmissible.of_pairing [Module.Finite R T] [Free.{0} R T]
    (h_adm : IsAdmissible ρ F) (b : T'' ≃ₗ[R] T →ₗ[R] R)
    (h_equiv : ∀ (g : Γ) (x : T'') (y : T), b (σ g x) (ρ g y) = (χ g ^ c).val • b x y) :
    IsAdmissible σ F ∧
    ∀ (s : Γ) (Q : R[X]), IsWeilPair (toGp s) 0 → IsKilledBy ρ s 0 Q → IsKilledBy σ s⁻¹ 0 Q := by
  let B : T'' →ₗ[ℤ_[p]] T →ₗ[ℤ_[p]] R := b.restrictScalars₁₂ ℤ_[p] ℤ_[p]
  let v : Basis (ChooseBasisIndex R T) R T := chooseBasis R T
  have adm_char {F : Filter Γ} : IsAdmissible (charRep R (χ ^ c)) F :=
    isAdmissible_of_cyclotomicGp_zpow c fun _ _ ↦ rfl
  -- Pairing with the basis vectors `v l` of `T` is jointly injective on `T''`, so has a retraction.
  obtain ⟨Ψ, hΨ⟩ :=
    exists_leftInverse_baseChange (fun l ↦ B.flip (v l)) fun x hx ↦ b.map_eq_zero_iff.1 (v.ext hx)
  have h_coef (a : R) (y : T) (x : Bmax ⊗[ℤ_[p]] T'') :
      (B.flip y).baseChange _ (coeffEnd R _ a x) = baseChangePairing B x (1 ⊗ₜ (a • y)) := by
    induction x with
    | tmul z y' => simp [B, baseChangePairing, smul_tmul']
    | add x x' hx hx' => simp [hx, hx']
  -- Write `1 ⊗ v l = ∑ k, a l k • d l k` with `d l k` invariant; pairing with the `d l k` maps
  -- equivariantly to copies of the character `χ ^ c` and also has a retraction.
  have h_span (l : ChooseBasisIndex R T) : ∃ (n : ℕ) (a : Fin n → Bmax)
      (d : Fin n → fixedPeriods ρ Bmax F), ∑ i, a i • (d i : Bmax ⊗[ℤ_[p]] T) = 1 ⊗ₜ v l :=
    mem_span_set'.1 (h_adm.ge (x := 1 ⊗ₜ v l) trivial)
  choose n a d hd using h_span
  have hσ : IsAdmissible σ F := by
    refine of_retraction hF (fun _ ↦ adm_char)
      (fun i : Σ l, Fin (n l) ↦ (baseChangePairing B).flip (d i.fst i.snd)) (fun i ↦ ?_)
      (Ψ ∘ₗ pi fun l ↦ ∑ k, a l k • proj ⟨l, k⟩) fun x ↦ ?_
    · filter_upwards [(d i.fst i.snd).prop] with g hg x
      have h_map : baseChangePairing B (tensorAction Bmax (toGp g) (σ g) x)
          (tensorAction Bmax (toGp g) (ρ g) (d i.fst i.snd)) =
          tensorAction Bmax (toGp g) (charRep R (χ ^ c) g)
            (baseChangePairing B x (d i.fst i.snd)) :=
        baseChangePairing_map B (h_equiv g) x (d i.fst i.snd) (smul_mul' (toGp g))
      rwa [hg] at h_map
    · simpa [← hd, LinearMap.pi, ↓h_coef] using hΨ (coeffEnd R _ 1 x)
  have h_pcr : IsPotentiallyCrystalline σ := hσ.mono hF
  refine ⟨hσ, fun s Q hs ⟨hρ, h_killed⟩ ↦ ⟨h_pcr, ?_⟩⟩
  -- As the pairings with the `1 ⊗ v l` have the left inverse `Ψ`, they are jointly injective, so it
  -- suffices to compare the pairings with the `1 ⊗ v l`.
  refine ext fun x ↦ hΨ.injective (funext fun l ↦ ?_)
  -- On inertia `linearFrob` is `1` for `χ ^ c`, so `linearFrob σ t⁻¹ 0` is adjoint to
  -- `linearFrob ρ t 0`.
  have h_one : linearFrob σ 1 0 = 1 := by simpa using linearFrob_pow h_pcr hs 0
  have h_adjoint (t : Γ) (ht : IsWeilPair (toGp t) 0) (x : Bmax ⊗[ℤ_[p]] T'')
      (y : Bmax ⊗[ℤ_[p]] T) :
      baseChangePairing B x (linearFrob ρ t 0 y) =
        baseChangePairing B (linearFrob σ t⁻¹ 0 x) y := by
    have h_pair : (baseChangePairing B).compl₁₂ (linearFrob σ t 0) (linearFrob ρ t 0) ∘ₗ
          linearFrob σ t⁻¹ 0 =
        (baseChangePairing B).compr₂ (linearFrob (charRep R (χ ^ c)) t 0) ∘ₗ
          linearFrob σ t⁻¹ 0 := by
      rw [linearFrob_baseChangePairing hρ ht h_pcr B (ρ' := charRep R (χ ^ c)) h_equiv adm_char]
    simp_all [DFunLike.ext_iff, ← End.mul_apply, ← linearFrob_mul,
      IsCrystalline.linearFrob_eq_one adm_char, isWeilPair_zero_iff]
  -- Move `Q(linearFrob σ s⁻¹ 0)` to the other side, where `Q` kills `(s, 0)`: `h_coef` moves the
  -- coefficients of `Q`, `h_adjoint` the powers of `linearFrob`.
  have h_pair_zero :
      baseChangePairing B x (eval₂ (coeffEnd R T) (linearFrob ρ s 0) Q (1 ⊗ₜ v l)) = 0 := by
    simp [h_killed]
  simp only [isWeilPair_zero_iff] at hs h_adjoint
  simpa [eval₂_eq_sum_range, ← linearFrob_pow, pow_mem, (commute_coeffEnd_linearFrob hρ ..).eq, *,
    isWeilPair_zero_iff] using h_pair_zero

end New.Period

/-!
## Crystalline descent from inertia

`New.Period.IsPotentiallyCrystalline.isCrystalline_of_inertia_fixes`: if `ρ` is potentially
crystalline (`New.Period.IsPotentiallyCrystalline`) and `New.Period.linearFrob ρ s 0 = 1` for every
`s` with `toGp s` in inertia, then `ρ` is crystalline (`New.Period.IsCrystalline`).
-/

section CrystallineDescent

open Submodule Subgroup IsIntegral Module.End NonarchimedeanGroup

/-- Descent: let `ρ` be a potentially crystalline representation of `Γ`, where `toGp : Γ → Gp p` has
open image. Suppose that for every `s` with `toGp s` in inertia (`IsWeilPair (toGp s) 0`),
`linearFrob ρ s 0` is the identity; this map is the `Bmax`-linear endomorphism of `Bmax ⊗ T` that
agrees with `toGp s ⊗ ρ s` on `Dpcris ρ`. Then `ρ` is crystalline, i.e. the elements of `Bmax ⊗ T`
fixed by all of `Γ` span it over `Bmax`. The field fixed by inertia and by a small open subgroup is
unramified, so its integers are Witt vectors, which lie in `Bmax`.

A variant of the criterion that a potentially crystalline representation is crystalline when inertia
fixes its D_pcris. -/
lemma New.Period.IsPotentiallyCrystalline.isCrystalline_of_inertia_fixes {p : ℕ} [ThePrime p]
    {Γ R T : Type*} [Group Γ] [CommRing R] [AddCommGroup T] [Module R T] [Algebra ℤ_[p] R]
    [Module ℤ_[p] T] [IsScalarTower ℤ_[p] R T] [𝒥 : OverGp Γ p] {ρ : Representation R Γ T}
    (h : IsPotentiallyCrystalline ρ)
    (hI : ∀ s : Γ, IsWeilPair (toGp s) 0 → linearFrob ρ s 0 = 1) :
    IsCrystalline ρ := by
  -- A period `y` fixed near `1` is fixed by the preimage of the open subgroup `U` generated by
  -- inertia and a small open `V`. Galois descent from `U` over the field `L` of algebraic elements
  -- of `Bmax` needs that whatever fixes the `U`-fixed part of `L` lies in `U`: the chart of `U` is
  -- unramified, and its constants lie in that part.
  refine eq_top_mono (span_le.mpr fun y hy ↦ ?_) h
  -- Every element of the open subgroup `V` is `toGp t` for some `t` that fixes `y`.
  obtain ⟨V, hV⟩ := is_nonarchimedean _ (nhds_one_le_map_nearOne Γ (Filter.image_mem_map hy))
  have inertia_normal : (inertiaGroup (Gp p) (intQpBar p)).Normal := by
    refine ⟨fun s hs g ↦ ?_⟩
    have h_conj := hs.conj g
    rwa [isLocalGalois_padic.mem_decompGroup g] at h_conj
  let U : OpenSubgroup (Gp p) :=
    ⟨inertiaGroup (Gp p) (intQpBar p) ⊔ V, isOpen_mono le_sup_right V.isOpen⟩
  have quotient_finite : Finite (Gp p ⧸ U.toSubgroup) := quotient_finite_of_isOpen _ U.isOpen
  -- The chart `c` of `U`: the group `U` fixes its constants `WittFq c.f` and `θ z` (`h_fix`), and
  -- `E = z + p` if `U` contains inertia (`h_unram`).
  obtain ⟨c, h_fix, -, h_unram, -⟩ := Lift.exists_kummerChart U.toSubgroup
    (𝒥 := ⟨U.toSubgroup.subtype, ⟨by simpa using U.isOpen⟩⟩)
  let L : Subalgebra ℚ_[p] Bmax := integralClosure ℚ_[p] Bmax
  let fieldL : Field L := (isField_of_isIntegral_of_isField' (Field.toIsField ℚ_[p])).toField
  refine span_subset_span L _ _
    (mem_span_fixed (A := L) 𝒥.toGp (U := U) (.tprod (actionRep _ Bmax toGp) (overZp ρ))
      (fun g a x ↦ tensorAction_smul ..) (fun g hg ↦ ?_) fun s hs ↦ ?_)
  · -- Write `toGp g = i * toGp t` with `i` in inertia and `toGp t ∈ V`; both `t` and `g / t` fix
    -- `y`.
    obtain ⟨i, hi, v, hv, h_eq⟩ := mem_sup_of_normal_left.mp hg
    obtain ⟨t, ht, rfl⟩ := hV hv
    have h_weil : IsWeilPair (toGp (g / t)) 0 := by simpa [isWeilPair_zero_iff, ← h_eq]
    have h_t : tensorAction Bmax (toGp t) (ρ t) y = y := ht
    -- `g / t` lies in inertia, where `linearFrob ρ (g / t) 0 = 1` by `hI`.
    have h_gt : tensorAction Bmax (toGp (g / t)) (ρ (g / t)) y = y := by
      rw [← linearFrob_zero_apply h h_weil hy, hI _ h_weil, Module.End.one_apply]
    show tensorAction Bmax (toGp g) (ρ g) y = y
    rw [← div_mul_cancel g t, map_mul, map_mul, ← tensorAction_tensorAction, h_t, h_gt]
  -- The constants are integral over `ℤ_[p]` and fixed by `U`, so `s` fixes them.
  have h_const : Lift.FixesLambda c.f s := by
    intro a
    let a' : Ainf := algebraMap (Lift.WittFq c.f) Ainf a
    let b : L := ⟨algebraMap Ainf Bmax a', (of_finite ℤ_[p] a).algebraMap.algebraMap.tower_top⟩
    have hb_fix (u : U.toSubgroup) : u • b = b := by
      have ha' : (u : Gp p) • a' = a' := (h_fix u).left a
      have h_val : (u : Gp p) • algebraMap Ainf Bmax a' = algebraMap Ainf Bmax a' := by
        rw [smul_algebraMap_eq_algebraMap_smul, ha']
      exact Subtype.ext h_val
    have hsb_val : s • algebraMap Ainf Bmax a' = algebraMap Ainf Bmax a' :=
      congrArg Subtype.val (hs ⟨b, hb_fix⟩)
    rw [smul_algebraMap_eq_algebraMap_smul] at hsb_val
    simpa using injective_BPlus_Bmax hsb_val
  -- As `U` contains inertia, `E = z + p`, so `θ z = -p` is fixed by `s`.
  obtain ⟨hE : c.E = c.z + p, -, -⟩ := h_unram (le_sup_left.trans U.toSubgroup.range_subtype.ge)
  have hz : s • theta c.z = theta c.z := by simp [← sub_eq_of_eq_add hE, c.theta_E]
  -- What fixes the constants and `θ z` lies in `U`.
  exact U.toSubgroup.range_subtype.le (c.chart_isChartOf s ⟨h_const, hz⟩)

end CrystallineDescent
