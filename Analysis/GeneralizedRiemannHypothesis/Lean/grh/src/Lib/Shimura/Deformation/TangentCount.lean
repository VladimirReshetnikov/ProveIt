import Lib.Shimura.CongruenceRelation.KernelReduction

/-!
# Counting w-torsion points bounds a space of natural semilinear functions by n − 1

`x` is a `k`-point of a family of abelian schemes with `𝓞 E`-action (`New.ThetaObject`).
`x.groupScheme` is its abelian variety, `x.baseHom : 𝓞 E → k` is the structure map and `w` its
kernel. A morphism `specOver k C ⟶ x.groupScheme` is a `C`-point, and `placeTorsion x C` is the
`𝓞 E`-module of the `C`-points killed by `w`; `placeTorsionMap ψ` carries such points along
`ψ : C → C'`, composing with `specOver.map ψ`. The main result is
`New.Variety.finrank_le_of_placeTorsion`; there `n = Fintype.card D.Index`.

## Relation to the literature

Known; see `Lib.Shimura.Deformation.TangentBound` for sources.
-/

namespace New.Variety

open Algebra Polynomial AlgebraicGeometry CategoryTheory Fintype IsAlgClosed LinearMap minpoly
  specOver Module Submodule RingHom TrivSqZeroExt Ideal Quotient FiniteField IsLocalRing
  CartesianMonoidalCategory

variable {E : Type} [Field E] [CMBase E] {D : PEL E}
  {k : Type} [Field k] [IsAlgClosed k]
  {Z : Scheme} {σ : Z ⟶ Spec (CommRingCat.of (NumberField.RingOfIntegers E))}
  {Y : ThetaFamily D Z σ} {x : ThetaObject Y (Spec ⟨k⟩)}

attribute [local instance low] Fintype.ofFinite in
/-- If x ↦ x^i, for a natural number i, is F-linear on an algebraically closed extension k of a
finite field F, then i is a power of |F|. -/
lemma mem_powers_card_of_isLinearMap_pow (F : Type*) {i : ℕ} [Field F] [Finite F] [Algebra F k]
    (h_lin : IsLinearMap F fun a : k ↦ a ^ i) :
    i ∈ Submonoid.powers (Nat.card F) := by
  -- Let `q = card F`. The fixed points of the `F`-linear map `x ↦ x ^ (q * i)` are the `q * i`
  -- roots of a separable polynomial, and a finite `F`-space has a power of `q` elements.
  let P : F[X] := X ^ (Fintype.card F * i) - X
  have h_sep : P.Separable := galois_poly_separable _ _ (ringChar.dvd (by simp))
  -- `x ↦ x ^ i` sends `0` to `0`, so `i ≠ 0`, and `card F > 1`.
  have h_ne : Fintype.card F * i ≠ 0 ∧ Fintype.card F * i ≠ 1 := by
    simpa [one_lt_card.ne'] using h_lin.map_zero
  have h_two : 2 ≤ Fintype.card F * i := (Nat.two_le_iff _).mpr h_ne
  let Φ : k →ₗ[F] k := h_lin.mk' _ ∘ₗ frobeniusAlgHom F k
  -- the fixed points of `Φ` are the roots of `P`
  have h_roots : rootSet P k = (Φ.fixedSubmodule : Set k) := by
    simp [Φ, P, Set.ext_iff, mem_rootSet, h_sep.ne_zero, sub_eq_zero, ← pow_mul]
  let V : Submodule F k := Φ.fixedSubmodule.copy (rootSet P k) h_roots
  let V_fintype : Fintype V := rootSetFintype _ k
  have h_card : Fintype.card F * i = Fintype.card F ^ finrank F V := calc
    _ = P.natDegree := (X_pow_card_sub_X_natDegree_eq F h_two).symm
    _ = Fintype.card V := (card_rootSet_eq_natDegree h_sep (splits _)).symm
    _ = _ := card_eq_pow_finrank
  -- The exponent is not `0`, so one factor `q` cancels.
  have h_pos : finrank F V ≠ 0 := fun h_zero ↦ by simp [h_card, h_zero] at h_two
  have h_pow : Fintype.card F * Fintype.card F ^ (finrank F V - 1) = Fintype.card F * i :=
    (mul_pow_sub_one h_pos _).trans h_card.symm
  exact ⟨finrank F V - 1, by simpa using h_pow⟩

/-- Suppose that the kernel of `x.baseHom` contains some `p ≠ 0`. Then `placeTorsion x k` is finite,
and there is a local ring `B` (that of the finite group scheme `placeTorsion x` at the origin) with
a universal point `u`: a homomorphism out of `B` is determined by the image of `u`, and every point
with values in a local ring `C` that reduces to `0` along some `C → k` is such an image. -/
lemma exists_local_universal_point {p : NumberField.RingOfIntegers E} (hp : x.baseHom p = 0)
    (hp₀ : p ≠ 0) :
    _root_.Finite (placeTorsion x k) ∧
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra k B) (_ : IsLocalRing B) (u : placeTorsion x B),
      (∀ {C : Type} [CommRing C] [Algebra k C],
        Function.Injective fun ψ : B →ₐ[k] C ↦ placeTorsionMap ψ u) ∧
      ∀ {C : Type} [CommRing C] [Algebra k C] [IsLocalRing C] (π : C →ₐ[k] k)
          (y : placeTorsion x C),
        placeTorsionMap π y = 0 → ∃ ψ : B →ₐ[k] C, placeTorsionMap ψ u = y := by
  -- With `ker x.baseHom = (p, c)` the points form the kernel of the finite map `κ = (p, c)`.
  obtain ⟨c, hc⟩ := IsDedekindDomain.exists_eq_span_pair (mem_ker.mpr hp) hp₀
  let κ : x.groupScheme ⟶ MonoidalCategoryStruct.tensorObj x.groupScheme x.groupScheme :=
    lift (p • 𝟙 x.groupScheme) (c • 𝟙 x.groupScheme)
  have hκ_fin : IsFinite κ.left := by
    -- `κ` followed by the first projection is `p • 𝟙`, which is finite.
    have : IsFinite (κ.left ≫ (fst x.groupScheme x.groupScheme).left) := by
      simpa only [κ, ← Over.comp_left, lift_fst] using
        (x.isIsogeny_smul_id hp₀).toIsFinite
    exact IsFinite.of_comp κ.left (fst x.groupScheme x.groupScheme).left
  have hκ {C : Type} [CommRing C] [Algebra k C] {y : specOver k C ⟶ x.groupScheme} :
      y ∈ placeTorsion x C ↔ y ≫ κ = 0 := by
    simp [κ, placeTorsion, hc, CartesianMonoidalCategory.hom_ext_iff,
      ← torsionBySet_eq_torsionBySet_span]
  -- The kernel of `κ` is a closed subscheme `ι : Spec Γ ⟶ x.groupScheme` with `Γ` finite over `k`.
  obtain ⟨Γ, ι, _, -, _, hι, h_lift⟩ := exists_finite_kernel_ring hκ_fin
  let u₀ : placeTorsion x Γ := ⟨ι, hκ.mpr hι⟩
  -- The points with values in `C` are the algebra maps `Γ → C`.
  have h_bij (C : Type) [CommRing C] [Algebra k C] :
      Function.Bijective fun ψ : Γ →ₐ[k] C ↦ placeTorsionMap ψ u₀ := by
    constructor
    · -- `ι` is a monomorphism and `specOver.map` is injective
      intro ψ₁ ψ₂ h_eq
      have h_val : specOver.map ψ₁ ≫ ι = specOver.map ψ₂ ≫ ι := congrArg Subtype.val h_eq
      exact map_bijective.injective ((Over.mono_of_mono_left ι).right_cancellation _ _ h_val)
    · -- a point killed by `κ` factors through `ι`
      intro y
      obtain ⟨ψ, hψ⟩ := map_bijective.surjective.exists.mp (h_lift _ (hκ.mp y.prop))
      exact ⟨ψ, Subtype.ext hψ⟩
  -- Localize `Γ` at the origin `o`.
  obtain ⟨o, ho : placeTorsionMap o u₀ = 0⟩ := (h_bij k).surjective 0
  let B : Type := Localization.AtPrime (comap o ⊥)
  -- A map out of `B` is determined by its restriction to `Γ`.
  have h_inj_B {C : Type} [CommRing C] [Algebra k C] :
      Function.Injective fun ψ : B →ₐ[k] C ↦
        placeTorsionMap ψ (placeTorsionMap (algHom k Γ B) u₀) := by
    intro ψ₁ ψ₂ h_eq
    have h_comp : placeTorsionMap (ψ₁.comp (algHom k Γ B)) u₀ =
        placeTorsionMap (ψ₂.comp (algHom k Γ B)) u₀ := by simpa using h_eq
    exact Localization.algHom_ext _ ((h_bij _).injective h_comp)
  refine ⟨.of_surjective _ (h_bij k).surjective, B, _, _, inferInstance,
    placeTorsionMap (algHom k Γ B) u₀, fun h_eq ↦ h_inj_B h_eq, fun π y hy ↦ ?_⟩
  obtain ⟨ψ, rfl : placeTorsionMap ψ u₀ = y⟩ := (h_bij _).surjective y
  -- As `π ∘ ψ = o`, the map `ψ` sends elements outside the kernel of `o` to units.
  have hψ : π.comp ψ = o := (h_bij k).injective (by simp [ho, hy])
  have hπ_surj : Function.Surjective π.toRingHom := fun c ↦ ⟨_, π.commutes c⟩
  have h_unit (g : primeCompl (Ideal.comap o ⊥)) : IsUnit (ψ g) := by
    have h_ne : π (ψ g) ≠ 0 := (AlgHom.congr_fun hψ g).trans_ne g.prop
    exact (IsLocalHom.of_surjective π.toRingHom hπ_surj).map_nonunit _ h_ne.isUnit
  refine ⟨IsLocalization.liftAlgHom h_unit, ?_⟩
  rw [← placeTorsionMap_comp]
  congr with g
  exact IsLocalization.lift_eq h_unit g

/-- If a nilpotent `τ` divides every element of the kernel of `z : B → k`, then `τ` generates the
`k`-algebra `B`, and each scaling `τ ↦ a • τ` extends to an endomorphism of `B`. -/
lemma adjoin_eq_top_and_exists_algHom_eq_smul {B : Type*} [CommRing B] [Algebra k B] (z : B →ₐ[k] k)
    {τ : B} {N : ℕ} (hN : τ ^ N = 0) (h_dvd : ∀ b : B, z b = 0 → τ ∣ b) :
    k[τ] = ⊤ ∧ ∀ a : k, ∃ σ : B →ₐ[k] B, σ τ = a • τ := by
  -- Descending induction: write `b = τ * d + z b`.
  have h_desc (m : ℕ) (h_mem : ∀ b : B, τ ^ m * b ∈ k[τ]) : k[τ] = ⊤ := by
    induction m with
    | zero => simpa [SetLike.ext_iff] using h_mem
    | succ m ih =>
      refine ih fun b ↦ ?_
      obtain ⟨d, hd⟩ := h_dvd (b - z b • 1) (by simp)
      rw [eq_add_of_sub_eq hd]
      simp [mul_add, ← mul_assoc, ← pow_succ, add_mem_cancel_left, h_mem, Subalgebra.smul_mem,
        pow_mem]
  have h_top : k[τ] = ⊤ := h_desc N (by simp [hN])
  -- The minimal polynomial of `τ` is a power of `X`, so it also kills `a • τ`.
  obtain ⟨m, -, hm⟩ := (dvd_prime_pow prime_X N).mp (dvd k τ (by simp [hN]))
  have h_minpoly_ne : minpoly k τ ≠ 0 := by simp [hm.eq_zero_iff]
  let pb : PowerBasis k B := PowerBasis.ofAdjoinEqTop (ne_zero_iff.mp h_minpoly_ne) h_top
  have hτ : τ ^ m = 0 := by simpa [dvd_iff] using hm.dvd
  refine ⟨h_top, fun a ↦ ?_⟩
  have h_aeval : aeval (a • τ) (X ^ m : k[X]) = 0 := by simp [_root_.smul_pow, hτ]
  exact ⟨pb.lift (a • τ) (aeval_eq_zero_of_dvd_aeval_eq_zero hm.dvd' h_aeval), pb.lift_gen _ _⟩

omit [IsAlgClosed k] in
/-- In a local `k`-algebra `B` with a `k`-point `z`, every `t ≠ 0` has a linear form `γ` with
`γ (t * b) = z b` for all `b`. -/
lemma exists_dual_mul_eq {B : Type*} [CommRing B] [Algebra k B] [IsLocalRing B] (z : B →ₐ[k] k)
    {t : B} (ht : t ≠ 0) :
    ∃ γ : Dual k B, ∀ b : B, γ (t * b) = z b := by
  -- `z` kills the annihilator of `t`, so it factors through multiplication by `t`.
  have hz_surj : Function.Surjective z.toRingHom := fun c ↦ ⟨algebraMap k B c, z.commutes' c⟩
  have h_ann (a : B) (ha : t * a = 0) : z a = 0 :=
    (ker_eq_maximalIdeal z.toRingHom hz_surj).ge fun ha_unit ↦ ht (ha_unit.mul_left_eq_zero.mp ha)
  -- so `z` lies in the range of the dual of multiplication by `t`
  have h_mem : z.toLinearMap ∈ LinearMap.range (mulLeft k t).dualMap :=
    (mulLeft k t).range_dualMap_eq_dualAnnihilator_ker.ge
      ((mem_dualAnnihilator z.toLinearMap).mpr h_ann)
  obtain ⟨γ, hγ⟩ : ∃ γ : Dual k B, (mulLeft k t).dualMap γ = z.toLinearMap := h_mem
  exact ⟨γ, fun b ↦ DFunLike.congr_fun hγ b⟩

/-- Let `τ ^ N = 0`. If for every factorisation `b = τ ^ i * g` with `τ ^ i ≠ 0` the cofactor `g` is
divisible by `τ`, then `b = 0`. -/
lemma eq_zero_of_dvd_cofactor {B : Type*} [CommRing B] {τ b : B} {N : ℕ} (hN : τ ^ N = 0)
    (h_dvd : ∀ (i : ℕ) (g : B), b = τ ^ i * g → τ ^ i ≠ 0 → τ ∣ g) :
    b = 0 := by
  have h_pow (i : ℕ) : τ ^ i ∣ b := by
    induction i with
    | zero => simp
    | succ i ih =>
      obtain ⟨g, hg⟩ := ih
      by_cases hi : τ ^ i = 0
      · simp [hg, hi]
      · simpa only [hg, pow_succ] using mul_dvd_mul_left _ (h_dvd i g hg hi)
  simpa [hN] using h_pow N

/-- Facts on a `k`-algebra `B` with a point `u` of `placeTorsion x`, a map `s : B → k[ε]` and
an element `τ`, relative to a line `L` of tangent vectors of `x.groupScheme` at `0`: `u` is
universal (as in `exists_local_universal_point`), `s` sends `u` to `L 1`, and `τ` is a nilpotent
local parameter of `B` that `s` sends to a nonzero multiple of `ε`. -/
structure IsLocalParameter (L : k →+ (specOver k (DualNumber k) ⟶ x.groupScheme)) (N : ℕ)
    {B : Type} [CommRing B] [Algebra k B] (u : placeTorsion x B) (s : B →ₐ[k] TrivSqZeroExt k k)
    (τ : B) : Prop where
  /-- A homomorphism out of `B` is determined by the image of `u`. -/
  injective : ∀ {C : Type} [CommRing C] [Algebra k C],
    Function.Injective fun ψ : B →ₐ[k] C ↦ placeTorsionMap ψ u
  /-- A point over a local `C` that reduces to `0` along `π : C → k` is an image of `u`. -/
  exists_map_eq : ∀ {C : Type} [CommRing C] [Algebra k C] [IsLocalRing C] (π : C →ₐ[k] k)
    (y : placeTorsion x C), placeTorsionMap π y = 0 → ∃ ψ : B →ₐ[k] C, placeTorsionMap ψ u = y
  /-- `s` sends `u` to the tangent vector `L 1`. -/
  val_eq : (placeTorsionMap s u).val = L 1
  /-- Scaling `ε` by `a` then sends `u` to `L a`. -/
  val_map_eq : ∀ a : k,
    (placeTorsionMap (TrivSqZeroExt.map (a • LinearMap.id)) (placeTorsionMap s u)).val = L a
  /-- `s τ` has no constant term. -/
  fst_eq_zero : (s τ).fst = 0
  /-- `s τ` has a nonzero `ε`-term. -/
  snd_ne_zero : (s τ).snd ≠ 0
  /-- `τ` is nilpotent of order at most `N`. -/
  pow_eq_zero : τ ^ N = 0
  /-- `τ` divides every element of `B` that `s` sends to a multiple of `ε`. -/
  dvd_of_fst_eq_zero : ∀ b : B, (s b).fst = 0 → τ ∣ b
  /-- Every tangent vector `L a` is the image under `s` of a point over `B`. -/
  exists_lift : ∀ a : k, ∃ y : placeTorsion x B, (placeTorsionMap s y).val = L a

/-- Let `ker x.baseHom` contain `p ≠ 0`, and let `L` be a line of tangent vectors of `x.groupScheme`
at `0` (`L 1 ≠ 0`, each `L m` reduces to `0`) on which `𝓞 E` acts through `x.baseHom`, scaled by
the maps `ε ↦ m ε`. Let `ν` map a type `T` to the `k`-points of `placeTorsion x` such that every
point `z` over a local `k`-algebra with a `k`-point `π` has a parameter `t` with `π t = 0` and
`t ^ N = 0`, `N` the size of the fibre of `ν` over the reduction of `z`, and with `z` zero
modulo `t` when its reduction is `0` (`h_param`). Then some local `k`-algebra `B`, point `u`, map
`s : B → k[ε]` and element `τ` satisfy `IsLocalParameter` for `L` and the fibre of `ν` over `0`. -/
lemma exists_isLocalParameter {p : NumberField.RingOfIntegers E} (hp : x.baseHom p = 0)
    (hp₀ : p ≠ 0) {L : k →+ (specOver k (DualNumber k) ⟶ x.groupScheme)} (hL_ne : L 1 ≠ 0)
    (hL_fst : ∀ m : k, specOver.map (fstHom k k k) ≫ L m = 0)
    (hL_smul : ∀ (a : NumberField.RingOfIntegers E) (m : k),
      a • L m = L (((algebraMap k k).comp x.baseHom) a * m))
    (hL_map : ∀ m : k,
      specOver.map (AlgHom.restrictScalars k (TrivSqZeroExt.map (m • LinearMap.id))) ≫ L 1 = L m)
    {T : Type} (ν : T → placeTorsion x k)
    (h_param : ∀ (B : Type) [CommRing B] [IsLocalRing B] [Algebra k B] (z : placeTorsion x B)
      (π : B →ₐ[k] k), ∃ t : B, π t = 0 ∧ t ^ Nat.card {t' : T // ν t' = placeTorsionMap π z} = 0 ∧
        (placeTorsionMap π z = 0 → ∀ (C : Type) [CommRing C] [Algebra k C] (G : B →ₐ[k] C),
          G t = 0 → placeTorsionMap G z = 0)) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra k B) (_ : IsLocalRing B) (u : placeTorsion x B)
      (s : B →ₐ[k] TrivSqZeroExt k k) (τ : B),
      IsLocalParameter L (Nat.card {t' : T // ν t' = 0}) u s τ := by
  obtain ⟨-, B, _, _, _, u, h_inj, h_fac⟩ := exists_local_universal_point hp hp₀
  -- The tangent vector `L 1` is given by `s : B → k[ε]`, and `z` is the origin.
  have hL_mem : L 1 ∈ placeTorsion x (TrivSqZeroExt k k) := by simp +contextual [hL_smul]
  obtain ⟨s, hs⟩ : ∃ s : B →ₐ[k] TrivSqZeroExt k k, (placeTorsionMap s u).val = L 1 :=
    (h_fac _ ⟨L 1, hL_mem⟩ (Subtype.ext (hL_fst 1))).imp fun _ ↦ congrArg Subtype.val
  have hs_map (a : k) :
      (placeTorsionMap (TrivSqZeroExt.map (a • .id)) (placeTorsionMap s u)).val = L a := by
    rw [← hL_map a, ← hs]; rfl
  let z : B →ₐ[k] k := (fstHom k k k).comp s
  have h_fst_u : specOver.map (fstHom k k k) ≫ (placeTorsionMap s u).val = 0 := by rw [hs, hL_fst]
  have hz : placeTorsionMap z u = 0 := (placeTorsionMap_comp ..).trans (Subtype.ext h_fst_u)
  -- `τ` vanishes at the origin, `u ≡ 0` modulo `τ`, and `τ ^ N = 0` where `N` is the size of the
  -- fibre of `ν` over `0`.
  obtain ⟨τ, hτ_fst : (s τ).fst = 0, hN, hτ_zero⟩ := h_param B u z
  rw [hz] at hN
  replace hτ_zero : ∀ (C : Type) [CommRing C] [Algebra k C] (G : B →ₐ[k] C),
      G τ = 0 → placeTorsionMap G u = 0 := hτ_zero hz
  -- Modulo `τ` the universal point is `0`, so `τ` generates the maximal ideal.
  have h_dvd (b : B) (hb : (s b).fst = 0) : τ ∣ b := by
    have h_pts : placeTorsionMap (mkₐ k (.span {τ})) u =
        placeTorsionMap ((ofId k (B ⧸ Ideal.span {τ})).comp z) u := by
      simp [hz, hτ_zero]
    have h_eq : mkₐ k (.span {τ}) = .comp (ofId k (B ⧸ Ideal.span {τ})) z := h_inj h_pts
    simpa [z, hb, eq_zero_iff_dvd] using AlgHom.congr_fun h_eq b
  obtain ⟨h_top, h_scale⟩ := adjoin_eq_top_and_exists_algHom_eq_smul z hN h_dvd
  have hτ_snd : (s τ).snd ≠ 0 := fun h_snd ↦
    -- otherwise `s τ = 0`, so `s` kills `u` and `L 1 = 0`
    hL_ne (by simp [← hs, hτ_zero _ s (ext hτ_fst h_snd)])
  -- Scaling `τ` lifts every tangent vector `L a` to a point over `B`.
  have h_lift (a : k) : ∃ y : placeTorsion x B, (placeTorsionMap s y).val = L a := by
    obtain ⟨σ, hσ⟩ := h_scale a
    have h_gen : ∀ b ∈ ({τ} : Set B), s.comp σ b = (TrivSqZeroExt.map (a • .id)).comp s b := by
      simp [TrivSqZeroExt.ext_iff, hσ, hτ_fst]
    have h_eq : s.comp σ = (TrivSqZeroExt.map (a • .id)).comp s :=
      AlgHom.ext_of_adjoin_eq_top h_top h_gen
    refine ⟨placeTorsionMap σ u, ?_⟩
    rw [← placeTorsionMap_comp, h_eq, placeTorsionMap_comp, hs_map]
  exact ⟨B, inferInstance, inferInstance, inferInstance, u, s, τ,
    { injective := fun h_eq ↦ h_inj h_eq, exists_map_eq := h_fac, val_eq := hs,
      val_map_eq := hs_map, fst_eq_zero := hτ_fst, snd_ne_zero := hτ_snd, pow_eq_zero := hN,
      dvd_of_fst_eq_zero := h_dvd, exists_lift := h_lift }⟩

/-- Let `u`, `s`, `τ` satisfy `IsLocalParameter` for the tangent line `L`, and let `f` be natural
in `C` (`hf`). On a point `y` over `B` that `s` sends to the tangent vector `L a`, the coefficient
of `τ ^ i` is multiplied by `a ^ i`: if `f B u l = τ ^ i * g`, `γ` reads the coefficient of
`τ ^ i` (`hγ`) and `(s g).fst ≠ 0`, then `a ^ i = γ (f B y l) / (s g).fst`. -/
lemma pow_eq_div_of_isLocalParameter {L : k →+ (specOver k (DualNumber k) ⟶ x.groupScheme)}
    (hL_fst : ∀ m : k, specOver.map (fstHom k k k) ≫ L m = 0)
    {N : ℕ} {B : Type} [CommRing B] [Algebra k B] [IsLocalRing B] {u : placeTorsion x B}
    {s : B →ₐ[k] TrivSqZeroExt k k} {τ : B} (hT : IsLocalParameter L N u s τ) {i : ℕ}
    {γ : Dual k B} (hγ : ∀ b : B, γ (τ ^ i * b) = (s b).fst)
    {W : Type*} [AddCommGroup W] [Module k W]
    (f : ∀ (C : Type) [CommRing C] [Algebra k C] [IsLocalRing C],
      placeTorsion x C →ₛₗ[x.baseHom] W →ₗ[k] C)
    (hf : ∀ {C C' : Type} [CommRing C] [Algebra k C] [CommRing C'] [Algebra k C'] [IsLocalRing C]
      [IsLocalRing C'] (ψ : C →ₐ[k] C') (z : ↥(placeTorsion x C)) (l : W),
      f C' (placeTorsionMap ψ z) l = ψ (f C z l))
    {l : W} {g : B} (h_factor : f B u l = τ ^ i * g) (hg : (s g).fst ≠ 0) {y : placeTorsion x B}
    {a : k} (hy : (placeTorsionMap s y).val = L a) :
    a ^ i = γ (f B y l) / (s g).fst := by
  let z : B →ₐ[k] k := (fstHom k k k).comp s
  have hy_fst : specOver.map (fstHom k k k) ≫ (placeTorsionMap s y).val = 0 := by rw [hy, hL_fst]
  obtain ⟨ψ, rfl⟩ := hT.exists_map_eq z y ((placeTorsionMap_comp ..).trans (Subtype.ext hy_fst))
  -- `ψ` scales `ε` by `a`.
  have h_comp : s.comp ψ = (TrivSqZeroExt.map (a • .id)).comp s := by
    simpa only [← placeTorsionMap_comp, ← hT.val_map_eq, SetLike.coe_eq_coe, hT.injective.eq_iff]
      using hy
  have hψ (b : B) : s (ψ b) = TrivSqZeroExt.map (a • .id) (s b) := AlgHom.congr_fun h_comp b
  obtain ⟨b, hb⟩ : τ ∣ ψ τ := hT.dvd_of_fst_eq_zero _ (by simp [hψ, hT.fst_eq_zero])
  have hb_fst : (s b).fst = a := by
    simpa [hb, hT.fst_eq_zero, hT.snd_ne_zero, mul_comm] using congrArg TrivSqZeroExt.snd (hψ τ)
  -- `ψ` sends `τ ^ i * g` to `τ ^ i * (b ^ i * ψ g)`, whose coefficient of `τ ^ i` is
  -- `a ^ i * (s g).fst`.
  have h_apply : f B (placeTorsionMap ψ u) l = τ ^ i * (b ^ i * ψ g) := by
    rw [hf, h_factor, map_mul, map_pow, hb, mul_pow, mul_assoc]
  rw [h_apply, hγ, eq_div_iff hg]
  simp [hψ, hb_fst]

/-- Let `u` be a point over the local `k`-algebra `B` through which every point that reduces to `0`
factors (`h_fac`), and let `f` be natural in `C` (`hf`). If `f B u l = 0` and `l` gives `0` at every
`k`-point, then `l` gives `0` at every point over a finite local `k`-algebra `C`: such a point is a
constant point plus one that factors through `u`. -/
lemma apply_eq_zero_of_apply_universal_eq_zero {B : Type} [CommRing B] [Algebra k B] [IsLocalRing B]
    {u : placeTorsion x B}
    (h_fac : ∀ {C : Type} [CommRing C] [Algebra k C] [IsLocalRing C] (π : C →ₐ[k] k)
      (y : placeTorsion x C), placeTorsionMap π y = 0 → ∃ ψ : B →ₐ[k] C, placeTorsionMap ψ u = y)
    {W : Type*} [AddCommGroup W] [Module k W]
    (f : ∀ (C : Type) [CommRing C] [Algebra k C] [IsLocalRing C],
      placeTorsion x C →ₛₗ[x.baseHom] W →ₗ[k] C)
    (hf : ∀ {C C' : Type} [CommRing C] [Algebra k C] [CommRing C'] [Algebra k C'] [IsLocalRing C]
      [IsLocalRing C'] (ψ : C →ₐ[k] C') (z : ↥(placeTorsion x C)) (l : W),
      f C' (placeTorsionMap ψ z) l = ψ (f C z l))
    {l : W} (h_zero : f B u l = 0) (h_const : ∀ y : placeTorsion x k, f k y l = 0)
    (C : Type) [CommRing C] [Algebra k C] [IsLocalRing C] [Module.Finite k C]
    (y : placeTorsion x C) :
    f C y l = 0 := by
  let π : C →ₐ[k] k := lift.comp (mkₐ k (maximalIdeal C))
  have h_red : placeTorsionMap π (y - placeTorsionMap (ofId k C) (placeTorsionMap π y)) = 0 := by
    -- `↓`: after `map_sub` splits the difference, simp must form `π ∘ ofId` before the inner
    -- `ofId ∘ π`.
    simp [↓map_sub, ↓← placeTorsionMap_comp]
  obtain ⟨ψ, hψ⟩ := h_fac π _ h_red
  -- `y` is the image of `u` plus a constant point, and `l` gives `0` at both.
  have h_split : f C y l = f C (placeTorsionMap ψ u) l +
      f C (placeTorsionMap (ofId k C) (placeTorsionMap π y)) l := by
    rw [hψ, map_sub, LinearMap.sub_apply, sub_add_cancel]
  have h_const_π : π (f C y l) = 0 := by rw [← hf π y l, h_const]
  rw [h_split]
  simp [hf, h_zero, h_const_π]

/-- The main step of `finrank_le_of_placeTorsion`. Let `u`, `s`, `τ` satisfy `IsLocalParameter`
for the tangent line `L`, let `γ i` read the coefficient of `τ ^ i` (`hγ`), and let `f` be as in
`finrank_le_of_placeTorsion`. If `l` gives `0` at every `k`-point and the coefficient of
`τ ^ q ^ j` in `f B u l` is `0` for every `j > 0` with `τ ^ q ^ j ≠ 0`, with `q` the norm of
`w = ker x.baseHom`, then `l = 0`: a lowest term of `f B u l` would have degree `q ^ j` with
`j > 0`. -/
lemma eq_zero_of_isLocalParameter (h_ker : RingHom.ker x.baseHom ≠ ⊥)
    {L : k →+ (specOver k (DualNumber k) ⟶ x.groupScheme)}
    (hL_fst : ∀ m : k, specOver.map (fstHom k k k) ≫ L m = 0)
    (hL_smul : ∀ (a : NumberField.RingOfIntegers E) (m : k),
      a • L m = L (((algebraMap k k).comp x.baseHom) a * m))
    {N : ℕ} {B : Type} [CommRing B] [Algebra k B] [IsLocalRing B] {u : placeTorsion x B}
    {s : B →ₐ[k] TrivSqZeroExt k k} {τ : B} (hT : IsLocalParameter L N u s τ)
    {γ : ℕ → Dual k B} (hγ : ∀ i : ℕ, τ ^ i ≠ 0 → ∀ b : B, γ i (τ ^ i * b) = (s b).fst)
    {W : Type*} [AddCommGroup W] [Module k W]
    (f : ∀ (C : Type) [CommRing C] [Algebra k C] [IsLocalRing C],
      placeTorsion x C →ₛₗ[x.baseHom] W →ₗ[k] C)
    (hf : ∀ {C C' : Type} [CommRing C] [Algebra k C] [CommRing C'] [Algebra k C'] [IsLocalRing C]
      [IsLocalRing C'] (ψ : C →ₐ[k] C') (z : ↥(placeTorsion x C)) (l : W),
      f C' (placeTorsionMap ψ z) l = ψ (f C z l))
    (hf_tangent : ∀ z : placeTorsion x (TrivSqZeroExt k k),
      specOver.map (fstHom k k k) ≫ z.val = 0 → f (TrivSqZeroExt k k) z = 0)
    (h_sep : ∀ l : W,
      (∀ (C : Type) [CommRing C] [Algebra k C] [IsLocalRing C] [Module.Finite k C]
        (z : ↥(placeTorsion x C)), f C z l = 0) → l = 0)
    {l : W} (h_const : ∀ y : placeTorsion x k, f k y l = 0)
    (h_coeff_zero : ∀ j : ℕ, 0 < j →
      τ ^ Nat.card (NumberField.RingOfIntegers E ⧸ RingHom.ker x.baseHom) ^ j ≠ 0 →
      γ (Nat.card (NumberField.RingOfIntegers E ⧸ RingHom.ker x.baseHom) ^ j) (f B u l) = 0) :
    l = 0 := by
  -- `pt a` lifts the tangent vector `L a` to `B`.
  choose pt h_pt using hT.exists_lift
  let F : Type := NumberField.RingOfIntegers E ⧸ RingHom.ker x.baseHom
  have h_max : (ker x.baseHom).IsMaximal := (ker_isPrime x.baseHom).isMaximal h_ker
  let F_field : Field F := Quotient.field _
  algebraize [x.baseHom.kerLift]
  set q : ℕ := Nat.card F
  -- The key step: `f B u l` has no lowest term `τ ^ i * g` with `g` a unit.
  have h_lowest (i : ℕ) (g : B) (h_factor : f B u l = τ ^ i * g) (hi : τ ^ i ≠ 0) :
      (s g).fst = 0 := by
    by_contra hg
    -- On a lift of `L a` the coefficient of `τ ^ i` is multiplied by `a ^ i`.
    have h_pow_eq_div (y : placeTorsion x B) (a : k) (hy : (placeTorsionMap s y).val = L a) :
        a ^ i = γ i (f B y l) / (s g).fst :=
      pow_eq_div_of_isLocalParameter hL_fst hT (hγ i hi) f hf h_factor hg hy
    -- `f` vanishes on tangent vectors, which excludes a linear term.
    have hi_ne : i ≠ 1 := by
      rintro rfl
      have h_zero : f (TrivSqZeroExt k k) (placeTorsionMap s u) = 0 :=
        hf_tangent _ (by rw [hT.val_eq, hL_fst])
      simpa [h_zero, h_factor, hT.fst_eq_zero, hT.snd_ne_zero, hg] using
        congrArg TrivSqZeroExt.snd (hf s u l)
    -- Semilinearity of `f` makes `a ↦ a ^ i` linear over `F`, so `i` is a power of `q`.
    have h_lin : IsLinearMap F fun a : k ↦ a ^ i := by
      refine ⟨fun a b ↦ ?_, Quot.ind fun a b ↦ ?_⟩
      · rw [h_pow_eq_div (pt a + pt b) (a + b) (by simp [h_pt])]
        simp [h_pow_eq_div _ _ (h_pt _), add_div]
      · -- the scalar `a` of `F` acts on `k` through `x.baseHom`
        show (x.baseHom a * b) ^ i = x.baseHom a * b ^ i
        rw [h_pow_eq_div (a • pt b) (x.baseHom a * b) (by simp [h_pt, hL_smul]),
          h_pow_eq_div _ _ (h_pt b)]
        simp [mul_div_assoc, smul_eq_mul]
    obtain ⟨j, rfl⟩ : i ∈ Submonoid.powers q := mem_powers_card_of_isLinearMap_pow F h_lin
    have hj : 0 < j := j.pos_of_ne_zero fun hj_zero ↦ hi_ne (by simp [hj_zero])
    exact hg (by rw [← hγ _ hi, ← h_factor, h_coeff_zero j hj hi])
  -- As `τ` is nilpotent and generates the maximal ideal, `f B u l` vanishes.
  have h_zero : f B u l = 0 :=
    eq_zero_of_dvd_cofactor hT.pow_eq_zero fun i g hg hi ↦
      hT.dvd_of_fst_eq_zero g (h_lowest i g hg hi)
  -- A point over a finite local `C` is a constant point plus one that factors through `u`.
  exact h_sep l (apply_eq_zero_of_apply_universal_eq_zero hT.exists_map_eq f hf h_zero h_const)

/-- Let `x` over `k` be the reduction, at a good place `w = ker x.baseHom` (which gives some `p ≠ 0`
in `w` and a tangent line at `0` on which `𝓞 E` acts through `x.baseHom`), of an object `y` over a
valuation subring of `ℂ` with a full structure. Let `f` attach to each `l ∈ W` a function
`y ↦ f C y l` from the `w`-torsion points over a local `k`-algebra `C` to `C`, semilinear in `y`
along `x.baseHom` and linear in `l`, such that (a) `f` is natural in `C`; (b) `f` vanishes on the
points over `k[ε]` that reduce to `0`; (c) only `l = 0` gives zero on all finite local `C`. Then
`dim W ≤ n - 1`, where `n = Fintype.card D.Index` is the number of indices of the PEL datum `D`. -/
lemma finrank_le_of_placeTorsion (hw : D.IsGoodAt (RingHom.ker x.baseHom)) {V : ValuationSubring ℂ}
    {φ : V →+* k} {y : ThetaObject Y (Spec (CommRingCat.of V))}
    (hy : x.IsPullbackAlong (specMap φ) y) (h_full : y.FullLevelStructure) {W : Type*}
    [AddCommGroup W] [Module k W]
    (f : ∀ (C : Type) [CommRing C] [Algebra k C] [IsLocalRing C],
      placeTorsion x C →ₛₗ[x.baseHom] W →ₗ[k] C)
    (hf : ∀ {C C' : Type} [CommRing C] [Algebra k C] [CommRing C'] [Algebra k C'] [IsLocalRing C]
      [IsLocalRing C'] (ψ : C →ₐ[k] C') (z : ↥(placeTorsion x C)) (l : W),
      f C' (placeTorsionMap ψ z) l = ψ (f C z l))
    (hf_tangent : ∀ z : placeTorsion x (TrivSqZeroExt k k),
      specOver.map (fstHom k k k) ≫ z.val = 0 → f (TrivSqZeroExt k k) z = 0)
    (h_sep : ∀ l : W,
      (∀ (C : Type) [CommRing C] [Algebra k C] [IsLocalRing C] [Module.Finite k C]
        (z : ↥(placeTorsion x C)), f C z l = 0) → l = 0) :
    Module.finrank k W ≤ Fintype.card D.Index - 1 := by
  -- The local ring `B` of `placeTorsion x` at the origin is `k[τ]` with `τ` nilpotent. The lowest
  -- term of `f B u l`, if any, has degree a power `q ^ j` of the norm `q` of `w = ker x.baseHom`,
  -- with `0 < j < n - dim (placeTorsion x k)`, where `n = card D.Index`. These coefficients and the
  -- values on `k`-points determine `l`, which bounds the dimension of `W`.
  obtain ⟨-, ⟨h_ker, p, hp, hp₀, -⟩, _, hβ, -⟩ :=
    ringChar_prime_and_exists_isCoprime_of_isGoodAt_ker hw
  -- `ν` reduces `w`-torsion sections to `k`-points. For a `w`-torsion point over a local `B` with a
  -- `k`-point, `h_card` gives a local parameter `τ` whose nilpotency is bounded by a fibre of `ν`.
  obtain ⟨ν, -, h_card⟩ := exists_param_pow_card_eq_zero hw h_full hy
  -- `L` is a line of tangent vectors at `0` on which `𝓞 E` acts through `x.baseHom`.
  obtain ⟨L, hL_ne, hL_fst, hL_smul, hL_map, -⟩ := exists_isLieLine x rfl hβ
  obtain ⟨h_finite, -⟩ := exists_local_universal_point hp hp₀
  obtain ⟨B, _, _, _, u, s, τ, hT⟩ :=
    exists_isLocalParameter hp hp₀ hL_ne hL_fst hL_smul hL_map ν h_card
  -- For `τ ^ i ≠ 0` the functional `γ i` reads the coefficient of `τ ^ i` in a multiple of `τ ^ i`.
  have h_coeff (i : ℕ) (hi : τ ^ i ≠ 0) : ∃ γ : Dual k B, ∀ b : B, γ (τ ^ i * b) = (s b).fst :=
    exists_dual_mul_eq ((fstHom k k k).comp s) hi
  choose! γ hγ using h_coeff
  -- `F` is the residue field at `w`, with `q` elements.
  let F : Type := NumberField.RingOfIntegers E ⧸ RingHom.ker x.baseHom
  have h_max : (ker x.baseHom).IsMaximal := (ker_isPrime x.baseHom).isMaximal h_ker
  let F_field : Field F := Quotient.field _
  algebraize [x.baseHom.kerLift]
  set q : ℕ := Nat.card F
  -- The `q ^ n` torsion sections map onto the `k`-points, so `q ^ (n - dim)` pass through `0`.
  have hν : Function.Surjective ν := by
    intro z
    -- `h_card` gives `t ^ N = 0` in `k`, so `N ≠ 0`: the fibre of `ν` over `z` is not empty.
    obtain ⟨t, -, ht, -⟩ := h_card k z (AlgHom.id k k)
    obtain ⟨-, h_card_ne⟩ := pow_eq_zero_iff'.mp ht
    obtain ⟨h_nonempty, -⟩ := Nat.card_ne_zero.mp h_card_ne
    simpa [placeTorsionMap] using h_nonempty
  have h_count : q ^ card D.Index = Nat.card ν.ker * q ^ finrank F (placeTorsion x k) := by
    have h_index : ν.ker.index = Nat.card (placeTorsion x k) := by
      rw [AddSubgroup.index_ker, ν.range_eq_top.mpr hν, AddSubgroup.card_top]
    rw [← natCard_eq_pow_finrank, ← h_index, ν.ker.card_mul_index]
    exact (card_torsionBySet_adelicTorsion h_ker).symm
  have h_lt {i : ℕ} (hi : τ ^ q ^ i ≠ 0) : i < card D.Index - finrank F (placeTorsion x k) := by
    have h_lt_card : q ^ i < Nat.card ν.ker := by
      simpa using (fun h_le ↦ pow_eq_zero_of_le h_le hT.pow_eq_zero).mt hi
    rw [lt_tsub_iff_right, ← pow_lt_pow_iff_right₀ (Finite.one_lt_card (α := F)), pow_add, h_count]
    exact Nat.mul_lt_mul_of_pos_right h_lt_card (pow_pos Nat.card_pos _)
  have h_pos : 0 < card D.Index - finrank F (placeTorsion x k) :=
    h_lt fun h_zero ↦ hT.snd_ne_zero (by rw [pow_zero, pow_one] at h_zero; simp [h_zero])
  -- `Φ l` lists the values of `l` on `k`-points and the coefficients of the `τ ^ q ^ j`, `j > 0`.
  let Φ : W →ₗ[k] (placeTorsion x k →ₗ[F] k) × (Set.Ioi (Fin.mk 0 h_pos) → k) :=
    -- the `F`-linear map `z ↦ f k z`; semilinearity along `x.baseHom` is linearity over `F`
    (⟨(f k).toAddHom, Quot.ind fun a z ↦ (f k).map_smul' a z⟩ :
      placeTorsion x k →ₗ[F] W →ₗ[k] k).flip.prod
      (.pi fun j : Set.Ioi (Fin.mk 0 h_pos) ↦ γ (q ^ (j.val : ℕ)) ∘ₗ f B u)
  -- The target has dimension `d + (n - d - 1)`, with `d` the dimension of `placeTorsion x k`.
  have h_dim : finrank k ((placeTorsion x k →ₗ[F] k) × (Set.Ioi (Fin.mk 0 h_pos) → k)) ≤
      card D.Index - 1 := calc
    _ = finrank F (placeTorsion x k) + (card D.Index - finrank F (placeTorsion x k) - 1) := by
      simp [finrank_linearMap]
    _ ≤ _ := by omega
  refine (Φ.finrank_le_finrank_of_injective ((injective_iff_map_eq_zero _).mpr fun l hl ↦ ?_)).trans
    h_dim
  -- `Φ l = 0`: `l` gives `0` at every `k`-point, and the coefficients of the `τ ^ q ^ j` vanish.
  have h_const (y : placeTorsion x k) : f k y l = 0 := LinearMap.congr_fun (congrArg Prod.fst hl) y
  exact eq_zero_of_isLocalParameter h_ker hL_fst hL_smul hT hγ f hf hf_tangent h_sep h_const
    fun j hj hi ↦ congrFun (congrArg Prod.snd hl) ⟨⟨j, h_lt hi⟩, hj⟩

end New.Variety
