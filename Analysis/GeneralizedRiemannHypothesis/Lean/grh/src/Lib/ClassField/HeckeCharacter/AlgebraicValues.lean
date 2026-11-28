import Lib.ClassField.HeckeL.EulerProduct
import Lib.ClassField.Local.ArtinMap
import Lib.Cohomology.Etale.Basic
import Lib.Weil.Construction.FiniteMultiplier

/-!
# Values of algebraic Hecke characters

An algebraic Hecke character of a number field `K` is a character of the finite ideles with open
kernel that is `∏ τ, τ x ^ (-n τ)` on `Kˣ`, for integers `n τ` indexed by the complex embeddings of
`K`. Over a CM field, a unitary Hecke character of suitable type becomes algebraic after a twist by
a half-integral power of the absolute value. This is applied to the base change `y ↦ μ (y / ȳ)` of a
character `μ` of `U(1)(𝔸)` with a weight, and to `υ |·| ^ (-1 / 2)`, with `υ` the splitting
character of the Weil data.

## Main definitions and results

* `New.AlgHeckeChar.exists_pow_eq_prod`, `New.AlgHeckeChar.norm_map_eq_sqrt_finIdeleAbs_zpow`,
  `New.AlgHeckeChar.norm_padic_eq_prod`, `New.AlgHeckeChar.conjugateBy`: powers, complex and
  `p`-adic absolute values and conjugates of the values of an algebraic Hecke character.
* `New.IsHeckeOfType.toAlgebraic`: the algebraic character `ψ |·|^{k/2}` of infinity type `m`, for
  `ψ` of type `m (Φ w) - m (Φ̄ w)` with `m (Φ w) + m (Φ̄ w) = k` at every infinite place `w`.
* `New.AutChar.HasWeight.isHeckeOfType`: if `ν` has weight `e`, its base change has type `2 • e`.
* `New.AutChar.HasWeight.baseChangeAlgebraic`: this base change as an algebraic Hecke character.
* `New.AutChar.HasWeight.norm_map_eq_one`, `New.AutChar.HasWeight.norm_padic_eq_prod`: at a point
  `u` of `U(1)(𝔸)` with archimedean part `1`, the conjugates of the value `μ u` of a character of
  weight `e` have modulus `1`, and its absolute value under `ι : ℂ →+* ℂ_[p]` is
  `∏ τ, ‖u_τ‖ ^ (-e τ)`, with `u_τ` the component of `u` at the prime induced by `ι ∘ Φ τ`.
* `New.WeilData.chiFinAlgebraic`: the character `υ |·|^{-1/2}` as an algebraic Hecke character.

Notions from other files:
* `New.IsHeckeOfType`: The character ψ of the finite ideles is the finite part of a Hecke character
  of type n: its kernel is open and ψ(x) ∏_w (Φ_w(x)/|Φ_w(x)|)^{n_w} = 1 on K^×.
* `New.AutChar.HasWeight`: μ has weight e and tame part ψ: almost all residue characters ψ_w are
  trivial, and μ(u) = ∏_v u_v^{e(v)} · ∏_w ψ_w(u mod w) whenever u has integral finite part.
* `New.adeleExtension` σ: the extension of an embedding σ of E into `ℂ_[p]` to the finite adeles,
  through the prime that σ induces.

## Relation to the literature

Known result: the values of characters of type A₀. Source: A. Weil, On a certain type of characters
of the idèle-class group of an algebraic number-field (1956).
-/

noncomputable section

namespace New

/-!
## Values of algebraic Hecke characters

An element `θ` of `New.AlgHeckeChar K` is a pair of a character `θ.val.fst` of the finite ideles
with open kernel and exponents `n τ = θ.val.snd.toAdd τ`, one for each complex embedding `τ` of `K`,
such that the character is `∏ τ, τ x ^ (-n τ)` on `Kˣ`.
-/

namespace AlgHeckeChar

open NumberField Finset

variable {K : Type} [Field K] [NumberField K] (θ : AlgHeckeChar K) (y : (𝔸f K)ˣ)

/-- Let `θ` be an algebraic Hecke character with exponents `n τ` and `y` a finite idele. There are
`N > 0` and `γ` in `Kˣ` such that `y ^ N / γ` is a unit at all finite places and
`θ(y) ^ N = ∏ τ, τ γ ^ (-n τ)`. This is the key step in Weil's proof that characters of type A₀
take algebraic values on finite ideles. -/
theorem exists_pow_eq_prod :
    ∃ N > (0 : ℕ), ∃ γ : Kˣ,
      y ^ N / principalIdele γ ∈ idelesUnitOff ∅ ∧
      (θ.val.fst y : ℂ) ^ N = ∏ τ : K →+* ℂ, τ γ ^ (-θ.val.snd.toAdd τ) := by
  -- The principal ideles and the units in the kernel generate an open subgroup `H` of finite index.
  obtain ⟨h_open, (h_principal : ∀ x : Kˣ, (θ.val.fst (principalIdele x) : ℂ) =
      ∏ τ : K →+* ℂ, τ x ^ (-θ.val.snd.toAdd τ))⟩ := θ.property
  let H : Subgroup (𝔸f K)ˣ := principalIdele.range ⊔ (θ.val.fst.ker ⊓ idelesUnitOff ∅)
  have h_fin : H.FiniteIndex :=
    finiteIndex_idele_subgroup_of_isOpen H
      (Subgroup.isOpen_mono le_sup_right (h_open.inter (isOpen_idelesUnitOff ∅)))
      fun x _ ↦ Subgroup.mem_sup_left ⟨x, rfl⟩
  obtain ⟨_, ⟨γ, rfl⟩, u, ⟨hu_ker, hu_unit⟩, h_eq⟩ : ∃ a ∈ principalIdele.range,
      ∃ u ∈ θ.val.fst.ker ⊓ idelesUnitOff ∅, a * u = y ^ H.index :=
    Subgroup.mem_sup.1 (H.pow_index_mem y)
  refine ⟨H.index, h_fin.index_ne_zero.pos, γ, ?_, ?_⟩
  · rwa [← h_eq, mul_div_cancel_left]
  · rw [← Units.val_pow_eq_pow_val, ← map_pow, ← h_eq, map_mul,
      show θ.val.fst u = 1 from hu_ker, mul_one, h_principal]

/-- Let `γ` in `Kˣ` and the finite idele `y` be such that `y ^ N / γ` is a unit at all finite
places. Then the moduli of the conjugates `σ (τ γ)` have product `|y| ^ (-N)`, where `|y|` is the
norm of `y` and `τ` runs over the embeddings of `K`. This is the product formula for `γ`. -/
theorem prod_norm_map_embeddings_eq_inv_finIdeleAbs_pow {N : ℕ} {γ : Kˣ}
    (h_unit : y ^ N / principalIdele γ ∈ idelesUnitOff ∅) (σ : ℂ →+* ℂ) :
    ∏ τ : K →+* ℂ, ‖σ (τ γ)‖ = (finIdeleAbs y ^ N)⁻¹ := by
  have h_one : finIdeleAbs (y ^ N / principalIdele γ) = 1 := ideleAbs_finIdeleIncl_eq_one h_unit
  have h_prod : ∏ τ : K →+* ℂ, τ γ = (Algebra.norm ℚ γ.val : ℚ) :=
    ((RingHom.equivRatAlgHom K ℂ).prod_comp (· γ.val)).trans
      (Algebra.norm_eq_prod_embeddings ℚ ℂ γ.val).symm
  rw [← map_pow, ← div_mul_cancel (y ^ N) (principalIdele γ), map_mul, h_one, one_mul,
    finIdeleAbs_principalIdele, ← norm_prod, ← map_prod, h_prod]
  simp

/-- Let `K` be a CM field and `θ` an algebraic Hecke character whose exponents satisfy
`n τ + n τ̄ = j` for all `τ`. Then every conjugate `σ (θ y)` of a value has modulus `|y| ^ (j / 2)`,
where `|y|` is the norm of the finite idele `y`. -/
theorem norm_map_eq_sqrt_finIdeleAbs_zpow [IsCMField K] {j : ℤ}
    (hj : ∀ τ : K →+* ℂ, θ.val.snd.toAdd τ + θ.val.snd.toAdd (star τ) = j) (σ : ℂ →+* ℂ) :
    ‖σ (θ.val.fst y)‖ = √(finIdeleAbs y) ^ j := by
  -- The embeddings `σ τ` and `σ τ̄` are complex conjugate. So the square of the modulus of
  -- `σ (θ(y) ^ N)` is `∏ τ, |σ τ γ| ^ (-j)`, and `∏ τ, |σ τ γ|`, the modulus of the norm of `γ`, is
  -- `|y| ^ (-N)` by the product formula.
  obtain ⟨N, hN, γ, h_unit, h_pow⟩ : ∃ N > (0 : ℕ), ∃ γ : Kˣ,
      y ^ N / principalIdele γ ∈ idelesUnitOff ∅ ∧
      (θ.val.fst y : ℂ) ^ N = ∏ τ : K →+* ℂ, τ γ ^ (-θ.val.snd.toAdd τ) :=
    θ.exists_pow_eq_prod y
  have h_conj (τ : K →+* ℂ) : ‖σ (star τ γ)‖ = ‖σ (τ γ)‖ := by
    rw [show star τ γ = τ (star γ.val) from (map_star_complex τ γ).symm, ← σ.comp_apply,
      map_star_complex, norm_star, σ.comp_apply]
  have h_norm : ∏ τ : K →+* ℂ, ‖σ (τ γ)‖ = (finIdeleAbs y ^ N)⁻¹ :=
    prod_norm_map_embeddings_eq_inv_finIdeleAbs_pow y h_unit σ
  have h_value : ‖σ (θ.val.fst y)‖ ^ N = ∏ τ : K →+* ℂ, ‖σ (τ γ)‖ ^ (-θ.val.snd.toAdd τ) := by
    simp [← norm_pow, ← map_pow, h_pow]
  have h_value_conj :
      ‖σ (θ.val.fst y)‖ ^ N = ∏ τ : K →+* ℂ, ‖σ (τ γ)‖ ^ (-θ.val.snd.toAdd (star τ)) := by
    rw [h_value, ← Equiv.prod_comp (Function.Involutive.toPerm star star_involutive)]
    simp only [Function.Involutive.coe_toPerm, h_conj]
  -- It is enough to compare the powers with exponent `N * 2`.
  refine (pow_left_inj₀ (norm_nonneg _) (by positivity) (mul_ne_zero hN.ne' two_ne_zero)).1 ?_
  calc ‖σ (θ.val.fst y)‖ ^ (N * 2)
    _ = ∏ τ : K →+* ℂ, ‖σ (τ γ)‖ ^ (-j) := by
      rw [pow_mul, sq]
      nth_rw 1 [h_value]
      rw [h_value_conj, ← prod_mul_distrib]
      exact prod_congr rfl fun τ _ ↦ by rw [← zpow_add₀ (by simp), ← neg_add, hj]
    _ = finIdeleAbs y ^ ((N : ℤ) * j) := by
      rw [prod_zpow, h_norm, inv_zpow', neg_neg, zpow_mul, zpow_natCast]
    _ = (√(finIdeleAbs y) ^ j) ^ (N * 2) := by
      rw [← zpow_natCast (_ ^ j), zpow_comm, zpow_natCast, pow_mul',
        Real.sq_sqrt (show 0 ≤ finIdeleAbs y from ideleAbs_pos.le), zpow_mul, zpow_natCast]

/-- Let `θ` be an algebraic Hecke character with exponents `n τ`, and let `ι : ℂ →+* ℂ_[p]`. Then
`‖ι (θ y)‖ = ∏ τ, ‖y_τ‖ ^ (-n τ)`, where `y_τ` is the image in `ℂ_[p]` of the component of the
finite idele `y` at the prime induced by `ι ∘ τ`. -/
theorem norm_padic_eq_prod {p : ℕ} [Fact p.Prime] (ι : ℂ →+* ℂ_[p]) :
    ‖ι (θ.val.fst y)‖ =
      ∏ τ : K →+* ℂ, ‖adeleExtension (ι.comp τ) y.val‖ ^ (-θ.val.snd.toAdd τ) := by
  obtain ⟨N, hN, γ, h_unit, (h_pow : (θ.val.fst y : ℂ) ^ N =
      ∏ τ : K →+* ℂ, τ γ ^ (-θ.val.snd.toAdd τ))⟩ := θ.exists_pow_eq_prod y
  have h_norm (τ : K →+* ℂ) : ‖ι (τ γ)‖ = ‖adeleExtension (ι.comp τ) y.val‖ ^ N := by
    -- `y ^ N / γ` is a unit at the prime induced by `ι ∘ τ`.
    have h_val : ‖adeleExtension (ι.comp τ) (y ^ N / principalIdele γ).val‖ =
        ‖adeleExtension (ι.comp τ) 1‖ :=
      (norm_adeleExtension_eq_iff _ _).2
        (by simpa using mem_idelesUnitOff.1 h_unit _ (Set.notMem_empty _))
    rw [← norm_pow, ← map_pow, ← Units.val_pow_eq_pow_val,
      ← div_mul_cancel (y ^ N) (principalIdele γ), Units.val_mul, map_mul, norm_mul, h_val]
    simp
  refine (pow_left_inj₀ (norm_nonneg _) (by positivity) hN.ne').1 ?_
  calc ‖ι (θ.val.fst y)‖ ^ N
    _ = ∏ τ : K →+* ℂ, ‖ι (τ γ)‖ ^ (-θ.val.snd.toAdd τ) := by simp [← norm_pow, ← map_pow, h_pow]
    _ = (∏ τ : K →+* ℂ, ‖adeleExtension (ι.comp τ) y.val‖ ^ (-θ.val.snd.toAdd τ)) ^ N := by
      simp only [h_norm, ← zpow_natCast, zpow_comm _ (N : ℤ), prod_zpow]

/-- If the finite idele `y` is a unit at all primes above `p`, then the value `θ y` of an algebraic
Hecke character is a unit at `ι : ℂ →+* ℂ_[p]`. -/
theorem norm_padic_eq_one {p : ℕ} [Fact p.Prime] (ι : ℂ →+* ℂ_[p])
    (hy : ∀ w : FinPlace K, (p : 𝓞 K) ∈ w.asIdeal → Valued.v (y.val w) = 1) :
    ‖ι (θ.val.fst y)‖ = 1 := by
  have h_unit (τ : K →+* ℂ) :
      ‖adeleExtension (ι.comp τ) y.val‖ = ‖adeleExtension (ι.comp τ) 1‖ :=
    (norm_adeleExtension_eq_iff _ _).2 (by simpa using hy _ (natCast_mem_placeOfEmb _))
  simp [θ.norm_padic_eq_prod y ι, h_unit]

/-- The conjugate `σ ∘ θ` of an algebraic Hecke character `θ` by an automorphism `σ` of `ℂ`. It is
algebraic, and its exponent at `σ ∘ τ` is that of `θ` at `τ`. -/
def conjugateBy (σ : ℂ ≃+* ℂ) : AlgHeckeChar K where
  val :=
    ((Units.map σ.toMonoidHom).comp θ.val.fst,
      Multiplicative.ofAdd fun τ ↦ θ.val.snd.toAdd (σ.symm.toRingHom.comp τ))
  property := by
    obtain ⟨h_open, h_principal⟩ := θ.property
    have h_ker : θ.val.fst.ker ≤ ((Units.map σ.toMonoidHom).comp θ.val.fst).ker :=
      fun y (hy : θ.val.fst y = 1) ↦ by simp [hy]
    refine ⟨Subgroup.isOpen_mono h_ker h_open, fun x ↦ ?_⟩
    -- Reindex the product by `τ ↦ σ ∘ τ`.
    let e : (K →+* ℂ) ≃ (K →+* ℂ) :=
      { toFun τ := σ.toRingHom.comp τ
        invFun τ := σ.symm.toRingHom.comp τ
        left_inv τ := by simp [← RingHom.comp_assoc]
        right_inv τ := by simp [← RingHom.comp_assoc] }
    rw [← e.prod_comp]
    simp [e, h_principal, ← RingHom.comp_assoc]

/-- For an algebraic Hecke character `θ` of the number field `K`, an automorphism `σ` of `ℂ` and a
finite idele `y`, the finite-idele character of the conjugate `θ.conjugateBy σ` (that is, `σ ∘ θ`)
takes at `y` the value `σ` applied to the value of `θ` at `y`. -/
lemma conjugateBy_apply (σ : ℂ ≃+* ℂ) : ((θ.conjugateBy σ).val.fst y : ℂ) = σ (θ.val.fst y) := rfl

/-- The conjugate of the character `θ` by `σ` has at `σ ∘ τ` the exponent of `θ` at `τ`. -/
lemma conjugateBy_exponent (σ : ℂ ≃+* ℂ) (τ : K →+* ℂ) :
    (θ.conjugateBy σ).val.snd.toAdd (σ.toRingHom.comp τ) = θ.val.snd.toAdd τ := by
  simp [conjugateBy, ← RingHom.comp_assoc]

end AlgHeckeChar

/-! ## Algebraic characters from unitary Hecke characters of a CM field -/

section ToAlgebraic

open Finset Complex Real Variety

-- `Type _`: the algebraic characters need `E : Type`, the lemma on `finPart` has any universe.
variable {E : Type _} [Field E] [CMType E] {ψ : (𝔸f E)ˣ →* ℂˣ} {m : (E →+* ℂ) → ℤ} {k : ℤ}

/-- Let `Φ w` be the embedding of the CM type at an infinite place `w`. Suppose that
`m (Φ w) + m (Φ̄ w) = k` for every `w` and that the character `ψ` of the finite ideles is the finite
part of a Hecke character of type `m (Φ w) - m (Φ̄ w)`. This is the algebraic Hecke character
`ψ |·| ^ (k / 2)` of infinity type `m`. -/
def IsHeckeOfType.toAlgebraic
    (hk : ∀ w : NumberField.InfinitePlace E, m (Φ w) + m (star (Φ w)) = k)
    (H : IsHeckeOfType ψ fun w : NumberField.InfinitePlace E ↦ m (Φ w) - m (star (Φ w))) :
    AlgHeckeChar E where
  val :=
    (ψ *
        MonoidHom.toHomUnits (G := (𝔸f E)ˣ) (M := ℂ)
          { toFun a := √(finIdeleAbs a)
            map_one' := by simp
            -- Without `id (…)`, `simp` cannot evaluate this homomorphism below.
            map_mul' := id (by simp [finIdeleAbs]) } ^ k,
      Multiplicative.ofAdd m)
  property := by
    obtain ⟨h_open, h_principal⟩ := H
    refine ⟨?_, fun x ↦ ?_⟩
    · -- The kernel contains the open group `ψ.ker ⊓ idelesUnitOff ∅`, as `finIdeleAbs` is `1` on
      -- `idelesUnitOff ∅`.
      refine (ψ.ker ⊓ idelesUnitOff ∅).isOpen_mono (fun y hy ↦ ?_)
        (h_open.and (isOpen_idelesUnitOff _))
      obtain ⟨hy_ker, hy_unit⟩ := hy
      ext
      simp [show ψ y = 1 from hy_ker,
        show finIdeleAbs y = 1 from ideleAbs_finIdeleIncl_eq_one hy_unit]
    · -- For `z = Φ w x` and `k = a + b`, from `z * conj z = ‖z‖ ^ 2` we get
      -- `(z / ‖z‖) ^ (a - b) * ‖z‖ ^ (a + b) = z ^ a * conj z ^ b`.
      have h_place (w : NumberField.InfinitePlace E) :
          (Φ w x / ‖Φ w x‖) ^ (m (Φ w) - m (star (Φ w))) * ‖Φ w x‖ ^ k =
            Φ w x ^ m (Φ w) * starRingEnd ℂ (Φ w x) ^ m (star (Φ w)) := by
        simp [← hk w, div_zpow, zpow_add₀, zpow_sub₀, field, ← mul_zpow, mul_conj', sq]
      -- On `Eˣ` the value of `ψ` is given by its type, that of `finIdeleAbs` by the product
      -- formula.
      have h_psi := eq_inv_of_mul_eq_one_left (h_principal x)
      have h_sqrt : √|(Algebra.norm ℚ (x : E) : ℝ)| =
          ∏ w : NumberField.InfinitePlace E, ‖Φ w x‖ := by
        simp [abs_norm_eq_prod_norm_sq, sqrt_prod]
      -- After inverting both sides we compare products over the infinite places.
      simp [h_psi, h_sqrt, prod_embeddings_eq_prod_pairs, ← prod_zpow, ← mul_inv,
        ← prod_mul_distrib, h_place]

/-- At the idele `locIdele w x` (equal to `x` at `w` and `1` elsewhere), the value of
`ψ |·| ^ (k / 2)` is `ψ x` times the power `k` of the square root of `|x|_w`. The logarithm of the
valuation of `x` is minus its order, so `|x|_w = q_w ^ log (v x)`, where `q_w = w.q` is the size of
the residue field at `w`. -/
@[simp]
lemma IsHeckeOfType.toAlgebraic_locIdele
    (hk : ∀ w : NumberField.InfinitePlace E, m (Φ w) + m (star (Φ w)) = k)
    (H : IsHeckeOfType ψ fun w : NumberField.InfinitePlace E ↦ m (Φ w) - m (star (Φ w)))
    (w : FinPlace E) (x : (LocField w)ˣ) :
    ((H.toAlgebraic hk).val.fst (locIdele w x)).val =
      ψ (locIdele w x) * √w.q ^ (k * (Valued.v x.val).log) := by
  simp [toAlgebraic, norm_locField_eq_q_zpow, sqrt_eq_rpow, zpow_mul', ← rpow_zpow_comm]

/-- If the unitary Hecke character `χ` is `z ↦ ∏ w, (z w / ‖z w‖) ^ n w` at infinity, its finite
part has type `n`: it has open kernel and is inverse to `∏ w, (Φ w x / ‖Φ w x‖) ^ n w` on `Eˣ`. Here
`E` is a CM field and `Φ w` is the complex embedding that the CM type chooses to induce the infinite
place `w`. -/
lemma HeckeChar.isHeckeOfType_finPart {n : NumberField.InfinitePlace E → ℤ} (χ : HeckeChar E)
    (h_inf : ∀ z : (NumberField.InfinitePlace E → ℂ)ˣ,
      χ.val (Units.map (MonoidHom.inl (NumberField.InfinitePlace E → ℂ) (𝔸f E)) z) =
        ∏ w : NumberField.InfinitePlace E, (z.val w / ‖z.val w‖) ^ n w) :
    IsHeckeOfType χ.finPart n := by
  refine ⟨χ.finPart.ker.isOpen_of_mem_nhds (g := 1) ?_, fun x ↦ ?_⟩
  · -- A continuous character of a nonarchimedean group is trivial near `1`.
    let χf : (𝔸f E)ˣ →ₜ* Circle :=
      χ.val.comp
        ⟨Units.map (.inr (NumberField.InfinitePlace E → ℂ) (𝔸f E)), .units_map _ (.prodMk_right _)⟩
    refine (char_eventually_eq_one _ χf.continuous_toFun).mono fun y hy ↦ Units.ext ?_
    show (χf y : ℂ) = 1
    exact congrArg Subtype.val hy
  · -- `χ` is trivial on the principal idele of `x`, the product of its finite and infinite parts.
    let a : (𝔸 E)ˣ := .map (.inr (NumberField.InfinitePlace E → ℂ) (𝔸f E)) (principalIdele x) *
      .map (.inl (NumberField.InfinitePlace E → ℂ) (𝔸f E)) (x.map (.pi fun w ↦ Φ w))
    -- It is the image of `x` in the adeles.
    have h_one : χ.val a = 1 := χ.property a ⟨x.val, by aesop⟩
    simpa [a, h_inf, Circle.ext_iff, HeckeChar.finPart] using h_one

end ToAlgebraic

/-! ## Characters of U(1) with a weight -/

namespace AutChar.HasWeight

open NumberField Finset Complex Variety

section BaseChangeType

variable {E : Type*} [Field E] [CMType E] {e : InfinitePlace E → ℤ} {ν : AutChar E}
  {ψ : (w : FinPlace E) → MulChar (ResField w) ℂ}

/-- At infinity the base change `x ↦ ν (x / x̄)` of a character `ν` of weight `e` is
`z ↦ ∏ w, (z w / ‖z w‖) ^ (2 * e w)`. -/
lemma baseChange_apply_inf [h : ν.HasWeight e ψ] (z : (NumberField.InfinitePlace E → ℂ)ˣ) :
    ν.baseChange.val (Units.map (MonoidHom.inl (NumberField.InfinitePlace E → ℂ) (𝔸f E)) z) =
      ∏ w : NumberField.InfinitePlace E, (z.val w / ‖z.val w‖) ^ (2 • e) w := by
  -- The idele `z / z̄` has finite part `1`, so only the factors at infinity remain, and
  -- `z / z̄ = (z / |z|) ^ 2`.
  set x : (𝔸 E)ˣ := Units.map (MonoidHom.inl (NumberField.InfinitePlace E → ℂ) (𝔸f E)) z with hx
  have h_fin : (divStar x : 𝔸 E).snd ∈ Ô E := by simp [hx, coe_divStar]
  rw [show (ν.baseChange.val x : ℂ) = ν.val (divStar x) from rfl, h.apply_eq _ h_fin]
  suffices h_factor : ∀ v : NumberField.InfinitePlace E,
      z.val v * (starRingEnd ℂ (z.val v))⁻¹ = (z.val v / ‖z.val v‖) ^ 2 by
    simp [hx, coe_divStar, zpow_mul, ← OneMemClass.one_def, h_factor]
  exact fun v ↦ by grind [Complex.mul_conj', (z.isUnit.apply v).ne_zero]

/-- If the character `ν` of `U(1)(𝔸)` has weight `e` and tame part `ψ`, then the restriction of
`x ↦ ν (x / x̄)` to the finite ideles of `E` is the finite part of a Hecke character of type
`2 e`. -/
lemma isHeckeOfType [h : ν.HasWeight e ψ] : IsHeckeOfType ν.baseChange.finPart (2 • e) :=
  ν.baseChange.isHeckeOfType_finPart h.baseChange_apply_inf

end BaseChangeType

variable {E : Type} [Field E] [CMType E] {μ : AutChar E} {e : InfinitePlace E → ℤ}
  {ψ : (w : FinPlace E) → MulChar (ResField w) ℂ}

open scoped Classical in
/-- The base change `y ↦ μ (y / ȳ)` of a character `μ` of `U(1)(𝔸)` of weight `e`, on finite
ideles, as an algebraic Hecke character: its exponents are `e` on the CM type and `-e` on its
conjugate. -/
def baseChangeAlgebraic (h : μ.HasWeight e ψ) : AlgHeckeChar E :=
  IsHeckeOfType.toAlgebraic (k := 0)
    (m := fun σ : E →+* ℂ ↦
      if σ = Φ (InfinitePlace.mk σ) then e (InfinitePlace.mk σ) else -e (InfinitePlace.mk σ))
    (by simp)
    (μ.baseChange.isHeckeOfType_finPart fun z ↦ by simp [h.baseChange_apply_inf z, two_mul])

/-- For a character `μ` of weight `e`, the algebraic Hecke character `h.baseChangeAlgebraic`, which
is the base change of `μ` on finite ideles, has the exponent `e w` at the embedding `Φ w` of the CM
type and `-e w` at its conjugate. -/
lemma baseChangeAlgebraic_exponent (h : μ.HasWeight e ψ) (w : InfinitePlace E) :
    h.baseChangeAlgebraic.val.snd.toAdd (Φ w) = e w ∧
    h.baseChangeAlgebraic.val.snd.toAdd (star (Φ w)) = -e w := by
  simp [baseChangeAlgebraic, IsHeckeOfType.toAlgebraic]

/-- Let `μ` have weight `e` and tame part `ψ`. If `u` in `U(1)(𝔸)` has archimedean part `1`, then
its finite part is `y / ȳ` for a finite idele `y`, and `μ u` is the value at `y` of the base change
of `μ`. -/
lemma exists_baseChangeAlgebraic_apply_eq (h : μ.HasWeight e ψ) (u : unitary (𝔸 E))
    (hu : (u : 𝔸 E).fst = 1) :
    ∃ y : (𝔸f E)ˣ,
      (u : 𝔸 E).snd = y.val * star (y⁻¹).val ∧
      (h.baseChangeAlgebraic.val.fst y : ℂ) = μ.val u := by
  obtain ⟨y, hy⟩ := exists_snd_div_divStar_finIdeleIncl_eq_one u
  have h_fst : ((u / divStar (finIdeleIncl y) : unitary (𝔸 E)) : 𝔸 E).fst = 1 := by
    simp [div_eq_mul_inv, ← map_inv, hu, coe_divStar, finIdeleIncl]
  obtain rfl : u = divStar (finIdeleIncl y) := div_eq_one.1 (Subtype.ext (Prod.ext h_fst hy))
  refine ⟨y, rfl, ?_⟩
  simp [baseChangeAlgebraic, IsHeckeOfType.toAlgebraic, HeckeChar.finPart,
    baseChange_apply_coe_toFun]

/-- Let `μ` have weight `e` and tame part `ψ`. If `u` in `U(1)(𝔸)` has archimedean part `1`, then
`|σ (μ u)| = 1` for every ring homomorphism `σ : ℂ → ℂ`. -/
lemma norm_map_eq_one [h : μ.HasWeight e ψ] (u : unitary (𝔸 E)) (hu : (u : 𝔸 E).fst = 1)
    {F : Type*} [FunLike F ℂ ℂ] [RingHomClass F ℂ ℂ] (σ : F) :
    ‖σ (μ.val u)‖ = 1 := by
  obtain ⟨y, -, h_val⟩ := h.exists_baseChangeAlgebraic_apply_eq u hu
  have h_sum (τ : E →+* ℂ) : h.baseChangeAlgebraic.val.snd.toAdd τ +
      h.baseChangeAlgebraic.val.snd.toAdd (star τ) = 0 := by
    obtain ⟨h_pos, h_neg⟩ := h.baseChangeAlgebraic_exponent (InfinitePlace.mk τ)
    obtain h_eq | h_eq : Φ (InfinitePlace.mk τ) = τ ∨ star (Φ (InfinitePlace.mk τ)) = τ :=
      InfinitePlace.mk_eq_iff.1 (mk_Φ _) <;>
    · rw [← h_eq]
      simp [h_pos, h_neg]
  simpa [h_val] using h.baseChangeAlgebraic.norm_map_eq_sqrt_finIdeleAbs_zpow y h_sum (σ : ℂ →+* ℂ)

/-- Let `μ` have weight `e` and tame part `ψ`, let `ι : ℂ →+* ℂ_[p]`, and let `u` in `U(1)(𝔸)` have
archimedean part `1`. Then `‖ι (μ u)‖ = ∏ τ, ‖u_τ‖ ^ (-e τ)` over the infinite places `τ`, where
`u_τ` is the image in `ℂ_[p]` of the finite part of `u` at the prime induced by `ι ∘ Φ τ`, with `Φ`
the CM type. -/
lemma norm_padic_eq_prod {p : ℕ} [Fact p.Prime] (h : μ.HasWeight e ψ) (ι : ℂ →+* ℂ_[p])
    (u : unitary (𝔸 E)) (hu : (u : 𝔸 E).fst = 1) :
    ‖ι (μ.val u)‖ =
      ∏ τ : InfinitePlace E, ‖adeleExtension (ι.comp (Φ τ)) (u : 𝔸 E).snd‖ ^ (-e τ) := by
  obtain ⟨y, h_snd, h_val⟩ := h.exists_baseChangeAlgebraic_apply_eq u hu
  rw [← h_val, AlgHeckeChar.norm_padic_eq_prod, prod_embeddings_eq_prod_pairs, h_snd]
  refine prod_congr rfl fun w _ ↦ ?_
  obtain ⟨h_pos, h_neg⟩ := h.baseChangeAlgebraic_exponent w
  -- The conjugate embedding reads `y` at the conjugate prime.
  have h_emb : ι.comp (star (Φ w)) = (ι.comp (Φ w)).comp (starRingEnd E) := by
    ext x
    simp [starRingEnd_apply (R := E)]
  have h_star : adeleExtension (ι.comp (Φ w)) (star (y⁻¹).val) =
      (adeleExtension (ι.comp (star (Φ w))) y.val)⁻¹ := by
    rw [adeleExtension_star, h_emb, map_units_inv]
  rw [map_mul, h_star, norm_mul, norm_inv, mul_zpow, inv_zpow', h_pos, h_neg]

end AutChar.HasWeight

/-! ## The character `υ |·| ^ (-1 / 2)` on finite ideles -/

namespace WeilData

open NumberField Finset Variety

variable {E : Type} [Field E] [CMType E] [WeilData E]

open scoped Classical in
/-- The character `υ |·| ^ (-1 / 2)` of the finite ideles, with `υ` the splitting character, as an
algebraic Hecke character: its exponents are `0` on the CM type and `-1` on its conjugate. -/
def chiFinAlgebraic : AlgHeckeChar E :=
  IsHeckeOfType.toAlgebraic (k := -1)
    (m := fun σ : E →+* ℂ ↦ if σ = Φ (InfinitePlace.mk σ) then 0 else -1)
    (by simp)
    ((υ : HeckeChar E).isHeckeOfType_finPart fun z ↦ by
      simpa using υ_unit (z.map (MonoidHom.inl (InfinitePlace E → ℂ) (𝔸f E)))
        ⟨one_mem _, one_mem _⟩)

/-- Let `E` be a CM field with a chosen CM type and Weil data, and let `υ` be the splitting
character. For every finite idele `x`, the finite-idele character underlying the algebraic Hecke
character `chiFinAlgebraic`, evaluated at `x` and read in `ℂ`, equals
`chiFin x = υ(x)|x|^(-1/2)`. -/
lemma chiFinAlgebraic_apply (x : (𝔸f E)ˣ) :
    (chiFinAlgebraic.val.fst x : ℂ) = chiFin x := by
  simp [chiFinAlgebraic, IsHeckeOfType.toAlgebraic, HeckeChar.finPart, chiFin, chiAdelic,
    finIdeleAbs]

/-- The algebraic Hecke character `υ |·| ^ (-1 / 2)` has the exponent `0` at the embedding `Φ w` of
the CM type and `-1` at its conjugate. -/
lemma chiFinAlgebraic_exponent (w : InfinitePlace E) :
    chiFinAlgebraic.val.snd.toAdd (Φ w) = 0 ∧
    chiFinAlgebraic.val.snd.toAdd (star (Φ w)) = -1 := by
  simp [chiFinAlgebraic, IsHeckeOfType.toAlgebraic]

/-- For Weil data on `E` and a finite idele `x`, there are `n > 0` and `y` in `Eˣ` such that `x ^ n`
and `y` have the same valuation at every finite place and
`(υ(x) |x| ^ (-1 / 2)) ^ n = ∏ v, Φ v ȳ`, over the embeddings `Φ v` of the CM type. -/
lemma exists_chiFin_pow_eq_prod (x : (𝔸f E)ˣ) :
    ∃ n > (0 : ℕ), ∃ y : Eˣ,
      (∀ w : FinPlace E, Valued.v ((x ^ n).val w) = Valued.v ((principalIdele y).val w)) ∧
      chiFin x ^ n = ∏ v : InfinitePlace E, Φ v (starRingEnd E y) := by
  obtain ⟨n, hn, y, h_unit, (h_pow : (chiFinAlgebraic.val.fst x : ℂ) ^ n =
      ∏ τ : E →+* ℂ, τ y ^ (-(chiFinAlgebraic (E := E)).val.snd.toAdd τ))⟩ :=
    chiFinAlgebraic.exists_pow_eq_prod x
  refine ⟨n, hn, y, fun w ↦ ?_, ?_⟩
  · have h_one := mem_idelesUnitOff.1 h_unit w id
    rw [← div_mul_cancel (x ^ n) (principalIdele y), Units.val_mul]
    simp [h_one]
  · -- The exponents are `0` on the CM type and `-1` on its conjugate.
    rw [← chiFinAlgebraic_apply, h_pow, prod_embeddings_eq_prod_pairs]
    refine prod_congr rfl fun v _ ↦ ?_
    simp [chiFinAlgebraic_exponent v, starRingEnd_apply (R := E), map_star_complex]

/-- For an embedding `ι` of `ℂ` into `ℂ_[p]`, the `p`-adic absolute value of
`υ(x) |x| ^ (-1 / 2)` is the product over the infinite places `v` of the absolute values of `x`
under the extension to the finite adeles of `y ↦ ι (Φ v ȳ)`, the embedding `weightEmbedding ι v`. -/
lemma norm_map_chiFin {p : ℕ} [Fact p.Prime] (ι : ℂ →+* ℂ_[p]) (x : (𝔸f E)ˣ) :
    ‖ι (chiFin x)‖ = ∏ v : InfinitePlace E, ‖adeleExtension (weightEmbedding ι v) x.val‖ := by
  rw [← chiFinAlgebraic_apply, chiFinAlgebraic.norm_padic_eq_prod, prod_embeddings_eq_prod_pairs]
  refine prod_congr rfl fun v _ ↦ ?_
  -- The exponents are `0` on the CM type and `-1` on its conjugate.
  have h_emb : ι.comp (star (Φ v)) = weightEmbedding ι v := by
    ext y
    simp [starRingEnd_apply (R := E), map_star_complex]
  simp [chiFinAlgebraic_exponent v, h_emb]

end WeilData

end New

end
