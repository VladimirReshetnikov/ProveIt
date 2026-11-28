import Lib.ClassField.HeckeCharacter.AlgebraicValues
import Lib.ClassField.HeckeCharacter.SplitTameCharacters
import Lib.PadicHodge.Characters
import Lib.PadicHodge.Limit.CrystallineLimit

/-!
# Base change of U(1) and Hecke characters, their L-functions and parallel twists

Let `E` be a CM field with CM type `Φ`. A character `ν` of `U(1)(𝔸)` trivial on rational points
gives by base change the Hecke character `x ↦ ν(x / x̄)` of `E`. For `e ≠ 0` and `S` finite, its
`L`-function without the factors at `S ∪ S̄` does not vanish at real `s ≥ 1`. Algebraic Hecke
characters are also base changed along the norm.

## Main definitions and results

* `New.AutChar.L`: the Euler product of the base change, without the factors at `S ∪ S̄`.
* `New.AutChar.HasWeight.L_ne_zero`: for `e ≠ 0` and `S` finite, this `L`-function does not vanish
  at real `s ≥ 1`.
* `New.AutChar.HasWeight.toAlgebraic`: the algebraic Hecke character
  `ν(x / x̄) υ(x)^{-k} |x|^{j - k/2}`, with `υ` the splitting character of `New.SplittingChar`.
* `New.Variety.exists_twist_algHeckeChar`: twisting ρ by ω, controlled at the places w where ω is
  unramified and its type is one natural number d. The twist is by χ^d·μ, with χ the cyclotomic
  character and μ the ℓ-adic avatar of ω|·|^(−d), whose type vanishes over w.

Notions from other files:
* `New.AutChar`: The group of continuous circle-valued characters of U(1)(𝔸), the norm-one adeles of
  the CM field E, trivial on elements coming from E.
* `New.HeckeChar`: The group of unitary Hecke characters of E: continuous circle-valued characters
  of the idele group trivial on principal ideles.
* `New.IsHeckeOfType`: The character ψ of the finite ideles is the finite part of a Hecke character
  of type n: its kernel is open and ψ(x) ∏_w (Φ_w(x)/|Φ_w(x)|)^{n_w} = 1 on K^×.
* `New.IsHeckeOfType.toAlgebraic`: the algebraic character `ψ |·|^{k/2}` of infinity type `m`, for
  `ψ` of type `m (Φ w) - m (Φ̄ w)` with `m (Φ w) + m (Φ̄ w) = k` at every infinite place `w`.
* `New.AutChar.HasWeight`: μ has weight e and tame part ψ: almost all residue characters ψ_w are
  trivial, and μ(u) = ∏_v u_v^{e(v)} · ∏_w ψ_w(u mod w) whenever u has integral finite part.
* `New.heckeCoeff` φ S: the value of φ at the chosen uniformiser at v for v outside S, and 0 for v
  in S; `New.eulerProd` a is the Euler product ∏_v (1 - a_v q_v^(-s))⁻¹.

## Relation to the literature

Known; see `Lib.ClassField.HeckeL.ContinuationAtOne`,
`Lib.ClassField.Avatar.LocalGlobalCompatibility` and `Lib.ClassField.Global.CMSplittingCharacters`
for sources.
-/

noncomputable section

namespace New

/-!
## Base change of U(1) characters: L-function and algebraicity

Conventions: `ν.HasWeight e ψ` says that `ν` has weight `e` at infinity and tame part `ψ` (one
character `ψ w` of each residue field). `star` is complex conjugation, also on places. `χ.finPart`
is the restriction to finite ideles, and `χ.atUniformizer w` is the value at the chosen uniformiser
at `w`.
-/

section AutCharLFunction

open WeilData Finset Complex Real Variety

variable {E : Type _} [Field E] [CMType E] {e : NumberField.InfinitePlace E → ℤ} (ν : AutChar E)

lemma WeilData.charUnramifiedAt_upsilon [SplittingChar E] (v : FinPlace E) :
    CharUnramifiedAt υ.finPart v := by
  simp_all [CharUnramifiedAt, HeckeChar.finPart, upsilon_eq_atUniformizer_zpow v]

/-- The Euler product of the character `x ↦ ν (x / x̄)` of `E`, without the factors at `S ∪ S̄`.
It is the partial Hecke `L`-function if `S ∪ S̄` contains the ramified places. -/
def AutChar.L (S : Set (FinPlace E)) : ℝ → ℂ :=
  eulerProd (heckeCoeff ν.baseChange.finPart (Set.conjClosure S))

namespace AutChar.HasWeight

variable {ν} {S : Set (FinPlace E)}
  {ψ : (w : FinPlace E) → MulChar (ResField w) ℂ} [h : ν.HasWeight e ψ]
  {w : FinPlace E} (hψ_w : ψ w = 1) (hψ_star : ψ (star w) = 1)

include h

/-- Let `ν` have weight `e`. At an idele `y` with finite part `1`, the Hecke character
`y ↦ ν(y / ȳ) υ(y) ^ (-k)` takes the value `∏ w, (y_w / |y_w|) ^ (2 e_w - k)`. -/
lemma baseChange_mul_upsilon_zpow_inv_apply [WeilData E] (k : ℤ) (y : (𝔸 E)ˣ)
    (hy_fin : (y : 𝔸 E).2 = 1) :
    ((ν.baseChange * (υ ^ k)⁻¹).val y : ℂ) =
      ∏ w : NumberField.InfinitePlace E, ((y : 𝔸 E).1 w / ‖(y : 𝔸 E).1 w‖) ^ (2 * e w - k) := by
  let z : (NumberField.InfinitePlace E → ℂ)ˣ := y.map (MonoidHom.fst _ (𝔸f E))
  have hy : y = z.map (MonoidHom.inl _ (𝔸f E)) := Units.ext (Prod.ext rfl hy_fin)
  let u (w : NumberField.InfinitePlace E) : ℂ := z.val w / ‖z.val w‖
  have hu_ne (w : NumberField.InfinitePlace E) : u w ≠ 0 := by
    simpa [u] using (z.isUnit.apply w).ne_zero
  -- At infinity the base change has type `2 e` and `υ` has type `1`.
  have h_base : (ν.baseChange.val y : ℂ) = ∏ w, u w ^ (2 * e w) := by
    simpa [hy] using h.baseChange_apply_inf z
  have h_upsilon : (υ.val y : ℂ) = ∏ w, u w :=
    υ_unit y (by simp [show y.map (MonoidHom.snd _ (𝔸f E)) = 1 from Units.ext hy_fin])
  calc ((ν.baseChange * (υ ^ k)⁻¹).val y : ℂ)
      = (ν.baseChange.val y : ℂ) / (υ.val y : ℂ) ^ k := by
        cases k <;> simp [div_eq_mul_inv]
    _ = ∏ w, u w ^ (2 * e w) / u w ^ k := by
        rw [h_base, h_upsilon, ← prod_zpow, prod_div_distrib]
    _ = ∏ w, u w ^ (2 * e w - k) := prod_congr rfl fun w _ ↦ (zpow_sub₀ (hu_ne w) ..).symm

/-- Let `ν` be a character of `U(1)(𝔸)` of weight `e` with tame part `ψ`, and let `υ` be the
splitting character in the Weil data on `E`, whose component at each infinite place `w` is
`z ↦ z / |z|` in the chosen embedding. At an idele `y` with finite part `1`, the rank-`r` space
character `ν.spaceChar r : y ↦ ν(y / ȳ) υ(y) ^ (-r)` takes the value
`∏ w, (y_w / |y_w|) ^ (2 e_w - r)`, where `y_w` is the complex component of `y` at the infinite
place `w`. In this sense it has the weight `e - r / 2`. -/
theorem spaceChar_apply_of_snd_eq_one [WeilData E] (r : ℕ) (y : (𝔸 E)ˣ) (hy_fin : (y : 𝔸 E).2 = 1) :
    ((ν.spaceChar r).val y : ℂ) =
      ∏ w : NumberField.InfinitePlace E, ((y : 𝔸 E).1 w / ‖(y : 𝔸 E).1 w‖) ^ (2 * e w - r) := by
  rw [AutChar.spaceChar, inv_pow, ← zpow_natCast]
  exact h.baseChange_mul_upsilon_zpow_inv_apply r y hy_fin

/-- Let `ν` have weight `e ≠ 0` and some tame part, and let `S` be finite. Then the `L`-function of
`x ↦ ν(x / x̄)` without the factors at `S ∪ S̄` does not vanish at any real `s ≥ 1` (at `s = 1`
its value is the limit from the right, see `New.eulerProd`). -/
lemma L_ne_zero (hS : S.Finite) (he : e ≠ 0) {s : ℝ} (hs : 1 ≤ s) : ν.L S s ≠ 0 := by
  -- The square of the base change has a nonzero type at infinity, so it is not trivial.
  exact h.isHeckeOfType.eulerProd_ne_zero hS.conjClosure
    ((h.isHeckeOfType.pow 2).ne_one (by positivity)) hs

/-- If the tame part `ψ` of `ν` is trivial at `w` and at `w̄`, the base change of `ν` is unramified
at `w`. -/
lemma charUnramifiedAt (hψ_w : ψ w = 1) (hψ_star : ψ (star w) = 1) :
    CharUnramifiedAt ν.baseChange.finPart w := by
  -- By `exists_baseChange_finPart_locIdele` the value at a local unit `x` is `ψ w` at the reduction
  -- of `x / x̄`, a unit.
  intro x hx
  obtain ⟨h_int, h_eq⟩ := h.exists_baseChange_finPart_locIdele hψ_star x fun _ ↦ hx
  ext
  simp [h_eq, MulChar.one_apply, hψ_w]

/-- Let `ν` have weight `e` and tame part `ψ`, with `ψ w` and `ψ w̄` trivial. Then the Hecke
character `x ↦ ν (x / x̄)` takes mutually inverse values at the chosen uniformisers at `w̄` and at
`w`. -/
lemma atUniformizer_star (hψ_w : ψ w = 1) (hψ_star : ψ (star w) = 1) :
    ν.baseChange.atUniformizer (star w) = (ν.baseChange.atUniformizer w)⁻¹ := by
  have h_unr : CharUnramifiedAt ν.baseChange.finPart (star w) :=
    h.charUnramifiedAt hψ_star (by rwa [star_star])
  -- Conjugation inverts `x / x̄`, so it inverts the value of the base change.
  have h_div (x : (𝔸f E)ˣ) :
      divStar (.map (.inr (NumberField.InfinitePlace E → ℂ) (𝔸f E)) (star x) : (𝔸 E)ˣ) =
        (divStar (.map (.inr (NumberField.InfinitePlace E → ℂ) (𝔸f E)) x))⁻¹ :=
    Subtype.ext (Prod.ext (star_mul_star _ _) (star_mul' _ _)).symm
  have h_star (x : (𝔸f E)ˣ) : ν.baseChange.finPart (star x) = (ν.baseChange.finPart x)⁻¹ := by
    simp [HeckeChar.finPart, baseChange_apply_coe_toFun, h_div, Units.ext_iff]
  -- The conjugate of the uniformiser at `w` is a uniformiser at `star w`, where `ν.baseChange` is
  -- unramified.
  simpa [star_locIdele, h_unr.apply_locIdele_eq_zpow (.map _ _), HeckeChar.atUniformizer,
    Units.ext_iff]
    using h_star (locIdele w (uniformizer w))

/-- Let ν be a continuous circle-valued character of the norm-one adeles of the CM field E that is
trivial on E. Suppose ν has weight `e` and tame part `ψ`: almost all residue characters ψ_w are
trivial, and ν(u) = ∏_v u_v^{e(v)} · ∏_w ψ_w(u mod w) whenever u has integral finite part. If
ψ_v = 1 for all v ∉ S, then `ν⁻¹` and `ν` have the same `L`-function without the factors at
`S ∪ S̄`. -/
theorem L_inv (hS : ∀ v : FinPlace E, v ∉ S → ψ v = 1) : ν⁻¹.L S = ν.L S := by
  -- The Euler factor of `ν⁻¹` at `v` is that of `ν` at `star v`: both coefficients are `0` on
  -- `S ∪ S̄`, and outside it conjugation of the prime inverts the value of the base change.
  let c : FinPlace E → ℂ := heckeCoeff ν.baseChange.finPart S.conjClosure
  have h_coeff (v : FinPlace E) :
      heckeCoeff ν⁻¹.baseChange.finPart S.conjClosure v = c (star v) := by
    have hv_star : star v ∈ S.conjClosure ↔ v ∈ S.conjClosure := by simp [Set.conjClosure, or_comm]
    unfold c heckeCoeff
    by_cases hv : v ∈ S.conjClosure
    · rw [Set.indicator_of_notMem (not_not.mpr hv),
        Set.indicator_of_notMem (not_not.mpr (hv_star.mpr hv))]
    · obtain ⟨hv_out, hv_star_out⟩ : v ∉ S ∧ star v ∉ S := by
        simpa [Set.conjClosure, not_or] using hv
      rw [Set.indicator_of_mem hv, Set.indicator_of_mem (mt hv_star.mp hv)]
      simpa [HeckeChar.atUniformizer] using
        (h.atUniformizer_star (hS v hv_out) (hS (star v) hv_star_out)).symm
  -- Reindex the sum over the primes by conjugation, which preserves the norm `q`.
  have h_sum (s : ℝ) :
      ∑' v : FinPlace E, Complex.log (1 + -(c (star v) * (v.q : ℂ) ^ (-s : ℂ))) =
        ∑' v : FinPlace E, Complex.log (1 + -(c v * (v.q : ℂ) ^ (-s : ℂ))) := by
    simpa [q_star] using (Function.Involutive.toPerm star star_involutive).tsum_eq
      fun v : FinPlace E ↦ Complex.log (1 + -(c v * (v.q : ℂ) ^ (-s : ℂ)))
  unfold AutChar.L eulerProd
  simp only [h_coeff, h_sum]
  rfl

include hψ_w hψ_star

variable [WeilData E] (k j : ℤ)

open scoped Classical in
/-- For a character ν of U(1)(𝔸) of weight e, the algebraic Hecke character ν(x/x̄) υ(x)^{−k}
|x|^{j−k/2}, of infinity type j + e − k on the CM type, j − e on its conjugate. -/
def toAlgebraic : AlgHeckeChar E :=
  IsHeckeOfType.toAlgebraic (k := 2 * j - k)
    (m :=
      fun σ ↦
        j +
          if σ = Φ (NumberField.InfinitePlace.mk σ) then
            e (NumberField.InfinitePlace.mk σ) - k
          else
            -e (NumberField.InfinitePlace.mk σ))
    (by simp +arith)
    ((ν.baseChange * (υ ^ k)⁻¹).isHeckeOfType_finPart fun z ↦ by
      -- The type at infinity is `2 * e w - k = (j + (e w - k)) - (j - e w)`.
      rw [h.baseChange_mul_upsilon_zpow_inv_apply k _ rfl]
      refine prod_congr rfl fun w _ ↦ ?_
      congr 1
      simp +arith)

/-- The algebraic character made from `ν` is unramified at `w` if the tame part of `ν` is trivial at
`w` and at `w̄` (the section hypotheses `hψ_w`, `hψ_star`). -/
lemma charUnramifiedAt_toAlgebraic : CharUnramifiedAt (h.toAlgebraic k j).val.fst w := by
  -- The three factors `baseChange ν`, `υ` and the absolute value are each trivial on a local unit
  -- `u`.
  intro u hu
  ext
  simp [toAlgebraic, h.charUnramifiedAt hψ_w hψ_star u hu, charUnramifiedAt_upsilon w u hu, hu]

end AutChar.HasWeight

end AutCharLFunction

/-!
## Base change of algebraic Hecke characters and twists of parallel type

An element ω of `New.AlgHeckeChar` E is a pair (θ, n). Here θ = ω.1.1 is a character of the finite
ideles with open kernel, n = ω.1.2.toAdd is its type, and θ(x) = ∏_σ σ(x)^(−n_σ) on E^×.
`New.GaloisRep.IsSphericalAbove` ρ R J w P says that above w, ρ is unramified or crystalline, its
jump multiplicities are related to J by R, and P kills every geometric Frobenius.
-/

section HeckeTwist

variable {E K₀ : Type _}
  {ℓ : ℕ} [Field E] [EmbeddedNumberField E] [Field K₀] [NumberField K₀] [ThePrime ℓ]

open Polynomial GaloisRep Units Fintype Period

/-- For the norm from `E` to `K₀`: `∏ s, s (N x) ^ n s = ∏ σ, σ x ^ n (σ|K₀)`, the products running
over the complex embeddings of `K₀` and of `E`. -/
lemma prod_norm_zpow [Algebra K₀ E] (x : E) (n : (K₀ →+* ℂ) → ℤ) :
    ∏ s : K₀ →+* ℂ, s (Algebra.norm K₀ x) ^ n s =
      ∏ σ : E →+* ℂ, σ x ^ n (σ.comp (algebraMap K₀ E)) := by
  classical
  -- Group the `σ` by their restriction `s`; the norm is the product over the `σ` that extend `s`.
  rw [← prod_fiberwise fun σ : E →+* ℂ ↦ σ.comp (algebraMap K₀ E)]
  refine Finset.prod_congr rfl fun s _ ↦ ?_
  let s_algebra : Algebra K₀ ℂ := s.toAlgebra
  let extensions : {σ : E →+* ℂ // σ.comp (algebraMap K₀ E) = s} ≃ (E →ₐ[K₀] ℂ) :=
    { toFun σ := ⟨σ.val, RingHom.congr_fun σ.prop⟩
      invFun τ := ⟨τ, τ.comp_algebraMap⟩ }
  rw [show s (Algebra.norm K₀ x) = ∏ τ : E →ₐ[K₀] ℂ, τ x from Algebra.norm_eq_prod_embeddings ..,
    ← Finset.prod_zpow]
  exact (prod_equiv extensions _ (fun τ ↦ τ x ^ n s)
    fun σ ↦ congrArg (fun t ↦ σ.val x ^ n t) σ.prop).symm

/-- Base change `ω ∘ N` to `E` of an algebraic Hecke character `ω` of `K₀`; its exponent at an
embedding `σ` of `E` is that of `ω` at `σ|K₀`. -/
noncomputable def AlgHeckeChar.baseChange [Algebra K₀ E] (ω : AlgHeckeChar K₀) :
    AlgHeckeChar E where
  val :=
    (ω.1.1.comp (Units.map (adeleNorm K₀ E)),
      Multiplicative.ofAdd fun σ ↦ ω.1.2.toAdd (σ.comp (algebraMap K₀ E)))
  property := by
    refine ⟨ω.2.1.preimage (by fun_prop), fun x ↦ ?_⟩
    -- On a principal idele the norm of ideles is the norm of the fields.
    calc
      (ω.1.1 (map (adeleNorm K₀ E) (principalIdele x)) : ℂ)
      _ = ω.1.1 (principalIdele (x.map (Algebra.norm K₀))) :=
        congrArg (fun y ↦ (ω.1.1 y : ℂ)) (map_adeleNorm_principalIdele x)
      _ = ∏ s : K₀ →+* ℂ, s (Algebra.norm K₀ x.1) ^ (-ω.1.2.toAdd s) := ω.2.2 _
      _ = _ := prod_norm_zpow x.1 _

@[fun_prop]
lemma Selmer.continuous_cyclotomicCharIn :
  Continuous (cyclotomicCharIn (Γ := Gal(Ω/E)) (PadicAlgCl ℓ) Ω ℓ) :=
  (continuous_algebraMap ℤ_[ℓ] (PadicAlgCl ℓ)).units_map.comp (continuous_cyclotomicChar ℓ)

/-- The one-dimensional representation of `Gal(Ω/E)` by the scalars `μ g`. -/
def scalarRep (μ : Gal(Ω/E) →* (PadicAlgCl ℓ)ˣ) : Gal(Ω/E) →* GL (Fin 1) (PadicAlgCl ℓ) :=
  (Matrix.GeneralLinearGroup.scalar (Fin 1)).comp μ

/-- In a chart `L : PadicPlaceEmbedding E A ℓ` at `A` above `ℓ` (`decompRep` restricts to the
decomposition group at `A`; `cyclotomicGp` is the cyclotomic character of its image `L.toGp g`),
twisting the scalar representation of `μ` by the `d`-th power of the cyclotomic character is its
Tate twist by `d`. -/
private lemma decompRep_scalarRep_cyclotomicCharIn_pow_mul [PadicIso ℓ]
    (μ : Gal(Ω/E) →* (PadicAlgCl ℓ)ˣ)
    (A : ClosurePlace) (d : ℕ) [L : PadicPlaceEmbedding E A ℓ] (g : decompGroup Gal(Ω/E) A)
    (x : Fin 1 → PadicAlgCl ℓ) :
    decompRep (scalarRep (cyclotomicCharIn (PadicAlgCl ℓ) Ω ℓ ^ d * μ)) A g x =
      (cyclotomicGp (L.toGp g) ^ (d : ℤ)).val • decompRep (scalarRep μ) A g x := by
  simp [scalarRep, PadicPlaceEmbedding.cyclotomicGp_eq_cyclotomicChar, mul_smul, ← map_pow,
    ← smul_def]

/-- In a chart at `A` above `ℓ`, the scalar representation of `μ` is the Tate twist by `-d` of its
twist by the `d`-th power of the cyclotomic character. -/
private lemma decompRep_scalarRep_eq_cyclotomicCharIn_pow_mul [PadicIso ℓ]
    (μ : Gal(Ω/E) →* (PadicAlgCl ℓ)ˣ) (A : ClosurePlace) (d : ℕ) [L : PadicPlaceEmbedding E A ℓ]
    (g : decompGroup Gal(Ω/E) A) (x : Fin 1 → PadicAlgCl ℓ) :
    decompRep (scalarRep μ) A g x =
      (cyclotomicGp (L.toGp g) ^ (-d : ℤ)).val •
        decompRep (scalarRep (cyclotomicCharIn (PadicAlgCl ℓ) Ω ℓ ^ d * μ)) A g x := by
  rw [decompRep_scalarRep_cyclotomicCharIn_pow_mul]
  simp [smul_smul, ← mul_pow]

/-- Twisting a character by the `d`-th power of the cyclotomic character keeps it unramified or
crystalline at `A`. -/
lemma isGoodAt_scalarRep_cyclotomicCharIn_pow_mul [PadicIso ℓ] (μ : Gal(Ω/E) →* (PadicAlgCl ℓ)ˣ)
    (A : ClosurePlace) (d : ℕ) (h : IsGoodAt (scalarRep μ) A) :
    IsGoodAt (scalarRep (cyclotomicCharIn (PadicAlgCl ℓ) Ω ℓ ^ d * μ)) A := by
  obtain ⟨h_inertia, h_crys⟩ := h
  -- The cyclotomic character is trivial on inertia away from `ℓ`; the crystalline part passes to
  -- the Tate twist.
  refine ⟨?_, h_crys.tate_twist d (decompRep_scalarRep_cyclotomicCharIn_pow_mul μ A d)⟩
  simpa +contextual [scalarRep, cyclotomicChar_eq_one_of_mem_inertiaGroup (A := A)] using h_inertia

/-- Twisting a character by the `d`-th power of the cyclotomic character lowers its jumps at `A`
by `d`. -/
lemma hasJumpsAt_scalarRep_cyclotomicCharIn_pow_mul [PadicIso ℓ] (μ : Gal(Ω/E) →* (PadicAlgCl ℓ)ˣ)
    (A : ClosurePlace) (d : ℕ) (n : (E →+* ℂ) → ℤ)
    (h : HasJumpsAt (scalarRep μ) A fun τ : E →+* ℂ ↦ {n τ + d}) :
    HasJumpsAt (scalarRep (cyclotomicCharIn (PadicAlgCl ℓ) Ω ℓ ^ d * μ)) A fun τ : E →+* ℂ ↦
      {n τ} := by
  -- The jump `u` of the twist has the multiplicity of the jump `u + d` of `μ`.
  intro L γ τ hτ u
  simp [← jump_twist_cyclotomicGp (-d) (decompRep_scalarRep_eq_cyclotomicCharIn_pow_mul μ A d),
    ← h hτ,
    Multiset.count_singleton]

/-- Let μ be a character of Gal(Ω/E) with values in the algebraic closure of ℚ_ℓ, let A be a place
of Ω, and let s be such that s⁻¹ stabilises A and acts as x ↦ x^q modulo its maximal ideal, with
q ≠ 0. If X − q^d c kills s at A for the one-dimensional representation μ, then X − c kills s at A
for χ_ℓ^d · μ, where χ_ℓ is the ℓ-adic cyclotomic character. "P kills s at A" (`PolyKillsAt`) means
P(r(s)) = 0 when ℓ is a unit at A, and otherwise the Weil-pair condition `New.Period.IsKilledBy`
along every local datum at A. -/
lemma polyKillsAt_scalarRep_cyclotomicCharIn_pow_mul [PadicIso ℓ]
    (μ : Gal(Ω/E) →* (PadicAlgCl ℓ)ˣ) (A : ClosurePlace) (d : ℕ) (s : Gal(Ω/E)) (q : ℕ)
    (c : PadicAlgCl ℓ) (hq : q ≠ 0) (hs : IsFrob A q s⁻¹)
    (h : PolyKillsAt (scalarRep μ) A s (X - C (q ^ d * c))) :
    PolyKillsAt (scalarRep (cyclotomicCharIn (PadicAlgCl ℓ) Ω ℓ ^ d * μ)) A s (X - C c) := by
  -- It suffices to show that `q ^ d * (X - c)` kills `s`.
  obtain ⟨h_away, h_above⟩ :
      (A.valuation ℓ = 1 → aeval (scalarRep μ s).val (X - C ((q : PadicAlgCl ℓ) ^ d * c)) = 0) ∧
        ∀ [L : PadicPlaceEmbedding E A ℓ] ⦃hs : s ∈ decompGroup Gal(Ω/E) A⦄ ⦃k : ℕ⦄,
          IsWeilPair (L.toGp ⟨s, hs⟩) k →
            IsKilledBy (decompRep (scalarRep μ) A) ⟨s, hs⟩ k (X - C ((q : PadicAlgCl ℓ) ^ d * c)) :=
    h
  have hq_ne : (q : PadicAlgCl ℓ) ^ d ≠ 0 := by simp [hq]
  -- (the second field binds the chart `L` implicitly, hence `@fun`)
  refine .of_dvd (P := C ((q : PadicAlgCl ℓ) ^ d) * (X - C c))
    ⟨fun hℓ ↦ ?_, @fun L hs_dec k hk ↦ ?_⟩ ((C_mul_dvd hq_ne).mpr dvd_rfl)
  · -- Away from `ℓ` the cyclotomic character takes the value `q` at `s⁻¹`.
    have h_cyc : (q : PadicAlgCl ℓ) = algebraMap ℤ_[ℓ] (PadicAlgCl ℓ) (cyclotomicChar Ω ℓ s⁻¹) := by
      rw [hs.cyclotomicChar_eq ℓ hℓ]
      simp
    have h_val : aeval (scalarRep μ s).val (X - C (q ^ d * c)) = 0 := h_away hℓ
    -- `simp_all` unfolds the scalar representations and uses `h_cyc` and `h_val`.
    simp_all [sub_eq_zero, Matrix.algebraMap_eq_diagonal, scalarRep, Matrix.diagonal_pow,
      funext_iff]
  · -- Above `ℓ` we have `q = ℓ ^ k`, and the linear Frobenius of `μ` is `ℓ ^ (k * d)` times that
    -- of the twist.
    have h_frob : IsFrob (intQpBar ℓ) q (L.toGp ⟨s, hs_dec⟩)⁻¹ := by
      rwa [← map_inv, L.isFrob_iff]
    have hq_pow : q = ℓ ^ k := hk.eq_pow_of_isFrob h_frob
    obtain ⟨h_pcr, h_killed⟩ :
        IsKilledBy (decompRep (scalarRep μ) A) ⟨s, hs_dec⟩ k (X - C (q ^ d * c)) :=
      h_above hk
    have h_pcr_twist := h_pcr.tate_twist d (decompRep_scalarRep_cyclotomicCharIn_pow_mul μ A d)
    refine ⟨h_pcr_twist, ?_⟩
    rw [C_mul', eval₂_smul, ← h_killed, eq_comm, linearFrob_twist_cyclotomicGp h_pcr_twist hk d
      (decompRep_scalarRep_eq_cyclotomicCharIn_pow_mul μ A d)]
    rw [eval₂_sub, eval₂_C]
    simp [hq_pow, pow_mul, Algebra.smul_def, mul_sub]

/-- Mapping the Hecke polynomial of `t` by a ring homomorphism `f` gives the Hecke polynomial of
`f ∘ t`. -/
lemma map_heckePoly {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (q N : ℕ) (t : ℕ → R) :
    (heckePoly q N t).map f = heckePoly q N (f ∘ t) := by
  simp [heckePoly, Polynomial.map_sum]

/-- Let ω be an algebraic Hecke character of the CM field E of type n, and let ι = ιℓ be the fixed
isomorphism of ℂ with the algebraic closure of ℚ_ℓ. For continuous ρ there is a continuous ρ' (in
the proof, a twist of ρ) with the following property at every finite place w where ω is unramified
and n_σ = d for all σ with ισ inducing w. Put c = ω(ϖ_w), with ϖ_w the chosen uniformiser
`uniformizer w` at w. If `IsSphericalAbove` holds for ρ with jump data J and `heckePoly q a` of the
ι(t_j c^(−j)), it holds for ρ' with jump data J(τ) − n_τ and `heckePoly q a` of the ι(t_j). Here
`IsSphericalAbove ρ R J w P` means that at each place of Ω over w, ρ is good, its jump
multiplicities are R-related to J, and P kills geometric Frobenius. Also `heckePoly q a t = Σ_{j≤a}
(−1)^j q^{j(j−1)/2} t_j X^{a−j}`. -/
lemma Variety.exists_twist_algHeckeChar [PadicIso ℓ] [CMType E] (ω : AlgHeckeChar E) (d : ℕ)
    {ρ : PadicRep Gal(Ω/E) ℓ} (hρ : Continuous ρ.rep) :
    ∃ ρ' : PadicRep Gal(Ω/E) ℓ,
      Continuous ρ'.rep ∧
      -- at a place `w` where `ω` is unramified and of type `d` at all embeddings over `w`
      ∀ w : FinPlace E,
        (∀ σ : E →+* ℂ, inducedPrime σ = w → ω.val.2.toAdd σ = d) →
        CharUnramifiedAt ω.val.1 w →
        ∀ {R : ℕ → ℕ → Prop} {J : (E →+* ℂ) → Multiset ℤ} {q a : ℕ} {t : ℕ → ℂ},
          IsSphericalAbove ρ.rep R J w
            (heckePoly q a
              (ιℓ ∘ fun j : ℕ ↦ t j * (ω.val.1 (locIdele w (uniformizer w)) : ℂ)⁻¹ ^ j)) →
          IsSphericalAbove ρ'.rep R (fun τ : E →+* ℂ ↦ (J τ).map fun u : ℤ ↦ u - ω.val.2.toAdd τ) w
            (heckePoly q a (ιℓ ∘ t)) := by
  -- Twist by `ν = cyclotomicCharIn ^ d * μ`, with `μ` the avatar of `θ = ω |·| ^ (-d)`. The type of
  -- `θ` vanishes over `w`, so `avatarCompatAt_of_type_eq_zero` describes `μ` at `w`. The character
  -- `|·| ^ d`, of type `d`, is `IsHeckeOfType.toAlgebraic` of the trivial character with weight
  -- `k = 2 d`.
  have one_hecke : IsHeckeOfType (K := E) 1 fun _ ↦ (d - d : ℤ) := by
    simp [IsHeckeOfType, isOpen_iff_eventually]
  let θ : AlgHeckeChar E := ω / one_hecke.toAlgebraic (m := d) (k := d + d) (fun _ ↦ rfl)
  let μ : Gal(Ω/E) →* (PadicAlgCl ℓ)ˣ := θ.avatar
  let ν : Gal(Ω/E) →* (PadicAlgCl ℓ)ˣ := cyclotomicCharIn _ Ω ℓ ^ d * μ
  refine ⟨⟨twistByChar ν ρ.rep⟩, .of_coeHom_comp (.smul (by fun_prop) (by fun_prop)), ?_⟩
  intro w hd hω R J q a t hρ_sph A hA
  set c : ℂ := ((ω.val.1 (locIdele w (uniformizer w)) : ℂˣ) : ℂ) with hc
  have θ_val : heckeCoeff θ.val.fst ∅ w = w.q ^ d * c := by
    simp [heckeCoeff, θ, c, v_uniformizer, ← two_mul, zpow_mul, ← Complex.ofReal_pow, field]
  -- `θ` is unramified at `w`: `ω` is, and `|·| ^ d` is trivial on local units.
  have hθ_unr : ∀ x : (LocField w)ˣ, Valued.v x.val = 1 → θ.val.fst (locIdele w x) = 1 :=
    fun x hx ↦ by simp [θ, hω x hx, hx, Units.ext_iff]
  -- At `A`, `μ` is unramified or crystalline, has minus the type of `θ` as its jumps, and
  -- `X - ιℓ (θ ϖ_w)` kills every geometric Frobenius.
  obtain ⟨μ_unr, μ_jump, μ_frob⟩ :
      IsGoodAt (scalarRep μ) A ∧
        JumpsRelAt (scalarRep μ) A Eq (fun τ : E →+* ℂ ↦ {-θ.val.snd.toAdd τ}) ∧
        ∀ s : Gal(Ω/E), IsFrob A w.q s⁻¹ →
          PolyKillsAt (scalarRep μ) A s (X - C (ιℓ (heckeCoeff θ.val.fst ∅ w))) :=
    (avatarCompatAt_of_type_eq_zero θ
        fun σ hσ ↦ sub_eq_zero.mpr (hd σ hσ)).isSphericalAbove_of_unramified hθ_unr hA
  -- Being unramified or crystalline passes to the twist, jumps are shifted by the jump of `ν`, and
  -- `Q` kills `s` for the twist if `Q (c X)` kills it for `ρ` and `X - c` for `ν`.
  have h_twist (g : Gal(Ω/E)) : (twistByChar ν ρ.rep g).val = (ν g).val • (ρ.rep g).val := rfl
  obtain ⟨ρ_unr, ρ_jump, ρ_frob⟩ := hρ_sph hA
  refine ⟨ρ_unr.twist h_twist (isGoodAt_scalarRep_cyclotomicCharIn_pow_mul μ A d μ_unr),
    ρ_jump.twist h_twist (hasJumpsAt_scalarRep_cyclotomicCharIn_pow_mul μ A d _ ?_), fun s hs ↦ ?_⟩
  · simpa [μ, θ, IsHeckeOfType.toAlgebraic, neg_add_eq_sub] using μ_jump
  refine .twist (c := ιℓ c) ((ρ_frob s hs).of_dvd ⟨C (ιℓ c ^ a), ?_⟩) h_twist
    (polyKillsAt_scalarRep_cyclotomicCharIn_pow_mul μ A d s w.q _ w.one_lt_q.ne_zero hs ?_)
  · -- Substituting `ιℓ c * X` multiplies the term of `t j` by `ιℓ c ^ a / ιℓ c ^ j`.
    ext
    rw [← map_pow, coeff_mul_C]
    simp +contextual [coeff_heckePoly, c, apply_ite, pow_sub₀, field]
  · simpa [θ_val] using μ_frob s hs

end HeckeTwist

end New

end
