import Lib.ClassField.Global.ExistenceTheorem
import Lib.GaloisRep.Main.LocalConditions
import Lib.General.NumberTheory.PadicLimitsValuation

/-!
# p-adic avatars of Hecke characters and local conditions for twists and characters

The file constructs the `p`-adic avatar of an algebraic Hecke character of a totally complex field
`K`. This is a continuous character of the absolute Galois group `Γ`, defined after fixing
`ι : ℂ ≃ ℚ̄_p`. The file then studies local conditions on a Galois representation `r` at a place `A`
of `Ω`: finite type, good, Hodge–Tate jumps, and polynomials killing an element.

## Main definitions and results

* `New.AlgHeckeChar.avatar`: the continuous character of `Γ` obtained from an algebraic Hecke
  character `(θ, n)` by correcting `ι ∘ θ` at the places above `p`. It is multiplicative in
  `(θ, n)`.
* `New.GaloisRep.localConditions_twist`: how the local conditions `New.GaloisRep.IsFiniteTypeAt`
  (finite type), `New.GaloisRep.IsGoodAt` (unramified, or crystalline above `ℓ`),
  `New.GaloisRep.JumpsRelAt` (Hodge–Tate jumps) and `New.GaloisRep.PolyKillsAt` (a polynomial kills
  an element) behave when a representation is multiplied by a character. It collects the four
  lemmas `IsFiniteTypeAt.twist`, `IsGoodAt.twist`, `JumpsRelAt.twist` and `PolyKillsAt.twist`.
* `New.Period.isPotentiallyCrystalline_of_unramified_char`: take a continuous `p`-adic character `ν`
  of an open subgroup of `G_p`, trivial on inertia near `1`. An algebra on which `ν` acts by scalars
  is potentially crystalline (`IsPotentiallyCrystalline.of_unramified_char`) with the jumps of the
  trivial action (`jump_eq_jump_one_of_unramified_char`). Weil elements act on its Weil–Deligne
  representation through `ν` (`isKilledBy_X_sub_C_of_unramified_char`).
* `New.GaloisRep.localConditions_char_of_finite_image_inertia`: the conditions for a character with
  finite image on inertia, collected from `IsFiniteTypeAt.scalar_of_finite_image_inertia`,
  `hasJumpsAt_zero_of_finite_image_inertia` and `polyKillsAt_X_sub_C_of_finite_image_inertia`.
* `New.GaloisRep.AvatarCompatAt`: local-global compatibility for the ℓ-adic avatar
  `New.AlgHeckeChar.avatar` of an algebraic Hecke character θ of a totally complex field E;
  `New.GaloisRep.AvatarCompatAt.isSphericalAbove_of_unramified` is its consequence where θ is
  unramified.
* `New.GaloisRep.avatarCompatAt_of_type_eq_zero`: it holds at a place w of E if the infinity type
  vanishes at the embeddings over w.

Notions from other files:
* `New.AlgHeckeChar`: The type of algebraic Hecke characters of K: pairs (θ, n) of a character of
  the finite ideles and its infinity type, as in `New.algHeckeChars`.
* `New.Period.IsPotentiallyCrystalline`: the elements of `Bmax ⊗ T` fixed by all `g` near `1`
  (`New.Period.Dpcris`) span `Bmax ⊗ T` over `Bmax`.
* `New.GaloisRep.HasJumpsAt`: For each local datum at `A` with embedding `e`, each `g` in
  `Gal(ℚ̄_ℓ/ℚ_ℓ)` and the embedding `γ` of `ℚ̄_ℓ` in `ℂ_ℓ` given by `g`, the Hodge–Tate jumps of
  `r` at `γ`, with multiplicity, are `J` at the embedding `ι_ℓ⁻¹ ∘ g⁻¹ ∘ e` of `E` in `ℂ`.
* `New.Period.IsKilledBy`: `T` is potentially crystalline and the polynomial `P` kills
  `New.Period.linearFrob ρ s k`, the `Bmax`-linear extension of `φ ^ k s ⊗ ρ s` from `Dpcris`.
* `New.IsFrob`: `σ` stabilises the valuation subring `A` and `σ • x ≡ x ^ q` modulo the maximal
  ideal for all `x ∈ A`.

## Relation to the literature

Known result: Characters with finite image on inertia are potentially crystalline of weight 0. Only
the potentially unramified case of the theorem on locally algebraic characters is covered, together
with the jumps and the action of Weil elements. The period is a solution of Lang's equation for GL_1
in A_inf with coefficients, and no Lubin–Tate theory is used. Source: B. Conrad, Lifting global
representations with local properties (preprint 2011), Appendix B; J.-P. Serre, Abelian l-adic
representations (1968), III, Appendix.

See also `Lib.ClassField.Avatar.LocalGlobalCompatibility` and
`Lib.PadicHodge.Crystalline.Regularity`.
-/

/-!
## p-adic avatars of algebraic Hecke characters

Let `K` be a totally complex number field with absolute Galois group `Γ`, and fix `ι : ℂ ≃ ℚ̄_p`. An
algebraic Hecke character (`New.AlgHeckeChar`) is a pair `(θ, n)`: a character of the finite ideles
with open kernel (`θ.character` in the code) and integers `n σ` (`θ.infinityType σ`), with
`θ x = ∏ σ, σ x ^ (-n σ)` on `Kˣ`. Correcting `ι ∘ θ` at the places above `p` gives a character that
is trivial on `Kˣ`, so it comes from `Γ` by `New.exists_comp_artinMap`.
-/

namespace New

open NumberField Subgroup Finset

variable {K : Type} [Field K] [EmbeddedNumberField K] {p : ℕ} [Fact p.Prime] [PadicIso p]
  [IsTotallyComplex K] (θ : AlgHeckeChar K)

/-- There is a homomorphism `av` from algebraic Hecke characters `(θ, n)` to characters of `Γ` with
values in `ℚ̄_pˣ` such that (a) `av θ` is continuous and (b) if `g` maps to the Artin symbol of the
finite idele `x`, then `av θ g = ι (θ x) * ∏ σ, (ι σ x) ^ n σ`. Here `Γ = Gal(Ω/K)` with `Ω` an
algebraic closure of `K`, and `ι` is the fixed isomorphism `ιℓ : ℂ ≃ ℚ̄_p`, `θ x` is
`θ.character x`, `n σ` is `θ.infinityType σ`, and `ι σ x` (written with `adeleExtension`) is the
image of the component of `x` at the prime induced by `ι ∘ σ`.

A case of Weil's construction of Galois characters attached to algebraic Hecke characters, for `K`
totally complex. -/
lemma exists_avatar :
    ∃ av : AlgHeckeChar K →* Gal(Ω/K) →* (PadicAlgCl p)ˣ, ∀ θ : AlgHeckeChar K,
      -- (a) the avatar is continuous
      Continuous (av θ) ∧
      -- (b) its value on the Artin symbol of an idele `x`
      ∀ (x : (𝔸f K)ˣ) (g : Gal(Ω/K)), artinMap Gal(Ω/K) x = ⟦g⟧ →
        (av θ g).val = ιℓ (θ.character x) *
          ∏ σ : K →+* ℂ, adeleExtension (ιℓ.toRingHom.comp σ) x ^ θ.infinityType σ := by
  -- The right-hand side `ψ θ` is a continuous character of the ideles, trivial on `Kˣ`, so it
  -- factors through the Artin map by `exists_comp_artinMap`.
  let ψ (θ : AlgHeckeChar K) : (𝔸f K)ˣ →* (PadicAlgCl p)ˣ :=
    (Units.map ιℓ).comp θ.character * ∏ σ : K →+* ℂ,
      Units.map (adeleExtension (ιℓ.toRingHom.comp σ)).toMonoidHom ^ θ.infinityType σ
  have hψ_cont (θ : AlgHeckeChar K) : Continuous (ψ θ) := by
    -- `θ` has open kernel, and the embeddings `adeleExtension` are continuous.
    refine .mul (.of_isOpen_ker _ (isOpen_mono (fun x hx ↦ ?_) θ.property.1)) ?_
    · simp [MonoidHom.mem_ker.1 hx]
    · simp only [MonoidHom.coe_finsetProd, Finset.prod_fn]
      exact continuous_finsetProd _ fun σ _ ↦ (continuous_adeleExtension _).units_map.zpow _
  have hψ_rat (θ : AlgHeckeChar K) (x : Kˣ) : ψ θ (principalIdele x) = 1 := by
    -- `θ x = ∏ σ, σ x ^ (-n σ)` cancels the product.
    have h_rat : (θ.character (principalIdele x)).val = ∏ σ : K →+* ℂ, σ x ^ (-θ.infinityType σ) :=
      θ.property.2 x
    simp [ψ, Units.ext_iff, h_rat, prod_eq_zero_iff, zpow_ne_zero]
  have h_factor (θ : AlgHeckeChar K) : ∃ μ : Gal(Ω/K) →* (PadicAlgCl p)ˣ, Continuous μ ∧
      ∀ (x : (𝔸f K)ˣ) (g : Gal(Ω/K)), artinMap Gal(Ω/K) x = ⟦g⟧ → μ g = ψ θ x :=
    exists_comp_artinMap Gal(Ω/K) (ψ θ) (hψ_cont θ) (hψ_rat θ)
  choose μ hμ_cont hμ using h_factor
  -- The Artin map is onto, so `μ θ` is determined by `ψ θ`, which is multiplicative in `θ`.
  have hμ_mul (θ θ' : AlgHeckeChar K) : μ (θ * θ') = μ θ * μ θ' := by
    ext g : 1
    obtain ⟨x, hx⟩ := artinMap_surjective Gal(Ω/K) ⟦g⟧
    have hψ_mul : ψ (θ * θ') x = ψ θ x * ψ θ' x := by
      simp [ψ, AlgHeckeChar.character, AlgHeckeChar.infinityType, zpow_add, prod_mul_distrib,
        mul_mul_mul_comm]
    rw [MonoidHom.mul_apply, hμ _ x g hx, hμ θ x g hx, hμ θ' x g hx, hψ_mul]
  exact ⟨.mk' μ hμ_mul, fun θ ↦ ⟨hμ_cont θ, fun x g hg ↦ by simp [ψ, hμ θ x g hg]⟩⟩

namespace AlgHeckeChar

/-- The p-adic avatar: a chosen homomorphism sending the algebraic Hecke character (θ, n) to the
continuous character μ of Γ with μ(Art x) = ι(θ(x)) ∏_σ (ισ)(x)^{n_σ}. Here ι is `ιℓ` and (ισ)(x) is
the image under ισ of the component of x at the prime induced by ισ. Its defining properties are
`continuous_avatar` and `avatar_apply_of_artinMap_eq`. -/
noncomputable def avatar : AlgHeckeChar K →* Gal(Ω/K) →* (PadicAlgCl p)ˣ :=
  (exists_avatar (K := K)).choose

/-- Let `θ` be an algebraic Hecke character of the totally complex number field `K`, with infinity
type `n`. Its `p`-adic avatar `avatar θ` is the Galois character `μ` with
`μ(Art x) = ι(θ(x)) ∏_σ (ισ)(x)^{n_σ}`, where `ι` is the chosen isomorphism `ℂ ≅ ℚ̄_p`. This lemma
states that `avatar θ` is continuous. -/
@[fun_prop]
lemma continuous_avatar : Continuous (avatar θ) :=
  (exists_avatar.choose_spec θ).1

/-- The defining formula of the avatar of `(θ, n)`. If the class of `g` is the Artin symbol of the
finite idele `x`, then `avatar θ g = ι (θ x) * ∏ σ, (ι σ x) ^ n σ`. Here `ι` is `ιℓ : ℂ ≃ ℚ̄_p`,
`θ x` and `n σ` are `θ.character x` and `θ.infinityType σ`, and `ι σ x`, written with
`adeleExtension`, is the image under `ι ∘ σ` of the component of `x` at the prime induced by
`ι ∘ σ`. -/
lemma avatar_apply_of_artinMap_eq {x : (𝔸f K)ˣ} {g : Gal(Ω/K)} (hg : artinMap Gal(Ω/K) x = ⟦g⟧) :
    (avatar θ g).val = ιℓ (θ.character x) *
      ∏ σ : K →+* ℂ, adeleExtension (ιℓ.toRingHom.comp σ) x ^ θ.infinityType σ :=
  (exists_avatar.choose_spec θ).2 x g hg

/-- Let `A` lie over the place `v`, and suppose that `v ∤ p`, or that the exponent
`n σ = θ.infinityType σ` is zero for every `σ` such that `ι ∘ σ` induces `v`. If `g` lies in the
decomposition group of `A` and its class is the local Artin symbol of `x` at `v`, then the avatar of
`(θ, n)` takes at `g` the value `ι (θ x)`, where `x` is viewed as the idele `locIdele v x` supported
at `v`. -/
lemma avatar_localArtin {A : ValuationSubring Ω} {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)}
    (hA : IsPlaceOver A v)
    (hv : ↑p ∉ v.asIdeal ∨ ∀ σ : K →+* ℂ, inducedPrime σ = v → θ.infinityType σ = 0)
    {x : (v.adicCompletion K)ˣ} {g : decompGroup Gal(Ω/K) A}
    (hg : localArtin Gal(Ω/K) A v x = ⟦g⟧) :
    (avatar θ g).val = ιℓ (θ.character (locIdele v x)) := by
  -- The global Artin symbol of `locIdele v x` is the local symbol of `x`.
  have h_artin : artinMap Gal(Ω/K) (locIdele v x) = ⟦g.val⟧ := by
    simp [hA.artinAt_eq_of_localArtin_eq hg]
  -- Each factor of the product in `avatar_apply_of_artinMap_eq` is `1`.
  have h_factor (σ : K →+* ℂ) :
      adeleExtension (ιℓ.toRingHom.comp σ) (locIdele v x) ^ θ.infinityType σ = 1 := by
    rcases eq_or_ne (inducedPrime σ) v with rfl | hσ
    · -- The place induced by `σ` lies above `p`, so the exponent is zero.
      rw [hv.resolve_left (not_not.2 (natCast_mem_placeOfEmb _)) σ rfl, zpow_zero]
    · -- At the place induced by `σ` the idele has component `1`.
      -- (Without excluding the last simp lemma `adeleExtension` does not unfold.)
      simp [adeleExtension, locIdele_apply_of_ne hσ, -RingEquiv.toRingHom_eq_coe]
  rw [θ.avatar_apply_of_artinMap_eq h_artin, prod_eq_one fun σ _ ↦ h_factor σ, mul_one]

end AlgHeckeChar

end New

/-!
## Local conditions at a place and closure properties of killing polynomials

The local conditions on a representation `r` of `Gal(Ω/E)` at a place `A` of `Ω` used here are:
* `New.GaloisRep.IsFiniteTypeAt`: trivial on inertia near `1` away from `ℓ`, potentially
  crystalline above `ℓ`;
* `New.GaloisRep.IsGoodAt`: unramified away from `ℓ`, crystalline above `ℓ`;
* `New.GaloisRep.PolyKillsAt`: a polynomial kills `r s` away from `ℓ` and, above `ℓ`, kills
  `linearFrob` of each Weil pair `(s, k)`, its action on the Weil–Deligne representation.
-/

namespace New.GaloisRep

open Polynomial Period IsCrystalline PadicPlaceEmbedding

variable {ℓ : ℕ} {E m : Type} {A : ClosurePlace} [ThePrime ℓ] [Field E] [EmbeddedNumberField E]
  [Fintype m] [DecidableEq m] {r : GalRep ℓ E m}

/-- Let `A` be a place not above `ℓ`, let `r` be of finite type at `A` (trivial on inertia near
`1`), and let `s` be an inertia element killed by `P`, that is, `P (r s) = 0`. Then `Q (r s) = 0`
for every polynomial `Q` that vanishes at all roots of `P`. -/
lemma IsFiniteTypeAt.aeval_eq_zero_of_roots (hr : IsFiniteTypeAt r A) (hA : A.valuation ℓ = 1)
    {s : Gal(Ω/E)} (hs : s ∈ inertiaGroup Gal(Ω/E) A) {P : (PadicAlgCl ℓ)[X]}
    (hP : PolyKillsAt r A s P) (Q : (PadicAlgCl ℓ)[X])
    (h_roots : ∀ x : PadicAlgCl ℓ, P.IsRoot x → Q.IsRoot x) : aeval (r s).val Q = 0 := by
  -- Powers of `s` come arbitrarily close to `1` and stay in inertia, so `r s` has finite order.
  obtain ⟨n, hn, h_one⟩ : ∃ n ≥ 1, s ^ n ∈ inertiaGroup Gal(Ω/E) A → r (s ^ n) = 1 :=
    ((mapClusterPt_one_atTop_pow s).frequently (hr.1 hA)).forall_exists_of_atTop 1
  -- Hence a polynomial kills `r s` as soon as it vanishes at the roots of one that does.
  refine map_eq_zero_of_roots _ ⟨n, hn, ?_⟩ (hP.1 hA) h_roots
  simpa [Units.ext_iff] using h_one (pow_mem hs n)

/-- Above `ℓ`, inertia acts on the Weil–Deligne representation through a finite group. So if `P`
kills an inertial element `s` there, then so does every `Q` that vanishes at the roots of `P`: `r`
restricted to the decomposition group is potentially crystalline and `Q` kills `linearFrob` of
`(s, 0)`. -/
lemma PolyKillsAt.isKilledBy_of_roots [L : PadicPlaceEmbedding E A ℓ]
    {s : decompGroup Gal(Ω/E) A} (hs : IsWeilPair (L.toGp s) 0) {P Q : (PadicAlgCl ℓ)[X]}
    (hP : PolyKillsAt r A s P) (h_roots : ∀ x : PadicAlgCl ℓ, P.IsRoot x → Q.IsRoot x) :
    IsKilledBy (decompRep r A) s 0 Q := by
  obtain ⟨h_pcr, h_kill⟩ : IsKilledBy (decompRep r A) s 0 P := hP.2 hs
  -- Some positive power of `s` is near `1`, where inertia acts trivially.
  obtain ⟨N, hN, h_one⟩ : ∃ N ≥ 1, ∀ t : decompGroup Gal(Ω/E) A, L.toGp t = L.toGp s ^ N →
      IsWeilPair (L.toGp t) 0 → linearFrob (decompRep r A) t 0 = 1 :=
    ((mapClusterPt_one_atTop_pow _).frequently
      (Filter.mem_comap'.1 h_pcr.eventually_linearFrob_eq_one)).forall_exists_of_atTop 1
  have h_order : linearFrob (decompRep r A) s 0 ^ N = 1 := by
    rw [← linearFrob_pow h_pcr hs N, mul_zero]
    exact h_one (s ^ N) (map_pow _ s N) (by simpa [map_pow] using hs.pow N)
  -- Evaluation at `linearFrob` is a ring homomorphism, as it commutes with the coefficients.
  let φ : (PadicAlgCl ℓ)[X] →+* Module.End Bmax (TensorProduct ℤ_[ℓ] Bmax (m → PadicAlgCl ℓ)) :=
    eval₂RingHom' _ _ (commute_coeffEnd_linearFrob h_pcr hs)
  exact ⟨h_pcr, map_eq_zero_of_roots φ ⟨N, hN, by simpa [φ] using h_order⟩ h_kill h_roots⟩

/-- If `P` kills `s` for `r` at `A`, so does every multiple of `P`. -/
lemma PolyKillsAt.of_dvd {s : Gal(Ω/E)} {P Q : (PadicAlgCl ℓ)[X]} (hP : PolyKillsAt r A s P)
    (h_dvd : P ∣ Q) : PolyKillsAt r A s Q := by
  obtain ⟨R, rfl⟩ := h_dvd
  refine ⟨fun hA ↦ by simp [hP.1 hA], fun {L} hs k hk ↦ ?_⟩
  obtain ⟨h_pcr, h_kill⟩ := hP.2 (hs := hs) hk
  -- `linearFrob` commutes with the coefficients, so evaluation at it is multiplicative.
  refine ⟨h_pcr, ?_⟩
  rw [eval₂_mul_noncomm _ _ fun _ ↦ commute_coeffEnd_linearFrob h_pcr hk _, h_kill, zero_mul]

/-- At a place `A`, `r` is good (unramified away from `ℓ`, crystalline above `ℓ`) exactly when it is
of finite type (trivial on inertia near `1` away from `ℓ`, potentially crystalline above `ℓ`) and
`X - 1` kills every element of inertia.

A case of the Weil–Deligne criterion for unramified, resp. crystalline, representations (Fontaine;
Brinon–Conrad). Here finite type replaces vanishing monodromy, and `X - 1` killing each inertial
element replaces trivial inertia action. -/
lemma isGoodAt_iff : IsGoodAt r A ↔
    IsFiniteTypeAt r A ∧ ∀ s ∈ inertiaGroup Gal(Ω/E) A, PolyKillsAt r A s (X - 1) := by
  refine ⟨fun ⟨h_unr, h_crys⟩ ↦ ?_, fun ⟨h_fin, h_kill⟩ ↦ ?_⟩
  · refine ⟨⟨fun hℓ ↦ .of_forall (h_unr hℓ), h_crys.isPotentiallyCrystalline⟩, fun s hs ↦ ?_⟩
    refine ⟨fun hℓ ↦ by simp [h_unr hℓ s hs], fun {L} hsD k hk ↦
      ⟨h_crys.isPotentiallyCrystalline, ?_⟩⟩
    -- An element of inertia has degree `0`, where `linearFrob` is the identity on a crystalline
    -- `r`.
    have h_pow : ℓ ^ 0 = ℓ ^ k := hk.eq_pow_of_isFrob (isWeilPair_zero_iff.2 hs)
    obtain rfl : 0 = k := (ℓ.pow_right_inj Fact.out).1 h_pow
    have h_frob : linearFrob (decompRep r A) ⟨s, hsD⟩ 0 = 1 := h_crys.linearFrob_eq_one hk
    simp [h_frob]
  · refine ⟨fun hℓ s hs ↦ ?_, h_fin.2.isCrystalline_of_inertia_fixes fun s hs ↦ ?_⟩
    · have h_eval : aeval (r s).val (X - 1 : (PadicAlgCl ℓ)[X]) = 0 := (h_kill s hs).1 hℓ
      exact Units.ext (by simpa [sub_eq_zero] using h_eval)
    · -- Descent: a potentially crystalline `r` with `linearFrob = 1` on inertia is crystalline.
      obtain ⟨-, h_eval⟩ : IsKilledBy (decompRep r A) s 0 (X - 1) :=
        (h_kill _ (isWeilPair_zero_iff.1 hs)).2 hs
      simpa [sub_eq_zero] using h_eval

end New.GaloisRep

/-! ## Local conditions of the twist of a representation by a character -/

section LocalTwist

open Matrix Polynomial New.Period Multiset

namespace New.GaloisRep

variable {ℓ : ℕ} [ThePrime ℓ] {E m : Type} [Field E] [Algebra E Ω] [Fintype m] [DecidableEq m]
  {r r' : GalRep ℓ E m} {A : ClosurePlace} {μ : Gal(Ω/E) →* (PadicAlgCl ℓ)ˣ}

variable (ℓ m) in
/-- The pairing `(u, x) ↦ u 0 • x` of a vector with one entry and a vector indexed by `m`. -/
noncomputable def twistPairing :
    (Fin 1 → PadicAlgCl ℓ) →ₗ[ℤ_[ℓ]] (m → PadicAlgCl ℓ) →ₗ[ℤ_[ℓ]] m → PadicAlgCl ℓ :=
  (Algebra.lsmul ℤ_[ℓ] ℤ_[ℓ] (m → PadicAlgCl ℓ)).toLinearMap ∘ₗ LinearMap.proj 0

/-- The twist `r' = μ • r` is the tensor product of `μ` and `r`: the pairing `twistPairing` is
equivariant for the decomposition group at `A`. Here `decompRep r A` is `r` restricted to that
group, acting by matrices on vectors `m → ℚ̄_ℓ`. -/
lemma twistPairing_decompRep (h_twist : ∀ g : Gal(Ω/E), (r' g).val = (μ g).val • (r g).val)
    (g : decompGroup Gal(Ω/E) A) (u : Fin 1 → PadicAlgCl ℓ) (x : m → PadicAlgCl ℓ) :
    twistPairing ℓ m (decompRep ((GeneralLinearGroup.scalar (Fin 1)).comp μ) A g u)
      (decompRep r A g x) = decompRep r' A g (twistPairing ℓ m u x) := by
  simp [h_twist, twistPairing, mul_comm]

/-- Admissibility along a filter `F` passes from `r` and the character `μ`, both restricted to the
decomposition group at `A`, to the twist `r' = μ • r`. Admissible means crystalline for `F = ⊤` and
potentially crystalline for `F = nearOne`, the pull-back along `toGp` (given by `OverGp`) of the
neighbourhoods of `1` in `Gal(ℚ̄_ℓ/ℚ_ℓ)`. -/
lemma isAdmissible_twist [OverGp (decompGroup Gal(Ω/E) A) ℓ]
    {F : Filter (decompGroup Gal(Ω/E) A)} (hr : IsAdmissible (decompRep r A) F)
    (h_twist : ∀ g : Gal(Ω/E), (r' g).val = (μ g).val • (r g).val)
    (hμ : IsAdmissible (decompRep ((GeneralLinearGroup.scalar (Fin 1)).comp μ) A) F) :
    IsAdmissible (decompRep r' A) F :=
  -- The pairing is equivariant and onto.
  hμ.of_bilinear (twistPairing ℓ m) (twistPairing_decompRep h_twist) hr
    fun x ↦ ⟨1 ⊗ₜ x, by simp [twistPairing]⟩

/-- Where `r` and the character `μ` are trivial, so is the twist `r' = μ • r`. -/
lemma twist_apply_eq_one (h_twist : ∀ g : Gal(Ω/E), (r' g).val = (μ g).val • (r g).val)
    {s : Gal(Ω/E)} (hr : r s = 1) (hμ : (GeneralLinearGroup.scalar (Fin 1)).comp μ s = 1) :
    r' s = 1 := by
  have hμ_one : (μ s).val = 1 := by simpa [GeneralLinearGroup.ext_iff] using hμ
  exact Units.ext (by rw [h_twist, hr, hμ_one, one_smul])

/-- If `r` and the character `μ`, read as a representation by `1 × 1` matrices, are of finite type
at `A` (trivial on inertia near `1` away from `ℓ`, potentially crystalline above `ℓ`), so is the
twist `r' = μ • r`. -/
lemma IsFiniteTypeAt.twist (hr : IsFiniteTypeAt r A)
    (h_twist : ∀ g : Gal(Ω/E), (r' g).val = (μ g).val • (r g).val)
    (hμ : IsFiniteTypeAt ((GeneralLinearGroup.scalar (Fin 1)).comp μ) A) : IsFiniteTypeAt r' A := by
  refine ⟨fun hℓ ↦ ?_, isAdmissible_twist hr.2 h_twist hμ.2⟩
  filter_upwards [hr.1 hℓ, hμ.1 hℓ] with s hr_one hμ_one hs
  exact twist_apply_eq_one h_twist (hr_one hs) (hμ_one hs)

/-- If `r` and the character `μ` are unramified at `A` (crystalline above `ℓ`), so is the twist
`r' = μ • r`. -/
lemma IsGoodAt.twist (hr : IsGoodAt r A)
    (h_twist : ∀ g : Gal(Ω/E), (r' g).val = (μ g).val • (r g).val)
    (hμ : IsGoodAt ((GeneralLinearGroup.scalar (Fin 1)).comp μ) A) : IsGoodAt r' A :=
  ⟨fun hℓ s hs ↦ twist_apply_eq_one h_twist (hr.1 hℓ s hs) (hμ.1 hℓ s hs),
    isAdmissible_twist hr.2 h_twist hμ.2⟩

/-- Evaluating `Q (c X)` at an element `β` that commutes with the coefficients, mapped by `f`, is
evaluating `Q` at `f c * β`. -/
lemma eval₂_comp_C_mul_X {R S : Type*} [Semiring R] [Semiring S] {f : R →+* S} {β : S}
    (h_comm : ∀ a : R, Commute (f a) β) (Q : R[X]) (c : R) :
    (Q.comp (C c * X)).eval₂ f β = Q.eval₂ f (f c * β) := by
  let φ : R[X] →+* S := eval₂RingHom' f β h_comm
  have φ_C : φ.comp C = f := RingHom.ext fun a ↦ eval₂_C f β
  calc _ = Q.eval₂ (φ.comp C) (φ (C c * X)) := Q.hom_eval₂ C φ (C c * X)
    _ = Q.eval₂ f (f c * β) := by simp [φ_C, map_mul φ, φ]

/-- If `Q (c X)` kills `s` for `r` and `X - c` kills `s` for the character `μ`, then `Q` kills `s`
for the twist `r' = μ • r`. Here `P` kills `s` if `P (r s) = 0` away from `ℓ` and, above `ℓ`, if it
kills `linearFrob` of `s` on the potentially crystalline restriction of `r`. -/
lemma PolyKillsAt.twist {s : Gal(Ω/E)} {Q : (PadicAlgCl ℓ)[X]} {c : PadicAlgCl ℓ}
    (hr : PolyKillsAt r A s (Q.comp (C c * X)))
    (h_twist : ∀ g : Gal(Ω/E), (r' g).val = (μ g).val • (r g).val)
    (hμ : PolyKillsAt ((GeneralLinearGroup.scalar (Fin 1)).comp μ) A s (X - C c)) :
    PolyKillsAt r' A s Q := by
  refine ⟨fun hℓ ↦ ?_, fun {L} hs k hk ↦ ?_⟩
  · -- Away from `ℓ`: `μ s = c`, so `r' s = c • r s`.
    have hμ_val : (μ s).val = c := by simpa [funext_iff, algebraMap, sub_eq_zero] using hμ.1 hℓ
    simpa [h_twist, hμ_val, aeval_comp, Algebra.smul_def] using hr.1 hℓ
  · -- Above `ℓ`, `linearFrob` is `c` on the character and respects `twistPairing`, so `linearFrob`
    -- of `r'` is `c` times that of `r`.
    set r₁ : GalRep ℓ E (Fin 1) := (GeneralLinearGroup.scalar (Fin 1)).comp μ
    obtain ⟨pcr_r, kill_r⟩ := hr.2 (hs := hs) hk
    obtain ⟨pcr_μ, kill_μ⟩ := hμ.2 (hs := hs) hk
    have pcr : IsPotentiallyCrystalline (decompRep r' A) := isAdmissible_twist pcr_r h_twist pcr_μ
    let t : decompGroup Gal(Ω/E) A := ⟨s, hs⟩
    have frob_μ : linearFrob (decompRep r₁ A) t k = coeffEnd (PadicAlgCl ℓ) _ c := by
      simpa [sub_eq_zero] using kill_μ
    let B := Lift.baseChangePairing (A := Bmax) (twistPairing ℓ m)
    have B_coef (a : PadicAlgCl ℓ) (x : TensorProduct ℤ_[ℓ] Bmax (m → PadicAlgCl ℓ)) :
        B (coeffEnd (PadicAlgCl ℓ) _ a (1 ⊗ₜ 1)) x = coeffEnd (PadicAlgCl ℓ) _ a x := by
      -- `coeffEnd` is by definition the base change of multiplication by scalars.
      change _ = LinearMap.baseChange Bmax (Algebra.lsmul ℤ_[ℓ] ℤ_[ℓ] (m → PadicAlgCl ℓ) a) x
      simp [B, twistPairing, Lift.baseChangePairing]
    have B_frob : B.compl₁₂ (linearFrob (decompRep r₁ A) t k) (linearFrob (decompRep r A) t k) =
        B.compr₂ (linearFrob (decompRep r' A) t k) :=
      linearFrob_baseChangePairing pcr_r hk pcr_μ _ (twistPairing_decompRep h_twist) pcr
    have frob_twist : linearFrob (decompRep r' A) t k =
        coeffEnd (PadicAlgCl ℓ) _ c * linearFrob (decompRep r A) t k := by
      refine LinearMap.ext fun x ↦ ?_
      have B_one : B (1 ⊗ₜ 1) x = x := by simpa using B_coef 1 x
      -- Evaluate `B_frob` at `(1 ⊗ 1, x)`.
      simpa [frob_μ, B_one, ← B_coef] using (LinearMap.congr_fun₂ B_frob (1 ⊗ₜ 1) x).symm
    -- `linearFrob` commutes with the coefficients, so the factor `c` moves into the polynomial.
    exact ⟨pcr, by rwa [frob_twist, ← eval₂_comp_C_mul_X (commute_coeffEnd_linearFrob pcr_r hk)]⟩

/-- Let `A` be a place of Ω whose decomposition group maps with open image to Gal(Q̄_ℓ/Q_ℓ)
(`OverGp`), let `γ` be a ℤ_ℓ-algebra embedding of Q̄_ℓ into ℂ_ℓ, and let `r' = μ • r` pointwise. If
`u` is a Hodge–Tate jump of multiplicity one at `γ` of the character `μ` restricted to the
decomposition group of `A`, then for every integer `w` the multiplicity of the jump `w + u` of `r'`
at `γ` equals that of the jump `w` of `r`, both restricted to that decomposition group. -/
lemma jump_twist [OverGp (decompGroup Gal(Ω/E) A) ℓ] {γ : PadicAlgCl ℓ →ₐ[ℤ_[ℓ]] ℂ_[ℓ]} {u : ℤ}
    (h_twist : ∀ g : Gal(Ω/E), (r' g).val = (μ g).val • (r g).val)
    (hμ : jump (decompRep ((GeneralLinearGroup.scalar (Fin 1)).comp μ) A) γ u = 1) (w : ℤ) :
    jump (decompRep r' A) γ (w + u) = jump (decompRep r A) γ w := by
  -- Some `f ≠ 0` lies in `hodgeTateMaps` of `μ` for `u`, and a value `f x ≠ 0` in `ℂ_[ℓ]` is a
  -- period of `μ`.
  set r₁ : GalRep ℓ E (Fin 1) := (GeneralLinearGroup.scalar (Fin 1)).comp μ
  obtain ⟨f, hf, x, hx⟩ : ∃ f ∈ hodgeTateMaps (decompRep r₁ A) γ u,
      ∃ x : Fin 1 → PadicAlgCl ℓ, f x ≠ 0 := by
    -- `jump` is the rank of the space `hodgeTateMaps`, so that space has a nonzero element.
    obtain ⟨f, hf_ne, -⟩ := finrank_eq_one_iff'.1 hμ
    exact ⟨f, f.property, by simpa [Subtype.ext_iff, DFunLike.ext_iff] using hf_ne⟩
  have h_period : ∀ᶠ t : decompGroup Gal(Ω/E) A in nearOne _,
      γ (μ t.val).val * f x = (χ t ^ (-u)).val • toGp t • f x := by
    filter_upwards [hf x] with t ht
    have h_scalar : decompRep r₁ A t x = (μ t.val).val • x := by simp [r₁]
    rwa [h_scalar, map_smulₛₗ] at ht
  exact jump_twist_of_period _ hx h_period (by simp [h_twist])

variable [PadicIso ℓ]

/-- Let the character `μ` have the single jump `u τ` at each `τ`. If a relation `R` holds between
the multiplicities in `J τ` and those of the jumps of `r` (`JumpsRelAt`), then it holds between
those in `J τ` shifted by `u τ` and those of the jumps of the twist `r' = μ • r`. -/
lemma JumpsRelAt.twist {R : ℕ → ℕ → Prop} {J : (E →+* ℂ) → Multiset ℤ} {u : (E →+* ℂ) → ℤ}
    (hr : JumpsRelAt r A R J) (h_twist : ∀ g : Gal(Ω/E), (r' g).val = (μ g).val • (r g).val)
    (hμ : HasJumpsAt ((GeneralLinearGroup.scalar (Fin 1)).comp μ) A fun τ : E →+* ℂ ↦ {u τ}) :
    JumpsRelAt r' A R fun τ : E →+* ℂ ↦ (J τ).map fun v : ℤ ↦ v + u τ := by
  -- Fix a chart `L` at `A`, an embedding `γ` given by `g ∈ Gal(ℚ̄_ℓ/ℚ_ℓ)`, and an integer `v`.
  intro L γ g hg v
  set τ : E →+* ℂ := .comp ιℓ.symm (.comp ↑g⁻¹ (L.e.comp (algebraMap E Ω)) : E →+* PadicAlgCl ℓ)
  have h_one : jump (decompRep ((GeneralLinearGroup.scalar (Fin 1)).comp μ) A) γ (u τ) = 1 :=
    (hμ hg (u τ)).symm.trans (count_singleton_self (u τ))
  show R (((J τ).map fun v : ℤ ↦ v + u τ).count v) (jump (decompRep r' A) γ v)
  rw [← sub_add_cancel v (u τ), count_map_eq_count' _ _ (add_left_injective (u τ)),
    jump_twist h_twist h_one]
  exact hr hg (v - u τ)

/-- Let `r' = μ • r` be the twist of `r` by a character `μ`, read as a representation by `1 × 1`
matrices. At the place `A`: (a), (b) if `r` and `μ` are of finite type (trivial on inertia near 1 if
ℓ is a unit at A, else potentially crystalline), or unramified (crystalline above `ℓ`), so is `r'`;
(c) if the jumps of `r` stand in the relation `R` to a family `J` of multisets (for each integer v,
`R` holds between the multiplicity of v in `J` and its multiplicity as a jump), and `μ` has the
single jump `u τ` at each `τ`, then the jumps of `r'` stand in the relation `R` to `J` shifted by
`u`; (d) if `Q (c X)` kills `s` for `r` and `X - c` kills `s` for `μ`, then `Q` kills `s` for `r'`.
The clauses are `IsFiniteTypeAt.twist`, `IsGoodAt.twist`, `JumpsRelAt.twist` and
`PolyKillsAt.twist`.

The compatibility of Weil–Deligne representations and Hodge–Tate weights with tensor products, in
the case of twists by a character. -/
lemma localConditions_twist (A : ClosurePlace)
    (h_twist : ∀ g : Gal(Ω/E), (r' g).val = (μ g).val • (r g).val) :
    (IsFiniteTypeAt r A → IsFiniteTypeAt ((GeneralLinearGroup.scalar (Fin 1)).comp μ) A →
      IsFiniteTypeAt r' A) ∧
    (IsGoodAt r A → IsGoodAt ((GeneralLinearGroup.scalar (Fin 1)).comp μ) A → IsGoodAt r' A) ∧
    (∀ {R : ℕ → ℕ → Prop} {J : (E →+* ℂ) → Multiset ℤ} {u : (E →+* ℂ) → ℤ},
      JumpsRelAt r A R J →
      HasJumpsAt ((GeneralLinearGroup.scalar (Fin 1)).comp μ) A (fun τ : E →+* ℂ ↦ {u τ}) →
      JumpsRelAt r' A R fun τ : E →+* ℂ ↦ (J τ).map fun v : ℤ ↦ v + u τ) ∧
    ∀ {s : Gal(Ω/E)} {Q : (PadicAlgCl ℓ)[X]} {c : PadicAlgCl ℓ},
      PolyKillsAt r A s (Q.comp (C c * X)) →
      PolyKillsAt ((GeneralLinearGroup.scalar (Fin 1)).comp μ) A s (X - C c) →
      PolyKillsAt r' A s Q :=
  ⟨fun hr hμ ↦ hr.twist h_twist hμ, fun hr hμ ↦ hr.twist h_twist hμ,
    fun hr hμ ↦ hr.twist h_twist hμ, fun hr hμ ↦ hr.twist h_twist hμ⟩

end New.GaloisRep

end LocalTwist

/-!
## Potential crystallinity of p-adic characters unramified near 1

Let `Γ` be a topological group and `toGp`, from the instance `𝒥 : OverGp Γ p`, the given
homomorphism from `Γ` to `G_p`. If `toGp` is an open embedding, a continuous `p`-adic character `ν`
of `Γ` that is trivial on inertia near `1` is potentially crystalline. The monoid
`New.Period.FrobGal = ℕ × G_p` acts on `New.Period.Ainf`, the pair `(k, s)` as `φ ^ k s`.
`New.Period.IsWeilPair s k` says that `s` acts on the residue field as `x ↦ x ^ (1 / p ^ k)`.

* `New.Period.exists_unramified_period`: a case of Lang's theorem, a unit `y` of `A_inf ⊗ T`, for a
  finite free `ℤ_p`-algebra `T` and `a ∈ T`, with `φ ^ k s y = y` and `s y = a ^ k y` for every Weil
  pair `(s, k)`, when `1 - a` is nilpotent modulo `p`.
-/

namespace New.Period

open Polynomial Filter Function Algebra TensorProduct Module Multiplicative Ideal Topology
  IsScalarTower Subgroup LinearMap IsAdicComplete Selmer PadicComplex

variable {p : ℕ} [ThePrime p] {Γ T : Type*} [Group Γ] [CommRing T]
  [Algebra ℤ_[p] T] [𝒥 : OverGp Γ p] {ν : Γ →* (PadicAlgCl p)ˣ}

attribute [local instance] SMulCommClass.symm

/-- The monoid `FrobGal = ℕ × G_p` acts on `A_inf ⊗ T` by its action on `A_inf`. -/
noncomputable instance : MulSemiringAction FrobGal (Ainf ⊗[ℤ_[p]] T) :=
  ⟨by simp [one_def, smul_tmul'], fun m ↦
    (map (MulSemiringAction.toAlgHom ℤ_[p] _ m) (.id _ T)).map_mul⟩

/-- The operator `φ - 1` of `A_inf`, tensored with `T`, is `φ - 1` on `A_inf ⊗ T`. -/
private lemma rTensor_frobenius_sub_id_apply (z : Ainf ⊗[ℤ_[p]] T) :
    (DistribSMul.toLinearMap ℤ_[p] Ainf ((ofAdd 1, 1) : FrobGal) - .id).rTensor T z =
      ((ofAdd 1, 1) : FrobGal) • z - z := by aesop

/-- The map `φ - 1` is onto on `A_inf ⊗ T`, with `φ` the Frobenius of `A_inf`. -/
private lemma exists_frobenius_smul_sub_eq (v : Ainf ⊗[ℤ_[p]] T) :
    ∃ x : Ainf ⊗[ℤ_[p]] T, ((ofAdd 1, 1) : FrobGal) • x - x = v := by
  -- On `A_inf` itself this is `exists_frobEnd_sub_xi_pow_mul_eq`; tensor with `T`.
  let d : Ainf →ₗ[ℤ_[p]] Ainf := DistribSMul.toLinearMap ℤ_[p] Ainf ((ofAdd 1, 1) : FrobGal) - .id
  have d_surj : Surjective d := fun c : Ainf ↦ by
    change ∃ x : Ainf, frobEnd x - x = c
    simpa only [pow_zero, one_mul] using c.exists_frobEnd_sub_xi_pow_mul_eq 0
  simpa only [d, rTensor_frobenius_sub_id_apply] using d.rTensor_surjective T d_surj v

/-- For a flat `ℤ_p`-algebra `T`, an element of `A_inf ⊗ T` fixed by the Frobenius lies in `T`. -/
private lemma exists_one_tmul_eq_of_frobenius_smul_eq [Flat ℤ_[p] T] {z : Ainf ⊗[ℤ_[p]] T}
    (hz : ((ofAdd 1, 1) : FrobGal) • z = z) : ∃ o : T, 1 ⊗ₜ o = z := by
  -- The kernel of `φ - 1` on `A_inf` is `ℤ_p`, and tensoring with `T` keeps exactness.
  let d : Ainf →ₗ[ℤ_[p]] Ainf := DistribSMul.toLinearMap ℤ_[p] Ainf ((ofAdd 1, 1) : FrobGal) - .id
  have hz_ker : d.rTensor T z = 0 := by rw [rTensor_frobenius_sub_id_apply, hz, sub_self]
  have h_exact : Exact (Algebra.linearMap ℤ_[p] Ainf) d := fun c : Ainf ↦ by
    refine ⟨fun hc ↦ exists_algebraMap_eq_of_frobenius_eq c ?_, by aesop⟩
    have hc_fixed : frobEnd c = c := sub_eq_zero.1 hc
    simpa [frobEnd_eq_frobenius] using hc_fixed
  simpa [(TensorProduct.lid ℤ_[p] T).symm.surjective.exists, hz_ker] using
    Flat.rTensor_exact T h_exact z

/-- For a Weil pair `(s, k)`, the action of `φ ^ k s` on `A_inf ⊗ T` disappears after reducing the
Witt coordinates of `A_inf` to the residue field by `toWittResidue`. -/
private lemma map_toWittResidue_smul_of_isWeilPair {s : Gp p} {k : ℕ} (hs : IsWeilPair s k)
    (z : Ainf ⊗[ℤ_[p]] T) :
    map toWittResidue (.id ℤ_[p] T) (((ofAdd k, s) : FrobGal) • z) =
      map toWittResidue (.id ℤ_[p] T) z := by
  induction z with
  | tmul c o => simp [toWittResidue_smul_of_isFrob hs, smul_tmul']
  | add z₁ z₂ h₁ h₂ => simp [h₁, h₂]

/-- If `1 - a` is nilpotent modulo `p`, then `A_inf ⊗ T` has a unit `y` with `(1 ⊗ a) φ y = y`. -/
private lemma exists_isUnit_mul_frobenius_smul_eq [Free ℤ_[p] T] [Module.Finite ℤ_[p] T] (a : T)
    (h_nilp : ∃ e : ℕ, ↑p ∣ (1 - a) ^ e) :
    ∃ y : Ainf ⊗[ℤ_[p]] T, IsUnit y ∧ 1 ⊗ₜ a * ((ofAdd 1, 1) : FrobGal) • y = y := by
  -- With `α = 1 ⊗ a`, solve `α φ x - x = 1` by successive approximation and put
  -- `y = (1 - α) x + 1`.
  obtain ⟨e, b, hb⟩ := h_nilp
  let φ : FrobGal := (ofAdd 1, 1)
  let α : Ainf ⊗[ℤ_[p]] T := 1 ⊗ₜ a
  have α_fixed (m : FrobGal) : m • α = α := by simp [α, smul_tmul']
  -- `α φ - 1` is onto modulo every power of `1 - α`, hence modulo `p`, hence onto.
  have approx (k : ℕ) (v : Ainf ⊗[ℤ_[p]] T) :
      ∃ n w : Ainf ⊗[ℤ_[p]] T, v = α * φ • n - n + (1 - α) ^ k * w := by
    induction k with
    | zero => exact ⟨0, v, by simp⟩
    | succ k ih =>
      obtain ⟨n, w, hv⟩ := ih
      obtain ⟨x, rfl⟩ := exists_frobenius_smul_sub_eq w
      refine ⟨n + (1 - α) ^ k * x, φ • x, ?_⟩
      simp only [hv, smul_add, smul_mul', smul_pow', smul_sub, smul_one, α_fixed]
      ring
  have h_pow : (1 - α) ^ e = (p : Ainf) • (1 ⊗ₜ b) := by
    simp [α, one_def, hb, ← nsmul_eq_mul, ← tmul_sub, smul_tmul']
  have complete : IsAdicComplete (span {(p : Ainf)}) (Ainf ⊗[ℤ_[p]] T) := isAdicComplete_of_free _
  obtain ⟨x, hx⟩ : ∃ x : Ainf ⊗[ℤ_[p]] T, α * φ • x - x = 1 := by
    let f : Ainf ⊗[ℤ_[p]] T →+ Ainf ⊗[ℤ_[p]] T :=
      α • (frobEnd (A := Ainf ⊗[ℤ_[p]] T)).toAddMonoidHom - .id _
    refine mem_range_of_approx f (map_natCast_smul f Ainf Ainf p) id (fun v ↦ ?_) 1
    obtain ⟨n, w, hv⟩ := approx e v
    exact ⟨n, 1 ⊗ₜ b * w, by rwa [h_pow, smul_mul_assoc] at hv⟩
  refine ⟨(1 - α) * x + 1, ?_, ?_⟩
  · -- `(1 - α) ^ e` lies in `(p)`, so `1 - α` lies in the Jacobson radical
    refine mem_jacobson_bot.1 (isRadical_jacobson _ ⟨e, ?_⟩) x
    apply ((map_algebraMap_iff ..).2 complete).le_jacobson_bot
    simp [h_pow, Algebra.smul_def, mem_span_singleton, Ideal.map_span]
  · rw [smul_add, smul_mul', smul_sub, smul_one, α_fixed]
    linear_combination (1 - α) * hx

/-- A case of Lang's theorem for `GL₁`. Let `T` be a finite free `ℤ_p`-algebra and `a ∈ T` with
`1 - a` nilpotent modulo `p`. Then `A_inf ⊗ T` has a unit `y` whose line `T y` is kept by `φ` and
`G_p`, with `φ ^ k s • y = y` and `s • y = a ^ k y` for every Weil pair `(s, k)`, that is, whenever
`s` acts on the residue field as `x ↦ x ^ (1 / p ^ k)`.

A rank-one form of the fact that unramified representations have a basis of invariants over
`W(F̄_p)[1/p]` (see Caruso), for a value `a` unipotent modulo `p` and with the period taken in
`A_inf ⊗ T`. -/
lemma exists_unramified_period [Free ℤ_[p] T] [Module.Finite ℤ_[p] T] (a : T)
    (h_nilp : ∃ e : ℕ, ↑p ∣ (1 - a) ^ e) :
    ∃ y : Ainf ⊗[ℤ_[p]] T,
      IsUnit y ∧
      -- (a) the line of `y` is stable
      (∀ m : FrobGal, ∃ o : T, m • y = 1 ⊗ₜ o * y) ∧
      -- (b) the action of a Weil element `s` of degree `k`, with and without Frobenius
      ∀ (s : Gp p) (k : ℕ), IsWeilPair s k →
        ((ofAdd k, s) : FrobGal) • y = y ∧ s • y = 1 ⊗ₜ a ^ k * y := by
  -- Take `y` with `α φ y = y`, where `α = 1 ⊗ a`. For any `m` the quotient `m • y / y` is fixed
  -- by `φ`, so it lies in `T`; for a Weil pair it is `1`, as one sees after reducing Witt
  -- coordinates.
  let φ : FrobGal := (ofAdd 1, 1)
  let α : Ainf ⊗[ℤ_[p]] T := 1 ⊗ₜ a
  obtain ⟨y, hy, y_eq⟩ : ∃ y : Ainf ⊗[ℤ_[p]] T, IsUnit y ∧ α * φ • y = y :=
    exists_isUnit_mul_frobenius_smul_eq a h_nilp
  have α_fixed (m : FrobGal) : m • α = α := by simp [α, smul_tmul']
  -- every `m` fixes `α` and commutes with `φ`, so `m • y` solves the same equation; iterate it
  have smul_y_eq (k : ℕ) (m : FrobGal) : α ^ k * (φ ^ k * m) • y = m • y := by
    induction k with
    | zero => simp
    | succ k ih =>
      have φ_comm : φ ^ (k + 1) * m = φ ^ k * m * φ := by
        simp [φ, pow_succ, Prod.mul_def, mul_right_comm]
      calc _ = α ^ k * (φ ^ k * m) • (α * φ • y) := by
            rw [φ_comm, mul_smul (φ ^ k * m), smul_mul', α_fixed, pow_succ, mul_assoc]
        _ = m • y := by rw [y_eq, ih]
  have stable (m : FrobGal) : ∃ o : T, m • y = 1 ⊗ₜ o * y := by
    obtain ⟨z, hz⟩ : y ∣ m • y := hy.dvd
    have z_fixed : φ • z = z := by
      simpa [mul_smul, hz, y_eq, hy.mul_right_inj, ← mul_assoc] using smul_y_eq 1 m
    obtain ⟨o, ho⟩ := exists_one_tmul_eq_of_frobenius_smul_eq z_fixed
    exact ⟨o, by rw [hz, ho, mul_comm]⟩
  refine ⟨y, hy, stable, fun s k hs ↦ ?_⟩
  -- `φ ^ k s` acts trivially on the Witt vectors of the residue field of `O^♭`,
  -- so its factor `o` is `1`
  have weil_fix : ((ofAdd k, s) : FrobGal) • y = y := by
    obtain ⟨o, ho⟩ := stable (ofAdd k, s)
    have h_one : (1 : WittVector p (IsLocalRing.ResidueField OFlat)) ⊗ₜ[ℤ_[p]] o = 1 := by
      simpa [ho, (hy.map _).mul_eq_right] using map_toWittResidue_smul_of_isWeilPair hs y
    obtain rfl : o = 1 := includeRight_injective (FaithfulSMul.algebraMap_injective ..) h_one
    simpa [← one_def] using ho
  refine ⟨weil_fix, ?_⟩
  -- `φ ^ k * (1, s) = (ofAdd k, s)` fixes `y`, so `s • y = α ^ k * y`
  have h_mul : φ ^ k * ((1, s) : FrobGal) = (ofAdd k, s) := by simp [φ, ← ofAdd_nsmul]
  show ((1, s) : FrobGal) • y = _
  rw [← smul_y_eq k (1, s), h_mul, weil_fix]

/-- If `‖1 - b‖ < 1` and `f ≠ 0`, then `b ∈ ℚ̄_p` has an `f`-th root `a` with `‖1 - a‖ < 1`. -/
lemma exists_root_near_one {b : PadicAlgCl p} {f : ℕ} (hf : f ≠ 0) (hb : ‖1 - b‖ < 1) :
    ∃ a : PadicAlgCl p, a ^ f = b ∧ ‖1 - a‖ < 1 := by
  -- otherwise all roots of `X ^ f - b` are at distance at least `1` from `1`, so `1 ≤ ‖1 - b‖`
  by_contra! h_far
  have h_roots (w : PadicAlgCl p) (hw : w ∈ (X ^ f - C b).roots) :
      1 ≤ ‖1 - algebraMap (PadicAlgCl p) (PadicAlgCl p) w‖ :=
    h_far w (by simpa [sub_eq_zero] using (mem_roots'.1 hw).2)
  exact hb.not_ge (by
    simpa [monic_X_pow_sub_C, hf] using pow_le_norm_aeval _ 1 zero_le_one h_roots)

/-- If `toGp` is an open embedding, a continuous character `ν` that is trivial on inertia near `1`
is, on the preimage of some open subgroup of `G_p`, trivial on inertia (the `g` for which
`(toGp g, 0)` is a Weil pair) and at distance less than `1` from `1`. -/
private lemma exists_openSubgroup_trivial_on_inertia_and_norm_sub_lt_one [TopologicalSpace Γ]
    (h_emb : IsOpenEmbedding 𝒥.toGp) (hν : Continuous ν)
    (hν_inertia : ∀ᶠ g : Γ in 𝓝 1, IsWeilPair (toGp g) 0 → ν g = 1) :
    ∃ U : OpenSubgroup (Gp p), ∀ g : Γ, toGp g ∈ U →
      (IsWeilPair (toGp g) 0 → ν g = 1) ∧ ‖1 - (ν g).val‖ < 1 := by
  have h_close : ∀ᶠ g : Γ in 𝓝 1, ‖1 - (ν g).val‖ < 1 := by
    simpa [dist_eq_norm'] using Metric.continuous_iff'.mp (Units.continuous_val.comp hν) 1 1 one_pos
  have h_near : ∀ᶠ g : Γ in nearOne Γ, (IsWeilPair (toGp g) 0 → ν g = 1) ∧ ‖1 - (ν g).val‖ < 1 :=
    (nearOne_eq_nhds_one h_emb).le (hν_inertia.and h_close)
  obtain ⟨U, hU⟩ := NonarchimedeanGroup.is_nonarchimedean _ (mem_comap'.mp h_near)
  exact ⟨U, fun g hg ↦ hU hg rfl⟩

/-- Let `toGp` be an open embedding and `U` an open subgroup of `G_p`. The preimage of `U` contains
an arithmetic Frobenius `φ` for some `p ^ f` with `f ≠ 0`, and the `φ ^ k * i` with `i` in inertia
are dense in it: a closed set that contains them contains the whole preimage. -/
private lemma exists_isFrob_and_dense [TopologicalSpace Γ]
    (h_emb : IsOpenEmbedding 𝒥.toGp) (U : OpenSubgroup (Gp p)) :
    ∃ (f : ℕ) (φ : Γ), f ≠ 0 ∧ toGp φ ∈ U ∧ IsFrob (intQpBar p) (p ^ f) (toGp φ) ∧
      ∀ S : Set Γ, IsClosed S →
        (∀ (k : ℕ) (i : Γ), toGp i ∈ U → toGp i ∈ inertiaGroup (Gp p) (intQpBar p) →
          φ ^ k * i ∈ S) →
        ∀ g : Γ, toGp g ∈ U → g ∈ S := by
  -- `V` is the absolute Galois group of a finite extension of `ℚ_p`, of residue degree `f`
  let V : OpenSubgroup (Gp p) := U ⊓ ⟨𝒥.toGp.range, h_emb.isOpen_range⟩
  obtain ⟨h_local, ⟨e, f, ⟨hef, hq, -⟩, -⟩, -⟩ := IsLocalGalois.of_finite V
  obtain ⟨⟨⟨_, hφU, φ, rfl⟩, hφ⟩, h_dense, -⟩ := h_local.frobenius_spec
  refine ⟨f, φ, right_ne_zero_of_mul (hef.trans_ne index_ne_zero_of_finite), hφU,
    by rwa [hq, residueCard_padic] at hφ, fun S hS h_mem g hg ↦ ?_⟩
  -- `toGp g` lies in `V`, hence in the closure of the products, which lie in the image of `S`
  have h_closure : toGp g ∈ _root_.closure (𝒥.toGp '' S) := by
    refine map_mem_closure (f := Subtype.val) (by fun_prop) (h_dense hφ ⟨toGp g, hg, g, rfl⟩) ?_
    rintro _ ⟨⟨k, ⟨_, hiU, i, rfl⟩, hi⟩, rfl⟩
    exact ⟨φ ^ k * i, h_mem k i hiU hi, by simp⟩
  exact h_emb.isClosed_iff'.mp hS g h_closure

/-- Let `Γ` be a topological group with a map `toGp : Γ → Gp p` that is an open embedding, and let
`ν : Γ →* (PadicAlgCl p)ˣ` be a continuous character with `ν g = 1` for all `g` near `1` in `Γ` such
that `toGp g` lies in inertia (`IsWeilPair (toGp g) 0`). Then there are a `CoeffRing` `O`, meaning
the ring of integers of a finite Galois extension of ℚ_p in ℚ̄_p, and a unit `y` of
`Ainf ⊗[ℤ_[p]] O` such that: (a) `y` is fixed by φ^k s for every Weil pair `(s, k)`, that is,
whenever `s⁻¹` acts on the residue field of ℚ̄_p as Frobenius for `p ^ k`; and (b) for `g` in
`nearOne Γ`, the pull-back along `toGp` of the neighbourhoods of `1` in `G_p`, we have
`toGp g • y = (1 ⊗ o) * y` for some `o` in `O` equal to `ν g⁻¹`. -/
lemma exists_period_of_character [TopologicalSpace Γ]
    (h_emb : IsOpenEmbedding 𝒥.toGp) (hν : Continuous ν)
    (hν_inertia : ∀ᶠ g : Γ in 𝓝 1, IsWeilPair (toGp g) 0 → ν g = 1) :
    ∃ (O : CoeffRing p) (y : Ainf ⊗[ℤ_[p]] O.val),
      IsUnit y ∧
      -- (a)
      (∀ (s : Gp p) (k : ℕ), IsWeilPair s k → ((ofAdd k, s) : FrobGal) • y = y) ∧
      -- (b)
      ∀ᶠ g : Γ in nearOne Γ, ∃ o : O.val, toGp g • y = 1 ⊗ₜ o * y ∧ o.val = (ν g⁻¹).val := by
  -- Take the period of `exists_unramified_period` for an `f`-th root of `ν φ`, with `φ` a
  -- Frobenius; the identity to prove is closed and holds on the dense set of the `φ ^ k * i`.
  obtain ⟨U, hU⟩ := exists_openSubgroup_trivial_on_inertia_and_norm_sub_lt_one h_emb hν hν_inertia
  obtain ⟨f, φ, hf, hφU, hφ_frob, h_dense⟩ := exists_isFrob_and_dense h_emb U
  obtain ⟨a, ha, ha_near⟩ : ∃ a : PadicAlgCl p, a ^ f = ν φ ∧ ‖1 - a‖ < 1 :=
    exists_root_near_one hf (hU φ hφU).2
  obtain ⟨O, hO⟩ : ∃ O : CoeffRing p, 1 - a ∈ O.val :=
    (CoeffRing.eventually_mem ha_near.le).exists
  -- `a₀` is `a` as an element of `O`
  let a₀ : O.val := 1 - ⟨1 - a, hO⟩
  have h_nilp : ∃ n : ℕ, (p : O.val) ∣ (1 - a₀) ^ n := by
    obtain ⟨n, hn⟩ :=
      exists_pow_lt_of_lt_one (norm_pos_iff.mpr (NeZero.ne (p : PadicAlgCl p))) ha_near
    exact ⟨n, by simpa [a₀, O.dvd_iff_norm_le] using hn.le⟩
  obtain ⟨y, hy, h_line, h_weil⟩ := exists_unramified_period a₀ h_nilp
  refine ⟨O, y, hy, fun s k hs ↦ (h_weil s k hs).1, U, U.mem_nhds_one, fun g hg ↦ ?_⟩
  obtain ⟨o, ho⟩ : ∃ o : O.val, toGp g • y = 1 ⊗ₜ o * y := h_line (1, toGp g)
  refine ⟨o, ho, ?_⟩
  -- to identify `o`, map to `ℂ_[p]` by `θ`: the condition `g⁻¹ • y = ν g * y` becomes closed
  let Θ : Ainf ⊗[ℤ_[p]] O.val →ₐ[ℤ_[p]] ℂ_[p] :=
    productMap ((thetaBPlus.restrictScalars _).comp (toAlgHom _ Ainf _))
      ((toAlgHom ℤ_[p] (PadicAlgCl p) ℂ_[p]).comp O.val.val)
  let S : Set Γ := {g : Γ | Θ (toGp g⁻¹ • y) = ν g * Θ y}
  have h_closed : IsClosed S := by
    refine isClosed_eq ?_ (by fun_prop)
    -- on a pure tensor `a ⊗ o` the left side is `(toGp g⁻¹ • θ a) * o`
    obtain ⟨s, rfl⟩ : ∃ s : Finset (Ainf × O), y = ∑ i ∈ s, i.1 ⊗ₜ[ℤ_[p]] i.2 := y.exists_finset
    simp [Θ, Finset.smul_sum, smul_tmul']
    fun_prop
  -- it holds at `φ ^ k * i` with `i` in inertia: the inverse is a Weil element of degree `f * k`,
  -- so it multiplies `y` by `a ^ (f * k) = (ν φ) ^ k`, and `ν i = 1`
  have h_frob (k : ℕ) (i : Γ) (hiU : toGp i ∈ U)
      (hi : toGp i ∈ inertiaGroup (Gp p) (intQpBar p)) : φ ^ k * i ∈ S := by
    have h_pair : IsWeilPair (toGp (φ ^ k * i))⁻¹ (f * k) := by
      simpa [IsWeilPair, pow_mul] using (hφ_frob.pow k).mul_iff.mpr hi
    have h_smul : toGp (φ ^ k * i)⁻¹ • y = 1 ⊗ₜ a₀ ^ (f * k) * y := by
      rw [map_inv, (h_weil _ _ h_pair).2]
    have hνi : ν i = 1 := (hU i hiU).1 (inv_mem hi)
    show Θ (toGp (φ ^ k * i)⁻¹ • y) = (ν (φ ^ k * i)).val * Θ y
    rw [h_smul]
    simp [a₀, Θ, ha, hνi, coe_eq, pow_mul]
  -- these elements are dense in the preimage of `U`, so it holds at `g⁻¹`
  have h_apply : Θ (toGp g • y) = ν g⁻¹ * Θ y := by
    simpa [S] using h_dense S h_closed h_frob g⁻¹ (by simpa using hg)
  simpa [ho, Θ, (hy.map _).ne_zero, ← map_inv₀, coe_eq] using h_apply

/-- For a unit `z` of `Bmax ⊗ T`, the elements `(1 ⊗ x) * z` span `Bmax ⊗ T` over `Bmax`. -/
private lemma span_range_one_tmul_mul_eq_top {z : Bmax ⊗[ℤ_[p]] T} (hz : IsUnit z) :
    Submodule.span Bmax (Set.range fun x : T ↦ 1 ⊗ₜ x * z) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun w ↦ ?_
  obtain ⟨v, rfl⟩ : ∃ v : Bmax ⊗[ℤ_[p]] T, v * z = w := hz.unit.mulRight_bijective.2 w
  induction v with
  | tmul b x =>
    simpa [← smul_mul_assoc, smul_tmul'] using
      Submodule.smul_mem _ b (Submodule.subset_span ⟨x, rfl⟩ :
        1 ⊗ₜ x * z ∈ Submodule.span Bmax (Set.range fun x : T ↦ 1 ⊗ₜ x * z))
  | add v₁ v₂ h₁ h₂ => simpa [add_mul] using add_mem h₁ h₂

variable [Algebra (PadicAlgCl p) T] [IsScalarTower ℤ_[p] (PadicAlgCl p) T]

omit [Algebra ℤ_[p] T] [IsScalarTower ℤ_[p] (PadicAlgCl p) T] in
/-- Let `ρ` act on the `ℚ̄_p`-algebra `T` by the scalars `ν g`, and let `y` be a unit of
`A_inf ⊗ O` that `toGp g` multiplies by `ν g⁻¹` for `g` near `1`. Then `ρ` has the jumps of the
trivial representation on `T`. -/
private lemma jump_eq_jump_one_of_period {ρ : Γ →* End (PadicAlgCl p) T}
    (hρ : ∀ (g : Γ) (x : T), ρ g x = (ν g).val • x) {O : CoeffRing p}
    {y : Ainf ⊗[ℤ_[p]] O.val} (hy : IsUnit y)
    (h_near : ∀ᶠ g : Γ in nearOne Γ,
      ∃ o : O.val, toGp g • y = 1 ⊗ₜ o * y ∧ o.val = (ν g⁻¹).val) :
    jump ρ = jump (1 : Γ →* End (PadicAlgCl p) T) := by
  -- The image of `y` under `θ ⊗ γ` is a period of weight `0` for `ν⁻¹`, and a twist by a
  -- character with such a period keeps the jumps (`jump_twist_of_period`).
  ext γ u
  let Θ : Ainf ⊗[ℤ_[p]] O.val →ₐ[ℤ_[p]] ℂ_[p] :=
    productMap ((thetaBPlus.restrictScalars _).comp (toAlgHom _ Ainf _)) (γ.comp O.val.val)
  obtain ⟨S, hS⟩ := y.exists_finset
  obtain ⟨s, hs⟩ := exists_gp_eq_algHom γ
  -- `g` near `1` fixes the conjugates by `s` of the coefficients of `y`, so `Θ` commutes with
  -- `g` on `y`
  have h_coef : ∀ᶠ g : Γ in nearOne Γ, ∀ i ∈ S, toGp g (s i.2) = s i.2 :=
    S.eventually_all.2 fun i _ ↦ eventually_nearOne_apply_eq Γ (s i.2)
  have h_period : ∀ᶠ g : Γ in nearOne Γ,
      γ (ν g⁻¹).val * Θ y = (χ g ^ (-0 : ℤ)).val • toGp g • Θ y := by
    filter_upwards [h_near, h_coef] with g ⟨o, h_line, ho⟩ h_fix
    simpa +contextual [Θ, hS, hs, ho, h_fix, Finset.smul_sum, smul_tmul'] using
      (congrArg Θ h_line).symm
  simpa using (jump_twist_of_period _ (hy.map Θ).ne_zero h_period (by simp [hρ])).symm

variable (T) in
/-- The map `A_inf ⊗ O → Bmax ⊗ T` induced by `A_inf → Bmax` and `O ⊆ ℚ̄_p → T`. -/
private noncomputable def toBmaxTensor (O : CoeffRing p) :
    Ainf ⊗[ℤ_[p]] O.val →ₐ[ℤ_[p]] Bmax ⊗[ℤ_[p]] T :=
  map (toAlgHom ℤ_[p] Ainf Bmax) ((toAlgHom ℤ_[p] (PadicAlgCl p) T).comp O.val.val)

omit [OverGp Γ p] in
/-- Let `ρ` act on `T` by the scalars `ν g`. Then `m ⊗ ρ g` sends `(1 ⊗ x) * z` to `ν h` times
`(1 ⊗ ρ (h⁻¹ * g) x) * (m • z)`, where `z` and `m • z` are mapped to `Bmax ⊗ T`. -/
private lemma tensorAction_one_tmul_mul_toBmaxTensor {ρ : Γ →* End (PadicAlgCl p) T}
    (hρ : ∀ (g : Γ) (x : T), ρ g x = (ν g).val • x) {O : CoeffRing p} (m : FrobGal) (h g : Γ)
    (x : T) (z : Ainf ⊗[ℤ_[p]] O.val) :
    tensorAction Bmax m (ρ g) (1 ⊗ₜ x * toBmaxTensor T O z) =
      coeffEnd (PadicAlgCl p) T (ν h).val (1 ⊗ₜ ρ (h⁻¹ * g) x * toBmaxTensor T O (m • z)) := by
  obtain ⟨S, rfl⟩ := z.exists_finset
  simp [toBmaxTensor, tensorAction, hρ, Finset.mul_sum, Finset.smul_sum, smul_tmul']

/-- Let `ρ` act on `T` by the scalars `ν g`, and let `toGp g` multiply `y ∈ A_inf ⊗ O` by `ν g⁻¹`
for `g` near `1`. Then the elements `(1 ⊗ x) * y` of `Bmax ⊗ T` are fixed by all `g` near `1`. -/
private lemma one_tmul_mul_toBmaxTensor_mem_dpcris {ρ : Γ →* End (PadicAlgCl p) T}
    (hρ : ∀ (g : Γ) (x : T), ρ g x = (ν g).val • x) {O : CoeffRing p} {y : Ainf ⊗[ℤ_[p]] O.val}
    (h_near : ∀ᶠ g : Γ in nearOne Γ,
      ∃ o : O.val, toGp g • y = 1 ⊗ₜ o * y ∧ o.val = (ν g⁻¹).val) (x : T) :
    1 ⊗ₜ x * toBmaxTensor T O y ∈ Dpcris ρ := by
  -- The factor `ν g⁻¹` on `y` cancels the factor `ν g` on `x`.
  refine h_near.mono fun g ⟨o, (h_line : ((1, toGp g) : FrobGal) • y = 1 ⊗ₜ o * y), ho⟩ ↦ ?_
  show tensorAction Bmax ((1, toGp g) : FrobGal) (ρ g) (1 ⊗ₜ x * toBmaxTensor T O y) = _
  rw [tensorAction_one_tmul_mul_toBmaxTensor hρ (1, toGp g) 1, h_line]
  simp [toBmaxTensor, hρ, ho, algebraMap_eq_smul_one, ← mul_assoc]

variable [TopologicalSpace Γ]

/-- Let `𝒥.toGp` be an open embedding and `ν` a continuous character of `Γ`, trivial on inertia near
`1`. If `ρ` acts on a commutative `ℚ̄_p`-algebra `T` by the scalars `ν g`, then `ρ` is potentially
crystalline. -/
lemma IsPotentiallyCrystalline.of_unramified_char (h_emb : IsOpenEmbedding 𝒥.toGp)
    (hν : Continuous ν) (hν_inertia : ∀ᶠ g : Γ in 𝓝 1, IsWeilPair (toGp g) 0 → ν g = 1)
    {ρ : Γ →* End (PadicAlgCl p) T} (hρ : ∀ (g : Γ) (x : T), ρ g x = (ν g).val • x) :
    IsPotentiallyCrystalline ρ := by
  -- With the period `y` of `exists_period_of_character`, the elements `(1 ⊗ x) * y` are fixed near
  -- `1`, and they span `Bmax ⊗ T` because `y` is a unit.
  obtain ⟨O, y, hy, -, h_near⟩ := exists_period_of_character h_emb hν hν_inertia
  have h_fixed : Set.range (fun x : T ↦ 1 ⊗ₜ x * toBmaxTensor T O y) ⊆ Dpcris ρ :=
    Set.range_subset_iff.2 (one_tmul_mul_toBmaxTensor_mem_dpcris hρ h_near)
  change Submodule.span Bmax (Dpcris ρ : Set (Bmax ⊗[ℤ_[p]] T)) = ⊤
  exact top_unique ((span_range_one_tmul_mul_eq_top (hy.map _)).ge.trans
    (Submodule.span_mono h_fixed))

omit [Algebra ℤ_[p] T] [IsScalarTower ℤ_[p] (PadicAlgCl p) T] in
/-- Let `𝒥.toGp` be an open embedding and `ν` a continuous character of `Γ`, trivial on inertia near
`1`. If `ρ` acts on a commutative `ℚ̄_p`-algebra `T` by the scalars `ν g`, then `ρ` has the jumps
(Hodge–Tate weights with multiplicity) of the trivial representation on `T`. -/
lemma jump_eq_jump_one_of_unramified_char (h_emb : IsOpenEmbedding 𝒥.toGp) (hν : Continuous ν)
    (hν_inertia : ∀ᶠ g : Γ in 𝓝 1, IsWeilPair (toGp g) 0 → ν g = 1) {ρ : Γ →* End (PadicAlgCl p) T}
    (hρ : ∀ (g : Γ) (x : T), ρ g x = (ν g).val • x) :
    jump ρ = jump (1 : Γ →* End (PadicAlgCl p) T) := by
  obtain ⟨O, y, hy, -, h_near⟩ := exists_period_of_character h_emb hν hν_inertia
  exact jump_eq_jump_one_of_period hρ hy h_near

/-- Let `𝒥.toGp` be an open embedding and `ν` a continuous character of `Γ`, trivial on inertia near
`1`, and let `ρ` act on a commutative `ℚ̄_p`-algebra `T` by the scalars `ν g`. For a Weil pair
`(toGp s, k)`, the polynomial `X - ν s` kills `ρ` at `s` and `k`: `ρ` is potentially crystalline and
`linearFrob ρ s k` is multiplication by `ν s` on `Bmax ⊗ T`. -/
lemma isKilledBy_X_sub_C_of_unramified_char (h_emb : IsOpenEmbedding 𝒥.toGp) (hν : Continuous ν)
    (hν_inertia : ∀ᶠ g : Γ in 𝓝 1, IsWeilPair (toGp g) 0 → ν g = 1) {ρ : Γ →* End (PadicAlgCl p) T}
    (hρ : ∀ (g : Γ) (x : T), ρ g x = (ν g).val • x) {s : Γ} {k : ℕ} (hs : IsWeilPair (toGp s) k) :
    IsKilledBy ρ s k (X - C (ν s).val) := by
  -- It is enough to compute `linearFrob` on the elements `(1 ⊗ x) * y`, with `y` the period of
  -- `exists_period_of_character`: they span `Bmax ⊗ T` because `y` is a unit.
  have h_pcr : IsPotentiallyCrystalline ρ := .of_unramified_char h_emb hν hν_inertia hρ
  obtain ⟨O, y, hy, h_weil, h_near⟩ := exists_period_of_character h_emb hν hν_inertia
  -- `φ ^ k s` fixes `y`, and `ρ s` multiplies `x` by `ν s`.
  have h_frob : linearFrob ρ s k = coeffEnd (PadicAlgCl p) T (ν s).val := by
    refine ext_on_range (span_range_one_tmul_mul_eq_top (hy.map (toBmaxTensor T O))) fun x ↦ ?_
    simp [linearFrob_apply h_pcr hs, tensorAction_one_tmul_mul_toBmaxTensor hρ _ s,
      one_tmul_mul_toBmaxTensor_mem_dpcris hρ h_near x, h_weil (toGp s) k hs]
  exact ⟨h_pcr, by simp [h_frob]⟩

/-- Let `𝒥.toGp` be an open embedding and `ν` a continuous character of `Γ`, trivial on inertia near
`1`, and let `ρ` act on a commutative `ℚ̄_p`-algebra `T` by the scalars `ν g`. Then `ρ` is
potentially crystalline, has the jumps of the trivial action, and for every Weil pair `(toGp s, k)`
the polynomial `X - ν s` kills `linearFrob ρ s k`.

A case of the fact that potentially unramified characters are potentially crystalline of weight 0
(Caruso). -/
lemma isPotentiallyCrystalline_of_unramified_char (h_emb : IsOpenEmbedding 𝒥.toGp)
    (hν : Continuous ν) (hν_inertia : ∀ᶠ g : Γ in 𝓝 1, IsWeilPair (toGp g) 0 → ν g = 1)
    {ρ : Γ →* End (PadicAlgCl p) T} (hρ : ∀ (g : Γ) (x : T), ρ g x = (ν g).val • x) :
    -- (a) potentially crystalline
    IsPotentiallyCrystalline ρ ∧
    -- (b) the jumps of the trivial representation
    jump ρ = jump (1 : Γ →* End (PadicAlgCl p) T) ∧
    -- (c) a Weil element `s` acts by the scalar `ν s`
    ∀ (s : Γ) (k : ℕ), IsWeilPair (toGp s) k → IsKilledBy ρ s k (X - C (ν s).val) :=
  ⟨.of_unramified_char h_emb hν hν_inertia hρ,
    jump_eq_jump_one_of_unramified_char h_emb hν hν_inertia hρ,
    fun _ _ hs ↦ isKilledBy_X_sub_C_of_unramified_char h_emb hν hν_inertia hρ hs⟩

end New.Period

/-!
## Local conditions for characters and for avatars with vanishing type

The local conditions `New.GaloisRep.IsFiniteTypeAt`, `New.GaloisRep.IsGoodAt`,
`New.GaloisRep.HasJumpsAt` and `New.GaloisRep.PolyKillsAt` for characters, at a valuation subring A
of Ω over a place w of E.
-/

namespace New.GaloisRep

open NumberField Matrix.GeneralLinearGroup Polynomial Period QuotientGroup AlgHeckeChar

section FiniteInertiaImage

variable {ℓ : ℕ} [ThePrime ℓ] {E : Type} [Field E] [EmbeddedNumberField E]
  {A : ClosurePlace} {μ : Gal(Ω/E) →* (PadicAlgCl ℓ)ˣ} {m : Type} [Fintype m] [DecidableEq m]

/-- A continuous character with finite image on the inertia group of A is trivial on the elements
of inertia near 1. -/
lemma eventually_eq_one_of_finite_image_inertia (hμ : Continuous μ)
    (hfin : (μ '' inertiaGroup Gal(Ω/E) A).Finite) :
    ∀ᶠ s : Gal(Ω/E) in nhds 1, s ∈ inertiaGroup Gal(Ω/E) A → μ s = 1 := by
  -- The set of values `≠ 1` on inertia is finite, hence closed, and its preimage misses `1`.
  have h_closed : IsClosed (μ ⁻¹' {z ∈ μ '' inertiaGroup Gal(Ω/E) A | z ≠ 1}) :=
    (hfin.sep fun z ↦ z ≠ 1).isClosed.preimage hμ
  filter_upwards [h_closed.compl_mem_nhds (by simp)] with s hs hs_inertia
  by_contra h_ne
  exact hs ⟨Set.mem_image_of_mem μ hs_inertia, h_ne⟩

/-- The map of a chart L at A from the decomposition group to Gal(ℚ̄_ℓ/ℚ_ℓ) is an open embedding. -/
private lemma isOpenEmbedding_toGp (L : PadicPlaceEmbedding E A ℓ) :
    Topology.IsOpenEmbedding L.toGp := by
  obtain ⟨-, h_open, -⟩ := L.inducesPlace
  exact h_open

/-- The form of `eventually_eq_one_of_finite_image_inertia` along a chart L at A: the character is
trivial at the s near 1 in the decomposition group for which (`L.toGp s`, 0) is a Weil pair. -/
private lemma eventually_eq_one_of_isWeilPair_zero [L : PadicPlaceEmbedding E A ℓ]
    (hμ : Continuous μ) (hfin : (μ '' inertiaGroup Gal(Ω/E) A).Finite) :
    ∀ᶠ s : decompGroup Gal(Ω/E) A in nhds 1,
      IsWeilPair (L.toGp s) 0 → μ.domRestrict (decompGroup Gal(Ω/E) A) s = 1 :=
  (continuousAt_subtype_val.eventually (eventually_eq_one_of_finite_image_inertia hμ hfin)).mono
    fun _ hs h_pair ↦ hs (L.isWeilPair_zero_iff.1 h_pair)

/-- If a continuous ℓ-adic character μ has finite image on the inertia group of A, then the
representation by the scalar matrices μ(s) is of finite type at A: trivial on inertia near 1 off ℓ,
potentially crystalline above ℓ. -/
lemma IsFiniteTypeAt.scalar_of_finite_image_inertia (hμ : Continuous μ)
    (hfin : (μ '' inertiaGroup Gal(Ω/E) A).Finite) : IsFiniteTypeAt ((scalar m).comp μ) A := by
  refine ⟨fun _ ↦ ?_, fun {L} ↦ ?_⟩
  · filter_upwards [eventually_eq_one_of_finite_image_inertia hμ hfin] with s h_one hs using
      by simp [h_one hs]
  · exact .of_unramified_char (isOpenEmbedding_toGp L) hμ.continuousOn.domRestrict
      (eventually_eq_one_of_isWeilPair_zero hμ hfin) (by simp)

/-- If a continuous ℓ-adic character μ has finite image on the inertia group of A, then X − μ(s)
kills s for the representation r by the scalar matrices μ(s): it annihilates r(s) off ℓ, and above
ℓ the linearised Frobenius on periods at every Weil pair given by s. -/
lemma polyKillsAt_X_sub_C_of_finite_image_inertia (hμ : Continuous μ)
    (hfin : (μ '' inertiaGroup Gal(Ω/E) A).Finite) (s : Gal(Ω/E)) :
    PolyKillsAt ((scalar m).comp μ) A s (X - C (μ s).val) := by
  refine ⟨fun _ ↦ ?_, fun {L} hs k hk ↦ ?_⟩
  · have h_scalar : ((scalar m).comp μ s).val =
        algebraMap (PadicAlgCl ℓ) (Matrix m m (PadicAlgCl ℓ)) (μ s).val := rfl
    rw [map_sub, aeval_X, aeval_C, h_scalar, sub_self]
  · -- The decomposition group acts by the scalars `μ t`, and `μ` is trivial on inertia near `1`.
    have h_scalar (t : decompGroup Gal(Ω/E) A) (x : m → PadicAlgCl ℓ) :
        decompRep ((scalar m).comp μ) A t x = (μ t).val • x := by simp
    exact isKilledBy_X_sub_C_of_unramified_char (isOpenEmbedding_toGp L)
      hμ.continuousOn.domRestrict (eventually_eq_one_of_isWeilPair_zero hμ hfin) h_scalar hk

end FiniteInertiaImage

variable {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ] {E : Type} [Field E] [EmbeddedNumberField E]
  {A : ClosurePlace} {w : FinPlace E} {μ : Gal(Ω/E) →* (PadicAlgCl ℓ)ˣ}
  {m : Type} [Fintype m] [DecidableEq m]

/-- The condition `JumpsRelAt r A R J` (the relation `R` holds between the multiplicities in `J` and
those of the Hodge–Tate jumps of `r` at A) at a place A over w depends only on the values of J at
the embeddings τ that induce w. -/
lemma JumpsRelAt.congr {r : GalRep ℓ E m} {R : ℕ → ℕ → Prop} {J J' : (E →+* ℂ) → Multiset ℤ}
    (hA : IsPlaceOver A w) (h : JumpsRelAt r A R J)
    (hJ : ∀ τ : E →+* ℂ, inducedPrime τ = w → J τ = J' τ) : JumpsRelAt r A R J' := by
  intro L γ g hg
  -- The chart `L.e` induces `A` and `g⁻¹` keeps norms, so `g⁻¹ ∘ L.e` induces `w` on `E`.
  have hw : w = placeOfEmb (L.e.comp (algebraMap E Ω)) :=
    hA.unique (by simpa [L.inducesPlace.1.1] using isPlaceOver_placeOfEmb L.e)
  let τ : E →+* ℂ := .comp ιℓ.symm (.comp ↑g⁻¹ (L.e.comp (algebraMap E Ω)) : E →+* PadicAlgCl ℓ)
  have hτ : inducedPrime τ = w := by
    ext x
    simpa [τ, hw] using congrArg (· < 1)
      (norm_smul_Cp g⁻¹ (L.e (algebraMap E Ω (algebraMap (𝓞 E) E x)) : ℂ_[ℓ]))
  rw [← hJ τ hτ]
  exact h hg

/-- If a continuous ℓ-adic character μ has finite image on the inertia group of A, then the
representation of rank one that it defines has the single Hodge–Tate jump 0 along every chart
at A. -/
lemma hasJumpsAt_zero_of_finite_image_inertia [Unique m] (hμ : Continuous μ)
    (hfin : (μ '' inertiaGroup Gal(Ω/E) A).Finite) :
    HasJumpsAt ((scalar m).comp μ) A fun _ : E →+* ℂ ↦ {0} := by
  -- The jumps are those of the trivial action, which has the single jump `0`.
  have h_jump [L : PadicPlaceEmbedding E A ℓ] : jump (decompRep ((scalar m).comp μ) A) =
      jump (1 : decompGroup Gal(Ω/E) A →* Module.End (PadicAlgCl ℓ) (m → PadicAlgCl ℓ)) :=
    jump_eq_jump_one_of_unramified_char (isOpenEmbedding_toGp L) hμ.continuousOn.domRestrict
      (eventually_eq_one_of_isWeilPair_zero hμ hfin) (by simp)
  simp [JumpsRelAt, h_jump, hasJumps_of_cyclotomicGp_zpow 0 _ _]

/-- Let μ be a continuous ℓ-adic character with finite image on the inertia group of A, and r the
representation of rank one that it defines. Then (a) r is of finite type at A (trivial on inertia
near 1 off ℓ, potentially crystalline above ℓ), (b) its only Hodge–Tate jump is 0 along every chart
at A, and (c) X − μ(s) kills every s in the sense of `PolyKillsAt`: it annihilates r(s) off ℓ, and
above ℓ the linearised Frobenius on periods at every Weil pair given by s. -/
lemma localConditions_char_of_finite_image_inertia [Unique m] (hμ : Continuous μ)
    (hfin : (μ '' inertiaGroup Gal(Ω/E) A).Finite) :
    let r : GalRep ℓ E m := (scalar m).comp μ
    -- (a) finite type
    IsFiniteTypeAt r A ∧
    -- (b) the only jump is 0
    HasJumpsAt r A (fun _ : E →+* ℂ ↦ {0}) ∧
    -- (c) each `s` is killed by `X - μ s`
    ∀ s : Gal(Ω/E), PolyKillsAt r A s (X - C (μ s).val) :=
  ⟨.scalar_of_finite_image_inertia hμ hfin, hasJumpsAt_zero_of_finite_image_inertia hμ hfin,
    polyKillsAt_X_sub_C_of_finite_image_inertia hμ hfin⟩

variable [IsTotallyComplex E] (θ : AlgHeckeChar E)

/-! ### Avatars of algebraic Hecke characters -/

variable (w) in
/-- Local-global compatibility at w for the avatar r of θ, whose infinity type is n. At every A over
w: (a) r is of finite type at A; (b) its jump at τ is −n(τ) for the τ that come from charts at A;
(c) for m = 0 or 1 and every s whose inverse is a Frobenius for the power q^m, q the norm of w,
there is x in E_w^× of order m with local Artin symbol the class of s, and X − ι(θ(x)) kills s. -/
def AvatarCompatAt : Prop :=
  ∀ ⦃A : ValuationSubring Ω⦄, IsPlaceOver A w →
    let r : GalRep ℓ E (Fin 1) := (scalar (Fin 1)).comp θ.avatar
    -- (a) finite type, (b) the jump at `τ` is minus the exponent of `θ`
    IsFiniteTypeAt r A ∧
    HasJumpsAt r A (fun τ : E →+* ℂ ↦ {-θ.infinityType τ}) ∧
    -- (c) `s` is in inertia (`m = 0`) or a geometric Frobenius (`m = 1`)
    ∀ s : Gal(Ω/E), ∀ m ≤ (1 : ℕ), ∀ h : IsFrob A (w.q ^ m) s⁻¹,
      ∃ x : (w.adicCompletion E)ˣ,
        Valued.v x.val = .exp (-m) ∧
        localArtin Gal(Ω/E) A w x = (⟨s, inv_mem h.1⟩ : decompGroup Gal(Ω/E) A) ∧
        PolyKillsAt r A s (X - C (ιℓ (θ.character (locIdele w x))))

/-- If w ∤ ℓ and θ is unramified at w, the ℓ-adic avatar of θ at a geometric Frobenius at A over
w equals ι of the value of θ at the local idele of the chosen uniformiser at w. -/
lemma _root_.New.AlgHeckeChar.avatar_frob (hA : IsPlaceOver A w) (hℓ : ↑ℓ ∉ w.asIdeal)
    (h_unr : New.CharUnramifiedAt θ.character w) {s : Gal(Ω/E)} (hs : IsFrob A w.q s⁻¹) :
    (avatar θ s).val = ιℓ (heckeCoeff θ.character ∅ w) := by
  -- The class of `s` is the local Artin symbol of an `x` with the valuation of a uniformiser.
  obtain ⟨x, hx, hxs⟩ := hA.exists_localArtin_eq_of_isFrob hs
  -- Off `ℓ` the avatar at `s` is `ιℓ (θ x)`, and `θ x` depends only on the valuation of `x`.
  simp [hx, h_unr.apply_locIdele_eq_zpow x, heckeCoeff, θ.avatar_localArtin hA (.inl hℓ) hxs]

/-- For most geometric Frobenius elements s at places w (the filter `New.mostFrobenii`), the avatar
of θ at s is ι of the value of θ at the chosen uniformiser at w. -/
lemma _root_.New.AlgHeckeChar.eventually_avatar_frob :
    ∀ᶠ y : FrobeniusDatum E in mostFrobenii E,
      (avatar θ y.frob).val = ιℓ (heckeCoeff θ.character ∅ y.place) := by
  -- Almost all places are unramified for `θ` and prime to `ℓ`.
  obtain ⟨h_open, -⟩ := θ.property
  have h_good : ∀ᶠ w : FinPlace E in .cofinite, CharUnramifiedAt θ.character w ∧ ↑ℓ ∉ w.asIdeal :=
    (eventually_unramified _ h_open).and (finite_natCast_mem ℓ).compl_mem_cofinite
  exact eventually_mostFrobenii h_good fun y ⟨h_unr, hℓ⟩ ↦
    θ.avatar_frob y.isPlaceOver hℓ h_unr y.isFrob_inv

/-- Local-global compatibility `New.GaloisRep.AvatarCompatAt` holds at w for the ℓ-adic avatar r of
an algebraic Hecke character θ of a totally complex E whose exponent n_σ vanishes for every σ with
ισ inducing w (`inducedPrime σ = w`). That is, at every A over w: r is of finite type; its jump at τ
is −n(τ); and for m = 0, 1, each s whose inverse is a Frobenius for q^m (q the norm of w) is killed
by X − ι(θ(x)) for some x in E_w^× of order m with local Artin symbol the class of s.

A case of the description of Hodge–Tate weights and Weil–Deligne representations of avatars of
algebraic Hecke characters: E is totally complex, and w is a place where the exponents at all
embeddings inducing w vanish. -/
lemma avatarCompatAt_of_type_eq_zero
    (h_type : ∀ σ : E →+* ℂ, inducedPrime σ = w → θ.infinityType σ = 0) : AvatarCompatAt w θ := by
  intro A hA
  obtain ⟨h_open, -⟩ := θ.property
  -- On the Weil group the avatar is `ιℓ ∘ θ`, read through local class field theory.
  have av_eq {x : (w.adicCompletion E)ˣ} {g : decompGroup Gal(Ω/E) A}
      (h : localArtin Gal(Ω/E) A w x = ⟦g⟧) : (avatar θ g).val = ιℓ (θ.character (locIdele w x)) :=
    θ.avatar_localArtin hA (.inr h_type) h
  -- Inertia comes from the compact group of unit ideles, and the kernel of `θ` is open.
  have finite : (avatar θ '' inertiaGroup Gal(Ω/E) A).Finite := by
    refine .of_surjOn (fun y ↦ Units.map ιℓ (kerLift θ.character y)) ?_
      (finite_quotient_image_of_isCompact h_open isCompact_idelesUnitOff_empty)
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨x, hx, hxs⟩ := hA.exists_localArtin_eq_of_mem_inertiaGroup hs
    exact ⟨QuotientGroup.mk (locIdele w x), ⟨locIdele w x, locIdele_mem_idelesUnitOff hx, rfl⟩,
      Units.ext (av_eq hxs).symm⟩
  -- So the avatar is of finite type with the single jump `0`, which is `-n τ` for `τ` over `w`.
  have h_jump : HasJumpsAt ((scalar (Fin 1)).comp θ.avatar) A fun _ : E →+* ℂ ↦ {0} :=
    hasJumpsAt_zero_of_finite_image_inertia (continuous_avatar θ) finite
  refine ⟨.scalar_of_finite_image_inertia (continuous_avatar θ) finite,
    h_jump.congr hA fun τ hτ ↦ by simp [h_type τ hτ], fun s m _ hs ↦ ?_⟩
  obtain ⟨x, hx, hxs⟩ := hA.exists_localArtin_eq_of_isFrob_pow hs
  exact ⟨x, hx, hxs, by simpa [av_eq hxs] using
    polyKillsAt_X_sub_C_of_finite_image_inertia (m := Fin 1) (continuous_avatar θ) finite s⟩

/-- Suppose local-global compatibility `AvatarCompatAt` holds at w for θ, with infinity type n, and
θ is unramified at w. Then at every place A of Ω over w, the avatar r of θ (a) is good (unramified
if ℓ is a unit at A, crystalline above ℓ). (b) Its Hodge–Tate jump multiplicities at the embeddings
τ coming from charts at A equal those of the single weight −n(τ), which is the role of the relation
`Eq` against the sets {−n(τ)}. (c) X − ι(θ(ϖ_w)) kills every geometric Frobenius at A, ϖ_w being the
chosen uniformiser (`heckeCoeff`). -/
lemma AvatarCompatAt.isSphericalAbove_of_unramified {θ : AlgHeckeChar E} (h_av : AvatarCompatAt w θ)
    (h_unr : New.CharUnramifiedAt θ.character w) :
    IsSphericalAbove ((scalar (Fin 1)).comp (avatar θ)) Eq (fun τ : E →+* ℂ ↦ {-θ.infinityType τ}) w
      (X - C (ιℓ (heckeCoeff θ.character ∅ w))) := by
  intro A hA
  obtain ⟨h_fin, h_jump, h_kill⟩ := h_av hA
  -- `isGoodAt_iff`: good means of finite type with inertia killed by `X - 1`.
  refine ⟨isGoodAt_iff.2 ⟨h_fin, fun s hs ↦ ?_⟩, h_jump, fun s hs ↦ ?_⟩
  · -- Inertia comes from local units, on which `θ` is trivial.
    obtain ⟨x, hx, -, hs_poly⟩ := h_kill s 0 zero_le_one (inv_mem hs)
    simpa [h_unr.apply_locIdele_eq_zpow x, hx] using hs_poly
  · -- A Frobenius element comes from a uniformiser.
    obtain ⟨x, hx, -, hs_poly⟩ := h_kill s 1 le_rfl (by simpa using hs)
    simpa [h_unr.apply_locIdele_eq_zpow x, hx, heckeCoeff] using hs_poly

end New.GaloisRep
