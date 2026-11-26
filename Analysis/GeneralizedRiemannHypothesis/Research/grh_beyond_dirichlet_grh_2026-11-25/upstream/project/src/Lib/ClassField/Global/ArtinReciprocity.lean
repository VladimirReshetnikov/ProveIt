import Lib.Adelic.Adeles.LocalFactors
import Lib.ClassField.Global.AlbertBrauerHasseNoether

/-!
# Artin's reciprocity law and the sign law

Global reciprocity for a number field `K` with absolute Galois group `Γ`, on finite ideles.

## Overview of this theory

Class field theory, local duality and Hecke `L`-functions, in the cases that the proof uses. Here
`K` is a number field and `Γ` an absolute Galois group.

* `New.IsHeckeOfType.eulerProd_ne_zero`: for a Hecke character `ψ` of `K` whose infinity type is
  given by an integer at each infinite place, with `ψ ^ 2 ≠ 1`, and a finite set `S` of primes, the
  partial `L`-function `L^S(s, ψ)` is nonzero for real `s ≥ 1`.
* `New.IsLocalGalois.classOfInvariant_bijective`: for a henselian local field `k` of characteristic
  `0`, not necessarily complete, the map from `ℚ/ℤ` to `H²(Γ, k̄ˣ)` is bijective. So the Brauer
  group of `k` is `ℚ/ℤ`.
* `New.exists_comp_artinMap`: for totally complex `K`, a continuous homomorphism from the finite
  ideles `𝔸_fˣ` to a `T₁` group that is trivial on `Kˣ` factors continuously through `Art`.
* `New.card_mul_card_le_of_orthogonal`: let `k` be local with valuation ring `O`, `l` a prime with
  `#(O/l) = l ^ d`, and `M` a finite Galois module killed by `l ^ r`. Suppose `M` is fixed by a
  subgroup `Q` containing an `l`-power of every element. If groups of 1-cocycles `X` in
  `Hom(M, k̄ˣ)` and `W` in `M` are orthogonal under cup product, then `#X · #W ≤ #M ^ (2 + d)`.
* `New.RelationSetting.exists_card_cocycles_le`: let `K` be totally complex and `M` finite, killed
  by `ℓ ^ r`, unramified outside a finite set `S`, with local conditions at `S` that contain the
  coboundaries. Relations are equivariant homomorphisms from an open normal subgroup `U` to the dual
  of `M` that obey the reciprocity law at the primes split for `U`. If some element is central
  modulo `U`, fixes the roots of unity of `ℓ`-power order and fixes no nonzero vector, the number of
  relations is bounded from below by the number of Selmer cocycles and the local terms.

These replace local and global class field theory (finite ideles only, no Weil group), local Tate
duality and the Greenberg–Wiles formula (inequalities for cocycles; no perfect pairing, no dual
Selmer group), and the continuation of Hecke `L`-functions (infinity type given by integers, real
`s` only).

`Places` and `GaloisCohomology` give the setting. `Local` builds the invariant and the local Artin
map, and `LocalDuality` counts by Kummer theory and dévissage. In `Global`, prime densities from
`HeckeL` give the second inequality. This gives Chebotarev and, with Tate's index formula for
`S`-units, Albert–Brauer–Hasse–Noether. Norm and existence theorems come next. `GreenbergWiles`
counts cocycles by `S`-units and power residue reciprocity. `Grunwald`, `Avatar` and
`HeckeCharacter` hold applications. `New.exists_avatar` is in `Lib.PadicHodge.Characters`.

## This file

* `New.artin_reciprocity`: if the symbol `(ξ, x)` dies on an open subgroup containing the complex
  conjugations, the character `ξ` kills the Artin symbol of `x ∈ Kˣ`. This applies when `ξ` kills
  the conjugations (`New.abelianLift_artinMap_principalIdele_eq_one`) or `x` is totally positive
  (`New.artinMap_principalIdele_eq_one_of_isTotallyPositive`).
* `New.abelianLift_artinMap_principalIdele_eq_one_iff`: the sign law for characters nontrivial on
  all conjugations.

The case `K(μ_q)` is `New.artin_reciprocity_cyclotomic`. Characters `χ : New.QZChar Γ` are
continuous with values in `ℚ/ℤ`. `New.QZChar.abelianLift χ` is the induced map on the
abelianisation, written multiplicatively. `artinMap Γ (principalIdele x)` is the Artin symbol of the
finite idele of `x`. Only `Γ` is an explicit argument of `artinMap`; `ideleAt v` takes the component
at `v` of an idele. There are no components at the real places.

Notions from other files:
* `New.IsProGalois`: a profinite group acts on the Galois extension Ω/K (Ω the fixed algebraic
  closure of ℚ; `EmbeddedNumberField K` puts the number field `K` inside Ω) as its Galois group,
  with open stabilisers.
* `New.cyclicClass`: The symbol (χ, w) = δχ ∪ w in H²(Γ, M) of a character χ : Γ → ℚ/ℤ and an
  invariant w; here M = Ωˣ (`New.unitsModule`), and `DiscreteUnits.ofBase` sends `x ∈ Kˣ` to an
  invariant of Ωˣ, and `resH2` restricts classes to a subgroup.
* `New.artinAt`: The local Artin map K_v^× → Γ^ab, through the decomposition group of the chosen
  valuation subring `New.placeOver v` over v.

## Relation to the literature

Known; see `Lib.ClassField.Global.AlbertBrauerHasseNoether` for sources.
-/

namespace New

open NumberField Set Subgroup QZChar QZ Nat Algebra IsCyclotomicExtension Cohomology
  MulSemiringAction HeightOneSpectrum Polynomial Valuation IsAlgClosed ZMod

variable {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [Field K] [EmbeddedNumberField K]
  [MulSemiringAction Γ Ω] [IsProGalois Γ K Ω]

omit [TopologicalSpace Γ] in
/-- Let `s` be in the inertia group of `A` and send `ζ` (with `ζ ≡ 1` and `ζ ≠ 1`) to `ζ ^ a`. For
a unit `w` of `A` and `y = (ζ - 1) * w`, the quotient `s • y / y` is `≡ a` modulo the maximal
ideal. -/
lemma valuation_smul_div_sub_natCast_lt_one {A : ValuationSubring Ω} {s : Γ}
    (hs : s ∈ inertiaGroup Γ A) {ζ w : Ω} {a : ℕ} (hζ : ζ ≠ 1) (hζ_cong : A.valuation (ζ - 1) < 1)
    (ha : s • ζ = ζ ^ a) (hw : A.valuation w = 1) :
    A.valuation (s • ((ζ - 1) * w) / ((ζ - 1) * w) - a) < 1 := by
  have h_mem (x : Ω) (hx : A.valuation (x - 1) < 1) :
      Units.mk0 x (fun h0 : x = 0 ↦ hx.ne (by simp [h0])) ∈ A.principalUnitGroup := hx
  -- The elements `≡ 1` form a group, which holds `ζ` and `s • w / w`.
  have h_term (i : ℕ) : A.valuation (ζ ^ i * (s • w / w) - 1) < 1 := by
    simpa [ValuationSubring.mem_principalUnitGroup_iff] using
      mul_mem (pow_mem (h_mem ζ hζ_cong) i) (h_mem _ (valuation_smul_div_sub_one_lt_one hs hw))
  -- The quotient is `(ζ ^ a - 1) / (ζ - 1) * (s • w / w)`, a sum of `a` such elements.
  have h_sum :
      s • ((ζ - 1) * w) / ((ζ - 1) * w) - a = ∑ i ∈ Finset.range a, (ζ ^ i * (s • w / w) - 1) := by
    simp [geom_sum_eq hζ, ← Finset.sum_mul, mul_div_mul_comm, smul_sub, ha]
  rw [h_sum]
  exact A.valuation.map_sum_lt one_ne_zero fun i _ ↦ h_term i

/-- A homomorphism `F` from `ℚˣ` to a monoid that is `1` at every prime and not `1` at `-1` is `1`
exactly at the positive rationals. -/
lemma map_eq_one_iff_pos {M : Type*} [Monoid M] (F : ℚˣ →* M)
    (h_prime : ∀ p : ℕ, p.Prime → ∀ h0 : (p : ℚ) ≠ 0, F (Units.mk0 p h0) = 1) (h_neg : F (-1) ≠ 1)
    (x : ℚˣ) :
    F x = 1 ↔ 0 < x.val := by
  -- `F` is `1` at every natural number, by induction on the prime factorisation.
  have h_nat : ∀ (n : ℕ) (h0 : (n : ℚ) ≠ 0), F (Units.mk0 n h0) = 1 :=
    recOnMul nofun (by simp) h_prime (by simp +contextual)
  -- A rational number times its denominator is its sign times a natural number.
  have h_sign : x * .mk0 x.val.den (by simp) =
      (if 0 < x.val then 1 else -1) * .mk0 x.val.num.natAbs (by simp) := by
    aesop (add simp [abs, le_of_lt])
  have h_val : F x = F (if 0 < x.val then 1 else -1) := by
    simpa only [F.map_mul, h_nat, mul_one] using congrArg F h_sign
  simp [h_val, apply_ite F, h_neg]

/-- The tame symbol at the place `v` of an odd prime `q = v.q` of `ℚ`. Let `ξ` be a character of
`Gal(Ω/ℚ)` whose kernel is that of the cyclotomic character modulo `q`, `ζ` a primitive `q`-th root
of unity with `ζ ≡ 1` at `placeOver v`, and `η` a unit there with `((ζ - 1) η) ^ (q - 1) = q`. For
`x ∈ ℚˣ` a unit at `v` equal to the integer `k` and `g ∈ Gal(Ω/ℚ)`, `ξ` of the local Artin symbol
of `x` is `ξ g` exactly when `k` is the cyclotomic character modulo `q` of `g`. -/
lemma abelianLift_artinAt_eq_toHom_iff_of_tame {ξ : QZChar Gal(Ω/ℚ)} {v : FinPlace ℚ}
    [Fact v.q.Prime] (hξ : ker ξ = cycloGalGroup v.q) (hq : 2 < v.q)
    (h_unif : IsUniformiser (placeOver v) (v.q : ℚ)) {ζ η : Ω} (hζ : IsPrimitiveRoot ζ v.q)
    (hζ_cong : (placeOver v).valuation (ζ - 1) < 1) (hη_unit : (placeOver v).valuation η = 1)
    (h_root : ((ζ - 1) * η) ^ (v.q - 1) = algebraMap ℚ Ω v.q) (k : ℤ) (g : Gal(Ω/ℚ)) (x : ℚˣ)
    (hu : v.valuation ℚ x = 1) (hx : x.val = k) :
    abelianLift ξ (artinAt Gal(Ω/ℚ) v (ideleAt v (principalIdele x))) = toHom ξ g ↔
      k = (cyclotomicCharMod Ω v.q g).val := by
  have h_over : IsPlaceOver (placeOver v) v := v.isPlaceOver_placeOver
  have hu_idele : Valued.v (ideleAt v (principalIdele x)).val = 1 :=
    (v_algebraMap_eq_valuation _).trans hu
  -- The symbol of `x` at `v` is the class of an element `s` of the inertia group.
  obtain ⟨s, hs, hs_art⟩ : ∃ s : decompGroup Gal(Ω/ℚ) (placeOver v),
      s.val ∈ inertiaGroup Gal(Ω/ℚ) (placeOver v) ∧
        localArtin Gal(Ω/ℚ) (placeOver v) v (ideleAt v (principalIdele x)) = s :=
    h_over.exists_mem_inertiaGroup_localArtin_eq (Γ := Gal(Ω/ℚ)) hu_idele
  -- With `y = (ζ - 1) * η` and `s • ζ = ζ ^ a`, the quotient `s • y / y` is `≡ k` by the tame
  -- symbol and `≡ a` by direct computation. So `q` divides `k - a`.
  let a : ℕ := (cyclotomicCharMod Ω v.q s.val : ZMod v.q).val
  let y : Ω := (ζ - 1) * η
  have h_k : (placeOver v).valuation (s.val • y / y - algebraMap ℚ Ω k) < 1 := by
    refine (h_over.valuation_sub_lt_one_iff_of_localArtin_eq h_unif hu_idele hs_art h_root
      (x := k)).mp ?_
    -- The side condition says that the component of the idele of `x` at `v` is `k`.
    simp [ideleAt, principalIdele, hx]
  have h_a : (placeOver v).valuation (s.val • y / y - a) < 1 :=
    valuation_smul_div_sub_natCast_lt_one hs (hζ.ne_one hq.le) hζ_cong
      (smul_eq_pow_cyclotomicCharMod s.val hζ.pow_eq_one) hη_unit
  have h_sub_lt : (placeOver v).valuation (algebraMap ℤ Ω (k - a)) < 1 := by
    simpa using map_sub_lt _ h_a h_k
  have h_mem : algebraMap ℤ (𝓞 ℚ) (k - a) ∈ v.asIdeal := (h_over _).mp h_sub_lt
  -- The absolute norm of `v` is `q`, and the norm of the integer `k - a` is `k - a`.
  have h_norm : Algebra.norm ℤ (algebraMap ℤ (𝓞 ℚ) (k - a)) = k - a := by
    rw [Algebra.norm_algebraMap]
    simp [RingOfIntegers.rank]
  have h_dvd : (v.q : ℤ) ∣ k - a := by
    have h_norm_dvd := Ideal.absNorm_dvd_norm_of_mem h_mem
    rw [h_norm] at h_norm_dvd
    simpa using h_norm_dvd
  have h_cyc : (cyclotomicCharMod Ω v.q s.val).val = k := by
    simpa [a] using (intCast_eq_intCast_iff_dvd_sub (a : ℤ) k v.q).mpr h_dvd
  have h_sym : abelianLift ξ (artinAt Gal(Ω/ℚ) v (ideleAt v (principalIdele x))) = toHom ξ s :=
    congrArg (abelianLift ξ) (h_over.artinAt_eq_of_localArtin_eq hs_art)
  calc abelianLift ξ (artinAt Gal(Ω/ℚ) v (ideleAt v (principalIdele x))) = toHom ξ g
        ↔ toHom ξ s = toHom ξ g := by rw [h_sym]
    _ ↔ cyclotomicCharMod Ω v.q s.val = cyclotomicCharMod Ω v.q g := by
        rw [(toHom ξ).eq_iff, ← ker, hξ, ← MonoidHom.eq_iff]
    _ ↔ k = (cyclotomicCharMod Ω v.q g).val := by rw [Units.ext_iff, h_cyc]

/-- Artin's law for `K(μ_q)`, `q` an odd prime. Some character `χ` (a) has the same kernel as the
cyclotomic character modulo `q`, and (b) kills the Artin symbol of the finite idele of `x ∈ Kˣ`
exactly when the norm of `x` to `ℚ` is positive. The norm carries the law down to `ℚ`, where `-1`
and the primes generate: `q = N (ζ - 1)`, and a unit at `q` multiplies `ζ - 1` by its residue. -/
lemma artin_reciprocity_cyclotomic {q : ℕ} [P : Fact q.Prime] (hq : Fact (2 < q)) :
    ∃ χ : QZChar Γ,
      ker χ = (cyclotomicCharMod Ω q).ker ∧
      ∀ x : Kˣ, abelianLift χ (artinMap Γ (principalIdele x)) = 1 ↔ 0 < Algebra.norm ℚ x.val := by
  classical
  -- We prove the law for `ℚ` and a character `ξ` of `Gal(Ω/ℚ)`, then pull `ξ` back to `Γ`.
  obtain ⟨ξ, hξ⟩ : ∃ ξ : QZChar Gal(Ω/ℚ), ker ξ = cycloGalGroup q :=
    exists_ker_eq_of_isCyclic ⟨cycloGalGroup q, isOpen_ker_cyclotomicCharMod.out⟩
      (isCyclic_of_injective _ (QuotientGroup.kerLift_injective _))
  -- `v` is the place of `q`: `q` is a uniformiser at `v` and a unit at the other places.
  obtain ⟨v, ⟨rfl, hq_unit⟩, hq_val, -⟩ := exists_rat_place_of_prime P.out
  have h_over (w : FinPlace ℚ) : IsPlaceOver (placeOver w) w := w.isPlaceOver_placeOver
  have h_frob (w : FinPlace ℚ) : ∃ σ : Gal(Ω/ℚ), IsFrob (placeOver w) w.q σ :=
    (h_over w).exists_isFrob Gal(Ω/ℚ)
  choose σ hσ using h_frob
  -- `F x` and `Floc w x` are the values of `ξ` on the global symbol and on the symbol at `w`.
  let F : ℚˣ →* Multiplicative QZ := (abelianLift ξ).comp ((artinMap _).comp principalIdele)
  let Floc (w : FinPlace ℚ) (x : ℚˣ) : Multiplicative QZ :=
    abelianLift ξ (artinAt _ w (ideleAt w (principalIdele x)))
  -- From here on `q` is `v.q`. At a place `A` over `v` one has `(ζ - 1) ^ (q - 1) * ε = q` with a
  -- unit `ε`. For a `(q - 1)`-th root `η` of `ε`, `(ζ - 1) * η` is a `(q - 1)`-th root of `q`.
  let A : ClosurePlace := placeOver v
  have h_unif : IsUniformiser A (v.q : ℚ) := (h_over v).isUniformiser_iff.mpr hq_val
  have h_pos : 0 < v.q - 1 := tsub_pos_of_lt P.out.one_lt
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Ω, IsPrimitiveRoot ζ v.q := HasEnoughRootsOfUnity.prim
  obtain ⟨ε, hε⟩ : ∃ ε : Aˣ, (ζ - 1) ^ (v.q - 1) * ε = v.q := by
    have h_lift_eq : algebraMap (𝓞 Ω) Ω hζ.toInteger = ζ := hζ.coe_toInteger
    simpa [Associated, Subtype.ext_iff, h_lift_eq] using
      (Rat.associated_zeta_sub_one_pow_prime _ hζ).map
      ((algebraMap (𝓞 Ω) Ω).codRestrict A (algebraMap_ringOfIntegers_mem A))
  obtain ⟨η, hη⟩ : ∃ η : Ω, η ^ (v.q - 1) = ε := exists_pow_nat_eq (ε : Ω) h_pos
  have hη_unit : A.valuation η = 1 := by simpa [h_pos.ne', ← hη] using A.valuation_unit ε
  have h_root : ((ζ - 1) * η) ^ (v.q - 1) = algebraMap ℚ Ω v.q := by simp [mul_pow, hη, hε]
  have hζ_cong : A.valuation (ζ - 1) < 1 := by
    simpa [← hε, pow_lt_one_iff h_pos.ne'] using
      (mod_cast h_unif.valuationVia_lt_one : A.valuation v.q < 1)
  -- The symbol at `v` of an integer `k` that is a unit at `v` acts on `ζ` as the power `k`.
  have h_tame (k : ℤ) (g : Gal(Ω/ℚ)) (x : ℚˣ) (hu : v.valuation ℚ x = 1) (hx : x.val = k) :
      Floc v x = toHom ξ g ↔ k = (cyclotomicCharMod Ω v.q g).val :=
    abelianLift_artinAt_eq_toHom_iff_of_tame hξ hq.out h_unif hζ hζ_cong hη_unit h_root k g x hu hx
  -- At the places `w ≠ v` the character `ξ` is unramified.
  have hq_val' (w : FinPlace ℚ) (hw : w ≠ v) : (placeOver w).valuation v.q = 1 :=
    (h_over w).valuationVia_eq_one_iff.mpr (hq_unit w hw)
  have h_unr (w : FinPlace ℚ) (hw : w ≠ v) (x : ℚˣ) :
      Floc w x = .ofAdd ((w.valuation ℚ x).log • ξ.val (σ w)) :=
    (h_over w).abelianLift_artinAt_of_inertiaGroup_le_ker ξ
      (fun g hg ↦ hξ.ge (cyclotomicCharMod_eq_one_of_mem_inertiaGroup hg (hq_val' w hw))) (hσ w) x
  -- So if `x` is a unit away from `w`, only `v` and `w` contribute to the global symbol.
  have h_two (w : FinPlace ℚ) (x : ℚˣ) (hx : ∀ u ≠ w, u.valuation ℚ x = 1) :
      F x = ∏ u ∈ {v, w}, Floc u x := by
    have h_support : Function.mulSupport (fun u ↦ Floc u x) ⊆ ({v, w} : Finset (FinPlace ℚ)) := by
      simp +contextual [subset_def, not_imp_comm, h_unr, hx]
    exact (abelianLift_artinMap_eq_finprod ξ (principalIdele x)).trans
      (finprod_eq_prod_of_mulSupport_subset (fun u ↦ Floc u x) h_support)
  have h_prime (p : ℕ) (hp : p.Prime) (h0 : (p : ℚ) ≠ 0) : F (.mk0 p h0) = 1 := by
    obtain ⟨w, ⟨rfl, hp_unit⟩, hp_val, -⟩ := exists_rat_place_of_prime hp
    rw [h_two w (.mk0 _ h0) hp_unit]
    obtain rfl | hw := eq_or_ne w v
    · -- `q` is the norm of `ζ - 1` from the field cut out by `ξ`, so its symbol vanishes.
      obtain ⟨z, hz⟩ : ∃ z : fixedFieldOf (K := ℚ) (Ω := Ω) (ker ξ), norm ℚ z = w.q := by
        rw [hξ]
        exact ⟨_,
          norm_zeta_sub_one_of_prime_ne_two _ (cyclotomic.irreducible_rat hp.pos) hq.out.ne'⟩
      simpa using abelianLift_artinAt_eq_one_of_mem_closure (subset_closure ⟨z, congrArg _ hz⟩)
    · -- For `p ≠ q` the symbol at `v` is `ξ` of a Frobenius at `p`, that at `w` its inverse.
      have h_cyc : (w.q : ℤ) = (cyclotomicCharMod Ω v.q (σ w)).val := by
        simp [(hσ w).cyclotomicCharMod_eq (hq_val' w hw)]
      have h_v : Floc v (.mk0 _ h0) = .ofAdd (ξ.val (σ w)) :=
        (h_tame w.q _ _ (hp_unit v hw.symm) rfl).mpr h_cyc
      simp [Finset.prod_pair hw.symm, h_v, h_unr w hw, hp_val]
  -- The symbol of `-1` acts on `ζ` as the power `-1`, which is not `1` as `2 < q`.
  have h_neg : F (-1) ≠ 1 := by
    simpa [h_two v, neg_one_ne_one] using h_tame (-1) 1 (-1) (by simp) rfl
  -- The Artin symbol of `x` over `K` restricts to that of its norm over `ℚ`.
  let res : Γ →ₜ* Gal(Ω/ℚ) := ⟨toAlgAut Γ ℚ Ω, continuous_of_equivariant_emb 1 fun _ _ ↦ rfl⟩
  refine ⟨comap res ξ, congrArg (Subgroup.comap res.toMonoidHom) hξ, fun x ↦ ?_⟩
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (artinMap Γ (principalIdele x))
  have h_res : artinMap Gal(Ω/ℚ) (principalIdele (x.map (norm ℚ))) = res g := by
    rw [← map_adeleNorm_principalIdele]
    exact artinMap_map_adeleNorm hg.symm 1 (by simp) fun _ ↦ rfl
  have h_law : F (x.map (norm ℚ)) = 1 ↔ 0 < (x.map (norm ℚ)).val :=
    map_eq_one_iff_pos F h_prime h_neg (x.map (norm ℚ))
  have h_comap : (comap res ξ).val g = ξ.val (res g) := rfl
  simpa [F, h_res, ← hg, h_comap] using h_law

/-! ### The law in general -/

lemma abelianLift_add_eq_mul (χ ψ : QZChar Γ) :
    abelianLift (χ + ψ) = abelianLift χ * abelianLift ψ := by
  aesop

omit [MulSemiringAction Γ Ω] in
lemma QZChar.apply_pow (χ : QZChar Γ) (g : Γ) (n : ℕ) : χ.val (g ^ n) = n • χ.val g := by
  apply Multiplicative.ofAdd.injective
  simpa only [ofAdd_nsmul, toHom_apply] using map_pow (toHom χ) g n

/-- For a prime `l` and `a > 1` there is a prime `p > 2`, not dividing `a`, such that `l` divides
the order of `a` modulo `p`. -/
lemma exists_prime_dvd_orderOf {l a : ℕ} (hl : l.Prime) (ha : 1 < a) :
    ∃ p : ℕ, p.Prime ∧ 2 < p ∧ IsUnit (a : ZMod p) ∧ l ∣ orderOf (a : ZMod p) := by
  -- Take a prime factor `p` of the cyclotomic value `Φ_N (a)`, where `N = l (l + 1)`.
  let N : ℕ := l * (l + 1)
  have hN : 1 < N := one_lt_mul'' hl.one_lt (by simp [hl.pos])
  have hN_ne : N ≠ 0 := hN.ne_bot
  have h_eval_gt : a - 1 < ((cyclotomic N ℤ).eval ↑a).natAbs :=
    sub_one_lt_natAbs_cyclotomic_eval hN ha.ne'
  obtain ⟨p, hp, hp_dvd⟩ := exists_prime_and_dvd (n := ((cyclotomic N ℤ).eval ↑a).natAbs) (by omega)
  have : Fact p.Prime := ⟨hp⟩
  -- Modulo `p` the order of `a` is the part `m` of `N` prime to `p`; in particular `m < p`.
  let m : ℕ := ordCompl[p] N
  have m_pos : 0 < m := ordCompl_pos p hN_ne
  have : NeZero (↑m : ZMod p) := .of_not_dvd (ZMod p) (not_dvd_ordCompl hp hN_ne)
  have h_root : (cyclotomic (p ^ N.factorization p * m) (ZMod p)).IsRoot (a : ℤ) := by
    refine (cyclotomic.eval_apply (a : ℤ) _ (algebraMap ℤ (ZMod p))).trans <| ?_
    rwa [eq_intCast, intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd, ordProj_mul_ordCompl_eq_self]
  have h_prim : IsPrimitiveRoot (a : ZMod p) m := isRoot_cyclotomic_prime_pow_mul_iff_of_charP.mp
    (mod_cast h_root)
  have m_lt : m < p := h_prim.eq_orderOf.trans_lt (orderOf_lt hp.one_lt _)
  -- If `p` divided `l`, then `l + 1` would divide `m`, and `l < m < p ≤ l`.
  have h_not_dvd : ¬p ∣ l := fun hpl ↦ by
    have h_succ : l + 1 ∣ m := dvd_ordCompl_of_dvd_not_dvd (dvd_mul_left (l + 1) l) fun h ↦ by
      simpa [hp.ne_one] using dvd_sub h hpl
    linarith [le_of_dvd m_pos h_succ, le_of_dvd hl.pos hpl]
  have h_dvd : l ∣ m := dvd_ordCompl_of_dvd_not_dvd (dvd_mul_right l (l + 1)) h_not_dvd
  have hp_two_lt : 2 < p := (hl.two_le.trans (le_of_dvd m_pos h_dvd)).trans_lt m_lt
  exact ⟨p, hp, hp_two_lt, h_prim.isUnit m_pos.ne', by rwa [← h_prim.eq_orderOf]⟩

/-- Artin's lemma: for a Frobenius `σ` at a place `A` of `Ω` over the finite place `v` of `K` (`v.q`
the size of its residue field), a prime `l` and `m ≠ 0`, some character `χ` that satisfies the
reciprocity law has `m • χ σ` of order not prime to `l`. -/
lemma exists_reciprocity_character {A : ClosurePlace} {v : FinPlace K} (hA : IsPlaceOver A v)
    {σ : Γ} (hσ : IsFrob A v.q σ) {l m : ℕ} (hl : l.Prime) (hm : m ≠ 0) :
    ∃ χ : QZChar Γ,
      (∀ y : Kˣ, abelianLift χ (artinMap Γ (principalIdele y)) = 1) ∧
      ∀ a : ℕ, l.Coprime a → a • m • χ.val σ ≠ 0 := by
  obtain ⟨p, hp, hp_odd, h_isUnit, h_order⟩ :=
    exists_prime_dvd_orderOf hl (one_lt_pow (n := 2 * m) (by simpa) v.one_lt_q)
  have : Fact p.Prime := ⟨hp⟩
  -- Twice the character `χ` that cuts out the `p`-th roots of unity satisfies the law: its value
  -- on the symbol of `y` is that of `χ` on the symbol of `y * y`, whose norm is positive.
  obtain ⟨χ, h_ker, h_sign⟩ := artin_reciprocity_cyclotomic (Γ := Γ) (K := K) (q := p) ⟨hp_odd⟩
  have h_law (y : Kˣ) : abelianLift (χ + χ) (artinMap Γ (principalIdele y)) = 1 := by
    simpa [abelianLift_add_eq_mul] using h_sign (y * y)
  refine ⟨χ + χ, h_law, fun a ha h0 ↦ ?_⟩
  -- `σ` raises these roots to the power `v.q`, so the order of `v.q ^ (2 * m)` modulo `p`, and
  -- with it `l`, would divide `a`.
  have h_unit : A.valuation p = 1 :=
    ((isUnit_iff_coprime _ p).mp (by simpa [hm] using h_isUnit)).valuation_eq_one
      hA.valuation_q_lt_one
  have h_mem : (σ ^ (2 * m)) ^ a ∈ ker χ := by
    rw [MonoidHom.mem_ker, QZChar.toHom_apply, ofAdd_eq_one]
    simpa [QZChar.apply_pow, mul_nsmul', two_nsmul] using h0
  have h_pow : ((v.q ^ (2 * m) : ℕ) : ZMod p) ^ a = 1 := by
    simpa [Units.ext_iff, hσ.cyclotomicCharMod_eq h_unit] using h_ker.le h_mem
  exact hl.coprime_iff_not_dvd.mp ha (h_order.trans (orderOf_dvd_of_pow_eq_one h_pow))

/-- The local symbol `χ (Art_v x)` is trivial at almost all places: there `χ` is unramified and `x`
is a unit. -/
lemma finite_mulSupport_abelianLift_artinAt (χ : QZChar Γ) (x : Kˣ) :
    (Function.mulSupport fun v : FinPlace K ↦
      abelianLift χ (artinAt Γ v (ideleAt v (principalIdele x)))).Finite := by
  have h_unr : ∀ᶠ v : FinPlace K in .cofinite, inertiaGroup Γ (placeOver v) ≤ ker χ :=
    (finite_ramified (isOpen_ker χ)).mono fun v hv ↦ hv _ (FinPlace.isPlaceOver_placeOver v)
  exact (h_unr.and (finite_setOf_valued_val_ne_one (principalIdele x))).mono fun v hv ↦
    ((FinPlace.isPlaceOver_placeOver v).artinAt_units_trivial_iff_inertiaGroup_le χ).mpr hv.left _
      hv.right

/-- Let `c` be an element of an additive monoid whose order divides `i`. If, for every prime
`l ∣ n`, no `a • n • c` with `a` prime to `l` vanishes, then `n ∣ i`. -/
lemma _root_.dvd_of_addOrderOf_dvd_of_forall_nsmul_ne_zero {M : Type*} [AddMonoid M] {c : M}
    {n i : ℕ} (h_ord : addOrderOf c ∣ i)
    (h : ∀ l : ℕ, l.Prime → l ∣ n → ¬∃ a : ℕ, l.Coprime a ∧ a • n • c = 0) :
    n ∣ i := by
  -- Otherwise `n = b g` and `i = a g` with `a`, `b` coprime and `b ≠ 1`; take a prime factor `l` of
  -- `b`. Then `a` is prime to `l`, and `a • n • c = (a b g) • c = b • (i • c) = 0`.
  obtain ⟨b, a, h_coprime, hn_eq, hi_eq⟩ := n.exists_coprime i
  by_contra h_not
  have hb_ne_one : b ≠ 1 := fun h_one ↦ h_not (hn_eq.dvd.trans (by simp [h_one, Nat.gcd_dvd_right]))
  obtain ⟨l, hl, hlb⟩ := exists_prime_and_dvd hb_ne_one
  refine h l hl (hlb.trans ⟨_, hn_eq⟩) ⟨a, h_coprime.of_dvd_left hlb, ?_⟩
  rw [smul_smul, ← addOrderOf_dvd_iff_nsmul_eq_zero]
  exact h_ord.trans (hi_eq.dvd.trans (mul_dvd_mul_left a (Nat.gcd_dvd_left n i)))

/-- The local step of Artin's reciprocity law. Let `σ v` be a Frobenius at each place `v` of `K`,
and let `n v` be the order of `ξ` at the local Artin symbol of `x` at `v`. Let the symbol `(ξ, x)`
die on an open subgroup `U` that contains the complex conjugations, and let `χ` be a character such
that, for each `v` and each prime `l ∣ n v`, no `a • n v • χ (σ v)` with `a` prime to `l` vanishes.
Then `(ξ, x)` dies on the kernel of `χ`. -/
lemma resH2_ker_cyclicClass_eq_zero {ξ χ : QZChar Γ} {x : Kˣ} (U : OpenSubgroup Γ)
    (hU : ∀ g : Γ, IsComplexConj g → g ∈ U)
    (h_res : (unitsModule Γ).resH2 U
      (cyclicClass (unitsModule Γ).ρ ξ (DiscreteUnits.ofBase Γ Ω (.ofMul x))) = 0)
    {σ : FinPlace K → Γ} (hσ : ∀ v : FinPlace K, IsFrob (placeOver v) v.q (σ v))
    (hχ : ∀ (v : FinPlace K) (l : ℕ), l.Prime →
      l ∣ orderOf (abelianLift ξ (artinAt Γ v (ideleAt v (principalIdele x)))) →
      ¬∃ a : ℕ, l.Coprime a ∧
        a • orderOf (abelianLift ξ (artinAt Γ v (ideleAt v (principalIdele x)))) •
          χ.val (σ v) = 0) :
    (unitsModule Γ).resH2 (⟨ker χ, isOpen_ker χ⟩ : OpenSubgroup Γ)
      (cyclicClass (unitsModule Γ).ρ ξ (DiscreteUnits.ofBase Γ Ω (.ofMul x))) = 0 := by
  -- Apply `albert_brauer_hasse_noether` over the fixed field of `ker χ`: the class dies locally,
  -- as the local degree at each `v` is divisible by `n v`.
  let s (v : FinPlace K) : Multiplicative QZ :=
    abelianLift ξ (artinAt Γ v (ideleAt v (principalIdele x)))
  refine albert_brauer_hasse_noether _ (fun {A w} hw ↦ ?_)
    (U.comap _ (subgroupIncl _).continuous_toFun) (fun g ↦ hU g)
    (DiscreteModule.resH2_subgroupOf_eq_zero_symm (congrArg _ h_res) :)
  let v : FinPlace K := w.below K
  have hv : IsPlaceOver A v := hw.isPlaceOver_below
  let V : OpenSubgroup (decompGroup Γ A) := ⟨_, isOpen_ker (comap (subgroupIncl _) χ)⟩
  -- The group `χ (decompGroup Γ A)` depends on `v` only, being the range of `χ` on the local
  -- symbols, and so contains `χ (σ v)`. Its order is the index of `V`.
  have h_frob_mem : toHom χ (σ v) ∈ (decompGroup Γ A).map (toHom χ) :=
    (hv.range_abelianLift_comp_artinAt _).le
      ((v.isPlaceOver_placeOver.range_abelianLift_comp_artinAt _).ge ⟨_, (hσ v).left, rfl⟩)
  have h_frob : orderOf (toHom χ (σ v)) ∣ V.toSubgroup.index :=
    (orderOf_dvd_natCard _ h_frob_mem).trans (relIndex_ker ..).symm.dvd
  have h_dvd : orderOf (s v) ∣ V.toSubgroup.index :=
    dvd_of_addOrderOf_dvd_of_forall_nsmul_ne_zero (by rwa [← orderOf_ofAdd_eq_addOrderOf]) (hχ v)
  -- Restriction to `V` multiplies the local invariant, of order `n v`, by the index of `V`.
  have hr : V.toSubgroup.index • (s v).toAdd = 0 := addOrderOf_dvd_iff_nsmul_eq_zero.mp h_dvd
  have h_cls :
      (unitsModule (decompGroup Γ A)).resH2 V
        (classOfInvariant _ (fixedFieldOf (K := K) (decompGroup Γ A)) A (s v).toAdd) = 0 :=
    (hv.isLocalGalois_and_residueCard_eq_and_isUniformiser Γ).left.resH2_classOfInvariant_eq_zero V
      hr
  -- The restricted class lives in `restrictTo` of the module, which is
  -- `unitsModule (decompGroup Γ A)` only after unfolding, hence `erw`.
  erw [hv.abelianLift_artinAt_principal, _root_.map_neg, neg_eq_zero] at h_cls
  exact (unitsModule ..).resH2_subgroupOf_eq_zero_symm (V := decompGroup ..) h_cls

/-- `Ω` is an algebraic closure of `ℚ`, on which `Γ` acts as the Galois group of `Ω/K`.
If the symbols `(ξ, x)` and `(χ, y)` are equal in `H²(Γ, Ωˣ)`, then `ξ` at the local Artin
symbol of `x` equals `χ` at that of `y`, at every place `v`: both are minus the local invariant of
the symbol, and the local invariant map is injective. -/
lemma abelianLift_artinAt_eq_of_cyclicClass_eq {ξ χ : QZChar Γ} {x y : Kˣ}
    (h_eq : cyclicClass (unitsModule Γ).ρ ξ (DiscreteUnits.ofBase Γ Ω (.ofMul x)) =
      cyclicClass (unitsModule Γ).ρ χ (DiscreteUnits.ofBase Γ Ω (.ofMul y)))
    (v : FinPlace K) :
    abelianLift ξ (artinAt Γ v (ideleAt v (principalIdele x))) =
      abelianLift χ (artinAt Γ v (ideleAt v (principalIdele y))) := by
  -- The value of a character at a local symbol is minus the local invariant of the symbol.
  have h_inv (ψ : QZChar Γ) (z : Kˣ) :
      classOfInvariant (decompGroup Γ (placeOver v))
          (fixedFieldOf (K := K) (decompGroup Γ (placeOver v))) (placeOver v)
          (abelianLift ψ (artinAt Γ v (ideleAt v (principalIdele z)))).toAdd =
        -(unitsModule Γ).resH2 (decompGroup Γ (placeOver v))
          (cyclicClass (unitsModule Γ).ρ ψ (DiscreteUnits.ofBase Γ Ω (.ofMul z))) :=
    v.isPlaceOver_placeOver.abelianLift_artinAt_principal (Γ := Γ) ψ z
  apply Multiplicative.toAdd.injective
  apply (v.isPlaceOver_placeOver.isLocalGalois_and_residueCard_eq_and_isUniformiser
    Γ).left.isClassOfInvariant_classOfInvariant.left
  rw [h_inv, h_inv, h_eq]

/-- The characters `χ : Γ → ℚ/ℤ` that satisfy the reciprocity law over `K`: `χ` kills the Artin
symbol of the finite idele of every `y ∈ Kˣ`. -/
private noncomputable def reciprocityChars (K : Type) [Field K] [EmbeddedNumberField K]
    [IsProGalois Γ K Ω] : AddSubgroup (QZChar Γ) :=
  ⨅ y : Kˣ, AddMonoidHom.ker
    (.mk' (fun χ : QZChar Γ ↦ (abelianLift χ (artinMap Γ (principalIdele y))).toAdd)
      fun χ ψ ↦ by simp [abelianLift_add_eq_mul])

/-- For `g : Γ` and `n l : ℕ`, the characters `χ` for which `n • χ g` has order prime to `l`: some
`a` prime to `l` has `a • n • χ g = 0`. -/
private noncomputable def QZChar.coprimeOrderSubgroup (g : Γ) (n l : ℕ) : AddSubgroup (QZChar Γ) :=
  let primeToL : Submonoid ℕ :=
    { carrier := l.Coprime, mul_mem' := .mul_right, one_mem' := l.gcd_one_right }
  (Submodule.torsion' ℤ QZ primeToL).toAddSubgroup.comap
    (.mk' (fun χ : QZChar Γ ↦ n • χ.val g) (by simp))

/-- Artin's reciprocity law for the number field `K`, with `Ω` an algebraic closure of `ℚ` and
`Γ` the Galois group of `Ω/K`. If the symbol `(ξ, x) = δξ ∪ x ∈ H²(Γ, Ωˣ)` restricts to zero on an
open subgroup `U` that contains the complex conjugations, then `ξ` kills the Artin symbol of the
finite idele of `x`. -/
lemma artin_reciprocity {ξ : QZChar Γ} {x : Kˣ} (U : OpenSubgroup Γ)
    (hU : ∀ g : Γ, IsComplexConj g → g ∈ U)
    (h_res : (unitsModule Γ).resH2 U
      (cyclicClass (unitsModule Γ).ρ ξ (DiscreteUnits.ofBase Γ Ω (.ofMul x))) = 0) :
    abelianLift ξ (artinMap Γ (principalIdele x)) = 1 := by
  -- Artin's lemma and a covering argument give a character `χ` that satisfies the law; then
  -- `(ξ, x)` dies on `ker χ` and is a symbol `(χ, y)` with the same local symbols, of product `1`.
  set α : H2 (unitsModule Γ).ρ :=
    cyclicClass (unitsModule Γ).ρ ξ (DiscreteUnits.ofBase Γ Ω (.ofMul x))
  have h_frob_exists (v : FinPlace K) : ∃ σ : Γ, IsFrob (placeOver v) v.q σ :=
    v.isPlaceOver_placeOver.exists_isFrob Γ
  choose σ hσ using h_frob_exists
  -- The local symbol `s v` is minus the local invariant of `α` (`abelianLift_artinAt_principal`).
  let s (v : FinPlace K) : Multiplicative QZ :=
    abelianLift ξ (artinAt Γ v (ideleAt v (principalIdele x)))
  let n (v : FinPlace K) : ℕ := orderOf (s v)
  have hn (v : FinPlace K) : n v ≠ 0 := (isAddTorsion (s v).toAdd).addOrderOf_pos.ne'
  have h_fin : (Function.mulSupport s).Finite := finite_mulSupport_abelianLift_artinAt ξ x
  let G : AddSubgroup (QZChar Γ) := reciprocityChars K
  have mem_G (χ : QZChar Γ) : χ ∈ G ↔ ∀ y : Kˣ, abelianLift χ (artinMap Γ (principalIdele y)) = 1 :=
    AddSubgroup.mem_iInf
  let H (i : Σ _ : FinPlace K, ℕ) : AddSubgroup G :=
    (QZChar.coprimeOrderSubgroup (σ i.fst) (n i.fst) i.snd).addSubgroupOf G
  have mem_H (v : FinPlace K) (l : ℕ) (χ : G) :
      χ ∈ H ⟨v, l⟩ ↔ ∃ a : ℕ, l.Coprime a ∧ a • n v • ((χ : QZChar Γ) : Γ → QZ) (σ v) = 0 :=
    ⟨fun ⟨a, ha⟩ ↦ ⟨a.val, a.prop, ha⟩, fun ⟨a, ha, h0⟩ ↦ ⟨⟨a, ha⟩, h0⟩⟩
  -- By Artin's lemma these subgroups have infinite index.
  have h_index (v : FinPlace K) (l : ℕ) (hl : l.Prime) : (H ⟨v, l⟩).index = 0 := by
    by_contra h0
    obtain ⟨χ, hχ, h_ne⟩ :=
      exists_reciprocity_character v.isPlaceOver_placeOver (hσ v) hl (mul_ne_zero (hn v) h0)
    -- A multiple of `χ` by the index lies in `H ⟨v, l⟩`, which contradicts Artin's lemma.
    obtain ⟨a, ha, h_zero⟩ :=
      (mem_H v l _).mp ((H ⟨v, l⟩).nsmul_index_mem (⟨χ, (mem_G χ).mpr hχ⟩ : G))
    have h_zero' : a • (n v * (H ⟨v, l⟩).index) • χ.val (σ v) = 0 := by
      simpa [mul_smul] using h_zero
    exact h_ne a ha h_zero'
  -- Finitely many subgroups of infinite index do not cover `G`.
  obtain ⟨χ, hχ⟩ : ∃ χ : G, ∀ (v : FinPlace K) (l : ℕ), l.Prime → l ∣ n v → χ ∉ H ⟨v, l⟩ := by
    by_contra! h_cover
    -- Otherwise the `H ⟨v, l⟩` with `s v ≠ 1` and `l` a prime factor of `n v` cover `G`.
    let S : Finset (Σ _ : FinPlace K, ℕ) := h_fin.toFinset.sigma fun v ↦ (n v).primeFactors
    open Pointwise in
    have h_covers : ⋃ i ∈ S, (0 : (Σ _ : FinPlace K, ℕ) → G) i +ᵥ (H i : Set G) = univ := by
      refine eq_univ_of_forall fun χ ↦ ?_
      obtain ⟨v, l, hl, hln, hχ_mem⟩ := h_cover χ
      have hv : s v ≠ 1 := fun h_one ↦ by simp [n, h_one, hl.ne_one] at hln
      exact mem_iUnion₂.mpr ⟨⟨v, l⟩, by simp [S, hv, hl, hln, hn v], by simpa using hχ_mem⟩
    obtain ⟨⟨v, l⟩, hl, ⟨h_ne⟩⟩ :=
      AddSubgroup.exists_finiteIndex_of_leftCoset_cover (H := H) (g := 0) (s := S) h_covers
    exact h_ne (h_index v l (Nat.prime_of_mem_primeFactors (Finset.mem_sigma.mp hl).right))
  -- The symbol dies on `ker χ`, as `χ` lies in no `H ⟨v, l⟩` with `l ∣ n v`.
  have h_ker : (unitsModule Γ).resH2 (⟨ker χ.val, isOpen_ker χ.val⟩ : OpenSubgroup Γ) α = 0 :=
    resH2_ker_cyclicClass_eq_zero U hU h_res hσ
      fun v l hl hln h_ex ↦ hχ v l hl hln ((mem_H v l χ).mpr h_ex)
  -- So `α = (χ, y)`, whose local symbols are those of `(ξ, x)`.
  obtain ⟨y, hy⟩ : ∃ y : Kˣ, α = cyclicClass _ χ.val (DiscreteUnits.ofBase Γ Ω (.ofMul y)) :=
    ((cyclicClass_spec χ.val).left α).mp h_ker
  calc abelianLift ξ (artinMap Γ (principalIdele x))
      = ∏ᶠ v, s v := abelianLift_artinMap_eq_finprod ξ (principalIdele x)
    _ = ∏ᶠ v, abelianLift χ.val (artinAt Γ v (ideleAt v (principalIdele y))) :=
        finprod_congr (abelianLift_artinAt_eq_of_cyclicClass_eq hy)
    _ = abelianLift χ.val (artinMap Γ (principalIdele y)) :=
        (abelianLift_artinMap_eq_finprod χ.val (principalIdele y)).symm
    _ = 1 := (mem_G χ.val).mp χ.prop y

/-- Artin reciprocity: if χ kills all complex conjugations, then χ kills the Artin image of the
principal finite idele of every x ∈ K^×, whatever the signs of x at the real places. -/
lemma abelianLift_artinMap_principalIdele_eq_one (χ : ↥(QZChar Γ)) (x : Kˣ)
    (h : ∀ c : Γ, IsComplexConj c → χ.val c = 0) :
    abelianLift χ (artinMap Γ (principalIdele x)) = 1 :=
  -- The symbol `(χ, x)` dies on the kernel of `χ`, which contains the complex conjugations.
  artin_reciprocity ⟨_, isOpen_ker χ⟩ h (((cyclicClass_spec χ).left _).mpr ⟨x, rfl⟩)

/-- If `x ∈ Kˣ` is totally positive, the Artin symbol `artinMap Γ (principalIdele x)` of its finite
idele is trivial.

This is a case of Artin's global reciprocity law (triviality on principal ideles), for totally
positive elements and the map on finite ideles. -/
lemma artinMap_principalIdele_eq_one_of_isTotallyPositive {x : Kˣ} (h : IsTotallyPositive x.val) :
    artinMap Γ (principalIdele x) = 1 := by
  refine abelianization_ext fun χ ↦ ?_
  obtain ⟨U, hU, h_res⟩ := h.exists_resH2_cyclicClass_eq_zero (χ := χ)
  simpa using artin_reciprocity U hU h_res

/-- Sign law: let `χ` be a character of `Γ` that is nonzero on every complex conjugation. Then for
`b ∈ Kˣ`, `χ` kills the Artin symbol of `b` exactly when the norm of `b` to `ℚ` is positive.

This is a consequence of the global Artin reciprocity law; it describes `χ ∘ artinMap` only on
principal finite ideles and only for characters nonzero on every complex conjugation. -/
lemma abelianLift_artinMap_principalIdele_eq_one_iff {χ : ↥(QZChar Γ)}
    (h : ∀ c : Γ, IsComplexConj c → χ.val c ≠ 0) (b : Kˣ) :
    abelianLift χ (artinMap Γ (principalIdele b)) = 1 ↔ 0 < Algebra.norm ℚ b.val := by
  -- `χ` and the character `ξ` of the cube roots of unity agree on complex conjugations, so the law
  -- applies to `χ - ξ`.
  obtain ⟨ξ, h_ker, h_sign⟩ := artin_reciprocity_cyclotomic (Γ := Γ) (K := K) (q := 3) ⟨by simp⟩
  have h_diff (c : Γ) (hc : IsComplexConj c) : (χ - ξ).val c = 0 := by
    -- As `c² = 1`, a nonzero value at `c` is the element of order 2.
    have h_half (ψ : QZChar Γ) (hψ : ψ.val c ≠ 0) : ψ.val c = ofZMod 2 1 := by
      have h_two : 2 • ψ.val c = 0 := (two_nsmul _).trans (map_mul_eq_one (toHom ψ) hc.mul_self)
      rcases Fin.exists_fin_two.mp (exists_ofZMod h_two) with h_zero | h_one
      · exact absurd (h_zero.symm.trans (map_zero _)) hψ
      · exact h_one.symm
    -- `c` raises the cube roots of unity to the power `-1 ≠ 1`.
    have hξ : ξ.val c ≠ 0 := fun h0 ↦
      absurd (hc.cyclotomicCharMod_eq_neg_one.symm.trans (h_ker.le h0)) (by decide)
    simp [h_half χ (h c hc), h_half ξ hξ]
  rw [← sub_add_cancel χ ξ, abelianLift_add_eq_mul]
  simp [abelianLift_artinMap_principalIdele_eq_one (χ - ξ) b h_diff, h_sign]

end New
