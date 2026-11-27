import Lib.PadicComparison.Descent.TestCovers

/-!
# Perfect algebras, étale algebras over perfect rings, and constant Laurent polynomials

Fix a prime p (the class `ThePrime p`). An algebra is perfect when x ↦ x^p is bijective; for hp :
p = 0, `frobPow hp 1` is this map x ↦ x^p as a ring endomorphism, and O♭ denotes the tilt of the
ring of integers of ℂ_p. The file constructs perfections of quotients and perfected blow-up charts,
and it shows that étale algebras lift along surjections and are perfect over a perfect base in which
p = 0. It also proves that a Laurent polynomial that is a polynomial both in T and in T⁻¹ is
constant.

## Main definitions and results

* `New.Variety.perfectRing_monoidAlgebra`: O♭[G] is perfect when G is a module over the non-negative
  rationals.
* `New.Variety.PerfectAlg.isClosedUnderColimitsOfShape_widePushoutShape`,
  `New.Variety.perfectRing_tensor`: if p = 0 in S, perfect S-algebras are closed under wide
  pushouts, so, for perfect S, under tensor products.
* `New.Variety.exists_perfection_quotient`: the perfection of B/t, for p = 0 in the base.
* `New.Variety.exists_perfect_blowup_charts`: for f, g in a perfect algebra B over a perfect ring
  with p = 0, perfected charts B₁ (where g ∣ f) and B₂ (where f ∣ g) form an exact sequence
  B → B₁ × B₂ → B₀ → 0; the proof splits Laurent polynomials by
  `New.Variety.surjective_toLaurent_add_invert`.
* `New.Variety.exists_etale_lift`: an étale algebra over a quotient of C lifts to an étale algebra
  over C.
* `New.Variety.perfectRing_of_etale`: an étale algebra over a perfect ring in which p = 0 is
  perfect.

Notions from other files:
* `New.Variety.PadicTest.tilt`: The functor from p-adic tests to commutative O^♭-algebras sending a
  test S to its tilt S^♭.

## Relation to the literature

Known; see `Lib.PadicComparison.Descent.AlmostDescent` for sources.
-/

noncomputable section

/-! ## Constant Laurent polynomials -/
section LaurentConstant

open Polynomial LaurentPolynomial

/-- `H⁰(ℙ¹, 𝒪) = k`: if `P(T) = Q(T⁻¹)` as Laurent polynomials over the commutative ring `k`, then
`P` and `Q` are the same constant. -/
lemma New.Variety.eq_C_of_toLaurent_eq {k : Type} [CommRing k] (P Q : k[X])
    (hPQ : P.toLaurent = invert Q.toLaurent) :
    ∃ c : k, P = Polynomial.C c ∧ Q = Polynomial.C c := by
  -- `trunc` cuts off the negative powers of `T`: it returns `P` on the left side, and of the right
  -- side, with `Q` written as a sum of monomials, only the constant term of `Q` remains.
  have hP : P = .C (Q.coeff 0) := by
    rw [Q.as_sum_range] at hPQ
    simpa using congrArg trunc hPQ
  -- So `Q(T⁻¹) = P(T)` is that constant, and `Q ↦ Q(T⁻¹)` is injective.
  have hQ : Q = .C (Q.coeff 0) := by
    rw [← toLaurent_inj, ← invert.injective.eq_iff, ← hPQ, hP]
    simp
  exact ⟨Q.coeff 0, hP, hQ⟩

end LaurentConstant

namespace New.Variety

variable {p : ℕ}
/-!
## Perfect algebras, tensor products and blow-up charts

The category `New.Variety.PerfectAlg S` of perfect S-algebras, mostly for a ring S with p = 0. The
tilt of a p-adic test (`New.Variety.PadicTest`) is a perfect O♭-algebra.
-/

section PerfectAlgebras

open CategoryTheory Limits PerfectClosure TensorProduct AlgHom Polynomial Fact Ideal Quotient Period
  Function NeZero Algebra.TensorProduct ObjectProperty CharP

/-! ### Perfect algebras and Frobenius -/

/-- The full subcategory of commutative S-algebras on which x ↦ x^p is bijective. -/
abbrev PerfectAlg (S : Type) [CommRing S] [ThePrime p] : Type 1 :=
  FullSubcategory fun A : CommAlg S ↦ PerfectRing A p

variable {S : Type} [CommRing S] [ThePrime p]

/-- The underlying ring of a perfect S-algebra is perfect. -/
instance (b : PerfectAlg S) : PerfectRing b.obj p := b.property

/-- The maximal ideal 𝔪 of the local ring O^♭. -/
abbrev MaxIdealFlat : Type := ↥(IsLocalRing.maximalIdeal OFlat)

/-- The functor from p-adic tests to perfect O^♭-algebras sending S to its tilt S^♭. -/
def PadicTest.perfectTilt : PadicTest ⥤ PerfectAlg OFlat :=
  ObjectProperty.lift _ tilt fun c ↦ c.isPerfectTorsionFree_tilt.1

/-- The prime p is zero in every O^♭-algebra, as O^♭ has characteristic p. -/
lemma natCast_eq_zero_of_algebra_oFlat [Algebra OFlat S] : (p : S) = 0 := by
  simp [← map_natCast (algebraMap OFlat S), cast_eq_zero]

lemma coe_frobPow_one (hp : (p : S) = 0) : ⇑(frobPow hp 1) = fun x : S ↦ x ^ p := by ext; simp

lemma bijective_frobPow_one (hp : (p : S) = 0) [PerfectRing S p] : Bijective (frobPow hp 1) := by
  simpa only [coe_frobPow_one] using PerfectRing.bijective_frobenius

lemma perfectRing_of_bijective_frobPow (hp : (p : S) = 0) (h_bij : Bijective (frobPow hp 1)) :
    PerfectRing S p := ⟨by rwa [coe_frobPow_one] at h_bij⟩

open AddMonoidAlgebra in
/-- For a commutative additive monoid G that is a module over the non-negative rationals, the
monoid algebra O♭[G] is perfect: x ↦ x^p is bijective on it. Here p is the fixed prime and
O♭ = `OFlat` is the tilt of the ring of integers of ℂ_p, a perfect ring of characteristic p. -/
lemma perfectRing_monoidAlgebra (G : Type) [AddCommMonoid G] [Module ℚ≥0 G] :
    PerfectRing OFlat[G] p := by
  -- Frobenius is the composite of two ring isomorphisms: multiplication by `p` on the exponents
  -- and Frobenius on the coefficients.
  let e : OFlat[G] ≃+* OFlat[G] :=
    mapDomainRingEquiv _ (DistribMulAction.toAddEquiv₀ G (p : ℚ≥0) (NeZero.ne _)) *
      mapRingEquiv G (frobeniusEquiv OFlat p)
  have he : e.toRingHom = frobPow natCast_eq_zero_of_algebra_oFlat 1 := by
    ext
    · simp [e, frobenius_def]
    · simp [e, ← Nat.cast_smul_eq_nsmul ℚ≥0, DistribMulAction.toAddEquiv₀]
  refine perfectRing_of_bijective_frobPow natCast_eq_zero_of_algebra_oFlat ?_
  simpa [← he] using e.bijective

lemma isReduced_of_perfectRing (h_perf : PerfectRing S p) : IsReduced S := by
  refine (isReduced_iff_pow_one_lt p out).2 fun x hx ↦ ?_
  exact h_perf.bijective_frobenius.injective (by simpa [ne] using hx)

open LaurentPolynomial hiding C

/-- Every Laurent polynomial over S is a polynomial in T plus a polynomial in T⁻¹ without
constant term: the map (P, Q) ↦ P(T) + T⁻¹ Q(T⁻¹) from S[X] × S[X] to S[T, T⁻¹] is surjective,
that is, H¹(ℙ¹, 𝒪) = 0. -/
lemma surjective_toLaurent_add_invert :
    Surjective fun ((P, Q) : S[X] × S[X]) ↦ P.toLaurent + invert (X * Q).toLaurent := by
  intro f
  induction f using LaurentPolynomial.induction_on' with
  | add u v hu hv =>
    obtain ⟨⟨P₁, Q₁⟩, rfl⟩ := hu
    obtain ⟨⟨P₂, Q₂⟩, rfl⟩ := hv
    exact ⟨(P₁ + P₂, Q₁ + Q₂), by simp [mul_add, add_add_add_comm]⟩
  | C_mul_T n a =>
    -- it remains to treat the monomials `a Tⁿ` and `a T⁻⁽ⁿ⁺¹⁾`
    obtain n | n := n
    · exact ⟨(monomial n a, 0), by simp⟩
    · exact ⟨(0, monomial n a), by simp [Int.negSucc_eq]⟩

/-! ### Algebras over a ring with p = 0: colimits and perfection -/

omit [ThePrime p] in
lemma natCast_eq_zero_of_algebra (hp : (p : S) = 0) (B : Type) [CommRing B] [Algebra S B] :
    (p : B) = 0 := by
  rw [← map_natCast (algebraMap S B), hp, map_zero]

/-- If p = 0 in S, a wide pushout (indexed by any type J) of perfect S-algebras is perfect. -/
lemma PerfectAlg.isClosedUnderColimitsOfShape_widePushoutShape (hp : (p : S) = 0) (J : Type*) :
    IsClosedUnderColimitsOfShape (fun A : CommAlg S ↦ PerfectRing A p) (WidePushoutShape J) := by
  -- Frobenius is a natural endomorphism `τ` of the forgetful functor to rings, invertible on the
  -- diagram. The functor preserves connected colimits, so `τ` is invertible at the colimit too.
  refine ⟨fun A ⟨c⟩ ↦ ?_⟩
  have hp_alg (B : CommAlg S) : (p : B) = 0 := natCast_eq_zero_of_algebra hp B
  let F : CommAlg S ⥤ CommRingCat := (commAlgCatEquivUnder (.of S)).functor ⋙ Under.forget _
  let τ : F ⟶ F :=
    { app B := CommRingCat.ofHom (frobPow (hp_alg B) 1)
      naturality := by aesop_cat (add simp [F, commAlgCatEquivUnder]) }
  have (j : WidePushoutShape J) : PerfectRing (c.diag.obj j) p := c.prop_diag_obj j
  have : IsIso (c.diag.whiskerLeft τ) :=
    (isoOfAppBijective _ fun j ↦ bijective_frobPow_one (hp_alg (c.diag.obj j))).isIso_hom
  have : IsIso (τ.app A) := isIso_app_coconePt_of_preservesColimit _ τ _ c.isColimit
  exact perfectRing_of_bijective_frobPow (hp_alg A) (ConcreteCategory.bijective_of_isIso (τ.app A))

/-- For a prime `p` (fixed by the class `ThePrime p`) with `p = 0` in the commutative ring `S`, an
`S`-algebra `B` and an element `t ∈ B`, there is a perfection of `B/t`: a perfect `S`-algebra `c`
(one on which x ↦ x^p is bijective) with an `S`-algebra map `e : B → c` such that (a) every
`S`-algebra map `φ` from `B` to a perfect `S`-algebra with `φ t = 0` factors as `ψ ∘ e`; (b)
`e r = e s` implies `t ∣ r^{p^n} − s^{p^n}` for some `n`; (c) `e t = 0`; (d) every `y` in `c` has
some power `y^{p^n}` in the image of `e`. -/
lemma exists_perfection_quotient (hp : (p : S) = 0) (B : Type) [CommRing B] [Algebra S B] (t : B) :
    ∃ (c : PerfectAlg S) (e : B →ₐ[S] c.obj),
      (∀ {d : PerfectAlg S} (φ : B →ₐ[S] d.obj), φ t = 0 → ∃ ψ : c.obj →ₐ[S] d.obj, ψ.comp e = φ) ∧
      (∀ r s : B, e r = e s → ∃ n : ℕ, t ∣ r ^ p ^ n - s ^ p ^ n) ∧
      e t = 0 ∧
      ∀ y : c.obj, ∃ (n : ℕ) (r : B), e r = y ^ p ^ n := by
  let Q : Type := B ⧸ span ({t} : Set B)
  let π : B →ₐ[S] Q := Ideal.Quotient.mkₐ S (span {t})
  have h_ker (r : B) : π r = 0 ↔ t ∣ r := Ideal.Quotient.eq_zero_iff_dvd t r
  -- A map that kills `t` descends to the quotient `Q`.
  let descend {d : PerfectAlg S} (φ : B →ₐ[S] d.obj) (hφ : φ t = 0) : Q →ₐ[S] d.obj :=
    liftₐ (span {t}) φ ((RingHom.ker φ).span_singleton_le_iff_mem.2 hφ)
  obtain _ | _ := subsingleton_or_nontrivial Q
  · -- The zero ring is perfect, so `Q` itself will do, and `t` divides every element of `B`.
    exact ⟨⟨.of S Q, ⟨bijective_of_subsingleton _⟩⟩, π,
      fun φ hφ ↦ ⟨descend φ hφ, AlgHom.ext fun _ ↦ rfl⟩,
      fun r s _ ↦ ⟨0, (h_ker _).1 (Subsingleton.elim _ 0)⟩, (h_ker t).2 dvd_rfl,
      fun y ↦ ⟨0, 0, Subsingleton.elim (α := Q) _ _⟩⟩
  -- Otherwise take the perfect closure of `Q`; nonzero `S`-algebras have characteristic `p`.
  have h_charP (A : Type) [CommRing A] [Algebra S A] [Nontrivial A] : CharP A p :=
    (CharP.charP_iff_prime_eq_zero out).2 (natCast_eq_zero_of_algebra hp A)
  algebraize [(of Q p).comp (algebraMap S Q)]
  let ι : Q →ₐ[S] PerfectClosure Q p := ⟨of Q p, fun _ ↦ rfl⟩
  refine ⟨⟨.of S (PerfectClosure Q p), inferInstance⟩, ι.comp π, ?_, ?_, ?_, fun y ↦ ?_⟩
  · -- (a) This is the universal property of the perfect closure.
    intro d φ hφ
    obtain _ | _ := subsingleton_or_nontrivial d.obj
    · simp [nontriviality]
    obtain ⟨ψ, hψ⟩ : ∃ ψ : PerfectClosure Q p →+* d.obj, ψ.comp (of Q p) = descend φ hφ :=
      (lift Q p d.obj).symm.surjective _
    exact ⟨⟨ψ, fun s ↦ (RingHom.congr_fun hψ _).trans ((descend φ hφ).commutes s)⟩,
      AlgHom.ext fun b ↦ RingHom.congr_fun hψ (π b)⟩
  · -- (b) Two elements of `Q` have the same image iff an iterate of Frobenius identifies them.
    intro r s (hrs : of Q p (π r) = of Q p (π s))
    obtain ⟨n, hn⟩ : ∃ n : ℕ, π r ^ p ^ n = π s ^ p ^ n := by
      simpa [of_apply, mk_eq_iff, iterate_frobenius] using hrs
    exact ⟨n, (h_ker _).1 (by simp [hn])⟩
  · simp [(h_ker t).2 dvd_rfl]
  · -- (d) The perfect closure is purely inseparable over `Q`.
    obtain ⟨n, q, hq⟩ := (isPRadical Q p).pow_mem' y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨n, r, hq⟩

/-- If p = 0 in the reduced ring S and every element is a p-th power, then S is perfect. -/
lemma perfectRing_of_pow_surjective (hp : (p : S) = 0) [IsReduced S]
    (h_surj : Surjective fun x : S ↦ x ^ p) : PerfectRing S p := by
  -- Frobenius is a ring homomorphism, and its kernel consists of nilpotent elements.
  have h_inj : Injective (frobPow hp 1) := (injective_iff_map_eq_zero _).2 (by simp [ne])
  exact ⟨by rwa [coe_frobPow_one] at h_inj, h_surj⟩

/-! ### Tensor products and blow-up charts -/

lemma perfectRing_tensor (hp : (p : S) = 0) [PerfectRing S p] (B D : PerfectAlg S) :
    PerfectRing (B.obj ⊗[S] D.obj) p := by
  -- The tensor product is the pushout of `B` and `D` over `S`, and all three rings are perfect.
  have h_pushout :=
    IsPushout.of_is_coproduct (B.obj.binaryCofanIsColimit D.obj) CommAlgCat.isInitialSelf
  refine (PerfectAlg.isClosedUnderColimitsOfShape_widePushoutShape hp
    WalkingPair).colimitsOfShape_le _
    ⟨{ diag := _, ι := _, isColimit := h_pushout.isColimit, prop_diag_obj := ?_ }⟩
  -- The vertices of the span are `S`, `B` and `D`.
  rintro (_ | _ | _)
  exacts [inferInstanceAs (PerfectRing S p), B.property, D.property]

/-- Let S be perfect with p = 0 and i a map from a perfect S-algebra B to an S-algebra A. Suppose
that for every field k and every map a : B → k some injective map η from k to a perfect S-algebra
makes η ∘ a factor through i. Then i is injective after tensoring with any perfect S-algebra. -/
lemma injective_rTensor_of_field_maps_factor (hp : (p : S) = 0) [PerfectRing S p]
    (B : PerfectAlg S) {A : Type} [CommRing A] [Algebra S A] (i : B.obj →ₐ[S] A)
    (h_factor : ∀ (k : Type) [Field k] [Algebra S k] (a : B.obj →ₐ[S] k),
      ∃ (K : PerfectAlg S) (η : k →ₐ[S] K.obj) (ψ : A →ₐ[S] K.obj),
        Injective η ∧ ψ.comp i = η.comp a)
    (D : PerfectAlg S) : Injective (i.toLinearMap.rTensor D.obj) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  -- `B ⊗ D` is perfect, so reduced; it suffices that `x` lies in every prime `J`.
  have : IsReduced (B.obj ⊗[S] D.obj) := isReduced_of_perfectRing (perfectRing_tensor hp B D)
  refine IsNilpotent.eq_zero (nilpotent_iff_mem_prime.2 fun J _ ↦ ?_)
  let φ := IsScalarTower.toAlgHom S (B.obj ⊗[S] D.obj) J.ResidueField
  obtain ⟨K, η, ψ, h_inj, hψ⟩ := h_factor _ (φ.comp includeLeft)
  -- `η ∘ φ` factors through `A ⊗ D`, so it kills `x`.
  have factor (u : B.obj ⊗[S] D.obj) : η (φ u) =
      productMap ψ (η.comp (φ.comp includeRight)) (i.toLinearMap.rTensor D.obj u) := by
    induction u with
    | tmul b d =>
      have hb : ψ (i b) = η (φ (b ⊗ₜ 1)) := AlgHom.congr_fun hψ b
      simp [hb, ← map_mul]
    | add u v hu hv => simp [hu, hv]
  simpa [φ] using show φ x = 0 from h_inj (by simp [factor, hx])

/-- The relation f = g T in terms of T⁻¹: (g - f T⁻¹) = -(f - g T) T⁻¹. -/
lemma invert_toLaurent_C_sub_C_mul_X {R : Type} [CommRing R] (f g : R) :
    invert (C g - C f * X).toLaurent = -(C f - C g * X).toLaurent * T (-1) := by
  have h_inv : (T 1 * T (-1) : R[T;T⁻¹]) = 1 := by rw [← T_add, add_neg_cancel, T_zero]
  simp only [map_sub, map_mul, toLaurent_C, toLaurent_X, invert_C, invert_T]
  linear_combination -LaurentPolynomial.C g * h_inv

/-- If P(T) - Q(T⁻¹) = (f - g T)(U(T) + T⁻¹ V(T⁻¹)), then P - (f - g X) U and Q - (g - f X) V are
the same constant. -/
lemma exists_C_of_toLaurent_sub_invert_eq {R : Type} [CommRing R] (f g : R) (P Q U V : R[X])
    (h_eq : P.toLaurent - invert Q.toLaurent =
      (C f - C g * X).toLaurent * (U.toLaurent + invert V.toLaurent * T (-1))) :
    ∃ c : R, P - (C f - C g * X) * U = C c ∧ Q - (C g - C f * X) * V = C c := by
  refine eq_C_of_toLaurent_eq _ _ ?_
  calc (P - (C f - C g * X) * U).toLaurent
      = P.toLaurent - (C f - C g * X).toLaurent * U.toLaurent := by rw [map_sub, map_mul]
    _ = invert Q.toLaurent - invert (C g - C f * X).toLaurent * invert V.toLaurent := by
        rw [invert_toLaurent_C_sub_C_mul_X]
        linear_combination h_eq
    _ = invert (Q - (C g - C f * X) * V).toLaurent := by simp only [map_sub, map_mul]

/-- If p = 0 in S, every S-algebra k that is a field maps injectively to a perfect S-algebra. -/
lemma exists_injective_algHom_perfect (hp : (p : S) = 0) (k : Type) [Field k] [Algebra S k] :
    ∃ (K : PerfectAlg S) (η : k →ₐ[S] K.obj), Injective η := by
  -- The perfection of `k = k/0` will do: an element of its kernel is nilpotent, so zero.
  obtain ⟨K, η, -, h_ker, -⟩ := exists_perfection_quotient hp k 0
  refine ⟨K, η, (injective_iff_map_eq_zero η).2 fun u hu ↦ ?_⟩
  obtain ⟨n, hn⟩ := h_ker u 0 (by rw [hu, map_zero])
  exact eq_zero_of_pow_eq_zero (n := p ^ n) (by simpa [ne] using hn)

lemma bijective_pow_prime_pow (A : PerfectAlg S) (n : ℕ) : Bijective fun x : A.obj ↦ x ^ p ^ n :=
  (A.property.pow _ p n).bijective_frobenius

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- Let B, B₁, B₂, B₀ be perfect S-algebras with maps E₁ : B[X] → B₁, E₂ : B[X] → B₂ and
E₀ : B[T, T⁻¹] → B₀. Suppose E₀ kills f - g T, maps B[X] → B₀ that kill f - g X factor through E₁,
and those that kill g - f X factor through E₂. Then X ↦ T and X ↦ T⁻¹ induce maps j₁ : B₁ → B₀ and
j₂ : B₂ → B₀. -/
lemma exists_blowup_gluing_maps {B B₁ B₂ B₀ : PerfectAlg S} (f g : B.obj)
    (E₁ : B.obj[X] →ₐ[S] B₁.obj) (E₂ : B.obj[X] →ₐ[S] B₂.obj)
    (E₀ : B.obj[T;T⁻¹] →ₐ[S] B₀.obj) (h_rel : E₀ (C f - C g * X).toLaurent = 0)
    (h_lift₁ : ∀ φ : B.obj[X] →ₐ[S] B₀.obj, φ (C f - C g * X) = 0 →
      ∃ ψ : B₁.obj →ₐ[S] B₀.obj, ψ.comp E₁ = φ)
    (h_lift₂ : ∀ φ : B.obj[X] →ₐ[S] B₀.obj, φ (C g - C f * X) = 0 →
      ∃ ψ : B₂.obj →ₐ[S] B₀.obj, ψ.comp E₂ = φ) :
    ∃ (j₁ : B₁.obj →ₐ[S] B₀.obj) (j₂ : B₂.obj →ₐ[S] B₀.obj),
      (∀ P : B.obj[X], j₁ (E₁ P) = E₀ P.toLaurent) ∧
      ∀ P : B.obj[X], j₂ (E₂ P) = E₀ (invert P.toLaurent) := by
  obtain ⟨j₁, hj₁⟩ := h_lift₁ (E₀.comp ⟨toLaurent, by simp⟩) h_rel
  obtain ⟨j₂, hj₂⟩ := h_lift₂ (E₀.comp ⟨.comp invert.toRingHom toLaurent, by simp⟩)
    (show E₀ (invert (C g - C f * X).toLaurent) = 0 by
      simp [invert_toLaurent_C_sub_C_mul_X, h_rel, -map_sub])
  exact ⟨j₁, j₂, AlgHom.congr_fun hj₁, AlgHom.congr_fun hj₂⟩

/-- Let p = 0 in S and B, B₁, B₂, B₀ be perfect S-algebras. Let E₁, E₂ map B[X] to B₁, B₂, let E₀
map B[T, T⁻¹] to B₀, and let j₁, j₂ map B₁, B₂ to B₀ with j₁ (E₁ P) = E₀ (P(T)) and
j₂ (E₂ P) = E₀ (P(T⁻¹)). If every element of B₀ has a p^n-th power in the image of E₀, then
(y, z) ↦ j₁ y - j₂ z maps onto B₀. -/
lemma surjective_blowup_difference (hp : (p : S) = 0) {B B₁ B₂ B₀ : PerfectAlg S}
    (E₁ : B.obj[X] →ₐ[S] B₁.obj) (E₂ : B.obj[X] →ₐ[S] B₂.obj)
    (E₀ : B.obj[T;T⁻¹] →ₐ[S] B₀.obj) (j₁ : B₁.obj →ₐ[S] B₀.obj) (j₂ : B₂.obj →ₐ[S] B₀.obj)
    (hj₁ : ∀ P : B.obj[X], j₁ (E₁ P) = E₀ P.toLaurent)
    (hj₂ : ∀ P : B.obj[X], j₂ (E₂ P) = E₀ (invert P.toLaurent))
    (h_root : ∀ w : B₀.obj, ∃ (n : ℕ) (r : B.obj[T;T⁻¹]), E₀ r = w ^ p ^ n) :
    Surjective (j₁.toLinearMap.coprod (-j₂.toLinearMap)) := by
  intro w
  -- `w ^ p ^ n` is the image of `P(T) + T⁻¹ Q(T⁻¹)`; take roots of both terms.
  obtain ⟨n, r, hw⟩ := h_root w
  obtain ⟨⟨P, Q⟩, rfl⟩ := surjective_toLaurent_add_invert r
  obtain ⟨y, hy⟩ : ∃ y, y ^ p ^ n = E₁ P := (bijective_pow_prime_pow B₁ n).surjective _
  obtain ⟨z, hz⟩ : ∃ z, z ^ p ^ n = E₂ (X * Q) := (bijective_pow_prime_pow B₂ n).surjective _
  refine ⟨(y, -z), (bijective_pow_prime_pow B₀ n).injective ?_⟩
  calc j₁.toLinearMap.coprod (-j₂.toLinearMap) (y, -z) ^ p ^ n
      = j₁ y ^ p ^ n + j₂ z ^ p ^ n := by
        simp [add_pow_prime_pow_eq out, natCast_eq_zero_of_algebra hp]
    _ = j₁ (E₁ P) + j₂ (E₂ (X * Q)) := by rw [← map_pow, ← map_pow, hy, hz]
    _ = w ^ p ^ n := by rw [hj₁, hj₂, ← hw, map_add]

/-- Let B, B₁, B₂, B₀ be perfect S-algebras (x ↦ x^p is bijective on them). Let E₁, E₂ map B[X] to
B₁, B₂, let E₀ map B[T, T⁻¹] to B₀, and let j₁, j₂ satisfy j₁ (E₁ P) = E₀ (P(T)) and j₂ (E₂ P) = E₀
(P(T⁻¹)). Suppose E₁, E₂ kill f - g X, respectively g - f X, every element of B₁, B₂ has a p^n-th
power in the image of E₁, E₂, and elements with the same image under E₀ have p^n-th powers congruent
modulo f - g T. Then y in B₁ and z in B₂ with j₁ y = j₂ z are E₁ r and E₂ r for one constant r in
B. -/
lemma exists_eq_of_blowup_glue_eq {B B₁ B₂ B₀ : PerfectAlg S} (f g : B.obj)
    (E₁ : B.obj[X] →ₐ[S] B₁.obj) (E₂ : B.obj[X] →ₐ[S] B₂.obj)
    (E₀ : B.obj[T;T⁻¹] →ₐ[S] B₀.obj) (j₁ : B₁.obj →ₐ[S] B₀.obj) (j₂ : B₂.obj →ₐ[S] B₀.obj)
    (hj₁ : ∀ P : B.obj[X], j₁ (E₁ P) = E₀ P.toLaurent)
    (hj₂ : ∀ P : B.obj[X], j₂ (E₂ P) = E₀ (invert P.toLaurent))
    (h_rel₁ : E₁ (C f - C g * X) = 0) (h_rel₂ : E₂ (C g - C f * X) = 0)
    (h_root₁ : ∀ y : B₁.obj, ∃ (n : ℕ) (P : B.obj[X]), E₁ P = y ^ p ^ n)
    (h_root₂ : ∀ z : B₂.obj, ∃ (n : ℕ) (Q : B.obj[X]), E₂ Q = z ^ p ^ n)
    (h_ker₀ : ∀ r s : B.obj[T;T⁻¹], E₀ r = E₀ s →
      ∃ n : ℕ, (C f - C g * X).toLaurent ∣ r ^ p ^ n - s ^ p ^ n)
    {y : B₁.obj} {z : B₂.obj} (hyz : j₁ y = j₂ z) :
    ∃ r : B.obj, E₁ (C r) = y ∧ E₂ (C r) = z := by
  -- Powers of `y` and `z` are images of polynomials, and some powers of these differ in
  -- `B[T, T⁻¹]` by a multiple of `f - g T`.
  obtain ⟨n, P, hP⟩ := h_root₁ y
  obtain ⟨m, Q, hQ⟩ := h_root₂ (z ^ p ^ n)
  have h_same : E₀ (P.toLaurent ^ p ^ m) = E₀ (invert Q.toLaurent) := by
    simp [← hj₁, ← hj₂, hP, hQ, hyz]
  obtain ⟨N, W, hW⟩ := h_ker₀ _ _ h_same
  obtain ⟨⟨U, V⟩, rfl⟩ := surjective_toLaurent_add_invert W
  -- As `(f - g T) T⁻¹ = -(g - f T⁻¹)`, the polynomials corrected by multiples of the relations
  -- agree as Laurent polynomials, so both are one constant `c`. Its root maps to `(y, z)`.
  have h_diff : ((P ^ p ^ m) ^ p ^ N).toLaurent - invert (Q ^ p ^ N).toLaurent =
      (C f - C g * X).toLaurent * (U.toLaurent + invert V.toLaurent * T (-1)) := by
    simpa using hW
  obtain ⟨c, hPc, hQc⟩ := exists_C_of_toLaurent_sub_invert_eq f g _ _ U V h_diff
  obtain ⟨r, rfl⟩ : ∃ r, r ^ p ^ (n + m + N) = c := (bijective_pow_prime_pow B _).surjective c
  have hy : E₁ (C r) ^ p ^ (n + m + N) = y ^ p ^ (n + m + N) := by
    simpa [hP, h_rel₁, pow_add, pow_mul] using (congrArg E₁ hPc).symm
  have hz : E₂ (C r) ^ p ^ (n + m + N) = z ^ p ^ (n + m + N) := by
    simpa [hQ, h_rel₂, pow_add, pow_mul] using (congrArg E₂ hQc).symm
  exact ⟨r, (bijective_pow_prime_pow B₁ _).injective hy,
    (bijective_pow_prime_pow B₂ _).injective hz⟩

/-- Let p = 0 in S. Suppose maps from B[X] to perfect S-algebras that kill f - g X factor through
E₁ : B[X] → B₁, and those that kill g - f X factor through E₂ : B[X] → B₂. Then every point
a : B → k of B in a field becomes, after some injective map η from k to a perfect S-algebra, a
point that factors through B → B₁ × B₂. -/
lemma exists_factor_through_blowup_charts (hp : (p : S) = 0) {B B₁ B₂ : PerfectAlg S} (f g : B.obj)
    (E₁ : B.obj[X] →ₐ[S] B₁.obj) (E₂ : B.obj[X] →ₐ[S] B₂.obj)
    (h_lift₁ : ∀ {K : PerfectAlg S} (φ : B.obj[X] →ₐ[S] K.obj), φ (C f - C g * X) = 0 →
      ∃ ψ : B₁.obj →ₐ[S] K.obj, ψ.comp E₁ = φ)
    (h_lift₂ : ∀ {K : PerfectAlg S} (φ : B.obj[X] →ₐ[S] K.obj), φ (C g - C f * X) = 0 →
      ∃ ψ : B₂.obj →ₐ[S] K.obj, ψ.comp E₂ = φ)
    (k : Type) [Field k] [Algebra S k] (a : B.obj →ₐ[S] k) :
    ∃ (K : PerfectAlg S) (η : k →ₐ[S] K.obj) (ψ : (B₁.obj × B₂.obj) →ₐ[S] K.obj),
      Injective η ∧ ψ.comp ((E₁.comp CAlgHom).prod (E₂.comp CAlgHom)) = η.comp a := by
  obtain ⟨K, η, hη⟩ := exists_injective_algHom_perfect hp k
  -- In `k` either `g ∣ f` or `f ∣ g`, so the point `η ∘ a` of `B` lifts to a chart.
  obtain ⟨w, hw | hw⟩ := ValuationRing.cond (a g) (a f)
  · obtain ⟨ψ, hψ⟩ := h_lift₁ (η.comp (aevalTower a w)) (by simp [← hw])
    exact ⟨K, η, ψ.comp (.fst S _ _), hη,
      AlgHom.ext fun b ↦ by simpa using AlgHom.congr_fun hψ (C b)⟩
  · obtain ⟨ψ, hψ⟩ := h_lift₂ (η.comp (aevalTower a w)) (by simp [← hw])
    exact ⟨K, η, ψ.comp (.snd S _ _), hη,
      AlgHom.ext fun b ↦ by simpa using AlgHom.congr_fun hψ (C b)⟩

/-- The two charts of the blow-up of (f, g), perfected. For S perfect with p = 0 and f, g in a
perfect S-algebra B there are perfect S-algebras B₁, B₂ under B, and B₀, such that (a) g ∣ f in
B₁ and f ∣ g in B₂; (b) B → B₁ × B₂ → B₀ → 0 is an exact sequence of S-modules; (c) the first
map is injective after tensoring over S with any perfect S-algebra. -/
lemma exists_perfect_blowup_charts (hp : (p : S) = 0) [PerfectRing S p] (B : PerfectAlg S)
    (f g : B.obj) :
    ∃ (B₁ B₂ B₀ : PerfectAlg S) (i₁ : B.obj →ₐ[S] B₁.obj) (i₂ : B.obj →ₐ[S] B₂.obj)
        (j : (B₁.obj × B₂.obj) →ₗ[S] B₀.obj),
      i₁ g ∣ i₁ f ∧ i₂ f ∣ i₂ g ∧
      Surjective j ∧ Exact (i₁.prod i₂) j ∧
      ∀ D : PerfectAlg S, Injective ((i₁.prod i₂).toLinearMap.rTensor D.obj) := by
  -- The charts are the perfections `B₁` of `B[X] / (f - g X)`, `B₂` of `B[X] / (g - f X)` and `B₀`
  -- of `B[T, T⁻¹] / (f - g T)`, with `j₁ : X ↦ T`, `j₂ : X ↦ T⁻¹` and `j (y, z) = j₁ y - j₂ z`.
  obtain ⟨B₁, E₁, lift₁, -, rel₁, root₁⟩ := exists_perfection_quotient hp _ (C f - C g * X)
  obtain ⟨B₂, E₂, lift₂, -, rel₂, root₂⟩ := exists_perfection_quotient hp _ (C g - C f * X)
  obtain ⟨B₀, E₀, -, ker₀, rel₀, root₀⟩ := exists_perfection_quotient hp _ (C f - C g * X).toLaurent
  obtain ⟨j₁, j₂, hj₁, hj₂⟩ := exists_blowup_gluing_maps f g E₁ E₂ E₀ rel₀ lift₁ lift₂
  let i₁ : B.obj →ₐ[S] B₁.obj := E₁.comp CAlgHom
  let i₂ : B.obj →ₐ[S] B₂.obj := E₂.comp CAlgHom
  let j : (B₁.obj × B₂.obj) →ₗ[S] B₀.obj := j₁.toLinearMap.coprod (-j₂.toLinearMap)
  refine ⟨B₁, B₂, B₀, i₁, i₂, j, ?_, ?_,
    surjective_blowup_difference hp E₁ E₂ E₀ j₁ j₂ hj₁ hj₂ root₀,
    fun ⟨y, z⟩ ↦ ⟨fun hyz ↦ ?_, fun ⟨r, hr⟩ ↦ by simp [← hr, j, i₁, i₂, hj₁, hj₂]⟩,
    injective_rTensor_of_field_maps_factor hp B (i₁.prod i₂)
      (exists_factor_through_blowup_charts hp f g E₁ E₂ lift₁ lift₂)⟩
  · exact ⟨E₁ X, by simpa [i₁, sub_eq_zero] using rel₁⟩
  · exact ⟨E₂ X, by simpa [i₂, sub_eq_zero] using rel₂⟩
  · have h_glue : j₁ y = j₂ z := by simpa [j, add_neg_eq_zero] using hyz
    obtain ⟨r, hy, hz⟩ :=
      exists_eq_of_blowup_glue_eq f g E₁ E₂ E₀ j₁ j₂ hj₁ hj₂ rel₁ rel₂ root₁ root₂ ker₀ h_glue
    exact ⟨r, Prod.ext hy hz⟩

end PerfectAlgebras

/-! ## Étale algebras over quotients and over perfect rings -/

section EtalePerfect

open Function Algebra RingHom NeZero TensorProduct FormallyUnramified Etale IsLocalization Away

variable [ThePrime p] (C D : Type) [CommRing C] [CommRing D] [Algebra C D]

/-- Étale algebras lift along surjections: if C → D is onto and B is étale over D, then
B ≅ D ⊗_C T as D-algebras for some étale C-algebra T. -/
lemma exists_etale_lift (B : Type*) [CommRing B] [Algebra D B] [h_etale : Etale D B]
    (h_surj : Surjective (algebraMap C D)) :
    ∃ T : CommAlg C, Algebra.Etale C T ∧ Nonempty (D ⊗[C] T ≃ₐ[D] B) := by
  -- Lift a submersive presentation `P` of `B` of dimension `0` to a presentation `Q` over `C` and
  -- invert the Jacobian of `Q`; after base change to `D` the Jacobian is already a unit.
  algebraize [(algebraMap D B).comp (algebraMap C D)]
  obtain ⟨ι, σ, _, _, P : SubmersivePresentation D B ι σ, h_dim : P.dimension = 0⟩ :=
    (iff_isStandardSmoothOfRelativeDimension_zero.1 h_etale).1
  -- The coefficients of the relations of `P` come from `C`, so `P` has a model over `C`.
  have : P.HasCoeffs C := ⟨fun x _ ↦ h_surj x⟩
  let Q : PreSubmersivePresentation C (P.ModelOfHasCoeffs C) ι σ := P.1.ofHasCoeffs C
  let φ : D ⊗[C] P.ModelOfHasCoeffs C ≃ₐ[D] B := P.tensorModelOfHasCoeffsEquiv C
  -- `φ` sends the Jacobian of `Q` to that of `P`, a unit because `P` is submersive.
  have h_unit : IsUnit (φ (1 ⊗ₜ Q.jacobian)) := by
    let := Fintype.ofFinite σ
    classical
    -- `φ (1 ⊗ y)` is the value of the polynomial `y` at the generators of `B`.
    have hφ (y : MvPolynomial ι C) :
        φ (1 ⊗ₜ[C] algebraMap Q.Ring (P.ModelOfHasCoeffs C) y) = MvPolynomial.aeval P.val y :=
      (P.tensorModelOfHasCoeffsEquiv_tmul C 1 y).trans (by simp)
    have h_det : Q.jacobiMatrix.det = P.jacobianOfHasCoeffs C := rfl
    rw [Q.jacobian_eq_jacobiMatrix_det, hφ, h_det, P.aeval_jacobianOfHasCoeffs C]
    exact P.jacobian_isUnit
  refine ⟨.of _ (Localization.Away Q.jacobian), ?_, ⟨?_⟩⟩
  · -- Adjoining an inverse of the Jacobian adds one generator and one relation.
    let loc := PreSubmersivePresentation.localizationAway (Localization.Away Q.jacobian) Q.jacobian
    refine iff_isStandardSmoothOfRelativeDimension_zero.2
      ⟨_, _, _, inferInstance, ⟨loc.comp Q, ?_⟩, ?_⟩
    · simp [loc, algebraMap_isUnit, smul_def, -isUnit_map_iff]
    · grind [Presentation.dimension, Nat.card_sum]
  · -- Base change commutes with localisation, and localising at a unit changes nothing.
    have h_unit' : IsUnit ((1 : D) ⊗ₜ[C] Q.jacobian) := .of_map φ _ h_unit
    let e₁ : D ⊗[C] Localization.Away Q.jacobian ≃ₐ[D]
        Localization.Away ((1 : D) ⊗ₜ[C] Q.jacobian) :=
      tensorProductEquivTMulRight C D Q.jacobian (Localization.Away Q.jacobian)
    let e₂ : Localization.Away ((1 : D) ⊗ₜ[C] Q.jacobian) ≃ₐ[D] D ⊗[C] P.ModelOfHasCoeffs C :=
      (atUnit _ _ _ h_unit').symm.restrictScalars D
    exact e₁.trans (e₂.trans φ)

/-- Let `D` be étale over `C` with `p = 0` in `D`, and `f : D → E` a ring map with `C → E` étale.
If `s` is inverse to `f` up to the `p`-th power on both sides, then `f` is bijective. -/
lemma bijective_of_etale_of_inverse_up_to_pow [Etale C D] {E : Type} [CommRing E] (f : D →+* E)
    (hf : (f.comp (algebraMap C D)).Etale) (hp : (p : D) = 0) (s : E →+* D)
    (hsf : ∀ x : D, s (f x) = x ^ p) (hfs : ∀ x : E, f (s x) = x ^ p) : Bijective f := by
  -- `E` is étale and faithfully flat over `D`, so by descent it is enough to show
  -- `y ⊗ 1 = 1 ⊗ y` in `E ⊗[D] E` for every `y`.
  algebraize [f, f.comp (algebraMap C D)]
  have : Algebra.Etale D E := .of_restrictScalars C D E
  -- A prime `P` of `D` is the image of `P.comap s`, as `s (f x) = x ^ p`.
  have : Module.FaithfullyFlat D E := .of_comap_surjective fun P ↦ ⟨P.comap s, by
    ext
    simp [algebraMap_toAlgebra, hsf, P.isPrime.pow_mem_iff_mem, pos]⟩
  -- Frobenius of `E ⊗[D] E` factors through the multiplication map to `E` and `s`.
  have h_frob : frobPow (natCast_eq_zero_of_algebra hp (E ⊗[D] E)) 1 =
      (algebraMap D (E ⊗[D] E)).comp (s.comp (lmul' D).toRingHom) := by
    ext y <;> simp [← hfs, ← algebraMap_toAlgebra f, tmul_one_eq_one_tmul]
  -- The separability element `elem D E` multiplies to `1`, so its `p`-th power is `1`.
  have h_pow : elem D E ^ p = 1 := by
    calc elem D E ^ p = frobPow (natCast_eq_zero_of_algebra hp (E ⊗[D] E)) 1 (elem D E) := by simp
      _ = algebraMap D (E ⊗[D] E) (s (lmul' D (elem D E))) := RingHom.congr_fun h_frob _
      _ = 1 := by simp [lmul_elem, Algebra.TensorProduct.one_def]
  have h_unit : IsUnit (elem D E) := .of_pow_eq_one h_pow out
  refine ⟨FaithfulSMul.algebraMap_injective D E, fun y ↦ ?_⟩
  -- `elem D E` equalises `y ⊗ 1` and `1 ⊗ y`, and it is a unit.
  have h_eq : (y ⊗ₜ 1 : E ⊗[D] E) = 1 ⊗ₜ y := h_unit.mul_right_cancel (one_tmul_mul_elem y).symm
  exact (IsEffective.of_faithfullyFlat D E y).mp (sub_eq_zero.mpr h_eq :)

/-- An étale algebra over a perfect ring in which p = 0 is perfect. -/
lemma perfectRing_of_etale [Etale C D] [k : PerfectRing C p] (hp : (p : C) = 0) :
    PerfectRing D p := by
  have hD : (p : D) = 0 := natCast_eq_zero_of_algebra hp D
  -- `C → D → D` (Frobenius last) is also Frobenius of `C`, a bijection, followed by `C → D`.
  have h_comm : (frobPow hD 1).comp (algebraMap C D) = (algebraMap C D).comp (frobPow hp 1) :=
    RingHom.ext fun _ ↦ by simp
  have h_etale : ((frobPow hD 1).comp (algebraMap C D)).Etale := by
    rw [h_comm]
    exact RingHom.Etale.stableUnderComposition _ _ (.of_bijective (bijective_frobPow_one hp))
      (etale_algebraMap.2 inferInstance)
  -- The identity is inverse to Frobenius of `D` up to the `p`-th power.
  exact perfectRing_of_bijective_frobPow hD
    (bijective_of_etale_of_inverse_up_to_pow C D _ h_etale hD (.id D) (by simp) (by simp))

end EtalePerfect

end New.Variety

end
