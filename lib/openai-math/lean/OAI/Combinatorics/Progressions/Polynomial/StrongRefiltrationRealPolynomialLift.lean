import OAI.Combinatorics.Progressions.Linear.RefilteredKernelConstantBounds

namespace OAI

section

namespace Erdos3

open VectorPolynomial

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M]

theorem exists_unique_quotient_fiber_polynomial_lift
    (I : LieIdeal ℚ L) (J : LieIdeal ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ x ∈ I, φ x ∈ J)
    (hinj : ∀ x ∈ I, φ x = 0 → x = 0)
    (honto : ∀ y ∈ J, ∃ x ∈ I, φ x = y)
    (pbar : VectorPolynomial σ ℚ (L ⧸ I)) (q : VectorPolynomial σ ℚ M)
    (hcompat : map (lieQuotientProjection I J φ hφ).toLinearMap pbar =
      map (lieQuotientMap J).toLinearMap q) :
    ∃! p : VectorPolynomial σ ℚ L,
      map (lieQuotientMap I).toLinearMap p = pbar ∧ map φ.toLinearMap p = q := by
  let H := lieQuotientFiberProduct I J φ hφ
  let e := lieQuotientFiberEquiv I J φ hφ hinj honto
  have hc (a : σ →₀ ℕ) : coefficients (pair pbar q) a ∈ H.toSubmodule := by
    change lieQuotientProjection I J φ hφ (coefficients (pair pbar q) a).1 =
      lieQuotientMap J (coefficients (pair pbar q) a).2
    simpa only [coefficients_pair, coefficients_map, LieHom.coe_toLinearMap] using
      congrArg (fun P => coefficients P a) hcompat
  let r := restrictCoefficients H.toSubmodule (pair pbar q) hc
  let p := map e.symm.toLinearEquiv.toLinearMap r
  have he (a : σ →₀ ℕ) : (e (coefficients p a)).val =
      (coefficients pbar a, coefficients q a) := by
    change (e (coefficients (map e.symm.toLinearEquiv.toLinearMap r) a)).val = _
    rw [coefficients_map]
    change (e (e.symm (coefficients r a))).val = _
    rw [e.apply_symm_apply]
    exact (coefficients_restrictCoefficients H.toSubmodule (pair pbar q) hc a).trans
      (coefficients_pair pbar q a)
  have hpbar : map (lieQuotientMap I).toLinearMap p = pbar := by
    apply coefficients.injective
    ext a
    rw [coefficients_map]
    exact congrArg Prod.fst (he a)
  have hpq : map φ.toLinearMap p = q := by
    apply coefficients.injective
    ext a
    rw [coefficients_map]
    exact congrArg Prod.snd (he a)
  refine ⟨p, ⟨hpbar, hpq⟩, ?_⟩
  intro p' hp'
  apply coefficients.injective
  ext a
  apply e.injective
  apply Subtype.ext
  apply Prod.ext
  · change lieQuotientMap I (coefficients p' a) = lieQuotientMap I (coefficients p a)
    have h := congrArg (fun P => coefficients P a) (hp'.1.trans hpbar.symm)
    simpa only [coefficients_map, LieHom.coe_toLinearMap] using h
  · change φ (coefficients p' a) = φ (coefficients p a)
    have h := congrArg (fun P => coefficients P a) (hp'.2.trans hpq.symm)
    simpa only [coefficients_map, LieHom.coe_toLinearMap] using h

namespace NilpotentLieFiltration

variable {s : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem exists_unique_adapted_quotient_fiber_polynomial_lift
    (hinj : ∀ x ∈ F.layer s, φ x = 0 → x = 0)
    (honto : ∀ y ∈ G.layer s, ∃ x ∈ F.layer s, φ x = y)
    (w : σ → ℕ) (pbar : VectorPolynomial σ ℚ (L ⧸ F.layerIdeal s))
    (q : VectorPolynomial σ ℚ M)
    (hcompat : map (lieQuotientProjection (F.layerIdeal s) (G.layerIdeal s) φ (hφ s)).toLinearMap
      pbar = map (lieQuotientMap (G.layerIdeal s)).toLinearMap q)
    (hpbar : ∀ a, coefficients pbar a ∈
      (F.layer (Finsupp.weight w a)).map (lieQuotientMap (F.layerIdeal s)).toLinearMap)
    (hq : G.Adapted w q) :
    ∃! p : VectorPolynomial σ ℚ L,
      F.Adapted w p ∧ map (lieQuotientMap (F.layerIdeal s)).toLinearMap p = pbar ∧
        map φ.toLinearMap p = q := by
  obtain ⟨p, ⟨heq, hproj⟩, huniq⟩ := exists_unique_quotient_fiber_polynomial_lift
    (F.layerIdeal s) (G.layerIdeal s) φ (hφ s) hinj honto pbar q hcompat
  have hadapt : F.Adapted w p := by
    apply (F.adapted_iff_coefficients w p).mpr
    intro a
    apply (F.mem_layer_iff_quotient_and_projection G φ hφ hinj (Finsupp.weight w a) _).mpr
    have heqa := congrArg (fun P => coefficients P a) heq
    have hproja := congrArg (fun P => coefficients P a) hproj
    simp only [coefficients_map, LieHom.coe_toLinearMap] at heqa hproja
    rw [heqa, hproja]
    exact ⟨hpbar a, (G.adapted_iff_coefficients w q).mp hq a⟩
  exact ⟨p, ⟨hadapt, heq, hproj⟩, fun p' hp' => huniq p' hp'.2⟩

theorem exists_unique_quotient_fiber_polynomialOrbit_lift
    {r : ℕ} (F : NilpotentLieFiltration L (r + 1)) (G : NilpotentLieFiltration M (r + 1))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (hinj : ∀ x ∈ F.layer (r + 1), φ x = 0 → x = 0)
    (honto : ∀ y ∈ G.layer (r + 1), ∃ x ∈ F.layer (r + 1), φ x = y)
    (w : σ → ℕ) (pbar : F.quotientTop.PolynomialOrbit w) (q : G.PolynomialOrbit w)
    (hcompat : map (lieQuotientProjection (F.layerIdeal (r + 1)) (G.layerIdeal (r + 1))
      φ (hφ (r + 1))).toLinearMap pbar.log =
        map (lieQuotientMap (G.layerIdeal (r + 1))).toLinearMap q.log) :
    ∃! p : F.PolynomialOrbit w,
      map (lieQuotientMap (F.layerIdeal (r + 1))).toLinearMap p.log = pbar.log ∧
        map φ.toLinearMap p.log = q.log := by
  have hpbar : ∀ a, coefficients pbar.log a ∈
      (F.layer (Finsupp.weight w a)).map
        (lieQuotientMap (F.layerIdeal (r + 1))).toLinearMap :=
    (F.quotientTop.adapted_iff_coefficients w pbar.log).mp pbar.adapted
  obtain ⟨p, ⟨hp, heq, hproj⟩, huniq⟩ :=
    F.exists_unique_adapted_quotient_fiber_polynomial_lift G φ hφ hinj honto
      w pbar.log q.log hcompat hpbar q.adapted
  refine ⟨polynomialOrbitOfLog p hp, ⟨heq, hproj⟩, ?_⟩
  intro p' hp'
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  exact huniq p'.log ⟨p'.adapted, hp'⟩

end NilpotentLieFiltration

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (G : NilpotentLieFiltration M (s + 1))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem exists_unique_real_quotient_fiber_polynomialOrbit_lift
    (hinj : ∀ x ∈ F.layer (s + 1), φ x = 0 → x = 0)
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    (w : σ → ℕ) (pbar : F.quotientTop.realification.PolynomialOrbit w)
    (q : G.realification.PolynomialOrbit w)
    (hcompat : map
      (realLieHomToRat (realificationLieHom
        (lieQuotientProjection (F.layerIdeal (s + 1)) (G.layerIdeal (s + 1)) φ
          (hφ (s + 1))))).toLinearMap pbar.log =
      map (realLieHomToRat (realificationLieHom
        (lieQuotientMap (G.layerIdeal (s + 1))))).toLinearMap q.log) :
    ∃! p : F.realification.PolynomialOrbit w,
      map (realLieHomToRat (realificationLieHom
        (lieQuotientMap (F.layerIdeal (s + 1))))).toLinearMap p.log = pbar.log ∧
      map (realLieHomToRat (realificationLieHom φ)).toLinearMap p.log = q.log := by
  let e := F.realificationTopQuotientEquiv
  let φR := realLieHomToRat (realificationLieHom φ)
  let hφR := F.realificationLieHom_mem_layer G φ hφ
  let pbar' : F.realification.quotientTop.PolynomialOrbit w :=
    polynomialOrbitOfLog (map e.symm.toLinearEquiv.toLinearMap pbar.log)
      (F.quotientTop.realification.adapted_map F.realification.quotientTop
        e.symm.toLinearEquiv.toLinearMap
        (fun j x hx => (F.realificationTopQuotientEquiv_mem_layer_iff j (e.symm x)).mp
          (by simpa only [e, LieEquiv.apply_symm_apply] using hx)) w pbar.adapted)
  have hcompat' : map
      (lieQuotientProjection (F.realification.layerIdeal (s + 1))
        (G.realification.layerIdeal (s + 1)) φR (hφR (s + 1))).toLinearMap pbar'.log =
      map (lieQuotientMap (G.realification.layerIdeal (s + 1))).toLinearMap q.log := by
    apply coefficients.injective
    ext a
    rw [coefficients_map, coefficients_map]
    apply G.realificationTopQuotientEquiv.injective
    change G.realificationTopQuotientEquiv
      (lieQuotientProjection (F.realification.layerIdeal (s + 1))
        (G.realification.layerIdeal (s + 1))
        (realLieHomToRat (realificationLieHom φ))
        (F.realificationLieHom_mem_layer G φ hφ (s + 1)) (coefficients pbar'.log a)) =
      G.realificationTopQuotientEquiv
        (lieQuotientMap (G.realification.layerIdeal (s + 1)) (coefficients q.log a))
    rw [F.realificationTopQuotientEquiv_projection G φ hφ,
      G.realificationTopQuotientEquiv_mk]
    have he : e (coefficients pbar'.log a) = coefficients pbar.log a := by
      change e (coefficients (map e.symm.toLinearEquiv.toLinearMap pbar.log) a) = _
      rw [coefficients_map]
      exact e.apply_symm_apply _
    change realificationLieHom
      (lieQuotientProjection (F.layerIdeal (s + 1)) (G.layerIdeal (s + 1)) φ (hφ (s + 1)))
      (e (coefficients pbar'.log a)) = _
    rw [he]
    have ha := congrArg (fun P => coefficients P a) hcompat
    simp only [coefficients_map] at ha
    exact ha
  obtain ⟨p, ⟨hpbar, hpq⟩, huniq⟩ :=
    F.realification.exists_unique_quotient_fiber_polynomialOrbit_lift G.realification φR hφR
      (F.realificationLieHom_top_kernel_eq_zero G φ hφ hinj)
      (F.realificationLieHom_layer_surjective G φ hφ hsurj (s + 1)) w pbar' q hcompat'
  have hreal : map (realLieHomToRat (realificationLieHom
      (lieQuotientMap (F.layerIdeal (s + 1))))).toLinearMap p.log = pbar.log := by
    apply coefficients.injective
    ext a
    rw [coefficients_map]
    have ha := congrArg (fun P => e (coefficients P a)) hpbar
    simp only [coefficients_map] at ha
    change realificationLieHom (lieQuotientMap (F.layerIdeal (s + 1)))
      (coefficients p.log a) = _
    refine ha.trans ?_
    change e (coefficients (map e.symm.toLinearEquiv.toLinearMap pbar.log) a) = _
    rw [coefficients_map]
    exact e.apply_symm_apply _
  refine ⟨p, ⟨hreal, hpq⟩, ?_⟩
  intro p' hp'
  apply huniq p'
  refine ⟨?_, hp'.2⟩
  apply coefficients.injective
  ext a
  rw [coefficients_map]
  apply e.injective
  have ha := congrArg (fun P => coefficients P a) hp'.1
  rw [coefficients_map] at ha
  change realificationLieHom (lieQuotientMap (F.layerIdeal (s + 1)))
    (coefficients p'.log a) = e (coefficients pbar'.log a)
  refine ha.trans ?_
  change coefficients pbar.log a =
    e (coefficients (map e.symm.toLinearEquiv.toLinearMap pbar.log) a)
  rw [coefficients_map]
  exact (e.apply_symm_apply _).symm

theorem real_polynomialOrbit_formal_map_eval {t : ℕ}
    (G : NilpotentLieFiltration M t) (φ : L →ₗ⁅ℚ⁆ M)
    (w : σ → ℕ) (p : F.realification.PolynomialOrbit w)
    (q : G.realification.PolynomialOrbit w)
    (hmap : map (realLieHomToRat (realificationLieHom φ)).toLinearMap p.log = q.log)
    (x : σ → ℝ) :
    NilpotentLieBCHGroup.realificationMap
      (hnil := F.lowerCentralSeries_eq_bot) (hM := G.lowerCentralSeries_eq_bot) φ
      (F.realification.polynomialOrbitRealEval w x p) =
        G.realification.polynomialOrbitRealEval w x q := by
  apply NilpotentLieBCHGroup.ext
  change realificationLieHom φ (eval₂ x p.log) = eval₂ x q.log
  rw [← hmap]
  exact (eval₂_map (realificationLieHom φ).toLinearMap x p.log).symm

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (G : NilpotentLieFiltration M (s + 1))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (U : LieSubalgebra ℚ F.AssociatedGraded)
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (b : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (b '' {i | j ≤ ν i}))
    (hU : BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω U.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    (htop : ∀ a ∈ U,
      basisGradeProjection (F.associatedGradedBasis e ω hF) ω (s + 1) a = a →
      F.associatedGradedMap G φ hφ a = 0 → a = 0)

include e ω hF b ν hG hU hsurj htop in

theorem exists_unique_refiltered_quotient_polynomialOrbit_lift
    (w : σ → ℕ) (pbar : (F.gradedRefiltration U).quotientTop.PolynomialOrbit w)
    (q : (G.gradedRefiltration (U.map (F.associatedGradedMap G φ hφ))).PolynomialOrbit w)
    (hcompat : map
      (lieQuotientProjection ((F.gradedRefiltration U).layerIdeal (s + 1))
        ((G.gradedRefiltration (U.map (F.associatedGradedMap G φ hφ))).layerIdeal (s + 1))
        (F.gradedRefiltrationMap G φ hφ U)
        (F.gradedRefiltrationMap_mem_layer G φ hφ U (s + 1))).toLinearMap pbar.log =
      map (lieQuotientMap
        ((G.gradedRefiltration (U.map (F.associatedGradedMap G φ hφ))).layerIdeal
          (s + 1))).toLinearMap q.log) :
    ∃! p : (F.gradedRefiltration U).PolynomialOrbit w,
      map (lieQuotientMap ((F.gradedRefiltration U).layerIdeal (s + 1))).toLinearMap
        p.log = pbar.log ∧
      map (F.gradedRefiltrationMap G φ hφ U).toLinearMap p.log = q.log := by
  exact (F.gradedRefiltration U).exists_unique_quotient_fiber_polynomialOrbit_lift
    (G.gradedRefiltration (U.map (F.associatedGradedMap G φ hφ)))
    (F.gradedRefiltrationMap G φ hφ U)
    (F.gradedRefiltrationMap_mem_layer G φ hφ U)
    (fun x hx hz => Subtype.ext
      (F.gradedRefiltrationLayer_top_kernel_eq_zero G e ω hF φ hφ U htop x hx
        (congrArg Subtype.val hz)))
    (F.gradedRefiltrationMap_layer_surjective G e ω hF b ν hG φ hφ U hU hsurj (s + 1))
    w pbar q hcompat

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (G : NilpotentLieFiltration M (s + 1))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (U : LieSubalgebra ℚ F.AssociatedGraded)
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (b : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (b '' {i | j ≤ ν i}))
    (hU : BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω U.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    (htop : ∀ a ∈ U,
      basisGradeProjection (F.associatedGradedBasis e ω hF) ω (s + 1) a = a →
      F.associatedGradedMap G φ hφ a = 0 → a = 0)

include e ω hF b ν hG hU hsurj htop in

theorem exists_unique_real_refiltered_quotient_polynomialOrbit_lift
    (w : σ → ℕ)
    (pbar : (F.gradedRefiltration U).quotientTop.realification.PolynomialOrbit w)
    (q : (G.gradedRefiltration
      (U.map (F.associatedGradedMap G φ hφ))).realification.PolynomialOrbit w)
    (hcompat : map (realLieHomToRat (realificationLieHom
      (lieQuotientProjection ((F.gradedRefiltration U).layerIdeal (s + 1))
        ((G.gradedRefiltration (U.map (F.associatedGradedMap G φ hφ))).layerIdeal (s + 1))
        (F.gradedRefiltrationMap G φ hφ U)
        (F.gradedRefiltrationMap_mem_layer G φ hφ U (s + 1))))).toLinearMap pbar.log =
      map (realLieHomToRat (realificationLieHom (lieQuotientMap
        ((G.gradedRefiltration (U.map (F.associatedGradedMap G φ hφ))).layerIdeal
          (s + 1))))).toLinearMap q.log) :
    ∃! p : (F.gradedRefiltration U).realification.PolynomialOrbit w,
      map (realLieHomToRat (realificationLieHom
        (lieQuotientMap ((F.gradedRefiltration U).layerIdeal (s + 1))))).toLinearMap
        p.log = pbar.log ∧
      map (realLieHomToRat (realificationLieHom
        (F.gradedRefiltrationMap G φ hφ U))).toLinearMap p.log = q.log := by
  exact (F.gradedRefiltration U).exists_unique_real_quotient_fiber_polynomialOrbit_lift
    (G.gradedRefiltration (U.map (F.associatedGradedMap G φ hφ)))
    (F.gradedRefiltrationMap G φ hφ U)
    (F.gradedRefiltrationMap_mem_layer G φ hφ U)
    (fun x hx hz => Subtype.ext
      (F.gradedRefiltrationLayer_top_kernel_eq_zero G e ω hF φ hφ U htop x hx
        (congrArg Subtype.val hz)))
    (F.gradedRefiltrationMap_layer_surjective G e ω hF b ν hG φ hφ U hU hsurj)
    w pbar q hcompat

end Erdos3.NilpotentLieFiltration

end

end OAI
