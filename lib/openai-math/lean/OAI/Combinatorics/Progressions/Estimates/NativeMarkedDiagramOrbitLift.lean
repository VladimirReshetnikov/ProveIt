/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Polynomial.StrongRefiltrationRealPolynomialLift
import OAI.Combinatorics.Progressions.Sampling.MarkedKernelProjectionScoreRestoration

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d n : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
  (hQ : Q.filtration = D.filtration.quotientTop) {w : σ → ℕ}

noncomputable def topQuotientOrbit (g : D.filtration.realification.PolynomialOrbit w) :
    Q.filtration.realification.PolynomialOrbit w :=
  let q := D.filtration.realQuotientPolynomialOrbit
    (D.filtration.layerIdeal (s + 1)) (t := s) le_rfl g
  NilpotentLieFiltration.polynomialOrbitOfLog q.log (by rw [hQ]; exact q.adapted)

theorem topQuotientOrbit_eval (g : D.filtration.realification.PolynomialOrbit w) (x : σ → ℤ) :
    Q.filtration.realification.polynomialOrbitEval w x (D.topQuotientOrbit Q hQ g) =
      realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot)
        (lieQuotientMap (D.filtration.layerIdeal (s + 1)))
        (D.filtration.realification.polynomialOrbitEval w x g) := by
  exact D.filtration.realQuotientPolynomialOrbit_eval
    (D.filtration.layerIdeal (s + 1)) (t := s) le_rfl g x

theorem topQuotientOrbit_cyclicOrbitPoint
    (g : D.filtration.realification.PolynomialOrbit w) (N : ℕ) [NeZero N] (x : σ → ZMod N) :
    Q.cyclicOrbitPoint (D.topQuotientOrbit Q hQ g) N x =
      (QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot)
        (lieQuotientMap (D.filtration.layerIdeal (s + 1)))
        (D.filtration.realification.polynomialOrbitEval w (fun i => ((x i).val : ℤ)) g)) : Q.Space) := by
  exact congrArg (QuotientGroup.mk : Q.RealGroup → Q.Space)
    (D.topQuotientOrbit_eval Q hQ g (fun i => ((x i).val : ℤ)))

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d n : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
    (hQ : Q.filtration = D.filtration.quotientTop) {w : σ → ℕ}

theorem topQuotientOrbit_surjective :
    Function.Surjective (D.topQuotientOrbit Q hQ (w := w)) := by
  intro q
  let φ := realLieHomToRat
    (realificationLieHom (lieQuotientMap (D.filtration.layerIdeal (s + 1))))
  have hf : ∀ j, ∀ x ∈ D.filtration.realification.layer j,
      φ x ∈ Q.filtration.realification.layer j := by
    intro j x hx
    rw [hQ]
    exact D.filtration.realQuotientStep_mem_layer
      (D.filtration.layerIdeal (s + 1)) (t := s) le_rfl hx
  have hsurj : ∀ j, ∀ y ∈ Q.filtration.realification.layer j,
      ∃ x ∈ D.filtration.realification.layer j, φ x = y := by
    intro j y hy
    rw [hQ] at hy
    change y ∈ ((D.filtration.layer j).map
      (lieQuotientMap (D.filtration.layerIdeal (s + 1))).toLinearMap).baseChange ℝ at hy
    rw [realification_map] at hy
    exact hy
  obtain ⟨p, hp⟩ := D.filtration.realification.filteredPolynomialMap_surjective
    Q.filtration.realification φ hf w hsurj
    ⟨q.log, (Q.filtration.realification.mem_adaptedSubmodule w q.log).mpr q.adapted⟩
  let g : D.filtration.realification.PolynomialOrbit w :=
    polynomialOrbitOfLog p.val
      ((D.filtration.realification.mem_adaptedSubmodule w p.val).mp p.property)
  refine ⟨g, ?_⟩
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  change VectorPolynomial.map φ.toLinearMap p.val = q.log
  exact congrArg Subtype.val hp

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (G : NilpotentLieFiltration M (s + 1))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem exists_real_quotient_fiber_polynomialOrbit_lift
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    (w : σ → ℕ) (pbar : F.quotientTop.realification.PolynomialOrbit w)
    (q : G.realification.PolynomialOrbit w)
    (hcompat : map
      (realLieHomToRat (realificationLieHom
        (lieQuotientProjection (F.layerIdeal (s + 1)) (G.layerIdeal (s + 1)) φ
          (hφ (s + 1))))).toLinearMap pbar.log =
      map (realLieHomToRat (realificationLieHom
        (lieQuotientMap (G.layerIdeal (s + 1))))).toLinearMap q.log) :
    ∃ p : F.realification.PolynomialOrbit w,
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
  obtain ⟨p, hpbar, hpq⟩ :=
    F.realification.exists_quotient_fiber_polynomialOrbit_lift G.realification φR hφR
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
  exact ⟨p, hreal, hpq⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct

variable {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d n : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (G : NilpotentLieFiltration M (s + 1))
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ G.layer j)
    (Q : RationalFilteredNilmanifold
      (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
    (hQ : Q.filtration = D.filtration.quotientTop) {w : σ → ℕ}

theorem exists_prescribed_marked_topQuotientOrbit_lift
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (q : Q.filtration.realification.PolynomialOrbit w)
    (marked : G.realification.PolynomialOrbit w)
    (hcompat : map
      (realLieHomToRat (realificationLieHom
        (lieQuotientProjection (D.filtration.layerIdeal (s + 1))
          (G.layerIdeal (s + 1)) φ (hφ (s + 1))))).toLinearMap q.log =
      map (realLieHomToRat (realificationLieHom
        (lieQuotientMap (G.layerIdeal (s + 1))))).toLinearMap marked.log) :
    ∃ g : D.filtration.realification.PolynomialOrbit w,
      D.topQuotientOrbit Q hQ g = q ∧
      map (realLieHomToRat (realificationLieHom φ)).toLinearMap g.log = marked.log ∧
      (∀ z : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot)
        (lieQuotientMap (D.filtration.layerIdeal (s + 1)))
        (D.filtration.realification.polynomialOrbitRealEval w z g) =
          Q.filtration.realification.polynomialOrbitRealEval w z q) ∧
      ∀ z : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := G.lowerCentralSeries_eq_bot) φ
        (D.filtration.realification.polynomialOrbitRealEval w z g) =
          G.realification.polynomialOrbitRealEval w z marked := by
  let q' : D.filtration.quotientTop.realification.PolynomialOrbit w :=
    polynomialOrbitOfLog q.log (by rw [← hQ]; exact q.adapted)
  obtain ⟨g, hquot, hmark⟩ :=
    D.filtration.exists_real_quotient_fiber_polynomialOrbit_lift G φ hφ hsurj w
      q' marked hcompat
  have hq : D.topQuotientOrbit Q hQ g = q := by
    apply Subtype.ext
    apply NilpotentLieBCHGroup.ext
    exact hquot
  refine ⟨g, hq, hmark, ?_, ?_⟩
  · intro z
    apply NilpotentLieBCHGroup.ext
    change realificationLieHom (lieQuotientMap (D.filtration.layerIdeal (s + 1)))
      (eval₂ z g.log) = eval₂ z q.log
    change map (realLieHomToRat (realificationLieHom
      (lieQuotientMap (D.filtration.layerIdeal (s + 1))))).toLinearMap g.log =
      q.log at hquot
    rw [← hquot]
    exact (eval₂_map
      (realificationLieHom (lieQuotientMap (D.filtration.layerIdeal (s + 1)))).toLinearMap
      z g.log).symm
  · intro z
    apply NilpotentLieBCHGroup.ext
    change realificationLieHom φ (eval₂ z g.log) = eval₂ z marked.log
    rw [← hmark]
    exact (eval₂_map (realificationLieHom φ).toLinearMap z g.log).symm

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct

variable {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s d e n m : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (E : RationalFilteredNilmanifold M (s + 1) e)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ E.filtration.layer j)

noncomputable def topQuotientMarkedMap :
    (L ⧸ D.filtration.layerIdeal (s + 1)) →ₗ⁅ℚ⁆
      (M ⧸ E.filtration.layerIdeal (s + 1)) :=
  lieQuotientProjection (D.filtration.layerIdeal (s + 1))
    (E.filtration.layerIdeal (s + 1)) φ (hφ (s + 1))

theorem topQuotientMarkedMap_real_mk (x : ℝ ⊗[ℚ] L) :
    realificationLieHom (D.topQuotientMarkedMap E φ hφ)
      (realificationLieHom (lieQuotientMap (D.filtration.layerIdeal (s + 1))) x) =
    realificationLieHom (lieQuotientMap (E.filtration.layerIdeal (s + 1)))
      (realificationLieHom φ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
  (hQ : Q.filtration = D.filtration.quotientTop)
  (QF : RationalFilteredNilmanifold (M ⧸ E.filtration.layerIdeal (s + 1)) s m)
  (hQF : QF.filtration = E.filtration.quotientTop) {w : σ → ℕ}

include hQ hQF in
theorem topQuotientMarkedMap_mem_layer (j : ℕ)
    (x : L ⧸ D.filtration.layerIdeal (s + 1)) (hx : x ∈ Q.filtration.layer j) :
    D.topQuotientMarkedMap E φ hφ x ∈ QF.filtration.layer j := by
  rw [hQ] at hx
  rw [hQF]
  obtain ⟨z, hz, rfl⟩ := hx
  exact ⟨φ z, hφ j z hz, rfl⟩

noncomputable def topQuotientMarkedOrbit (q : Q.filtration.realification.PolynomialOrbit w) :
    QF.filtration.realification.PolynomialOrbit w :=
  polynomialOrbitOfLog
    (map (realLieHomToRat (realificationLieHom (D.topQuotientMarkedMap E φ hφ))).toLinearMap q.log)
    (Q.filtration.realification.adapted_map QF.filtration.realification _
      (Q.filtration.realificationLieHom_mem_layer QF.filtration
        (D.topQuotientMarkedMap E φ hφ)
        (D.topQuotientMarkedMap_mem_layer E φ hφ Q hQ QF hQF)) w q.adapted)

@[simp] theorem topQuotientMarkedOrbit_log (q : Q.filtration.realification.PolynomialOrbit w) :
    (D.topQuotientMarkedOrbit E φ hφ Q hQ QF hQF q).log =
      map (realLieHomToRat (realificationLieHom
        (lieQuotientProjection (D.filtration.layerIdeal (s + 1))
          (E.filtration.layerIdeal (s + 1)) φ (hφ (s + 1))))).toLinearMap q.log := rfl

theorem topQuotientMarkedOrbit_eq_iff (q : Q.filtration.realification.PolynomialOrbit w)
    (marked : E.filtration.realification.PolynomialOrbit w) :
    D.topQuotientMarkedOrbit E φ hφ Q hQ QF hQF q = E.topQuotientOrbit QF hQF marked ↔
      map (realLieHomToRat (realificationLieHom
        (lieQuotientProjection (D.filtration.layerIdeal (s + 1))
          (E.filtration.layerIdeal (s + 1)) φ (hφ (s + 1))))).toLinearMap q.log =
      map (realLieHomToRat (realificationLieHom
        (lieQuotientMap (E.filtration.layerIdeal (s + 1))))).toLinearMap marked.log := by
  constructor
  · intro h
    exact congrArg (fun p => p.log) h
  · intro h
    exact Subtype.ext (NilpotentLieBCHGroup.ext h)

theorem topQuotientMarkedOrbit_topQuotientOrbit
    (g : D.filtration.realification.PolynomialOrbit w)
    (marked : E.filtration.realification.PolynomialOrbit w)
    (hmark : map (realLieHomToRat (realificationLieHom φ)).toLinearMap g.log = marked.log) :
    D.topQuotientMarkedOrbit E φ hφ Q hQ QF hQF (D.topQuotientOrbit Q hQ g) =
      E.topQuotientOrbit QF hQF marked := by
  apply (D.topQuotientMarkedOrbit_eq_iff E φ hφ Q hQ QF hQF _ marked).mpr
  change map (realLieHomToRat (realificationLieHom (D.topQuotientMarkedMap E φ hφ))).toLinearMap
    (map (realLieHomToRat (realificationLieHom
      (lieQuotientMap (D.filtration.layerIdeal (s + 1))))).toLinearMap g.log) = _
  rw [← hmark]
  apply coefficients.injective
  ext a
  simp only [coefficients_map]
  exact D.topQuotientMarkedMap_real_mk E φ hφ (coefficients g.log a)

theorem exists_marked_topQuotientOrbit_lift_of_quotient_eq
    (hsurj : ∀ j, ∀ y ∈ E.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (q : Q.filtration.realification.PolynomialOrbit w)
    (marked : E.filtration.realification.PolynomialOrbit w)
    (heq : D.topQuotientMarkedOrbit E φ hφ Q hQ QF hQF q = E.topQuotientOrbit QF hQF marked) :
    ∃ g : D.filtration.realification.PolynomialOrbit w,
      D.topQuotientOrbit Q hQ g = q ∧
      map (realLieHomToRat (realificationLieHom φ)).toLinearMap g.log = marked.log ∧
      (∀ z : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot)
        (lieQuotientMap (D.filtration.layerIdeal (s + 1)))
        (D.filtration.realification.polynomialOrbitRealEval w z g) =
          Q.filtration.realification.polynomialOrbitRealEval w z q) ∧
      ∀ z : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ
        (D.filtration.realification.polynomialOrbitRealEval w z g) =
          E.filtration.realification.polynomialOrbitRealEval w z marked :=
  D.exists_prescribed_marked_topQuotientOrbit_lift E.filtration φ hφ Q hQ hsurj q marked
    ((D.topQuotientMarkedOrbit_eq_iff E φ hφ Q hQ QF hQF q marked).mp heq)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration VectorPolynomial

variable {L M ι κ σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s d f nE nF : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (Fmark : RationalFilteredNilmanifold M (s + 1) f)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
  (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
  (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nE)
  (hE : E.filtration = D.filtration.gradedRefiltration W)
  (EF : RationalFilteredNilmanifold
    (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
  (hEF : EF.filtration = Fmark.filtration.gradedRefiltration
    (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))

include hE hEF

theorem refilteredMarkedMap_mem_layer (j : ℕ)
    (x : D.filtration.gradedRefiltrationSubalgebra W) (hx : x ∈ E.filtration.layer j) :
    D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W x ∈ EF.filtration.layer j := by
  rw [hE] at hx
  rw [hEF]
  exact D.filtration.gradedRefiltrationMap_mem_layer Fmark.filtration φ hφ W j x hx

theorem refilteredMarkedMap_layer_surjective
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.filtration.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis b ω hD) ω W.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (j : ℕ) (y : Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))
    (hy : y ∈ EF.filtration.layer j) :
    ∃ x ∈ E.filtration.layer j,
      D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W x = y := by
  rw [hEF] at hy
  obtain ⟨x, hx, heq⟩ := D.filtration.gradedRefiltrationMap_layer_surjective
    Fmark.filtration b ω hD c ν hF φ hφ W hW hsurj j y hy
  exact ⟨x, by rwa [hE], heq⟩

theorem exists_refiltered_prescribed_marked_topQuotientOrbit_lift
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.filtration.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis b ω hD) ω W.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    {nQ : ℕ} (Q : RationalFilteredNilmanifold
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s nQ)
    (hQ : Q.filtration = E.filtration.quotientTop) {w : σ → ℕ}
    (q : Q.filtration.realification.PolynomialOrbit w)
    (marked : EF.filtration.realification.PolynomialOrbit w)
    (hcompat : map
      (realLieHomToRat (realificationLieHom
        (lieQuotientProjection (E.filtration.layerIdeal (s + 1))
          (EF.filtration.layerIdeal (s + 1))
          (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)
          (D.refilteredMarkedMap_mem_layer Fmark φ hφ W E hE EF hEF (s + 1))))).toLinearMap
        q.log =
      map (realLieHomToRat (realificationLieHom
        (lieQuotientMap (EF.filtration.layerIdeal (s + 1))))).toLinearMap marked.log) :
    ∃ g : E.filtration.realification.PolynomialOrbit w,
      E.topQuotientOrbit Q hQ g = q ∧
      map (realLieHomToRat (realificationLieHom
        (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W))).toLinearMap g.log =
          marked.log ∧
      (∀ z : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot)
        (lieQuotientMap (E.filtration.layerIdeal (s + 1)))
        (E.filtration.realification.polynomialOrbitRealEval w z g) =
          Q.filtration.realification.polynomialOrbitRealEval w z q) ∧
      ∀ z : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := EF.filtration.lowerCentralSeries_eq_bot)
        (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)
        (E.filtration.realification.polynomialOrbitRealEval w z g) =
          EF.filtration.realification.polynomialOrbitRealEval w z marked := by
  exact E.exists_prescribed_marked_topQuotientOrbit_lift EF.filtration
    (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)
    (D.refilteredMarkedMap_mem_layer Fmark φ hφ W E hE EF hEF) Q hQ
    (D.refilteredMarkedMap_layer_surjective Fmark φ hφ W E hE EF hEF
      b ω hD c ν hF hW hsurj) q marked hcompat

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d e n m : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (E : RationalFilteredNilmanifold M (s + 1) e)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ E.filtration.layer j)
    (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
    (QF : RationalFilteredNilmanifold (M ⧸ E.filtration.layerIdeal (s + 1)) s m)

theorem topQuotientMarkedMap_basis_logHeight {p : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
    (hQ : Q.GeometryComplexityLE p)
    (hproj : ∀ i j, rationalLogHeight (Q.basis.repr
      (lieQuotientMap (D.filtration.layerIdeal (s + 1)) (D.basis j)) i) ≤ p)
    (hmark : ∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis i)) j) ≤ p)
    (hprojF : ∀ i j, rationalLogHeight (QF.basis.repr
      (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis j)) i) ≤ p)
    (i : Fin n) (j : Fin m) :
    rationalLogHeight (QF.basis.repr (D.topQuotientMarkedMap E φ hφ (Q.basis i)) j) ≤
      quotientInducedMapHeightBudget p := by
  exact lieQuotientProjection_basis_logHeight
    (D.filtration.layerIdeal (s + 1)) (E.filtration.layerIdeal (s + 1))
    D.basis E.basis Q.basis QF.basis φ (hφ (s + 1)) hp
    (by simpa only [Fintype.card_fin] using hD.1)
    (by simpa only [Fintype.card_fin] using hE.1)
    (by simpa only [Fintype.card_fin] using hQ.1)
    (fun i j => hproj j i) hmark (fun i j => hprojF j i) i j

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s d e n m : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (E : RationalFilteredNilmanifold M (s + 1) e)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ E.filtration.layer j)
  (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
  (hQ : Q.filtration = D.filtration.quotientTop)
  (QF : RationalFilteredNilmanifold (M ⧸ E.filtration.layerIdeal (s + 1)) s m)
  (hQF : QF.filtration = E.filtration.quotientTop)

include hQ hQF in

theorem topQuotientMarkedMap_layer_surjective
    (hsurj : ∀ j, ∀ y ∈ E.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (j : ℕ) (y : M ⧸ E.filtration.layerIdeal (s + 1)) (hy : y ∈ QF.filtration.layer j) :
    ∃ x ∈ Q.filtration.layer j, D.topQuotientMarkedMap E φ hφ x = y := by
  rw [hQF] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  obtain ⟨x, hx, hφx⟩ := hsurj j z hz
  refine ⟨lieQuotientMap (D.filtration.layerIdeal (s + 1)) x, ?_, ?_⟩
  · rw [hQ]
    exact ⟨x, hx, rfl⟩
  · exact congrArg (lieQuotientMap (E.filtration.layerIdeal (s + 1))) hφx

include hQ hQF in

theorem topQuotientMarkedMap_real_layer_surjective
    (hsurj : ∀ j, ∀ y ∈ E.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (j : ℕ) (y : ℝ ⊗[ℚ] (M ⧸ E.filtration.layerIdeal (s + 1)))
    (hy : y ∈ QF.filtration.realification.layer j) :
    ∃ x ∈ Q.filtration.realification.layer j,
      realificationLieHom (D.topQuotientMarkedMap E φ hφ) x = y := by
  exact Q.filtration.realificationLieHom_layer_surjective QF.filtration
    (D.topQuotientMarkedMap E φ hφ)
    (D.topQuotientMarkedMap_mem_layer E φ hφ Q hQ QF hQF)
    (D.topQuotientMarkedMap_layer_surjective E φ hφ Q hQ QF hQF hsurj) j y hy

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s d e n m : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (E : RationalFilteredNilmanifold M (s + 1) e)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ E.filtration.layer j)
  (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
  (hQ : Q.filtration = D.filtration.quotientTop)
  (QF : RationalFilteredNilmanifold (M ⧸ E.filtration.layerIdeal (s + 1)) s m)
  (hQF : QF.filtration = E.filtration.quotientTop) {w : σ → ℕ}

noncomputable def markedTopQuotientDiagram (x : D.RealGroup) : Q.Space × E.Space :=
  (QuotientGroup.mk (realificationMap
    (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := Q.filtration.lowerCentralSeries_eq_bot)
    (lieQuotientMap (D.filtration.layerIdeal (s + 1))) x),
   QuotientGroup.mk (realificationMap
    (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ x))

theorem exists_marked_topQuotientOrbit_lift_diagram
    (hsurj : ∀ j, ∀ y ∈ E.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (q : Q.filtration.realification.PolynomialOrbit w)
    (marked : E.filtration.realification.PolynomialOrbit w)
    (heq : D.topQuotientMarkedOrbit E φ hφ Q hQ QF hQF q = E.topQuotientOrbit QF hQF marked) :
    ∃ g : D.filtration.realification.PolynomialOrbit w,
      D.topQuotientOrbit Q hQ g = q ∧
      map (realLieHomToRat (realificationLieHom φ)).toLinearMap g.log = marked.log ∧
      ∀ z : σ → ℝ,
        D.markedTopQuotientDiagram E φ Q
          (D.filtration.realification.polynomialOrbitRealEval w z g) =
        ((QuotientGroup.mk (Q.filtration.realification.polynomialOrbitRealEval w z q) : Q.Space),
         (QuotientGroup.mk (E.filtration.realification.polynomialOrbitRealEval w z marked) : E.Space)) := by
  obtain ⟨g, hg, hm, hqeval, hmeval⟩ :=
    D.exists_marked_topQuotientOrbit_lift_of_quotient_eq E φ hφ Q hQ QF hQF hsurj q marked heq
  refine ⟨g, hg, hm, ?_⟩
  intro z
  simp only [markedTopQuotientDiagram, hqeval z, hmeval z]

theorem exists_marked_topQuotientOrbit_lift_externalFamily
    [PseudoMetricSpace Q.Space] [PseudoMetricSpace E.Space]
    {A : Type*} (K : ℝ≥0) (observable : A → D.RealGroup → ℂ)
    (hrecovery : ∀ a source, positiveImageSlice (D.markedTopQuotientDiagram E φ Q) K
      (observable a) (D.markedTopQuotientDiagram E φ Q source).2
        (D.markedTopQuotientDiagram E φ Q source).1 = observable a source)
    (hsurj : ∀ j, ∀ y ∈ E.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (q : Q.filtration.realification.PolynomialOrbit w)
    (marked : E.filtration.realification.PolynomialOrbit w)
    (heq : D.topQuotientMarkedOrbit E φ hφ Q hQ QF hQF q = E.topQuotientOrbit QF hQF marked) :
    ∃ g : D.filtration.realification.PolynomialOrbit w,
      D.topQuotientOrbit Q hQ g = q ∧
      map (realLieHomToRat (realificationLieHom φ)).toLinearMap g.log = marked.log ∧
      ∀ a (z : σ → ℝ),
        positiveImageSlice (D.markedTopQuotientDiagram E φ Q) K (observable a)
          (QuotientGroup.mk (E.filtration.realification.polynomialOrbitRealEval w z marked))
          (QuotientGroup.mk (Q.filtration.realification.polynomialOrbitRealEval w z q)) =
        observable a (D.filtration.realification.polynomialOrbitRealEval w z g) := by
  obtain ⟨g, hg, hm, hdiagram⟩ :=
    D.exists_marked_topQuotientOrbit_lift_diagram E φ hφ Q hQ QF hQF hsurj q marked heq
  refine ⟨g, hg, hm, ?_⟩
  intro a z
  have h := hrecovery a (D.filtration.realification.polynomialOrbitRealEval w z g)
  rw [hdiagram z] at h
  exact h

theorem topQuotientMarkedOrbit_realEval
    (q : Q.filtration.realification.PolynomialOrbit w) (x : σ → ℝ) :
    QF.filtration.realification.polynomialOrbitRealEval w x
      (D.topQuotientMarkedOrbit E φ hφ Q hQ QF hQF q) =
    realificationMap (hnil := Q.filtration.lowerCentralSeries_eq_bot)
      (hM := QF.filtration.lowerCentralSeries_eq_bot) (D.topQuotientMarkedMap E φ hφ)
      (Q.filtration.realification.polynomialOrbitRealEval w x q) := by
  apply NilpotentLieBCHGroup.ext
  change eval₂ x (map (realLieHomToRat
    (realificationLieHom (D.topQuotientMarkedMap E φ hφ))).toLinearMap q.log) = _
  exact eval₂_map (realificationLieHom (D.topQuotientMarkedMap E φ hφ)).toLinearMap x q.log

theorem topQuotientMarkedOrbit_left_mul_of_map_eq_one
    (q : Q.filtration.realification.PolynomialOrbit w) (z : Q.RealGroup)
    (hz : realificationMap (hnil := Q.filtration.lowerCentralSeries_eq_bot)
      (hM := QF.filtration.lowerCentralSeries_eq_bot) (D.topQuotientMarkedMap E φ hφ) z = 1) :
    D.topQuotientMarkedOrbit E φ hφ Q hQ QF hQF
        (Q.filtration.realification.constantGroupOrbit w z * q) =
      D.topQuotientMarkedOrbit E φ hφ Q hQ QF hQF q := by
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  apply sub_eq_zero.mp
  apply eq_zero_of_eval₂_zero (K := ℝ)
  intro x
  rw [map_sub]
  apply sub_eq_zero.mpr
  have he : QF.filtration.realification.polynomialOrbitRealEval w x
      (D.topQuotientMarkedOrbit E φ hφ Q hQ QF hQF
        (Q.filtration.realification.constantGroupOrbit w z * q)) =
      QF.filtration.realification.polynomialOrbitRealEval w x
        (D.topQuotientMarkedOrbit E φ hφ Q hQ QF hQF q) := by
    rw [D.topQuotientMarkedOrbit_realEval E φ hφ Q hQ QF hQF,
      D.topQuotientMarkedOrbit_realEval E φ hφ Q hQ QF hQF,
      map_mul, polynomialOrbitRealEval_constantGroupOrbit, map_mul, hz, one_mul]
  exact congrArg NilpotentLieBCHGroup.coord he

theorem exists_marked_topQuotientOrbit_left_translated_lift_diagram
    (hsurj : ∀ j, ∀ y ∈ E.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (q : Q.filtration.realification.PolynomialOrbit w)
    (marked : E.filtration.realification.PolynomialOrbit w)
    (heq : D.topQuotientMarkedOrbit E φ hφ Q hQ QF hQF q = E.topQuotientOrbit QF hQF marked)
    (z : Q.RealGroup)
    (hz : realificationMap (hnil := Q.filtration.lowerCentralSeries_eq_bot)
      (hM := QF.filtration.lowerCentralSeries_eq_bot) (D.topQuotientMarkedMap E φ hφ) z = 1) :
    ∃ g : D.filtration.realification.PolynomialOrbit w,
      D.topQuotientOrbit Q hQ g = Q.filtration.realification.constantGroupOrbit w z * q ∧
      map (realLieHomToRat (realificationLieHom φ)).toLinearMap g.log = marked.log ∧
      ∀ x : σ → ℝ,
        D.markedTopQuotientDiagram E φ Q
          (D.filtration.realification.polynomialOrbitRealEval w x g) =
        ((QuotientGroup.mk (z * Q.filtration.realification.polynomialOrbitRealEval w x q) : Q.Space),
         (QuotientGroup.mk (E.filtration.realification.polynomialOrbitRealEval w x marked) : E.Space)) := by
  have heq' := (D.topQuotientMarkedOrbit_left_mul_of_map_eq_one E φ hφ Q hQ QF hQF q z hz).trans heq
  obtain ⟨g, hg, hm, hdiag⟩ := D.exists_marked_topQuotientOrbit_lift_diagram
    E φ hφ Q hQ QF hQF hsurj (Q.filtration.realification.constantGroupOrbit w z * q) marked heq'
  refine ⟨g, hg, hm, ?_⟩
  intro x
  simpa only [map_mul, polynomialOrbitRealEval_constantGroupOrbit] using hdiag x

end Erdos3.RationalFilteredNilmanifold

end

end OAI
