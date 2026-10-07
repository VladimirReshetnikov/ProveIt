import OAI.Combinatorics.Progressions.Dynamics.UniformExternalNetScalarBudget
import OAI.Combinatorics.Progressions.Estimates.FixedObservableCorrelation
import OAI.Combinatorics.Progressions.Estimates.McShaneEnvelope
import OAI.Combinatorics.Progressions.Estimates.PositiveReconstruction
import OAI.Combinatorics.Progressions.Nilpotent.LocalMajorDenseSliceNiltest

namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {X Y : Type*} [Nonempty X] [PseudoMetricSpace Y]
  (φ : X → Y) (L : ℝ≥0)

noncomputable def positiveImageExtension (f : X → ℂ) (y : Y) : ℂ :=
  positiveClip (mcShaneEnvelope φ L (fun x => (f x).re) y)

omit [Nonempty X] in
theorem positiveImageExtension_unit_interval (f : X → ℂ) (y : Y) :
    (positiveImageExtension φ L f y).im = 0 ∧
      0 ≤ (positiveImageExtension φ L f y).re ∧ (positiveImageExtension φ L f y).re ≤ 1 :=
  positiveClip_unit_interval _

omit [Nonempty X] in
theorem positiveImageExtension_norm_le_one (f : X → ℂ) (y : Y) :
    ‖positiveImageExtension φ L f y‖ ≤ 1 := norm_positiveClip_le_one _

theorem positiveImageExtension_lipschitz (f : X → ℂ) (hf : ∀ x, 0 ≤ (f x).re) :
    LipschitzWith L (positiveImageExtension φ L f) := by
  unfold positiveImageExtension
  have h := positiveClip_lipschitz.comp
    (Complex.isometry_ofReal.lipschitzWith.comp (mcShaneEnvelope_lipschitz φ L _ hf))
  simpa only [Function.comp_def, one_mul] using h

theorem positiveImageExtension_eq (f : X → ℂ)
    (hf : ∀ x, (f x).im = 0 ∧ 0 ≤ (f x).re ∧ (f x).re ≤ 1)
    (hLip : ∀ x z, ‖f x - f z‖ ≤ L * dist (φ x) (φ z)) (x : X) :
    positiveImageExtension φ L f (φ x) = f x := by
  have hreal : ∀ x z, |(f x).re - (f z).re| ≤ L * dist (φ x) (φ z) :=
    fun x z => (Complex.abs_re_le_norm (f x - f z)).trans (hLip x z)
  have heq : ((f x).re : ℂ) = f x := Complex.ext rfl (hf x).1.symm
  unfold positiveImageExtension
  rw [mcShaneEnvelope_eq φ L _ (fun x => (hf x).2.1) hreal, heq,
    positiveClip_eq_self _ (hf x)]

theorem positiveImageExtension_nonexpansive (f g : X → ℂ)
    (hf : ∀ x, 0 ≤ (f x).re) (hg : ∀ x, 0 ≤ (g x).re)
    {δ : ℝ} (hfg : ∀ x, ‖f x - g x‖ ≤ δ) (y : Y) :
    ‖positiveImageExtension φ L f y - positiveImageExtension φ L g y‖ ≤ δ := by
  have henv := mcShaneEnvelope_abs_sub_le φ L (fun x => (f x).re) (fun x => (g x).re)
    hf hg (fun x => (Complex.abs_re_le_norm (f x - g x)).trans (hfg x)) y
  have hclip := positiveClip_lipschitz.dist_le_mul
    (mcShaneEnvelope φ L (fun x => (f x).re) y : ℂ)
    (mcShaneEnvelope φ L (fun x => (g x).re) y : ℂ)
  have hbound : ‖positiveImageExtension φ L f y - positiveImageExtension φ L g y‖ ≤
      |mcShaneEnvelope φ L (fun x => (f x).re) y - mcShaneEnvelope φ L (fun x => (g x).re) y| := by
    simpa only [positiveImageExtension, NNReal.coe_one, one_mul, dist_eq_norm,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hclip
  exact hbound.trans henv

theorem positiveImageExtension_bound_of_reconstruction (f : X → ℂ) (v : Y → ℂ)
    (hv : LipschitzWith L v) (heval : ∀ x, v (φ x) = f x)
    (hf : ∀ x, (f x).im = 0 ∧ 0 ≤ (f x).re ∧ (f x).re ≤ 1) :
    LipschitzWith L (positiveImageExtension φ L f) ∧
      (∀ y, (positiveImageExtension φ L f y).im = 0 ∧
        0 ≤ (positiveImageExtension φ L f y).re ∧ (positiveImageExtension φ L f y).re ≤ 1) ∧
      (∀ y, ‖positiveImageExtension φ L f y‖ ≤ 1) ∧
      ∀ x, positiveImageExtension φ L f (φ x) = f x := by
  refine ⟨positiveImageExtension_lipschitz φ L f (fun x => (hf x).2.1),
    positiveImageExtension_unit_interval φ L f, positiveImageExtension_norm_le_one φ L f, ?_⟩
  apply positiveImageExtension_eq φ L f hf
  intro x z
  simpa only [dist_eq_norm, heval] using hv.dist_le_mul (φ x) (φ z)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {X Y Z : Type*} [Nonempty X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]
  (φ : X → Y × Z) (L : ℝ≥0)

noncomputable def positiveImageSlice (f : X → ℂ) (z : Z) (y : Y) : ℂ :=
  positiveImageExtension φ L f (y, z)

theorem positiveImageSlice_lipschitz (f : X → ℂ) (hf : ∀ x, 0 ≤ (f x).re) (z : Z) :
    LipschitzWith L (positiveImageSlice φ L f z) := by
  apply LipschitzWith.of_dist_le_mul
  intro y y'
  have h := (positiveImageExtension_lipschitz φ L f hf).dist_le_mul (y, z) (y', z)
  simpa only [positiveImageSlice, Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using h

theorem positiveImageSlice_eq (f : X → ℂ)
    (hf : ∀ x, (f x).im = 0 ∧ 0 ≤ (f x).re ∧ (f x).re ≤ 1)
    (hLip : ∀ x z, ‖f x - f z‖ ≤ L * dist (φ x) (φ z)) (x : X) :
    positiveImageSlice φ L f (φ x).2 (φ x).1 = f x :=
  positiveImageExtension_eq φ L f hf hLip x

theorem positiveImageSlice_parameter_bound (f g : X → ℂ)
    (hf : ∀ x, 0 ≤ (f x).re) (hg : ∀ x, 0 ≤ (g x).re)
    {δ : ℝ} (hfg : ∀ x, ‖f x - g x‖ ≤ δ) (z z' : Z) (y : Y) :
    ‖positiveImageSlice φ L f z y - positiveImageSlice φ L g z' y‖ ≤
      δ + L * dist z z' := by
  have hleft := positiveImageExtension_nonexpansive φ L f g hf hg hfg (y, z)
  have hright : ‖positiveImageSlice φ L g z y - positiveImageSlice φ L g z' y‖ ≤
      L * dist z z' := by
    have h := (positiveImageExtension_lipschitz φ L g hg).dist_le_mul (y, z) (y, z')
    simpa only [positiveImageSlice, Prod.dist_eq, dist_self, max_eq_right dist_nonneg,
      dist_eq_norm] using h
  exact (norm_sub_le_norm_sub_add_norm_sub (positiveImageSlice φ L f z y) (positiveImageSlice φ L g z y)
    (positiveImageSlice φ L g z' y)).trans (add_le_add hleft hright)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem exists_stable_positive_reconstruction {Θ X Y : Type*}
    [Nonempty X] [PseudoMetricSpace Y] (φ : X → Y) (f : Θ → X → ℂ) (L : ℝ≥0)
    (hf : ∀ θ x, (f θ x).im = 0 ∧ 0 ≤ (f θ x).re ∧ (f θ x).re ≤ 1)
    (hrec : ∀ θ, ∃ (v : Y → ℂ) (K : ℝ≥0), K ≤ L ∧ LipschitzWith K v ∧
      ∀ x, v (φ x) = f θ x) :
    ∃ V : Θ → Y → ℂ,
      (∀ θ, LipschitzWith L (V θ)) ∧
      (∀ θ y, (V θ y).im = 0 ∧ 0 ≤ (V θ y).re ∧ (V θ y).re ≤ 1) ∧
      (∀ θ y, ‖V θ y‖ ≤ 1) ∧ (∀ θ x, V θ (φ x) = f θ x) ∧
      ∀ θ θ' δ, (∀ x, ‖f θ x - f θ' x‖ ≤ δ) → ∀ y, ‖V θ y - V θ' y‖ ≤ δ := by
  refine ⟨fun θ => positiveImageExtension φ L (f θ),
    fun θ => positiveImageExtension_lipschitz φ L (f θ) (fun x => (hf θ x).2.1),
    fun θ => positiveImageExtension_unit_interval φ L (f θ),
    fun θ => positiveImageExtension_norm_le_one φ L (f θ), ?_, ?_⟩
  · intro θ
    obtain ⟨v, K, hK, hv, heval⟩ := hrec θ
    exact (positiveImageExtension_bound_of_reconstruction φ L (f θ) v
      (hv.weaken hK) heval (hf θ)).2.2.2
  · intro θ θ' δ hdiff y
    exact positiveImageExtension_nonexpansive φ L (f θ) (f θ')
      (fun x => (hf θ x).2.1) (fun x => (hf θ' x).2.1) hdiff y

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {X Y Z : Type*} [Nonempty X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]
  (φ : X → Y × Z) (K : ℝ≥0) (f : X → ℂ)
  (hf : ∀ x, 0 ≤ (f x).re)
  (hrecovery : ∀ x, positiveImageSlice φ K f (φ x).2 (φ x).1 = f x)

include hf hrecovery

theorem positiveImageExtension_reconstructs_of_positiveImageSlice_eq :
    LipschitzWith K (positiveImageExtension φ K f) ∧
      ∀ x, positiveImageExtension φ K f (φ x) = f x := by
  refine ⟨positiveImageExtension_lipschitz φ K f hf, ?_⟩
  intro x
  simpa only [positiveImageSlice, Prod.mk.eta] using hrecovery x

theorem exists_lipschitz_reconstruction_of_positiveImageSlice_eq :
    ∃ (v : Y × Z → ℂ) (K' : ℝ≥0), K' ≤ K ∧ LipschitzWith K' v ∧
      ∀ x, v (φ x) = f x := by
  exact ⟨positiveImageExtension φ K f, K, le_rfl,
    positiveImageExtension_reconstructs_of_positiveImageSlice_eq φ K f hf hrecovery⟩

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem exists_external_test_net {O A R X Y Z IO IA IZ : Type*}
    [Nonempty X] [PseudoMetricSpace A] [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    [Fintype IO] [Fintype IA] [Fintype R] [Fintype IZ]
    (φ : X → Y × Z) (F : O → A → R → X → ℂ) (L M : ℝ≥0)
    (hpositive : ∀ o a r x, (F o a r x).im = 0 ∧ 0 ≤ (F o a r x).re ∧ (F o a r x).re ≤ 1)
    (hreconstruct : ∀ o a r, ∃ (v : Y × Z → ℂ) (K : ℝ≥0), K ≤ L ∧ LipschitzWith K v ∧
      ∀ x, v (φ x) = F o a r x)
    (hvariation : ∀ o a a' r x, ‖F o a r x - F o a' r x‖ ≤ M * dist a a')
    (oc : IO → O) (ac : IA → A) (zc : IZ → Z) {δO δA δZ : ℝ}
    (hO : ∀ o, ∃ i, ∀ a r x, ‖F o a r x - F (oc i) a r x‖ ≤ δO)
    (hA : ∀ a, ∃ i, dist a (ac i) ≤ δA) (hZ : ∀ z, ∃ i, dist z (zc i) ≤ δZ) :
    let n := Fintype.card IO * Fintype.card IA * Fintype.card R * Fintype.card IZ
    ∃ centers : Fin n → Y → ℂ,
      (∀ i, LipschitzWith L (centers i)) ∧
      (∀ i y, (centers i y).im = 0 ∧ 0 ≤ (centers i y).re ∧ (centers i y).re ≤ 1) ∧
      (∀ i y, ‖centers i y‖ ≤ 1) ∧
      (∀ o a r x, positiveImageSlice φ L (F o a r) (φ x).2 (φ x).1 = F o a r x) ∧
      ∀ o a r z, ∃ i, ∀ y,
        ‖positiveImageSlice φ L (F o a r) z y - centers i y‖ ≤ δO + M * δA + L * δZ := by
  classical
  let I := IO × IA × R × IZ
  let n := Fintype.card IO * Fintype.card IA * Fintype.card R * Fintype.card IZ
  have hcard : Fintype.card I = n := by simp only [I, n, Fintype.card_prod, Nat.mul_assoc]
  let e : I ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let centers : Fin n → Y → ℂ := fun i =>
    positiveImageSlice φ L (F (oc (e.symm i).1) (ac (e.symm i).2.1) (e.symm i).2.2.1)
      (zc (e.symm i).2.2.2)
  refine ⟨centers, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact positiveImageSlice_lipschitz φ L _ (fun x => (hpositive _ _ _ x).2.1) _
  · intro i y
    exact positiveImageExtension_unit_interval φ L _ _
  · intro i y
    exact positiveImageExtension_norm_le_one φ L _ _
  · intro o a r x
    obtain ⟨v, K, hK, hv, heval⟩ := hreconstruct o a r
    exact (positiveImageExtension_bound_of_reconstruction φ L (F o a r) v
      (hv.weaken hK) heval (hpositive o a r)).2.2.2 x
  · intro o a r z
    obtain ⟨io, hio⟩ := hO o
    obtain ⟨ia, hia⟩ := hA a
    obtain ⟨iz, hiz⟩ := hZ z
    refine ⟨e (io, ia, r, iz), ?_⟩
    intro y
    have hsource : ∀ x, ‖F o a r x - F (oc io) (ac ia) r x‖ ≤ δO + M * δA := by
      intro x
      exact (norm_sub_le_norm_sub_add_norm_sub (F o a r x) (F (oc io) a r x)
        (F (oc io) (ac ia) r x)).trans (add_le_add (hio a r x)
          ((hvariation (oc io) a (ac ia) r x).trans (mul_le_mul_of_nonneg_left hia M.coe_nonneg)))
    have h := (positiveImageSlice_parameter_bound φ L (F o a r) (F (oc io) (ac ia) r)
      (fun x => (hpositive _ _ _ x).2.1) (fun x => (hpositive _ _ _ x).2.1) hsource z (zc iz) y).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hiz L.coe_nonneg))
    simpa only [centers, Equiv.symm_apply_apply] using h

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct

namespace NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def adaptedPolynomialRealValueHom (t : σ → ℝ) :
    (F.realification.adaptedPolynomialFiltration w).Group →* F.realification.Group :=
  (F.realification.polynomialOrbitRealEval w t).comp (F.realification.adaptedBCHToOrbit w)

theorem adaptedPolynomialRealValueHom_coord (t : σ → ℝ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    (F.adaptedPolynomialRealValueHom w t g).coord =
      eval₂ t (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) := rfl

theorem adaptedPolynomialRealValueHom_constant (t : σ → ℝ) (κ : F.realification.Group) :
    F.adaptedPolynomialRealValueHom w t (F.realification.adaptedConstantGroupHom w κ) = κ := by
  apply NilpotentLieBCHGroup.ext
  rw [adaptedPolynomialRealValueHom_coord, F.realification.adaptedConstantGroupHom_log,
    eval₂_monomial, Finsupp.prod_zero_index, one_smul]

end NilpotentLieFiltration

namespace RationalFilteredNilmanifold

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ)

theorem lattice_factorization_quotient
    (g E b R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (κ : D.RealGroup) (hκ : κ ∈ D.realLattice)
    (hprod : E * b * R * D.filtration.realification.adaptedConstantGroupHom w κ = g)
    (t : σ → ℝ) :
    (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w t g) : D.Space) =
      QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w t E *
        D.filtration.adaptedPolynomialRealValueHom w t b *
        D.filtration.adaptedPolynomialRealValueHom w t R) := by
  have h := congrArg (D.filtration.adaptedPolynomialRealValueHom w t) hprod
  simp only [map_mul, NilpotentLieFiltration.adaptedPolynomialRealValueHom_constant] at h
  rw [← h]
  exact QuotientGroup.mk_mul_of_mem _ hκ

namespace Niltest

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem evalReal_of_lattice_factorization (T : D.Niltest w)
    (E b R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (κ : D.RealGroup) (hκ : κ ∈ D.realLattice)
    (hprod : E * b * R * D.filtration.realification.adaptedConstantGroupHom w κ =
      ⟨⟨T.orbit.log, T.orbit.property⟩⟩) (t : σ → ℝ) :
    T.evalReal t = T.observable (QuotientGroup.mk
      (D.filtration.adaptedPolynomialRealValueHom w t E *
        D.filtration.adaptedPolynomialRealValueHom w t b *
        D.filtration.adaptedPolynomialRealValueHom w t R)) := by
  exact congrArg T.observable (lattice_factorization_quotient D w _ E b R κ hκ hprod t)

theorem eval_of_lattice_factorization (T : D.Niltest w)
    (E b R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (κ : D.RealGroup) (hκ : κ ∈ D.realLattice)
    (hprod : E * b * R * D.filtration.realification.adaptedConstantGroupHom w κ =
      ⟨⟨T.orbit.log, T.orbit.property⟩⟩) (x : σ → ℤ) :
    T.eval x = T.observable (QuotientGroup.mk
      (D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) E *
        D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) b *
        D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) R)) := by
  rw [← T.evalReal_integer]
  exact evalReal_of_lattice_factorization D w T E b R κ hκ hprod _

end Niltest
end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem observable_change_left (T : D.Niltest w) (a a₀ : D.RealGroup) (x : D.Space) :
    letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
    ‖T.observable (a • x) - T.observable (a₀ • x)‖ ≤ (T.lipBound : ℝ) * dist a a₀ := by
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := D.metricSpace
  have hpoint : dist (a • x) (a₀ • x) ≤ dist a a₀ := by
    have hLip : LipschitzWith 1 (fun a : D.RealGroup => a • x) :=
      quotientMetricSpace_lipschitz_orbit (D.basis.baseChange ℝ) D.realLattice
        D.realLattice_closed_discrete.1 x
    simpa only [NNReal.coe_one, one_mul] using hLip.dist_le_mul a a₀
  calc
    _ ≤ (T.lipBound : ℝ) * dist (a • x) (a₀ • x) := by
      simpa only [dist_eq_norm] using T.lipschitz.dist_le_mul (a • x) (a₀ • x)
    _ ≤ _ := mul_le_mul_of_nonneg_left hpoint T.lipBound.coe_nonneg

theorem observable_freeze_factors (T : D.Niltest w) (a a₀ b r r₀ : D.RealGroup)
    (hr : (QuotientGroup.mk r : D.Space) = QuotientGroup.mk r₀) :
    letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
    ‖T.observable (QuotientGroup.mk (a * b * r)) -
      T.observable (QuotientGroup.mk (a₀ * b * r₀))‖ ≤ (T.lipBound : ℝ) * dist a a₀ := by
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  have heq : T.observable (QuotientGroup.mk (a * b * r)) =
      T.observable (QuotientGroup.mk (a * b * r₀)) :=
    congrArg (fun x : D.Space => T.observable ((a * b) • x)) hr
  rw [heq, mul_assoc a b r₀, mul_assoc a₀ b r₀]
  exact T.observable_change_left a a₀ (QuotientGroup.mk (b * r₀))

theorem eval_freeze_of_lattice_factorization (T : D.Niltest w)
    (E b R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (κ : D.RealGroup) (hκ : κ ∈ D.realLattice)
    (hprod : E * b * R * D.filtration.realification.adaptedConstantGroupHom w κ =
      ⟨⟨T.orbit.log, T.orbit.property⟩⟩) (x : σ → ℤ) (a₀ r₀ : D.RealGroup)
    {p δ : ℝ} (hT : T.ComplexityLE p)
    (hr : (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) R) : D.Space) =
      QuotientGroup.mk r₀)
    (hE : letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
      dist (D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) E) a₀ ≤ δ) :
    ‖T.eval x - T.observable (QuotientGroup.mk
      (a₀ * D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) b * r₀))‖ ≤
      Real.exp p * δ := by
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  have hLip : (T.lipBound : ℝ) ≤ Real.exp p := by
    have hb := T.observable_budget hT
    linarith [T.normBound.coe_nonneg]
  rw [eval_of_lattice_factorization D w T E b R κ hκ hprod x]
  exact (T.observable_freeze_factors _ a₀ _ _ r₀ hr).trans
    ((mul_le_mul_of_nonneg_right hLip dist_nonneg).trans
      (mul_le_mul_of_nonneg_left hE (Real.exp_pos p).le))

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L s d)

theorem frozen_observable_change_left (S : D.Space → ℂ) {ℓ : ℝ≥0}
    (hS : letI := D.metricSpace; LipschitzWith ℓ S) (a a' b r : D.RealGroup) :
    letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
      (D.basis.baseChange ℝ)
    ‖S (QuotientGroup.mk (a * b * r)) - S (QuotientGroup.mk (a' * b * r))‖ ≤
      (ℓ : ℝ) * dist a a' := by
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let := D.metricSpace
  let x : D.Space := QuotientGroup.mk (b * r)
  have hLip : LipschitzWith 1 (fun a : D.RealGroup => a • x) :=
    quotientMetricSpace_lipschitz_orbit (D.basis.baseChange ℝ) D.realLattice
      D.realLattice_closed_discrete.1 x
  have hpoint : dist (a • x) (a' • x) ≤ dist a a' := by
    simpa only [NNReal.coe_one, one_mul] using hLip.dist_le_mul a a'
  have h := (hS.dist_le_mul (a • x) (a' • x)).trans
    (mul_le_mul_of_nonneg_left hpoint ℓ.coe_nonneg)
  simpa only [x, MulAction.Quotient.smul_mk, smul_eq_mul, mul_assoc, dist_eq_norm] using h

theorem frozen_observable_variation (S S' : D.Space → ℂ) {ℓ : ℝ≥0}
    (hS' : letI := D.metricSpace; LipschitzWith ℓ S') {δ : ℝ}
    (hSS' : ∀ x, ‖S x - S' x‖ ≤ δ) (a a' b r : D.RealGroup) :
    letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
      (D.basis.baseChange ℝ)
    ‖S (QuotientGroup.mk (a * b * r)) - S' (QuotientGroup.mk (a' * b * r))‖ ≤
      δ + (ℓ : ℝ) * dist a a' := by
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  exact (norm_sub_le_norm_sub_add_norm_sub (S (QuotientGroup.mk (a * b * r))) (S' (QuotientGroup.mk (a * b * r)))
    (S' (QuotientGroup.mk (a' * b * r)))).trans
    (add_le_add (hSS' _) (D.frozen_observable_change_left S' hS' a a' b r))

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_frozen_external_test_net {L O R X Y Z IO IA IZ : Type*}
    [LieRing L] [LieAlgebra ℚ L] [Nonempty X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    [Fintype IO] [Fintype IA] [Fintype R] [Fintype IZ]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (φ : X → Y × Z)
    (b : X → D.RealGroup) (S : O → D.Space → ℂ) (A : Set D.RealGroup) (r : R → D.RealGroup)
    (K ℓ : ℝ≥0) (hS : ∀ o, letI := D.metricSpace; LipschitzWith ℓ (S o))
    (hpositive : ∀ o x, (S o x).im = 0 ∧ 0 ≤ (S o x).re ∧ (S o x).re ≤ 1)
    (hreconstruct : ∀ o (a : A) j, ∃ (v : Y × Z → ℂ) (C : ℝ≥0),
      C ≤ K ∧ LipschitzWith C v ∧ ∀ x, v (φ x) = S o (QuotientGroup.mk (a.val * b x * r j)))
    (oc : IO → O) (ac : IA → A) (zc : IZ → Z) {δO δA δZ : ℝ}
    (hO : ∀ o, ∃ i, ∀ x, ‖S o x - S (oc i) x‖ ≤ δO)
    (hA :
      letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
        (D.basis.baseChange ℝ)
      ∀ a : A, ∃ i, dist a (ac i) ≤ δA)
    (hZ : ∀ z, ∃ i, dist z (zc i) ≤ δZ) :
    let F := fun o (a : A) j x => S o (QuotientGroup.mk (a.val * b x * r j))
    let n := Fintype.card IO * Fintype.card IA * Fintype.card R * Fintype.card IZ
    ∃ centers : Fin n → Y → ℂ,
      (∀ i, LipschitzWith K (centers i)) ∧
      (∀ i y, (centers i y).im = 0 ∧ 0 ≤ (centers i y).re ∧ (centers i y).re ≤ 1) ∧
      (∀ i y, ‖centers i y‖ ≤ 1) ∧
      (∀ o a j x, positiveImageSlice φ K (F o a j) (φ x).2 (φ x).1 =
        S o (QuotientGroup.mk (a.val * b x * r j))) ∧
      ∀ o a j z, ∃ i, ∀ y,
        ‖positiveImageSlice φ K (F o a j) z y - centers i y‖ ≤ δO + ℓ * δA + K * δZ := by
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let F := fun o (a : A) j x => S o (QuotientGroup.mk (a.val * b x * r j))
  have hvariation : ∀ o (a a' : A) j x, ‖F o a j x - F o a' j x‖ ≤ ℓ * dist a a' := by
    intro o a a' j x
    exact D.frozen_observable_change_left (S o) (hS o) a.val a'.val (b x) (r j)
  exact exists_external_test_net φ F K ℓ (fun o a j x => hpositive o _)
    hreconstruct hvariation oc ac zc
    (fun o => by obtain ⟨i, hi⟩ := hO o; exact ⟨i, fun a j x => hi _⟩) hA hZ

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_controlled_native_external_net (s t r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M O R IO X Y : Type*}
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      [Fintype IO] [Fintype R] [Nonempty X] [PseudoMetricSpace Y] {d e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M t e)
      (B K ℓ : ℝ≥0) {p ε : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      1 ≤ B → (B : ℝ) ≤ Real.exp ((p + 2) ^ r) →
      (K : ℝ) ≤ Real.exp p → (ℓ : ℝ) ≤ Real.exp p →
      0 < ε → 1 / ε ≤ Real.exp p →
      (Fintype.card IO : ℝ) ≤ Real.exp p → (Fintype.card R : ℝ) ≤ Real.exp p →
      ∀ (S : O → D.Space → ℂ) (b : X → D.RealGroup) (r₀ : R → D.RealGroup)
        (φ : X → Y × E.Space) (oc : IO → O),
      (∀ o, letI := D.metricSpace; LipschitzWith ℓ (S o)) →
      (∀ o x, (S o x).im = 0 ∧ 0 ≤ (S o x).re ∧ (S o x).re ≤ 1) →
      (∀ o, ∃ i, ∀ x, ‖S o x - S (oc i) x‖ ≤ ε / 3) →
      (∀ o (a : coordinateBox (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
          (D.basis.baseChange ℝ) B) j,
        ∃ (v : Y × E.Space → ℂ) (K' : ℝ≥0), K' ≤ K ∧
          (letI := E.metricSpace; LipschitzWith K' v) ∧
          ∀ x, v (φ x) = S o (QuotientGroup.mk (a.val * b x * r₀ j))) →
      letI := E.metricSpace
      let A := coordinateBox (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
        (D.basis.baseChange ℝ) B
      let F := fun o (a : A) j x => S o (QuotientGroup.mk (a.val * b x * r₀ j))
      ∃ n : ℕ, (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ ∃ centers : Fin n → Y → ℂ,
        (∀ i, LipschitzWith K (centers i)) ∧
        (∀ i y, (centers i y).im = 0 ∧ 0 ≤ (centers i y).re ∧ (centers i y).re ≤ 1) ∧
        (∀ i y, ‖centers i y‖ ≤ 1) ∧
        (∀ o a j x, positiveImageSlice φ K (F o a j) (φ x).2 (φ x).1 = F o a j x) ∧
        ∀ o a j z, ∃ i, ∀ y, ‖positiveImageSlice φ K (F o a j) z y - centers i y‖ ≤ ε := by
  obtain ⟨cA, _, hgroup⟩ := exists_native_group_parameter_cover s r
  obtain ⟨cZ, _, hquot⟩ := exists_native_quotient_parameter_cover t
  let X : Polynomial ℕ := Polynomial.X
  let T := 2 * X + 7
  let P := 2 * X + (T + Polynomial.C cA) ^ cA + (T + Polynomial.C cZ) ^ cZ
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L M O R IO X₀ Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d e D E B K ℓ p ε
    hp hD hE hB hBp hK hℓ hε hεinv hIO hR S b r₀ φ oc hS hpositive hO hreconstruct
  let q := 2 * p + 7
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hq : 0 ≤ q := hp.trans hpq
  have hBq : (B : ℝ) ≤ Real.exp ((q + 2) ^ r) := hBp.trans
    (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by linarith) r))
  obtain ⟨nA, _, hnA, ac, hAcov⟩ := hgroup D B hq (hD.mono D hpq) hB hBq
    (externalNetMesh_pos ℓ hε) (externalNetMesh_inverse_bound ℓ hε hp hℓ hεinv)
  obtain ⟨nZ, _, hnZ, zc, hZcov⟩ := hquot E hq (hE.mono E hpq)
    (externalNetMesh_pos K hε) (externalNetMesh_inverse_bound K hε hp hK hεinv)
  let := E.metricSpace
  have hnet := D.exists_frozen_external_test_net φ b S
    (coordinateBox (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ) B)
    r₀ K ℓ hS hpositive hreconstruct oc ac zc hO hAcov hZcov
  dsimp only at hnet
  obtain ⟨centers, hLip, hunit, hcap, heval, hcover⟩ := hnet
  have hfinal : 2 * p + (q + cA) ^ cA + (q + cZ) ^ cZ ≤ (p + C) ^ C := by
    simpa [P, T, X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hcount : ((Fintype.card IO * nA * Fintype.card R * nZ : ℕ) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    push_cast
    calc
      _ ≤ Real.exp p * Real.exp ((q + cA) ^ cA) * Real.exp p * Real.exp ((q + cZ) ^ cZ) := by
        gcongr
      _ = Real.exp (2 * p + (q + cA) ^ cA + (q + cZ) ^ cZ) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr hfinal
  refine ⟨_, ?_, centers, hLip, hunit, hcap, heval, ?_⟩
  · simpa only [Fintype.card_fin] using hcount
  · intro o a j z
    obtain ⟨i, hi⟩ := hcover o a j z
    exact ⟨i, fun y => (hi y).trans (externalNetMesh_error K ℓ hε.le)⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_controlled_native_external_nets (s t r netExponent : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M O R X Y : Type*}
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      [Fintype R] [Nonempty X] [PseudoMetricSpace Y] {d e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M t e)
      (B K ℓ : ℝ≥0) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      1 ≤ B → (B : ℝ) ≤ Real.exp ((p + 2) ^ r) →
      (K : ℝ) ≤ Real.exp p → (ℓ : ℝ) ≤ Real.exp p →
      (Fintype.card R : ℝ) ≤ Real.exp p →
      ∀ (S : O → D.Space → ℂ) (b : X → D.RealGroup) (r₀ : R → D.RealGroup)
        (φ : X → Y × E.Space),
      (∀ o, letI := D.metricSpace; LipschitzWith ℓ (S o)) →
      (∀ o x, (S o x).im = 0 ∧ 0 ≤ (S o x).re ∧ (S o x).re ≤ 1) →
      (∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
        (n : ℝ) ≤ Real.exp ((p + Real.log (1 / η) + netExponent) ^ netExponent) ∧
        ∃ oc : Fin n → O, ∀ o, ∃ i, ∀ x, ‖S o x - S (oc i) x‖ ≤ η) →
      (∀ o (a : coordinateBox (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
          (D.basis.baseChange ℝ) B) j,
        ∃ (v : Y × E.Space → ℂ) (K' : ℝ≥0), K' ≤ K ∧
          (letI := E.metricSpace; LipschitzWith K' v) ∧
          ∀ x, v (φ x) = S o (QuotientGroup.mk (a.val * b x * r₀ j))) →
      letI := E.metricSpace
      let A := coordinateBox (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
        (D.basis.baseChange ℝ) B
      let F := fun o (a : A) j x => S o (QuotientGroup.mk (a.val * b x * r₀ j))
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ n : ℕ, (n : ℝ) ≤ Real.exp ((p + Real.log (1 / ε) + C) ^ C) ∧ ∃ centers : Fin n → Y → ℂ,
        (∀ i, LipschitzWith K (centers i)) ∧
        (∀ i y, (centers i y).im = 0 ∧ 0 ≤ (centers i y).re ∧ (centers i y).re ≤ 1) ∧
        (∀ i y, ‖centers i y‖ ≤ 1) ∧
        (∀ o a j x, positiveImageSlice φ K (F o a j) (φ x).2 (φ x).1 = F o a j x) ∧
        ∀ o a j z, ∃ i, ∀ y, ‖positiveImageSlice φ K (F o a j) z y - centers i y‖ ≤ ε := by
  obtain ⟨localExponent, _, hnet⟩ := exists_controlled_native_external_net s t r
  obtain ⟨C, hC, hscalar⟩ := exists_uniformExternalNetScalarBudget netExponent localExponent
  refine ⟨C, hC, ?_⟩
  intro L M O R X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d e D E B K ℓ p
    hp hD hE hB hBp hK hℓ hR S b r₀ φ hS hpositive hO hreconstruct
  let := E.metricSpace
  dsimp only
  intro ε hε hε1
  obtain ⟨q, hq, hpq, hlogq, hmemberq, hqC⟩ := hscalar p ε hp hε hε1
  obtain ⟨nO, hnO, oc, hcoverO⟩ := hO (ε / 3) (by positivity) (by linarith)
  have hexp := Real.exp_le_exp.mpr hpq
  have hBq : (B : ℝ) ≤ Real.exp ((q + 2) ^ r) :=
    hBp.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by linarith) r))
  have hεinv : 1 / ε ≤ Real.exp q := by
    calc
      1 / ε = Real.exp (Real.log (1 / ε)) := (Real.exp_log (by positivity)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlogq
  have hnOq : (Fintype.card (Fin nO) : ℝ) ≤ Real.exp q := by
    simpa only [Fintype.card_fin] using hnO.trans (Real.exp_le_exp.mpr hmemberq)
  obtain ⟨n, hn, centers, hLip, hunit, hcap, heval, hcover⟩ :=
    hnet D E B K ℓ hq (hD.mono D hpq) (hE.mono E hpq)
      hB hBq (hK.trans hexp) (hℓ.trans hexp) hε hεinv hnOq (hR.trans hexp)
      S b r₀ φ oc hS hpositive hcoverO hreconstruct
  exact ⟨n, hn.trans (Real.exp_le_exp.mpr hqC), centers, hLip, hunit, hcap, heval, hcover⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_controlled_native_external_nets_of_recovery (s t r netExponent : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M O R X Y : Type*}
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      [Fintype R] [Nonempty X] [PseudoMetricSpace Y] {d e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M t e)
      (B K ℓ : ℝ≥0) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      1 ≤ B → (B : ℝ) ≤ Real.exp ((p + 2) ^ r) →
      (K : ℝ) ≤ Real.exp p → (ℓ : ℝ) ≤ Real.exp p →
      (Fintype.card R : ℝ) ≤ Real.exp p →
      ∀ (S : O → D.Space → ℂ) (b : X → D.RealGroup) (r₀ : R → D.RealGroup)
        (φ : X → Y × E.Space),
      (∀ o, letI := D.metricSpace; LipschitzWith ℓ (S o)) →
      (∀ o x, (S o x).im = 0 ∧ 0 ≤ (S o x).re ∧ (S o x).re ≤ 1) →
      (∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
        (n : ℝ) ≤ Real.exp ((p + Real.log (1 / η) + netExponent) ^ netExponent) ∧
        ∃ oc : Fin n → O, ∀ o, ∃ i, ∀ x, ‖S o x - S (oc i) x‖ ≤ η) →
      letI := E.metricSpace
      let A := coordinateBox (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
        (D.basis.baseChange ℝ) B
      let F := fun o (a : A) j x => S o (QuotientGroup.mk (a.val * b x * r₀ j))
      (∀ o a j x, positiveImageSlice φ K (F o a j) (φ x).2 (φ x).1 = F o a j x) →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ n : ℕ, (n : ℝ) ≤ Real.exp ((p + Real.log (1 / ε) + C) ^ C) ∧ ∃ centers : Fin n → Y → ℂ,
        (∀ i, LipschitzWith K (centers i)) ∧
        (∀ i y, (centers i y).im = 0 ∧ 0 ≤ (centers i y).re ∧ (centers i y).re ≤ 1) ∧
        (∀ i y, ‖centers i y‖ ≤ 1) ∧
        (∀ o a j x, positiveImageSlice φ K (F o a j) (φ x).2 (φ x).1 = F o a j x) ∧
        ∀ o a j z, ∃ i, ∀ y, ‖positiveImageSlice φ K (F o a j) z y - centers i y‖ ≤ ε := by
  obtain ⟨C, hC, hnet⟩ := exists_uniform_controlled_native_external_nets s t r netExponent
  refine ⟨C, hC, ?_⟩
  intro L M O R X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d e D E B K ℓ p
    hp hD hE hB hBp hK hℓ hR S b r₀ φ hS hpositive hO
  let := E.metricSpace
  dsimp only
  intro hrecovery
  apply hnet D E B K ℓ hp hD hE hB hBp hK hℓ hR S b r₀ φ hS hpositive hO
  intro o a j
  exact exists_lipschitz_reconstruction_of_positiveImageSlice_eq φ K
    (fun x => S o (QuotientGroup.mk (a.val * b x * r₀ j)))
    (fun x => (hpositive o _).2.1) (hrecovery o a j)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
