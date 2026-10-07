/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Polynomial.WeightedPolynomialRestriction

namespace OAI

section

namespace Erdos3

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

noncomputable def lieQuotientDescend (I : LieIdeal ℚ L) (f : L →ₗ⁅ℚ⁆ M)
    (hI : ∀ x ∈ I, f x = 0) : (L ⧸ I) →ₗ⁅ℚ⁆ M :=
  { toLinearMap := I.toSubmodule.liftQ f.toLinearMap hI
    map_lie' {x y} := by
      obtain ⟨a, rfl⟩ := lieQuotientMap_surjective I x
      obtain ⟨b, rfl⟩ := lieQuotientMap_surjective I y
      exact f.map_lie a b }

@[simp] theorem lieQuotientDescend_mk (I : LieIdeal ℚ L) (f : L →ₗ⁅ℚ⁆ M)
    (hI : ∀ x ∈ I, f x = 0) (x : L) :
    lieQuotientDescend I f hI (lieQuotientMap I x) = f x := rfl

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t : ℕ}
  (F : NilpotentLieFiltration L s)

def quotientLie (I : LieIdeal ℚ L) (hI : F.layer (t + 1) ≤ I.toSubmodule) :
    NilpotentLieFiltration (L ⧸ I) t where
  layer j := (F.layer j).map (lieQuotientMap I).toLinearMap
  antitone := fun _ _ hij => Submodule.map_mono (F.antitone hij)
  one_eq_top := by
    rw [F.one_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (lieQuotientMap_surjective I)
  lie_mem := by
    rintro i j x y ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨⁅a, b⁆, F.lie_mem ha hb, (lieQuotientMap I).map_lie a b⟩
  terminal := by
    apply bot_unique
    rintro x ⟨a, ha, rfl⟩
    exact (lieQuotientMap_eq_zero I a).mpr (hI ha)

theorem quotientLie_mem (I : LieIdeal ℚ L) (hI : F.layer (t + 1) ≤ I.toSubmodule)
    {j : ℕ} {x : L} (hx : x ∈ F.layer j) :
    lieQuotientMap I x ∈ (F.quotientLie I hI).layer j := ⟨x, hx, rfl⟩

theorem adapted_quotientLie {σ : Type*} (I : LieIdeal ℚ L)
    (hI : F.layer (t + 1) ≤ I.toSubmodule) (w : σ → ℕ)
    {p : VectorPolynomial σ ℚ L} (hp : F.Adapted w p) :
    (F.quotientLie I hI).Adapted w (VectorPolynomial.map (lieQuotientMap I).toLinearMap p) :=
  F.adapted_map (F.quotientLie I hI) (lieQuotientMap I).toLinearMap
    (fun _ _ hx => F.quotientLie_mem I hI hx) w hp

def quotientTop (F : NilpotentLieFiltration L (s + 1)) :
    NilpotentLieFiltration (L ⧸ F.layerIdeal (s + 1)) s :=
  F.quotientLie (F.layerIdeal (s + 1)) le_rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup VectorPolynomial

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (I : LieIdeal ℚ L)
  (hI : F.layer (t + 1) ≤ I.toSubmodule)

noncomputable def quotientStepHom : F.Group →* (F.quotientLie I hI).Group :=
  mapOfSteps (lieQuotientMap I)

@[simp] theorem quotientStepHom_coord (g : F.Group) :
    (F.quotientStepHom I hI g).coord = lieQuotientMap I g.coord := rfl

theorem quotientStepHom_surjective : Function.Surjective (F.quotientStepHom I hI) :=
  mapOfSteps_surjective _ (lieQuotientMap_surjective I)

theorem quotientStepHom_ker : (F.quotientStepHom I hI).ker =
    NilpotentLieBCHGroup.subgroup (hnil := F.lowerCentralSeries_eq_bot) I.toLieSubalgebra := by
  ext g
  change quotientStepHom F I hI g = 1 ↔ g.coord ∈ I
  constructor
  · intro h
    exact (lieQuotientMap_eq_zero I g.coord).mp (congrArg coord h)
  · intro h
    exact NilpotentLieBCHGroup.ext ((lieQuotientMap_eq_zero I g.coord).mpr h)

theorem quotientStepHom_eq_changeStep : F.quotientStepHom I hI =
    (changeStep (lie_quotient_lowerCentralSeries_eq_bot F.lowerCentralSeries_eq_bot I)
      (F.quotientLie I hI).lowerCentralSeries_eq_bot).toMonoidHom.comp
        (quotientHom (hnil := F.lowerCentralSeries_eq_bot) I) := by
  ext g
  rfl

noncomputable def quotientStepEquiv : F.Group ⧸ (F.quotientStepHom I hI).ker ≃*
    (F.quotientLie I hI).Group :=
  QuotientGroup.quotientKerEquivOfSurjective _ (F.quotientStepHom_surjective I hI)

noncomputable def quotientPolynomialOrbit {σ : Type*} {w : σ → ℕ} (p : F.PolynomialOrbit w) :
    (F.quotientLie I hI).PolynomialOrbit w :=
  polynomialOrbitOfLog (VectorPolynomial.map (lieQuotientMap I).toLinearMap p.log)
    (F.adapted_quotientLie I hI w p.adapted)

@[simp] theorem quotientPolynomialOrbit_log {σ : Type*} {w : σ → ℕ} (p : F.PolynomialOrbit w) :
    (F.quotientPolynomialOrbit I hI p).log =
      VectorPolynomial.map (lieQuotientMap I).toLinearMap p.log := rfl

theorem quotientPolynomialOrbit_eval {σ : Type*} {w : σ → ℕ} (p : F.PolynomialOrbit w) (x : σ → ℤ) :
    (F.quotientLie I hI).polynomialOrbitEval w x (F.quotientPolynomialOrbit I hI p) =
      F.quotientStepHom I hI (F.polynomialOrbitEval w x p) := by
  apply NilpotentLieBCHGroup.ext
  simp only [polynomialOrbitEval_coord, quotientPolynomialOrbit_log, quotientStepHom_coord, eval_map]
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def quotientMultidegree (I : LieIdeal ℚ L) :
    MultidegreeLieFiltration σ (L ⧸ I) s bound where
  ordinary := F.ordinary.quotientLie I (by rw [F.ordinary.terminal]; exact bot_le)
  layer a := (F.layer a).map (lieQuotientMap I).toLinearMap
  antitone := fun _ _ hab => Submodule.map_mono (F.antitone hab)
  zero_eq_top := by
    rw [F.zero_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (lieQuotientMap_surjective I)
  lie_mem := by
    rintro a b x y ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
    exact ⟨⁅p, q⁆, F.lie_mem hp hq, (lieQuotientMap I).map_lie p q⟩
  terminal := by
    intro a ha
    rw [F.terminal a ha, Submodule.map_bot]
  degree_eq := by
    intro n
    change (F.ordinary.layer n).map (lieQuotientMap I).toLinearMap = _
    rw [F.degree_eq]
    simp only [Submodule.map_iSup]

theorem quotientMultidegree_mem (I : LieIdeal ℚ L) {a : σ → ℕ} {x : L}
    (hx : x ∈ F.layer a) :
    lieQuotientMap I x ∈ (F.quotientMultidegree I).layer a := ⟨x, hx, rfl⟩

theorem quotientMultidegree_layer_eq_bot (I : LieIdeal ℚ L) (a : σ → ℕ)
    (ha : F.layer a ≤ I.toSubmodule) : (F.quotientMultidegree I).layer a = ⊥ := by
  apply bot_unique
  rintro x ⟨y, hy, rfl⟩
  exact (lieQuotientMap_eq_zero I y).mpr (ha hy)

theorem quotientMultidegree_adapted (I : LieIdeal ℚ L)
    {p : VectorPolynomial σ ℚ L} (hp : F.Adapted p) :
    (F.quotientMultidegree I).Adapted (VectorPolynomial.map (lieQuotientMap I).toLinearMap p) := by
  intro a
  rw [coefficients_map]
  exact F.quotientMultidegree_mem I (hp a)

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (I : LieIdeal ℚ L)
  (hI : F.layer (t + 1) ≤ I.toSubmodule)

noncomputable def realQuotientStepHom :
    F.realification.Group →* (F.quotientLie I hI).realification.Group :=
  realificationMap (hnil := F.lowerCentralSeries_eq_bot)
    (hM := (F.quotientLie I hI).lowerCentralSeries_eq_bot) (lieQuotientMap I)

theorem realQuotientStepHom_surjective : Function.Surjective (F.realQuotientStepHom I hI) := by
  intro g
  obtain ⟨x, hx⟩ := LinearMap.lTensor_surjective ℝ (lieQuotientMap_surjective I) g.coord
  exact ⟨⟨x⟩, NilpotentLieBCHGroup.ext hx⟩

theorem mem_realQuotientStepHom_ker (g : F.realification.Group) :
    g ∈ (F.realQuotientStepHom I hI).ker ↔ g.coord ∈ I.toSubmodule.baseChange ℝ := by
  constructor
  · intro hg
    apply (realification_mkQ_eq_zero_iff I.toSubmodule g.coord).mp
    exact congrArg (fun z : (F.quotientLie I hI).realification.Group => z.coord)
      (MonoidHom.mem_ker.mp hg)
  · intro hg
    apply MonoidHom.mem_ker.mpr
    apply NilpotentLieBCHGroup.ext
    exact (realification_mkQ_eq_zero_iff I.toSubmodule g.coord).mpr hg

theorem realQuotientStepHom_lattice (Γ : Subgroup F.Group) :
    (Γ.map (F.quotientStepHom I hI)).map realificationHom =
      (Γ.map realificationHom).map (F.realQuotientStepHom I hI) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem realQuotientStep_mem_layer {j : ℕ} {x : ℝ ⊗[ℚ] L}
    (hx : x ∈ F.realification.layer j) :
    realificationLieHom (lieQuotientMap I) x ∈ (F.quotientLie I hI).realification.layer j := by
  have hmap : (F.layer j).baseChange ℝ ≤
      (((F.layer j).map (lieQuotientMap I).toLinearMap).baseChange ℝ).comap
        (realificationLieHom (lieQuotientMap I)).toLinearMap := by
    rw [Submodule.baseChange_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    change (1 : ℝ) ⊗ₜ[ℚ] (lieQuotientMap I a) ∈
      ((F.layer j).map (lieQuotientMap I).toLinearMap).baseChange ℝ
    exact Submodule.tmul_mem_baseChange_of_mem 1 ⟨a, ha, rfl⟩
  exact hmap hx

noncomputable def realQuotientPolynomialOrbit {σ : Type*} {w : σ → ℕ}
    (q : F.realification.PolynomialOrbit w) : (F.quotientLie I hI).realification.PolynomialOrbit w :=
  polynomialOrbitOfLog (VectorPolynomial.map
    (realLieHomToRat (realificationLieHom (lieQuotientMap I))).toLinearMap q.log)
    (F.realification.adapted_map (F.quotientLie I hI).realification _
      (fun _ _ hx => F.realQuotientStep_mem_layer I hI hx) w q.adapted)

theorem realQuotientPolynomialOrbit_eval {σ : Type*} {w : σ → ℕ}
    (q : F.realification.PolynomialOrbit w) (x : σ → ℤ) :
    (F.quotientLie I hI).realification.polynomialOrbitEval w x
      (F.realQuotientPolynomialOrbit I hI q) =
        F.realQuotientStepHom I hI (F.realification.polynomialOrbitEval w x q) := by
  apply NilpotentLieBCHGroup.ext
  change eval (fun i => (x i : ℚ)) (VectorPolynomial.map
    (realLieHomToRat (realificationLieHom (lieQuotientMap I))).toLinearMap q.log) = _
  rw [eval_map]
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open scoped TensorProduct

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M]
  (I : LieIdeal ℚ L) (π : L →ₗ⁅ℚ⁆ M) (hker : ∀ x ∈ I, π x = 0)

noncomputable def quotientInducedMark : (L ⧸ I) →ₗ⁅ℚ⁆ M :=
  lieQuotientDescend I π hker

@[simp] theorem quotientInducedMark_mk (x : L) :
    quotientInducedMark I π hker (lieQuotientMap I x) = π x := rfl

@[simp] theorem quotientInducedMark_comp :
    (quotientInducedMark I π hker).comp (lieQuotientMap I) = π := by
  ext x
  rfl

@[simp] theorem quotientInducedMark_real_mk (x : ℝ ⊗[ℚ] L) :
    realificationLieHom (quotientInducedMark I π hker)
      (realificationLieHom (lieQuotientMap I) x) = realificationLieHom π x := by
  induction x using TensorProduct.inductionOn with
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

@[simp] theorem quotientInducedMark_real_comp :
    (realificationLieHom (quotientInducedMark I π hker)).comp
      (realificationLieHom (lieQuotientMap I)) = realificationLieHom π := by
  ext x
  exact quotientInducedMark_real_mk I π hker x

namespace NilpotentLieFiltration

variable {s t u : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M u)

theorem quotientInducedMark_mem_layer
    (I : LieIdeal ℚ L) (hkill : F.layer (t + 1) ≤ I.toSubmodule)
    (π : L →ₗ⁅ℚ⁆ M) (hker : ∀ x ∈ I, π x = 0)
    (hπ : ∀ j, ∀ x ∈ F.layer j, π x ∈ G.layer j)
    (j : ℕ) (y : L ⧸ I) (hy : y ∈ (F.quotientLie I hkill).layer j) :
    quotientInducedMark I π hker y ∈ G.layer j := by
  obtain ⟨x, hx, rfl⟩ := hy
  exact hπ j x hx

theorem quotientInducedMark_realQuotientStepHom
    (I : LieIdeal ℚ L) (hkill : F.layer (t + 1) ≤ I.toSubmodule)
    (π : L →ₗ⁅ℚ⁆ M) (hker : ∀ x ∈ I, π x = 0)
    (g : F.realification.Group) :
    NilpotentLieBCHGroup.realificationMap
      (hnil := (F.quotientLie I hkill).lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) (quotientInducedMark I π hker)
      (F.realQuotientStepHom I hkill g) =
        NilpotentLieBCHGroup.realificationMap
          (hnil := F.lowerCentralSeries_eq_bot) (hM := G.lowerCentralSeries_eq_bot) π g := by
  apply NilpotentLieBCHGroup.ext
  exact quotientInducedMark_real_mk I π hker g.coord

end NilpotentLieFiltration
end Erdos3

end

end OAI
