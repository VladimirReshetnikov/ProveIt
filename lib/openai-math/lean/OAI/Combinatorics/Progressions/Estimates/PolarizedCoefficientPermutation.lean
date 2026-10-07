import OAI.Combinatorics.Progressions.Estimates.SubmoduleSupRestriction
import OAI.Combinatorics.Progressions.Polynomial.AdditiveTriplePolynomialRestriction
import OAI.Combinatorics.Progressions.Polynomial.DilationPairPolynomial
import OAI.Combinatorics.Progressions.Polynomial.MultiaffineTriplePolynomial
import OAI.Combinatorics.Progressions.Polynomial.MultidegreeDilationDegree

namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

def polynomialOrbitOfLog (p : VectorPolynomial σ ℚ L) (hp : F.Adapted p) : F.PolynomialOrbit :=
  ⟨⟨p⟩, hp⟩

@[simp] theorem polynomialOrbitOfLog_eval (p : VectorPolynomial σ ℚ L) (hp : F.Adapted p)
    (x : σ → ℤ) :
    (F.polynomialOrbitEval x (F.polynomialOrbitOfLog p hp)).coord = eval (fun i => (x i : ℚ)) p := rfl

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def constantMultidegreeOrbit (a : F.Group) : F.PolynomialOrbit :=
  ⟨⟨monomial 0 a.coord⟩, F.monomial_mem_adaptedSubmodule 0 (by
    change a.coord ∈ F.layer 0
    rw [F.zero_eq_top]
    trivial)⟩

theorem constantMultidegreeOrbit_eval (a : F.Group) (x : σ → ℤ) :
    F.polynomialOrbitEval x (F.constantMultidegreeOrbit a) = a := by
  apply NilpotentLieBCHGroup.ext
  change eval (fun i => (x i : ℚ)) (monomial 0 a.coord) = a.coord
  rw [eval_monomial, Finsupp.prod_zero_index, one_smul]

noncomputable def normalizeMultidegreeOrbit (p : F.PolynomialOrbit) (a b : F.Group) :
    F.PolynomialOrbit := F.constantMultidegreeOrbit a⁻¹ * p * F.constantMultidegreeOrbit b⁻¹

theorem normalizeMultidegreeOrbit_eval (p : F.PolynomialOrbit) (a b : F.Group) (x : σ → ℤ) :
    F.polynomialOrbitEval x (F.normalizeMultidegreeOrbit p a b) =
      a⁻¹ * F.polynomialOrbitEval x p * b⁻¹ := by
  simp only [normalizeMultidegreeOrbit, map_mul, F.constantMultidegreeOrbit_eval]

theorem normalizeMultidegreeOrbit_zero (p : F.PolynomialOrbit) (a b : F.Group)
    (h : F.polynomialOrbitEval 0 p = a * b) :
    F.polynomialOrbitEval 0 (F.normalizeMultidegreeOrbit p a b) = 1 := by
  rw [F.normalizeMultidegreeOrbit_eval, h]
  simp

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem adapted_rationalDilation (r : ℚ) (p : VectorPolynomial σ ℚ L)
    (hp : F.Adapted p) : F.Adapted (weightedDilation (fun _ : σ => 1) r p) := by
  intro a
  rw [coefficients_weightedDilation]
  exact (F.layer _).smul_mem _ (hp a)

noncomputable def rationalDilationOrbit (r : ℚ) (p : F.PolynomialOrbit) : F.PolynomialOrbit :=
  F.polynomialOrbitOfLog (weightedDilation (fun _ : σ => 1) r (p.log F))
    (F.adapted_rationalDilation r _ (p.adapted F))

theorem rationalDilationOrbit_eval (r : ℚ) (p : F.PolynomialOrbit) (x : σ → ℤ) :
    (F.polynomialOrbitEval x (F.rationalDilationOrbit r p)).coord =
      eval (fun i => r * (x i : ℚ)) (p.log F) := by
  change eval (fun i => (x i : ℚ)) (weightedDilation (fun _ : σ => 1) r (p.log F)) = _
  rw [eval_weightedDilation]
  simp only [pow_one]

theorem rationalDilationOrbit_rescaled (r : ℚ) (q : ℤ) (hr : r * (q : ℚ) = 1)
    (p : F.PolynomialOrbit) (x : σ → ℤ) :
    F.polynomialOrbitEval (fun i => q * x i) (F.rationalDilationOrbit r p) =
      F.polynomialOrbitEval x p := by
  apply NilpotentLieBCHGroup.ext
  rw [F.rationalDilationOrbit_eval, F.polynomialOrbitEval_coord]
  simp only [Int.cast_mul, ← mul_assoc, hr, one_mul]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem strictUpperLayer_zero : F.strictUpperLayer 0 = ⊤ := by
  have h : F.ordinary.layer 1 ≤ (F.strictUpperLayer 0).toSubmodule := by
    rw [F.degree_eq]
    apply iSup_le
    intro a
    apply iSup_le
    intro ha
    have hlt : (0 : σ → ℕ) < a := by
      refine lt_iff_le_not_ge.mpr ⟨fun _ => Nat.zero_le _, ?_⟩
      intro hzero
      have heq : a = 0 := le_antisymm hzero (fun _ => Nat.zero_le _)
      simp only [heq, Pi.zero_apply, Finset.sum_const_zero] at ha
      omega
    intro x hx
    exact F.layer_le_strictUpperLayer hlt hx
  apply top_unique
  intro x _
  exact h (by simp only [F.ordinary.one_eq_top, Submodule.mem_top])

theorem dilationPairLayer_zero (q : ℚ) : F.dilationPairLayer q 0 = ⊤ := by
  apply top_unique
  intro x _
  rw [F.mem_dilationPairLayer]
  simp only [F.zero_eq_top, F.strictUpperLayer_zero, Submodule.mem_top, LieSubmodule.mem_top,
    true_and]

theorem dilationPair_degree_comap (q : ℚ) (n : ℕ) :
    (F.ordinary.dilationPairFiltration q).layer n =
      ⨆ (a : σ → ℕ) (_ha : n ≤ ∑ i, a i),
        (F.dilationPairLayer q a).comap (F.ordinary.dilationPairSubalgebra q).incl.toLinearMap := by
  let K := F.ordinary.dilationPairSubalgebra q
  let ι := K.incl.toLinearMap
  by_cases hn : n = 0
  · subst n
    have hleft : (F.ordinary.dilationPairFiltration q).layer 0 = ⊤ := by
      apply top_unique
      rw [← (F.ordinary.dilationPairFiltration q).one_eq_top]
      exact (F.ordinary.dilationPairFiltration q).antitone (by decide : 0 ≤ 1)
    rw [hleft]
    symm
    apply top_unique
    apply le_iSup_of_le (0 : σ → ℕ)
    apply le_iSup_of_le (show 0 ≤ ∑ _ : σ, 0 from Nat.zero_le _)
    rw [F.dilationPairLayer_zero, Submodule.comap_top]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hr (a : σ → ℕ) (ha : n ≤ ∑ i, a i) :
        F.dilationPairLayer q a ≤ LinearMap.range ι := by
      intro x hx
      exact ⟨⟨x, F.dilationPairLayer_le_subalgebra q a (hn1.trans ha) hx⟩, rfl⟩
    change (F.ordinary.dilationPairLayer q n).comap ι = _
    rw [← F.dilationPairDegreeLayer_eq, dilationPairDegreeLayer]
    rw [submodule_comap_iSup_of_le_range ι Subtype.val_injective _
      (fun a => iSup_le (fun ha => hr a ha))]
    apply iSup_congr
    intro a
    exact submodule_comap_iSup_of_le_range ι Subtype.val_injective _ (hr a)

noncomputable def dilationPairMultidegree (q : ℚ) :
    MultidegreeLieFiltration σ (F.ordinary.dilationPairSubalgebra q) s bound where
  ordinary := F.ordinary.dilationPairFiltration q
  layer a := (F.dilationPairLayer q a).comap (F.ordinary.dilationPairSubalgebra q).incl.toLinearMap
  antitone := fun _ _ h _ hx => F.dilationPairLayer_antitone q h hx
  zero_eq_top := by rw [F.dilationPairLayer_zero, Submodule.comap_top]
  lie_mem := fun hx hy => F.dilationPairLayer_lie_mem q hx hy
  terminal a ha := by
    apply bot_unique
    intro x hx
    change x = 0
    apply Subtype.ext
    change x.val = (0 : L × L)
    have h : x.val ∈ F.dilationPairLayer q a := hx
    simpa only [F.dilationPairLayer_terminal q a ha, Submodule.mem_bot] using h
  degree_eq := F.dilationPair_degree_comap q

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3

namespace NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem dilationPair_top_group_relation (q : ℤ)
    (g : (F.dilationPairFiltration (q : ℚ)).Group)
    (hg : g ∈ (F.dilationPairFiltration (q : ℚ)).subgroup s) :
    (NilpotentLieBCHGroup.map (F.dilationPairFirst (q : ℚ)) g : F.Group) =
      (NilpotentLieBCHGroup.map (F.dilationPairSecond (q : ℚ)) g) ^ (q ^ s) := by
  apply NilpotentLieBCHGroup.ext
  rw [NilpotentLieBCHGroup.coord_zpow]
  change F.dilationPairFirst (q : ℚ) g.coord = (q ^ s) • F.dilationPairSecond (q : ℚ) g.coord
  rw [← Int.cast_smul_eq_zsmul ℚ, Int.cast_pow]
  exact F.dilationPairTop_relation (q : ℚ) hg

end NilpotentLieFiltration

namespace MultidegreeLieFiltration

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem dilationPair_projections_mem (q : ℚ) (a : σ → ℕ)
    (g : (F.dilationPairMultidegree q).Group)
    (hg : g ∈ (F.dilationPairMultidegree q).subgroup a) :
    (NilpotentLieBCHGroup.map (F.ordinary.dilationPairFirst q) g : F.Group) ∈ F.subgroup a ∧
      (NilpotentLieBCHGroup.map (F.ordinary.dilationPairSecond q) g : F.Group) ∈ F.subgroup a :=
  ⟨hg.1, hg.2.1⟩

theorem dilationPair_top_group_relation (q : ℤ)
    (g : (F.dilationPairMultidegree (q : ℚ)).Group)
    (hg : g ∈ (F.dilationPairMultidegree (q : ℚ)).subgroup bound) :
    (NilpotentLieBCHGroup.map (F.ordinary.dilationPairFirst (q : ℚ)) g : F.Group) =
      (NilpotentLieBCHGroup.map (F.ordinary.dilationPairSecond (q : ℚ)) g) ^ (q ^ ∑ i, bound i) := by
  apply NilpotentLieBCHGroup.ext
  rw [NilpotentLieBCHGroup.coord_zpow]
  change g.coord.val.1 = (q ^ ∑ i, bound i) • g.coord.val.2
  rw [← Int.cast_smul_eq_zsmul ℚ, Int.cast_pow]
  exact F.dilationPairLayer_top_relation (q : ℚ) hg

end MultidegreeLieFiltration

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem exists_splitTriple_orbit (i : σ) (hi : bound i ≤ 1)
    (u v : MvPolynomial (Option σ) ℚ)
    (hu : u ∈ weightedSupportLE (fun _ : Option σ => 1) 1)
    (hv : v ∈ weightedSupportLE (fun _ : Option σ => 1) 1)
    (hu0 : MvPolynomial.aeval (R := ℚ) (fun _ : Option σ => (0 : ℚ)) u = 0)
    (hv0 : MvPolynomial.aeval (R := ℚ) (fun _ : Option σ => (0 : ℚ)) v = 0)
    (p : VectorPolynomial σ ℚ L) (hp : F.Adapted p) (hp0 : coefficients p 0 = 0) :
    ∃ g : (F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
        (omittedCoordinateWeight_le_one i)).PolynomialOrbit (fun _ : Option σ => 1),
      (F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
        (omittedCoordinateWeight_le_one i)).polynomialOrbitEval _ 0 g = 1 ∧
      ∀ x : Option σ → ℤ,
        (((F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
          (omittedCoordinateWeight_le_one i)).polynomialOrbitEval _ x g).coord : L × L × L) =
          eval (fun j => (x j : ℚ)) (splitTriple i u v p) :=
  F.exists_additiveTripleOrbit_of_coefficients i hi (omittedCoordinateWeight i)
    (omittedCoordinateWeight_le_one i) (fun _ => 1) (fun _ => by decide) (splitTriple i u v p)
    (F.splitTriple_coefficient_mem i hi u v hu hv hp) (splitTriple_zero i u v p hp0 hu0 hv0)

theorem exists_coordinateAddition_orbit (i : σ) (hi : bound i ≤ 1)
    (p : F.PolynomialOrbit) (hp0 : F.polynomialOrbitEval 0 p = 1) :
    ∃ g : (F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
        (omittedCoordinateWeight_le_one i)).PolynomialOrbit (fun _ : Option σ => 1),
      (F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
        (omittedCoordinateWeight_le_one i)).polynomialOrbitEval _ 0 g = 1 ∧
      ∀ x : Option σ → ℤ,
        (((F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
          (omittedCoordinateWeight_le_one i)).polynomialOrbitEval _ x g).coord : L × L × L) =
          ((F.polynomialOrbitEval
              (Function.update (fun j => x (some j)) i (x (some i) + x none)) p).coord,
           (F.polynomialOrbitEval (fun j => x (some j)) p).coord,
           (F.polynomialOrbitEval (Function.update (fun j => x (some j)) i (x none)) p).coord) := by
  have hz : coefficients (p.log F) 0 = 0 := by
    have h := congrArg NilpotentLieBCHGroup.coord hp0
    simpa only [F.polynomialOrbitEval_coord, NilpotentLieBCHGroup.coord_one,
      Pi.zero_apply, Int.cast_zero, eval_zero_eq_coefficient] using h
  have hX (j : Option σ) : (MvPolynomial.X j : MvPolynomial (Option σ) ℚ) ∈
      weightedSupportLE (fun _ : Option σ => 1) 1 := by
    simpa only [MvPolynomial.X, Finsupp.weight_single, smul_eq_mul, mul_one] using
      weightedSupportLE_monomial (fun _ : Option σ => 1) (Finsupp.single j 1) (1 : ℚ)
  obtain ⟨g, hg0, hg⟩ := F.exists_splitTriple_orbit i hi (MvPolynomial.X (some i)) (MvPolynomial.X none)
    (hX _) (hX _) (by simp) (by simp) (p.log F) (p.adapted F) hz
  refine ⟨g, hg0, fun x => ?_⟩
  have hcast (y : σ → ℤ) (n : ℤ) : (fun j => (Function.update y i n j : ℚ)) =
      Function.update (fun j => (y j : ℚ)) i (n : ℚ) := by
    funext j
    by_cases hj : j = i <;> simp [hj, Function.update_of_ne]
  simpa only [eval_splitTriple, F.polynomialOrbitEval_coord, map_add, MvPolynomial.aeval_X,
    Function.update_eq_self, hcast, Int.cast_add] using hg x

theorem exists_normalizedCoordinateAddition_orbit (i : σ) (hi : bound i ≤ 1)
    (p : F.PolynomialOrbit) (a b : F.Group) (hp0 : F.polynomialOrbitEval 0 p = a * b) :
    ∃ g : (F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
        (omittedCoordinateWeight_le_one i)).PolynomialOrbit (fun _ : Option σ => 1),
      (F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
        (omittedCoordinateWeight_le_one i)).polynomialOrbitEval _ 0 g = 1 ∧
      ∀ x : Option σ → ℤ,
        (((F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
          (omittedCoordinateWeight_le_one i)).polynomialOrbitEval _ x g).coord : L × L × L) =
          ((a⁻¹ * F.polynomialOrbitEval
              (Function.update (fun j => x (some j)) i (x (some i) + x none)) p * b⁻¹).coord,
           (a⁻¹ * F.polynomialOrbitEval (fun j => x (some j)) p * b⁻¹).coord,
           (a⁻¹ * F.polynomialOrbitEval (Function.update (fun j => x (some j)) i (x none)) p * b⁻¹).coord) := by
  obtain ⟨g, hg0, hg⟩ := F.exists_coordinateAddition_orbit i hi (F.normalizeMultidegreeOrbit p a b)
    (F.normalizeMultidegreeOrbit_zero p a b hp0)
  exact ⟨g, hg0, fun x => by simpa only [F.normalizeMultidegreeOrbit_eval] using hg x⟩

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def dilationPairLog (q : ℚ) (p : VectorPolynomial σ ℚ L)
    (hp : F.Adapted p) (hp0 : coefficients p 0 = 0) :
    VectorPolynomial σ ℚ (F.ordinary.dilationPairSubalgebra q) :=
  F.ordinary.restrictDilationPairPolynomial q (fun _ : σ => 1) (fun _ => by decide)
    (dilationPair (fun _ : σ => 1) q p)
    (F.ordinary.dilationPair_coefficients _ q (F.adapted_ordinary hp))
    (by simp only [coefficients_dilationPair, hp0, smul_zero]; rfl)

theorem dilationPairMultidegree_mem_layer (q : ℚ) (a : σ → ℕ)
    (x : F.ordinary.dilationPairSubalgebra q) :
    x ∈ (F.dilationPairMultidegree q).layer a ↔ x.val ∈ F.dilationPairLayer q a := Iff.rfl

theorem dilationPairLog_adapted (q : ℚ) (p : VectorPolynomial σ ℚ L)
    (hp : F.Adapted p) (hp0 : coefficients p 0 = 0) :
    (F.dilationPairMultidegree q).Adapted (F.dilationPairLog q p hp hp0) := by
  intro a
  rw [F.dilationPairMultidegree_mem_layer]
  rw [dilationPairLog, NilpotentLieFiltration.restrictDilationPairPolynomial,
    coefficients_restrictCoefficients, coefficients_dilationPair]
  have hw : Finsupp.weight (fun _ : σ => 1) a = ∑ i, a i := by
    simp only [Finsupp.weight_eq_sum, smul_eq_mul, mul_one]
  rw [hw]
  exact F.dilationPairLayer_diagonal q _ (hp a)

omit [DecidableEq σ] in
theorem dilationPairLog_eval (q : ℚ) (p : VectorPolynomial σ ℚ L)
    (hp : F.Adapted p) (hp0 : coefficients p 0 = 0) (x : σ → ℚ) :
    (eval (V := F.ordinary.dilationPairSubalgebra q) x (F.dilationPairLog q p hp hp0) : L × L) =
      (eval (fun i => q * x i) p, eval x p) := by
  rw [dilationPairLog, NilpotentLieFiltration.restrictDilationPairPolynomial_eval,
    eval_dilationPair]
  simp only [pow_one]

noncomputable def dilationPairPolynomialOrbit (q : ℚ) (p : VectorPolynomial σ ℚ L)
    (hp : F.Adapted p) (hp0 : coefficients p 0 = 0) :
    (F.dilationPairMultidegree q).PolynomialOrbit :=
  (F.dilationPairMultidegree q).polynomialOrbitOfLog
    (F.dilationPairLog q p hp hp0) (F.dilationPairLog_adapted q p hp hp0)

theorem dilationPairPolynomialOrbit_eval (q : ℚ) (p : VectorPolynomial σ ℚ L)
    (hp : F.Adapted p) (hp0 : coefficients p 0 = 0) (x : σ → ℤ) :
    (((F.dilationPairMultidegree q).polynomialOrbitEval x
      (F.dilationPairPolynomialOrbit q p hp hp0)).coord : L × L) =
      (eval (fun i => q * (x i : ℚ)) p, eval (fun i => (x i : ℚ)) p) :=
  F.dilationPairLog_eval q p hp hp0 _

theorem dilationPairPolynomialOrbit_zero (q : ℚ) (p : VectorPolynomial σ ℚ L)
    (hp : F.Adapted p) (hp0 : coefficients p 0 = 0) :
    (F.dilationPairMultidegree q).polynomialOrbitEval 0
      (F.dilationPairPolynomialOrbit q p hp hp0) = 1 := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  change (((F.dilationPairMultidegree q).polynomialOrbitEval 0
    (F.dilationPairPolynomialOrbit q p hp hp0)).coord : L × L) = (0 : L × L)
  have h := F.dilationPairPolynomialOrbit_eval q p hp hp0 0
  simp only [Pi.zero_apply, Int.cast_zero, mul_zero, eval_zero_eq_coefficient, hp0] at h
  exact h

theorem exists_integer_dilationPair_orbit (q : ℤ) (p : F.PolynomialOrbit)
    (hp0 : F.polynomialOrbitEval 0 p = 1) :
    ∃ g : (F.dilationPairMultidegree (q : ℚ)).PolynomialOrbit,
      (F.dilationPairMultidegree (q : ℚ)).polynomialOrbitEval 0 g = 1 ∧
      ∀ x : σ → ℤ,
        (((F.dilationPairMultidegree (q : ℚ)).polynomialOrbitEval x g).coord : L × L) =
          ((F.polynomialOrbitEval (fun i => q * x i) p).coord, (F.polynomialOrbitEval x p).coord) := by
  have hz : coefficients (p.log F) 0 = 0 := by
    have h := congrArg NilpotentLieBCHGroup.coord hp0
    simpa only [F.polynomialOrbitEval_coord, NilpotentLieBCHGroup.coord_one,
      Pi.zero_apply, Int.cast_zero, eval_zero_eq_coefficient] using h
  refine ⟨F.dilationPairPolynomialOrbit (q : ℚ) (p.log F) (p.adapted F) hz,
    F.dilationPairPolynomialOrbit_zero (q : ℚ) (p.log F) (p.adapted F) hz, fun x => ?_⟩
  simpa only [F.polynomialOrbitEval_coord, Int.cast_mul] using
    F.dilationPairPolynomialOrbit_eval (q : ℚ) (p.log F) (p.adapted F) hz x

theorem exists_normalized_dilationPair_orbit (q : ℤ) (p : F.PolynomialOrbit)
    (a b : F.Group) (hp0 : F.polynomialOrbitEval 0 p = a * b) :
    ∃ g : (F.dilationPairMultidegree (q : ℚ)).PolynomialOrbit,
      (F.dilationPairMultidegree (q : ℚ)).polynomialOrbitEval 0 g = 1 ∧
      ∀ x : σ → ℤ,
        (((F.dilationPairMultidegree (q : ℚ)).polynomialOrbitEval x g).coord : L × L) =
          ((a⁻¹ * F.polynomialOrbitEval (fun i => q * x i) p * b⁻¹).coord,
            (a⁻¹ * F.polynomialOrbitEval x p * b⁻¹).coord) := by
  obtain ⟨g, hg0, hg⟩ := F.exists_integer_dilationPair_orbit q (F.normalizeMultidegreeOrbit p a b)
    (F.normalizeMultidegreeOrbit_zero p a b hp0)
  exact ⟨g, hg0, fun x => by simpa only [F.normalizeMultidegreeOrbit_eval] using hg x⟩

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def blockCoefficient (p : F.adaptedLieSubalgebra) (a : SquarefreeIndex ι) :
    F.layer (blockDegree π a.val) :=
  ⟨coefficients p.val (blockExponent π a.val), p.property (blockExponent π a.val)⟩

noncomputable def polarizedCoefficient (p : F.adaptedLieSubalgebra) (a : SquarefreeIndex ι) :
    F.SquarefreeAlgebra π :=
  (multidegreeFactorial (blockDegree π a.val) : ℚ) •
    F.squarefreeLayerMap π a (F.blockCoefficient π p a)

theorem polarizedCoefficient_zero (p : F.adaptedLieSubalgebra) (a : SquarefreeIndex ι)
    (ha : a.val = 0) : F.polarizedCoefficient π p a = 0 := by
  rw [polarizedCoefficient, F.squarefreeLayerMap_zero π a ha, smul_zero]

theorem polarizedCoefficient_coe (p : F.adaptedLieSubalgebra) (a : SquarefreeIndex ι)
    (ha : a.val ≠ 0) :
    (F.polarizedCoefficient π p a).val =
      (multidegreeFactorial (blockDegree π a.val) : ℚ) •
        squarefreeMonomial a (coefficients p.val (blockExponent π a.val)) := by
  change (multidegreeFactorial (blockDegree π a.val) : ℚ) •
    (F.squarefreeLayerMap π a (F.blockCoefficient π p a)).val = _
  rw [F.squarefreeLayerMap_coe π a ha]
  rfl

theorem polarizedCoefficient_mem (p : F.adaptedLieSubalgebra) (a : SquarefreeIndex ι) :
    F.polarizedCoefficient π p a ∈ F.squarefreeMultidegreeLayer π (fun i => a.val i) :=
  (F.squarefreeMultidegreeLayer π _).smul_mem _ (F.squarefreeLayerMap_mem π a _)

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem polarizedCoefficient_permute (p : F.adaptedLieSubalgebra)
    (e : Equiv.Perm ι) (he : ∀ i, π (e i) = π i) (a : SquarefreeIndex ι) :
    F.squarefreeBlockPermute π e he (F.polarizedCoefficient π p a) =
      F.polarizedCoefficient π p (SquarefreeIndex.permute e a) := by
  by_cases ha : a.val = 0
  · rw [F.polarizedCoefficient_zero π p a ha,
      F.polarizedCoefficient_zero π p _ ((SquarefreeIndex.permute_zero_iff e a).mpr ha),
      map_zero]
  · have hea : (SquarefreeIndex.permute e a).val ≠ 0 :=
      fun h => ha ((SquarefreeIndex.permute_zero_iff e a).mp h)
    apply Subtype.ext
    rw [F.squarefreeBlockPermute_apply, F.polarizedCoefficient_coe π p a ha,
      F.polarizedCoefficient_coe π p _ hea, map_smul, squarefreePermute_monomial,
      SquarefreeIndex.permute_blockDegree π e he a, blockExponent_permute π e he a]

end Erdos3.MultidegreeLieFiltration

end

end OAI
