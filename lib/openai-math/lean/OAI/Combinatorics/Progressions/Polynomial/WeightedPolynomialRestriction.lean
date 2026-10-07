/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Mathematical statements are unchanged from the pinned upstream source.
Use MvPolynomial coefficient lemmas explicitly on Lean 4.32; statements unchanged.
Import the finite-weight compatibility lemma for Lean 4.32. -/
import OAI.Compat.FinsuppWeight
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.RealifiedTripleLayers
import OAI.Combinatorics.Progressions.Geometry.CoordinateSubstitutionAlgebra

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {σ τ R V : Type*} [DecidableEq σ] [CommRing R] [AddCommGroup V] [Module R V]

theorem substitute_update_add (f : σ → MvPolynomial τ R) (i : σ)
    (u v : MvPolynomial τ R) (p : VectorPolynomial σ R V)
    (hp : ∀ a, 1 < a i → coefficients p a = 0) :
    substitute (Function.update f i (u + v)) p =
      substitute (Function.update f i u) p + substitute (Function.update f i v) p -
      substitute (Function.update f i 0) p := by
  apply coefficients.injective
  ext b
  simp only [map_sub, map_add, Finsupp.sub_apply, Finsupp.add_apply, coefficients_substitute]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a i ≤ 1
  · rw [aeval_monomial_update_add (R := R) f i u v a ha,
      MvPolynomial.coeff_sub, MvPolynomial.coeff_add, sub_smul, add_smul]
  · simp only [hp a (Nat.lt_of_not_ge ha), smul_zero, add_zero, sub_zero]

theorem coefficients_substitute_update_sub_mem (P : Submodule R V)
    (f : σ → MvPolynomial τ R) (i : σ) (u v : MvPolynomial τ R)
    (p : VectorPolynomial σ R V) (hp : ∀ a, 0 < a i → coefficients p a ∈ P)
    (b : τ →₀ ℕ) :
    coefficients (substitute (Function.update f i u) p - substitute (Function.update f i v) p) b ∈ P := by
  classical
  simp only [map_sub, Finsupp.sub_apply, coefficients_substitute]
  rw [← Finset.sum_sub_distrib]
  apply P.sum_mem
  intro a _
  by_cases ha : a i = 0
  · rw [aeval_monomial_update_eq_of_zero (R := R) f i u v a ha, sub_self]
    exact P.zero_mem
  · exact P.sub_mem (P.smul_mem _ (hp a (Nat.pos_of_ne_zero ha)))
      (P.smul_mem _ (hp a (Nat.pos_of_ne_zero ha)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

def Adapted (p : VectorPolynomial σ ℚ L) : Prop :=
  ∀ a, coefficients p a ∈ F.layer (fun i => a i)

noncomputable def adaptedSubmodule : Submodule ℚ (VectorPolynomial σ ℚ L) where
  carrier := {p | F.Adapted p}
  zero_mem' := by intro a; simp only [map_zero, Finsupp.zero_apply, Submodule.zero_mem]
  add_mem' hp hq := by
    intro a
    simpa only [map_add, Finsupp.add_apply] using (F.layer _).add_mem (hp a) (hq a)
  smul_mem' c p hp := by
    intro a
    simpa only [map_smul, Finsupp.smul_apply] using (F.layer _).smul_mem c (hp a)

theorem monomial_mem_adaptedSubmodule (a : σ →₀ ℕ) {x : L} (hx : x ∈ F.layer (fun i => a i)) :
    monomial (R := ℚ) a x ∈ F.adaptedSubmodule := by
  classical
  intro b
  by_cases h : a = b
  · subst b
    simpa only [coefficients_monomial, Finsupp.single_eq_same] using hx
  · simp [h]

theorem lie_mem_adaptedSubmodule {p q : VectorPolynomial σ ℚ L}
    (hp : p ∈ F.adaptedSubmodule) (hq : q ∈ F.adaptedSubmodule) :
    ⁅p, q⁆ ∈ F.adaptedSubmodule := by
  classical
  rw [← sum_monomial_coefficients p, ← sum_monomial_coefficients q]
  simp only [Finsupp.sum]
  rw [sum_lie_sum (coefficients p).support (coefficients q).support
    (fun a => monomial (R := ℚ) a (coefficients p a))
    (fun b => monomial (R := ℚ) b (coefficients q b))]
  apply Submodule.sum_mem
  intro a _
  apply Submodule.sum_mem
  intro b _
  rw [lie_monomial]
  apply F.monomial_mem_adaptedSubmodule
  exact F.lie_mem (hp a) (hq b)

noncomputable def adaptedLieSubalgebra : LieSubalgebra ℚ (VectorPolynomial σ ℚ L) :=
  { F.adaptedSubmodule with lie_mem' := F.lie_mem_adaptedSubmodule }

theorem adapted_ordinary {p : VectorPolynomial σ ℚ L} (hp : F.Adapted p) :
    F.ordinary.Adapted (fun _ => 1) p := by
  apply (F.ordinary.adapted_iff_coefficients _ _).mpr
  intro a
  have h := F.layer_le_ordinary (fun i => a i) (hp a)
  simpa only [Finsupp.weight_eq_sum, smul_eq_mul, mul_one] using h

noncomputable def polynomialSubgroup : Subgroup
    (NilpotentLieBCHGroup (VectorPolynomial σ ℚ L) s
      (VectorPolynomial.lowerCentralSeries_eq_bot F.ordinary.lowerCentralSeries_eq_bot)) :=
  NilpotentLieBCHGroup.subgroup F.adaptedLieSubalgebra

abbrev PolynomialOrbit := ↥F.polynomialSubgroup

def PolynomialOrbit.log (p : F.PolynomialOrbit) : VectorPolynomial σ ℚ L := p.val.coord

theorem PolynomialOrbit.adapted (p : F.PolynomialOrbit) : F.Adapted (p.log F) := p.property

noncomputable def polynomialOrbitEval (x : σ → ℤ) : F.PolynomialOrbit →* F.Group :=
  (NilpotentLieBCHGroup.map (evalLie (fun i => (x i : ℚ)))).comp F.polynomialSubgroup.subtype

@[simp] theorem polynomialOrbitEval_coord (p : F.PolynomialOrbit) (x : σ → ℤ) :
    (F.polynomialOrbitEval x p).coord = eval (fun i => (x i : ℚ)) (p.log F) := rfl

noncomputable def toOrdinaryOrbit : F.PolynomialOrbit →* F.ordinary.PolynomialOrbit (fun _ : σ => 1) where
  toFun p := ⟨p.val, (F.ordinary.mem_adaptedSubmodule _ _).mpr (F.adapted_ordinary p.property)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem toOrdinaryOrbit_eval (p : F.PolynomialOrbit) (x : σ → ℤ) :
    F.ordinary.polynomialOrbitEval (fun _ => 1) x (F.toOrdinaryOrbit p) = F.polynomialOrbitEval x p := rfl

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3

open scoped BigOperators

theorem multidegreeWeight_finsupp {σ : Type*} [Fintype σ] (c : σ → ℕ) (a : σ →₀ ℕ) :
    multidegreeWeight c (fun i => a i) = Finsupp.weight c a := by
  simp only [multidegreeWeight, Finsupp.weight_eq_sum, smul_eq_mul, mul_comm]

namespace MultidegreeLieFiltration

open VectorPolynomial

variable {σ τ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

def WeightedAdapted (c : σ → ℕ) (v : τ → ℕ) (p : VectorPolynomial τ ℚ L) : Prop :=
  ∀ a, coefficients p a ∈ F.weightedLayer c (Finsupp.weight v a)

noncomputable def weightedAdaptedSubmodule (c : σ → ℕ) (v : τ → ℕ) :
    Submodule ℚ (VectorPolynomial τ ℚ L) where
  carrier := {p | F.WeightedAdapted c v p}
  zero_mem' := by intro a; simp only [map_zero, Finsupp.zero_apply, LieSubmodule.zero_mem]
  add_mem' hp hq := by
    intro a
    rw [map_add, Finsupp.add_apply]
    exact (F.weightedLayer c _).add_mem (hp a) (hq a)
  smul_mem' r p hp := by
    intro a
    rw [map_smul, Finsupp.smul_apply]
    exact (F.weightedLayer c _).smul_mem r (hp a)

theorem weightedAdapted_monomial (c : σ → ℕ) (v : τ → ℕ) (a : τ →₀ ℕ) {x : L}
    (hx : x ∈ F.weightedLayer c (Finsupp.weight v a)) :
    F.WeightedAdapted c v (monomial a x) := by
  classical
  intro b
  by_cases h : a = b
  · subst b
    simpa only [coefficients_monomial, Finsupp.single_eq_same] using hx
  · simp [h]

theorem weightedAdapted_lie (c : σ → ℕ) (v : τ → ℕ) {p q : VectorPolynomial τ ℚ L}
    (hp : F.WeightedAdapted c v p) (hq : F.WeightedAdapted c v q) :
    F.WeightedAdapted c v ⁅p, q⁆ := by
  classical
  change ⁅p, q⁆ ∈ F.weightedAdaptedSubmodule c v
  rw [← sum_monomial_coefficients p, ← sum_monomial_coefficients q]
  simp only [Finsupp.sum]
  rw [sum_lie_sum (coefficients p).support (coefficients q).support
    (fun a => monomial (R := ℚ) a (coefficients p a))
    (fun b => monomial (R := ℚ) b (coefficients q b))]
  apply Submodule.sum_mem
  intro a _
  apply Submodule.sum_mem
  intro b _
  rw [lie_monomial]
  apply F.weightedAdapted_monomial
  rw [map_add]
  exact F.weightedLayer_lie_mem c (hp a) (hq b)

noncomputable def weightedAdaptedLieSubalgebra (c : σ → ℕ) (v : τ → ℕ) :
    LieSubalgebra ℚ (VectorPolynomial τ ℚ L) :=
  { F.weightedAdaptedSubmodule c v with lie_mem' := F.weightedAdapted_lie c v }

theorem weightedAdapted_bch (c : σ → ℕ) (v : τ → ℕ) (t : ℕ)
    {p q : VectorPolynomial τ ℚ L} (hp : F.WeightedAdapted c v p) (hq : F.WeightedAdapted c v q) :
    F.WeightedAdapted c v (lieBCH t p q) :=
  lieBCH_mem (F.weightedAdaptedLieSubalgebra c v) t hp hq

theorem weightedAdapted_constant (c : σ → ℕ) (v : τ → ℕ) (x : L) :
    F.WeightedAdapted c v (monomial 0 x) := by
  apply F.weightedAdapted_monomial
  simp only [map_zero, F.weightedLayer_zero, LieSubmodule.mem_top]

theorem weightedAdapted_substitute (c : σ → ℕ) (v : τ → ℕ) (f : σ → MvPolynomial τ ℚ)
    (hf : ∀ i, f i ∈ weightedSupportLE v (c i)) {p : VectorPolynomial σ ℚ L}
    (hp : F.Adapted p) : F.WeightedAdapted c v (VectorPolynomial.substitute f p) := by
  intro a
  rw [coefficients_substitute]
  apply Submodule.sum_mem
  intro b _
  by_cases hc : (MvPolynomial.aeval (R := ℚ) f (MvPolynomial.monomial b 1)).coeff a = 0
  · rw [hc, zero_smul]
    exact LieSubmodule.zero_mem _
  · apply Submodule.smul_mem
    have hb : coefficients p b ∈ F.weightedLayer c (Finsupp.weight c b) :=
      F.layer_le_weightedLayer c (fun i => b i) _ (by rw [multidegreeWeight_finsupp]) (hp b)
    exact F.weightedLayer_antitone c
      (aeval_monomial_weightedSupport f c v hf b (MvPolynomial.mem_support_iff.mpr hc)) hb

end MultidegreeLieFiltration

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*} [DecidableEq σ]

def omittedCoordinateWeight (i j : σ) : ℕ := if j = i then 0 else 1

theorem omittedCoordinateWeight_le_one (i j : σ) : omittedCoordinateWeight i j ≤ 1 := by
  unfold omittedCoordinateWeight
  split_ifs <;> omega

theorem omittedCoordinateWeight_total [Fintype σ] (i : σ) (bound : σ → ℕ) :
    multidegreeWeight (omittedCoordinateWeight i) bound + bound i = ∑ j, bound j := by
  have h (j : σ) : omittedCoordinateWeight i j * bound j + (if j = i then bound i else 0) = bound j := by
    by_cases hj : j = i <;> simp [omittedCoordinateWeight, hj]
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun j _ => h j)
  simpa [Finset.sum_add_distrib, multidegreeWeight] using hs

noncomputable def splitCoordinatePolynomial (i : σ) (u : MvPolynomial (Option σ) ℚ) :
    σ → MvPolynomial (Option σ) ℚ :=
  Function.update (fun j => MvPolynomial.X (some j)) i u

theorem splitCoordinatePolynomial_support (i : σ) (u : MvPolynomial (Option σ) ℚ)
    (hu : u ∈ weightedSupportLE (fun _ : Option σ => 1) 1) (j : σ) :
    splitCoordinatePolynomial i u j ∈ weightedSupportLE (fun _ : Option σ => 1) 1 := by
  by_cases hj : j = i
  · subst j
    simpa only [splitCoordinatePolynomial, Function.update_self] using hu
  · rw [splitCoordinatePolynomial, Function.update_of_ne hj]
    simpa only [MvPolynomial.X, Finsupp.weight_single, smul_eq_mul, mul_one] using
      weightedSupportLE_monomial (fun _ : Option σ => 1) (Finsupp.single (some j) 1) (1 : ℚ)

theorem splitCoordinatePolynomial_zero_support (i j : σ) :
    splitCoordinatePolynomial i 0 j ∈
      weightedSupportLE (fun _ : Option σ => 1) (omittedCoordinateWeight i j) := by
  by_cases hj : j = i
  · subst j
    simp only [splitCoordinatePolynomial, Function.update_self, omittedCoordinateWeight, ite_true]
    exact Submodule.zero_mem _
  · simp only [splitCoordinatePolynomial, Function.update_of_ne hj, omittedCoordinateWeight, ite_eq_right hj]
    simpa only [MvPolynomial.X, Finsupp.weight_single, smul_eq_mul, mul_one] using
      weightedSupportLE_monomial (fun _ : Option σ => 1) (Finsupp.single (some j) 1) (1 : ℚ)

theorem splitCoordinatePolynomial_eval (i j : σ) (u : MvPolynomial (Option σ) ℚ)
    (x : Option σ → ℚ) :
    MvPolynomial.aeval (R := ℚ) x (splitCoordinatePolynomial i u j) =
      Function.update (fun k => x (some k)) i (MvPolynomial.aeval (R := ℚ) x u) j := by
  by_cases hj : j = i <;> simp [splitCoordinatePolynomial, hj, Function.update_of_ne]

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ τ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem weightedAdapted_coefficients_mem (c : σ → ℕ) (v : τ → ℕ) (hv : ∀ i, 0 < v i)
    {p : VectorPolynomial τ ℚ L} (hp : F.WeightedAdapted c v p) (hzero : coefficients p 0 = 0)
    (a : τ →₀ ℕ) : coefficients p a ∈ F.weightedSubalgebra c := by
  classical
  by_cases ha : a = 0
  · rw [ha, hzero]
    exact (F.weightedSubalgebra c).zero_mem
  · have hi : ∃ i, a i ≠ 0 := by
      by_contra h
      push Not at h
      apply ha
      ext i
      exact h i
    obtain ⟨i, hi⟩ := hi
    have hpos : 1 ≤ Finsupp.weight v a := (hv i).trans_le (Finsupp.le_weight_of_ne_zero' v hi)
    exact F.weightedLayer_antitone c hpos (hp a)

noncomputable def restrictWeightedPolynomial (c : σ → ℕ) (v : τ → ℕ) (hv : ∀ i, 0 < v i)
    (p : VectorPolynomial τ ℚ L) (hp : F.WeightedAdapted c v p) (hzero : coefficients p 0 = 0) :
    VectorPolynomial τ ℚ (F.weightedSubalgebra c) :=
  restrictCoefficients (F.weightedSubalgebra c).toSubmodule p
    (F.weightedAdapted_coefficients_mem c v hv hp hzero)

theorem restrictWeightedPolynomial_adapted (c : σ → ℕ) (v : τ → ℕ) (hv : ∀ i, 0 < v i)
    (p : VectorPolynomial τ ℚ L) (hp : F.WeightedAdapted c v p) (hzero : coefficients p 0 = 0) :
    (F.weightedFiltration c).Adapted v (F.restrictWeightedPolynomial c v hv p hp hzero) := by
  apply ((F.weightedFiltration c).adapted_iff_coefficients v _).mpr
  intro a
  change (coefficients (restrictCoefficients (F.weightedSubalgebra c).toSubmodule p
      (F.weightedAdapted_coefficients_mem c v hv hp hzero)) a : L) ∈
    F.weightedLayer c (max 1 (Finsupp.weight v a))
  rw [coefficients_restrictCoefficients]
  by_cases hn : 1 ≤ Finsupp.weight v a
  · rw [max_eq_right hn]
    exact hp a
  · have hz : Finsupp.weight v a = 0 := by omega
    rw [hz]
    exact F.weightedAdapted_coefficients_mem c v hv hp hzero a

theorem restrictWeightedPolynomial_eval (c : σ → ℕ) (v : τ → ℕ) (hv : ∀ i, 0 < v i)
    (p : VectorPolynomial τ ℚ L) (hp : F.WeightedAdapted c v p) (hzero : coefficients p 0 = 0)
    (x : τ → ℚ) :
    (eval (V := F.weightedSubalgebra c) x
      (F.restrictWeightedPolynomial c v hv p hp hzero) : L) = eval x p :=
  eval_restrictCoefficients (F.weightedSubalgebra c).toSubmodule p
    (F.weightedAdapted_coefficients_mem c v hv hp hzero) x

noncomputable def restrictWeightedOrbit (c : σ → ℕ) (v : τ → ℕ) (hv : ∀ i, 0 < v i)
    (p : VectorPolynomial τ ℚ L) (hp : F.WeightedAdapted c v p) (hzero : coefficients p 0 = 0) :
    (F.weightedFiltration c).PolynomialOrbit v :=
  NilpotentLieFiltration.polynomialOrbitOfLog (F.restrictWeightedPolynomial c v hv p hp hzero)
    (F.restrictWeightedPolynomial_adapted c v hv p hp hzero)

theorem restrictWeightedOrbit_eval (c : σ → ℕ) (v : τ → ℕ) (hv : ∀ i, 0 < v i)
    (p : VectorPolynomial τ ℚ L) (hp : F.WeightedAdapted c v p) (hzero : coefficients p 0 = 0)
    (x : τ → ℤ) :
    (((F.weightedFiltration c).polynomialOrbitEval v x
      (F.restrictWeightedOrbit c v hv p hp hzero)).coord : L) =
      eval (fun i => (x i : ℚ)) p :=
  F.restrictWeightedPolynomial_eval c v hv p hp hzero (fun i => (x i : ℚ))

end Erdos3.MultidegreeLieFiltration

end

end OAI
