/- Modified for ProveIt: use Mathlib v4.32.0's primed generic product
and subset comparison lemmas. Mathematical statements unchanged. -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import OAI.Combinatorics.Progressions.Lattices.InjectiveSmallPrimeProduct
import OAI.Combinatorics.Progressions.Probability.ActualFixedSpatialUnchargedDensity

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem retainedPrimeProduct_le_chargedProduct_mul_smallProduct
    {L : Type*} [Fintype L] (p b e : L → ℕ) (cutoff : ℕ)
    (hp : ∀ l, 1 ≤ p l) (retained : Finset L)
    (hretained : ∀ l ∈ retained, b l ≠ 0 ∨ e l ≠ 0 ∨ p l ≤ cutoff) :
    (∏ l ∈ retained, p l) ≤
      ((∏ l, p l ^ b l) * (∏ l, p l ^ e l)) *
        ∏ l ∈ Finset.univ.filter (fun l => p l ≤ cutoff), p l := by
  let w (l : L) := (p l ^ b l * p l ^ e l) * (if p l ≤ cutoff then p l else 1)
  have hw (l : L) : 1 ≤ w l := by
    dsimp only [w]
    apply one_le_mul
    · exact one_le_mul (one_le_pow₀ (hp l)) (one_le_pow₀ (hp l))
    · split_ifs
      · exact hp l
      · exact le_rfl
  have hpoint (l : L) (hl : l ∈ retained) : p l ≤ w l := by
    have hb1 : 1 ≤ p l ^ b l := one_le_pow₀ (hp l)
    have he1 : 1 ≤ p l ^ e l := one_le_pow₀ (hp l)
    dsimp only [w]
    by_cases hsmall : p l ≤ cutoff
    · simp only [hsmall, ite_true]
      exact le_mul_of_one_le_left' (one_le_mul hb1 he1)
    · simp only [hsmall, ite_false, mul_one]
      rcases hretained l hl with hb | he | hs
      · exact (le_self_pow (hp l) hb).trans (le_mul_of_one_le_right' he1)
      · exact (le_self_pow (hp l) he).trans (le_mul_of_one_le_left' hb1)
      · exact (hsmall hs).elim
  calc
    (∏ l ∈ retained, p l) ≤ ∏ l ∈ retained, w l :=
      Finset.prod_le_prod' hpoint
    _ ≤ ∏ l, w l := Finset.prod_le_prod_of_subset_of_one_le'
      (Finset.subset_univ _) (fun l _ _ => hw l)
    _ = ((∏ l, p l ^ b l) * (∏ l, p l ^ e l)) *
        ∏ l ∈ Finset.univ.filter (fun l => p l ≤ cutoff), p l := by
      simp only [w, Finset.prod_mul_distrib, Finset.prod_filter]

theorem retainedPrimePowerModulus_le_power_of_primeProduct
    {L : Type*} [Fintype L] (p A : L → ℕ) (retained : Finset L)
    (depth : ℕ) (hp : ∀ l, 1 ≤ p l) (hA : ∀ l ∈ retained, A l ≤ depth) :
    (∏ l ∈ retained, p l ^ A l) ≤ (∏ l ∈ retained, p l) ^ depth := by
  calc
    (∏ l ∈ retained, p l ^ A l) ≤ ∏ l ∈ retained, p l ^ depth :=
      Finset.prod_le_prod' (fun l hl => pow_le_pow_right' (hp l) (hA l hl))
    _ = (∏ l ∈ retained, p l) ^ depth := Finset.prod_pow _ _ _

theorem retainedPrimePowerModulus_le_charged_cutoff
    {L : Type*} [Fintype L] (p A b e : L → ℕ) (cutoff depth : ℕ)
    (hp : ∀ l, 1 ≤ p l) (hinj : Function.Injective p)
    (retained : Finset L)
    (hretained : ∀ l ∈ retained, b l ≠ 0 ∨ e l ≠ 0 ∨ p l ≤ cutoff)
    (hA : ∀ l ∈ retained, A l ≤ depth) :
    (∏ l ∈ retained, p l ^ A l) ≤
      ((∏ l, p l ^ b l) * (∏ l, p l ^ e l) *
        (cutoff + 1) ^ (cutoff + 1)) ^ depth := by
  have hprime : (∏ l ∈ retained, p l) ≤
      (∏ l, p l ^ b l) * (∏ l, p l ^ e l) * (cutoff + 1) ^ (cutoff + 1) :=
    (retainedPrimeProduct_le_chargedProduct_mul_smallProduct
      p b e cutoff hp retained hretained).trans
        (Nat.mul_le_mul_left _ (prod_filter_le_cutoff_pow_of_injective p hinj cutoff))
  exact (retainedPrimePowerModulus_le_power_of_primeProduct
    p A retained depth hp hA).trans (pow_le_pow_left' hprime depth)

theorem retainedPrimePowerModulus_filter_le_charged_cutoff
    {L : Type*} [Fintype L] (p A b e : L → ℕ) (cutoff depth : ℕ)
    (hp : ∀ l, 1 ≤ p l) (hinj : Function.Injective p)
    (hA : ∀ l, A l ≤ depth) :
    (∏ l ∈ Finset.univ.filter (fun l => b l ≠ 0 ∨ e l ≠ 0 ∨ p l ≤ cutoff),
      p l ^ A l) ≤
      ((∏ l, p l ^ b l) * (∏ l, p l ^ e l) *
        (cutoff + 1) ^ (cutoff + 1)) ^ depth := by
  apply retainedPrimePowerModulus_le_charged_cutoff p A b e cutoff depth hp hinj
  · intro l hl
    exact (Finset.mem_filter.mp hl).2
  · intro l _
    exact hA l

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem retainedPrimePowerModulus_le_exp_charged_cutoff
    {L : Type*} [Fintype L] (p A b e : L → ℕ) (cutoff depth : ℕ)
    (hp : ∀ l, 1 ≤ p l) (hinj : Function.Injective p)
    (retained : Finset L)
    (hretained : ∀ l ∈ retained, b l ≠ 0 ∨ e l ≠ 0 ∨ p l ≤ cutoff)
    (hA : ∀ l ∈ retained, A l ≤ depth) (Pbad Ppres : ℝ)
    (hbad : ((∏ l, p l ^ b l : ℕ) : ℝ) ≤ Real.exp Pbad)
    (hpres : ((∏ l, p l ^ e l : ℕ) : ℝ) ≤ Real.exp Ppres) :
    ((∏ l ∈ retained, p l ^ A l : ℕ) : ℝ) ≤
      Real.exp ((depth : ℝ) *
        (Pbad + Ppres + ((cutoff + 1 : ℕ) : ℝ) * Real.log (cutoff + 1))) := by
  have hcharged :
      (((∏ l, p l ^ b l) * (∏ l, p l ^ e l) *
        (cutoff + 1) ^ (cutoff + 1) : ℕ) : ℝ) ≤
      Real.exp (Pbad + Ppres +
        ((cutoff + 1 : ℕ) : ℝ) * Real.log (cutoff + 1)) := by
    calc
      _ = ((∏ l, p l ^ b l : ℕ) : ℝ) * ((∏ l, p l ^ e l : ℕ) : ℝ) *
          ((cutoff + 1 : ℕ) : ℝ) ^ (cutoff + 1) := by norm_cast
      _ ≤ Real.exp Pbad * Real.exp Ppres *
          ((cutoff + 1 : ℕ) : ℝ) ^ (cutoff + 1) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hbad hpres (Nat.cast_nonneg _) (Real.exp_nonneg _))
          (by positivity)
      _ = _ := by
        rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul,
          Real.exp_log (by positivity)]
        simp only [Nat.cast_add, Nat.cast_one]
  have hnat := retainedPrimePowerModulus_le_charged_cutoff
    p A b e cutoff depth hp hinj retained hretained hA
  calc
    _ ≤ (((∏ l, p l ^ b l) * (∏ l, p l ^ e l) *
          (cutoff + 1) ^ (cutoff + 1) : ℕ) : ℝ) ^ depth := by
      exact_mod_cast hnat
    _ ≤ Real.exp (Pbad + Ppres +
          ((cutoff + 1 : ℕ) : ℝ) * Real.log (cutoff + 1)) ^ depth :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hcharged depth
    _ = _ := (Real.exp_nat_mul _ depth).symm

theorem retainedPrimePowerModulus_filter_le_exp_charged_cutoff
    {L : Type*} [Fintype L] (p A b e : L → ℕ) (cutoff depth : ℕ)
    (hp : ∀ l, 1 ≤ p l) (hinj : Function.Injective p)
    (hA : ∀ l, A l ≤ depth) (Pbad Ppres : ℝ)
    (hbad : ((∏ l, p l ^ b l : ℕ) : ℝ) ≤ Real.exp Pbad)
    (hpres : ((∏ l, p l ^ e l : ℕ) : ℝ) ≤ Real.exp Ppres) :
    ((∏ l ∈ Finset.univ.filter (fun l => b l ≠ 0 ∨ e l ≠ 0 ∨ p l ≤ cutoff),
      p l ^ A l : ℕ) : ℝ) ≤
      Real.exp ((depth : ℝ) *
        (Pbad + Ppres + ((cutoff + 1 : ℕ) : ℝ) * Real.log (cutoff + 1))) := by
  apply retainedPrimePowerModulus_le_exp_charged_cutoff
    p A b e cutoff depth hp hinj _ _ _ Pbad Ppres hbad hpres
  · intro l hl
    exact (Finset.mem_filter.mp hl).2
  · intro l _
    exact hA l

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem primePowerProduct_expBudget_nonneg
    {L : Type*} [Fintype L] (p b : L → ℕ) (hp : ∀ l, 1 ≤ p l)
    (P : ℝ) (hP : ((∏ l, p l ^ b l : ℕ) : ℝ) ≤ Real.exp P) : 0 ≤ P := by
  have hnat : 1 ≤ ∏ l, p l ^ b l :=
    Finset.one_le_prod (fun l _ => one_le_pow₀ (hp l))
  have hreal : (1 : ℝ) ≤ ((∏ l, p l ^ b l : ℕ) : ℝ) := by exact_mod_cast hnat
  exact Real.one_le_exp_iff.mp (hreal.trans hP)

theorem retainedPrimePower_cutoff_logCost_nonneg (cutoff : ℕ) :
    0 ≤ ((cutoff + 1 : ℕ) : ℝ) * Real.log (cutoff + 1) := by
  apply mul_nonneg (Nat.cast_nonneg _)
  apply Real.log_nonneg
  have hc : (0 : ℝ) ≤ cutoff := Nat.cast_nonneg cutoff
  linarith

theorem retainedPrimePowerModulus_le_exp_depthBudget
    {L : Type*} [Fintype L] (p A b e : L → ℕ) (cutoff depth : ℕ)
    (hp : ∀ l, 1 ≤ p l) (hinj : Function.Injective p)
    (retained : Finset L)
    (hretained : ∀ l ∈ retained, b l ≠ 0 ∨ e l ≠ 0 ∨ p l ≤ cutoff)
    (hA : ∀ l ∈ retained, A l ≤ depth) (Pbad Ppres Pdepth : ℝ)
    (hbad : ((∏ l, p l ^ b l : ℕ) : ℝ) ≤ Real.exp Pbad)
    (hpres : ((∏ l, p l ^ e l : ℕ) : ℝ) ≤ Real.exp Ppres)
    (hdepth : (depth : ℝ) ≤ Pdepth) :
    ((∏ l ∈ retained, p l ^ A l : ℕ) : ℝ) ≤
      Real.exp (Pdepth *
        (Pbad + Ppres + ((cutoff + 1 : ℕ) : ℝ) * Real.log (cutoff + 1))) := by
  have hcost : 0 ≤ Pbad + Ppres +
      ((cutoff + 1 : ℕ) : ℝ) * Real.log (cutoff + 1) :=
    add_nonneg (add_nonneg (primePowerProduct_expBudget_nonneg p b hp Pbad hbad)
      (primePowerProduct_expBudget_nonneg p e hp Ppres hpres))
      (retainedPrimePower_cutoff_logCost_nonneg cutoff)
  exact (retainedPrimePowerModulus_le_exp_charged_cutoff
    p A b e cutoff depth hp hinj retained hretained hA Pbad Ppres hbad hpres).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hdepth hcost))

theorem log_retainedPrimePowerModulus_le_depthBudget
    {L : Type*} [Fintype L] (p A b e : L → ℕ) (cutoff depth : ℕ)
    (hp : ∀ l, 1 ≤ p l) (hinj : Function.Injective p)
    (retained : Finset L)
    (hretained : ∀ l ∈ retained, b l ≠ 0 ∨ e l ≠ 0 ∨ p l ≤ cutoff)
    (hA : ∀ l ∈ retained, A l ≤ depth) (Pbad Ppres Pdepth : ℝ)
    (hbad : ((∏ l, p l ^ b l : ℕ) : ℝ) ≤ Real.exp Pbad)
    (hpres : ((∏ l, p l ^ e l : ℕ) : ℝ) ≤ Real.exp Ppres)
    (hdepth : (depth : ℝ) ≤ Pdepth) :
    Real.log ((∏ l ∈ retained, p l ^ A l : ℕ) : ℝ) ≤
      Pdepth * (Pbad + Ppres +
        ((cutoff + 1 : ℕ) : ℝ) * Real.log (cutoff + 1)) := by
  have hnat : 1 ≤ ∏ l ∈ retained, p l ^ A l :=
    Finset.one_le_prod (fun l _ => one_le_pow₀ (hp l))
  have hreal : (1 : ℝ) ≤ ((∏ l ∈ retained, p l ^ A l : ℕ) : ℝ) := by
    exact_mod_cast hnat
  apply (Real.log_le_iff_le_exp (zero_lt_one.trans_le hreal)).mpr
  exact retainedPrimePowerModulus_le_exp_depthBudget
    p A b e cutoff depth hp hinj retained hretained hA Pbad Ppres Pdepth hbad hpres hdepth

theorem log_retainedPrimePowerModulus_filter_le_depthBudget
    {L : Type*} [Fintype L] (p A b e : L → ℕ) (cutoff depth : ℕ)
    (hp : ∀ l, 1 ≤ p l) (hinj : Function.Injective p)
    (hA : ∀ l, A l ≤ depth) (Pbad Ppres Pdepth : ℝ)
    (hbad : ((∏ l, p l ^ b l : ℕ) : ℝ) ≤ Real.exp Pbad)
    (hpres : ((∏ l, p l ^ e l : ℕ) : ℝ) ≤ Real.exp Ppres)
    (hdepth : (depth : ℝ) ≤ Pdepth) :
    Real.log ((∏ l ∈ Finset.univ.filter
        (fun l => b l ≠ 0 ∨ e l ≠ 0 ∨ p l ≤ cutoff), p l ^ A l : ℕ) : ℝ) ≤
      Pdepth * (Pbad + Ppres +
        ((cutoff + 1 : ℕ) : ℝ) * Real.log (cutoff + 1)) := by
  apply log_retainedPrimePowerModulus_le_depthBudget
    p A b e cutoff depth hp hinj _ _ _ Pbad Ppres Pdepth hbad hpres hdepth
  · intro l hl
    exact (Finset.mem_filter.mp hl).2
  · intro l _
    exact hA l

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

local instance retainedReferencePrimeNeZero : ∀ p : path.primes, NeZero p.val :=
  path.primeNeZero

local instance retainedReferenceModulusNeZero : NeZero path.referenceModulus :=
  ⟨path.referenceModulus_pos.ne'⟩

noncomputable def referenceRetainedPrimes (cutoff : ℕ) : Finset path.primes :=
  Finset.univ.filter (fun p => path.referenceBadDepth p.val ≠ 0 ∨
    path.prescribed p.val ≠ 0 ∨ p.val ≤ cutoff)

omit [Fintype Tsp] in
theorem referenceRetainedPrimes_omitted (cutoff : ℕ) (p : path.primes)
    (hp : p ∉ path.referenceRetainedPrimes cutoff) :
    cutoff < p.val ∧ path.referenceBadDepth p.val = 0 ∧ path.prescribed p.val = 0 := by
  simp only [referenceRetainedPrimes, Finset.mem_filter, Finset.mem_univ, true_and,
    not_or, not_not] at hp
  exact ⟨Nat.lt_of_not_ge hp.2.2, hp.1, hp.2.1⟩

noncomputable def referenceLocalDensity
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (β : Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod path.referenceModulus)
    (p : path.primes) : ℝ :=
  rationalOutputDensity
    (FiniteProbabilityWeights.uniform
      (LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B →
        ZMod (p.val ^ path.exponent p.val)))
    (localPrimePowerIntegerPolynomialOutput p.val (path.exponent p.val) (path.prescribed p.val)
      (path.localReferencePolynomial raw) (path.origin p)) (p.val ^ path.exponent p.val)
    (fun j => ZMod.castHom (Finset.dvd_prod_of_mem
      (fun p : path.primes => p.val ^ path.exponent p.val) (Finset.mem_univ p))
      (ZMod (p.val ^ path.exponent p.val)) (β j))

omit [Fintype Tsp] in
theorem referenceLocalDensity_nonneg
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (β : Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod path.referenceModulus)
    (p : path.primes) : 0 ≤ path.referenceLocalDensity raw β p :=
  rationalOutputDensity_nonneg _ _ _ _

omit [Fintype Tsp] in

theorem reference_rational_density_product
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (β : Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod path.referenceModulus) :
    rationalOutputDensity path.referenceInputLaw
      (integerLongPolynomialOutput path.referencePolynomial raw path.referenceModulus)
      path.referenceModulus β = ∏ p : path.primes, path.referenceLocalDensity raw β p := by
  dsimp only [referenceInputLaw, referenceLocalDensity, referencePolynomial,
    localReferencePolynomial, referenceModulus]
  have h := allocatedForecastPolynomial_rational_density_product
    (allocatedShortAxis (I := I) U b S.value) path.noise (allocatedReadDeck path.read)
    (fun j a => allocatedReadProjection path.read ⟨j, a.val⟩)
    path.primes path.exponent path.prescribed path.prime path.base path.origin raw β
  simp only [rationalOutputDensity, ← Nat.card_eq_fintype_card] at h ⊢
  exact h

noncomputable def retainedReferenceForecast {Ω Z : Type*} [Fintype Ω]
    (inactive : FiniteProbabilityWeights Ω) (gridPoint : Ω → Z)
    (raw : Ω → PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (cutoff : ℕ) (gridVolume : ℝ) (z : Z)
    (β : Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod path.referenceModulus) : ℝ :=
  gridVolume * inactive.fiberMean gridPoint z (fun i =>
    ∏ p ∈ path.referenceRetainedPrimes cutoff, path.referenceLocalDensity (raw i) β p)

omit [Fintype Tsp] in
theorem reference_inactive_density_product {Ω Z : Type*} [Fintype Ω]
    (inactive : FiniteProbabilityWeights Ω) (gridPoint : Ω → Z)
    (raw : Ω → PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (gridVolume : ℝ) (z : Z)
    (β : Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod path.referenceModulus) :
    rationalInactiveForecast inactive (fun _ => path.referenceInputLaw) gridPoint
      (fun i => integerLongPolynomialOutput path.referencePolynomial (raw i) path.referenceModulus)
      path.referenceModulus gridVolume z β =
    gridVolume * inactive.fiberMean gridPoint z
      (fun i => ∏ p : path.primes, path.referenceLocalDensity (raw i) β p) := by
  unfold rationalInactiveForecast
  simp_rw [path.reference_rational_density_product]

omit [Fintype Tsp] in

theorem reference_inactive_goodPrimeDeletion {Ω Z : Type*} [Fintype Ω]
    (hm : 0 < m)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod)
    (inactive : FiniteProbabilityWeights Ω) (gridPoint : Ω → Z)
    (raw : Ω → PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (cutoff : ℕ) (hcutoff : 0 < cutoff) (hsmall : 2 / (cutoff : ℝ) ≤ 1 / 2)
    {δ : ℝ} (hδ : 0 ≤ δ) (haccuracy : 4 / (cutoff : ℝ) ≤ δ)
    (gridVolume : ℝ) (hvolume : 0 ≤ gridVolume) (z : Z)
    (β : Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod path.referenceModulus) :
    let full := rationalInactiveForecast inactive (fun _ => path.referenceInputLaw) gridPoint
      (fun i => integerLongPolynomialOutput path.referencePolynomial (raw i) path.referenceModulus)
      path.referenceModulus gridVolume z β
    let truncated := path.retainedReferenceForecast inactive gridPoint raw cutoff gridVolume z β
    (1 - δ) * truncated ≤ full ∧ full ≤ (1 + δ) * truncated := by
  dsimp only
  rw [path.reference_inactive_density_product]
  unfold retainedReferenceForecast
  apply inactive.fiberMean_prod_bounds_of_omitted_prod_sub_one_le gridPoint z
    gridVolume δ hvolume hδ (path.referenceRetainedPrimes cutoff)
    (fun i p => path.referenceLocalDensity (raw i) β p)
    (fun i p => path.referenceLocalDensity_nonneg (raw i) β p)
  intro i
  apply (indexed_good_prime_product_tail (fun p : path.primes => p.val) Subtype.val_injective
    (Finset.univ \ path.referenceRetainedPrimes cutoff)
    (fun p => path.referenceLocalDensity (raw i) β p) cutoff hcutoff hsmall ?_
    (fun p _ => path.referenceLocalDensity_nonneg (raw i) β p) ?_).trans haccuracy
  · intro p hp
    exact (path.referenceRetainedPrimes_omitted cutoff p (Finset.mem_sdiff.mp hp).2).1
  · intro p hp
    obtain ⟨_, hbad, hpres⟩ :=
      path.referenceRetainedPrimes_omitted cutoff p (Finset.mem_sdiff.mp hp).2
    exact (path.localReference_uncharged_density hm hD (raw i) p hbad hpres _).1

noncomputable def referenceRetainedModulus (cutoff : ℕ) : ℕ :=
  ∏ p ∈ path.referenceRetainedPrimes cutoff, p.val ^ path.exponent p.val

omit [Fintype Tsp] in
theorem referenceRetainedModulus_le (cutoff depth : ℕ)
    (hdepth : ∀ p : path.primes, path.exponent p.val ≤ depth) :
    path.referenceRetainedModulus cutoff ≤
      (path.Rbad * (∏ p : path.primes, p.val ^ path.prescribed p.val) *
        (cutoff + 1) ^ (cutoff + 1)) ^ depth := by
  have h := retainedPrimePowerModulus_filter_le_charged_cutoff
    (fun p : path.primes => p.val) (fun p : path.primes => path.exponent p.val)
    (fun p : path.primes => path.referenceBadDepth p.val)
    (fun p : path.primes => path.prescribed p.val) cutoff depth
    (fun p => (path.prime p.val p.property).one_le) Subtype.val_injective hdepth
  apply h.trans
  exact pow_le_pow_left' (Nat.mul_le_mul_right _
    (Nat.mul_le_mul_right _ path.referenceBadDepth_product_le)) depth

omit [Fintype Tsp] in

theorem referenceRetainedModulus_le_exp (cutoff depth : ℕ)
    (hdepth : ∀ p : path.primes, path.exponent p.val ≤ depth) :
    (path.referenceRetainedModulus cutoff : ℝ) ≤
      Real.exp ((depth : ℝ) *
        (Pbad + Ppres + ((cutoff + 1 : ℕ) : ℝ) * Real.log (cutoff + 1))) := by
  apply retainedPrimePowerModulus_filter_le_exp_charged_cutoff
    (fun p : path.primes => p.val) (fun p : path.primes => path.exponent p.val)
    (fun p : path.primes => path.referenceBadDepth p.val)
    (fun p : path.primes => path.prescribed p.val) cutoff depth
    (fun p => (path.prime p.val p.property).one_le) Subtype.val_injective hdepth
    Pbad Ppres
  · exact (Nat.cast_le.mpr path.referenceBadDepth_product_le).trans path.RbadBound
  · exact path.presBound

omit [Fintype Tsp] in
theorem referenceRetainedModulus_pos (cutoff : ℕ) :
    0 < path.referenceRetainedModulus cutoff := by
  apply Finset.prod_pos
  intro p _
  exact pow_pos (path.prime p.val p.property).pos _

omit [Fintype Tsp] in
theorem referenceRetainedModulus_dvd (cutoff : ℕ) :
    path.referenceRetainedModulus cutoff ∣ path.referenceModulus :=
  Finset.prod_dvd_prod_of_subset (path.referenceRetainedPrimes cutoff) Finset.univ
    (fun p : path.primes => p.val ^ path.exponent p.val) (Finset.subset_univ _)

omit [Fintype Tsp] in

theorem referenceRetainedModulus_log_le (cutoff depth : ℕ)
    (hdepth : ∀ p : path.primes, path.exponent p.val ≤ depth)
    (Pdepth : ℝ) (hPdepth : (depth : ℝ) ≤ Pdepth) :
    Real.log (path.referenceRetainedModulus cutoff : ℝ) ≤
      Pdepth * (Pbad + Ppres + ((cutoff + 1 : ℕ) : ℝ) * Real.log (cutoff + 1)) := by
  apply log_retainedPrimePowerModulus_filter_le_depthBudget
    (fun p : path.primes => p.val) (fun p : path.primes => path.exponent p.val)
    (fun p : path.primes => path.referenceBadDepth p.val)
    (fun p : path.primes => path.prescribed p.val) cutoff depth
    (fun p => (path.prime p.val p.property).one_le) Subtype.val_injective hdepth
    Pbad Ppres Pdepth
  · exact (Nat.cast_le.mpr path.referenceBadDepth_product_le).trans path.RbadBound
  · exact path.presBound
  · exact hPdepth

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI
