import PolynomialFormulas.Fin5DihedralRelativeCore
import PolynomialFormulas.LazardGeneralResolventCriterion
import PolynomialFormulas.LazardQuinticRootBranchEquivariance
import PolynomialFormulas.LazardQuinticRootNondegeneracy

/-!
# Lazard's degree-five relative resolvents

This file packages the sharpness argument in Section 5 of Lazard's paper as
literal two-factor orbit products.  The two relevant subgroup indices are

* `C5 < D5`, with conjugate values `T'` and `-T'` (and likewise for `U'`);
* `D5 < F20`, with conjugate values `T' U'` and `-T' U'`, and likewise
  `epsilon` and `-epsilon`.

The proof does not take distinctness of the two values as a certificate.  It
derives it from nonvanishing and `2 != 0`, and then invokes the general
orbit-product separability criterion.  The representative-value lemmas below
also identify the quotient-indexed signed functions with the displayed root
expressions for every representative in the two ambient groups.
-/

open Polynomial

namespace LeanProofs.PolynomialFormulas.LazardSection5DegreeFiveRelativeResolvents

/- Lean 4.32 has no namespace-assignment aliases.  Re-export only this
file's dependency surface under the short local namespaces. -/
namespace Criterion
export LeanProofs.PolynomialFormulas.LazardGeneralResolventCriterion
  (Cosets baseCoset orbitResolvent orbitResolvent_separable_iff)
end Criterion

namespace Classification
export LeanProofs.PolynomialFormulas.Fin5DihedralRelativeCore
  (S5 mem_standardD5_iff reflection reflection_mem_standardD5
    relIndex_standardC5_standardD5 relIndex_standardD5_standardF20
    standardC5 standardD5 standardF20)
end Classification

open LazardQuintic
open Fin5Solvable FrobeniusDummitResolvent

set_option autoImplicit false

abbrev C5InD5 : Subgroup Classification.standardD5 :=
  Classification.standardC5.subgroupOf Classification.standardD5

abbrev D5InF20 : Subgroup Classification.standardF20 :=
  Classification.standardD5.subgroupOf Classification.standardF20

noncomputable local instance c5InD5CosetsFintype :
    Fintype (Criterion.Cosets C5InD5) :=
  Fintype.ofFinite _

noncomputable local instance d5InF20CosetsFintype :
    Fintype (Criterion.Cosets D5InF20) :=
  Fintype.ofFinite _

def d5Reflection : Classification.standardD5 :=
  ⟨Classification.reflection, Classification.reflection_mem_standardD5⟩

def f20MultiplierTwo : Classification.standardF20 :=
  ⟨multiplierTwo, multiplierTwo_mem_standardF20⟩

/-! ## A reusable two-coset signed orbit -/

noncomputable def signedTwoCosetValue
    {A K : Type*} [Group A] [AddGroup K]
    (G : Subgroup A) (t : K) : Criterion.Cosets G → K :=
  by
    classical
    exact fun c => if c = Criterion.baseCoset G then t else -t

theorem ne_neg_of_ne_zero_of_two_ne_zero
    {K : Type*} [Field K] {t : K}
    (ht : t ≠ 0) (htwo : (2 : K) ≠ 0) : t ≠ -t := by
  intro h
  have h' : -t = t := h.symm
  have hproduct : (2 : K) * t = 0 := by
    calc
      (2 : K) * t = t + t := two_mul t
      _ = -t + t := by rw [h']
      _ = 0 := neg_add_cancel t
  exact htwo ((mul_eq_zero.mp hproduct).resolve_right ht)

theorem signedTwoCosetValue_injective
    {A K : Type*} [Group A] [Field K]
    (G : Subgroup A) [Finite (Criterion.Cosets G)]
    (hcard : Nat.card (Criterion.Cosets G) = 2)
    (other : Criterion.Cosets G)
    (hother : other ≠ Criterion.baseCoset G)
    (t : K) (ht : t ≠ 0) (htwo : (2 : K) ≠ 0) :
    Function.Injective (signedTwoCosetValue G t) := by
  obtain ⟨uniqueOther, huniqueOther, hunique⟩ :=
    (Nat.card_eq_two_iff' (Criterion.baseCoset G)).mp hcard
  have hother_eq : other = uniqueOther := hunique other hother
  have hne : t ≠ -t := ne_neg_of_ne_zero_of_two_ne_zero ht htwo
  intro a b hab
  by_cases ha : a = Criterion.baseCoset G
  · by_cases hb : b = Criterion.baseCoset G
    · exact ha.trans hb.symm
    · have hab' : t = -t := by
        simpa [signedTwoCosetValue, ha, hb] using hab
      exact (hne hab').elim
  · by_cases hb : b = Criterion.baseCoset G
    · have hab' : -t = t := by
        simpa [signedTwoCosetValue, ha, hb] using hab
      exact (hne hab'.symm).elim
    · calc
        a = uniqueOther := hunique a ha
        _ = b := (hunique b hb).symm

/-! ## The concrete two-element quotients -/

theorem reflection_not_mem_standardC5 :
    Classification.reflection ∉ Classification.standardC5 := by
  rw [← Fin5TransitiveC5.mem_c5Elements_iff]
  decide

theorem multiplierTwo_not_mem_standardD5 :
    multiplierTwo ∉ Classification.standardD5 := by
  rw [Classification.mem_standardD5_iff]
  decide

theorem d5Reflection_coset_ne_base :
    (d5Reflection : Criterion.Cosets C5InD5) ≠
      Criterion.baseCoset C5InD5 := by
  intro h
  have hrel := QuotientGroup.leftRel_apply.mp (Quotient.exact' h)
  have hreflection_inv : Classification.reflection⁻¹ ∈
      Classification.standardC5 := by
    exact hrel
  have hreflection : Classification.reflection ∈ Classification.standardC5 := by
    simpa using Classification.standardC5.inv_mem hreflection_inv
  exact reflection_not_mem_standardC5 hreflection

theorem f20MultiplierTwo_coset_ne_base :
    (f20MultiplierTwo : Criterion.Cosets D5InF20) ≠
      Criterion.baseCoset D5InF20 := by
  intro h
  have hrel := QuotientGroup.leftRel_apply.mp (Quotient.exact' h)
  have hmultiplier_inv : multiplierTwo⁻¹ ∈ Classification.standardD5 := by
    exact hrel
  have hmultiplier : multiplierTwo ∈ Classification.standardD5 := by
    simpa using Classification.standardD5.inv_mem hmultiplier_inv
  exact multiplierTwo_not_mem_standardD5 hmultiplier

theorem natCard_C5InD5_cosets :
    Nat.card (Criterion.Cosets C5InD5) = 2 := by
  change C5InD5.index = 2
  exact Classification.relIndex_standardC5_standardD5

theorem natCard_D5InF20_cosets :
    Nat.card (Criterion.Cosets D5InF20) = 2 := by
  change D5InF20.index = 2
  exact Classification.relIndex_standardD5_standardF20

/-! ## The displayed sign actions -/

@[simp] theorem rootTPrime_permute_reflection
    {K : Type*} [Field K] (x : Fin 5 → K) :
    rootTPrime (permuteRootTuple x Classification.reflection) =
      -rootTPrime x := by
  have hperm :
      permuteRootTuple x Classification.reflection =
        ![x 0, x 4, x 3, x 2, x 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hperm]
  simp [rootTPrime]
  ring

@[simp] theorem rootUPrime_permute_reflection
    {K : Type*} [Field K] (x : Fin 5 → K) :
    rootUPrime (permuteRootTuple x Classification.reflection) =
      -rootUPrime x := by
  have hperm :
      permuteRootTuple x Classification.reflection =
        ![x 0, x 4, x 3, x 2, x 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hperm]
  simp [rootUPrime]
  ring

@[simp] theorem rootEpsilon_permute_fiveCycle_section5
    {K : Type*} [Field K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootEpsilon omega (permuteRootTuple x fiveCycle) =
      rootEpsilon omega x := by
  rw [rootEpsilon]
  congr 1
  simp [rootEpsilonProduct, permuteRootTuple,
    fiveCycle, finRotate_apply]
  ring

theorem rootEpsilon_permute_fiveCycle_pow_section5
    {K : Type*} [Field K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) (n : ℕ) :
    rootEpsilon omega (permuteRootTuple x (fiveCycle ^ n)) =
      rootEpsilon omega x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, permuteRootTuple_mul,
        rootEpsilon_permute_fiveCycle_section5, ih]

@[simp] theorem rootEpsilon_permute_reflection
    {K : Type*} [Field K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootEpsilon omega (permuteRootTuple x Classification.reflection) =
      rootEpsilon omega x := by
  have hperm :
      permuteRootTuple x Classification.reflection =
        ![x 0, x 4, x 3, x 2, x 1] := by
    funext i
    fin_cases i <;> rfl
  rw [rootEpsilon]
  rw [hperm]
  congr 1
  simp [rootEpsilonProduct]
  ring

set_option maxRecDepth 100000 in
theorem standardC5_power_decomposition :
    ∀ g : Classification.S5, g ∈ Classification.standardC5 →
      ∃ k : Fin 5, g = fiveCycle ^ (k : ℕ) := by
  simp only [← Fin5TransitiveC5.mem_c5Elements_iff]
  decide

set_option maxRecDepth 100000 in
theorem standardD5_decomposition :
    ∀ g : Classification.S5, g ∈ Classification.standardD5 →
      ∃ k : Fin 5,
        g = fiveCycle ^ (k : ℕ) ∨
        g = fiveCycle ^ (k : ℕ) * Classification.reflection := by
  simp only [Classification.mem_standardD5_iff]
  decide

set_option maxRecDepth 100000 in
theorem standardF20_D5_decomposition :
    ∀ g : Classification.S5, g ∈ Classification.standardF20 →
      g ∈ Classification.standardD5 ∨
      ∃ d : Classification.S5, d ∈ Classification.standardD5 ∧
        g = d * multiplierTwo := by
  simp only [← Fin5TransitiveC5.mem_f20Elements_iff,
    Classification.mem_standardD5_iff]
  decide

theorem rootTPrime_permute_of_mem_standardC5
    {K : Type*} [Field K] (x : Fin 5 → K)
    {g : Classification.S5} (hg : g ∈ Classification.standardC5) :
    rootTPrime (permuteRootTuple x g) = rootTPrime x := by
  obtain ⟨k, rfl⟩ := standardC5_power_decomposition g hg
  exact rootTPrime_permute_fiveCycle_pow x k

theorem rootUPrime_permute_of_mem_standardC5
    {K : Type*} [Field K] (x : Fin 5 → K)
    {g : Classification.S5} (hg : g ∈ Classification.standardC5) :
    rootUPrime (permuteRootTuple x g) = rootUPrime x := by
  obtain ⟨k, rfl⟩ := standardC5_power_decomposition g hg
  exact rootUPrime_permute_fiveCycle_pow x k

theorem rootEpsilon_permute_of_mem_standardD5
    {K : Type*} [Field K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K)
    {g : Classification.S5} (hg : g ∈ Classification.standardD5) :
    rootEpsilon omega (permuteRootTuple x g) = rootEpsilon omega x := by
  obtain ⟨k, hk | hk⟩ := standardD5_decomposition g hg
  · rw [hk]
    exact rootEpsilon_permute_fiveCycle_pow_section5 omega x k
  · rw [hk, permuteRootTuple_mul, rootEpsilon_permute_reflection]
    exact rootEpsilon_permute_fiveCycle_pow_section5 omega x k

/-! ## The intermediate discriminant resolvent for `D5 < F20` -/

/-- Lazard's evident degree-ten relative invariant `T' U'`. -/
def rootDiscriminantProduct
    {K : Type*} [Field K] (x : Fin 5 → K) : K :=
  rootTPrime x * rootUPrime x

@[simp] theorem rootDiscriminantProduct_permute_reflection
    {K : Type*} [Field K] (x : Fin 5 → K) :
    rootDiscriminantProduct
        (permuteRootTuple x Classification.reflection) =
      rootDiscriminantProduct x := by
  simp [rootDiscriminantProduct]

theorem rootDiscriminantProduct_permute_of_mem_standardD5
    {K : Type*} [Field K] (x : Fin 5 → K)
    {g : Classification.S5} (hg : g ∈ Classification.standardD5) :
    rootDiscriminantProduct (permuteRootTuple x g) =
      rootDiscriminantProduct x := by
  obtain ⟨k, hk | hk⟩ := standardD5_decomposition g hg
  · rw [hk, rootDiscriminantProduct,
      rootTPrime_permute_fiveCycle_pow,
      rootUPrime_permute_fiveCycle_pow]
    rfl
  · rw [hk, permuteRootTuple_mul,
      rootDiscriminantProduct_permute_reflection,
      rootDiscriminantProduct,
      rootTPrime_permute_fiveCycle_pow,
      rootUPrime_permute_fiveCycle_pow]
    rfl

@[simp] theorem rootDiscriminantProduct_permute_multiplierTwo
    {K : Type*} [Field K] (x : Fin 5 → K) :
    rootDiscriminantProduct (permuteRootTuple x multiplierTwo) =
      -rootDiscriminantProduct x := by
  simp [rootDiscriminantProduct,
    rootTPrime_permute_multiplierTwo,
    rootUPrime_permute_multiplierTwo]
  ring

noncomputable def rootDiscriminantD5F20Value
    {K : Type*} [Field K] (x : Fin 5 → K) :
    Criterion.Cosets D5InF20 → K :=
  signedTwoCosetValue D5InF20 (rootDiscriminantProduct x)

noncomputable def rootDiscriminantD5F20RelativeResolvent
    {K : Type*} [Field K] (x : Fin 5 → K) : K[X] :=
  Criterion.orbitResolvent D5InF20 (rootDiscriminantD5F20Value x)

theorem rootDiscriminantD5F20Value_representative
    {K : Type*} [Field K] (x : Fin 5 → K)
    (g : Classification.standardF20) :
    rootDiscriminantD5F20Value x (g : Criterion.Cosets D5InF20) =
      rootDiscriminantProduct (permuteRootTuple x g.1) := by
  by_cases hg : g.1 ∈ Classification.standardD5
  · have hcoset : (g : Criterion.Cosets D5InF20) =
        Criterion.baseCoset D5InF20 := by
      apply Quotient.sound'
      apply QuotientGroup.leftRel_apply.mpr
      exact Classification.standardD5.inv_mem hg
    rw [rootDiscriminantD5F20Value, signedTwoCosetValue,
      if_pos hcoset,
      rootDiscriminantProduct_permute_of_mem_standardD5 x hg]
  · obtain hd | ⟨d, hd, hgd⟩ :=
      standardF20_D5_decomposition g.1 g.2
    · exact (hg hd).elim
    · have hcoset : (g : Criterion.Cosets D5InF20) ≠
          Criterion.baseCoset D5InF20 := by
        intro h
        have hrel := QuotientGroup.leftRel_apply.mp (Quotient.exact' h)
        have hinv : g.1⁻¹ ∈ Classification.standardD5 := by
          exact hrel
        exact hg (by simpa using Classification.standardD5.inv_mem hinv)
      rw [rootDiscriminantD5F20Value, signedTwoCosetValue,
        if_neg hcoset, hgd, permuteRootTuple_mul,
        rootDiscriminantProduct_permute_multiplierTwo,
        rootDiscriminantProduct_permute_of_mem_standardD5 x hd]

theorem rootDiscriminantProduct_D5_F20_relativeOrbitResolvent_separable
    {K : Type*} [Field K] {x : Fin 5 → K}
    (hx : Function.Injective x) (htwo : (2 : K) ≠ 0) :
    (rootDiscriminantD5F20RelativeResolvent x).Separable := by
  rw [rootDiscriminantD5F20RelativeResolvent,
    Criterion.orbitResolvent_separable_iff]
  apply signedTwoCosetValue_injective D5InF20
    natCard_D5InF20_cosets
    (f20MultiplierTwo : Criterion.Cosets D5InF20)
    f20MultiplierTwo_coset_ne_base (rootDiscriminantProduct x)
  · exact mul_ne_zero (rootTPrime_ne_zero hx) (rootUPrime_ne_zero hx)
  · exact htwo

theorem rootTuple_rootDiscriminantProduct_D5_F20_relativeOrbitResolvent_separable
    (p : ℚ[X]) (hp : Irreducible p) (hdeg : p.natDegree = 5) :
    (rootDiscriminantD5F20RelativeResolvent
      (QuinticScalarGaloisBridge.rootTuple p hp hdeg)).Separable := by
  exact rootDiscriminantProduct_D5_F20_relativeOrbitResolvent_separable
    (QuinticScalarGaloisBridge.rootTuple_injective p hp hdeg)
    (by norm_num)

/-! ## `T'` and `U'` for `C5 < D5` -/

noncomputable def rootTPrimeC5D5Value
    {K : Type*} [Field K] (x : Fin 5 → K) :
    Criterion.Cosets C5InD5 → K :=
  signedTwoCosetValue C5InD5 (rootTPrime x)

noncomputable def rootUPrimeC5D5Value
    {K : Type*} [Field K] (x : Fin 5 → K) :
    Criterion.Cosets C5InD5 → K :=
  signedTwoCosetValue C5InD5 (rootUPrime x)

noncomputable def rootTPrimeC5D5RelativeResolvent
    {K : Type*} [Field K] (x : Fin 5 → K) : K[X] :=
  Criterion.orbitResolvent C5InD5 (rootTPrimeC5D5Value x)

noncomputable def rootUPrimeC5D5RelativeResolvent
    {K : Type*} [Field K] (x : Fin 5 → K) : K[X] :=
  Criterion.orbitResolvent C5InD5 (rootUPrimeC5D5Value x)

theorem rootTPrimeC5D5Value_representative
    {K : Type*} [Field K] (x : Fin 5 → K)
    (g : Classification.standardD5) :
    rootTPrimeC5D5Value x (g : Criterion.Cosets C5InD5) =
      rootTPrime (permuteRootTuple x g.1) := by
  by_cases hg : g.1 ∈ Classification.standardC5
  · have hcoset : (g : Criterion.Cosets C5InD5) =
        Criterion.baseCoset C5InD5 := by
      apply Quotient.sound'
      apply QuotientGroup.leftRel_apply.mpr
      exact Classification.standardC5.inv_mem hg
    rw [rootTPrimeC5D5Value, signedTwoCosetValue, if_pos hcoset,
      rootTPrime_permute_of_mem_standardC5 x hg]
  · obtain ⟨k, hk | hk⟩ := standardD5_decomposition g.1 g.2
    · apply (hg ?_).elim
      rw [hk]
      exact Classification.standardC5.pow_mem
        (Subgroup.mem_zpowers fiveCycle) k
    · have hcoset : (g : Criterion.Cosets C5InD5) ≠
          Criterion.baseCoset C5InD5 := by
        intro h
        have hrel := QuotientGroup.leftRel_apply.mp (Quotient.exact' h)
        have hinv : g.1⁻¹ ∈ Classification.standardC5 := by
          exact hrel
        exact hg (by simpa using Classification.standardC5.inv_mem hinv)
      rw [rootTPrimeC5D5Value, signedTwoCosetValue, if_neg hcoset,
        hk, permuteRootTuple_mul, rootTPrime_permute_reflection,
        rootTPrime_permute_fiveCycle_pow]

theorem rootUPrimeC5D5Value_representative
    {K : Type*} [Field K] (x : Fin 5 → K)
    (g : Classification.standardD5) :
    rootUPrimeC5D5Value x (g : Criterion.Cosets C5InD5) =
      rootUPrime (permuteRootTuple x g.1) := by
  by_cases hg : g.1 ∈ Classification.standardC5
  · have hcoset : (g : Criterion.Cosets C5InD5) =
        Criterion.baseCoset C5InD5 := by
      apply Quotient.sound'
      apply QuotientGroup.leftRel_apply.mpr
      exact Classification.standardC5.inv_mem hg
    rw [rootUPrimeC5D5Value, signedTwoCosetValue, if_pos hcoset,
      rootUPrime_permute_of_mem_standardC5 x hg]
  · obtain ⟨k, hk | hk⟩ := standardD5_decomposition g.1 g.2
    · apply (hg ?_).elim
      rw [hk]
      exact Classification.standardC5.pow_mem
        (Subgroup.mem_zpowers fiveCycle) k
    · have hcoset : (g : Criterion.Cosets C5InD5) ≠
          Criterion.baseCoset C5InD5 := by
        intro h
        have hrel := QuotientGroup.leftRel_apply.mp (Quotient.exact' h)
        have hinv : g.1⁻¹ ∈ Classification.standardC5 := by
          exact hrel
        exact hg (by simpa using Classification.standardC5.inv_mem hinv)
      rw [rootUPrimeC5D5Value, signedTwoCosetValue, if_neg hcoset,
        hk, permuteRootTuple_mul, rootUPrime_permute_reflection,
        rootUPrime_permute_fiveCycle_pow]

theorem rootTPrime_C5_D5_relativeOrbitResolvent_separable
    {K : Type*} [Field K]
    {x : Fin 5 → K} (hx : Function.Injective x)
    (htwo : (2 : K) ≠ 0) :
    (rootTPrimeC5D5RelativeResolvent x).Separable := by
  rw [rootTPrimeC5D5RelativeResolvent,
    Criterion.orbitResolvent_separable_iff]
  apply signedTwoCosetValue_injective C5InD5 natCard_C5InD5_cosets
    (d5Reflection : Criterion.Cosets C5InD5)
    d5Reflection_coset_ne_base (rootTPrime x)
  · exact rootTPrime_ne_zero hx
  · exact htwo

theorem rootUPrime_C5_D5_relativeOrbitResolvent_separable
    {K : Type*} [Field K]
    {x : Fin 5 → K} (hx : Function.Injective x)
    (htwo : (2 : K) ≠ 0) :
    (rootUPrimeC5D5RelativeResolvent x).Separable := by
  rw [rootUPrimeC5D5RelativeResolvent,
    Criterion.orbitResolvent_separable_iff]
  apply signedTwoCosetValue_injective C5InD5 natCard_C5InD5_cosets
    (d5Reflection : Criterion.Cosets C5InD5)
    d5Reflection_coset_ne_base (rootUPrime x)
  · exact rootUPrime_ne_zero hx
  · exact htwo

/-! The generic theorems above isolate the exact two hypotheses used by the
relative-resolvent calculation.  The following paper-facing wrappers close
the remaining quantifier for irreducible rational quintics: irreducibility
supplies a duplicate-free ordered root tuple, while characteristic zero
supplies `2 ≠ 0`.  Thus neither injectivity nor separability is a caller
certificate at these endpoints. -/

theorem rootTuple_rootTPrime_C5_D5_relativeOrbitResolvent_separable
    (p : ℚ[X]) (hp : Irreducible p) (hdeg : p.natDegree = 5) :
    (rootTPrimeC5D5RelativeResolvent
      (QuinticScalarGaloisBridge.rootTuple p hp hdeg)).Separable := by
  exact rootTPrime_C5_D5_relativeOrbitResolvent_separable
    (QuinticScalarGaloisBridge.rootTuple_injective p hp hdeg) (by norm_num)

theorem rootTuple_rootUPrime_C5_D5_relativeOrbitResolvent_separable
    (p : ℚ[X]) (hp : Irreducible p) (hdeg : p.natDegree = 5) :
    (rootUPrimeC5D5RelativeResolvent
      (QuinticScalarGaloisBridge.rootTuple p hp hdeg)).Separable := by
  exact rootUPrime_C5_D5_relativeOrbitResolvent_separable
    (QuinticScalarGaloisBridge.rootTuple_injective p hp hdeg) (by norm_num)

/-! ## `epsilon` for `D5 < F20` -/

noncomputable def rootEpsilonD5F20Value
    {K : Type*} [Field K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    Criterion.Cosets D5InF20 → K :=
  signedTwoCosetValue D5InF20 (rootEpsilon omega x)

noncomputable def rootEpsilonD5F20RelativeResolvent
    {K : Type*} [Field K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) : K[X] :=
  Criterion.orbitResolvent D5InF20 (rootEpsilonD5F20Value omega x)

theorem rootEpsilonD5F20Value_representative
    {K : Type*} [Field K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K)
    (g : Classification.standardF20) :
    rootEpsilonD5F20Value omega x (g : Criterion.Cosets D5InF20) =
      rootEpsilon omega (permuteRootTuple x g.1) := by
  by_cases hg : g.1 ∈ Classification.standardD5
  · have hcoset : (g : Criterion.Cosets D5InF20) =
        Criterion.baseCoset D5InF20 := by
      apply Quotient.sound'
      apply QuotientGroup.leftRel_apply.mpr
      exact Classification.standardD5.inv_mem hg
    rw [rootEpsilonD5F20Value, signedTwoCosetValue, if_pos hcoset,
      rootEpsilon_permute_of_mem_standardD5 omega x hg]
  · obtain hd | ⟨d, hd, hgd⟩ := standardF20_D5_decomposition g.1 g.2
    · exact (hg hd).elim
    · have hcoset : (g : Criterion.Cosets D5InF20) ≠
          Criterion.baseCoset D5InF20 := by
        intro h
        have hrel := QuotientGroup.leftRel_apply.mp (Quotient.exact' h)
        have hinv : g.1⁻¹ ∈ Classification.standardD5 := by
          exact hrel
        exact hg (by simpa using Classification.standardD5.inv_mem hinv)
      rw [rootEpsilonD5F20Value, signedTwoCosetValue, if_neg hcoset,
        hgd, permuteRootTuple_mul, rootEpsilon_permute_multiplierTwo,
        rootEpsilon_permute_of_mem_standardD5 omega x hd]

theorem rootEpsilon_D5_F20_relativeOrbitResolvent_separable
    {K : Type*} [Field K]
    (omega : FifthRootOfUnity K) {x : Fin 5 → K}
    (hepsilon : rootEpsilon omega x ≠ 0)
    (htwo : (2 : K) ≠ 0) :
    (rootEpsilonD5F20RelativeResolvent omega x).Separable := by
  rw [rootEpsilonD5F20RelativeResolvent,
    Criterion.orbitResolvent_separable_iff]
  apply signedTwoCosetValue_injective D5InF20 natCard_D5InF20_cosets
    (f20MultiplierTwo : Criterion.Cosets D5InF20)
    f20MultiplierTwo_coset_ne_base (rootEpsilon omega x) hepsilon
  exact htwo

theorem rootTuple_rootEpsilon_D5_F20_relativeOrbitResolvent_separable
    (c : DepressedQuintic ℚ) (hp : Irreducible c.polynomial)
    (omega : FifthRootOfUnity c.polynomial.SplittingField) :
    (rootEpsilonD5F20RelativeResolvent omega
      (QuinticScalarGaloisBridge.rootTuple c.polynomial hp
        c.polynomial_natDegree)).Separable := by
  exact rootEpsilon_D5_F20_relativeOrbitResolvent_separable omega
    (rootTuple_rootEpsilon_ne_zero c hp omega) (by norm_num)

/-- All three degree-five sharpness candidates on one irreducible depressed
rational quintic.  This is the premise-minimal paper-facing package: the
caller supplies the polynomial's irreducibility and the primitive fifth-root
data, but no root-injectivity, nonvanishing, orbit, or separability fact. -/
theorem rootTuple_section5_degreeFive_relativeOrbitResolvents_separable
    (c : DepressedQuintic ℚ) (hp : Irreducible c.polynomial)
    (omega : FifthRootOfUnity c.polynomial.SplittingField) :
    (rootTPrimeC5D5RelativeResolvent
        (QuinticScalarGaloisBridge.rootTuple c.polynomial hp
          c.polynomial_natDegree)).Separable ∧
      (rootUPrimeC5D5RelativeResolvent
        (QuinticScalarGaloisBridge.rootTuple c.polynomial hp
          c.polynomial_natDegree)).Separable ∧
      (rootEpsilonD5F20RelativeResolvent omega
        (QuinticScalarGaloisBridge.rootTuple c.polynomial hp
          c.polynomial_natDegree)).Separable := by
  exact ⟨
    rootTuple_rootTPrime_C5_D5_relativeOrbitResolvent_separable
      c.polynomial hp c.polynomial_natDegree,
    rootTuple_rootUPrime_C5_D5_relativeOrbitResolvent_separable
      c.polynomial hp c.polynomial_natDegree,
    rootTuple_rootEpsilon_D5_F20_relativeOrbitResolvent_separable c hp omega⟩

end LeanProofs.PolynomialFormulas.LazardSection5DegreeFiveRelativeResolvents
