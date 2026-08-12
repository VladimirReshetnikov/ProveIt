import PolynomialFormulas.LazardQuinticRootRadicals
import PolynomialFormulas.FrobeniusDummitResolvent

namespace LeanProofs.PolynomialFormulas.LazardQuintic

open Fin5Solvable FrobeniusDummitResolvent

set_option autoImplicit false

/-- Reorder a root tuple by a permutation.  The multiplication convention is
chosen so that reordering by `g * h` means first reordering by `g`, then by
`h`. -/
def permuteRootTuple {K : Type*} (x : Fin 5 → K)
    (g : Fin5Solvable.S5) : Fin 5 → K :=
  fun i ↦ x (g i)

@[simp] theorem permuteRootTuple_mul
    {K : Type*} (x : Fin 5 → K)
    (g h : Fin5Solvable.S5) :
    permuteRootTuple x (g * h) =
      permuteRootTuple (permuteRootTuple x g) h := by
  rfl

@[simp] theorem permuteRootTuple_one
    {K : Type*} (x : Fin 5 → K) :
    permuteRootTuple x 1 = x := by
  funext i
  simp [permuteRootTuple]

theorem permuteRootTuple_injective
    {K : Type*} {x : Fin 5 → K} (hx : Function.Injective x)
    (g : Fin5Solvable.S5) :
    Function.Injective (permuteRootTuple x g) :=
  hx.comp g.injective

/-- The quotient of Lazard's two cyclic difference products. -/
def rootCyclicRatio {K : Type*} [Field K] (x : Fin 5 → K) : K :=
  rootTPrime x / rootUPrime x

theorem map_rootTPrime
    {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (x : Fin 5 → K) :
    f (rootTPrime x) = rootTPrime (fun i ↦ f (x i)) := by
  simp [rootTPrime]

theorem map_rootUPrime
    {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (x : Fin 5 → K) :
    f (rootUPrime x) = rootUPrime (fun i ↦ f (x i)) := by
  simp [rootUPrime]

theorem map_rootCyclicRatio
    {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (x : Fin 5 → K) :
    f (rootCyclicRatio x) = rootCyclicRatio (fun i ↦ f (x i)) := by
  simp [rootCyclicRatio, map_rootTPrime, map_rootUPrime]

@[simp] theorem rootTPrime_permute_fiveCycle
    {K : Type*} [Field K] (x : Fin 5 → K) :
    rootTPrime (permuteRootTuple x fiveCycle) = rootTPrime x := by
  simp [rootTPrime, permuteRootTuple, fiveCycle, finRotate_apply]
  ring

@[simp] theorem rootUPrime_permute_fiveCycle
    {K : Type*} [Field K] (x : Fin 5 → K) :
    rootUPrime (permuteRootTuple x fiveCycle) = rootUPrime x := by
  simp [rootUPrime, permuteRootTuple, fiveCycle, finRotate_apply]
  ring

@[simp] theorem rootTPrime_permute_multiplierTwo
    {K : Type*} [Field K] (x : Fin 5 → K) :
    rootTPrime (permuteRootTuple x multiplierTwo) = rootUPrime x := by
  simp [rootTPrime, rootUPrime, permuteRootTuple, multiplierTwo]
  ring

@[simp] theorem rootUPrime_permute_multiplierTwo
    {K : Type*} [Field K] (x : Fin 5 → K) :
    rootUPrime (permuteRootTuple x multiplierTwo) = -rootTPrime x := by
  simp [rootTPrime, rootUPrime, permuteRootTuple, multiplierTwo]
  ring

theorem rootCyclicSumSq_permute_multiplierTwo
    {K : Type*} [Field K] (x : Fin 5 → K) :
    rootTPrime (permuteRootTuple x multiplierTwo) ^ 2 +
        rootUPrime (permuteRootTuple x multiplierTwo) ^ 2 =
      rootTPrime x ^ 2 + rootUPrime x ^ 2 := by
  rw [rootTPrime_permute_multiplierTwo, rootUPrime_permute_multiplierTwo]
  ring

theorem rootCyclicRatio_permute_multiplierTwo
    {K : Type*} [Field K] {x : Fin 5 → K}
    (hx : Function.Injective x)
    (hzero : rootTPrime x ^ 2 + rootUPrime x ^ 2 = 0) :
    rootCyclicRatio (permuteRootTuple x multiplierTwo) =
      rootCyclicRatio x := by
  have hT := rootTPrime_ne_zero hx
  have hU := rootUPrime_ne_zero hx
  simp only [rootCyclicRatio, rootTPrime_permute_multiplierTwo,
    rootUPrime_permute_multiplierTwo]
  field_simp [hT, hU]
  linear_combination -hzero

theorem rootTPrime_permute_fiveCycle_pow
    {K : Type*} [Field K] (x : Fin 5 → K) (n : ℕ) :
    rootTPrime (permuteRootTuple x (fiveCycle ^ n)) = rootTPrime x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, permuteRootTuple_mul,
        rootTPrime_permute_fiveCycle, ih]

theorem rootUPrime_permute_fiveCycle_pow
    {K : Type*} [Field K] (x : Fin 5 → K) (n : ℕ) :
    rootUPrime (permuteRootTuple x (fiveCycle ^ n)) = rootUPrime x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, permuteRootTuple_mul,
        rootUPrime_permute_fiveCycle, ih]

theorem rootCyclicSumSq_permute_multiplierTwo_pow
    {K : Type*} [Field K] (x : Fin 5 → K) (n : ℕ) :
    rootTPrime (permuteRootTuple x (multiplierTwo ^ n)) ^ 2 +
        rootUPrime (permuteRootTuple x (multiplierTwo ^ n)) ^ 2 =
      rootTPrime x ^ 2 + rootUPrime x ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hp : multiplierTwo ^ (n + 1) =
          multiplierTwo ^ n * multiplierTwo := pow_succ _ _
      rw [hp, permuteRootTuple_mul,
        rootCyclicSumSq_permute_multiplierTwo, ih]

theorem rootCyclicRatio_permute_multiplierTwo_pow
    {K : Type*} [Field K] {x : Fin 5 → K}
    (hx : Function.Injective x)
    (hzero : rootTPrime x ^ 2 + rootUPrime x ^ 2 = 0)
    (n : ℕ) :
    rootCyclicRatio (permuteRootTuple x (multiplierTwo ^ n)) =
      rootCyclicRatio x := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hp : multiplierTwo ^ (n + 1) =
          multiplierTwo ^ n * multiplierTwo := pow_succ _ _
      rw [hp, permuteRootTuple_mul]
      calc
        rootCyclicRatio
            (permuteRootTuple
              (permuteRootTuple x (multiplierTwo ^ n)) multiplierTwo) =
            rootCyclicRatio (permuteRootTuple x (multiplierTwo ^ n)) := by
          apply rootCyclicRatio_permute_multiplierTwo
          · exact permuteRootTuple_injective hx _
          · rw [rootCyclicSumSq_permute_multiplierTwo_pow, hzero]
        _ = rootCyclicRatio x := ih

/-- Every element of the concrete affine copy of `F₂₀` has a unique
normal form `fiveCycle^a * multiplierTwo^b`. -/
theorem affineElementSubtype_surjective :
    Function.Surjective affineElementSubtype := by
  classical
  letI := Fintype.ofFinite affineF20
  have hcard : Fintype.card (Fin 5 × Fin 4) = Fintype.card affineF20 := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      Nat.card_prod, affineF20_eq_standardF20,
      Fin5TransitiveC5.natCard_standardF20]
    norm_num
  exact ((Fintype.bijective_iff_injective_and_card affineElementSubtype).2
    ⟨affineElementSubtype_injective, hcard⟩).2

/-- If `T'²+U'²=0`, the cyclic quotient `T'/U'` is invariant under the
standard Frobenius subgroup `F₂₀`.  The proof derives the action from the
two explicit generators, rather than accepting it as a certificate. -/
theorem rootCyclicRatio_permute_of_mem_standardF20
    {K : Type*} [Field K] {x : Fin 5 → K}
    (hx : Function.Injective x)
    (hzero : rootTPrime x ^ 2 + rootUPrime x ^ 2 = 0)
    (g : Fin5Solvable.S5) (hg : g ∈ standardF20) :
    rootCyclicRatio (permuteRootTuple x g) = rootCyclicRatio x := by
  have hg' : g ∈ affineF20 := by
    rw [affineF20_eq_standardF20]
    exact hg
  obtain ⟨ab, hab⟩ := affineElementSubtype_surjective ⟨g, hg'⟩
  have hgeq : g = affineElement ab := congrArg Subtype.val hab.symm
  rw [hgeq, affineElement, permuteRootTuple_mul]
  let y := permuteRootTuple x (fiveCycle ^ (ab.1 : ℕ))
  have hy : Function.Injective y := permuteRootTuple_injective hx _
  have hyzero : rootTPrime y ^ 2 + rootUPrime y ^ 2 = 0 := by
    dsimp only [y]
    rw [rootTPrime_permute_fiveCycle_pow,
      rootUPrime_permute_fiveCycle_pow, hzero]
  calc
    rootCyclicRatio (permuteRootTuple y (multiplierTwo ^ (ab.2 : ℕ))) =
        rootCyclicRatio y :=
      rootCyclicRatio_permute_multiplierTwo_pow hy hyzero _
    _ = rootCyclicRatio x := by
      simp only [rootCyclicRatio, y, rootTPrime_permute_fiveCycle_pow,
        rootUPrime_permute_fiveCycle_pow]

end LeanProofs.PolynomialFormulas.LazardQuintic
