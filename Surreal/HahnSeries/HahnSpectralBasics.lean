import Surreal.HahnSeries.Binomial
import Surreal.HahnSeries.ContinuumDefects
import Surreal.HahnSeries.DefectRigidity
import Surreal.HahnSeries.NoncommutativeNeumann
import Surreal.HahnSeries.SquareRoots
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# Inverse-smooth diagonal data, integer multiples, power images and rank-one completeness

This file proves four results of
`docs/surcomplex/infinite-dimensional-hahn-spectral-theory/article.tex`:
`ihs:hh:ex:smoothD` with the remark after it on `D - isI`, `ihs:dz:lem:group`,
`ihs:dz:lem:powers` and `ihs:hh:prop:complete`, together with the every-rank sequential form
of the completeness proof.

## The diagonal inverse-smooth space (`ihs:hh:ex:smoothD`)

As in `Surreal/HahnSeries/ContinuumDefects.lean`, the source space `H = ℓ²(ℕ_{≥1})` is
`ℓ²(ℕ, ℂ)` and the source index `n ≥ 1` is the Lean index `n - 1`, so `D = invDiag` acts by
`(D x)_n = x_n / (n + 1)` and `D^k` by `(D^k x)_n = x_n / (n + 1)^k` (`invDiagEnd_pow_apply`).
Hence `f ∈ Ran D^k` exactly when `((n + 1)^k f_n)_n ∈ ℓ²` (`mem_range_invDiagEnd_pow_iff`), and
then the unique preimage is `D^(-k) f = ((n + 1)^k f_n)_n` (`invDiagEnd_pow_eq_iff_of_memℓp`; for
`f` in the space `H_∞` below, `rapidPreimage` and `invDiagEnd_pow_eq_iff`).
The space `H_∞ = ⋂_k Ran D^k` (`rapidSpace`) consists exactly of the `f` with
`∑_n (n + 1)^(2k) |f_n|² < ∞` for every integer `k ≥ 1` (`mem_rapidSpace_iff`), which is
`ihs:hh:eq:rapidspace` in source indexing. For `s = t^η` with `η > 0` in any partially ordered
abelian group `Γ`, the equation `(D - sI) y = f` with constant `f` has a solution in
`H((t^Γ))` exactly when `f ∈ H_∞` (`exists_shiftResolvent_invDiag_iff`,
`exists_shiftResolvent_invDiag_iff_summable`), and the solution is then unique and equal to
`∑ s^n D^(-n-1) f` (`shiftResolvent_invDiag_eq_iff`). Finitely supported vectors lie in `H_∞`
(`mem_rapidSpace_of_finite`, `single_mem_rapidSpace`), so `H_∞` is dense in the ordinary
Hilbert topology (`dense_rapidSpace`). The vector `f_n = n^(-2)` (`powerVec 2`) equals
`D f^(1)` and so lies in `Ran D` (`invDiag_powerVec_one`, `powerVec_two_mem_range`), but it is
not in `Ran D²` and hence not in `H_∞` (`powerVec_two_notMem_range_sq`,
`powerVec_two_notMem_rapidSpace`), so `(D - sI) y = f` has no solution
(`not_exists_shiftResolvent_powerVec_two`).

For the remark after the example, `scaledShiftResolvent S c η` is `S - c s I` for a constant
`c`. For injective `S` on a vector space over any field and `c ≠ 0`, the equation
`(S - c s I) y = f` is `(c⁻¹ S - sI) y = c⁻¹ f` (`scaledShiftResolvent_eq_const_iff`). It is
solvable exactly when `f ∈ ⋂_{m ≥ 1} Ran S^m` (`exists_scaledShiftResolvent_eq_const_iff`), with
unique solution `∑ c^n s^n S^(-n-1) f` (`scaledShiftResolvent_eq_const_iff_eq_hsum`). For
`S = D` and `c = i` this gives the same criterion `f ∈ H_∞` for `D - isI`
(`exists_scaledShiftResolvent_invDiag_I_iff`) and the solution `∑ i^n s^n D^(-n-1) f`
(`scaledShiftResolvent_invDiag_I_eq_iff`).

## Integer-multiple subgroups (`ihs:dz:lem:group`)

Let `G` be an abelian group and `e_j`, `j ∈ s`, positive integers indexed by a finset. Then
`G = ⋃_j e_j G` exactly when `e_j G = G` for some `j` (`iUnion_range_nsmul_eq_univ_iff`); the
source's `s ≥ 1` is not needed for this equivalence. The proof follows the source: every proper
`e_j G` lies in a proper `p_j G` for a prime `p_j ∣ e_j` (`exists_prime_dvd_not_surjective`),
and one element avoids all the chosen `p G` (`exists_notMem_range_nsmul_primes`,
`exists_notMem_range_nsmul`). The source's Chinese-remainder combination is replaced by an
induction over the finite set of primes, adding `N • x_q` with `N` the product of the earlier
primes and using Bezout (`mem_range_nsmul_of_coprime`). If `G` is linearly ordered, `s` is
nonempty and the union is proper, the union omits a positive element
(`exists_pos_notMem_iUnion_range_nsmul`, `exists_pos_notMem_range_nsmul`).

## Power image (`ihs:dz:lem:powers`)

For a field `K` that is algebraically closed of characteristic zero, any linearly ordered
abelian group `Γ`, not necessarily divisible, and `e ≥ 1`, the `e`th powers of the elements of
positive valuation in `K((t^Γ))` are exactly `0` and the nonzero `ζ` of positive valuation with
`v(ζ) ∈ eΓ` (`exists_pow_eq_iff`); the source's case `K = ℂ` is `exists_pow_eq_iff_complex`.
The root is
`d^(1/e) t^γ (1 + k)^(1/e)`, with the binomial root from `Surreal/HahnSeries/Binomial.lean`.

## Rank-one completeness (`ihs:hh:prop:complete`)

For an additive subgroup `Γ ≤ ℝ` (the zero subgroup is allowed), `valSize x = e^(-v(x))`,
`valSize 0 = 0`, is an ultrametric size on `V((t^Γ))` for any additive group `V`
(`valSize_add_le`). For any additive commutative group `V`, `RankOneHahn Γ V`, a type synonym
for `V((t^Γ))`, carries the metric
`d(x, y) = valSize (x - y)`. It is an ultrametric space (`RankOneHahn.instIsUltrametricDist`)
and complete (`completeSpace_rankOneHahn`). The proof is the source's exact coefficient
stabilization: the limit is built by `exists_limit_of_eventually_agree`, which holds for every
linearly ordered `Γ` and any `V` with zero. For a sequence that agrees eventually at all
exponents `≤ R` for each cutoff `R`, it produces a Hahn series that the sequence eventually
agrees with below each cutoff, and that series is unique (`eq_of_eventually_agree`). This
sequential statement is not completeness of a uniform structure at higher rank, where nets
would be needed.

## Not covered

The comparison of the metric topology with the field-valued norm balls, stated before
`ihs:hh:prop:complete`, and the results that use these lemmas (`ihs:hh:thm:closedrange`,
`ihs:dz:lem:local`, `ihs:dz:thm:image`, `ihs:dz:thm:criterion`) are not formalized here.
-/

namespace Surreal.HahnSpectralBasics

open _root_.HahnSeries Filter Topology
open scoped ENNReal lp

noncomputable section

section ScaledShift

open Surreal.InfiniteSpectral

variable {Γ k V : Type*} [AddCommGroup Γ] [PartialOrder Γ] [IsOrderedAddMonoid Γ]
  [Field k] [AddCommGroup V] [Module k V]

/-- The operator `S - c s I` on `V((t^Γ))`, with `s = t^η` and a constant scalar `c`. For
`S = D` and `c = i` it is the operator `D - isI` of the remark after `ihs:hh:ex:smoothD`. -/
def scaledShiftResolvent (S : Module.End k V) (c : k) (η : Γ) (y : HahnModule Γ k V) :
    HahnModule Γ k V :=
  HahnModule.of k (((HahnModule.of k).symm y).map S) - single η c • y

theorem shiftResolvent_eq_scaledShiftResolvent_one (S : Module.End k V) (η : Γ) :
    shiftResolvent S η = scaledShiftResolvent S 1 η :=
  rfl

theorem coeff_scaledShiftResolvent (S : Module.End k V) (c : k) (η : Γ)
    (y : HahnModule Γ k V) (γ : Γ) :
    ((HahnModule.of k).symm (scaledShiftResolvent S c η y)).coeff γ =
      S (((HahnModule.of k).symm y).coeff γ) - c • ((HahnModule.of k).symm y).coeff (γ - η) := by
  rw [scaledShiftResolvent, HahnModule.of_symm_sub, coeff_sub, coeff_single_smul_hahnModule,
    Equiv.symm_apply_apply, map_coeff]

/-- For `c ≠ 0`, `(S - c s I) y = f` is equivalent to `(c⁻¹ S - sI) y = c⁻¹ f`. -/
theorem scaledShiftResolvent_eq_const_iff {c : k} (hc : c ≠ 0) (S : Module.End k V) (η : Γ)
    (y : HahnModule Γ k V) (f : V) :
    scaledShiftResolvent S c η y = HahnModule.of k (single 0 f) ↔
      shiftResolvent (c⁻¹ • S) η y = HahnModule.of k (single 0 (c⁻¹ • f)) := by
  have key : ∀ γ, ((HahnModule.of k).symm (shiftResolvent (c⁻¹ • S) η y)).coeff γ =
      c⁻¹ • ((HahnModule.of k).symm (scaledShiftResolvent S c η y)).coeff γ := by
    intro γ
    rw [coeff_shiftResolvent, coeff_scaledShiftResolvent, smul_sub, smul_smul,
      inv_mul_cancel₀ hc, one_smul, LinearMap.smul_apply]
  have key0 : ∀ γ,
      ((HahnModule.of k).symm (HahnModule.of k (single (0 : Γ) (c⁻¹ • f)))).coeff γ =
        c⁻¹ • ((HahnModule.of k).symm (HahnModule.of k (single (0 : Γ) f))).coeff γ := by
    intro γ
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    by_cases hγ : γ = 0
    · rw [hγ, coeff_single_same, coeff_single_same]
    · rw [coeff_single_of_ne hγ, coeff_single_of_ne hγ, smul_zero]
  constructor
  · intro h
    refine HahnModule.ext _ _ (funext fun γ => ?_)
    rw [key, key0, h]
  · intro h
    refine HahnModule.ext _ _ (funext fun γ => smul_right_injective V (inv_ne_zero hc) ?_)
    change c⁻¹ • _ = c⁻¹ • _
    rw [← key, ← key0, h]

theorem injective_inv_smul {S : Module.End k V} (hS : Function.Injective S) {c : k}
    (hc : c ≠ 0) : Function.Injective (c⁻¹ • S) := fun _ _ h =>
  hS (smul_right_injective V (inv_ne_zero hc) h)

/-- The remark after `ihs:hh:ex:smoothD`, generic form: for injective `S`, `c ≠ 0` and
`s = t^η` with `η > 0`, the equation `(S - c s I) y = f` with constant `f` is solvable exactly
when `f ∈ ⋂_{m ≥ 1} Ran S^m`, the same criterion as for `S - sI` (`ihs:hh:thm:smooth`). -/
theorem exists_scaledShiftResolvent_eq_const_iff {S : Module.End k V}
    (hS : Function.Injective S) {c : k} (hc : c ≠ 0) {η : Γ} (hη : 0 < η) (f : V) :
    (∃ y, scaledShiftResolvent S c η y = HahnModule.of k (single 0 f)) ↔
      ∀ n : ℕ, f ∈ LinearMap.range (S ^ (n + 1)) := by
  simp only [scaledShiftResolvent_eq_const_iff hc]
  rw [exists_shiftResolvent_eq_const_iff (injective_inv_smul hS hc) hη]
  refine forall_congr' fun n => ?_
  rw [smul_pow, LinearMap.range_smul _ _ (pow_ne_zero _ (inv_ne_zero hc)),
    Submodule.smul_mem_iff _ (inv_ne_zero hc)]

/-- The remark after `ihs:hh:ex:smoothD`, generic form: if `S^(n+1) u_n = f` for every `n`,
the unique solution of `(S - c s I) y = f` is `∑ c^n s^n S^(-n-1) f`. -/
theorem scaledShiftResolvent_eq_const_iff_eq_hsum {S : Module.End k V}
    (hS : Function.Injective S) {c : k} (hc : c ≠ 0) {η : Γ} (hη : 0 < η) {f : V}
    {u : ℕ → V} (hu : ∀ n, (S ^ (n + 1)) (u n) = f) (y : HahnModule Γ k V) :
    scaledShiftResolvent S c η y = HahnModule.of k (single 0 f) ↔
      y = HahnModule.of k (inverseSmoothFamily hη fun n => c ^ n • u n).hsum := by
  have hu' : ∀ n, ((c⁻¹ • S) ^ (n + 1)) (c ^ n • u n) = c⁻¹ • f := by
    intro n
    rw [smul_pow, LinearMap.smul_apply, map_smul, hu, smul_smul]
    congr 1
    rw [inv_pow, pow_succ, mul_inv, mul_comm (c ^ n)⁻¹ c⁻¹, mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ hc), mul_one]
  rw [scaledShiftResolvent_eq_const_iff hc]
  refine ⟨fun hy => eq_hsum_of_shiftResolvent_eq_const (injective_inv_smul hS hc) hη hy hu', ?_⟩
  rintro rfl
  exact shiftResolvent_hsum_inverseSmoothFamily (injective_inv_smul hS hc) hη hu'

end ScaledShift

section InverseSmoothDiagonal

open Surreal.ContinuumDefects Surreal.DefectRigidity Surreal.InfiniteSpectral

/-- `D^k` acts diagonally: `(D^k x)_n = x_n / (n + 1)^k` in the shifted indexing. -/
theorem invDiagEnd_pow_apply (k : ℕ) (x : ℓ²(ℕ, ℂ)) (n : ℕ) :
    (invDiagEnd ^ k) x n = x n / ((n : ℂ) + 1) ^ k := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    change invDiag x n / _ = _
    rw [invDiag_apply, div_div, pow_succ, mul_comm ((n : ℂ) + 1)]

/-- `f ∈ Ran D^k` exactly when `((n + 1)^k f_n)_n ∈ ℓ²`. -/
theorem mem_range_invDiagEnd_pow_iff (k : ℕ) (f : ℓ²(ℕ, ℂ)) :
    f ∈ LinearMap.range (invDiagEnd ^ k) ↔ Memℓp (fun n : ℕ => ((n : ℂ) + 1) ^ k * f n) 2 := by
  have hne : ∀ n : ℕ, ((n : ℂ) + 1) ^ k ≠ 0 := fun n => pow_ne_zero _ (Nat.cast_add_one_ne_zero n)
  constructor
  · intro hf
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hf
    convert lp.memℓp y using 1
    funext n
    rw [invDiagEnd_pow_apply, mul_div_cancel₀ _ (hne n)]
  · intro h
    refine LinearMap.mem_range.mpr ⟨⟨_, h⟩, lp.ext (funext fun n => ?_)⟩
    rw [invDiagEnd_pow_apply]
    change ((n : ℂ) + 1) ^ k * f n / ((n : ℂ) + 1) ^ k = f n
    exact mul_div_cancel_left₀ _ (hne n)

/-- `ihs:hh:ex:smoothD`, per-`k` form: if `f ∈ Ran D^k`, that is `((n + 1)^k f_n)_n ∈ ℓ²`
(`mem_range_invDiagEnd_pow_iff`), then `D^(-k) f = ((n + 1)^k f_n)_n` is the unique preimage of
`f` under `D^k`. -/
theorem invDiagEnd_pow_eq_iff_of_memℓp {k : ℕ} {f : ℓ²(ℕ, ℂ)}
    (hf : Memℓp (fun n : ℕ => ((n : ℂ) + 1) ^ k * f n) 2) (x : ℓ²(ℕ, ℂ)) :
    (invDiagEnd ^ k) x = f ↔ x = ⟨fun n : ℕ => ((n : ℂ) + 1) ^ k * f n, hf⟩ := by
  have hpre : (invDiagEnd ^ k) ⟨fun n : ℕ => ((n : ℂ) + 1) ^ k * f n, hf⟩ = f := by
    refine lp.ext (funext fun n => ?_)
    rw [invDiagEnd_pow_apply]
    change ((n : ℂ) + 1) ^ k * f n / ((n : ℂ) + 1) ^ k = f n
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ (Nat.cast_add_one_ne_zero n))
  refine ⟨fun hx => Module.End.iterate_injective injective_invDiagEnd k ?_, ?_⟩
  · rw [hx, hpre]
  · rintro rfl
    exact hpre

/-- The inverse-smooth space `H_∞ = ⋂_k Ran D^k` of `ihs:hh:eq:rapidspace`; see
`mem_rapidSpace_iff` for the source's moment description. -/
def rapidSpace : Submodule ℂ ℓ²(ℕ, ℂ) :=
  ⨅ k : ℕ, LinearMap.range (invDiagEnd ^ k)

/-- `f ∈ H_∞` exactly when `((n + 1)^k f_n)_n ∈ ℓ²` for every `k`. -/
theorem mem_rapidSpace_iff_memℓp (f : ℓ²(ℕ, ℂ)) :
    f ∈ rapidSpace ↔ ∀ k : ℕ, Memℓp (fun n : ℕ => ((n : ℂ) + 1) ^ k * f n) 2 := by
  simp only [rapidSpace, Submodule.mem_iInf, mem_range_invDiagEnd_pow_iff]

theorem norm_sq_natCast_add_one_pow_mul (k : ℕ) (a : ℂ) (n : ℕ) :
    ‖((n : ℂ) + 1) ^ k * a‖ ^ 2 = ((n : ℝ) + 1) ^ (2 * k) * ‖a‖ ^ 2 := by
  rw [norm_mul, norm_pow, norm_natCast_add_one, mul_pow, ← pow_mul, mul_comm k 2]

/-- `ihs:hh:eq:rapidspace`: `f ∈ H_∞` exactly when `∑_n (n + 1)^(2k) |f_n|² < ∞` for every
integer `k ≥ 1`. The Lean index `n` is the source index `n + 1`. -/
theorem mem_rapidSpace_iff (f : ℓ²(ℕ, ℂ)) :
    f ∈ rapidSpace ↔
      ∀ k : ℕ, 1 ≤ k → Summable fun n : ℕ => ((n : ℝ) + 1) ^ (2 * k) * ‖f n‖ ^ 2 := by
  rw [mem_rapidSpace_iff_memℓp]
  constructor
  · intro h k _
    have hs := (memℓp_two_iff_summable_sq _).mp (h k)
    simpa only [norm_sq_natCast_add_one_pow_mul] using hs
  · intro h k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa only [pow_zero, one_mul] using lp.memℓp f
    · rw [memℓp_two_iff_summable_sq]
      simpa only [norm_sq_natCast_add_one_pow_mul] using h k hk

/-- The preimage `D^(-k) f = ((n + 1)^k f_n)_n` of `f ∈ H_∞`, the source's `(n^k f_n)`. -/
def rapidPreimage {f : ℓ²(ℕ, ℂ)} (hf : f ∈ rapidSpace) (k : ℕ) : ℓ²(ℕ, ℂ) :=
  ⟨fun n : ℕ => ((n : ℂ) + 1) ^ k * f n, (mem_rapidSpace_iff_memℓp f).mp hf k⟩

theorem rapidPreimage_apply {f : ℓ²(ℕ, ℂ)} (hf : f ∈ rapidSpace) (k n : ℕ) :
    rapidPreimage hf k n = ((n : ℂ) + 1) ^ k * f n :=
  rfl

theorem invDiagEnd_pow_rapidPreimage {f : ℓ²(ℕ, ℂ)} (hf : f ∈ rapidSpace) (k : ℕ) :
    (invDiagEnd ^ k) (rapidPreimage hf k) = f := by
  refine lp.ext (funext fun n => ?_)
  rw [invDiagEnd_pow_apply, rapidPreimage_apply]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ (Nat.cast_add_one_ne_zero n))

/-- `ihs:hh:ex:smoothD`: `D^(-k) f = ((n + 1)^k f_n)_n` is the unique preimage of `f ∈ H_∞`
under `D^k`; see `invDiagEnd_pow_eq_iff_of_memℓp` for the form assuming only `f ∈ Ran D^k`. -/
theorem invDiagEnd_pow_eq_iff {f : ℓ²(ℕ, ℂ)} (hf : f ∈ rapidSpace) (k : ℕ) (x : ℓ²(ℕ, ℂ)) :
    (invDiagEnd ^ k) x = f ↔ x = rapidPreimage hf k :=
  invDiagEnd_pow_eq_iff_of_memℓp ((mem_rapidSpace_iff_memℓp f).mp hf k) x

variable {Γ : Type*} [AddCommGroup Γ] [PartialOrder Γ] [IsOrderedAddMonoid Γ]

/-- `ihs:hh:ex:smoothD`: for `s = t^η` with `η > 0`, the constant data `f` for which
`(D - sI) y = f` has a solution `y ∈ H((t^Γ))` are exactly the elements of `H_∞`. -/
theorem exists_shiftResolvent_invDiag_iff {η : Γ} (hη : 0 < η) (f : ℓ²(ℕ, ℂ)) :
    (∃ y, shiftResolvent invDiagEnd η y = HahnModule.of ℂ (single 0 f)) ↔ f ∈ rapidSpace := by
  rw [exists_shiftResolvent_eq_const_iff injective_invDiagEnd hη, rapidSpace,
    Submodule.mem_iInf]
  constructor
  · intro h k
    rcases k with _ | k
    · exact LinearMap.mem_range.mpr ⟨f, by rw [pow_zero, Module.End.one_apply]⟩
    · exact h k
  · intro h n
    exact h (n + 1)

/-- `ihs:hh:ex:smoothD` with `ihs:hh:eq:rapidspace`: `(D - sI) y = f` is solvable exactly
when `∑_n (n + 1)^(2k) |f_n|² < ∞` for every integer `k ≥ 1`. -/
theorem exists_shiftResolvent_invDiag_iff_summable {η : Γ} (hη : 0 < η) (f : ℓ²(ℕ, ℂ)) :
    (∃ y, shiftResolvent invDiagEnd η y = HahnModule.of ℂ (single 0 f)) ↔
      ∀ k : ℕ, 1 ≤ k → Summable fun n : ℕ => ((n : ℝ) + 1) ^ (2 * k) * ‖f n‖ ^ 2 := by
  rw [exists_shiftResolvent_invDiag_iff hη, mem_rapidSpace_iff]

/-- `ihs:hh:ex:smoothD` with `ihs:hh:eq:smoothsolution`: for `f ∈ H_∞` the unique solution of
`(D - sI) y = f` is `∑ s^n D^(-n-1) f`, with `D^(-n-1) f = ((m + 1)^(n+1) f_m)_m`. -/
theorem shiftResolvent_invDiag_eq_iff {η : Γ} (hη : 0 < η) {f : ℓ²(ℕ, ℂ)}
    (hf : f ∈ rapidSpace) (y : HahnModule Γ ℂ ℓ²(ℕ, ℂ)) :
    shiftResolvent invDiagEnd η y = HahnModule.of ℂ (single 0 f) ↔
      y = HahnModule.of ℂ (inverseSmoothFamily hη fun n => rapidPreimage hf (n + 1)).hsum := by
  have hu : ∀ n : ℕ, (invDiagEnd ^ (n + 1)) (rapidPreimage hf (n + 1)) = f :=
    fun n => invDiagEnd_pow_rapidPreimage hf (n + 1)
  refine ⟨fun hy => eq_hsum_of_shiftResolvent_eq_const injective_invDiagEnd hη hy hu, ?_⟩
  rintro rfl
  exact shiftResolvent_hsum_inverseSmoothFamily injective_invDiagEnd hη hu

/-- `ihs:hh:ex:smoothD`: finitely supported vectors belong to `H_∞`. -/
theorem mem_rapidSpace_of_finite {f : ℓ²(ℕ, ℂ)} (hf : {n | f n ≠ 0}.Finite) :
    f ∈ rapidSpace := by
  rw [mem_rapidSpace_iff_memℓp]
  intro k
  refine (memℓp_zero_iff.mpr (hf.subset fun n hn => ?_)).of_exponent_ge (by simp)
  exact right_ne_zero_of_mul hn

theorem single_mem_rapidSpace (n : ℕ) (c : ℂ) : lp.single 2 n c ∈ rapidSpace := by
  refine mem_rapidSpace_of_finite ((Set.finite_singleton n).subset fun m hm => ?_)
  by_contra h
  exact hm (by rw [lp.single_apply, Pi.single_eq_of_ne h])

/-- `ihs:hh:ex:smoothD`: `H_∞` is dense in the ordinary Hilbert topology. -/
theorem dense_rapidSpace : Dense (rapidSpace : Set ℓ²(ℕ, ℂ)) := by
  intro f
  refine mem_closure_of_tendsto (lp.hasSum_single ENNReal.ofNat_ne_top f).tendsto_sum_nat
    (Eventually.of_forall fun s => ?_)
  exact rapidSpace.sum_mem fun i _ => single_mem_rapidSpace i (f i)

/-- `D (n^(-1))_n = (n^(-2))_n`, in the shifted indexing. -/
theorem invDiag_powerVec_one :
    invDiag (powerVec 1 (by norm_num)) = powerVec 2 (by norm_num) := by
  refine lp.ext (funext fun n => ?_)
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hc : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [invDiag_apply, powerVec_apply, powerVec_apply, hc, ← Complex.ofReal_div]
  congr 1
  rw [Real.rpow_neg hpos.le, Real.rpow_neg hpos.le, Real.rpow_one, Real.rpow_two, sq,
    mul_inv, div_eq_mul_inv]

/-- `ihs:hh:ex:smoothD`: the vector `f_n = n^(-2)` lies in `Ran D`. -/
theorem powerVec_two_mem_range :
    powerVec 2 (by norm_num) ∈ LinearMap.range invDiagEnd :=
  LinearMap.mem_range.mpr ⟨powerVec 1 (by norm_num), invDiag_powerVec_one⟩

/-- The vector `f_n = n^(-2)` is not in `Ran D²`, since `(n² f_n)_n = (1)_n ∉ ℓ²`. -/
theorem powerVec_two_notMem_range_sq :
    powerVec 2 (by norm_num) ∉ LinearMap.range (invDiagEnd ^ 2) := by
  rw [mem_range_invDiagEnd_pow_iff, memℓp_two_iff_summable_sq]
  intro hs
  have hone : (fun n : ℕ => ‖((n : ℂ) + 1) ^ 2 * powerVec 2 (by norm_num) n‖ ^ 2) =
      fun _ => (1 : ℝ) := by
    funext n
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [norm_sq_natCast_add_one_pow_mul, powerVec_apply, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hpos.le _), Real.rpow_neg hpos.le, Real.rpow_two,
      inv_pow, ← pow_mul, mul_inv_cancel₀ (pow_ne_zero _ hpos.ne')]
  rw [hone] at hs
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hs.tendsto_atTop_zero)

/-- `ihs:hh:ex:smoothD`: the vector `f_n = n^(-2)` does not belong to `H_∞`. -/
theorem powerVec_two_notMem_rapidSpace : powerVec 2 (by norm_num) ∉ rapidSpace := by
  intro h
  exact powerVec_two_notMem_range_sq ((Submodule.mem_iInf _).mp h 2)

/-- `ihs:hh:ex:smoothD`: the data `f_n = n^(-2)`, which have an ordinary first preimage under
`D`, have no infinitesimal resolvent: `(D - sI) y = f` has no solution in `H((t^Γ))`. -/
theorem not_exists_shiftResolvent_powerVec_two {η : Γ} (hη : 0 < η) :
    ¬ ∃ y, shiftResolvent invDiagEnd η y =
      HahnModule.of ℂ (single 0 (powerVec 2 (by norm_num))) := by
  rw [exists_shiftResolvent_invDiag_iff hη]
  exact powerVec_two_notMem_rapidSpace

/-- The remark after `ihs:hh:ex:smoothD`: `(D - isI) y = f` with constant `f` is solvable
exactly when `f ∈ H_∞`. -/
theorem exists_scaledShiftResolvent_invDiag_I_iff {η : Γ} (hη : 0 < η) (f : ℓ²(ℕ, ℂ)) :
    (∃ y, scaledShiftResolvent invDiagEnd Complex.I η y = HahnModule.of ℂ (single 0 f)) ↔
      f ∈ rapidSpace := by
  rw [exists_scaledShiftResolvent_eq_const_iff injective_invDiagEnd Complex.I_ne_zero hη,
    ← exists_shiftResolvent_eq_const_iff injective_invDiagEnd hη,
    exists_shiftResolvent_invDiag_iff hη]

/-- The remark after `ihs:hh:ex:smoothD`: for `f ∈ H_∞` the unique solution of
`(D - isI) y = f` is `∑ i^n s^n D^(-n-1) f`. -/
theorem scaledShiftResolvent_invDiag_I_eq_iff {η : Γ} (hη : 0 < η) {f : ℓ²(ℕ, ℂ)}
    (hf : f ∈ rapidSpace) (y : HahnModule Γ ℂ ℓ²(ℕ, ℂ)) :
    scaledShiftResolvent invDiagEnd Complex.I η y = HahnModule.of ℂ (single 0 f) ↔
      y = HahnModule.of ℂ
        (inverseSmoothFamily hη fun n => Complex.I ^ n • rapidPreimage hf (n + 1)).hsum :=
  scaledShiftResolvent_eq_const_iff_eq_hsum injective_invDiagEnd Complex.I_ne_zero hη
    (fun n => invDiagEnd_pow_rapidPreimage hf (n + 1)) y

end InverseSmoothDiagonal

section IntegerMultiples

variable {G : Type*} [AddCommGroup G]

/-- Bezout step: if `m` and `p` are coprime and `m x ∈ pG`, then `x ∈ pG`. -/
theorem mem_range_nsmul_of_coprime {m p : ℕ} (h : Nat.Coprime m p) {x : G}
    (hx : m • x ∈ Set.range fun y : G => p • y) : x ∈ Set.range fun y : G => p • y := by
  obtain ⟨w, hw⟩ := hx
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr h
  have hw' : (p : ℤ) • w = (m : ℤ) • x := by
    rw [natCast_zsmul, natCast_zsmul]
    exact hw
  refine ⟨a • w + b • x, ?_⟩
  calc p • (a • w + b • x) = a • ((p : ℤ) • w) + b • ((p : ℤ) • x) := by
        rw [← natCast_zsmul, smul_add, smul_comm (p : ℤ) a w, smul_comm (p : ℤ) b x]
    _ = (a * m + b * p) • x := by rw [hw', add_smul, mul_smul, mul_smul]
    _ = x := by rw [hab, one_smul]

/-- If `eG ≠ G` with `e > 0`, then `pG ≠ G` for some prime `p ∣ e`. -/
theorem exists_prime_dvd_not_surjective {e : ℕ} (he : 0 < e)
    (h : ¬ Function.Surjective fun x : G => e • x) :
    ∃ p, p.Prime ∧ p ∣ e ∧ ¬ Function.Surjective fun x : G => p • x := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
  by_cases he1 : e = 1
  · subst he1
    exact absurd (fun x => ⟨x, one_nsmul x⟩) h
  obtain ⟨p, hp, hpe⟩ := Nat.exists_prime_and_dvd he1
  by_cases hsp : Function.Surjective fun x : G => p • x
  · obtain ⟨m, rfl⟩ := hpe
    have hm : 0 < m := Nat.pos_of_mul_pos_left he
    have hms : ¬ Function.Surjective fun x : G => m • x := by
      intro hms
      apply h
      intro z
      obtain ⟨y, rfl⟩ := hsp z
      obtain ⟨x, rfl⟩ := hms y
      exact ⟨x, mul_smul p m x⟩
    obtain ⟨q, hq, hqm, hqs⟩ := ih m (lt_mul_left hm hp.one_lt) hm hms
    exact ⟨q, hq, Dvd.dvd.mul_left hqm p, hqs⟩
  · exact ⟨p, hp, hpe, hsp⟩

/-- For finitely many primes `p` with `pG ≠ G`, one element of `G` lies in no `pG`. This
replaces the Chinese-remainder step of the proof of `ihs:dz:lem:group`. -/
theorem exists_notMem_range_nsmul_primes (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hns : ∀ p ∈ P, ¬ Function.Surjective fun x : G => p • x) :
    ∃ x : G, ∀ p ∈ P, x ∉ Set.range fun y : G => p • y := by
  induction P using Finset.induction_on with
  | empty => exact ⟨0, fun p hp => absurd hp (Finset.notMem_empty p)⟩
  | @insert q P hqP ih =>
    obtain ⟨x, hx⟩ := ih (fun p hp => hP p (Finset.mem_insert_of_mem hp))
      (fun p hp => hns p (Finset.mem_insert_of_mem hp))
    have hq := hP q (Finset.mem_insert_self q P)
    obtain ⟨xq, hxq⟩ : ∃ xq : G, xq ∉ Set.range fun y : G => q • y := by
      have h := hns q (Finset.mem_insert_self q P)
      rw [← Set.range_eq_univ] at h
      exact (Set.ne_univ_iff_exists_notMem _).mp h
    have hne : ∀ p ∈ P, p ≠ q := fun p hp hpq => hqP (hpq ▸ hp)
    refine ⟨q • x + (∏ p ∈ P, p) • xq, fun p hp => ?_⟩
    rcases Finset.mem_insert.mp hp with rfl | hp
    · rintro ⟨w, hw⟩
      refine hxq (mem_range_nsmul_of_coprime (m := ∏ p ∈ P, p) (Nat.Coprime.prod_left
        fun r hr => (Nat.coprime_primes (hP r (Finset.mem_insert_of_mem hr)) hq).mpr
          (hne r hr)) ⟨w - x, ?_⟩)
      dsimp only at hw ⊢
      rw [smul_sub, hw, add_sub_cancel_left]
    · rintro ⟨w, hw⟩
      obtain ⟨M, hM⟩ := Finset.dvd_prod_of_mem (fun r : ℕ => r) hp
      refine hx p hp (mem_range_nsmul_of_coprime (m := q)
        ((Nat.coprime_primes hq (hP p (Finset.mem_insert_of_mem hp))).mpr
          (hne p hp).symm) ⟨w - M • xq, ?_⟩)
      dsimp only at hw hM ⊢
      rw [smul_sub, hw, ← mul_smul, ← hM, add_sub_cancel_right]

/-- `ihs:dz:lem:group`, omission form: if each `e_j G`, `e_j > 0`, is proper, one element of
`G` lies in none of them. -/
theorem exists_notMem_range_nsmul {ι : Type*} (s : Finset ι) (e : ι → ℕ)
    (he : ∀ j ∈ s, 0 < e j) (hns : ∀ j ∈ s, ¬ Function.Surjective fun x : G => e j • x) :
    ∃ x : G, ∀ j ∈ s, x ∉ Set.range fun y : G => e j • y := by
  classical
  have hex : ∀ j ∈ s, ∃ p, p.Prime ∧ p ∣ e j ∧ ¬ Function.Surjective fun x : G => p • x :=
    fun j hj => exists_prime_dvd_not_surjective (he j hj) (hns j hj)
  choose! p hp hpe hps using hex
  obtain ⟨x, hx⟩ := exists_notMem_range_nsmul_primes (s.image p)
    (fun q hq => by
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
      exact hp j hj)
    (fun q hq => by
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
      exact hps j hj)
  refine ⟨x, fun j hj hxj => hx (p j) (Finset.mem_image_of_mem p hj) ?_⟩
  obtain ⟨y, hy⟩ := hxj
  obtain ⟨m, hm⟩ := hpe j hj
  refine ⟨m • y, ?_⟩
  dsimp only at hy ⊢
  rw [← mul_smul, ← hm, hy]

/-- `ihs:dz:lem:group`: for positive integers `e_j`, `G = ⋃_j e_j G` exactly when
`e_j G = G` for some `j`. -/
theorem iUnion_range_nsmul_eq_univ_iff {ι : Type*} (s : Finset ι) (e : ι → ℕ)
    (he : ∀ j ∈ s, 0 < e j) :
    (⋃ j ∈ s, Set.range fun y : G => e j • y) = Set.univ ↔
      ∃ j ∈ s, Set.range (fun y : G => e j • y) = Set.univ := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    obtain ⟨x, hx⟩ := exists_notMem_range_nsmul s e he
      fun j hj hsurj => hne j hj (Set.range_eq_univ.mpr hsurj)
    have hmem : x ∈ ⋃ j ∈ s, Set.range fun y : G => e j • y := h ▸ Set.mem_univ x
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hmem
    exact hx j hj hxj
  · rintro ⟨j, hj, hr⟩
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion₂.mpr ⟨j, hj, ?_⟩
    rw [hr]
    exact Set.mem_univ x

/-- `ihs:dz:lem:group`, ordered clause: in a linearly ordered abelian group, a proper union
`⋃_j e_j G` over a nonempty index set omits a positive element. -/
theorem exists_pos_notMem_iUnion_range_nsmul [LinearOrder G] [IsOrderedAddMonoid G] {ι : Type*}
    {s : Finset ι} (hs : s.Nonempty) (e : ι → ℕ)
    (h : (⋃ j ∈ s, Set.range fun y : G => e j • y) ≠ Set.univ) :
    ∃ x : G, 0 < x ∧ x ∉ ⋃ j ∈ s, Set.range fun y : G => e j • y := by
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem _).mp h
  have hneg : -x ∉ ⋃ j ∈ s, Set.range fun y : G => e j • y := by
    intro hmem
    obtain ⟨j, hj, y, hy⟩ := Set.mem_iUnion₂.mp hmem
    exact hx (Set.mem_iUnion₂.mpr ⟨j, hj, -y, by dsimp only at hy ⊢; rw [smul_neg, hy, neg_neg]⟩)
  have hx0 : x ≠ 0 := by
    rintro rfl
    obtain ⟨j, hj⟩ := hs
    exact hx (Set.mem_iUnion₂.mpr ⟨j, hj, 0, smul_zero _⟩)
  rcases hx0.lt_or_gt with hlt | hgt
  · exact ⟨-x, neg_pos.mpr hlt, hneg⟩
  · exact ⟨x, hgt, hx⟩

/-- `ihs:dz:lem:group`, combined: in a linearly ordered abelian group, if every `e_j G`
(`e_j > 0`, nonempty index set) is proper, a positive element lies in none of them. -/
theorem exists_pos_notMem_range_nsmul [LinearOrder G] [IsOrderedAddMonoid G] {ι : Type*}
    {s : Finset ι} (hs : s.Nonempty) (e : ι → ℕ) (he : ∀ j ∈ s, 0 < e j)
    (hns : ∀ j ∈ s, Set.range (fun y : G => e j • y) ≠ Set.univ) :
    ∃ x : G, 0 < x ∧ ∀ j ∈ s, x ∉ Set.range fun y : G => e j • y := by
  have h : (⋃ j ∈ s, Set.range fun y : G => e j • y) ≠ Set.univ := by
    rw [Ne, iUnion_range_nsmul_eq_univ_iff s e he]
    rintro ⟨j, hj, hr⟩
    exact hns j hj hr
  obtain ⟨x, hx, hxu⟩ := exists_pos_notMem_iUnion_range_nsmul hs e h
  exact ⟨x, hx, fun j hj hxj => hxu (Set.mem_iUnion₂.mpr ⟨j, hj, hxj⟩)⟩

end IntegerMultiples

section PowerImage

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field K]
  [IsAlgClosed K] [CharZero K]

/-- `ihs:dz:lem:powers`: in `K((t^Γ))` with `K` algebraically closed of characteristic zero
and `Γ` any linearly ordered abelian group, the `e`th powers of the elements of positive
valuation are exactly `0` and the nonzero `ζ` of positive valuation with `v(ζ) ∈ eΓ`. The
source's case `K = ℂ` is `exists_pow_eq_iff_complex`. -/
theorem exists_pow_eq_iff {e : ℕ} (he : 0 < e) (ζ : K⟦Γ⟧) :
    (∃ x : K⟦Γ⟧, 0 < x.orderTop ∧ x ^ e = ζ) ↔
      ζ = 0 ∨ (0 < ζ.orderTop ∧ ∃ γ : Γ, ζ.order = e • γ) := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    by_cases hx0 : x = 0
    · left
      rw [hx0, zero_pow he.ne']
    · right
      refine ⟨?_, x.order, order_pow x e⟩
      rw [← order_eq_orderTop_of_ne_zero hx0] at hx
      rw [← order_eq_orderTop_of_ne_zero (pow_ne_zero e hx0), order_pow]
      exact WithTop.coe_pos.mpr ((nsmul_pos_iff he.ne').mpr (WithTop.coe_pos.mp hx))
  · rintro (rfl | ⟨hpos, γ, hγ⟩)
    · exact ⟨0, by simp, zero_pow he.ne'⟩
    by_cases hζ : ζ = 0
    · exact ⟨0, by simp, by rw [hζ, zero_pow he.ne']⟩
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq ζ.leadingCoeff he
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [zero_pow he.ne'] at hr
      exact leadingCoeff_ne_zero.mpr hζ hr.symm
    have hk := Surreal.HahnSeries.orderTop_leadingNormalized_sub_one_pos ζ hζ
    set w := Surreal.HahnSeries.binomialPower _ hk (1 / (e : ℚ)) with hwdef
    have hw : w ^ e = Surreal.HahnSeries.leadingNormalized ζ := by
      rw [hwdef, Surreal.HahnSeries.binomialPower_rat_root _ hk e he.ne', add_sub_cancel]
    have hw0 : w.orderTop = 0 :=
      ((orderTop_self_sub_one_pos_iff w).mp
        (Surreal.HahnSeries.orderTop_binomialPower_sub_one_pos _ hk _)).1
    have hγpos : 0 < γ := by
      rw [← order_eq_orderTop_of_ne_zero hζ, hγ] at hpos
      exact (nsmul_pos_iff he.ne').mp (WithTop.coe_pos.mp hpos)
    refine ⟨single γ r * w, ?_, ?_⟩
    · rw [orderTop_mul, hw0, add_zero, orderTop_single hr0]
      exact WithTop.coe_pos.mpr hγpos
    · rw [mul_pow, single_pow, hr, hw, ← hγ,
        Surreal.HahnSeries.leadingMonomial_mul_leadingNormalized ζ hζ]

/-- `ihs:dz:lem:powers` over the source's scalars `ℂ`: in `ℂ((t^Γ))`, for `Γ` any linearly
ordered abelian group, the `e`th powers of the elements of positive valuation are exactly `0`
and the nonzero `ζ` of positive valuation with `v(ζ) ∈ eΓ`. -/
theorem exists_pow_eq_iff_complex {e : ℕ} (he : 0 < e) (ζ : ℂ⟦Γ⟧) :
    (∃ x : ℂ⟦Γ⟧, 0 < x.orderTop ∧ x ^ e = ζ) ↔
      ζ = 0 ∨ (0 < ζ.orderTop ∧ ∃ γ : Γ, ζ.order = e • γ) :=
  exists_pow_eq_iff he ζ

end PowerImage

section SequentialLimits

variable {Γ V : Type*} [LinearOrder Γ] [Zero V]

/-- The every-rank sequential form of the proof of `ihs:hh:prop:complete`: if for every cutoff
`R` all sufficiently late `x_n` agree at every exponent `≤ R`, there is a Hahn series `y` with
which the `x_n` eventually agree at every exponent `≤ R`, for each `R`. -/
theorem exists_limit_of_eventually_agree (x : ℕ → HahnSeries Γ V)
    (hx : ∀ R : Γ, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ∀ γ ≤ R, (x m).coeff γ = (x n).coeff γ) :
    ∃ y : HahnSeries Γ V, ∀ R : Γ, ∃ N, ∀ n ≥ N, ∀ γ ≤ R, (x n).coeff γ = y.coeff γ := by
  choose N hN using hx
  have hstab : ∀ R γ, γ ≤ R → (x (N γ)).coeff γ = (x (N R)).coeff γ := by
    intro R γ hγ
    rw [hN γ (N γ) le_rfl (max (N γ) (N R)) (le_max_left _ _) γ le_rfl,
      hN R (N R) le_rfl (max (N γ) (N R)) (le_max_right _ _) γ hγ]
  let y : HahnSeries Γ V :=
    { coeff := fun γ => (x (N γ)).coeff γ
      isPWO_support' := by
        rw [Set.IsPWO, Set.partiallyWellOrderedOn_iff_exists_lt]
        intro f hf
        by_cases hup : ∃ n, 0 < n ∧ f 0 ≤ f n
        · obtain ⟨n, hn, hle⟩ := hup
          exact ⟨0, n, hn, hle⟩
        · push Not at hup
          have hle : ∀ n, f n ≤ f 0 := fun n => by
            rcases n with _ | n
            · exact le_rfl
            · exact (hup (n + 1) n.succ_pos).le
          refine (x (N (f 0))).isPWO_support.exists_lt fun n => ?_
          have hfn := hf n
          rw [Function.mem_support, hstab (f 0) (f n) (hle n)] at hfn
          exact hfn }
  refine ⟨y, fun R => ⟨N R, fun n hn γ hγ => ?_⟩⟩
  change (x n).coeff γ = (x (N γ)).coeff γ
  rw [hstab R γ hγ, hN R n hn (N R) le_rfl γ hγ]

/-- The limit in `exists_limit_of_eventually_agree` is unique. -/
theorem eq_of_eventually_agree {x : ℕ → HahnSeries Γ V} {y z : HahnSeries Γ V}
    (hy : ∀ R : Γ, ∃ N, ∀ n ≥ N, ∀ γ ≤ R, (x n).coeff γ = y.coeff γ)
    (hz : ∀ R : Γ, ∃ N, ∀ n ≥ N, ∀ γ ≤ R, (x n).coeff γ = z.coeff γ) : y = z := by
  ext γ
  obtain ⟨N₁, hN₁⟩ := hy γ
  obtain ⟨N₂, hN₂⟩ := hz γ
  rw [← hN₁ (max N₁ N₂) (le_max_left _ _) γ le_rfl, hN₂ (max N₁ N₂) (le_max_right _ _) γ le_rfl]

end SequentialLimits

section RankOne

variable {Γ : AddSubgroup ℝ} {V : Type*}

/-- The rank-one size `ρ(x) = e^(-v(x))`, with `ρ(0) = 0`. -/
def valSize [Zero V] (x : HahnSeries Γ V) : ℝ :=
  open Classical in if x = 0 then 0 else Real.exp (-((x.order : Γ) : ℝ))

theorem valSize_zero [Zero V] : valSize (0 : HahnSeries Γ V) = 0 := by
  rw [valSize, if_pos rfl]

theorem valSize_of_ne [Zero V] {x : HahnSeries Γ V} (hx : x ≠ 0) :
    valSize x = Real.exp (-((x.order : Γ) : ℝ)) := by
  rw [valSize, if_neg hx]

theorem valSize_nonneg [Zero V] (x : HahnSeries Γ V) : 0 ≤ valSize x := by
  by_cases hx : x = 0
  · rw [hx, valSize_zero]
  · rw [valSize_of_ne hx]
    exact (Real.exp_pos _).le

theorem valSize_eq_zero [Zero V] {x : HahnSeries Γ V} : valSize x = 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ valSize_zero⟩
  by_contra hx
  rw [valSize_of_ne hx] at h
  exact (Real.exp_pos _).ne' h

theorem valSize_neg [AddGroup V] (x : HahnSeries Γ V) : valSize (-x) = valSize x := by
  by_cases hx : x = 0
  · rw [hx, neg_zero]
  · rw [valSize_of_ne hx, valSize_of_ne (neg_ne_zero.mpr hx), order_neg]

/-- The ultrametric inequality `ρ(x + y) ≤ max(ρ(x), ρ(y))`. -/
theorem valSize_add_le [AddGroup V] (x y : HahnSeries Γ V) :
    valSize (x + y) ≤ max (valSize x) (valSize y) := by
  by_cases hxy : x + y = 0
  · rw [hxy, valSize_zero]
    exact le_max_of_le_left (valSize_nonneg x)
  by_cases hx : x = 0
  · rw [hx, zero_add]
    exact le_max_right _ _
  by_cases hy : y = 0
  · rw [hy, add_zero]
    exact le_max_left _ _
  rw [valSize_of_ne hxy, valSize_of_ne hx, valSize_of_ne hy]
  have h := min_order_le_order_add hxy
  rcases le_total x.order y.order with hle | hle
  · rw [min_eq_left hle] at h
    exact le_max_of_le_left (Real.exp_le_exp.mpr (neg_le_neg (Subtype.coe_le_coe.mpr h)))
  · rw [min_eq_right hle] at h
    exact le_max_of_le_right (Real.exp_le_exp.mpr (neg_le_neg (Subtype.coe_le_coe.mpr h)))

/-- `ρ(x) < ε` exactly when `x` vanishes at every exponent `γ` with `ε ≤ e^(-γ)`. -/
theorem valSize_lt_iff [Zero V] (x : HahnSeries Γ V) {ε : ℝ} (hε : 0 < ε) :
    valSize x < ε ↔ ∀ γ : Γ, ε ≤ Real.exp (-(γ : ℝ)) → x.coeff γ = 0 := by
  by_cases hx : x = 0
  · simp only [hx, valSize_zero, hε, coeff_zero, implies_true]
  rw [valSize_of_ne hx]
  constructor
  · intro h γ hγ
    by_contra hc
    have hle : ((x.order : Γ) : ℝ) ≤ γ := Subtype.coe_le_coe.mpr (order_le_of_coeff_ne_zero hc)
    exact (lt_of_le_of_lt (hγ.trans (Real.exp_le_exp.mpr (neg_le_neg hle))) h).false
  · intro h
    by_contra hle
    exact coeff_order_eq_zero.not.mpr hx (h _ (not_lt.mp hle))

variable (Γ V) in
/-- `V((t^Γ))` for an additive subgroup `Γ ≤ ℝ`, with the rank-one valuation metric. -/
def RankOneHahn [Zero V] : Type _ :=
  HahnSeries Γ V

/-- The identification of `RankOneHahn Γ V` with the Hahn series. -/
def RankOneHahn.toHahn [Zero V] : RankOneHahn Γ V ≃ HahnSeries Γ V :=
  Equiv.refl _

/-- The metric `d(x, y) = ρ(x - y)` of `ihs:hh:sec:rankone`. -/
instance RankOneHahn.instMetricSpace [AddCommGroup V] : MetricSpace (RankOneHahn Γ V) where
  dist x y := valSize (RankOneHahn.toHahn x - RankOneHahn.toHahn y)
  dist_self x := by
    rw [sub_self, valSize_zero]
  dist_comm x y := by
    rw [← neg_sub, valSize_neg]
  dist_triangle x y z := by
    rw [← sub_add_sub_cancel _ (RankOneHahn.toHahn y)]
    exact (valSize_add_le _ _).trans
      (max_le_add_of_nonneg (valSize_nonneg _) (valSize_nonneg _))
  eq_of_dist_eq_zero {x y} h := by
    change valSize (RankOneHahn.toHahn x - RankOneHahn.toHahn y) = 0 at h
    exact RankOneHahn.toHahn.injective (sub_eq_zero.mp (valSize_eq_zero.mp h))

theorem RankOneHahn.dist_eq [AddCommGroup V] (x y : RankOneHahn Γ V) :
    dist x y = valSize (RankOneHahn.toHahn x - RankOneHahn.toHahn y) :=
  rfl

/-- `ihs:hh:sec:rankone`: the metric `d` is an ultrametric. -/
instance RankOneHahn.instIsUltrametricDist [AddCommGroup V] :
    IsUltrametricDist (RankOneHahn Γ V) where
  dist_triangle_max x y z := by
    rw [RankOneHahn.dist_eq, RankOneHahn.dist_eq, RankOneHahn.dist_eq,
      ← sub_add_sub_cancel _ (RankOneHahn.toHahn y)]
    exact valSize_add_le _ _

/-- `ihs:hh:prop:complete`: for an additive subgroup `Γ ≤ ℝ` and any additive commutative group
`V` (in particular any complex vector space or Hilbert space), `V((t^Γ))` is complete for the
metric `d(x, y) = e^(-v(x - y))`. -/
theorem completeSpace_rankOneHahn [AddCommGroup V] : CompleteSpace (RankOneHahn Γ V) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  rw [Metric.cauchySeq_iff] at hu
  set x : ℕ → HahnSeries Γ V := fun n => RankOneHahn.toHahn (u n)
  have hagree : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ∀ γ : Γ, ε ≤ Real.exp (-(γ : ℝ)) →
      (x m).coeff γ = (x n).coeff γ := by
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    refine ⟨N, fun m hm n hn γ hγ => ?_⟩
    have h := (valSize_lt_iff _ hε).mp (hN m hm n hn) γ hγ
    rwa [coeff_sub, sub_eq_zero] at h
  obtain ⟨y, hy⟩ := exists_limit_of_eventually_agree x fun R => by
    obtain ⟨N, hN⟩ := hagree _ (Real.exp_pos (-(R : ℝ)))
    exact ⟨N, fun m hm n hn γ hγ => hN m hm n hn γ
      (Real.exp_le_exp.mpr (neg_le_neg (Subtype.coe_le_coe.mpr hγ)))⟩
  refine ⟨RankOneHahn.toHahn.symm y, Metric.tendsto_atTop.mpr fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hagree ε hε
  refine ⟨N, fun n hn => ?_⟩
  rw [RankOneHahn.dist_eq, Equiv.apply_symm_apply, valSize_lt_iff _ hε]
  intro γ hγ
  obtain ⟨M, hM⟩ := hy γ
  rw [coeff_sub, sub_eq_zero, hN n hn (max N M) (le_max_left _ _) γ hγ,
    hM (max N M) (le_max_right _ _) γ le_rfl]

instance RankOneHahn.instCompleteSpace [AddCommGroup V] : CompleteSpace (RankOneHahn Γ V) :=
  completeSpace_rankOneHahn

end RankOne

end

end Surreal.HahnSpectralBasics
