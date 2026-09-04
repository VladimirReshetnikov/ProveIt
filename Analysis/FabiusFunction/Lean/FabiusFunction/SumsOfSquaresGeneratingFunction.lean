import FabiusFunction.GeometricSimplexSum
import FabiusFunction.PartitionGeneratingFunction

/-!
# The sums-of-squares generating function

Let `r_d(n)` be the number of ordered `d`-tuples of integers with `x_1² + ⋯ + x_d² = n`
(`sumSqRep`, the cardinality of the finite set `sumSqFiber d n`).  For `‖q‖ < 1`,

  `(∑_{m ∈ ℤ} q^{m²})^d = ∑_{n ≥ 0} r_d(n) q^n`  (`hasSum_sumSqRep`, qg:prop-squares-theta):

the `d`-fold product of the theta series is the sum over `(Fin d → ℤ)` of `q^{∑ x_k²}`
(`hasSum_prod_fin_pi` transported along `ℕ ≃ ℤ`), which regroups by the value of `∑ x_k²`
(`hasSum_regroup`); each fibre is finite because `x_k² ≤ n`.
-/

set_option autoImplicit false

open Filter Topology Finset

namespace Fabius

/-- The ordered representations of `n` as a sum of `d` squares, as a finite set of tuples. -/
noncomputable def sumSqFiber (d n : ℕ) : Finset (Fin d → ℤ) :=
  (Fintype.piFinset fun _ : Fin d => Finset.Icc (-(n : ℤ)) n).filter
    fun x => ∑ k, (x k).natAbs ^ 2 = n

/-- `r_d(n)`, the number of ordered representations of `n` as a sum of `d` squares. -/
noncomputable def sumSqRep (d n : ℕ) : ℕ := (sumSqFiber d n).card

/-- Membership in `sumSqFiber d n` is equivalent to having squared-coordinate sum `n`. -/
theorem mem_sumSqFiber {d n : ℕ} {x : Fin d → ℤ} :
    x ∈ sumSqFiber d n ↔ ∑ k, (x k).natAbs ^ 2 = n := by
  unfold sumSqFiber
  rw [mem_filter, Fintype.mem_piFinset]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun k => ?_, h⟩
    have h1 : (x k).natAbs ^ 2 ≤ ∑ j, (x j).natAbs ^ 2 :=
      single_le_sum (f := fun j => (x j).natAbs ^ 2) (fun _ _ => Nat.zero_le _) (mem_univ k)
    rw [h] at h1
    have h2 : (x k).natAbs ≤ n := (Nat.le_self_pow two_ne_zero _).trans h1
    have h3 : |x k| ≤ (n : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast h2
    rw [mem_Icc]
    exact abs_le.mp h3

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

omit [CompleteSpace 𝕜] in
/-- The theta series `∑_{m ∈ ℤ} q^{m²}` converges absolutely for `‖q‖ < 1`. -/
theorem summable_norm_pow_natAbs_sq {q : 𝕜} (hq : ‖q‖ < 1) :
    Summable fun m : ℤ => ‖q ^ (m.natAbs ^ 2)‖ := by
  have hgeom := summable_geometric_of_lt_one (norm_nonneg q) hq
  have hb : ∀ m : ℕ, ‖q ^ (m ^ 2)‖ ≤ ‖q‖ ^ m := fun m => by
    rw [norm_pow]
    exact pow_le_pow_of_le_one (norm_nonneg q) hq.le (Nat.le_self_pow two_ne_zero _)
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hgeom
    rw [Int.natAbs_natCast]
    exact hb n
  · refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      ((summable_nat_add_iff 1).mpr hgeom)
    have h3 : (-((n : ℤ) + 1)).natAbs = n + 1 := by
      rw [Int.natAbs_neg, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; rfl,
        Int.natAbs_natCast]
    rw [h3]
    exact hb (n + 1)

set_option maxHeartbeats 1000000 in
/-- **The sums-of-squares generating function** (qg:prop-squares-theta):
`(∑_{m ∈ ℤ} q^{m²})^d = ∑_n r_d(n) q^n` for `‖q‖ < 1`. -/
theorem hasSum_sumSqRep {q : 𝕜} (hq : ‖q‖ < 1) (d : ℕ) :
    HasSum (fun n : ℕ => (sumSqRep d n : 𝕜) * q ^ n)
      ((∑' m : ℤ, q ^ (m.natAbs ^ 2)) ^ d) := by
  have hθ := summable_norm_pow_natAbs_sq hq
  -- an enumeration of `ℤ` by `ℕ`
  let e : ℕ ≃ ℤ := (Denumerable.eqv ℤ).symm
  let g : Fin d → ℕ → 𝕜 := fun _ n => q ^ ((e n).natAbs ^ 2)
  have hg : ∀ k, Summable fun n => ‖g k n‖ := fun k =>
    e.summable_iff.mpr hθ
  have hP := (hasSum_prod_fin_pi d g hg).1
  have hval : ∏ k : Fin d, ∑' n, g k n = (∑' m : ℤ, q ^ (m.natAbs ^ 2)) ^ d := by
    have hk : ∀ k : Fin d, ∑' n, g k n = ∑' m : ℤ, q ^ (m.natAbs ^ 2) := fun k =>
      e.tsum_eq fun m => q ^ (m.natAbs ^ 2)
    rw [prod_congr rfl fun k _ => hk k, prod_const, card_univ, Fintype.card_fin]
  rw [hval] at hP
  -- transport to tuples of integers
  let E : (Fin d → ℕ) ≃ (Fin d → ℤ) := Equiv.piCongrRight fun _ => e
  have hF : HasSum (fun x : Fin d → ℤ => q ^ (∑ k, (x k).natAbs ^ 2))
      ((∑' m : ℤ, q ^ (m.natAbs ^ 2)) ^ d) := by
    refine E.hasSum_iff.mp (hP.congr_fun fun i => ?_)
    show q ^ (∑ k, (E i k).natAbs ^ 2) = ∏ k, q ^ ((e (i k)).natAbs ^ 2)
    rw [prod_pow_eq_pow_sum]
    rfl
  -- regroup by the value of the sum of squares
  have hR := hasSum_regroup hF (fun x => ∑ k, (x k).natAbs ^ 2) (sumSqFiber d)
    (fun n x => mem_sumSqFiber)
  refine hR.congr_fun fun n => ?_
  rw [sum_congr rfl (fun x hx => by rw [mem_sumSqFiber.mp hx]), sum_const, nsmul_eq_mul]
  rfl

end Fabius
