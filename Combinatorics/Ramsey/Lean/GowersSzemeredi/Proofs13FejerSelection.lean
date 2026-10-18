import GowersSzemeredi.Proofs12BernoulliSelection
import GowersSzemeredi.Proofs13FejerDiagonal
import GowersSzemeredi.Proofs13FejerSignal

/-! Turn averaged survival bounds into an actual purified subset.
Exceptional edges may survive with probability one; their cardinality is
charged explicitly against the score. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem exists_subset_seed_survival_bounds {X E C : Type*} [DecidableEq X]
    [DecidableEq E] [Fintype C] [Nonempty C]
    (U : Finset X) (p : C → X → Real)
    (hp0 : ∀ c x, x ∈ U → 0 ≤ p c x) (hp1 : ∀ c x, x ∈ U → p c x ≤ 1)
    (good bad exceptional : Finset E) (carrier : E → Finset X)
    (hgood : ∀ e ∈ good, carrier e ⊆ U) (hbad : ∀ e ∈ bad, carrier e ⊆ U)
    (signal baseline eta mass : Real) (heta : 0 < eta) (hmass : 0 < mass)
    (hgoodmean : ∀ e ∈ good, signal ≤ 𝔼 c : C, ∏ x ∈ carrier e, p c x)
    (hbadmean : ∀ e ∈ bad, (𝔼 c : C, ∏ x ∈ carrier e, p c x) ≤
      baseline + if e ∈ exceptional then 1 else 0)
    (hbudget : eta * mass ≤ eta * (good.card : Real) * signal -
      (bad.card : Real) * baseline - exceptional.card) :
    ∃ S ⊆ U, mass ≤ ((good.filter fun e => carrier e ⊆ S).card : Real) ∧
      ((bad.filter fun e => carrier e ⊆ S).card : Real) ≤
        eta * ((good.filter fun e => carrier e ⊆ S).card : Real) := by
  apply exists_subset_seed_purification U p hp0 hp1 good bad carrier hgood hbad eta mass heta hmass
  rw [Finset.expect_sub_distrib, ← Finset.mul_expect,
    Finset.expect_sum_comm, Finset.expect_sum_comm]
  -- sum the mean bounds; the exceptional edges cost at most `|exceptional|`
  have hg := Finset.sum_le_sum hgoodmean
  have hb := Finset.sum_le_sum hbadmean
  rw [Finset.sum_const, nsmul_eq_mul] at hg
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_boole] at hb
  have he : ((bad.filter (· ∈ exceptional)).card : Real) ≤ exceptional.card := by
    exact_mod_cast Finset.card_le_card fun e he => (Finset.mem_filter.mp he).2
  linarith only [hbudget, mul_le_mul_of_nonneg_left hg heta.le, hb, he]

theorem exists_subset_fejer_purification {N L M : Nat} [NeZero N]
    {I X E : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    [DecidableEq X] [DecidableEq E]
    (hL : 0 < L) (hML : 2 * M ≤ L)
    (U : Finset X) (good bad exceptional : Finset E) (vertex : E → I → X)
    (phi feature : X → ZMod N) (positive : E → I → Bool)
    (hgood : ∀ e ∈ good, Finset.univ.image (vertex e) ⊆ U)
    (hbad : ∀ e ∈ bad, Finset.univ.image (vertex e) ⊆ U)
    (hphi : ∀ e ∈ good, ∑ i, (if positive e i then 1 else -1) * phi (vertex e i) = 0)
    (hfeature : ∀ e ∈ good, ∑ i, (if positive e i then 1 else -1) * feature (vertex e i) = 0)
    (hinj : ∀ e ∈ bad, e ∉ exceptional → Function.Injective (vertex e))
    (hdiagonal : ∀ e ∈ bad, e ∉ exceptional → ∀ v : I → Fin L × Fin L,
      (fejerPairRelation v (phi ∘ vertex e) = 0 ∧ fejerPairRelation v (feature ∘ vertex e) = 0) ↔
        ∀ i, (v i).1 = (v i).2)
    (eta mass : Real) (heta : 0 < eta) (hmass : 0 < mass)
    (hbudget : eta * mass ≤
      eta * (good.card : Real) * ((((L : Real) ^ 2)⁻¹) ^ Fintype.card I * (M : Real) ^ (Fintype.card I + 1)) -
      (bad.card : Real) * ((L : Real)⁻¹) ^ Fintype.card I - exceptional.card) :
    ∃ S ⊆ U, mass ≤ ((good.filter fun e => Finset.univ.image (vertex e) ⊆ S).card : Real) ∧
      ((bad.filter fun e => Finset.univ.image (vertex e) ⊆ S).card : Real) ≤
        eta * ((good.filter fun e => Finset.univ.image (vertex e) ⊆ S).card : Real) := by
  apply exists_subset_seed_survival_bounds U
    (fun c : ZMod N × ZMod N => fun x => finiteFejerKernel L (c.1 * phi x + c.2 * feature x))
    (fun _ _ _ => finiteFejerKernel_nonneg _) (fun _ _ _ => finiteFejerKernel_le_one hL _)
    good bad exceptional (fun e => Finset.univ.image (vertex e)) hgood hbad _ _ eta mass heta hmass
    (fun e he => fejer_kernel_mean_signal_lower hL hML (positive e) (vertex e) phi feature
      (hphi e he) (hfeature e he)) ?_ hbudget
  intro e he
  split_ifs with hex
  · -- an exceptional edge survives with probability at most one
    exact le_add_of_nonneg_of_le (by positivity) (Finset.expect_le Finset.univ_nonempty
      fun c _ => Finset.prod_le_one (fun _ _ => finiteFejerKernel_nonneg _)
        fun _ _ => finiteFejerKernel_le_one hL _)
  · rw [add_zero]
    simp_rw [Finset.prod_image (hinj e he hex).injOn]
    exact (fejer_kernel_mean_diagonal hL (phi ∘ vertex e) (feature ∘ vertex e)
      (hdiagonal e he hex)).le

end LeanProofs.GowersSzemeredi
