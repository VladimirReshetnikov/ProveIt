import GowersSzemeredi.Proofs16ProductTiling

/-! Declarations of `Proofs16ProductTiling` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- Short containment of one base axis supplies a tiling at the base's
common difference. All final axes have length v-1 or v; all boxes are proper. -/
theorem box_product_tiling_of_short_axis {N k n v : Nat} [NeZero N]
    (R : Box N k) (I : ModAP N) (i : Fin k)
    (hR : R.IsProper) (hI : I.IsProper) (hIstep : I.step = 1)
    (hn : 2 * n ≤ N) (hsub : (R.axis i).carrier ⊆ (modInterval N 0 n).carrier)
    (hL : n ≤ I.length) (hv : 1 ≤ v) (hfit : v ^ 2 ≤ R.width - 1) :
    ∃ M : Nat, ∃ S : Fin M → Box N (k + 1), ∃ J : Fin M → ModAP N,
      IsPartition (fun j => (S j).carrier)
        (Finset.univ.filter (fun x : Point N (k + 1) =>
          section16Init x ∈ R.carrier ∧ section16Last x ∈ I.carrier)) ∧
      (∀ j, (S j).IsProper ∧ v - 1 ≤ (S j).width) ∧
      (∀ j, IsLastCoordinateBoxProduct (S j) R (J j)) ∧
      ∀ j, 0 < (J j).length ∧ ((J j).length = v - 1 ∨ (J j).length = v) := by
  have haxis := R.width_le_axis_length i
  obtain ⟨M, J, hpart, hprop, hstep⟩ :=
    (R.axis i).partition_at_short_interval_step I (hR i) hI hn hsub hL hv
      (hfit.trans (Nat.sub_le_sub_right haxis 1))
  have hstep' (j : Fin M) : (J j).step = R.commonDiff := by
    rw [hstep j, hIstep, mul_one, R.axis_step]
  refine ⟨M, fun j => boxAppend R (J j) (hstep' j), J,
    boxAppend_partition R I J hstep' hpart, ?_, ?_, ?_⟩
  · intro j
    refine ⟨boxAppend_isProper R (J j) (hstep' j) hR (hprop j).1,
      boxAppend_width_ge R (J j) (hstep' j) ?_ ?_⟩
    · have hv2 : v ≤ v ^ 2 := by nlinarith
      omega
    · rcases (hprop j).2.2 with h | h <;> omega
  · intro j
    exact boxAppend_product R (J j) (hstep' j)
  · intro j
    exact (hprop j).2

end LeanProofs.GowersSzemeredi
