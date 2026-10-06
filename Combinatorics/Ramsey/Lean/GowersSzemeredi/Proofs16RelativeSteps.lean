import GowersSzemeredi.Proofs16BoundedChunks

/-! # Relative steps inside a short parent progression

When the parent step is a unit, translate and divide a contained progression
by that step. The short-interval estimate then controls its relative step.
Transporting a signed residue partition back to the original final axis
recovers the child's actual common difference.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- In a prime modulus, a proper progression with at least two points
has an invertible step, as required for relative index coordinates. -/
theorem ModAP.step_isUnit_of_prime {N : Nat} [NeZero N] [Fact N.Prime]
    (P : ModAP N) (hP : P.IsProper) (hlen : 2 ≤ P.length) : IsUnit P.step := by
  apply isUnit_iff_ne_zero.mpr
  intro hs
  have h := P.centered_step_pos hP hlen
  simp [hs, centeredAbs] at h

/-- Pull a progression back through an invertible affine parametrization. -/
def modAPUnitPullback {N : Nat} (u : (ZMod N)ˣ) (a : ZMod N) (R : ModAP N) : ModAP N where
  start := (↑u⁻¹ : ZMod N) * (R.start - a)
  step := (↑u⁻¹ : ZMod N) * R.step
  length := R.length

theorem modAPUnitPullback_carrier {N : Nat} (u : (ZMod N)ˣ) (a : ZMod N) (R : ModAP N) :
    (modAPUnitPullback u a R).carrier =
      R.carrier.image (fun x => (↑u⁻¹ : ZMod N) * (x - a)) := by
  classical
  unfold ModAP.carrier
  rw [Finset.image_image]
  apply Finset.image_congr
  intro i _
  dsimp [modAPUnitPullback]
  ring

theorem modAPUnitPullback_isProper {N : Nat} (u : (ZMod N)ˣ) (a : ZMod N)
    (R : ModAP N) (hR : R.IsProper) : (modAPUnitPullback u a R).IsProper := by
  rw [ModAP.IsProper, modAPUnitPullback_carrier, Finset.card_image_of_injective]
  · exact hR
  · intro x y hxy
    have h := congrArg (fun z : ZMod N => (↑u : ZMod N) * z) hxy
    simpa [← mul_assoc] using h

/-- The inverse affine map carries every contained progression into the
ordinary index interval of its parent. -/
theorem modAPUnitPullback_subset {N : Nat} (u : (ZMod N)ˣ) (B R : ModAP N)
    (hstep : B.step = (↑u : ZMod N)) (hsub : R.carrier ⊆ B.carrier) :
    (modAPUnitPullback u B.start R).carrier ⊆ (modInterval N 0 B.length).carrier := by
  classical
  rw [modAPUnitPullback_carrier]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (hsub hy)
  refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩
  change (0 : ZMod N) + (i : ZMod N) * 1 =
    (↑u⁻¹ : ZMod N) * (B.start + (i : ZMod N) * B.step - B.start)
  rw [hstep]
  simp [mul_left_comm, mul_comm]

/-- A short parent with invertible step supplies a tiling of a longer
parallel axis at the contained progression's step. -/
theorem ModAP.partition_at_contained_step {N v : Nat} [NeZero N]
    (R B I : ModAP N) (u : (ZMod N)ˣ) (hR : R.IsProper) (hI : I.IsProper)
    (hBstep : B.step = (↑u : ZMod N)) (hIstep : I.step = B.step)
    (hsub : R.carrier ⊆ B.carrier) (hshort : 2 * B.length ≤ N)
    (hL : B.length ≤ I.length) (hv : 1 ≤ v) (hfit : v ^ 2 ≤ R.length - 1) :
    ∃ M : Nat, ∃ J : Fin M → ModAP N,
      IsPartition (fun j => (J j).carrier) I.carrier ∧
      (∀ j, (J j).IsProper ∧ 0 < (J j).length ∧
        ((J j).length = v - 1 ∨ (J j).length = v)) ∧
      ∀ j, (J j).step = R.step := by
  let T := modAPUnitPullback u B.start R
  obtain ⟨M, J, hpart, hprop, hstep⟩ :=
    T.partition_at_short_interval_step I (modAPUnitPullback_isProper u B.start R hR)
      hI hshort (modAPUnitPullback_subset u B R hBstep hsub) hL hv hfit
  refine ⟨M, J, hpart, hprop, ?_⟩
  intro j
  rw [hstep j, hIstep, hBstep]
  change ((↑u⁻¹ : ZMod N) * R.step) * (↑u : ZMod N) = R.step
  simp [mul_right_comm]

/-- Tile a product when a base axis lies in a short parent progression
parallel to the final axis. The parent step need only be a unit; the modulus
need not be prime. -/
theorem box_product_tiling_of_contained_axis {N k v : Nat} [NeZero N]
    (R : Box N k) (B I : ModAP N) (i : Fin k) (u : (ZMod N)ˣ)
    (hR : R.IsProper) (hI : I.IsProper)
    (hBstep : B.step = (↑u : ZMod N)) (hIstep : I.step = B.step)
    (hsub : (R.axis i).carrier ⊆ B.carrier) (hshort : 2 * B.length ≤ N)
    (hL : B.length ≤ I.length) (hv : 1 ≤ v) (hfit : v ^ 2 ≤ R.width - 1) :
    ∃ M : Nat, ∃ S : Fin M → Box N (k + 1), ∃ J : Fin M → ModAP N,
      IsPartition (fun j => (S j).carrier)
        (Finset.univ.filter (fun x : Point N (k + 1) =>
          section16Init x ∈ R.carrier ∧ section16Last x ∈ I.carrier)) ∧
      (∀ j, (S j).IsProper ∧ v - 1 ≤ (S j).width) ∧
      (∀ j, IsLastCoordinateBoxProduct (S j) R (J j)) ∧
      ∀ j, 0 < (J j).length ∧ ((J j).length = v - 1 ∨ (J j).length = v) := by
  have haxis := R.width_le_axis_length i
  obtain ⟨M, J, hpart, hprop, hstep⟩ :=
    (R.axis i).partition_at_contained_step B I u (hR i) hI hBstep hIstep hsub
      hshort hL hv (hfit.trans (Nat.sub_le_sub_right haxis 1))
  have hstep' (j : Fin M) : (J j).step = R.commonDiff := (hstep j).trans (R.axis_step i)
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
