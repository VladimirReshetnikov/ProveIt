import GowersSzemeredi.Proofs16LiftWidth

/-! # The verified local affine lift at every input scale -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem section16_slice_control_ranges {r k : Nat} {s gamma ε : ℝ}
    (hr : 0 < r) (hs : 1 ≤ s) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 < (multipleC (((r : ℝ) * s)⁻¹ * ε) gamma k) ^ ((r : ℝ) * s) ∧
    (multipleC (((r : ℝ) * s)⁻¹ * ε) gamma k) ^ ((r : ℝ) * s) ≤ 1 ∧
    1 ≤ (multipleQ (((r : ℝ) * s)⁻¹ * ε) gamma k) ^ ((r : ℝ) * s) := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have ht : 1 ≤ (r : ℝ) * s := one_le_mul_of_one_le_of_one_le hr1 hs
  have ht0 : 0 < (r : ℝ) * s := zero_lt_one.trans_le ht
  have hi : ((r : ℝ) * s)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht
  have hb : 0 < gamma * (((r : ℝ) * s)⁻¹ * ε) := by positivity
  have hb1 : gamma * (((r : ℝ) * s)⁻¹ * ε) ≤ 1 := by
    calc
      _ ≤ 1 * (1 * 1) := mul_le_mul hg1 (mul_le_mul hi hε1 hε.le (by norm_num))
        (by positivity) (by norm_num)
      _ = 1 := by norm_num
  have hc : 0 < multipleC (((r : ℝ) * s)⁻¹ * ε) gamma k := pow_pos hb _
  have hc1 : multipleC (((r : ℝ) * s)⁻¹ * ε) gamma k ≤ 1 := pow_le_one₀ hb.le hb1
  have hQ : 1 ≤ multipleQ (((r : ℝ) * s)⁻¹ * ε) gamma k := by
    exact (one_le_inv₀ hc).mpr hc1
  exact ⟨Real.rpow_pos_of_pos hc _, Real.rpow_le_one hc.le hc1 ht0.le,
    Real.one_le_rpow hQ ht0.le⟩

theorem isMultilinear_constant {N d : Nat} (c : ZMod N) :
    IsMultilinear (fun _ : Point N d => c) := by
  classical
  let e0 : Fin d → Bool := fun _ => false
  refine ⟨fun e => if e = e0 then c else 0, ?_⟩
  intro x
  rw [Finset.sum_eq_single e0]
  · simp [e0]
  · intro e _ hne
    simp [hne]
  · simp

/-- The local cover now holds for every natural input scale m. The small
target branch uses genuine singleton boxes and one graph per cell. -/
theorem section16_local_affine_lift_all_scales {N k q r m : Nat} [Fact N.Prime]
    (P : Box N (k + 1)) (hP : P.IsProper) (hk : 0 < k) (hmP : m ≤ P.width)
    (B D : Finset (Point N (k + 1))) (hD : D ⊆ B)
    (phi : Point N (k + 1) → ZMod N) (gamma s : ℝ)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hsections : FinalCoordinateSectionsMultiplyLinear gamma s B phi) (hs : 1 ≤ s)
    (ell : Point N k → Fin q → ZMod N → ZMod N)
    (hell : ∀ h i, LinearOn Finset.univ (ell h i))
    (hcover : ∀ h x, appendCoordinate h x ∈ P.carrier → appendCoordinate h x ∈ D →
      ∃ i, phi (appendCoordinate h x) = ell h i x)
    (τ ε : ℝ) (hq : 0 < q) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hr : 6 * (q : ℝ) ≤ (r : ℝ) * τ ^ 2) :
    ∃ (p : Nat) (G : Finset (Point N (k + 1))) (L : Nat) (S : Fin L → Box N (k + 1))
      (nu : Fin L → ((Fin r × Fin p) ⊕ (Fin r × Fin r × Fin p × Fin p)) →
        Point N (k + 1) → ZMod N),
      (p : ℝ) ≤ (multipleQ (((r : ℝ) * s)⁻¹ * ε) gamma k) ^ ((r : ℝ) * s) ∧
      G ⊆ P.carrier ∧ (1 - 2 * τ - ε) * (P.carrier.card : ℝ) ≤ G.card ∧
      IsBoxPartition S P ∧
      (∀ j, (S j).IsProper ∧ Real.sqrt (((m : ℝ) / 8) ^
        ((multipleC (((r : ℝ) * s)⁻¹ * ε) gamma k) ^ ((r : ℝ) * s))) / 4 ≤ (S j).width) ∧
      (∀ j ij, IsMultilinear (nu j ij)) ∧
      ∀ j z, z ∈ (S j).carrier → z ∈ D → z ∈ G → ∃ ij, phi z = nu j ij z := by
  classical
  have hrpos : 0 < r := by
    by_contra hz
    have hz' : r = 0 := by omega
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    simp only [hz', Nat.cast_zero, zero_mul] at hr
    linarith
  obtain ⟨ha, _, hQ⟩ := section16_slice_control_ranges (k := k) hrpos hs hg hg1 hε hε1
  let a := (multipleC (((r : ℝ) * s)⁻¹ * ε) gamma k) ^ ((r : ℝ) * s)
  let w := ((m : ℝ) / 8) ^ a
  by_cases hw : 16 ≤ w
  · have hm : 4 ≤ m := by
      by_contra hm
      have hm' : (m : ℝ) ≤ 3 := by exact_mod_cast (by omega : m ≤ 3)
      have hbase : (m : ℝ) / 8 ≤ 1 := by linarith
      have hw1 : w ≤ 1 := Real.rpow_le_one (by positivity) hbase ha.le
      linarith
    exact section16_local_affine_lift_sqrt P hP hk hm hmP B D hD phi gamma s
      hsections hs ell hell hcover τ ε hq hτ hτ1 hε hε1 hr hw
  · have hw0 : 0 ≤ w := Real.rpow_nonneg (by positivity) _
    have hwidth : Real.sqrt w / 4 ≤ 1 := by
      have hsquare := Real.sq_sqrt hw0
      have hs0 := Real.sqrt_nonneg w
      nlinarith [not_le.mp hw]
    obtain ⟨L, x, hpart⟩ := box_singleton_partition P
    refine ⟨1, P.carrier, L, fun j => pointSingletonBox (x j),
      fun j _ _ => phi (x j), by simpa using hQ, Finset.Subset.rfl, ?_, hpart, ?_,
      fun j _ => isMultilinear_constant _, ?_⟩
    · have hn : (0 : ℝ) ≤ P.carrier.card := Nat.cast_nonneg _
      nlinarith
    · intro j
      refine ⟨pointSingletonBox_isProper _, ?_⟩
      simpa only [pointSingletonBox_width (by omega : 0 < k + 1), Nat.cast_one] using hwidth
    · intro j z hz _ _
      have hz' : z = x j := by simpa only [pointSingletonBox_carrier, Finset.mem_singleton] using hz
      exact ⟨Sum.inl (⟨0, hrpos⟩, 0), congrArg phi hz'⟩

end LeanProofs.GowersSzemeredi
