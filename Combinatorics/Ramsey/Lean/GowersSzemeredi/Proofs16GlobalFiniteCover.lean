import GowersSzemeredi.Proofs16GlobalGraphCover

/-! A bounded family of global multilinear candidates satisfies the actual
all-box definition, including its graph and width budgets. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem multiplyLinear_of_global_candidates {N k q : Nat} [NeZero N]
    (Gamma : Finset (Point N k × ZMod N)) (mu : Fin q → Point N k → ZMod N)
    (hmu : ∀ i, IsMultilinear (mu i))
    (hcover : ∀ x y, (x, y) ∈ Gamma → ∃ i, y = mu i x)
    {gamma r : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hr : 1 ≤ r) (hq : (q : Real) ≤ r) : MultiplyLinear gamma r Gamma := by
  classical
  intro theta ht ht1 P hP
  obtain ⟨ha, ha1, _⟩ := section16_slice_control_ranges (r := 1) (k := k)
    (by omega) hr hg hg1 ht ht1
  simp only [Nat.cast_one, one_mul] at ha ha1
  refine ⟨1, q, P.carrier, fun _ => P, fun _ => mu, Finset.Subset.rfl,
    ?_, ?_, fun _ => hP,
    hq.trans (multipleQ_rpow_ge_parameter k hg hg1 ht ht1 hr), ?_,
    fun _ i => hmu i, ?_⟩
  · have hn : (0 : Real) ≤ P.carrier.card := by positivity
    nlinarith
  · constructor
    · intro x
      simp
    · intro i j hij
      exact ((bne_iff_ne.mp hij) (Subsingleton.elim i j)).elim
  · intro j
    by_cases hw : P.width = 0
    · simp only [hw, Nat.cast_zero, Real.zero_rpow ha.ne', le_refl]
    · have hw1 : (1 : Real) ≤ P.width := by exact_mod_cast (show 1 ≤ P.width by omega)
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hw1 ha1
  · intro j x hxQ hxH y hxy
    exact hcover x y hxy

theorem multiplyLinear_of_global_values {N k : Nat} [NeZero N]
    (Gamma : Finset (Point N k × ZMod N)) (S : Finset (ZMod N))
    (hvalues : ∀ z ∈ Gamma, z.2 ∈ S)
    {gamma r : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hr : 1 ≤ r) (hS : (S.card : Real) ≤ r) : MultiplyLinear gamma r Gamma := by
  classical
  let e : Fin S.card ≃ {y // y ∈ S} := S.equivFin.symm
  apply multiplyLinear_of_global_candidates Gamma (fun i _ => (e i).val)
    (fun i => isMultilinear_constant _) ?_ hg hg1 hr hS
  intro x y hxy
  refine ⟨e.symm ⟨y, hvalues (x, y) hxy⟩, ?_⟩
  simp

theorem multiplyLinearFunction_of_global_values {N k : Nat} [NeZero N]
    (B : Finset (Point N k)) (phi : Point N k → ZMod N) (S : Finset (ZMod N))
    (hvalues : ∀ x ∈ B, phi x ∈ S)
    {gamma r : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hr : 1 ≤ r) (hS : (S.card : Real) ≤ r) : MultiplyLinearFunction gamma r B phi := by
  classical
  apply multiplyLinear_of_global_values (partialGraph B phi) S ?_ hg hg1 hr hS
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
  exact hvalues x hx

/-- Restriction to every proper coordinate face preserves the same global
value budget. No affine regularity of the original function is assumed. -/
theorem properCrossSections_of_global_values {N k : Nat} [NeZero N]
    (B : Finset (Point N k)) (phi : Point N k → ZMod N) (S : Finset (ZMod N))
    (hvalues : ∀ x ∈ B, phi x ∈ S)
    {gamma r : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hr : 1 ≤ r) (hS : (S.card : Real) ≤ r) :
    ProperCrossSectionsMultiplyLinear gamma r B phi := by
  classical
  intro l hl F
  apply multiplyLinearFunction_of_global_values (F.domain B) (F.pullback phi) S ?_
    hg hg1 hr hS
  intro x hx
  exact hvalues _ (Finset.mem_filter.mp hx).2

end LeanProofs.GowersSzemeredi
