import GowersSzemeredi.Proofs16LiftAllScales
import GowersSzemeredi.Proofs16BaseCaseZero

/-! Global multilinear graphs satisfy every admissible positive cover
parameter. In particular, an arbitrary function of the final coordinate
has constant, and hence multiply-linear, final-coordinate sections. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem IsMultilinear.multiplyLinearFunction {N k : Nat} [NeZero N]
    {phi : Point N k → ZMod N} (hphi : IsMultilinear phi)
    (B : Finset (Point N k)) {gamma r : Real}
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hr : 1 ≤ r) :
    MultiplyLinearFunction gamma r B phi := by
  classical
  intro theta ht ht1 P hP
  obtain ⟨ha, ha1, hq⟩ := section16_slice_control_ranges (r := 1) (k := k)
    (by omega) hr hg hg1 ht ht1
  simp only [Nat.cast_one, one_mul] at ha ha1 hq
  refine ⟨1, 1, P.carrier, fun _ => P, fun _ _ => phi,
    Finset.Subset.rfl, ?_, ?_, fun _ => hP, ?_, ?_, fun _ _ => hphi, ?_⟩
  · have hnonneg : (0 : Real) ≤ P.carrier.card := by positivity
    nlinarith
  · constructor
    · intro x
      simp
    · intro i j hij
      exact ((bne_iff_ne.mp hij) (Subsingleton.elim i j)).elim
  · simpa only [Nat.cast_one] using hq
  · intro j
    by_cases hw : P.width = 0
    · simp only [hw, Nat.cast_zero, Real.zero_rpow ha.ne', le_refl]
    · have hw1 : (1 : Real) ≤ P.width := by exact_mod_cast (show 1 ≤ P.width by omega)
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hw1 ha1
  · intro j x hxQ hxH y hxy
    obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hxy
    have hxy' : z = x := congrArg Prod.fst hzx
    subst z
    exact ⟨0, (congrArg Prod.snd hzx).symm⟩

theorem finalCoordinateSections_of_last_function {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (f : ZMod N → ZMod N)
    {gamma r : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hr : 1 ≤ r) :
    FinalCoordinateSectionsMultiplyLinear gamma r B (fun z => f (section16Last z)) := by
  intro x
  change MultiplyLinearFunction gamma r (section16FinalCoordinateSection B x)
    (fun h => f (section16Last (appendCoordinate h x)))
  have hc := (isMultilinear_constant (N := N) (d := k) (f x)).multiplyLinearFunction
    (section16FinalCoordinateSection B x) hg hg1 hr
  simpa only [section16FinalCoordinateRestriction, section16Last, appendCoordinate_eq_snoc, Fin.snoc_last] using hc

end LeanProofs.GowersSzemeredi
