import GowersSzemeredi.Proofs16WithLift

/-! A concrete two-dimensional slice provider from Freiman families.

If each final-coordinate section is covered by `q` order-eight Freiman
graphs, all `r` sampled sections can be linearized simultaneously with the
polynomial base case. Padding the sample count to `max 1 r` handles the
empty sample without a separate cover convention. The graph count is
`3 * (max 1 r * q)` and is independent of the requested loss.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-- The polynomial base exponent satisfies the range required by the lift. -/
theorem polyBaseExponent_le_one {q : Nat} {sigma : Real} (hq : 0 < q)
    (hs : 0 < sigma) (hs1 : sigma ≤ 1) : polyBaseExponent q sigma ≤ 1 := by
  have hη0 := polyBase_loss_pos hq hs
  have hη1 := polyBase_loss_le_one hq hs1 hs
  have hq1 : (1 : Real) ≤ q := by exact_mod_cast hq
  have hinv : (q : Real)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq1
  have hpow : (sigma / q) ^ 2 ≤ (1 : Real) := by nlinarith
  have ha : polyBaseCorExponent q sigma ≤ 1 := by
    unfold polyBaseCorExponent
    calc
      (2 : Real) ^ (-(14 : Real)) * (sigma / q) ^ 2 * (q : Real)⁻¹
          ≤ 1 * 1 * 1 := by
            gcongr
            norm_num
      _ = 1 := by norm_num
  exact (polyBaseExponent_le_half hq hs hs1).trans (by linarith)

/-- Cover all sampled slices by one family rather than refining one slice
at a time. The assumptions are concrete covers of individual sections. -/
theorem section16_slice_provider_of_freiman_families {N q : Nat} [Fact N.Prime]
    (hq : 0 < q) (B : Finset (Point N 2)) (phi : Point N 2 → ZMod N)
    (D : ZMod N → Fin q → Finset (Point N 1))
    (f : ZMod N → Fin q → Point N 1 → ZMod N)
    (hfreiman : ∀ t i, FreimanHom 8 (pointOneDomain (D t i)) (pointOneMap (f t i)))
    (hcover : ∀ t, partialGraph (section16FinalCoordinateSection B t)
      (section16FinalCoordinateRestriction phi t) ⊆
        section16FinsetUnion (fun i => partialGraph (D t i) (f t i))) :
    Section16SliceProvider B phi
      (fun r _ => ((3 * (max 1 r * q) : Nat) : Real))
      (fun r => polyBaseExponent (max 1 r * q)) := by
  classical
  intro r sample
  let sample' : Fin (max 1 r) → ZMod N := fun i =>
    if h : i.val < r then sample ⟨i.val, h⟩ else 0
  let e : Fin (max 1 r) × Fin q ≃ Fin (max 1 r * q) := finProdFinEquiv
  let D' := fun i : Fin (max 1 r * q) => D (sample' (e.symm i).1) (e.symm i).2
  let f' := fun i : Fin (max 1 r * q) => f (sample' (e.symm i).1) (e.symm i).2
  have hpos : 0 < max 1 r * q := Nat.mul_pos (by omega) hq
  apply section16_freiman_family_poly_cover hpos D' f'
    (fun i => hfreiman _ _) (section16StackedSlices B phi sample)
  intro z hz
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hz
  obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp (hcover (sample i) hi)
  let i' : Fin (max 1 r) := ⟨i.val, lt_of_lt_of_le i.isLt (le_max_right _ _)⟩
  have hs : sample' i' = sample i := by simp [sample', i', i.isLt]
  apply Finset.mem_biUnion.mpr
  refine ⟨e (i', j), Finset.mem_univ _, ?_⟩
  simpa only [D', f', Equiv.symm_apply_apply, hs] using hj

/-- The concrete family controls satisfy every numerical range used by the
parametric affine lift, including for an empty sampled family. -/
theorem section16_freiman_slice_provider_ranges {q : Nat} (hq : 0 < q) :
    Section16SliceProviderRanges
      (fun r _ => ((3 * (max 1 r * q) : Nat) : Real))
      (fun r => polyBaseExponent (max 1 r * q)) := by
  intro r sigma _hr hs hs1
  have hp : 0 < max 1 r * q := Nat.mul_pos (by omega) hq
  refine ⟨?_, polyBaseExponent_pos hp hs hs1, polyBaseExponent_le_one hp hs hs1⟩
  change (1 : Real) ≤ ((3 * (max 1 r * q) : Nat) : Real)
  exact_mod_cast (show 1 ≤ 3 * (max 1 r * q) by omega)

/-- Two-dimensional affine lifting with the concrete Freiman-family provider.
Only the line-cover and individual-section Freiman-cover inputs remain. -/
theorem section16_two_dimensional_cover_of_freiman_families
    {N q : Nat} [Fact N.Prime] (hq : 0 < q)
    {B : Finset (Point N 2)} {phi : Point N 2 → ZMod N}
    {theta gamma : Real} {Qd Ed : Real → Real}
    (hline : Section16AllBoxLineCoversWith theta gamma Qd Ed B phi)
    (D : ZMod N → Fin q → Finset (Point N 1))
    (f : ZMod N → Fin q → Point N 1 → ZMod N)
    (hfreiman : ∀ t i, FreimanHom 8 (pointOneDomain (D t i)) (pointOneMap (f t i)))
    (hcover : ∀ t, partialGraph (section16FinalCoordinateSection B t)
      (section16FinalCoordinateRestriction phi t) ⊆
        section16FinsetUnion (fun i => partialGraph (D t i) (f t i)))
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hEd : ∀ s, 0 < s → s ≤ 1 → 0 ≤ Ed s)
    {rho : Real} (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (m : Nat) (P : Box N 2) (hP : P.IsProper) (hm : m ≤ P.width) :
    let sigma := rho / 4
    ∃ qGamma qDelta : Nat,
      (qGamma : Real) ≤ section16Lemma9QBound sigma theta gamma 1 ∧
      (qDelta : Real) ≤ Qd (sigma / 2) ∧
      let l := lemma9WidthWith m qDelta 1 sigma theta gamma (Ed (sigma / 2))
        (section16Zeta theta gamma 1)
      let r := ⌈6 * (max 1 qGamma : Real) / sigma⌉₊
      let p : Real := ((3 * (max 1 r * q) : Nat) : Real)
      ∃ (n : Nat) (H : Finset (Point N 2)) (L : Nat)
        (Q : Fin L → Box N 2) (mu : Fin L → Fin n → Point N 2 → ZMod N),
        (n : Real) ≤ max p ((r.choose 2 : Real) * p * p) ∧
        H ⊆ P.carrier ∧ (1 - rho) * (P.carrier.card : Real) ≤ H.card ∧
        IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
        (∀ j, Real.sqrt (((Nat.floor l : Real) / 8) ^
          (polyBaseExponent (max 1 r * q) sigma)) / 4 ≤ (Q j).width) ∧
        (∀ j i, IsMultilinear (mu j i)) ∧
        ∀ j z, z ∈ (Q j).carrier → z ∈ B → z ∈ H → ∃ i, phi z = mu j i z := by
  exact hline.explicit_multilinear_cover_with
    (section16_slice_provider_of_freiman_families hq B phi D f hfreiman hcover)
    (section16_freiman_slice_provider_ranges hq) (by decide)
    ht ht1 hg hg1 hEd hrho hrho1 m P hP hm

end LeanProofs.GowersSzemeredi
