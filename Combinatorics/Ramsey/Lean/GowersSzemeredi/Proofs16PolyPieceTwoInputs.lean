import GowersSzemeredi.Proofs16VertexWithCovers
import GowersSzemeredi.Proofs16FreimanFinalSections
import GowersSzemeredi.Proofs16FreimanFamilyRestriction
import GowersSzemeredi.Proofs16SynchronizedCover

/-! Inputs for the dimension-two polynomial piece cover.

`section16_piece_cover_with` needs a spectrum cover, a remainder cover and
a slice provider on one common sub-domain `D` of the good domain. In
dimension two each comes from `PolyCoverAt 1`, off a global deletion:
* `section16GoodDomain_inter`: restricting the base set to the spectrum's
  good set `J` filters the good domain by `init ∈ J`.
* `Section16PhiOneIdentity.mono`.
* `section16_final_freiman_families_of_product`: every final-coordinate
  slice keeps all but `θN` points in a Freiman family of size
  `section16BaseFamilyBound γ θ`. The pruned set `B*` carries
  `Section16FinalFreimanFamilies`.
* `Section16FinalFreimanFamilies.of_translate`: any domain whose
  translated points lie in `B*` carries the families of `φ₁`.
* `card_translated_slice_bad_le`: the translated points that miss `B*`
  number at most `θN²`.
* `cubicSlice_count_monotone` and `cubicSlice_exponent_antitone`: the
  cubic slice controls are monotone in the sample size. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem section16GoodDomain_inter {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (H J : Finset (Point N k))
    (Y : (h : Point N k) → Finset (Section16CubeElement B h)) (x0 : Point N k) :
    section16GoodDomain B (H ∩ J) Y x0 =
      (section16GoodDomain B H Y x0).filter fun z => section16Init z ∈ J := by
  classical
  ext z
  simp only [section16GoodDomain, Section16GoodInducedPair, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_inter]
  tauto

theorem Section16PhiOneIdentity.mono {N k : Nat} [NeZero N]
    {B1 B1' : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N} {x0 : Point N k}
    {phiPrime : Point N k → ZMod N → ZMod N}
    (h : Section16PhiOneIdentity B1 phi x0 phiPrime) (hsub : B1' ⊆ B1) :
    Section16PhiOneIdentity B1' phi x0 phiPrime :=
  fun z hz => h z (hsub hz)

/-- Every final-coordinate slice of a product-property function keeps all
but `θN` of its points in a Freiman family. -/
theorem section16_final_freiman_families_of_product {N : Nat} [Fact N.Prime]
    {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (B : Finset (Point N 2)) (phi : Point N 2 → ZMod N)
    (hprod : HasProductProperty B phi gamma) :
    ∃ C : ZMod N → Finset (Point N 1),
      (∀ t, C t ⊆ section16FinalCoordinateSection B t) ∧
      (∀ t, ((section16FinalCoordinateSection B t).card : Real) - theta * N ≤ (C t).card) ∧
      Section16FinalFreimanFamilies (section16BaseFamilyBound gamma theta)
        (B.filter fun z => section16Init z ∈ C (section16Last z)) phi := by
  classical
  have hsl : ∀ t : ZMod N, HasProductProperty (section16FinalCoordinateSection B t)
      (section16FinalCoordinateRestriction phi t) gamma := by
    intro t
    have h := hprod.coordinateFace (lastSliceFace 1 t)
    have hdom : (lastSliceFace 1 t).domain B = section16FinalCoordinateSection B t := by
      ext x
      simp [CoordinateFace.domain, section16FinalCoordinateSection, lastSliceFace]
    have hfun : (lastSliceFace 1 t).pullback phi = section16FinalCoordinateRestriction phi t := by
      funext x
      rfl
    rw [hdom, hfun] at h
    exact h
  have hex : ∀ t : ZMod N, ∃ C : Finset (Point N 1),
      C ⊆ section16FinalCoordinateSection B t ∧
      ((section16FinalCoordinateSection B t).card : Real) - theta * N ≤ C.card ∧
      Section16FreimanFamilyCover (section16BaseFamilyBound gamma theta) C
        (section16FinalCoordinateRestriction phi t) := fun t =>
    section16_restrict_function_freiman_family hg hg1 ht ht1 _ _ (hsl t)
  choose C hCsub hCcard hCfam using hex
  refine ⟨C, hCsub, hCcard, ?_⟩
  intro t
  apply (hCfam t).mono
  intro y hy
  have hy' := (Finset.mem_filter.mp (Finset.mem_filter.mp hy).2).2
  simpa only [section16Init_appendCoordinate, section16Last_appendCoordinate] using hy'

/-- The families of `φ` on `B*` give families of `φ₁` on any domain whose
translated points lie in `B*`. -/
theorem Section16FinalFreimanFamilies.of_translate {N q : Nat} [NeZero N]
    {Bs : Finset (Point N 2)} {phi : Point N 2 → ZMod N}
    (h : Section16FinalFreimanFamilies q Bs phi) (x0 : Point N 1)
    (D : Finset (Point N 2))
    (hD : ∀ z ∈ D, appendCoordinate (section16Init z + x0) (section16Last z) ∈ Bs) :
    Section16FinalFreimanFamilies q D (section16PhiOne phi x0) := by
  classical
  intro t
  have hp := (h t).translate (-x0)
  have heq : (fun y => section16FinalCoordinateRestriction phi t (y - -x0)) =
      section16FinalCoordinateRestriction (section16PhiOne phi x0) t := by
    funext y
    simp [section16FinalCoordinateRestriction, section16PhiOne,
      section16Init_appendCoordinate, section16Last_appendCoordinate, sub_neg_eq_add, add_comm]
    rfl
  rw [heq] at hp
  apply hp.mono
  intro y hy
  have hb := hD _ (Finset.mem_filter.mp hy).2
  simp only [section16Init_appendCoordinate, section16Last_appendCoordinate] at hb
  apply Finset.mem_image.mpr
  refine ⟨y + x0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, by simp⟩

/-- The translated points of a slice-pruned set that miss it are sparse. -/
theorem card_translated_slice_bad_le {N : Nat} [NeZero N] {theta : Real}
    (B : Finset (Point N 2)) (C : ZMod N → Finset (Point N 1))
    (hC : ∀ t, C t ⊆ section16FinalCoordinateSection B t)
    (hcard : ∀ t, ((section16FinalCoordinateSection B t).card : Real) - theta * N ≤ (C t).card)
    (x0 : Point N 1) :
    (((Finset.univ : Finset (Point N 2)).filter fun z =>
        appendCoordinate (section16Init z + x0) (section16Last z) ∈ B ∧
          section16Init z + x0 ∉ C (section16Last z)).card : Real) ≤
      theta * (N : Real) ^ 2 := by
  classical
  set X := (Finset.univ : Finset (Point N 2)).filter fun z =>
    appendCoordinate (section16Init z + x0) (section16Last z) ∈ B ∧
      section16Init z + x0 ∉ C (section16Last z) with hX
  rw [Finset.card_eq_sum_card_fiberwise (f := section16Last) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  push_cast
  have hfib : ∀ t : ZMod N, ((X.filter fun z => section16Last z = t).card : Real) ≤
      theta * (N : Real) := by
    intro t
    have h1 : (X.filter fun z => section16Last z = t).card ≤
        (section16FinalCoordinateSection B t \ C t).card := by
      refine Finset.card_le_card_of_injOn (fun z => section16Init z + x0) (fun z hz => ?_) ?_
      · obtain ⟨hz1, hz2⟩ := Finset.mem_filter.mp hz
        obtain ⟨-, hzB, hzC⟩ := Finset.mem_filter.mp hz1
        rw [hz2] at hzB hzC
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzB⟩, hzC⟩
      · intro z hz z' hz' hzz
        apply initLast_injective
        simp only [Prod.mk.injEq]
        refine ⟨add_right_cancel hzz, ?_⟩
        exact ((Finset.mem_filter.mp hz).2).trans ((Finset.mem_filter.mp hz').2).symm
    have h2 : ((section16FinalCoordinateSection B t \ C t).card : Real) ≤ theta * N := by
      have hsum : ((section16FinalCoordinateSection B t \ C t).card : Real) + (C t).card =
          (section16FinalCoordinateSection B t).card := by
        exact_mod_cast Finset.card_sdiff_add_card_eq_card (hC t)
      linarith [hcard t]
    exact (by exact_mod_cast h1 : ((X.filter fun z => section16Last z = t).card : Real) ≤
      ((section16FinalCoordinateSection B t \ C t).card : Real)).trans h2
  calc ∑ t : ZMod N, ((X.filter fun z => section16Last z = t).card : Real)
      ≤ ∑ _t : ZMod N, theta * (N : Real) := Finset.sum_le_sum fun t _ => hfib t
    _ = theta * (N : Real) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]; ring

theorem cubicSlice_count_monotone (q : Nat) :
    Monotone (fun r : Nat => ((3 * (max 1 r * q) : Nat) : Real)) := by
  intro r r' hrr
  dsimp only
  exact_mod_cast Nat.mul_le_mul_left 3 (Nat.mul_le_mul_right q (max_le_max le_rfl hrr))

theorem cubicSlice_exponent_antitone {q : Nat} (hq : 0 < q) {eps : Real} (heps : 0 < eps) :
    Antitone (fun r : Nat => cubicBaseExponent (max 1 r * q) eps) := by
  intro r r' hrr
  dsimp only
  unfold cubicBaseExponent
  have h1 : 0 < max 1 r * q := Nat.mul_pos (by omega) hq
  have hle : ((max 1 r * q : Nat) : Real) ≤ ((max 1 r' * q : Nat) : Real) := by
    exact_mod_cast Nat.mul_le_mul_right q (max_le_max le_rfl hrr)
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact pow_le_pow_left₀ (by positivity) hle 4

end LeanProofs.GowersSzemeredi
