import GowersSzemeredi.Section16
import Mathlib.Combinatorics.Pigeonhole

/-!
# A common cube base in Gowers's Section 16

This module proves Lemma 16.7.  The proof is the finite double-counting
argument from the paper: every selected cube contributes its base and final
cross-section to exactly one good pair, and averaging over all bases selects a
base supporting the required number of pairs.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private abbrev Lemma167Witness {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) :=
  Σ h : Point N k, Section16CubeElement B h

private noncomputable def lemma167Witnesses {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (H : Finset (Point N k))
    (Y : (h : Point N k) → Finset (Section16CubeElement B h)) :
    Finset (Lemma167Witness B) :=
  H.sigma Y

private def lemma167Target {N k : Nat} [NeZero N]
    {B : Finset (Point N (k + 1))} (w : Lemma167Witness B) :
    Point N k × (Point N k × ZMod N) :=
  (w.2.1.1.base, (w.1, w.2.1.2))

private lemma lemma167_cube_side {N k : Nat} [NeZero N]
    {B : Finset (Point N (k + 1))} {h : Point N k}
    (C : Section16CubeElement B h) : C.1.1.side = h := by
  have hC := C.property
  simp only [section16CubeDomain, Finset.mem_filter, Finset.mem_univ,
    true_and] at hC
  exact hC.1

private lemma lemma167Target_good {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (H : Finset (Point N k))
    (Y : (h : Point N k) → Finset (Section16CubeElement B h))
    (w : Lemma167Witness B) (hw : w ∈ lemma167Witnesses B H Y) :
    Section16GoodInducedPair B H Y (lemma167Target w).1
      (lemma167Target w).2 := by
  have hmem := Finset.mem_sigma.mp hw
  exact ⟨hmem.1, w.2, hmem.2, rfl, rfl⟩

private lemma lemma167Target_injOn {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (H : Finset (Point N k))
    (Y : (h : Point N k) → Finset (Section16CubeElement B h)) :
    Set.InjOn lemma167Target (lemma167Witnesses B H Y : Set (Lemma167Witness B)) := by
  intro w hw z hz hwz
  rcases w with ⟨h, C⟩
  rcases z with ⟨h', C'⟩
  change (C.1.1.base, (h, C.1.2)) =
    (C'.1.1.base, (h', C'.1.2)) at hwz
  have hh : h = h' := congrArg (fun q => q.2.1) hwz
  subst h'
  have hC : C = C' := by
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · exact congrArg
          (fun q : Point N k × (Point N k × ZMod N) => q.1) hwz
      · exact (lemma167_cube_side C).trans (lemma167_cube_side C').symm
    · exact congrArg (fun q => q.2.2) hwz
  exact congrArg (fun D : Section16CubeElement B h => Sigma.mk h D) hC

private noncomputable def lemma167GoodTriples {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (H : Finset (Point N k))
    (Y : (h : Point N k) → Finset (Section16CubeElement B h)) :
    Finset (Point N k × (Point N k × ZMod N)) := by
  classical
  exact Finset.univ.filter fun q => Section16GoodInducedPair B H Y q.1 q.2

private lemma lemma167_witness_card {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (H : Finset (Point N k))
    (Y : (h : Point N k) → Finset (Section16CubeElement B h)) :
    (lemma167Witnesses B H Y).card = ∑ h ∈ H, (Y h).card := by
  simp [lemma167Witnesses, Finset.card_sigma]

private lemma lemma167_witness_le_good {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (H : Finset (Point N k))
    (Y : (h : Point N k) → Finset (Section16CubeElement B h)) :
    (lemma167Witnesses B H Y).card ≤ (lemma167GoodTriples B H Y).card := by
  classical
  exact Finset.card_le_card_of_injOn lemma167Target
    (fun w hw => by
      show lemma167Target w ∈ lemma167GoodTriples B H Y
      simpa [lemma167GoodTriples] using lemma167Target_good B H Y w hw)
    (lemma167Target_injOn B H Y)

private lemma lemma167_countWhere_eq_sum_ite {X : Type*} [Fintype X]
    (P : X → Prop) :
    countWhere P = ∑ x : X,
      @ite Nat (P x) (Classical.propDecidable (P x)) 1 0 := by
  classical
  unfold countWhere
  simp

private lemma lemma167_good_card {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (H : Finset (Point N k))
    (Y : (h : Point N k) → Finset (Section16CubeElement B h)) :
    (lemma167GoodTriples B H Y).card =
      ∑ x0 : Point N k, section16GoodInducedPairCount B H Y x0 := by
  classical
  change countWhere (fun q : Point N k × (Point N k × ZMod N) =>
      Section16GoodInducedPair B H Y q.1 q.2) =
    ∑ x0 : Point N k,
      countWhere (Section16GoodInducedPair B H Y x0)
  rw [lemma167_countWhere_eq_sum_ite]
  simp_rw [lemma167_countWhere_eq_sum_ite]
  rw [Fintype.sum_prod_type]

private lemma lemma167_sum_good_lower {N k : Nat} [NeZero N]
    (theta1 : Real) (B : Finset (Point N (k + 1)))
    (H : Finset (Point N k))
    (Y : (h : Point N k) → Finset (Section16CubeElement B h))
    (hH : theta1 / 8 * (N : Real) ^ k ≤ H.card)
    (hX : ∀ h, h ∈ H → theta1 / 4 * (N : Real) ^ (k + 1) ≤
      (section16CubeDomain B h).card)
    (hY : ∀ h, h ∈ H →
      (2 : Real) ^ (-(27 : Real)) * theta1 ^ 6 *
          (section16CubeDomain B h).card ≤ (Y h).card)
    (htheta1 : 0 ≤ theta1) :
    section16ThetaTwo theta1 * (N : Real) ^ (2 * k + 1) ≤
      ∑ x0 : Point N k, (section16GoodInducedPairCount B H Y x0 : Real) := by
  have hcoefficient :
      0 ≤ (2 : Real) ^ (-(27 : Real)) * theta1 ^ 6 := by positivity
  have htwo29 :
      (2 : Real) ^ (-(29 : Real)) =
        (2 : Real) ^ (-(27 : Real)) / 4 := by
    norm_num [Real.rpow_neg, Real.rpow_natCast]
  have hper (h : Point N k) (hh : h ∈ H) :
      (2 : Real) ^ (-(29 : Real)) * theta1 ^ (7 : Nat) *
          (N : Real) ^ (k + 1) ≤ (Y h).card := by
    calc
      (2 : Real) ^ (-(29 : Real)) * theta1 ^ (7 : Nat) *
          (N : Real) ^ (k + 1) =
          ((2 : Real) ^ (-(27 : Real)) * theta1 ^ 6) *
            (theta1 / 4 * (N : Real) ^ (k + 1)) := by
              rw [htwo29]
              ring
      _ ≤ ((2 : Real) ^ (-(27 : Real)) * theta1 ^ 6) *
          (section16CubeDomain B h).card := by
            exact mul_le_mul_of_nonneg_left (hX h hh) hcoefficient
      _ ≤ (Y h).card := hY h hh
  have hsumY :
      (H.card : Real) *
          ((2 : Real) ^ (-(29 : Real)) * theta1 ^ (7 : Nat) *
            (N : Real) ^ (k + 1)) ≤
        ∑ h ∈ H, ((Y h).card : Real) := by
    calc
      (H.card : Real) *
          ((2 : Real) ^ (-(29 : Real)) * theta1 ^ 7 *
            (N : Real) ^ (k + 1)) =
          ∑ _h ∈ H,
            ((2 : Real) ^ (-(29 : Real)) * theta1 ^ (7 : Nat) *
              (N : Real) ^ (k + 1)) := by simp
      _ ≤ ∑ h ∈ H, ((Y h).card : Real) := by
        exact Finset.sum_le_sum fun h hh => hper h hh
  have hperNonneg :
      0 ≤ (2 : Real) ^ (-(29 : Real)) * theta1 ^ (7 : Nat) *
        (N : Real) ^ (k + 1) := by positivity
  have hproduct :
      (theta1 / 8 * (N : Real) ^ k) *
          ((2 : Real) ^ (-(29 : Real)) * theta1 ^ (7 : Nat) *
            (N : Real) ^ (k + 1)) ≤
        ∑ h ∈ H, ((Y h).card : Real) := by
    exact (mul_le_mul_of_nonneg_right hH hperNonneg).trans hsumY
  have hwitness :
      ∑ h ∈ H, ((Y h).card : Real) ≤
        ∑ x0 : Point N k,
          (section16GoodInducedPairCount B H Y x0 : Real) := by
    have hnat := lemma167_witness_le_good B H Y
    rw [lemma167_witness_card, lemma167_good_card] at hnat
    exact_mod_cast hnat
  calc
    section16ThetaTwo theta1 * (N : Real) ^ (2 * k + 1) =
        (theta1 / 8 * (N : Real) ^ k) *
          ((2 : Real) ^ (-(29 : Real)) * theta1 ^ (7 : Nat) *
            (N : Real) ^ (k + 1)) := by
      unfold section16ThetaTwo
      have htwo32 :
          (2 : Real) ^ (-(32 : Real)) =
            (1 / 8) * (2 : Real) ^ (-(29 : Real)) := by
        norm_num [Real.rpow_neg, Real.rpow_natCast]
      have hNpow :
          (N : Real) ^ (2 * k + 1) =
            (N : Real) ^ k * (N : Real) ^ (k + 1) := by
        rw [← pow_add]
        congr 1
        omega
      rw [htwo32, hNpow]
      ring
    _ ≤ ∑ h ∈ H, ((Y h).card : Real) := hproduct
    _ ≤ ∑ x0 : Point N k,
        (section16GoodInducedPairCount B H Y x0 : Real) := hwitness

private lemma lemma167_point_card {N k : Nat} [NeZero N] :
    Fintype.card (Point N k) = N ^ k := by
  simp [ZMod.card]

private lemma lemma167_value_of_good {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (H : Finset (Point N k))
    (Y : (h : Point N k) → Finset (Section16CubeElement B h))
    (phiPrime : Point N k → ZMod N → ZMod N)
    (hvalues : ∀ h, h ∈ H → ∀ C, C ∈ Y h →
      phiPrime h C.1.2 = section16InducedCubeMap B h phi C)
    (x0 : Point N k) (z : Point N k × ZMod N)
    (hz : Section16GoodInducedPair B H Y x0 z) :
    phiPrime z.1 z.2 = section16CubeValueAtBase phi x0 z.1 z.2 := by
  rcases hz with ⟨hzH, C, hCY, hbase, hx⟩
  have hvalue := hvalues z.1 hzH C hCY
  rw [← hx, hvalue]
  have hside : C.1.1.side = z.1 := lemma167_cube_side C
  simp only [section16InducedCubeMap, section16CubeValueAtBase]
  apply Finset.sum_congr rfl
  intro e he
  congr 2
  unfold AxisCube.vertex
  rw [hbase, hside]

/-- **Gowers, Lemma 16.7.** -/
theorem lemma_16_7_holds : lemma_16_7 := by
  classical
  unfold lemma_16_7
  intro N k _ theta gamma B phi H1 Y phiPrime
  dsimp only
  intro hH hX hY hselection
  let theta1 := section16ThetaOne theta gamma k
  have htheta1 : 0 ≤ theta1 := by
    dsimp only [theta1, section16ThetaOne]
    exact (Nat.even_pow.mpr ⟨even_two, by positivity⟩).pow_nonneg _
  have htotal := lemma167_sum_good_lower theta1 B H1 Y hH hX hY htheta1
  have hcard :
      (Fintype.card (Point N k) : Real) *
          (section16ThetaTwo theta1 * (N : Real) ^ (k + 1)) ≤
        ∑ x0 : Point N k,
          (section16GoodInducedPairCount B H1 Y x0 : Real) := by
    rw [lemma167_point_card]
    have hNpow :
        (N : Real) ^ (2 * k + 1) =
          (N : Real) ^ k * (N : Real) ^ (k + 1) := by
      rw [← pow_add]
      congr 1
      omega
    calc
      ((N ^ k : Nat) : Real) *
          (section16ThetaTwo theta1 * (N : Real) ^ (k + 1)) =
          section16ThetaTwo theta1 * (N : Real) ^ (2 * k + 1) := by
            push_cast
            rw [hNpow]
            ring
      _ ≤ _ := htotal
  obtain ⟨x0, hx0⟩ :=
    Fintype.exists_le_sum_fiber_of_nsmul_le_sum
      (β := Point N k) (f := fun x : Point N k => x)
      (w := fun x => (section16GoodInducedPairCount B H1 Y x : Real))
      (b := section16ThetaTwo theta1 * (N : Real) ^ (k + 1)) (by
        simpa only [nsmul_eq_mul] using hcard)
  refine ⟨x0, ?_, ?_⟩
  · have hsingle :
        (∑ x : Point N k with x = x0,
          (section16GoodInducedPairCount B H1 Y x : Real)) =
            section16GoodInducedPairCount B H1 Y x0 := by
      apply Finset.sum_eq_single x0
      · intro x hx hne
        exact (hne (Finset.mem_filter.mp hx).2).elim
      · simp
    rw [hsingle] at hx0
    simpa only [theta1] using hx0
  · intro z hz
    exact lemma167_value_of_good B phi H1 Y phiPrime
      hselection.1 x0 z hz

end LeanProofs.GowersSzemeredi
