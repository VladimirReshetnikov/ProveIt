import GowersSzemeredi.Proofs16Lemma5With
import GowersSzemeredi.Proofs16DenseSelection
import GowersSzemeredi.Proofs16CommonBase

/-! **The dense induced selection and Lemma 16.7 with `(θ₁, ζ)` as
parameters** (Notes L.16d).

* `section16_dense_induced_selection_with`: the corpus's
  `section16_dense_induced_selection_of_arrangements` with
  `section16ThetaOne θ γ k ↦ t1` and `section16Zeta θ γ k ↦ zeta`. It
  assumes `0 < t1/4 ≤ 1/36`, `ζ ≤ section10Zeta α` for `t1/4 ≤ α ≤ 1/6`, and
  `0 < ζ`, and runs through `Proofs16Lemma5With`.
* `lemma_16_7_with`: Lemma 16.7 for any `t1 ≥ 0` and any `zeta`. The
  corpus proof never uses the printed formulas beyond `θ₁ ≥ 0`.

Both proofs are generated from the corpus proofs by a script with a guard
that no printed parameter survives. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem section16_dense_induced_selection_with {N k : Nat} [NeZero N]
    (hprime : N.Prime) (t1 zeta : Real) (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N)
    (ha0 : 0 < t1 / 4) (haS : t1 / 4 ≤ 1 / 36)
    (hzeta : ∀ alpha : Real, t1 / 4 ≤ alpha → alpha ≤ 1 / 6 → zeta ≤ section10Zeta alpha)
    (hz0 : 0 < zeta)
    (hB : t1 * (N : Real) ^ (17 * k + 15) ≤
        generalArrangementCount 8 B ∧
      (1 - (2 : Real) ^ (-(44 : Real))) * generalArrangementCount 8 B ≤
        respectedGeneralArrangementCount 8 B phi) :
    ∃ H : Finset (Point N k),
      ∃ Y : (h : Point N k) → Finset (Section16CubeElement B h),
        ∃ phiPrime : Point N k → ZMod N → ZMod N,
          t1 / 4 * (N : Real) ^ k ≤ H.card ∧
          (∀ h ∈ H, t1 / 4 * (N : Real) ^ (k + 1) ≤
            (section16CubeDomain B h).card) ∧
          (∀ h ∈ H, (2 : Real) ^ (-(27 : Real)) * (t1) ^ 6 *
            (section16CubeDomain B h).card ≤ (Y h).card) ∧
          Section16InducedSelection B phi H Y
            (fun h => section16LargeSpectrum B h (section16Delta (t1)))
            (zeta) phiPrime := by
  classical
  obtain ⟨H, hmass, hgood⟩ :=
    section16_good_sidelengths_with t1 B phi (by linarith) hB
  have hex : ∀ h : Point N k,
      ∃ Y : Finset (Section16CubeElement B h), ∃ psi : ZMod N → ZMod N,
        h ∈ H →
          (2 : Real) ^ (-(27 : Real)) * (t1) ^ 6 *
            (section16CubeDomain B h).card ≤ Y.card ∧
          HasBohrDifferenceModel (section16CubeMultifunctionDomain B h)
            (section16InducedCubeMap B h phi)
            (section16LargeSpectrum B h (section16Delta (t1)))
            (zeta) Y psi := by
    intro h
    by_cases hh : h ∈ H
    · obtain ⟨Y, psi, hY⟩ := section16_selected_side_model_with t1 zeta B phi h ha0 haS hzeta
        (hgood h hh).1 (hgood h hh).2
      exact ⟨Y, psi, fun _ => hY⟩
    · exact ⟨∅, fun _ => 0, fun hh' => (hh hh').elim⟩
  choose Y psi hY using hex
  obtain ⟨phiPrime, hselection⟩ := section16_inducedSelection_exists B phi H Y _ _ psi hprime
    hz0.le (fun h hh => (hY h hh).2)
  exact ⟨H, Y, phiPrime, section16_sidelength_card_of_mass B H _ hmass,
    fun h hh => section16_cube_card_lower B h _ (hgood h hh).1,
    fun h hh => (hY h hh).1, hselection⟩


private abbrev Lemma167wWitness {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) :=
  Σ h : Point N k, Section16CubeElement B h

private noncomputable def lemma167wWitnesses {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (H : Finset (Point N k))
    (Y : (h : Point N k) → Finset (Section16CubeElement B h)) :
    Finset (Lemma167wWitness B) :=
  H.sigma Y

private def lemma167wTarget {N k : Nat} [NeZero N]
    {B : Finset (Point N (k + 1))} (w : Lemma167wWitness B) :
    Point N k × (Point N k × ZMod N) :=
  (w.2.1.1.base, (w.1, w.2.1.2))

private lemma lemma167w_cube_side {N k : Nat} [NeZero N]
    {B : Finset (Point N (k + 1))} {h : Point N k}
    (C : Section16CubeElement B h) : C.1.1.side = h := by
  have hC := C.property
  simp only [section16CubeDomain, Finset.mem_filter, Finset.mem_univ,
    true_and] at hC
  exact hC.1

private lemma lemma167wTarget_good {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (H : Finset (Point N k))
    (Y : (h : Point N k) → Finset (Section16CubeElement B h))
    (w : Lemma167wWitness B) (hw : w ∈ lemma167wWitnesses B H Y) :
    Section16GoodInducedPair B H Y (lemma167wTarget w).1
      (lemma167wTarget w).2 := by
  have hmem := Finset.mem_sigma.mp hw
  exact ⟨hmem.1, w.2, hmem.2, rfl, rfl⟩

private lemma lemma167wTarget_injOn {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (H : Finset (Point N k))
    (Y : (h : Point N k) → Finset (Section16CubeElement B h)) :
    Set.InjOn lemma167wTarget (lemma167wWitnesses B H Y : Set (Lemma167wWitness B)) := by
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
      · exact (lemma167w_cube_side C).trans (lemma167w_cube_side C').symm
    · exact congrArg (fun q => q.2.2) hwz
  exact congrArg (fun D : Section16CubeElement B h => Sigma.mk h D) hC

private noncomputable def lemma167wGoodTriples {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (H : Finset (Point N k))
    (Y : (h : Point N k) → Finset (Section16CubeElement B h)) :
    Finset (Point N k × (Point N k × ZMod N)) := by
  classical
  exact Finset.univ.filter fun q => Section16GoodInducedPair B H Y q.1 q.2

private lemma lemma167w_witness_card {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (H : Finset (Point N k))
    (Y : (h : Point N k) → Finset (Section16CubeElement B h)) :
    (lemma167wWitnesses B H Y).card = ∑ h ∈ H, (Y h).card := by
  simp [lemma167wWitnesses, Finset.card_sigma]

private lemma lemma167w_witness_le_good {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (H : Finset (Point N k))
    (Y : (h : Point N k) → Finset (Section16CubeElement B h)) :
    (lemma167wWitnesses B H Y).card ≤ (lemma167wGoodTriples B H Y).card := by
  classical
  exact Finset.card_le_card_of_injOn lemma167wTarget
    (fun w hw => by
      show lemma167wTarget w ∈ lemma167wGoodTriples B H Y
      simpa [lemma167wGoodTriples] using lemma167wTarget_good B H Y w hw)
    (lemma167wTarget_injOn B H Y)

private lemma lemma167w_countWhere_eq_sum_ite {X : Type*} [Fintype X]
    (P : X → Prop) :
    countWhere P = ∑ x : X,
      @ite Nat (P x) (Classical.propDecidable (P x)) 1 0 := by
  classical
  unfold countWhere
  simp

private lemma lemma167w_good_card {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (H : Finset (Point N k))
    (Y : (h : Point N k) → Finset (Section16CubeElement B h)) :
    (lemma167wGoodTriples B H Y).card =
      ∑ x0 : Point N k, section16GoodInducedPairCount B H Y x0 := by
  classical
  change countWhere (fun q : Point N k × (Point N k × ZMod N) =>
      Section16GoodInducedPair B H Y q.1 q.2) =
    ∑ x0 : Point N k,
      countWhere (Section16GoodInducedPair B H Y x0)
  rw [lemma167w_countWhere_eq_sum_ite]
  simp_rw [lemma167w_countWhere_eq_sum_ite]
  rw [Fintype.sum_prod_type]

private lemma lemma167w_sum_good_lower {N k : Nat} [NeZero N]
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
    have hnat := lemma167w_witness_le_good B H Y
    rw [lemma167w_witness_card, lemma167w_good_card] at hnat
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

private lemma lemma167w_point_card {N k : Nat} [NeZero N] :
    Fintype.card (Point N k) = N ^ k := by
  simp [ZMod.card]

private lemma lemma167w_value_of_good {N k : Nat} [NeZero N]
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
  have hside : C.1.1.side = z.1 := lemma167w_cube_side C
  simp only [section16InducedCubeMap, section16CubeValueAtBase]
  apply Finset.sum_congr rfl
  intro e he
  congr 2
  unfold AxisCube.vertex
  rw [hbase, hside]

/-- **Gowers, Lemma 16.7.** -/

theorem lemma_16_7_with {N k : Nat} [NeZero N] (t1 zeta : Real) (ht1 : 0 ≤ t1)
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (H1 : Finset (Point N k)) (Y : (h : Point N k) → Finset (Section16CubeElement B h))
    (phiPrime : Point N k → ZMod N → ZMod N)
    (hH : t1 / 8 * (N : Real) ^ k ≤ H1.card)
    (hX : ∀ h, h ∈ H1 → t1 / 4 * (N : Real) ^ (k + 1) ≤ (section16CubeDomain B h).card)
    (hY : ∀ h, h ∈ H1 →
      (2 : Real) ^ (-(27 : Real)) * t1 ^ 6 * (section16CubeDomain B h).card ≤ (Y h).card)
    (hselection : Section16InducedSelection B phi H1 Y
      (fun h => section16LargeSpectrum B h (section16Delta t1)) zeta phiPrime) :
    ∃ x0 : Point N k,
      section16ThetaTwo t1 * (N : Real) ^ (k + 1) ≤ section16GoodInducedPairCount B H1 Y x0 ∧
      ∀ z, Section16GoodInducedPair B H1 Y x0 z →
        phiPrime z.1 z.2 = section16CubeValueAtBase phi x0 z.1 z.2 := by
  classical
  let theta1 := t1
  have htheta1 : 0 ≤ theta1 := ht1
  have htotal := lemma167w_sum_good_lower theta1 B H1 Y hH hX hY htheta1
  have hcard :
      (Fintype.card (Point N k) : Real) *
          (section16ThetaTwo theta1 * (N : Real) ^ (k + 1)) ≤
        ∑ x0 : Point N k,
          (section16GoodInducedPairCount B H1 Y x0 : Real) := by
    rw [lemma167w_point_card]
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
    exact lemma167w_value_of_good B phi H1 Y phiPrime
      hselection.1 x0 z hz


end LeanProofs.GowersSzemeredi
