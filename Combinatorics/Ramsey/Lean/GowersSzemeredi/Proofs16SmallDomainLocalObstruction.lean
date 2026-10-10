import GowersSzemeredi.Proofs16WeightedGraphSums
import GowersSzemeredi.Proofs16IntervalWordGeometry
import GowersSzemeredi.Proofs16SinglePieceSpectrum
import GowersSzemeredi.Proofs16EqualSideBoxCover
import Mathlib.Data.Nat.Prime.Infinite

/-! Ambient-normalized product property on small coordinate sections.

An arbitrary map on an interval box of width L has unit product property
whenever L^2 <= N. Consequently that property alone cannot provide a local
multilinear piece with fixed positive density and unbounded promised width.
This audits the auxiliary local input; it does not refute Theorem 16.2. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- The graph-pair support has at most |E|^2 elements, independently of the maps. -/
theorem weightedSimultaneousAdditiveEnergy_small_domain {N p : Nat} [NeZero N]
    (E : Finset (ZMod N)) (w : ZMod N → Real) (psi : Fin p → ZMod N → ZMod N)
    (hE : E.card ^ 2 ≤ N) :
    (N : Real)⁻¹ * (∑ x ∈ E, w x) ^ 4 ≤ weightedSimultaneousAdditiveEnergy E w psi := by
  classical
  let T := (E ×ˢ E).image (section16ParallelPairSum psi)
  have hc : T.card ≤ N := by
    apply (Finset.card_image_le).trans
    simpa [Finset.card_product, pow_two] using hE
  have hb := weightedSimultaneousAdditiveEnergy_support_bound E w psi T
    (fun a ha b hb => Finset.mem_image.mpr ⟨(a,b), Finset.mem_product.mpr ⟨ha,hb⟩, rfl⟩)
    (show (T.card : Real) ≤ N by exact_mod_cast hc)
  have hN : (0 : Real) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  calc
    _ ≤ (N : Real)⁻¹ * ((N : Real) * weightedSimultaneousAdditiveEnergy E w psi) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hN.le)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hN.ne', one_mul]

/-- Unit product property is automatic if every coordinate section has at
most sqrt(N) points. This includes every map, not just multilinear maps. -/
theorem HasProductProperty.of_small_coordinate_sections {N k : Nat} [NeZero N]
    (B : Finset (Point N k)) (phi : Point N k → ZMod N)
    (hB : ∀ y j, (coordinateSection B y j).card ^ 2 ≤ N) :
    HasProductProperty B phi 1 := by
  classical
  intro p j y E w hw hE
  cases p with
  | zero =>
    have he : (fun i : Fin 0 => coordinateRestriction phi (y i) j) =
        (fun _ : Fin 0 => fun _ : ZMod N => 0) := Subsingleton.elim _ _
    rw [he]
    exact (section16_zero_unit_product (N := N) (k := k)) 0 j y E w hw
      (fun _ _ _ => Finset.mem_univ _)
  | succ p =>
    have hsub : E ⊆ coordinateSection B (y 0) j := by
      intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hE 0 x hx⟩
    have hc := (Nat.pow_le_pow_left (Finset.card_le_card hsub) 2).trans (hB (y 0) j)
    simpa only [one_pow, one_mul] using
      weightedSimultaneousAdditiveEnergy_small_domain E w
        (fun i => coordinateRestriction phi (y i) j) hc

/-- Unit product property supplies every smaller nonnegative parameter. -/
theorem HasProductProperty.of_unit_parameter {N k : Nat} [NeZero N]
    {B : Finset (Point N k)} {phi : Point N k → ZMod N}
    (hunit : HasProductProperty B phi 1) {gamma : Real}
    (hg : 0 ≤ gamma) (hg1 : gamma ≤ 1) : HasProductProperty B phi gamma := by
  intro p j y E theta ht hE
  have hp : gamma ^ (8 * p) ≤ 1 := pow_le_one₀ hg hg1
  have hweight : 0 ≤ (N : Real)⁻¹ * (∑ x ∈ E, theta x) ^ 4 := by positivity
  calc
    _ = gamma ^ (8 * p) * ((N : Real)⁻¹ * (∑ x ∈ E, theta x) ^ 4) := by ring
    _ ≤ 1 * ((N : Real)⁻¹ * (∑ x ∈ E, theta x) ^ 4) :=
      mul_le_mul_of_nonneg_right hp hweight
    _ ≤ _ := by simpa only [one_pow, one_mul] using hunit p j y E theta ht hE

/-- Short interval boxes carry unit product property for arbitrary maps. -/
theorem interval_box_arbitrary_unit_product {N k L : Nat} [NeZero N]
    (phi : Point N k → ZMod N) (hL : L ^ 2 ≤ N) :
    HasProductProperty (alphabetIntervalBox N k L).carrier phi 1 := by
  classical
  apply HasProductProperty.of_small_coordinate_sections
  intro y j
  have hsub : coordinateSection (alphabetIntervalBox N k L).carrier y j ⊆
      (modInterval N 0 L).carrier := by
    intro x hx
    have hb := (Finset.mem_filter.mp hx).2
    have hh := (Finset.mem_filter.mp hb).2 j
    simpa [alphabetIntervalBox, replaceCoordinate] using hh
  have hi : (modInterval N 0 L).carrier.card ≤ L := by
    change (Finset.univ.image (fun i : Fin L => (0 : ZMod N) + (i : Nat) * 1)).card ≤ L
    exact Finset.card_image_le.trans (by rw [Finset.card_univ, Fintype.card_fin])
  exact (Nat.pow_le_pow_left ((Finset.card_le_card hsub).trans hi) 2).trans hL

/-- An affine function agrees with a quadratic at at most two field points. -/
theorem quadratic_affine_agreement_card {N : Nat} [Fact N.Prime]
    (S : Finset (ZMod N)) (a b : ZMod N) :
    (S.filter fun x => x ^ 2 = a * x + b).card ≤ 2 := by
  classical
  let A := S.filter fun x => x ^ 2 = a * x + b
  by_cases hA : A.Nonempty
  · obtain ⟨r, hr⟩ := hA
    have hroot := (Finset.mem_filter.mp hr).2
    have hsub : A ⊆ {r, a - r} := by
      intro x hx
      by_cases hxr : x = r
      · simp [hxr]
      · have hxroot := (Finset.mem_filter.mp hx).2
        have he : (x - r) * (x + r - a) = 0 := by
          linear_combination hxroot - hroot
        have hz : x + r - a = 0 :=
          (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hxr)
        have hxar : x = a - r := by linear_combination hz
        simp [hxar]
    exact (Finset.card_le_card hsub).trans (by
      calc ({r, a - r} : Finset (ZMod N)).card ≤ ({a - r} : Finset (ZMod N)).card + 1 :=
          Finset.card_insert_le _ _
        _ = 2 := by rw [Finset.card_singleton])
  · simp only [Finset.not_nonempty_iff_eq_empty] at hA
    change A.card ≤ 2
    rw [hA]
    simp

/-- The one-dimensional quadratic has at most two agreement points with
any multilinear map, even on an arbitrary partial domain. -/
theorem quadratic_multilinear_agreement_card {N : Nat} [NeZero N] [Fact N.Prime]
    (B : Finset (Point N 1)) (mu : Point N 1 → ZMod N) (hmu : IsMultilinear mu) :
    (B.filter fun z => (z 0) ^ 2 = mu z).card ≤ 2 := by
  classical
  obtain ⟨a, b, hab⟩ := hmu.linearOn_coordinate (0 : Point N 1) 0
  have hformula (z : Point N 1) : mu z = a * z 0 + b := by
    have he : replaceCoordinate (0 : Point N 1) 0 (z 0) = z := by
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp [replaceCoordinate]
    have h := hab (z 0) (Finset.mem_univ _)
    simpa only [coordinateRestriction, he] using h
  let A := B.filter fun z => (z 0) ^ 2 = mu z
  have hinj : Function.Injective (fun z : Point N 1 => z 0) := by
    intro z z' h
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact h
  have hsub : A.image (fun z => z 0) ⊆
      (Finset.univ : Finset (ZMod N)).filter (fun x => x ^ 2 = a * x + b) := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact (Finset.mem_filter.mp hz).2.trans (hformula z)
  change A.card ≤ 2
  rw [← Finset.card_image_of_injective A hinj]
  exact (Finset.card_le_card hsub).trans (quadratic_affine_agreement_card _ a b)

/-- The raw local input fails whenever the promised density times width
exceeds two at density one. This excludes positive-density growing-width
controls. The prime can be chosen above any prescribed threshold. -/
theorem not_localMultilinearPieceAt_of_quadratic
    {gamma : Real} (hg : 0 ≤ gamma) (hg1 : gamma ≤ 1)
    (c : Real → Real) (w : Real → Nat → Nat) (hc : 0 ≤ c 1)
    {L : Nat} (hL : 1 ≤ L) (hw : 2 < c 1 * w 1 L) :
    ¬ LocalMultilinearPieceAt 1 gamma c w := by
  classical
  intro hlocal
  obtain ⟨N, hsize, hprime⟩ := Nat.exists_infinite_primes (max (L ^ 2) 3)
  letI : Fact N.Prime := ⟨hprime⟩
  letI : NeZero N := ⟨hprime.ne_zero⟩
  have hLN : L ≤ N := by
    have hpow : L ≤ L ^ 2 := by nlinarith
    exact hpow.trans ((le_max_left _ _).trans hsize)
  let P := alphabetIntervalBox N 1 L
  let B := P.carrier
  let phi : Point N 1 → ZMod N := fun z => (z 0) ^ 2
  obtain ⟨R, mu, hR, hsub, hwidth, hmu, hcount⟩ :=
    hlocal N 1 (by norm_num) (by norm_num) P B phi
      (alphabetIntervalBox_proper hLN) (Finset.Subset.refl _) (by simp [B])
      ((interval_box_arbitrary_unit_product phi ((le_max_left _ _).trans hsize)).of_unit_parameter hg hg1)
  have hwide : w 1 L ≤ R.width := by
    simpa only [P, alphabetIntervalBox_width] using hwidth
  have hcard : R.carrier.card = R.width := by
    rw [Box.card_eq_prod_axis_card]
    simp only [Fin.prod_univ_one]
    rw [show (R.axis 0).carrier.card = (R.axis 0).length from hR 0]
    apply Nat.le_antisymm
    · exact Box.le_width_of_le_axis _ (by norm_num) (by intro i; have hi : i = 0 := Subsingleton.elim _ _; subst i; rfl)
    · exact R.width_le_axis_length 0
  have hsubfilter : (B.filter fun z => z ∈ R.carrier ∧ phi z = mu z) ⊆
      B.filter (fun z => (z 0) ^ 2 = mu z) := by
    intro z hz
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2.2⟩
  have htwo : (B.filter fun z => z ∈ R.carrier ∧ phi z = mu z).card ≤ 2 :=
    (Finset.card_le_card hsubfilter).trans (quadratic_multilinear_agreement_card B mu hmu)
  have hle : c 1 * (w 1 L : Real) ≤ c 1 * R.carrier.card := by
    rw [hcard]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hwide) hc
  have hupper : c 1 * (w 1 L : Real) ≤ 2 :=
    hle.trans (hcount.trans (by exact_mod_cast htwo))
  exact (not_lt_of_ge hupper) hw

/-- Necessary control budget for the raw local input. Any positive value
of c(1) forces bounded promised width, so growing widths are excluded. -/
theorem LocalMultilinearPieceAt.unit_density_width_budget
    {gamma : Real} (hg : 0 ≤ gamma) (hg1 : gamma ≤ 1)
    {c : Real → Real} {w : Real → Nat → Nat}
    (hlocal : LocalMultilinearPieceAt 1 gamma c w) (hc : 0 ≤ c 1)
    {L : Nat} (hL : 1 ≤ L) : c 1 * (w 1 L : Real) ≤ 2 := by
  by_contra h
  exact not_localMultilinearPieceAt_of_quadratic hg hg1 c w hc hL (lt_of_not_ge h) hlocal

/-- The raw relation-cover input has the same obstruction after averaging
its finite graph family. A fixed graph budget cannot restore growing width. -/
theorem not_localRelationCoverAt_of_quadratic {gamma : Real}
    (hg : 0 ≤ gamma) (hg1 : gamma ≤ 1)
    (Qc : Real → Nat → Real) (c : Real → Real) (w : Real → Nat → Nat)
    (hQ : ∀ t, 1 ≤ Qc t 1) (hc : 0 ≤ c 1)
    {L : Nat} (hL : 1 ≤ L) (hw : 2 < (c 1 / Qc 1 1) * (w 1 L : Real)) :
    ¬ LocalRelationCoverAt 1 gamma Qc c w := by
  intro hcover
  exact not_localMultilinearPieceAt_of_quadratic hg hg1 (fun t => c t / Qc t 1) w
    (div_nonneg hc (by linarith [hQ 1])) hL hw (hcover.localMultilinearPieceAt hQ)

end LeanProofs.GowersSzemeredi
