import GowersSzemeredi.Proofs05PhaseRemoval
import GowersSzemeredi.ProofInfrastructure
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.GroupTheory.OrderOfElement

/-!
# Downstream consequences of the Section 5 polynomial partition

This module develops the bookkeeping needed to apply the interval form of
Corollary 5.6 on an arbitrary proper modular progression.  In particular it
proves that the affine pullback of a polynomial still has the same degree
bound, and transports the resulting partition of natural indices back to
`ZMod N` without losing properness or multiplicity information.

The final density and refinement arguments are kept conditional on the one
remaining analytic input, `corollary_5_6`, so that they cannot accidentally
hide the outstanding Weyl-recurrence theorem.

`section5_local_phase_refinement_of_corollary_5_6` is in
`Proofs05DownstreamSide`, outside the final route. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-! ### Affine parametrization of modular progressions -/

/-- The point with natural index `t` in a modular progression. -/
def section5IndexPoint {N : Nat} (P : ModAP N) (t : Nat) : ZMod N :=
  P.start + (t : ZMod N) * P.step

/-- The same parametrization, with a modular index. -/
def section5ModIndexPoint {N : Nat} (P : ModAP N) (t : ZMod N) : ZMod N :=
  P.start + t * P.step

/-- Transport a natural-number progression through a modular progression. -/
def section5Transport {N : Nat} (P : ModAP N) (R : NatAP) : ModAP N where
  start := section5IndexPoint P R.start
  step := (R.step : ZMod N) * P.step
  length := R.length

@[simp] theorem section5Transport_length {N : Nat} (P : ModAP N) (R : NatAP) :
    (section5Transport P R).length = R.length :=
  rfl

theorem section5_modIndexPoint_natCast {N : Nat} (P : ModAP N) (t : Nat) :
    section5ModIndexPoint P (t : ZMod N) = section5IndexPoint P t :=
  rfl

theorem section5_carrier_eq_image_range {N : Nat} (P : ModAP N) :
    P.carrier = (Finset.range P.length).image (section5IndexPoint P) := by
  ext x
  unfold ModAP.carrier section5IndexPoint
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.isLt, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩

theorem section5Transport_carrier {N : Nat} (P : ModAP N) (R : NatAP) :
    (section5Transport P R).carrier =
      R.carrier.image (section5IndexPoint P) := by
  ext x
  simp only [ModAP.carrier, NatAP.carrier, section5Transport,
    section5IndexPoint, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨R.start + (i : Nat) * R.step, ⟨i, rfl⟩, ?_⟩
    push_cast
    ring
  · rintro ⟨t, ⟨i, rfl⟩, rfl⟩
    refine ⟨i, ?_⟩
    push_cast
    ring

theorem section5IndexPoint_injective_on_range {N : Nat} [NeZero N]
    (P : ModAP N) (hP : P.IsProper) :
    Set.InjOn (section5IndexPoint P) (Finset.range P.length : Set Nat) := by
  rw [ModAP.IsProper, section5_carrier_eq_image_range] at hP
  have hinj : Set.InjOn (section5IndexPoint P)
      (Finset.range P.length : Set Nat) := by
    apply Finset.card_image_iff.mp
    simpa only [Finset.card_range] using hP
  exact hinj

theorem section5Transport_isProper {N : Nat} [NeZero N]
    (P : ModAP N) (R : NatAP) (hP : P.IsProper) (hR : R.IsProper)
    (hsub : R.carrier ⊆ Finset.range P.length) :
    (section5Transport P R).IsProper := by
  rw [ModAP.IsProper, section5Transport_carrier,
    Finset.card_image_iff.mpr]
  · exact hR.2
  · intro x hx y hy hxy
    exact section5IndexPoint_injective_on_range P hP (hsub hx) (hsub hy) hxy

theorem section5Transport_sum {N : Nat} [NeZero N]
    (P : ModAP N) (R : NatAP) (hP : P.IsProper)
    (hsub : R.carrier ⊆ Finset.range P.length) (g : ZMod N → Complex) :
    (∑ x ∈ (section5Transport P R).carrier, g x) =
      ∑ t ∈ R.carrier, g (section5IndexPoint P t) := by
  rw [section5Transport_carrier, Finset.sum_image]
  intro x hx y hy hxy
  exact section5IndexPoint_injective_on_range P hP (hsub hx) (hsub hy) hxy

theorem section5Transport_partition {N M : Nat} [NeZero N]
    (P : ModAP N) (R : Fin M → NatAP) (hP : P.IsProper)
    (hR : IsNatAPPartition R (Finset.range P.length)) :
    IsPartition (fun j => (section5Transport P (R j)).carrier) P.carrier := by
  have hinj := section5IndexPoint_injective_on_range P hP
  simp only [section5Transport_carrier]
  refine ⟨fun x => ?_, fun i j hij => ?_⟩
  · rw [section5_carrier_eq_image_range]
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨j, htj⟩ := (hR.1 t).mp ht
      exact ⟨j, t, htj, rfl⟩
    · rintro ⟨j, t, htj, rfl⟩
      exact ⟨t, IsPartition.cell_subset hR j htj, rfl⟩
  · rw [Finset.disjoint_left]
    rintro _ hxi hxj
    obtain ⟨s, hsi, rfl⟩ := Finset.mem_image.mp hxi
    obtain ⟨t, htj, hts⟩ := Finset.mem_image.mp hxj
    obtain rfl := hinj (IsPartition.cell_subset hR j htj) (IsPartition.cell_subset hR i hsi) hts
    exact Finset.disjoint_left.mp (hR.2 i j hij) hsi htj

/-! ### Carrier-preserving properization -/

private lemma section5IndexPoint_mod_order {N : Nat} [NeZero N]
    (P : ModAP N) (i : Nat) :
    section5IndexPoint P (i % addOrderOf P.step) = section5IndexPoint P i := by
  unfold section5IndexPoint
  congr 1
  simpa only [nsmul_eq_mul] using mod_addOrderOf_nsmul P.step i

private lemma section5IndexPoint_injOn_order {N : Nat} [NeZero N]
    (P : ModAP N) :
    Set.InjOn (section5IndexPoint P) (Set.Iio (addOrderOf P.step)) := by
  intro i hi j hj hij
  have hmul : (i : ZMod N) * P.step = (j : ZMod N) * P.step :=
    add_left_cancel hij
  have hnsmul : i • P.step = j • P.step := by
    simpa only [nsmul_eq_mul] using hmul
  have hmod := ((isOfFinAddOrder_of_finite P.step).nsmul_inj_mod).mp hnsmul
  simpa only [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hmod

private lemma section5_carrier_eq_order_range_of_le {N : Nat} [NeZero N]
    (P : ModAP N) (horder : addOrderOf P.step ≤ P.length) :
    P.carrier = (Finset.range (addOrderOf P.step)).image
      (section5IndexPoint P) := by
  rw [section5_carrier_eq_image_range]
  apply Finset.Subset.antisymm
  · intro x hx
    rw [Finset.mem_image] at hx ⊢
    obtain ⟨i, _, rfl⟩ := hx
    refine ⟨i % addOrderOf P.step, ?_, section5IndexPoint_mod_order P i⟩
    exact Finset.mem_range.mpr (Nat.mod_lt _ (addOrderOf_pos P.step))
  · intro x hx
    rw [Finset.mem_image] at hx ⊢
    obtain ⟨i, hi, rfl⟩ := hx
    exact ⟨i, Finset.range_mono horder hi, rfl⟩

/-- Shorten an arbitrary modular progression to one traversal of its carrier. -/
def section5Normalize {N : Nat} (P : ModAP N) : ModAP N :=
  { P with length := P.carrier.card }

theorem section5Normalize_carrier {N : Nat} [NeZero N] (P : ModAP N) :
    (section5Normalize P).carrier = P.carrier := by
  -- the index map is injective below the order `t` of the step, and `P` is the image of
  -- `range (min P.length t)`
  have hinj (n : Nat) (hn : n ≤ addOrderOf P.step) :
      Set.InjOn (section5IndexPoint P) (Finset.range n : Set Nat) := fun i hi j hj =>
    section5IndexPoint_injOn_order P ((Finset.mem_range.mp hi).trans_le hn)
      ((Finset.mem_range.mp hj).trans_le hn)
  rcases le_total P.length (addOrderOf P.step) with h | h
  · have heq : P.carrier.card = P.length := by
      rw [section5_carrier_eq_image_range, Finset.card_image_of_injOn (hinj _ h),
        Finset.card_range]
    simp only [section5Normalize, heq]
  · have heq : P.carrier.card = addOrderOf P.step := by
      rw [section5_carrier_eq_order_range_of_le P h, Finset.card_image_of_injOn (hinj _ le_rfl),
        Finset.card_range]
    rw [section5_carrier_eq_order_range_of_le P h]
    change ({ P with length := P.carrier.card } : ModAP N).carrier = _
    rw [section5_carrier_eq_image_range, heq]
    rfl

theorem section5Normalize_isProper {N : Nat} [NeZero N] (P : ModAP N) :
    (section5Normalize P).IsProper := by
  rw [ModAP.IsProper, section5Normalize_carrier]
  rfl

/-! ### Affine pullback preserves the degree bound -/

theorem polynomialOn_affine_pullback {N k : Nat} [NeZero N]
    (phi : ZMod N → ZMod N) (a d : ZMod N)
    (hphi : PolynomialOn k Finset.univ phi) :
    PolynomialOn k Finset.univ
      (fun x => phi (a + x * d)) := by
  obtain ⟨c, hc⟩ := hphi
  -- `q = p ∘ (d X + a)` with `p = ∑ c_i X^i`, of degree at most `deg p ≤ k`
  set q : Polynomial (ZMod N) :=
    (Polynomial.ofFn (k + 1) c).comp (Polynomial.C d * Polynomial.X + Polynomial.C a) with hq
  have hqdeg : q.natDegree < k + 1 := by
    refine Nat.lt_succ_of_le (Polynomial.natDegree_comp_le.trans ?_)
    simpa using Nat.mul_le_mul (Nat.lt_succ_iff.mp (Polynomial.ofFn_natDegree_lt (by omega) c))
      (Polynomial.natDegree_linear_le (a := d) (b := a))
  refine ⟨fun i => q.coeff i, fun x _ => ?_⟩
  calc phi (a + x * d) = q.eval x := by
        rw [show a + x * d = d * x + a by ring]
        simp [hc, hq, Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum]
    _ = _ := by rw [Polynomial.eval_eq_sum_range' hqdeg, ← Fin.sum_univ_eq_sum_range]

theorem polynomialOn_section5ModIndexPoint {N k : Nat} [NeZero N]
    (P : ModAP N) (phi : ZMod N → ZMod N)
    (hphi : PolynomialOn k Finset.univ phi) :
    PolynomialOn k Finset.univ
      (fun x => phi (section5ModIndexPoint P x)) := by
  simpa only [section5ModIndexPoint] using
    polynomialOn_affine_pullback phi P.start P.step hphi

/-! ### A uniform additive-error version of phase removal -/

attribute [simp] cor57_norm_exponential

attribute [simp] exponential_add

alias downstream_norm_exponential_sub_one_le := cor57_norm_exponential_sub_one_le

alias downstream_phase_close_of_mem_interval := cor57_phase_close_of_mem_interval

private lemma downstream_sum_partition {X R : Type*} [DecidableEq X]
    [AddCommMonoid R] {m : Nat} (P : Fin m → Finset X) (S : Finset X)
    (hpartition : IsPartition P S) (g : X → R) :
    ∑ j, ∑ x ∈ P j, g x = ∑ x ∈ S, g x := by
  have hpair : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint P := by
    intro i _ j _ hij
    exact hpartition.2 i j (bne_iff_ne.mpr hij)
  have hunion : (Finset.univ : Finset (Fin m)).biUnion P = S := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact (hpartition.1 x).symm
  rw [show (∑ j, ∑ x ∈ P j, g x) =
      ∑ j ∈ (Finset.univ : Finset (Fin m)), ∑ x ∈ P j, g x by simp]
  rw [← Finset.sum_biUnion hpair, hunion]

private lemma downstream_scale_le {k r : Nat} (eta : Real)
    (heta : 0 < eta)
    (hlarge :
      (4 * Real.pi / eta) ^ polynomialPartitionConstant k < (r : Real)) :
    (r : Real) ^ (-(polynomialPartitionConstant k : Real)⁻¹) * (1 : Real) ≤
      eta / (4 * Real.pi) := by
  let K := polynomialPartitionConstant k
  have hK : 0 < K := by
    dsimp only [K]
    unfold polynomialPartitionConstant
    positivity
  have hKReal : (0 : Real) < K := by exact_mod_cast hK
  have hr : (0 : Real) < r := by
    have hbase : 0 < 4 * Real.pi / eta := by positivity
    exact (pow_nonneg hbase.le K).trans_lt hlarge
  have hbase : 0 < 4 * Real.pi / eta := by positivity
  have hroot : 4 * Real.pi / eta < (r : Real) ^ (K : Real)⁻¹ := by
    rw [Real.lt_rpow_inv_iff_of_pos hbase.le hr.le hKReal]
    simpa only [Real.rpow_natCast] using hlarge
  have hrootPos : 0 < (r : Real) ^ (K : Real)⁻¹ :=
    Real.rpow_pos_of_pos hr _
  have hinv : ((r : Real) ^ (K : Real)⁻¹)⁻¹ <
      (4 * Real.pi / eta)⁻¹ :=
    (inv_lt_inv₀ hrootPos hbase).2 hroot
  rw [Real.rpow_neg hr.le]
  have hright : (4 * Real.pi / eta)⁻¹ = eta / (4 * Real.pi) := by
    field_simp
  simpa only [K, hright, mul_one] using hinv.le

/-- Retain the diameter information in the local polynomial partition. -/
theorem section5_local_diameter_refinement_of_corollary_5_6
    (h56 : corollary_5_6) {N k v : Nat} [NeZero N]
    (P : ModAP N) (phi : ZMod N → ZMod N) (eta : Real)
    (hP : P.IsProper) (hk : 1 ≤ k)
    (hphi : PolynomialOn k Finset.univ phi) (heta : 0 < eta)
    (hlarge : max (polynomialPartitionThreshold k : Real)
        ((4 * Real.pi / eta) ^ polynomialPartitionConstant k) < P.length)
    (hv : 1 ≤ v)
    (hvupper : (v : Real) ≤
      (P.length : Real) ^ (polynomialPartitionConstant k : Real)⁻¹) :
    ∃ L : Nat, ∃ R : Fin L → ModAP N,
      IsPartition (fun j => (R j).carrier) P.carrier ∧
      (∀ j, (R j).IsProper ∧ 0 < (R j).length ∧
        ((R j).length = v - 1 ∨ (R j).length = v)) ∧
      ∀ j, diameterAtMostReal ((R j).carrier.image phi) (eta * N / (4 * Real.pi)) := by
  have hrN : P.length ≤ N := by
    rw [← (hP : P.carrier.card = P.length)]
    simpa only [ZMod.card] using P.carrier.card_le_univ
  -- Corollary 5.6 for the pullback of `phi` to the indices of `P`, transported back to `P`
  obtain ⟨L, S, _, hpartition, hproper, hdiam⟩ :=
    h56 N k P.length v _ hk (polynomialOn_section5ModIndexPoint P phi hphi)
      (by exact_mod_cast (le_max_left _ _).trans_lt hlarge) hrN hv hvupper
  refine ⟨L, fun j => section5Transport P (S j), section5Transport_partition P S hP hpartition,
    fun j => ⟨section5Transport_isProper P (S j) hP (hproper j).1
      (IsPartition.cell_subset hpartition j), (hproper j).2⟩, fun j => ?_⟩
  obtain ⟨d, hd, hdscale⟩ := hdiam j
  refine ⟨d, ?_, hdscale.trans ?_⟩
  · rw [section5Transport_carrier, Finset.image_image]
    exact hd
  · calc _ ≤ eta / (4 * Real.pi) * N := by
          gcongr
          simpa only [mul_one] using
            downstream_scale_le eta heta ((le_max_right _ _).trans_lt hlarge)
      _ = eta * N / (4 * Real.pi) := by ring

/-- A partition of `P` into cells whose `phi`-images have diameter at most
`η·N/(4π)` changes a disc-valued sum by at most `η/2·|P|` under the phase
`exponential (-phi)`. -/
lemma section5_phase_error_of_diameter {N L : Nat} [NeZero N]
    (P : Finset (ZMod N)) (R : Fin L → Finset (ZMod N)) (phi : ZMod N → ZMod N) (eta : Real)
    (hrefine : IsPartition R P)
    (hdiam : ∀ j, diameterAtMostReal ((R j).image phi) (eta * N / (4 * Real.pi)))
    (f : ZMod N → Complex) (hf : DiscValued f) :
    ‖∑ s ∈ P, f s * exponential (-(phi s))‖ ≤
      (∑ j, ‖∑ s ∈ R j, f s‖) + eta / 2 * P.card := by
  have hcell (j : Fin L) : ‖∑ s ∈ R j, f s * exponential (-(phi s))‖ ≤
      ‖∑ s ∈ R j, f s‖ + eta / 2 * (R j).card := by
    have hinj := (ZMod.val_injective N).injOn (s := ((R j : Finset (ZMod N)) : Set (ZMod N)))
    have key := cor57_cell_norm_le ((R j).image ZMod.val) f phi eta (eta * N / (4 * Real.pi)) hf
      (by simpa only [Finset.image_image, Function.comp_def, ZMod.natCast_zmod_val] using hdiam j)
      le_rfl
    simpa only [Finset.sum_image hinj, Finset.card_image_of_injective _ (ZMod.val_injective N),
      ZMod.natCast_zmod_val] using key
  calc
    ‖∑ s ∈ P, f s * exponential (-(phi s))‖ =
        ‖∑ j, ∑ s ∈ R j, f s * exponential (-(phi s))‖ := by
      rw [downstream_sum_partition R P hrefine]
    _ ≤ ∑ j, ‖∑ s ∈ R j, f s * exponential (-(phi s))‖ := norm_sum_le _ _
    _ ≤ ∑ j, (‖∑ s ∈ R j, f s‖ + eta / 2 * (R j).card) :=
      Finset.sum_le_sum fun j _ => hcell j
    _ = (∑ j, ‖∑ s ∈ R j, f s‖) + eta / 2 * P.card := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Nat.cast_sum, IsPartition.sum_card hrefine]

/-! ### An efficient local refinement with a uniform constant -/

/-- A concrete constant sufficient for the local form of Lemma 5.14. -/
def section5LocalRefinementConstant (k : Nat) (eta : Real) : Real :=
  max
      (max (polynomialPartitionThreshold k : Real)
        ((4 * Real.pi / eta) ^ polynomialPartitionConstant k))
      ((4 : Real) ^ polynomialPartitionConstant k) + 4

theorem section5LocalRefinementConstant_ge_four (k : Nat) (eta : Real) :
    4 ≤ section5LocalRefinementConstant k eta := by
  unfold section5LocalRefinementConstant
  have hthreshold : (0 : Real) ≤ polynomialPartitionThreshold k := by positivity
  have hinner : (0 : Real) ≤ max (polynomialPartitionThreshold k : Real)
      ((4 * Real.pi / eta) ^ polynomialPartitionConstant k) :=
    hthreshold.trans (le_max_left _ _)
  have houter : (0 : Real) ≤ max
      (max (polynomialPartitionThreshold k : Real)
        ((4 * Real.pi / eta) ^ polynomialPartitionConstant k))
      ((4 : Real) ^ polynomialPartitionConstant k) :=
    hinner.trans (le_max_left _ _)
  linarith

theorem section5LocalRefinementConstant_pos (k : Nat) (eta : Real) :
    0 < section5LocalRefinementConstant k eta := by
  exact lt_of_lt_of_le (by norm_num) (section5LocalRefinementConstant_ge_four k eta)

private lemma section5_floor_target (x : Real) (hx : 4 ≤ x) :
    ∃ v : Nat, 2 ≤ v ∧ (v : Real) ≤ x ∧ x / 2 < v := by
  have hfloorFour : 4 ≤ ⌊x⌋₊ :=
    (Nat.le_floor_iff (by positivity)).mpr hx
  refine ⟨⌊x⌋₊, by omega, Nat.floor_le (by positivity), ?_⟩
  · exact Nat.div_two_lt_floor (by linarith)

private lemma section5_rpow_root_ge_four {k r : Nat}
    (hr : (4 : Real) ^ polynomialPartitionConstant k < r) :
    4 < (r : Real) ^ (polynomialPartitionConstant k : Real)⁻¹ := by
  have hK : (0 : Real) < polynomialPartitionConstant k := by
    unfold polynomialPartitionConstant
    positivity
  have hrpos : (0 : Real) < r := by
    exact (pow_nonneg (by norm_num : (0 : Real) ≤ 4)
      (polynomialPartitionConstant k)).trans_lt hr
  rw [Real.lt_rpow_inv_iff_of_pos (by norm_num) hrpos.le hK]
  simpa only [Real.rpow_natCast] using hr

private lemma section5_large_partition_count
    {k r v L : Nat} (hr : 0 < r)
    (hvroot : (r : Real) ^ (polynomialPartitionConstant k : Real)⁻¹ / 2 < v)
    (hroot4 : 4 ≤ (r : Real) ^
      (polynomialPartitionConstant k : Real)⁻¹)
    (hcards : ∑ _j : Fin L, (v - 1 : Nat) ≤ r) :
    (L : Real) ≤ 4 * (r : Real) ^
      (1 - (polynomialPartitionConstant k : Real)⁻¹) := by
  set root : Real := (r : Real) ^ (polynomialPartitionConstant k : Real)⁻¹ with hroot
  -- every cell has `v - 1 ≥ root / 4` points, and `L (v - 1) ≤ r`
  have hv : 1 ≤ v := by exact_mod_cast (show (1 : Real) ≤ v by linarith)
  have hvminus : root / 4 ≤ ((v - 1 : Nat) : Real) := by
    rw [Nat.cast_sub hv, Nat.cast_one]
    linarith
  have hcardsReal : (L : Real) * (v - 1 : Nat) ≤ r := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hcards
    exact_mod_cast hcards
  rw [Real.rpow_sub (by exact_mod_cast hr), Real.rpow_one, ← hroot, mul_div_assoc',
    le_div_iff₀ (by linarith)]
  linarith [mul_le_mul_of_nonneg_left hvminus (Nat.cast_nonneg L)]

/-- Efficient geometric refinement, retaining the same count constant as phase removal. -/
theorem section5_efficient_diameter_refinement_of_corollary_5_6
    (h56 : corollary_5_6) {N k : Nat} [NeZero N]
    (P : ModAP N) (phi : ZMod N → ZMod N) (eta : Real)
    (hP : P.IsProper) (hk : 1 ≤ k)
    (hphi : PolynomialOn k Finset.univ phi) (heta : 0 < eta) :
    ∃ L : Nat, ∃ R : Fin L → ModAP N,
      IsPartition (fun j => (R j).carrier) P.carrier ∧
      (∀ j, (R j).IsProper) ∧
      (L : Real) ≤ section5LocalRefinementConstant k eta *
        (P.carrier.card : Real) ^
          (1 - (polynomialPartitionConstant k : Real)⁻¹) ∧
      ∀ j, diameterAtMostReal ((R j).carrier.image phi) (eta * N / (4 * Real.pi)) := by
  rw [show P.carrier.card = P.length from hP]
  have hC := section5LocalRefinementConstant_ge_four k eta
  by_cases hlarge : max (max (polynomialPartitionThreshold k : Real)
      ((4 * Real.pi / eta) ^ polynomialPartitionConstant k))
      ((4 : Real) ^ polynomialPartitionConstant k) < P.length
  · -- a long progression: Corollary 5.6 with the target length `v = ⌊|P|^(1/K)⌋ ≥ 4`
    have hroot4 := section5_rpow_root_ge_four ((le_max_right _ _).trans_lt hlarge)
    have hr : 0 < P.length := Nat.cast_pos.mp (lt_of_le_of_lt (by positivity)
      ((le_max_right _ _).trans_lt hlarge))
    obtain ⟨v, hvTwo, hvupper, hvhalf⟩ := section5_floor_target _ hroot4.le
    obtain ⟨L, R, hrefine, hproper, hdiam⟩ := section5_local_diameter_refinement_of_corollary_5_6
      (v := v) h56 P phi eta hP hk hphi heta ((le_max_left _ _).trans_lt hlarge) (by omega)
      hvupper
    have hsum : ∑ _j : Fin L, (v - 1 : Nat) ≤ P.length := by
      rw [← (hP : P.carrier.card = P.length), ← IsPartition.sum_card hrefine]
      exact Finset.sum_le_sum fun j _ => by
        have h1 : (R j).carrier.card = (R j).length := (hproper j).1
        rcases (hproper j).2.2 with h | h <;> omega
    exact ⟨L, R, hrefine, fun j => (hproper j).1,
      (section5_large_partition_count hr hvhalf hroot4.le hsum).trans
        (mul_le_mul_of_nonneg_right hC (by positivity)), hdiam⟩
  -- a short progression: its singletons, at most `|P| ≤ C ≤ C |P|^(1 - 1/K)` of them
  have hS := singletonNatAP_partition P.length
  refine ⟨P.length, fun i => section5Transport P (singletonNatAP i),
    section5Transport_partition P _ hP hS, fun j => section5Transport_isProper P _ hP
      (singletonNatAP_isProper j) (IsPartition.cell_subset hS j), ?_, fun j => ?_⟩
  · have hn : (P.length : Real) ≤ section5LocalRefinementConstant k eta := by
      unfold section5LocalRefinementConstant
      linarith [le_of_not_gt hlarge]
    rcases Nat.eq_zero_or_pos P.length with h0 | hr
    · rw [h0, Nat.cast_zero]
      positivity
    have hK : 1 ≤ polynomialPartitionConstant k :=
      Nat.one_le_iff_ne_zero.mpr (by unfold polynomialPartitionConstant; positivity)
    exact hn.trans (le_mul_of_one_le_right (by linarith) (Real.one_le_rpow
      (by exact_mod_cast hr) (sub_nonneg.mpr (inv_le_one_of_one_le₀ (by exact_mod_cast hK)))))
  · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp
      (rfl : (section5Transport P (singletonNatAP j)).carrier.card = 1)
    rw [hx, Finset.image_singleton]
    exact ⟨0, ⟨phi x, by simp [modInterval, ModAP.carrier]⟩, by rw [Nat.cast_zero]; positivity⟩

/-!
Every proper modular progression admits a phase-removing refinement with a
cell-count constant depending only on `k` and the uniform error tolerance.
This is the local quantitative engine of Lemma 5.14.
-/
theorem section5_efficient_local_phase_refinement_of_corollary_5_6
    (h56 : corollary_5_6) {N k : Nat} [NeZero N]
    (P : ModAP N) (phi : ZMod N → ZMod N) (eta : Real)
    (hP : P.IsProper) (hk : 1 ≤ k)
    (hphi : PolynomialOn k Finset.univ phi) (heta : 0 < eta) :
    ∃ L : Nat, ∃ R : Fin L → ModAP N,
      IsPartition (fun j => (R j).carrier) P.carrier ∧
      (∀ j, (R j).IsProper) ∧
      (L : Real) ≤ section5LocalRefinementConstant k eta *
        (P.carrier.card : Real) ^
          (1 - (polynomialPartitionConstant k : Real)⁻¹) ∧
      ∀ f : ZMod N → Complex, DiscValued f →
        ‖∑ s ∈ P.carrier, f s * exponential (-(phi s))‖ ≤
          (∑ j, ‖∑ s ∈ (R j).carrier, f s‖) +
            eta / 2 * P.carrier.card := by
  obtain ⟨L, R, hrefine, hproper, hcount, hdiam⟩ :=
    section5_efficient_diameter_refinement_of_corollary_5_6 h56 P phi eta hP hk hphi heta
  exact ⟨L, R, hrefine, hproper, hcount,
    section5_phase_error_of_diameter P.carrier _ phi eta hrefine hdiam⟩

/-- The efficient local refinement for an arbitrary (possibly wrapping or
repeating) input progression, obtained by carrier-preserving normalization. -/
theorem section5_efficient_local_phase_refinement_arbitrary_of_corollary_5_6
    (h56 : corollary_5_6) {N k : Nat} [NeZero N]
    (P : ModAP N) (phi : ZMod N → ZMod N) (eta : Real)
    (hk : 1 ≤ k) (hphi : PolynomialOn k Finset.univ phi) (heta : 0 < eta) :
    ∃ L : Nat, ∃ R : Fin L → ModAP N,
      IsPartition (fun j => (R j).carrier) P.carrier ∧
      (∀ j, (R j).IsProper) ∧
      (L : Real) ≤ section5LocalRefinementConstant k eta *
        (P.carrier.card : Real) ^
          (1 - (polynomialPartitionConstant k : Real)⁻¹) ∧
      ∀ f : ZMod N → Complex, DiscValued f →
        ‖∑ s ∈ P.carrier, f s * exponential (-(phi s))‖ ≤
          (∑ j, ‖∑ s ∈ (R j).carrier, f s‖) +
            eta / 2 * P.carrier.card := by
  obtain ⟨L, R, hrefine, hproper, hcount, herror⟩ :=
    section5_efficient_local_phase_refinement_of_corollary_5_6 h56
      (section5Normalize P) phi eta (section5Normalize_isProper P)
      hk hphi heta
  refine ⟨L, R, ?_, hproper, ?_, ?_⟩
  · simpa only [section5Normalize_carrier] using hrefine
  · simpa only [section5Normalize_carrier] using hcount
  · simpa only [section5Normalize_carrier] using herror

end LeanProofs.GowersSzemeredi
