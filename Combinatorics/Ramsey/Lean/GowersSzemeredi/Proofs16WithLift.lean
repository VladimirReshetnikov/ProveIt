import GowersSzemeredi.Proofs16ShortScale
import GowersSzemeredi.Proofs16FiniteCoverPadding
import GowersSzemeredi.Proofs16SynchronizedCover

/-! The affine lift with an abstract slice provider.

The lift of Lemma 16.10 uses the final-coordinate cross-sections only
through one cover of the union of the `r` sampled slices. The existing
modules obtain it by refining the `r` slice covers one after another, which
makes the width exponent `c(...)^(r*s)`, exponentially small in `r`; since
`r` grows like `1/loss`, the result is not polynomial in the loss.

Here that cover is a hypothesis: a slice provider gives, for every sample of
every size `r`, a `MultiplyLinearWith (Pb r) (Eb r)` cover of the stacked
slices. The assembly (sampling, interpolation, synchronized retiling, all
scales, global flattening) is copied from `Proofs16CompressedSynchronizedCover`
through `Proofs16GlobalLiftParameters` with `(Pb r ε, Eb r ε)` in place of
`(q((r*s)⁻¹*ε,gamma,k)^(r*s), c((r*s)⁻¹*ε,gamma,k)^(r*s))`.
`Section16AllBoxLineCoversWith.explicit_multilinear_cover_with` then combines it
with the generalized Lemma 16.9.

`Section16AllBoxLineCoversWith.explicit_multilinear_cover_with`,
`Section16LineCover.global_affine_lift_rounded_with`,
`Section16LineCover.global_affine_lift_with`, `Section16SliceProvider`,
`section16_local_affine_lift_all_scales_with` and
`section16_local_affine_lift_with` are in `Proofs16WithLiftSide`, outside the
final route. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- The union of the graphs of the sampled final-coordinate cross-sections. -/
def section16StackedSlices {N k r : Nat} [NeZero N] (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N) (sample : Fin r → ZMod N) :
    Finset (Point N k × ZMod N) :=
  section16FinsetUnion (fun i : Fin r =>
    partialGraph (section16FinalCoordinateSection B (sample i))
      (section16FinalCoordinateRestriction phi (sample i)))

/-- The provider's controls have the ranges used by the assembly. -/
def Section16SliceProviderRanges (Pb Eb : Nat → Real → Real) : Prop :=
  ∀ (r : Nat) (ε : Real), 0 < r → 0 < ε → ε ≤ 1 →
    1 ≤ Pb r ε ∧ 0 < Eb r ε ∧ Eb r ε ≤ 1

theorem section16StackedSlices_mem {N k r : Nat} [NeZero N]
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    {sample : Fin r → ZMod N} (h : Point N k) (i : Fin r)
    (hB : appendCoordinate h (sample i) ∈ B) :
    (h, phi (appendCoordinate h (sample i))) ∈ section16StackedSlices B phi sample := by
  unfold section16StackedSlices section16FinsetUnion
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_univ _, ?_⟩
  exact Finset.mem_image.mpr (⟨h, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hB⟩, rfl⟩)

/-- **Synchronized compressed cover for a family.** One cover of a relation
containing all members' sampled slices; each member interpolates its own
candidates; one common good set `F′` inside every member's recovered set. -/
theorem section16_synchronized_compressed_cover_family
    {N k r m v : Nat} [Fact N.Prime] {ι : Type}
    {D F : ι → Finset (Point N (k + 1))}
    {phi : ι → Point N (k + 1) → ZMod N} {sample : ι → Fin r → ZMod N}
    {Pb Eb : Real → Real} {Gs : Finset (Point N k × ZMod N)}
    (ha : ∀ a, Section16SampledOrAnchoredOn (D a) (phi a) (sample a) (F a))
    (hslice : MultiplyLinearWith Pb Eb Gs)
    (hGs : ∀ a h i, appendCoordinate h (sample a i) ∈ D a →
      (h, phi a (appendCoordinate h (sample a i))) ∈ Gs)
    (hr : 0 < r) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hPb : 0 ≤ Pb ε) (hEb : 0 ≤ Eb ε)
    (T : Box N k) (I : ModAP N) (hT : T.IsProper) (hI : I.IsProper)
    (hstep : I.step = T.commonDiff) (u : (ZMod N)ˣ) (hu : I.step = (↑u : ZMod N))
    (hk : 0 < k) (hm : 4 ≤ m) (hmT : m ≤ T.width) (hmI : m ≤ I.length)
    (hv : 1 ≤ v)
    (hvscale : (v : ℝ) ^ 2 + 1 ≤ ((m : ℝ) / 8) ^ (Eb ε))
    (η : ℝ) (F' : Finset (Point N (k + 1))) (hF'c : ∀ a, F' ⊆ F a)
    (hF : F' ⊆ lastProductSet T.carrier I.carrier)
    (hFm : (1 - η) * ((lastProductSet T.carrier I.carrier).card : ℝ) ≤ F'.card) :
    ∃ (p : Nat) (G : Finset (Point N (k + 1))) (L : Nat) (S : Fin L → Box N (k + 1))
      (nu : Fin L → ι × Fin (section16CompressedCandidateCount r p) →
        Point N (k + 1) → ZMod N),
      (p : ℝ) ≤ Pb ε ∧
      G ⊆ F' ∧ (1 - η - ε) * ((lastProductSet T.carrier I.carrier).card : ℝ) ≤ G.card ∧
      IsPartition (fun j => (S j).carrier) (lastProductSet T.carrier I.carrier) ∧
      (∀ j, (S j).IsProper ∧ v - 1 ≤ (S j).width) ∧
      (∀ j c, IsMultilinear (nu j c)) ∧
      ∀ a j z, z ∈ (S j).carrier → z ∈ D a → z ∈ G → ∃ c, phi a z = nu j c z := by
  obtain ⟨p, H, b, P, n, R, mu, hp, hH, hHm, hPpart, _,
      hPaxes, hPstep, hRpart, hRproper, hRwidth, hmu, hc⟩ :=
    hslice.short_parent_cover ε hε hε1 hPb hEb T I hT hI hk hm hmT hmI
  let e := section5NatFlattenEquiv n
  let R' := boxFlatten n R
  have hfit (j : Fin (∑ a, n a)) : v ^ 2 ≤ (R' j).width - 1 := by
    have h : v ^ 2 + 1 ≤ (R' j).width := by
      exact_mod_cast hvscale.trans (hRwidth (e.symm j).1 (e.symm j).2)
    omega
  have hne (j : Fin (∑ a, n a)) : (R' j).carrier.Nonempty :=
    (R' j).carrier_nonempty_of_axis_pos fun a => lt_of_lt_of_le
      (by have := hfit j; have := Nat.one_le_pow 2 v hv; omega) ((R' j).width_le_axis_length a)
  let axis : Fin k := ⟨0, hk⟩
  let parent := fun j : Fin (∑ a, n a) => (P (e.symm j).1).axis axis
  have hparentstep (j : Fin (∑ a, n a)) : (parent j).step = (↑u : ZMod N) := by
    dsimp only [parent]
    rw [(P _).axis_step, hPstep, ← hstep, hu]
  -- every member interpolates its own candidates on every cell
  have hlift (a : ι) (j : Fin (∑ a, n a)) :=
    (ha a).compressed_multilinear_cover hr (H ∩ (R' j).carrier)
      (fun _ => mu (e.symm j).1 (e.symm j).2) (fun _ => hmu _ _) fun h hh i hi _ =>
        hc (e.symm j).1 (e.symm j).2 h (Finset.mem_inter.mp hh).2 (Finset.mem_inter.mp hh).1 _
          (hGs a h i hi)
  choose nu hnu hcov using hlift
  let G := F' ∩ lastProductSet H I.carrier
  have hprod := lastProductSet_good_mass T.carrier H I.carrier ε hH hHm
  have hcover : ∀ a j z, section16Init z ∈ (R' j).carrier → z ∈ D a →
      z ∈ (fun _ : ι => G) a → ∃ c : ι × _, phi a z = nu c.1 j c.2 z := by
    intro a j z hzR hzD hzG
    obtain ⟨hzF, hzH⟩ := Finset.mem_inter.mp hzG
    rw [← appendCoordinate_init_last z] at hzD hzF ⊢
    obtain ⟨ij, hij⟩ := hcov a j _ (Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hzH).2.1, hzR⟩)
      _ hzD (hF'c a hzF)
    exact ⟨(a, ij), hij⟩
  obtain ⟨L, S, nu', hSpart, hSproper, hnu', hc'⟩ := section16_synchronize_base_cover_family
    T I hI R' (boxFlatten_partition T P n R hPpart hRpart) (fun j => hRproper _ _) parent axis
    (fun _ => u) hparentstep (fun j => by rw [hparentstep, hu])
    (fun j => (R' j).axis_carrier_subset_of_carrier_subset (P (e.symm j).1) (hne j)
      (IsPartition.cell_subset (hRpart (e.symm j).1) (e.symm j).2) axis)
    (fun j => (hPaxes (e.symm j).1 axis).2.1) (fun j => (hPaxes (e.symm j).1 axis).2.2) hv hfit
    D (fun _ => G) phi (fun j (c : ι × _) => nu c.1 j c.2) (fun j (c : ι × _) => hnu c.1 j c.2)
    hcover
  exact ⟨p, G, L, S, nu', hp, Finset.inter_subset_left, good_intersection_mass _ F' _ η ε hF
    hprod.1 hFm hprod.2, hSpart, hSproper, hnu', hc'⟩

/-- Finitely many good sets inside one set lose at most the sum of their
losses. -/
theorem good_finite_intersection_mass {α : Type*} [DecidableEq α] {ι : Type} [Fintype ι]
    (P : Finset α) (F : ι → Finset α) (t : Real)
    (hF : ∀ a, F a ⊆ P) (hFm : ∀ a, (1 - t) * (P.card : Real) ≤ (F a).card) :
    (P.filter fun z => ∀ a, z ∈ F a) ⊆ P ∧
      (1 - Fintype.card ι * t) * (P.card : Real) ≤ (P.filter fun z => ∀ a, z ∈ F a).card := by
  set X := P.filter fun z => ∀ a, z ∈ F a
  have hXP : X ⊆ P := Finset.filter_subset _ _
  refine ⟨hXP, ?_⟩
  have hsd : P \ X ⊆ Finset.univ.biUnion (fun a => P \ F a) := fun z hz => by
    obtain ⟨hzP, hzX⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨a, ha⟩ := not_forall.mp
      (fun h => hzX (Finset.mem_filter.mpr ⟨hzP, h⟩) : ¬ ∀ a, z ∈ F a)
    exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨hzP, ha⟩⟩
  have h1 : ((P \ X).card : Real) ≤ ∑ a, ((P \ F a).card : Real) := by
    exact_mod_cast (Finset.card_le_card hsd).trans Finset.card_biUnion_le
  have hcard (Y : Finset α) (hY : Y ⊆ P) : ((P \ Y).card : Real) + Y.card = P.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hY
  have h2 : ∑ a, ((P \ F a).card : Real) ≤ ∑ _a : ι, t * (P.card : Real) :=
    Finset.sum_le_sum fun a _ => by linarith [hFm a, hcard _ (hF a)]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
  linarith [hcard X hXP]

/-- **The local affine lift for a family.** -/
theorem section16_local_affine_lift_family {N k q r m v : Nat} [Fact N.Prime]
    {ι : Type} [Fintype ι]
    (P : Box N (k + 1)) (hP : P.IsProper) (hk : 0 < k)
    (hm : 4 ≤ m) (hmP : m ≤ P.width)
    (D : ι → Finset (Point N (k + 1))) (phi : ι → Point N (k + 1) → ZMod N)
    (Pb Eb : Real → Real) (Gs : (ι → Fin r → ZMod N) → Finset (Point N k × ZMod N))
    (hslice : ∀ sample, MultiplyLinearWith Pb Eb (Gs sample))
    (hGs : ∀ sample a h i, appendCoordinate h (sample a i) ∈ D a →
      (h, phi a (appendCoordinate h (sample a i))) ∈ Gs sample)
    (ell : ι → Point N k → Fin q → ZMod N → ZMod N)
    (hell : ∀ a h i, LinearOn Finset.univ (ell a h i))
    (hcover : ∀ a h x, appendCoordinate h x ∈ P.carrier → appendCoordinate h x ∈ D a →
      ∃ i, phi a (appendCoordinate h x) = ell a h i x)
    (τ ε : ℝ) (hq : 0 < q) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hPb : 0 ≤ Pb ε) (hEb : 0 ≤ Eb ε)
    (hr : 6 * (q : ℝ) * ((max 1 (Fintype.card ι) : Nat) : ℝ) ≤ (r : ℝ) * τ) (hv : 1 ≤ v)
    (hvscale : (v : ℝ) ^ 2 + 1 ≤ ((m : ℝ) / 8) ^ (Eb ε)) :
    ∃ (p : Nat) (G : Finset (Point N (k + 1))) (L : Nat) (S : Fin L → Box N (k + 1))
      (nu : Fin L → ι × Fin (section16CompressedCandidateCount r p) →
        Point N (k + 1) → ZMod N),
      (p : ℝ) ≤ Pb ε ∧
      G ⊆ P.carrier ∧ (1 - 2 * τ - ε) * (P.carrier.card : ℝ) ≤ G.card ∧
      IsBoxPartition S P ∧ (∀ j, (S j).IsProper ∧ v - 1 ≤ (S j).width) ∧
      (∀ j c, IsMultilinear (nu j c)) ∧
      ∀ a j z, z ∈ (S j).carrier → z ∈ D a → z ∈ G → ∃ c, phi a z = nu j c z := by
  let T := boxInit P
  let I := P.axis (Fin.last k)
  have hI : I.IsProper := hP (Fin.last k)
  have hmI : m ≤ I.length := hmP.trans (P.width_le_axis_length (Fin.last k))
  have hprod : IsLastCoordinateBoxProduct P T I := boxInit_last_product P
  have hcarrier : P.carrier = lastProductSet T.carrier I.carrier := hprod.1
  obtain ⟨u, hu⟩ := I.step_isUnit_of_prime hI (by omega)
  -- each member's recovered set, at the loss `τ' = τ / max 1 |ι|`
  set Mι : Nat := max 1 (Fintype.card ι)
  have hMpos : (0 : ℝ) < Mι := by positivity
  have hcardM : (Fintype.card ι : ℝ) ≤ Mι := by exact_mod_cast le_max_right 1 (Fintype.card ι)
  set τ' := τ / Mι with hτ'def
  have hτ' : 0 < τ' := div_pos hτ hMpos
  have hr' : 6 * (q : ℝ) ≤ (r : ℝ) * τ' := by
    rw [hτ'def, mul_div_assoc', le_div_iff₀ hMpos]
    linarith
  have hrpos : 0 < r :=
    Nat.cast_pos.mp (by nlinarith [(by exact_mod_cast hq : (0 : ℝ) < q)] : (0 : ℝ) < r)
  choose sample F _ hF hFm ha using fun a =>
    section16_box_recovered_good_set P T I hprod
      (Finset.card_pos.mp (by rw [show I.carrier.card = I.length from hI]; omega))
      (D a) (phi a) (ell a) (fun h _ i => hell a h i) (fun h hh x hx hz =>
        hcover a h x (by rw [appendCoordinate_eq_snoc]; exact (hprod.mem_snoc h x).mpr ⟨hh, hx⟩)
          hz) τ' hq hτ' (div_le_one_of_le₀ (hτ1.trans (by exact_mod_cast le_max_left 1 _))
            hMpos.le) hr'
  -- their common part loses at most `|ι|·2τ' ≤ 2τ`
  obtain ⟨hF'sub, hF'm⟩ := good_finite_intersection_mass P.carrier F (2 * τ') hF hFm
  set F' := P.carrier.filter fun z => ∀ a, z ∈ F a
  have hloss : (Fintype.card ι : ℝ) * (2 * τ') ≤ 2 * τ :=
    calc (Fintype.card ι : ℝ) * (2 * τ') = 2 * τ * (Fintype.card ι / Mι) := by rw [hτ'def]; ring
      _ ≤ 2 * τ * 1 := by gcongr; exact div_le_one_of_le₀ hcardM hMpos.le
      _ = 2 * τ := mul_one _
  have hF'm2 : (1 - 2 * τ) * (P.carrier.card : ℝ) ≤ F'.card := by
    linarith [mul_le_mul_of_nonneg_right hloss (Nat.cast_nonneg (α := ℝ) P.carrier.card)]
  obtain ⟨p, G, L, S, nu, hp, hG, hGm, hSpart, hSproper, hnu, hc⟩ :=
    section16_synchronized_compressed_cover_family ha (hslice sample) (hGs sample) hrpos
      ε hε hε1 hPb hEb T I (boxInit_isProper P hP) hI (P.axis_step (Fin.last k)) u hu.symm hk hm
      (hmP.trans (boxInit_width P hk)) hmI hv hvscale (2 * τ) F'
      (fun a z hz => (Finset.mem_filter.mp hz).2 a) (hcarrier ▸ hF'sub) (hcarrier ▸ hF'm2)
  refine ⟨p, G, L, S, nu, hp, hG.trans hF'sub, by simpa only [← hcarrier] using hGm, ?_,
    hSproper, hnu, hc⟩
  rw [IsBoxPartition, hcarrier]
  exact hSpart

/-- **The family local lift at every scale.** -/
theorem section16_local_affine_lift_all_scales_family {N k q r m : Nat} [Fact N.Prime]
    {ι : Type} [Fintype ι]
    (P : Box N (k + 1)) (hP : P.IsProper) (hk : 0 < k) (hmP : m ≤ P.width)
    (D : ι → Finset (Point N (k + 1))) (phi : ι → Point N (k + 1) → ZMod N)
    (Pb Eb : Real → Real) (Gs : (ι → Fin r → ZMod N) → Finset (Point N k × ZMod N))
    (hslice : ∀ sample, MultiplyLinearWith Pb Eb (Gs sample))
    (hGs : ∀ sample a h i, appendCoordinate h (sample a i) ∈ D a →
      (h, phi a (appendCoordinate h (sample a i))) ∈ Gs sample)
    (ell : ι → Point N k → Fin q → ZMod N → ZMod N)
    (hell : ∀ a h i, LinearOn Finset.univ (ell a h i))
    (hcover : ∀ a h x, appendCoordinate h x ∈ P.carrier → appendCoordinate h x ∈ D a →
      ∃ i, phi a (appendCoordinate h x) = ell a h i x)
    (τ ε : ℝ) (hq : 0 < q) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hPb : 1 ≤ Pb ε) (hEb : 0 < Eb ε) (_hEb1 : Eb ε ≤ 1)
    (hr : 6 * (q : ℝ) * ((max 1 (Fintype.card ι) : Nat) : ℝ) ≤ (r : ℝ) * τ) :
    ∃ (p : Nat) (G : Finset (Point N (k + 1))) (L : Nat) (S : Fin L → Box N (k + 1))
      (nu : Fin L → ι × Fin (section16CompressedCandidateCount r p) →
        Point N (k + 1) → ZMod N),
      (p : ℝ) ≤ Pb ε ∧
      G ⊆ P.carrier ∧ (1 - 2 * τ - ε) * (P.carrier.card : ℝ) ≤ G.card ∧
      IsBoxPartition S P ∧
      (∀ j, (S j).IsProper ∧ Real.sqrt (((m : ℝ) / 8) ^ (Eb ε)) / 4 ≤ (S j).width) ∧
      (∀ j c, IsMultilinear (nu j c)) ∧
      ∀ a j z, z ∈ (S j).carrier → z ∈ D a → z ∈ G → ∃ c, phi a z = nu j c z := by
  let w := ((m : ℝ) / 8) ^ (Eb ε)
  by_cases hw : 16 ≤ w
  · have hm : 4 ≤ m := by
      by_contra hm
      have hw1 : w ≤ 1 := Real.rpow_le_one (by positivity)
        (by rw [div_le_one (by norm_num)]; exact_mod_cast (by omega : m ≤ 8)) hEb.le
      linarith
    obtain ⟨v, hv, hvscale, hvwidth⟩ := section16_lift_width_rounding hw
    obtain ⟨p, G, L, S, nu, hp, hG, hGm, hpart, hproper, hnu, hc⟩ :=
      section16_local_affine_lift_family P hP hk hm hmP D phi Pb Eb Gs hslice hGs
        ell hell hcover τ ε hq hτ hτ1 hε hε1 (by linarith) hEb.le hr hv hvscale
    exact ⟨p, G, L, S, nu, hp, hG, hGm, hpart,
      fun j => ⟨(hproper j).1, hvwidth.trans (by exact_mod_cast (hproper j).2)⟩, hnu, hc⟩
  · -- below the threshold, single points
    have hw0 : 0 ≤ w := Real.rpow_nonneg (by positivity) _
    have hwidth : Real.sqrt w / 4 ≤ 1 := by
      nlinarith [Real.sq_sqrt hw0, Real.sqrt_nonneg w, not_le.mp hw]
    obtain ⟨L, x, hpart⟩ := box_singleton_partition P
    refine ⟨1, P.carrier, L, fun j => pointSingletonBox (x j),
      fun j c _ => phi c.1 (x j), by simpa using hPb, Finset.Subset.rfl,
      mul_le_of_le_one_left (Nat.cast_nonneg _) (by linarith), hpart,
      fun j => ⟨pointSingletonBox_isProper _, by
        simpa only [pointSingletonBox_width (by omega : 0 < k + 1), Nat.cast_one] using hwidth⟩,
      fun j _ => isMultilinear_constant _, fun a j z hz _ _ => ?_⟩
    obtain rfl : z = x j := by simpa only [pointSingletonBox_carrier, Finset.mem_singleton] using hz
    exact ⟨(a, ⟨0, by unfold section16CompressedCandidateCount; omega⟩), rfl⟩

/-- The line-cover conclusion of Lemma 16.9 for a family: one partition,
and per-member lines on every cell. -/
def Section16LineCoverFamily {N k : Nat} [NeZero N] {ι : Type}
    (P : Box N (k + 1)) (B1 : ι → Finset (Point N (k + 1)))
    (phi1 : ι → Point N (k + 1) → ZMod N)
    (sigma l : Real) (q : Nat) : Prop :=
  ∃ E : Finset (Point N (k + 1)), ∃ M : Nat,
    ∃ S : Fin M → Box N (k + 1),
      ∃ T : Fin M → Box N k, ∃ A : Fin M → ModAP N,
        ∃ ell : ι → Fin M → Point N k → Fin q → ZMod N → ZMod N,
          E ⊆ P.carrier ∧ (1 - sigma) * P.carrier.card ≤ E.card ∧
          IsBoxPartition S P ∧ (∀ u, (S u).IsProper) ∧
          (∀ u, IsLastCoordinateBoxProduct (S u) (T u) (A u)) ∧
          (∀ u, l ≤ (S u).width) ∧
          (∀ a u h i, LinearOn Finset.univ (ell a u h i)) ∧
          ∀ a u h x, h ∈ (T u).carrier →
            appendCoordinate h x ∈ B1 a → appendCoordinate h x ∈ E →
            appendCoordinate h x ∈ (S u).carrier →
            ∃ i, phi1 a (appendCoordinate h x) = ell a u h i x

/-- **The global affine lift for a family.** -/
theorem Section16LineCoverFamily.global_affine_lift_family {N k q r m : Nat} [Fact N.Prime]
    {ι : Type} [Fintype ι]
    {P : Box N (k + 1)} {B : ι → Finset (Point N (k + 1))}
    {phi : ι → Point N (k + 1) → ZMod N} {σ l : ℝ} {Pb Eb : Real → Real}
    (hline : Section16LineCoverFamily P B phi σ l q)
    (Gs : (ι → Fin r → ZMod N) → Finset (Point N k × ZMod N))
    (hslice : ∀ sample, MultiplyLinearWith Pb Eb (Gs sample))
    (hGs : ∀ sample a h i, appendCoordinate h (sample a i) ∈ B a →
      (h, phi a (appendCoordinate h (sample a i))) ∈ Gs sample)
    (hk : 0 < k) (hm : (m : ℝ) ≤ l) (τ ε : ℝ) (hq : 0 < q)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hPb : 1 ≤ Pb ε) (hEb : 0 < Eb ε) (hEb1 : Eb ε ≤ 1)
    (hr : 6 * (q : ℝ) * ((max 1 (Fintype.card ι) : Nat) : ℝ) ≤ (r : ℝ) * τ) :
    ∃ (n : Nat) (H : Finset (Point N (k + 1))) (L : Nat)
      (Q : Fin L → Box N (k + 1)) (mu : Fin L → Fin n → Point N (k + 1) → ZMod N),
      (n : ℝ) ≤ (Fintype.card ι : ℝ) * max (Pb ε) ((r.choose 2 : ℝ) * Pb ε * Pb ε) ∧
      H ⊆ P.carrier ∧ (1 - σ - 2 * τ - ε) * (P.carrier.card : ℝ) ≤ H.card ∧
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
      (∀ j, Real.sqrt (((m : ℝ) / 8) ^ (Eb ε)) / 4 ≤ (Q j).width) ∧
      (∀ j i, IsMultilinear (mu j i)) ∧
      ∀ a j z, z ∈ (Q j).carrier → z ∈ B a → z ∈ H → ∃ i, phi a z = mu j i z := by
  obtain ⟨E, M, S, T, J, ell, hE, hEm, hSpart, hSproper, hproduct, hwidth, hell, hc⟩ := hline
  -- the local lift on every cell `S u`, for the members restricted to `E`
  choose p G L R nu hp hG hGm hRpart hRproper hnu hcov using fun u =>
    section16_local_affine_lift_all_scales_family (S u) (hSproper u) hk
      (by exact_mod_cast hm.trans (hwidth u)) (fun a => B a ∩ E) phi Pb Eb Gs hslice
      (fun sample a h i hi => hGs sample a h i (Finset.mem_inter.mp hi).1)
      (fun a => ell a u) (fun a => hell a u)
      (fun a h x hxS hxD => hc a u h x
        (((hproduct u).mem_snoc h x).mp (appendCoordinate_eq_snoc h x ▸ hxS)).1
        (Finset.mem_inter.mp hxD).1 (Finset.mem_inter.mp hxD).2 hxS)
      τ ε hq hτ hτ1 hε hε1 hPb hEb hEb1 hr
  let n := Fintype.card ι * section16CompressedCandidateCount r ⌊Pb ε⌋₊
  have hpn (u : Fin M) :
      Fintype.card (ι × Fin (section16CompressedCandidateCount r (p u))) ≤ n := by
    rw [Fintype.card_prod, Fintype.card_fin]
    exact Nat.mul_le_mul_left _
      (section16_compressed_candidate_mono (r := r) (Nat.le_floor (hp u)))
  have hgood := IsPartition.good_union hSpart G (2 * τ + ε) hG
    (fun u => by simpa only [sub_add_eq_sub_sub] using hGm u)
  have hmass := good_intersection_mass P.carrier E (Finset.univ.biUnion G)
    σ (2 * τ + ε) hE hgood.1 hEm hgood.2
  let e := section5NatFlattenEquiv L
  refine ⟨n, E ∩ Finset.univ.biUnion G, ∑ u, L u, boxFlatten L R,
    fun j => padFiniteMultilinearFamily (nu (e.symm j).1 (e.symm j).2) n,
    (Nat.cast_mul _ _).trans_le (mul_le_mul_of_nonneg_left (section16_compressed_candidate_bound
      (Nat.floor_le (zero_le_one.trans hPb))) (Nat.cast_nonneg _)),
    Finset.inter_subset_left.trans hE, by simpa only [sub_add_eq_sub_sub] using hmass,
    boxFlatten_partition P S L R hSpart hRpart, fun j => (hRproper _ _).1,
    fun j => (hRproper _ _).2, fun j => padFiniteMultilinearFamily_isMultilinear _ (hnu _ _),
    fun a j z hzQ hzB hzH => ?_⟩
  obtain ⟨hzE, hzG⟩ := Finset.mem_inter.mp hzH
  have hzS := IsPartition.cell_subset (hRpart (e.symm j).1) (e.symm j).2 hzQ
  exact padFiniteMultilinearFamily_covers _ (hpn _) z (phi a z)
    (hcov (e.symm j).1 a (e.symm j).2 z hzQ (Finset.mem_inter.mpr ⟨hzB, hzE⟩)
      ((IsPartition.good_union_mem_iff hSpart G hG (e.symm j).1 hzS).mp hzG))

end LeanProofs.GowersSzemeredi
