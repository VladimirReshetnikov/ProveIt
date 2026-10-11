import GowersSzemeredi.Proofs16WithLift

/-! The affine lift of Lemma 16.10 for a family of functions, on one
partition.

Step (B) of Notes L.3, the third stage. `Proofs16FamilyLemma6` makes the
line covers of all pieces share one partition. Here the lift from line
covers to multilinear covers is done for all members at once:
* every member `a` samples its own slices (`sample a`), but one cover of a
  relation containing all sampled slices of all members serves every
  member (in dimension one such a relation is a stacked Freiman family);
* the per-member sampling losses are `τ/|ι|`, so the common good set loses
  `2τ` in total;
* every member's candidate maps are interpolated on the same cells, and
  the candidate family of a cell is indexed by `ι × (candidates)`.

The constructions are copies of `section16_synchronize_base_cover` and
`Section16SampledOrAnchoredOn.synchronized_compressed_cover_with` through
`Section16LineCover.global_affine_lift_rounded_with`, with every per-point
statement made per member. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- **Synchronized retiling for a family.** The tiling depends only on the
base cells, so it serves every member. -/
theorem section16_synchronize_base_cover_family {N k M v : Nat} [NeZero N] {C ι : Type*}
    (T : Box N k) (I : ModAP N) (hI : I.IsProper)
    (R : Fin M → Box N k) (hRpart : IsBoxPartition R T) (hR : ∀ j, (R j).IsProper)
    (B : Fin M → ModAP N) (axis : Fin k) (u : Fin M → (ZMod N)ˣ)
    (hBstep : ∀ j, (B j).step = (↑(u j) : ZMod N))
    (hIstep : ∀ j, I.step = (B j).step)
    (hsub : ∀ j, ((R j).axis axis).carrier ⊆ (B j).carrier)
    (hshort : ∀ j, 2 * (B j).length ≤ N) (hL : ∀ j, (B j).length ≤ I.length)
    (hv : 1 ≤ v) (hfit : ∀ j, v ^ 2 ≤ (R j).width - 1)
    (D G : ι → Finset (Point N (k + 1))) (phi : ι → Point N (k + 1) → ZMod N)
    (mu : Fin M → C → Point N (k + 1) → ZMod N)
    (hmu : ∀ j c, IsMultilinear (mu j c))
    (hcover : ∀ a j z, section16Init z ∈ (R j).carrier → z ∈ D a → z ∈ G a →
      ∃ c, phi a z = mu j c z) :
    ∃ (L : Nat) (S : Fin L → Box N (k + 1))
      (nu : Fin L → C → Point N (k + 1) → ZMod N),
      IsPartition (fun j => (S j).carrier) (lastProductSet T.carrier I.carrier) ∧
      (∀ j, (S j).IsProper ∧ v - 1 ≤ (S j).width) ∧
      (∀ j c, IsMultilinear (nu j c)) ∧
      ∀ a j z, z ∈ (S j).carrier → z ∈ D a → z ∈ G a → ∃ c, phi a z = nu j c z := by
  classical
  choose L S J hSpart hSproper hSproduct hJlength using fun j =>
    box_product_tiling_of_contained_axis (R j) (B j) I axis (u j)
      (hR j) hI (hBstep j) (hIstep j) (hsub j) (hshort j) (hL j) hv (hfit j)
  let e := section5NatFlattenEquiv L
  refine ⟨∑ j, L j, boxFlatten L S, fun j => mu (e.symm j).1,
    finsetPartition_flatten L (fun j => lastProductSet (R j).carrier I.carrier)
      (lastProductSet T.carrier I.carrier) (fun j a => (S j a).carrier)
      (lastProductSet_partition _ _ _ hRpart) hSpart,
    fun j => hSproper _ _, fun j c => hmu _ c, ?_⟩
  intro a j z hz hD hG
  have hp := (hSproduct (e.symm j).1 (e.symm j).2).1
  change z ∈ (S (e.symm j).1 (e.symm j).2).carrier at hz
  rw [hp] at hz
  exact hcover a _ z (Finset.mem_filter.mp hz).2.1 hD hG

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
  classical
  obtain ⟨p, H, b, P, n, R, mu, hp, hH, hHm, hPpart, hPproper,
      hPaxes, hPstep, hRpart, hRproper, hRwidth, hmu, hc⟩ :=
    hslice.short_parent_cover ε hε hε1 hPb hEb T I hT hI hk hm hmT hmI
  let e := section5NatFlattenEquiv n
  let R' := boxFlatten n R
  have hR'part : IsBoxPartition R' T := boxFlatten_partition T P n R hPpart hRpart
  have hfit (j : Fin (∑ a, n a)) : v ^ 2 ≤ (R' j).width - 1 := by
    have h := hvscale.trans (hRwidth (e.symm j).1 (e.symm j).2)
    have h' : v ^ 2 + 1 ≤ (R' j).width := by exact_mod_cast h
    omega
  have hne (j : Fin (∑ a, n a)) : (R' j).carrier.Nonempty := by
    apply Box.carrier_nonempty_of_axis_pos
    intro a
    have hw := (R' j).width_le_axis_length a
    have hf := hfit j
    have hv2 : 1 ≤ v ^ 2 := by nlinarith
    omega
  let axis : Fin k := ⟨0, hk⟩
  let parent := fun j : Fin (∑ a, n a) => (P (e.symm j).1).axis axis
  have hsub (j : Fin (∑ a, n a)) : ((R' j).axis axis).carrier ⊆ (parent j).carrier :=
    (R' j).axis_carrier_subset_of_carrier_subset (P (e.symm j).1) (hne j)
      (IsPartition.cell_subset (hRpart (e.symm j).1) (e.symm j).2) axis
  have hparentstep (j : Fin (∑ a, n a)) : (parent j).step = (↑u : ZMod N) := by
    dsimp only [parent]
    rw [(P _).axis_step, hPstep, ← hstep, hu]
  have hparallel (j : Fin (∑ a, n a)) : I.step = (parent j).step := by
    rw [hparentstep, hu]
  have hlift : ∀ (a : ι) (j : Fin (∑ a, n a)),
      ∃ nu : Fin (section16CompressedCandidateCount r p) → Point N (k + 1) → ZMod N,
        (∀ ij, IsMultilinear (nu ij)) ∧
        ∀ h ∈ H ∩ (R' j).carrier, ∀ x, appendCoordinate h x ∈ D a →
          appendCoordinate h x ∈ F a →
            ∃ ij, phi a (appendCoordinate h x) = nu ij (appendCoordinate h x) := by
    intro a j
    apply (ha a).compressed_multilinear_cover hr (H ∩ (R' j).carrier)
      (fun _ => mu (e.symm j).1 (e.symm j).2) (fun _ => hmu _ _)
    intro h hh i hi _
    obtain ⟨hhH, hhR⟩ := Finset.mem_inter.mp hh
    exact hc (e.symm j).1 (e.symm j).2 h hhR hhH (phi a (appendCoordinate h (sample a i)))
      (hGs a h i hi)
  choose nu hnu hcov using hlift
  let G := F' ∩ lastProductSet H I.carrier
  have hprod := lastProductSet_good_mass T.carrier H I.carrier ε hH hHm
  have hGmass := good_intersection_mass (lastProductSet T.carrier I.carrier) F'
    (lastProductSet H I.carrier) η ε hF hprod.1 hFm hprod.2
  let nuAll : Fin (∑ a, n a) → ι × Fin (section16CompressedCandidateCount r p) →
      Point N (k + 1) → ZMod N := fun j c => nu c.1 j c.2
  have hcover : ∀ a j z, section16Init z ∈ (R' j).carrier → z ∈ D a →
      z ∈ (fun _ : ι => G) a → ∃ c, phi a z = nuAll j c z := by
    intro a j z hzR hzD hzG
    obtain ⟨hzF, hzH⟩ := Finset.mem_inter.mp hzG
    have hhH := (Finset.mem_filter.mp hzH).2.1
    have hd : appendCoordinate (section16Init z) (section16Last z) ∈ D a := by
      simpa only [appendCoordinate_init_last] using hzD
    have hf : appendCoordinate (section16Init z) (section16Last z) ∈ F a := by
      simpa only [appendCoordinate_init_last] using hF'c a hzF
    obtain ⟨ij, hij⟩ := hcov a j (section16Init z)
      (Finset.mem_inter.mpr ⟨hhH, hzR⟩) (section16Last z) hd hf
    refine ⟨(a, ij), ?_⟩
    simpa only [appendCoordinate_init_last] using hij
  obtain ⟨L, S, nu', hSpart, hSproper, hnu', hc'⟩ := section16_synchronize_base_cover_family
    T I hI R' hR'part (fun j => hRproper _ _) parent axis (fun _ => u)
    hparentstep hparallel hsub (fun j => (hPaxes (e.symm j).1 axis).2.1)
    (fun j => (hPaxes (e.symm j).1 axis).2.2) hv hfit D (fun _ => G) phi nuAll
    (fun j c => hnu c.1 j c.2) hcover
  exact ⟨p, G, L, S, nu', hp, Finset.inter_subset_left, hGmass, hSpart, hSproper, hnu',
    fun a j z hz hzD hzG => hc' a j z hz hzD hzG⟩


/-- Finitely many good sets inside one set lose at most the sum of their
losses. -/
theorem good_finite_intersection_mass {α : Type*} [DecidableEq α] {ι : Type} [Fintype ι]
    (P : Finset α) (F : ι → Finset α) (t : Real)
    (hF : ∀ a, F a ⊆ P) (hFm : ∀ a, (1 - t) * (P.card : Real) ≤ (F a).card) :
    (P.filter fun z => ∀ a, z ∈ F a) ⊆ P ∧
      (1 - Fintype.card ι * t) * (P.card : Real) ≤ (P.filter fun z => ∀ a, z ∈ F a).card := by
  classical
  set X := P.filter fun z => ∀ a, z ∈ F a with hX
  have hXP : X ⊆ P := Finset.filter_subset _ _
  refine ⟨hXP, ?_⟩
  have hsd : P \ X ⊆ Finset.univ.biUnion (fun a => P \ F a) := by
    intro z hz
    obtain ⟨hzP, hzX⟩ := Finset.mem_sdiff.mp hz
    have hn : ¬ ∀ a, z ∈ F a := fun h => hzX (Finset.mem_filter.mpr ⟨hzP, h⟩)
    obtain ⟨a, ha⟩ := not_forall.mp hn
    exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨hzP, ha⟩⟩
  have h1 : ((P \ X).card : Real) ≤ ∑ a, ((P \ F a).card : Real) := by
    have h := (Finset.card_le_card hsd).trans Finset.card_biUnion_le
    exact_mod_cast h
  have h2 : ∀ a, ((P \ F a).card : Real) ≤ t * P.card := by
    intro a
    have hs : ((P \ F a).card : Real) + (F a).card = P.card := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card (hF a)
    linarith [hFm a]
  have h3 : ∑ a, ((P \ F a).card : Real) ≤ Fintype.card ι * (t * P.card) := by
    calc ∑ a, ((P \ F a).card : Real) ≤ ∑ _a : ι, t * (P.card : Real) :=
          Finset.sum_le_sum fun a _ => h2 a
      _ = Fintype.card ι * (t * P.card) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hX' : ((P \ X).card : Real) + X.card = P.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hXP
  nlinarith

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
  classical
  let T := boxInit P
  let I := P.axis (Fin.last k)
  have hT : T.IsProper := boxInit_isProper P hP
  have hI : I.IsProper := hP (Fin.last k)
  have hmT : m ≤ T.width := hmP.trans (boxInit_width P hk)
  have hmI : m ≤ I.length := hmP.trans (P.width_le_axis_length (Fin.last k))
  have hInonempty : I.carrier.Nonempty := by
    apply Finset.card_pos.mp
    rw [show I.carrier.card = I.length from hI]
    omega
  have hprod : IsLastCoordinateBoxProduct P T I := boxInit_last_product P
  have hcarrier : P.carrier = lastProductSet T.carrier I.carrier := hprod.1
  obtain ⟨u, hu⟩ := I.step_isUnit_of_prime hI (by omega)
  have hstep : I.step = T.commonDiff := P.axis_step (Fin.last k)
  set Mι : Nat := max 1 (Fintype.card ι) with hMι
  have hMpos : (0 : ℝ) < Mι := by
    have : 0 < Mι := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
    exact_mod_cast this
  have hM1 : (1 : ℝ) ≤ Mι := by
    have : 1 ≤ Mι := le_max_left _ _
    exact_mod_cast this
  have hcardM : (Fintype.card ι : ℝ) ≤ Mι := by
    have : Fintype.card ι ≤ Mι := le_max_right _ _
    exact_mod_cast this
  set τ' := τ / Mι with hτ'def
  have hτ' : 0 < τ' := div_pos hτ hMpos
  have hτ'1 : τ' ≤ 1 := by
    rw [hτ'def, div_le_one hMpos]; linarith
  have hr' : 6 * (q : ℝ) ≤ (r : ℝ) * τ' := by
    rw [hτ'def, mul_div_assoc', le_div_iff₀ hMpos]
    linarith
  have hrpos : 0 < r := by
    by_contra hz
    have hz' : r = 0 := by omega
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    simp only [hz', Nat.cast_zero, zero_mul] at hr'
    linarith
  have hrec : ∀ a : ι, ∃ (sample : Fin r → ZMod N) (F : Finset (Point N (k + 1))),
      (∀ i, sample i ∈ I.carrier) ∧ F ⊆ P.carrier ∧
      (1 - 2 * τ') * (P.carrier.card : ℝ) ≤ F.card ∧
      Section16SampledOrAnchoredOn (D a) (phi a) sample F := fun a =>
    section16_box_recovered_good_set P T I hprod hInonempty (D a) (phi a) (ell a)
      (fun h _ i => hell a h i) (fun h hh x hx hz =>
        hcover a h x (by
          rw [appendCoordinate_eq_snoc]
          exact (hprod.mem_snoc h x).mpr ⟨hh, hx⟩) hz) τ' hq hτ' hτ'1 hr'
  choose sample F _ hF hFm ha using hrec
  obtain ⟨hF'sub, hF'm⟩ := good_finite_intersection_mass P.carrier F (2 * τ') hF hFm
  set F' := P.carrier.filter fun z => ∀ a, z ∈ F a with hF'def
  have hF'c : ∀ a, F' ⊆ F a := fun a z hz => (Finset.mem_filter.mp hz).2 a
  have hloss : (Fintype.card ι : ℝ) * (2 * τ') ≤ 2 * τ := by
    rw [hτ'def]
    have h1 : (Fintype.card ι : ℝ) * (2 * (τ / Mι)) = 2 * τ * ((Fintype.card ι : ℝ) / Mι) := by
      ring
    rw [h1]
    have h2 : (Fintype.card ι : ℝ) / Mι ≤ 1 := (div_le_one hMpos).mpr hcardM
    nlinarith
  have hF'm2 : (1 - 2 * τ) * (P.carrier.card : ℝ) ≤ F'.card := by
    have hc : (0 : ℝ) ≤ P.carrier.card := Nat.cast_nonneg _
    nlinarith
  obtain ⟨p, G, L, S, nu, hp, hG, hGm, hSpart, hSproper, hnu, hc⟩ :=
    section16_synchronized_compressed_cover_family ha (hslice sample) (hGs sample) hrpos
      ε hε hε1 hPb hEb T I hT hI hstep u hu.symm hk hm hmT hmI hv hvscale (2 * τ) F' hF'c
      (hcarrier ▸ hF'sub) (hcarrier ▸ hF'm2)
  refine ⟨p, G, L, S, nu, hp, hG.trans hF'sub, ?_, ?_, hSproper, hnu, hc⟩
  · simpa only [← hcarrier] using hGm
  · change IsPartition (fun j => (S j).carrier) P.carrier
    rw [hcarrier]
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
  classical
  let w := ((m : ℝ) / 8) ^ (Eb ε)
  by_cases hw : 16 ≤ w
  · have hm : 4 ≤ m := by
      by_contra hm
      have hm' : (m : ℝ) ≤ 3 := by exact_mod_cast (by omega : m ≤ 3)
      have hbase : (m : ℝ) / 8 ≤ 1 := by linarith
      have hw1 : w ≤ 1 := Real.rpow_le_one (by positivity) hbase hEb.le
      linarith
    obtain ⟨v, hv, hvscale, hvwidth⟩ := section16_lift_width_rounding hw
    obtain ⟨p, G, L, S, nu, hp, hG, hGm, hpart, hproper, hnu, hc⟩ :=
      section16_local_affine_lift_family P hP hk hm hmP D phi Pb Eb Gs hslice hGs
        ell hell hcover τ ε hq hτ hτ1 hε hε1 (by linarith) hEb.le hr hv hvscale
    refine ⟨p, G, L, S, nu, hp, hG, hGm, hpart, ?_, hnu, hc⟩
    intro j
    refine ⟨(hproper j).1, hvwidth.trans ?_⟩
    exact_mod_cast (hproper j).2
  · have hw0 : 0 ≤ w := Real.rpow_nonneg (by positivity) _
    have hwidth : Real.sqrt w / 4 ≤ 1 := by
      have hsquare := Real.sq_sqrt hw0
      have hs0 := Real.sqrt_nonneg w
      nlinarith [not_le.mp hw]
    obtain ⟨L, x, hpart⟩ := box_singleton_partition P
    refine ⟨1, P.carrier, L, fun j => pointSingletonBox (x j),
      fun j c _ => phi c.1 (x j), by simpa using hPb, Finset.Subset.rfl, ?_, hpart, ?_,
      fun j _ => isMultilinear_constant _, ?_⟩
    · have hn : (0 : ℝ) ≤ P.carrier.card := Nat.cast_nonneg _
      nlinarith
    · intro j
      refine ⟨pointSingletonBox_isProper _, ?_⟩
      simpa only [pointSingletonBox_width (by omega : 0 < k + 1), Nat.cast_one] using hwidth
    · intro a j z hz _ _
      have hz' : z = x j := by
        simpa only [pointSingletonBox_carrier, Finset.mem_singleton] using hz
      exact ⟨(a, ⟨0, by unfold section16CompressedCandidateCount; omega⟩),
        congrArg (phi a) hz'⟩

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

/-- Line counts may be padded. -/
theorem Section16LineCoverFamily.mono_count {N k q q' : Nat} [NeZero N] {ι : Type}
    {P : Box N (k + 1)} {B : ι → Finset (Point N (k + 1))}
    {phi : ι → Point N (k + 1) → ZMod N} {σ l : ℝ}
    (hline : Section16LineCoverFamily P B phi σ l q) (hqq' : q ≤ q') :
    Section16LineCoverFamily P B phi σ l q' := by
  classical
  obtain ⟨E, M, S, T, J, ell, hE, hEm, hpart, hproper, hproduct, hw, hell, hc⟩ := hline
  let ell' := fun a u h (i : Fin q') =>
    if hi : i.val < q then ell a u h ⟨i.val, hi⟩ else fun _ => 0
  refine ⟨E, M, S, T, J, ell', hE, hEm, hpart, hproper, hproduct, hw, ?_, ?_⟩
  · intro a u h i
    dsimp only [ell']
    split_ifs
    · exact hell _ _ _ _
    · exact ⟨0, 0, by simp⟩
  · intro a u h x hh hxB hxE hxS
    obtain ⟨i, hi⟩ := hc a u h x hh hxB hxE hxS
    refine ⟨⟨i.val, i.isLt.trans_le hqq'⟩, ?_⟩
    simpa only [ell', dif_pos i.isLt] using hi

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
  classical
  obtain ⟨E, M, S, T, J, ell, hE, hEm, hSpart, hSproper, hproduct, hwidth, hell, hc⟩ := hline
  have hlocal : ∀ u, ∃ (p : Nat) (G : Finset (Point N (k + 1)))
      (L : Nat) (R : Fin L → Box N (k + 1))
      (nu : Fin L → ι × Fin (section16CompressedCandidateCount r p) →
        Point N (k + 1) → ZMod N),
      (p : ℝ) ≤ Pb ε ∧
      G ⊆ (S u).carrier ∧ (1 - 2 * τ - ε) * ((S u).carrier.card : ℝ) ≤ G.card ∧
      IsBoxPartition R (S u) ∧
      (∀ j, (R j).IsProper ∧ Real.sqrt (((m : ℝ) / 8) ^ (Eb ε)) / 4 ≤ (R j).width) ∧
      (∀ j c, IsMultilinear (nu j c)) ∧
      ∀ a j z, z ∈ (R j).carrier → z ∈ B a ∩ E → z ∈ G → ∃ c, phi a z = nu j c z := by
    intro u
    apply section16_local_affine_lift_all_scales_family (S u) (hSproper u) hk
      (by exact_mod_cast hm.trans (hwidth u)) (fun a => B a ∩ E) phi Pb Eb Gs hslice
      (fun sample a h i hi => hGs sample a h i (Finset.mem_inter.mp hi).1)
      (fun a => ell a u) (fun a => hell a u) ?_ τ ε hq hτ hτ1 hε hε1 hPb hEb hEb1 hr
    intro a h x hxS hxD
    have hxprod := hxS
    rw [appendCoordinate_eq_snoc] at hxprod
    have hh := ((hproduct u).mem_snoc h x).mp hxprod |>.1
    obtain ⟨hxB, hxE⟩ := Finset.mem_inter.mp hxD
    exact hc a u h x hh hxB hxE hxS
  choose p G L R nu hp hG hGm hRpart hRproper hnu hcov using hlocal
  let b := Pb ε
  let pmax := Nat.floor b
  let n0 := section16CompressedCandidateCount r pmax
  let n := Fintype.card ι * n0
  have hpmax : (pmax : ℝ) ≤ b := Nat.floor_le (zero_le_one.trans hPb)
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
    ?_, Finset.inter_subset_left.trans hE,
    ?_, boxFlatten_partition P S L R hSpart hRpart,
    fun j => (hRproper _ _).1, fun j => (hRproper _ _).2,
    fun j => padFiniteMultilinearFamily_isMultilinear _ (hnu _ _), ?_⟩
  · have hn0 : (n0 : ℝ) ≤ max (Pb ε) ((r.choose 2 : ℝ) * Pb ε * Pb ε) :=
      section16_compressed_candidate_bound hpmax
    change ((Fintype.card ι * n0 : Nat) : ℝ) ≤ _
    push_cast
    exact mul_le_mul_of_nonneg_left hn0 (Nat.cast_nonneg _)
  · simpa only [sub_add_eq_sub_sub] using hmass
  · intro a j z hzQ hzB hzH
    obtain ⟨hzE, hzG⟩ := Finset.mem_inter.mp hzH
    have hzS := IsPartition.cell_subset (hRpart (e.symm j).1) (e.symm j).2 hzQ
    have hzlocal := (IsPartition.good_union_mem_iff hSpart G hG (e.symm j).1 hzS).mp hzG
    apply padFiniteMultilinearFamily_covers _ (hpn _) z (phi a z)
    exact hcov (e.symm j).1 a (e.symm j).2 z hzQ (Finset.mem_inter.mpr ⟨hzB, hzE⟩) hzlocal

/-- The rounded family lift: sample size `r = ⌈6·max(1,q)·max(1,|ι|)/τ⌉`. -/
theorem Section16LineCoverFamily.global_affine_lift_rounded_family {N k q : Nat} [Fact N.Prime]
    {ι : Type} [Fintype ι]
    {P : Box N (k + 1)} {B : ι → Finset (Point N (k + 1))}
    {phi : ι → Point N (k + 1) → ZMod N} {σ l : ℝ} {Pb Eb : Nat → Real → Real}
    (hline : Section16LineCoverFamily P B phi σ l q)
    (Gs : (r : Nat) → (ι → Fin r → ZMod N) → Finset (Point N k × ZMod N))
    (hslice : ∀ r sample, MultiplyLinearWith (Pb r) (Eb r) (Gs r sample))
    (hGs : ∀ r sample a h i, appendCoordinate h (sample a i) ∈ B a →
      (h, phi a (appendCoordinate h (sample a i))) ∈ Gs r sample)
    (hranges : Section16SliceProviderRanges Pb Eb)
    (hk : 0 < k) (hl : 0 ≤ l) (τ ε : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let r := ⌈6 * (max 1 q : ℝ) * ((max 1 (Fintype.card ι) : Nat) : ℝ) / τ⌉₊
    ∃ (n : Nat) (H : Finset (Point N (k + 1))) (L : Nat)
      (Q : Fin L → Box N (k + 1)) (mu : Fin L → Fin n → Point N (k + 1) → ZMod N),
      (n : ℝ) ≤ (Fintype.card ι : ℝ) * max (Pb r ε) ((r.choose 2 : ℝ) * Pb r ε * Pb r ε) ∧
      H ⊆ P.carrier ∧ (1 - σ - 2 * τ - ε) * (P.carrier.card : ℝ) ≤ H.card ∧
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
      (∀ j, Real.sqrt (((⌊l⌋₊ : ℝ) / 8) ^ (Eb r ε)) / 4 ≤ (Q j).width) ∧
      (∀ j i, IsMultilinear (mu j i)) ∧
      ∀ a j z, z ∈ (Q j).carrier → z ∈ B a → z ∈ H → ∃ i, phi a z = mu j i z := by
  intro r
  let q' := max 1 q
  have hq' : 0 < q' := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hr : 6 * (q' : ℝ) * ((max 1 (Fintype.card ι) : Nat) : ℝ) ≤ (r : ℝ) * τ := by
    have h : 6 * (max 1 q : ℝ) * ((max 1 (Fintype.card ι) : Nat) : ℝ) / τ ≤ (r : ℝ) :=
      Nat.le_ceil _
    have h2 := (div_le_iff₀ hτ).mp h
    have hq'cast : ((q' : Nat) : ℝ) = max 1 (q : ℝ) := by
      simp only [q', Nat.cast_max, Nat.cast_one]
    rw [hq'cast]
    exact h2
  have hMpos : (0 : ℝ) < ((max 1 (Fintype.card ι) : Nat) : ℝ) := by
    have : 0 < max 1 (Fintype.card ι) := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
    exact_mod_cast this
  have hrpos : 0 < r := by
    by_contra hz
    have hz' : r = 0 := by omega
    have hq'' : (0 : ℝ) < q' := by exact_mod_cast hq'
    rw [hz', Nat.cast_zero, zero_mul] at hr
    have : (0 : ℝ) < 6 * (q' : ℝ) * ((max 1 (Fintype.card ι) : Nat) : ℝ) := by positivity
    linarith
  obtain ⟨hPb, hEb, hEb1⟩ := hranges r ε hrpos hε hε1
  have hpad := hline.mono_count (le_max_right 1 q)
  exact hpad.global_affine_lift_family (Gs r) (hslice r) (hGs r) hk (Nat.floor_le hl)
    τ ε hq' hτ hτ1 hε hε1 hPb hEb hEb1 hr
end LeanProofs.GowersSzemeredi
