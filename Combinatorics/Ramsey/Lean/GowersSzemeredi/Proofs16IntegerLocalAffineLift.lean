import GowersSzemeredi.Proofs16IntegerCompressedFamily

/-! Local sampled affine lifting for genuine integer boxes. The same
sample budget, candidate count, width and density losses are retained. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem section16_local_integer_affine_lift_family {N k q r m v : Nat} [Fact N.Prime]
    {ι : Type} [Fintype ι]
    (P : Box N (k + 1)) (hP : P.IsAscendingInteger) (hk : 0 < k)
    (hm : 4 ≤ m) (hmP : m ≤ P.width)
    (D : ι → Finset (Point N (k + 1))) (phi : ι → Point N (k + 1) → ZMod N)
    (Pb Eb : Real → Real) (Gs : (ι → Fin r → ZMod N) → Finset (Point N k × ZMod N))
    (hslice : ∀ sample, IntegerMultiplyLinearWith Pb Eb (Gs sample))
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
      IsBoxPartition S P ∧ (∀ j, (S j).IsAscendingInteger ∧ v - 1 ≤ (S j).width) ∧
      (∀ j c, IsMultilinear (nu j c)) ∧
      ∀ a j z, z ∈ (S j).carrier → z ∈ D a → z ∈ G → ∃ c, phi a z = nu j c z := by
  classical
  let T := boxInit P
  have hT : T.IsAscendingInteger := boxInit_isAscendingInteger P hP
  obtain ⟨d, A, hd, hcommon, haxes⟩ := hP
  let I0 := A (Fin.last k)
  let I := I0.toModAP N
  have hIeq : I = P.axis (Fin.last k) := (haxes _).2.2.2
  have hI0 : I0.IsProper := (haxes _).1
  have hI0N : I0.carrier ⊆ Finset.range N := (haxes _).2.2.1
  have hI : I.IsProper := (I0.toModAP_hasIntegerRepresentatives hI0 hI0N).isProper
  have hmT : m ≤ T.width := hmP.trans (boxInit_width P hk)
  have hmI : m ≤ I.length := by rw [hIeq]; exact hmP.trans (P.width_le_axis_length (Fin.last k))
  have hInonempty : I.carrier.Nonempty := by
    apply Finset.card_pos.mp
    rw [show I.carrier.card = I.length from hI]
    omega
  have hprod : IsLastCoordinateBoxProduct P T I := by rw [hIeq]; exact boxInit_last_product P
  have hcarrier : P.carrier = lastProductSet T.carrier I.carrier := hprod.1
  have hstep : I.step = T.commonDiff := by rw [hIeq]; exact P.axis_step (Fin.last k)
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
    section16_synchronized_integer_compressed_cover_family ha (hslice sample) (hGs sample) hrpos
      ε hε hε1 hPb hEb T I0 hT hI0 hI0N hstep hk hm hmT hmI hv hvscale (2 * τ) F' hF'c
      (hcarrier ▸ hF'sub) (hcarrier ▸ hF'm2)
  refine ⟨p, G, L, S, nu, hp, hG.trans hF'sub, ?_, ?_, hSproper, hnu, hc⟩
  · change (1 - 2 * τ - ε) * ((lastProductSet T.carrier I.carrier).card : Real) ≤ G.card at hGm
    rw [← hcarrier] at hGm
    exact hGm
  · change IsPartition (fun j => (S j).carrier) P.carrier
    rw [hcarrier]
    exact hSpart

/-- **The family local lift at every scale.** -/
theorem section16_local_integer_affine_lift_all_scales_family {N k q r m : Nat} [Fact N.Prime]
    {ι : Type} [Fintype ι]
    (P : Box N (k + 1)) (hP : P.IsAscendingInteger) (hk : 0 < k) (hmP : m ≤ P.width)
    (D : ι → Finset (Point N (k + 1))) (phi : ι → Point N (k + 1) → ZMod N)
    (Pb Eb : Real → Real) (Gs : (ι → Fin r → ZMod N) → Finset (Point N k × ZMod N))
    (hslice : ∀ sample, IntegerMultiplyLinearWith Pb Eb (Gs sample))
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
      (∀ j, (S j).IsAscendingInteger ∧ Real.sqrt (((m : ℝ) / 8) ^ (Eb ε)) / 4 ≤ (S j).width) ∧
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
      section16_local_integer_affine_lift_family P hP hk hm hmP D phi Pb Eb Gs hslice hGs
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
      refine ⟨pointSingletonBox_isAscendingInteger _, ?_⟩
      simpa only [pointSingletonBox_width (by omega : 0 < k + 1), Nat.cast_one] using hwidth
    · intro a j z hz _ _
      have hz' : z = x j := by
        simpa only [pointSingletonBox_carrier, Finset.mem_singleton] using hz
      exact ⟨(a, ⟨0, by unfold section16CompressedCandidateCount; omega⟩),
        congrArg (phi a) hz'⟩

end LeanProofs.GowersSzemeredi
