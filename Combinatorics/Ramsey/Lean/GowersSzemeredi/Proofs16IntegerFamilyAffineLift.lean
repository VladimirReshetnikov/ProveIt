import GowersSzemeredi.Proofs16IntegerLocalAffineLift

/-! Global and rounded affine lifting from genuine family line covers.
All refined cells retain ascending certificates, and all numerical controls
are identical to the existing sampling and interpolation construction. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem IntegerSection16LineCoverFamily.mono_count {N k q q' : Nat} [NeZero N] {ι : Type}
    {P : Box N (k + 1)} {B : ι → Finset (Point N (k + 1))}
    {phi : ι → Point N (k + 1) → ZMod N} {σ l : ℝ}
    (hline : IntegerSection16LineCoverFamily P B phi σ l q) (hqq' : q ≤ q') :
    IntegerSection16LineCoverFamily P B phi σ l q' := by
  classical
  obtain ⟨E, M, S, T, J, ell, hE, hEm, hpart, hproper, hTcert, hJcert, hproduct, hw, hell, hc⟩ := hline
  let ell' := fun a u h (i : Fin q') =>
    if hi : i.val < q then ell a u h ⟨i.val, hi⟩ else fun _ => 0
  refine ⟨E, M, S, T, J, ell', hE, hEm, hpart, hproper, hTcert, hJcert, hproduct, hw, ?_, ?_⟩
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
theorem IntegerSection16LineCoverFamily.global_affine_lift_family {N k q r m : Nat} [Fact N.Prime]
    {ι : Type} [Fintype ι]
    {P : Box N (k + 1)} {B : ι → Finset (Point N (k + 1))}
    {phi : ι → Point N (k + 1) → ZMod N} {σ l : ℝ} {Pb Eb : Real → Real}
    (hline : IntegerSection16LineCoverFamily P B phi σ l q)
    (Gs : (ι → Fin r → ZMod N) → Finset (Point N k × ZMod N))
    (hslice : ∀ sample, IntegerMultiplyLinearWith Pb Eb (Gs sample))
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
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsAscendingInteger) ∧
      (∀ j, Real.sqrt (((m : ℝ) / 8) ^ (Eb ε)) / 4 ≤ (Q j).width) ∧
      (∀ j i, IsMultilinear (mu j i)) ∧
      ∀ a j z, z ∈ (Q j).carrier → z ∈ B a → z ∈ H → ∃ i, phi a z = mu j i z := by
  classical
  obtain ⟨E, M, S, T, J, ell, hE, hEm, hSpart, hSproper, hTcert, hJcert, hproduct, hwidth, hell, hc⟩ := hline
  have hlocal : ∀ u, ∃ (p : Nat) (G : Finset (Point N (k + 1)))
      (L : Nat) (R : Fin L → Box N (k + 1))
      (nu : Fin L → ι × Fin (section16CompressedCandidateCount r p) →
        Point N (k + 1) → ZMod N),
      (p : ℝ) ≤ Pb ε ∧
      G ⊆ (S u).carrier ∧ (1 - 2 * τ - ε) * ((S u).carrier.card : ℝ) ≤ G.card ∧
      IsBoxPartition R (S u) ∧
      (∀ j, (R j).IsAscendingInteger ∧ Real.sqrt (((m : ℝ) / 8) ^ (Eb ε)) / 4 ≤ (R j).width) ∧
      (∀ j c, IsMultilinear (nu j c)) ∧
      ∀ a j z, z ∈ (R j).carrier → z ∈ B a ∩ E → z ∈ G → ∃ c, phi a z = nu j c z := by
    intro u
    apply section16_local_integer_affine_lift_all_scales_family (S u) (hSproper u) hk
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
theorem IntegerSection16LineCoverFamily.global_affine_lift_rounded_family {N k q : Nat} [Fact N.Prime]
    {ι : Type} [Fintype ι]
    {P : Box N (k + 1)} {B : ι → Finset (Point N (k + 1))}
    {phi : ι → Point N (k + 1) → ZMod N} {σ l : ℝ} {Pb Eb : Nat → Real → Real}
    (hline : IntegerSection16LineCoverFamily P B phi σ l q)
    (Gs : (r : Nat) → (ι → Fin r → ZMod N) → Finset (Point N k × ZMod N))
    (hslice : ∀ r sample, IntegerMultiplyLinearWith (Pb r) (Eb r) (Gs r sample))
    (hGs : ∀ r sample a h i, appendCoordinate h (sample a i) ∈ B a →
      (h, phi a (appendCoordinate h (sample a i))) ∈ Gs r sample)
    (hranges : Section16SliceProviderRanges Pb Eb)
    (hk : 0 < k) (hl : 0 ≤ l) (τ ε : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let r := ⌈6 * (max 1 q : ℝ) * ((max 1 (Fintype.card ι) : Nat) : ℝ) / τ⌉₊
    ∃ (n : Nat) (H : Finset (Point N (k + 1))) (L : Nat)
      (Q : Fin L → Box N (k + 1)) (mu : Fin L → Fin n → Point N (k + 1) → ZMod N),
      (n : ℝ) ≤ (Fintype.card ι : ℝ) * max (Pb r ε) ((r.choose 2 : ℝ) * Pb r ε * Pb r ε) ∧
      H ⊆ P.carrier ∧ (1 - σ - 2 * τ - ε) * (P.carrier.card : ℝ) ≤ H.card ∧
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsAscendingInteger) ∧
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
