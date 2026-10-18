import GowersSzemeredi.Proofs16WithLift
import GowersSzemeredi.Proofs16GlobalLiftParameters
import GowersSzemeredi.Proofs16WidthMonotonicity
import GowersSzemeredi.Proofs16WithLemma9

/-! Declarations of `Proofs16WithLift` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

/-- A slice provider: every stacked sample of every size has a cover with
the given controls. -/
def Section16SliceProvider {N k : Nat} [NeZero N] (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N) (Pb Eb : Nat → Real → Real) : Prop :=
  ∀ (r : Nat) (sample : Fin r → ZMod N),
    MultiplyLinearWith (Pb r) (Eb r) (section16StackedSlices B phi sample)

theorem section16_local_affine_lift_with {N k q r m v : Nat} [Fact N.Prime]
    (P : Box N (k + 1)) (hP : P.IsProper) (hk : 0 < k)
    (hm : 4 ≤ m) (hmP : m ≤ P.width)
    (B D : Finset (Point N (k + 1))) (hD : D ⊆ B)
    (phi : Point N (k + 1) → ZMod N) (Pb Eb : Real → Real)
    (hslice : ∀ sample : Fin r → ZMod N,
      MultiplyLinearWith Pb Eb (section16StackedSlices B phi sample))
    (ell : Point N k → Fin q → ZMod N → ZMod N)
    (hell : ∀ h i, LinearOn Finset.univ (ell h i))
    (hcover : ∀ h x, appendCoordinate h x ∈ P.carrier → appendCoordinate h x ∈ D →
      ∃ i, phi (appendCoordinate h x) = ell h i x)
    (τ ε : ℝ) (hq : 0 < q) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hPb : 0 ≤ Pb ε) (hEb : 0 ≤ Eb ε)
    (hr : 6 * (q : ℝ) ≤ (r : ℝ) * τ) (hv : 1 ≤ v)
    (hvscale : (v : ℝ) ^ 2 + 1 ≤ ((m : ℝ) / 8) ^ (Eb ε)) :
    ∃ (p : Nat) (G : Finset (Point N (k + 1))) (L : Nat) (S : Fin L → Box N (k + 1))
      (nu : Fin L → Fin (section16CompressedCandidateCount r p) →
        Point N (k + 1) → ZMod N),
      (p : ℝ) ≤ Pb ε ∧
      G ⊆ P.carrier ∧ (1 - 2 * τ - ε) * (P.carrier.card : ℝ) ≤ G.card ∧
      IsBoxPartition S P ∧ (∀ j, (S j).IsProper ∧ v - 1 ≤ (S j).width) ∧
      (∀ j ij, IsMultilinear (nu j ij)) ∧
      ∀ j z, z ∈ (S j).carrier → z ∈ D → z ∈ G → ∃ ij, phi z = nu j ij z := by
  obtain ⟨p, G, L, S, nu, hp, hG, hGm, hpart, hproper, hnu, hc⟩ :=
    section16_local_affine_lift_family (ι := Unit) P hP hk hm hmP
      (fun _ => D) (fun _ => phi) Pb Eb
      (fun sample => section16StackedSlices B phi (sample ())) (fun sample => hslice (sample ()))
      (fun sample a h i hi => by cases a; exact section16StackedSlices_mem h i (hD hi))
      (fun _ => ell) (fun _ => hell) (fun _ => hcover)
      τ ε hq hτ hτ1 hε hε1 hPb hEb (by simpa using hr) hv hvscale
  refine ⟨p, G, L, S, fun j i => nu j ((), i), hp, hG, hGm, hpart, hproper,
    fun j i => hnu j ((), i), ?_⟩
  intro j z hz hzD hzG
  obtain ⟨⟨⟨⟩, i⟩, hi⟩ := hc () j z hz hzD hzG
  exact ⟨i, hi⟩

theorem section16_local_affine_lift_all_scales_with {N k q r m : Nat} [Fact N.Prime]
    (P : Box N (k + 1)) (hP : P.IsProper) (hk : 0 < k) (hmP : m ≤ P.width)
    (B D : Finset (Point N (k + 1))) (hD : D ⊆ B)
    (phi : Point N (k + 1) → ZMod N) (Pb Eb : Real → Real)
    (hslice : ∀ sample : Fin r → ZMod N,
      MultiplyLinearWith Pb Eb (section16StackedSlices B phi sample))
    (ell : Point N k → Fin q → ZMod N → ZMod N)
    (hell : ∀ h i, LinearOn Finset.univ (ell h i))
    (hcover : ∀ h x, appendCoordinate h x ∈ P.carrier → appendCoordinate h x ∈ D →
      ∃ i, phi (appendCoordinate h x) = ell h i x)
    (τ ε : ℝ) (hq : 0 < q) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hPb : 1 ≤ Pb ε) (hEb : 0 < Eb ε) (hEb1 : Eb ε ≤ 1)
    (hr : 6 * (q : ℝ) ≤ (r : ℝ) * τ) :
    ∃ (p : Nat) (G : Finset (Point N (k + 1))) (L : Nat) (S : Fin L → Box N (k + 1))
      (nu : Fin L → Fin (section16CompressedCandidateCount r p) →
        Point N (k + 1) → ZMod N),
      (p : ℝ) ≤ Pb ε ∧
      G ⊆ P.carrier ∧ (1 - 2 * τ - ε) * (P.carrier.card : ℝ) ≤ G.card ∧
      IsBoxPartition S P ∧
      (∀ j, (S j).IsProper ∧ Real.sqrt (((m : ℝ) / 8) ^ (Eb ε)) / 4 ≤ (S j).width) ∧
      (∀ j ij, IsMultilinear (nu j ij)) ∧
      ∀ j z, z ∈ (S j).carrier → z ∈ D → z ∈ G → ∃ ij, phi z = nu j ij z := by
  obtain ⟨p, G, L, S, nu, hp, hG, hGm, hpart, hproper, hnu, hc⟩ :=
    section16_local_affine_lift_all_scales_family (ι := Unit) P hP hk hmP
      (fun _ => D) (fun _ => phi) Pb Eb
      (fun sample => section16StackedSlices B phi (sample ())) (fun sample => hslice (sample ()))
      (fun sample a h i hi => by cases a; exact section16StackedSlices_mem h i (hD hi))
      (fun _ => ell) (fun _ => hell) (fun _ => hcover)
      τ ε hq hτ hτ1 hε hε1 hPb hEb hEb1 (by simpa using hr)
  refine ⟨p, G, L, S, fun j i => nu j ((), i), hp, hG, hGm, hpart, hproper,
    fun j i => hnu j ((), i), ?_⟩
  intro j z hz hzD hzG
  obtain ⟨⟨⟨⟩, i⟩, hi⟩ := hc () j z hz hzD hzG
  exact ⟨i, hi⟩

theorem Section16LineCover.global_affine_lift_with {N k q r m : Nat} [Fact N.Prime]
    {P : Box N (k + 1)} {B : Finset (Point N (k + 1))}
    {phi : Point N (k + 1) → ZMod N} {σ l : ℝ} {Pb Eb : Real → Real}
    (hline : Section16LineCover P B phi σ l q)
    (hslice : ∀ sample : Fin r → ZMod N,
      MultiplyLinearWith Pb Eb (section16StackedSlices B phi sample))
    (hk : 0 < k) (hm : (m : ℝ) ≤ l) (τ ε : ℝ) (hq : 0 < q)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hPb : 1 ≤ Pb ε) (hEb : 0 < Eb ε) (hEb1 : Eb ε ≤ 1)
    (hr : 6 * (q : ℝ) ≤ (r : ℝ) * τ) :
    ∃ (n : Nat) (H : Finset (Point N (k + 1))) (L : Nat)
      (Q : Fin L → Box N (k + 1)) (mu : Fin L → Fin n → Point N (k + 1) → ZMod N),
      (n : ℝ) ≤ max (Pb ε) ((r.choose 2 : ℝ) * Pb ε * Pb ε) ∧
      H ⊆ P.carrier ∧ (1 - σ - 2 * τ - ε) * (P.carrier.card : ℝ) ≤ H.card ∧
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
      (∀ j, Real.sqrt (((m : ℝ) / 8) ^ (Eb ε)) / 4 ≤ (Q j).width) ∧
      (∀ j i, IsMultilinear (mu j i)) ∧
      ∀ j z, z ∈ (Q j).carrier → z ∈ B → z ∈ H → ∃ i, phi z = mu j i z := by
  obtain ⟨E, M, S, T, J, ell, hE, hEm, hpart, hproper, hproduct, hw, hell, hc⟩ := hline
  have hfamily : Section16LineCoverFamily P (fun _ : Unit => B) (fun _ => phi) σ l q :=
    ⟨E, M, S, T, J, fun _ => ell, hE, hEm, hpart, hproper, hproduct, hw,
      fun _ => hell, fun _ => hc⟩
  obtain ⟨n, H, L, Q, mu, hn, hH, hHm, hQ, hproperQ, hwidth, hmu, hcov⟩ :=
    hfamily.global_affine_lift_family
      (fun sample => section16StackedSlices B phi (sample ())) (fun sample => hslice (sample ()))
      (fun sample a h i hi => by cases a; exact section16StackedSlices_mem h i hi)
      hk hm τ ε hq hτ hτ1 hε hε1 hPb hEb hEb1 (by simpa using hr)
  refine ⟨n, H, L, Q, mu, ?_, hH, hHm, hQ, hproperQ, hwidth, hmu, hcov ()⟩
  simpa only [Fintype.card_unit, Nat.cast_one, one_mul] using hn

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

/-- The rounded global lift with a slice provider: the sample size is the
natural ceiling `r = ⌈6*max(1,q)/τ⌉` and the base scale is `⌊l⌋`. -/
theorem Section16LineCover.global_affine_lift_rounded_with {N k q : Nat} [Fact N.Prime]
    {P : Box N (k + 1)} {B : Finset (Point N (k + 1))}
    {phi : Point N (k + 1) → ZMod N} {σ l : ℝ} {Pb Eb : Nat → Real → Real}
    (hline : Section16LineCover P B phi σ l q)
    (hslice : Section16SliceProvider B phi Pb Eb)
    (hranges : Section16SliceProviderRanges Pb Eb)
    (hk : 0 < k) (hl : 0 ≤ l) (τ ε : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let r := ⌈6 * (max 1 q : ℝ) / τ⌉₊
    ∃ (n : Nat) (H : Finset (Point N (k + 1))) (L : Nat)
      (Q : Fin L → Box N (k + 1)) (mu : Fin L → Fin n → Point N (k + 1) → ZMod N),
      (n : ℝ) ≤ max (Pb r ε) ((r.choose 2 : ℝ) * Pb r ε * Pb r ε) ∧
      H ⊆ P.carrier ∧ (1 - σ - 2 * τ - ε) * (P.carrier.card : ℝ) ≤ H.card ∧
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
      (∀ j, Real.sqrt (((⌊l⌋₊ : ℝ) / 8) ^ (Eb r ε)) / 4 ≤ (Q j).width) ∧
      (∀ j i, IsMultilinear (mu j i)) ∧
      ∀ j z, z ∈ (Q j).carrier → z ∈ B → z ∈ H → ∃ i, phi z = mu j i z := by
  intro r
  let q' := max 1 q
  have hq' : 0 < q' := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hr : 6 * (q' : ℝ) ≤ (r : ℝ) * τ := by
    have h := (div_le_iff₀ hτ).mp (Nat.le_ceil (6 * (max 1 q : ℝ) / τ))
    simpa only [q', Nat.cast_max, Nat.cast_one] using h
  have hrpos : 0 < r := by
    by_contra hz
    have hz' : r = 0 := by omega
    have hq'' : (0 : ℝ) < q' := by exact_mod_cast hq'
    rw [hz', Nat.cast_zero, zero_mul] at hr
    linarith
  obtain ⟨hPb, hEb, hEb1⟩ := hranges r ε hrpos hε hε1
  have hpad := hline.mono_count (le_max_right 1 q)
  exact hpad.global_affine_lift_with (hslice r) hk (Nat.floor_le hl) τ ε hq' hτ hτ1 hε hε1
    hPb hEb hEb1 hr

/-- **The explicit lift with arbitrary spectrum and slice controls.** -/
theorem Section16AllBoxLineCoversWith.explicit_multilinear_cover_with {N k : Nat} [Fact N.Prime]
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    {theta gamma : Real} {Qd Ed : Real → Real} {Pb Eb : Nat → Real → Real}
    (hline : Section16AllBoxLineCoversWith theta gamma Qd Ed B phi)
    (hslice : Section16SliceProvider B phi Pb Eb)
    (hranges : Section16SliceProviderRanges Pb Eb)
    (hk : 0 < k) (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hEd : ∀ s, 0 < s → s ≤ 1 → 0 ≤ Ed s)
    {rho : Real} (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (m : Nat) (P : Box N (k + 1)) (hP : P.IsProper) (hm : m ≤ P.width) :
    let sigma := rho / 4
    ∃ qGamma qDelta : Nat,
      (qGamma : Real) ≤ section16Lemma9QBound sigma theta gamma k ∧
      (qDelta : Real) ≤ Qd (sigma / 2) ∧
      let l := lemma9WidthWith m qDelta k sigma theta gamma (Ed (sigma / 2))
        (section16Zeta theta gamma k)
      let r := ⌈6 * (max 1 qGamma : Real) / sigma⌉₊
      ∃ (n : Nat) (H : Finset (Point N (k + 1))) (L : Nat)
        (Q : Fin L → Box N (k + 1)) (mu : Fin L → Fin n → Point N (k + 1) → ZMod N),
        (n : Real) ≤ max (Pb r sigma) ((r.choose 2 : Real) * Pb r sigma * Pb r sigma) ∧
        H ⊆ P.carrier ∧ (1 - rho) * (P.carrier.card : Real) ≤ H.card ∧
        IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
        (∀ j, Real.sqrt (((Nat.floor l : Real) / 8) ^ (Eb r sigma)) / 4 ≤ (Q j).width) ∧
        (∀ j i, IsMultilinear (mu j i)) ∧
        ∀ j z, z ∈ (Q j).carrier → z ∈ B → z ∈ H → ∃ i, phi z = mu j i z := by
  intro sigma
  have hσ : 0 < sigma := by dsimp [sigma]; positivity
  have hσ1 : sigma ≤ 1 := by dsimp [sigma]; linarith
  obtain ⟨qGamma, qDelta, hqG, hqD, hcover⟩ := hline sigma hσ hσ1 m P hP hm
  refine ⟨qGamma, qDelta, hqG, hqD, ?_⟩
  intro l _
  have hl : 0 ≤ l := by
    have hz := (section16Zeta_pos_le_half k ht ht1 hg hg1).1
    dsimp only [l]
    unfold lemma9WidthWith
    positivity
  have hresult := hcover.global_affine_lift_rounded_with hslice hranges hk hl
    sigma sigma hσ hσ1 hσ hσ1
  have hmass : 1 - sigma - 2 * sigma - sigma = 1 - rho := by dsimp [sigma]; ring
  simpa only [hmass] using hresult

end LeanProofs.GowersSzemeredi
