import GowersSzemeredi.Proofs13PolyRecurrence
import GowersSzemeredi.Proofs13FiniteRecurrence
import GowersSzemeredi.Proofs13AllDensityExtraction

/-! Stage 13.6 at a polynomial precision (Notes L.7c, P2).

The catalogue's Lemma 13.6 consumes Stage 13.5 through its precision
`|P|^(−1/2^(11q))·N`. The step-span budget `hbudget` then forces the row
length `m ≤ ζ·|P|^(1/2^(11q))`, exponentially small in `q`. Everything
downstream (13.7, 13.8, the square extraction) uses the catalogue
predicates only through fields that do not involve that exponent.

This module therefore keeps the catalogue predicates and adds a polynomial
precision:
* `lemma_13_5_poly_with_catalogue`: one Stage 13.5 progression satisfying
  both `IsStage135Data` and `IsStage135At u u`, where
  `u = (2p(q+1)^8)^(−4)` (`stage135UniformExponent`).
  - If `(2p(q+1)^8)^2 ≤ 2^(11q)`, the phase-partition progression of
    `lemma_13_5_poly` beats both printed exponents.
  - Otherwise `q` is small, and the corpus progression of `lemma_13_5_prime`
    already has `1/2^(12q) ≥ u`.
* `lemma_13_6_from_initial_stages_at`: the corpus construction with the
  precision `ε` as a parameter, under the budget `ε ≤ ζ/m`.
* `lemma_13_6_poly`: the two combined, with every budget stated in terms of
  `|P|^u`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem natCast_rpow_le_rpow_of_exponent_le {n : Nat} {a b : Real} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ≤ b) : (n : Real) ^ a ≤ (n : Real) ^ b := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, Real.zero_rpow ha, Real.zero_rpow hb, le_refl]
  · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hab

/-- Stage 13.5 data persist under smaller positive exponents. -/
theorem IsStage135At.mono {N : Nat} [NeZero N] {S : Section13Context N}
    {D : Stage134Data N} {E : Stage135Data N} {eL eP eL' eP' : Real}
    (h : IsStage135At S D E eL eP) (hL : 0 < eL') (hP : 0 < eP')
    (hLle : eL' ≤ eL) (hPle : eP' ≤ eP) : IsStage135At S D E eL' eP' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, h2, h3, ?_, ?_, h6⟩
  · have := natCast_rpow_le_rpow_of_exponent_le (n := D.P.length) hL.ne'
      (hL.trans_le hLle).ne' hLle
    linarith only [this, h4]
  · intro i h hh
    refine (h5 i h hh).trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg N))
    exact natCast_rpow_le_rpow_of_exponent_le
      (neg_ne_zero.mpr (hP.trans_le hPle).ne') (neg_ne_zero.mpr hP.ne') (neg_le_neg hPle)

/-- The uniform Stage 13.5 exponent `(2p(q+1)^8)^(−4)`. -/
def stage135UniformExponent (p q : Nat) : Real :=
  (((2 * p * (q + 1) ^ 8 : Nat) : Real) ^ 4)⁻¹

theorem stage135UniformExponent_pos {p q : Nat} (hp : 0 < p) :
    0 < stage135UniformExponent p q := by
  unfold stage135UniformExponent
  have : (0 : Nat) < 2 * p * (q + 1) ^ 8 := by positivity
  positivity

/-- **Lemma 13.5, catalogue and polynomial at once.** -/
theorem lemma_13_5_poly_with_catalogue {N : Nat} [NeZero N] (hprime : N.Prime)
    {K : Real} {p : Nat} (hpp : ProgressionPhasePartition K p) (hp : 0 < p) (hK : K ≤ 2 ^ p)
    (S : Section13Context N) (D : Stage134Data N) (theta : Real)
    (h134 : IsStage134Data S theta D) :
    ∃ E : Stage135Data N, IsStage135Data S D E ∧
      IsStage135At S D E (stage135UniformExponent p D.q) (stage135UniformExponent p D.q) := by
  obtain ⟨c, hc⟩ : ∃ c : Nat, c = 2 * p * (D.q + 1) ^ 8 := ⟨_, rfl⟩
  have hc1 : 1 ≤ c := by
    have : 0 < 2 * p * (D.q + 1) ^ 8 := by positivity
    omega
  have hcR : (1 : Real) ≤ c := by exact_mod_cast hc1
  have hu : stage135UniformExponent p D.q = ((c : Real) ^ 4)⁻¹ := by
    unfold stage135UniformExponent
    rw [← hc]
  have he : stage135PolyExponent p D.q = ((c : Real) ^ 2)⁻¹ := by
    unfold stage135PolyExponent
    rw [← hc]
  have hupos : 0 < ((c : Real) ^ 4)⁻¹ := by positivity
  have hue : ((c : Real) ^ 4)⁻¹ ≤ ((c : Real) ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hcR (by norm_num))
  have h12 : (1 : Real) / 2 ^ (12 * D.q) ≤ 1 / 2 ^ (11 * D.q) :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
  have hpos11 : (0 : Real) < 1 / 2 ^ (11 * D.q) := by positivity
  have hpos12 : (0 : Real) < 1 / 2 ^ (12 * D.q) := by positivity
  by_cases hcase : c ^ 2 ≤ 2 ^ (11 * D.q)
  · obtain ⟨E, hE⟩ := lemma_13_5_poly hpp hp hK S D theta h134
    rw [he] at hE
    have h11 : (1 : Real) / 2 ^ (11 * D.q) ≤ ((c : Real) ^ 2)⁻¹ := by
      rw [one_div]
      exact inv_anti₀ (by positivity) (by exact_mod_cast hcase)
    refine ⟨E, (isStage135Data_iff_at S D E).mpr
      (hE.mono hpos12 hpos11 (h12.trans h11) h11), ?_⟩
    rw [hu]
    exact hE.mono hupos hupos hue hue
  · push_neg at hcase
    obtain ⟨E, hE⟩ := lemma_13_5_prime hprime S D theta h134
    have h2q : 2 ^ D.q ≤ 2 ^ (11 * D.q) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h12q : 2 ^ (12 * D.q) ≤ c ^ 4 := by
      calc 2 ^ (12 * D.q) = 2 ^ (11 * D.q) * 2 ^ D.q := by rw [← pow_add]; ring_nf
        _ ≤ c ^ 2 * c ^ 2 := Nat.mul_le_mul hcase.le (h2q.trans hcase.le)
        _ = c ^ 4 := by ring
    have hu12 : ((c : Real) ^ 4)⁻¹ ≤ 1 / 2 ^ (12 * D.q) := by
      rw [one_div]
      exact inv_anti₀ (by positivity) (by exact_mod_cast h12q)
    refine ⟨E, hE, ?_⟩
    rw [hu]
    exact ((isStage135Data_iff_at S D E).mp hE).mono hupos hupos hu12 (hu12.trans h12)

/-- The common step lies in every required Bohr set, at any precision `ε`
of the Stage 13.5 phases with `ε ≤ ζ/m`. -/
theorem stage136_common_step_mem_bohr_at {N : Nat} [NeZero N]
    (S : Section13Context N) (theta zeta eps : Real) (D : Stage134Data N)
    (E : Stage135Data N) (m : Nat) (K : ZMod N → Finset (ZMod N))
    (h134 : IsStage134Data S theta D)
    (hprec : ∀ i, ∀ h, h ∈ E.Q.carrier →
      (centeredAbs ((D.a i * h + D.b i) * E.Q.step) : Real) ≤ eps * N)
    (hK : ∀ h ∈ criticalHeights S D E, ∀ r ∈ K h,
      theta * (N : Real) ^ 2 ≤ ‖fourier (verticalEdgeFiberFunction S.A h) r‖)
    (hbudget : eps ≤ zeta / m) :
    ∀ h ∈ criticalHeights S D E, E.Q.step ∈ bohr (K h) (zeta / m) := by
  classical
  intro h hh
  have hmem := Finset.mem_inter.mp (Finset.mem_filter.mp hh).1
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro r hr
  obtain ⟨i, hi⟩ := h134.2.2.2.2.2.2.2.2 h hmem.2 r (hK h hh r hr)
  rw [hi]
  exact (hprec i h hmem.1).trans (mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg _))

/-- The common-step extraction from Bohr models at a general precision. -/
theorem lemma_13_6_of_bohr_models_at {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (theta zeta eps : Real) (D : Stage134Data N)
    (E : Stage135Data N) (m : Nat) (Y : ZMod N → Finset (Pair N))
    (K : ZMod N → Finset (ZMod N)) (psi : ZMod N → ZMod N → ZMod N)
    (h134 : IsStage134Data S theta D) (h135 : IsStage135Data S D E)
    (hprec : ∀ i, ∀ h, h ∈ E.Q.carrier →
      (centeredAbs ((D.a i * h + D.b i) * E.Q.step) : Real) ≤ eps * N)
    (hm : 0 < m) (hsize : m * m ≤ N) (hupper : m + 1 ≤ E.Q.length)
    (hlower : section13Zeta S.alpha / 2 *
      (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q S.alpha)) ≤ m)
    (hY : ∀ h ∈ criticalHeights S D E,
      Y h ⊆ verticalEdgeDomain S.A h ∧
      (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224 * (N : Real) ^ 2 ≤ (Y h).card)
    (hK : ∀ h ∈ criticalHeights S D E, ∀ r ∈ K h,
      theta * (N : Real) ^ 2 ≤ ‖fourier (verticalEdgeFiberFunction S.A h) r‖)
    (hbudget : eps ≤ zeta / m)
    (hmodel : ∀ h ∈ criticalHeights S D E,
      HasBohrDifferenceModel (section13EdgeIndexDomain N) (verticalPhiDifference S.phi h)
        (K h) zeta (Y h) (psi h)) :
    ∃ F : Stage136Data N, IsStage136Data S D E F ∧ m ≤ F.R.length ∧ F.R.length ≤ E.Q.length := by
  apply lemma_13_6_of_short_difference_rules_with_length S D E h135 m Y hm hsize hupper hlower hY
  intro h hh
  exact corollary_10_14_holds N (Pair N) (section13EdgeIndexDomain N)
    (verticalPhiDifference S.phi h) (K h) zeta (Y h) (psi h) (Fact.out : N.Prime)
    (hmodel h hh) m hm E.Q.step
    (stage136_common_step_mem_bohr_at S theta zeta eps D E m K h134 hprec hK hbudget h hh)

/-- **Stage 13.6 at a general precision**, at all densities. -/
theorem lemma_13_6_from_initial_stages_at {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N) (m : Nat) (eps : Real)
    (h134 : IsStage134Data S (section10Lambda (S.alpha ^ 32 / 16)) D)
    (h135 : IsStage135Data S D E)
    (hprec : ∀ i, ∀ h, h ∈ E.Q.carrier →
      (centeredAbs ((D.a i * h + D.b i) * E.Q.step) : Real) ≤ eps * N)
    (hm : 0 < m) (hsize : m * m ≤ N) (hupper : m + 1 ≤ E.Q.length)
    (hlower : section13Zeta S.alpha / 2 *
      (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q S.alpha)) ≤ m)
    (hbudget : eps ≤ section10Zeta (S.alpha ^ 32 / 16) / m) :
    ∃ F : Stage136Data N, IsStage136Data S D E F ∧ m ≤ F.R.length ∧ F.R.length ≤ E.Q.length := by
  classical
  let a : Real := S.alpha ^ 32 / 16
  let K : ZMod N → Finset (ZMod N) := fun h ↦
    domainLargeSpectrum (section13VerticalDomain S.A h) (section10Lambda a * N * N)
  have hex : ∀ h : ZMod N, ∃ Y : Finset (Pair N), ∃ psi : ZMod N → ZMod N,
      h ∈ criticalHeights S D E →
        Y ⊆ verticalEdgeDomain S.A h ∧
        (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224 * (N : Real) ^ 2 ≤ Y.card ∧
        HasBohrDifferenceModel (section13EdgeIndexDomain N) (verticalPhiDifference S.phi h)
          (K h) (section10Zeta a) Y psi := by
    intro h
    by_cases hh : h ∈ criticalHeights S D E
    · obtain ⟨Y, psi, hdata⟩ := section13_uniform_height_model_all_densities S h
        (Finset.mem_filter.mp hh).2
      exact ⟨Y, psi, fun _ ↦ hdata⟩
    · exact ⟨∅, fun _ ↦ 0, fun hh' ↦ (hh hh').elim⟩
  choose Y psi hdata using hex
  apply lemma_13_6_of_bohr_models_at S (section10Lambda a) (section10Zeta a) eps D E m Y K psi
    h134 h135 hprec hm hsize hupper hlower
    (fun h hh ↦ ⟨(hdata h hh).1, (hdata h hh).2.1⟩) ?_ hbudget
    (fun h hh ↦ (hdata h hh).2.2)
  intro h hh r hr
  have hthreshold := (Finset.mem_filter.mp hr).2
  change section10Lambda a * N * N ≤
    ‖fourier (domainFibreCountFunction (section13VerticalDomain S.A h)) r‖ at hthreshold
  rw [section13_vertical_fibre_function] at hthreshold
  convert hthreshold using 1 <;> ring

/-- **Lemmas 13.5 and 13.6 at a polynomial exponent.** Every budget is stated
in terms of `|P|^u` with `u = (2p(q+1)^8)^(−4)`. -/
theorem lemma_13_6_poly {N : Nat} [Fact N.Prime] {K : Real} {p : Nat}
    (hpp : ProgressionPhasePartition K p) (hp : 0 < p) (hK : K ≤ 2 ^ p)
    (S : Section13Context N) (D : Stage134Data N) (m : Nat)
    (h134 : IsStage134Data S (section10Lambda (S.alpha ^ 32 / 16)) D)
    (hm : 0 < m) (hsize : m * m ≤ N)
    (hupper : (m : Real) + 1 ≤ (D.P.length : Real) ^ stage135UniformExponent p D.q / 2)
    (hlower : section13Zeta S.alpha / 2 *
      (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q S.alpha)) ≤ m)
    (hbudget : (D.P.length : Real) ^ (-stage135UniformExponent p D.q) ≤
      section10Zeta (S.alpha ^ 32 / 16) / m) :
    ∃ E : Stage135Data N, ∃ F : Stage136Data N,
      IsStage135Data S D E ∧
      IsStage135At S D E (stage135UniformExponent p D.q) (stage135UniformExponent p D.q) ∧
      IsStage136Data S D E F ∧ m ≤ F.R.length ∧ F.R.length ≤ E.Q.length := by
  obtain ⟨E, h135, hE⟩ := lemma_13_5_poly_with_catalogue (Fact.out : N.Prime) hpp hp hK S D _ h134
  have hupper' : m + 1 ≤ E.Q.length := by
    have h : ((m + 1 : Nat) : Real) ≤ E.Q.length := by
      push_cast
      exact hupper.trans hE.2.2.2.1
    exact_mod_cast h
  obtain ⟨F, hF, hmF, hFQ⟩ := lemma_13_6_from_initial_stages_at S D E m _ h134 h135
    hE.2.2.2.2.1 hm hsize hupper' hlower hbudget
  exact ⟨E, F, h135, hE, hF, hmF, hFQ⟩

end LeanProofs.GowersSzemeredi
