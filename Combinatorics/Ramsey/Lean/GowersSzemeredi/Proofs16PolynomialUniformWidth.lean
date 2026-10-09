import GowersSzemeredi.Proofs16PolynomialProductAssembly

/-! Uniform graph-count control for the improved spectrum assembly.

The recurrence exponent decreases with the number of phases. Therefore
`floor (Qb sigma)` controls both the input threshold and a common lower
width bound, independently of the actual spectrum count in each cell.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The improved recurrence exponent is antitone in the number of phases. -/
theorem section16SimultaneousExponent_antitone_count {k p q r : Nat}
    (hp : 0 < p) (hqr : q ≤ r) :
    section16SimultaneousExponent k p r ≤ section16SimultaneousExponent k p q := by
  unfold section16SimultaneousExponent
  apply inv_anti₀ (by positivity)
  exact_mod_cast Nat.mul_le_mul_left 2
    (Nat.mul_le_mul_left p (Nat.pow_le_pow_left (by omega : q + 1 ≤ r + 1) _))

/-- A common graph-count upper bound gives a common product-width lower
bound, including the zero-width case. -/
theorem section16_polynomial_product_width_antitone_count {n k p q r : Nat}
    {zeta : Real} (hp : 0 < p) (hqr : q ≤ r) (hz : 0 ≤ zeta) :
    (zeta / 2) * Real.sqrt ((n : Real) ^ section16SimultaneousExponent k p r) ≤
      (zeta / 2) * Real.sqrt ((n : Real) ^ section16SimultaneousExponent k p q) := by
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.sqrt_le_sqrt
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst n
    simp only [Nat.cast_zero, Real.zero_rpow (section16SimultaneousExponent_pos k p r hp).ne',
      Real.zero_rpow (section16SimultaneousExponent_pos k p q hp).ne', le_refl]
  · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
      (section16SimultaneousExponent_antitone_count hp hqr)

/-- The statement of `exists_uniform_polynomial_spectrum_product_linearity` at fixed constants. -/
def UniformPolynomialSpectrumProductLinearityAt (k : Nat) (C p : Nat) : Prop :=
    ∀ (N m n : Nat) [NeZero N] (Qb Eb : Real → Real)
      (Gamma : Finset (Point N k × ZMod N)),
    MultiplyLinearWith Qb Eb Gamma →
    ∀ sigma zeta : Real, 0 < sigma → sigma ≤ 1 → 0 < zeta → zeta ≤ 1 / 2 →
    0 ≤ Qb sigma → 0 ≤ Eb sigma →
    ∀ (P : Box N k) (I : ModAP N) (u : (ZMod N)ˣ),
    P.IsProper → I.IsProper → I.step = P.commonDiff → I.step = (↑u : ZMod N) →
    1 ≤ k → 4 ≤ m → m ≤ P.width → m ≤ I.length →
    0 < n → (n : Real) ≤ ((m : Real) / 8) ^ (Eb sigma) →
    section16SimultaneousThreshold k C p (Nat.floor (Qb sigma)) ≤ n →
    ∀ (H : Finset (Point N k)) (K : Point N k → Finset (ZMod N))
      (A : Point N k → Finset (ZMod N)) (f : Point N k → ZMod N → ZMod N),
    (∀ x ∈ H, ∀ r ∈ K x, (x, r) ∈ Gamma) →
    (∀ x ∈ H, ∀ v : Nat, 0 < v → ∀ J : ModAP N, J.length ≤ v →
      J.step ∈ bohr (K x) (zeta / v) → LinearOn (J.carrier ∩ A x) (f x)) →
    ∃ G : Finset (Point N k), ∃ M : Nat,
      ∃ S : Fin M → Box N (k + 1), ∃ T : Fin M → Box N k, ∃ J : Fin M → ModAP N,
      G ⊆ P.carrier ∧ (1 - sigma) * (P.carrier.card : Real) ≤ G.card ∧
      IsPartition (fun j => (S j).carrier) (lastProductSet P.carrier I.carrier) ∧
      (∀ j, (S j).IsProper ∧ (zeta / 2) * Real.sqrt
        ((n : Real) ^ section16SimultaneousExponent k p (Nat.floor (Qb sigma))) ≤ (S j).width) ∧
      (∀ j, IsLastCoordinateBoxProduct (S j) (T j) (J j)) ∧
      ∀ j x, x ∈ G → x ∈ H → x ∈ (T j).carrier →
        LinearOn ((J j).carrier ∩ A x) (f x)

/-- `exists_uniform_polynomial_spectrum_product_linearity` at the constants of its input. -/
theorem uniformPolynomialSpectrumProductLinearityAt_of (k : Nat) {C p : Nat} (hC : 2 ≤ C) (hp : 0 < p)
    (hassembly : PolynomialSpectrumProductLinearityAt k C p) : UniformPolynomialSpectrumProductLinearityAt k C p := by
  unfold UniformPolynomialSpectrumProductLinearityAt
  intro N m n _ Qb Eb Gamma hML sigma zeta hs hs1 hz hzHalf hQ ha P I u
    hP hI hstep hu hk hm hmP hmI hn hnscale hnthreshold H K A f hK hlinear
  obtain ⟨q, G, M, S, T, J, hq, hGsub, hGmass, hpart, hproper, hproduct, hlin⟩ :=
    hassembly N m n Qb Eb Gamma hML sigma zeta hs hs1 hz hzHalf hQ ha P I u
      hP hI hstep hu hk hm hmP hmI hn hnscale hnthreshold H K A f hK hlinear
  refine ⟨G, M, S, T, J, hGsub, hGmass, hpart, ?_, hproduct, hlin⟩
  intro j
  exact ⟨(hproper j).1,
    (section16_polynomial_product_width_antitone_count hp (Nat.le_floor hq) hz.le).trans
      (hproper j).2⟩

/-- The polynomial spectrum assembly has a width bound expressed entirely
in terms of the supplied spectrum controls, with no unknown cover count. -/
theorem exists_uniform_polynomial_spectrum_product_linearity (k : Nat) :
    ∃ C p : Nat, 2 ≤ C ∧ 0 < p ∧
    ∀ (N m n : Nat) [NeZero N] (Qb Eb : Real → Real)
      (Gamma : Finset (Point N k × ZMod N)),
    MultiplyLinearWith Qb Eb Gamma →
    ∀ sigma zeta : Real, 0 < sigma → sigma ≤ 1 → 0 < zeta → zeta ≤ 1 / 2 →
    0 ≤ Qb sigma → 0 ≤ Eb sigma →
    ∀ (P : Box N k) (I : ModAP N) (u : (ZMod N)ˣ),
    P.IsProper → I.IsProper → I.step = P.commonDiff → I.step = (↑u : ZMod N) →
    1 ≤ k → 4 ≤ m → m ≤ P.width → m ≤ I.length →
    0 < n → (n : Real) ≤ ((m : Real) / 8) ^ (Eb sigma) →
    section16SimultaneousThreshold k C p (Nat.floor (Qb sigma)) ≤ n →
    ∀ (H : Finset (Point N k)) (K : Point N k → Finset (ZMod N))
      (A : Point N k → Finset (ZMod N)) (f : Point N k → ZMod N → ZMod N),
    (∀ x ∈ H, ∀ r ∈ K x, (x, r) ∈ Gamma) →
    (∀ x ∈ H, ∀ v : Nat, 0 < v → ∀ J : ModAP N, J.length ≤ v →
      J.step ∈ bohr (K x) (zeta / v) → LinearOn (J.carrier ∩ A x) (f x)) →
    ∃ G : Finset (Point N k), ∃ M : Nat,
      ∃ S : Fin M → Box N (k + 1), ∃ T : Fin M → Box N k, ∃ J : Fin M → ModAP N,
      G ⊆ P.carrier ∧ (1 - sigma) * (P.carrier.card : Real) ≤ G.card ∧
      IsPartition (fun j => (S j).carrier) (lastProductSet P.carrier I.carrier) ∧
      (∀ j, (S j).IsProper ∧ (zeta / 2) * Real.sqrt
        ((n : Real) ^ section16SimultaneousExponent k p (Nat.floor (Qb sigma))) ≤ (S j).width) ∧
      (∀ j, IsLastCoordinateBoxProduct (S j) (T j) (J j)) ∧
      ∀ j x, x ∈ G → x ∈ H → x ∈ (T j).carrier →
        LinearOn ((J j).carrier ∩ A x) (f x) := by
  obtain ⟨C, p, hC, hp, hassembly⟩ := exists_polynomial_spectrum_product_linearity k
  exact ⟨C, p, hC, hp, uniformPolynomialSpectrumProductLinearityAt_of k hC hp hassembly⟩

end LeanProofs.GowersSzemeredi
