import GowersSzemeredi.Proofs08AffineFrequencyProgression
import GowersSzemeredi.Proofs13OddFourierSquare

/-! Short odd progressions retain half the affine-frequency density. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- A padded cover of total capacity at most twice the original domain
retains half its density in one cell. -/
theorem exists_dense_equal_cover {X I : Type*} [DecidableEq X]
    [Fintype I] [Nonempty I] (S D : Finset X) (V : I → Finset X)
    (m : Nat) (delta : Real) (hδ : 0 ≤ delta) (hsub : D ⊆ S)
    (hcover : ∀ x ∈ S, ∃ i, x ∈ V i)
    (hcap : Fintype.card I * m ≤ 2 * S.card)
    (hmass : delta * S.card ≤ (D.card : Real)) :
    ∃ i, delta / 2 * m ≤ ((D ∩ V i).card : Real) := by
  classical
  have hD : D ⊆ Finset.univ.biUnion (fun i ↦ D ∩ V i) := by
    intro x hx
    obtain ⟨i, hi⟩ := hcover x (hsub hx)
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_inter.mpr ⟨hx, hi⟩⟩
  have hcount : (D.card : Real) ≤ ∑ i, ((D ∩ V i).card : Real) := by
    exact_mod_cast (Finset.card_le_card hD).trans Finset.card_biUnion_le
  have hcapR : (Fintype.card I : Real) * m ≤ 2 * S.card := by exact_mod_cast hcap
  have hs : ∑ _i : I, delta / 2 * m ≤ ∑ i, ((D ∩ V i).card : Real) := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h := mul_le_mul_of_nonneg_left hcapR (div_nonneg hδ (by norm_num : (0 : Real) ≤ 2))
    nlinarith only [h, hmass, hcount]
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hs
  exact ⟨i, hi⟩

/-- Select a progression of any prescribed shorter positive length,
retaining half the density and the original nonzero step. -/
theorem ModAP.dense_short_cover {N : Nat} [Fact N.Prime]
    (P : ModAP N) (D : Finset (ZMod N)) (delta : Real) (m : Nat)
    (hP : P.IsProper) (hstep : P.step != 0) (hm : 0 < m) (hml : m ≤ P.length)
    (hδ : 0 ≤ delta) (hD : D ⊆ P.carrier)
    (hmass : delta * P.length ≤ (D.card : Real)) :
    ∃ Q : ModAP N, ∃ E : Finset (ZMod N),
      Q.step = P.step ∧ Q.IsProper ∧ Q.length = m ∧ E ⊆ D ∧ E ⊆ Q.carrier ∧
      delta / 2 * m ≤ (E.card : Real) := by
  classical
  let I := Fin 1 × Fin (P.length / (1 * m) + 1)
  let V : I → ModAP N := commonStepCoverCell P 1 m
  letI : Nonempty I := ⟨(0, ⟨0, Nat.zero_lt_succ _⟩)⟩
  have hcap : Fintype.card I * m ≤ 2 * P.carrier.card := by
    rw [show P.carrier.card = P.length from hP]
    simpa only [I, Fintype.card_prod, Fintype.card_fin] using
      commonStepCoverCell_capacity P.length 1 m (by simpa only [one_mul] using hml)
  obtain ⟨i, hi⟩ := exists_dense_equal_cover P.carrier D (fun i ↦ (V i).carrier) m delta
    hδ hD (fun _ hx ↦ commonStepCoverCell_covers P (by omega) hm hx) hcap
    (by simpa only [show P.carrier.card = P.length from hP] using hmass)
  have hVs : (V i).step = P.step := by simp [V, commonStepCoverCell]
  have hmN : m ≤ N := hml.trans (by
    rw [← hP]
    simpa only [ZMod.card] using Finset.card_le_univ P.carrier)
  exact ⟨V i, D ∩ (V i).carrier, hVs,
    (V i).isProper_of_prime_step (by rwa [hVs]) hmN,
    rfl, Finset.inter_subset_left, Finset.inter_subset_right, hi⟩

/-- The quadratic affine-frequency exponent is positive and below one half. -/
theorem quadratic_frequency_exponent_bounds {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    0 < cor711Exponent ((alpha / 2) ^ (12359 : Nat)) 1 ∧
      cor711Exponent ((alpha / 2) ^ (12359 : Nat)) 1 ≤ 1 / 2 := by
  have hd : (alpha / 2) ^ (12359 : Nat) ≤ 1 :=
    pow_le_one₀ (by positivity) (by linarith)
  have hd0 : 0 ≤ (alpha / 2) ^ (12359 : Nat) := by positivity
  have hpow := pow_le_one₀ hd0 hd (n := 2)
  have hc : (2 : Real) ^ (-(14 : Real)) = 1 / 16384 := by
    rw [Real.rpow_neg (by norm_num : (0 : Real) ≤ 2)]
    norm_num
  unfold cor711Exponent
  constructor
  · positivity
  · simp only [Nat.cast_one, inv_one, mul_one, hc]
    calc
      _ ≤ (1 / 16384 : Real) * 1 := mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ ≤ _ := by norm_num

/-- An odd affine Fourier progression of length at most sqrt(N), with an
explicit power lower bound and half the previous relative density. -/
theorem quadratic_nonuniformity_odd_affine_frequencies :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 → ∃ N₀ : Nat,
      ∀ (N : Nat) [NeZero N] [Fact N.Prime], N₀ ≤ N →
        ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 2 →
        ∃ m : Nat, ∃ P : ModAP N, ∃ D : Finset (ZMod N), ∃ a b : ZMod N,
          Odd m ∧ 0 < m ∧ (m : Real) ≤ Real.sqrt N ∧
          (N : Real) ^ cor711Exponent ((alpha / 2) ^ (12359 : Nat)) 1 / 2 ≤ m ∧
          P.step != 0 ∧ P.IsProper ∧ P.length = m ∧ D ⊆ P.carrier ∧
          (alpha / 2) ^ (12359 : Nat) / 2 * m ≤ (D.card : Real) ∧
          ∀ x ∈ D, alpha / 2 * N ≤ ‖fourier (difference f x) (a * x + b)‖ := by
  intro alpha hα hαone
  let e := cor711Exponent ((alpha / 2) ^ (12359 : Nat)) 1
  obtain ⟨he, hehalf⟩ := quadratic_frequency_exponent_bounds hα hαone
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (eventually_nat_mul_rpow_le (C := 4) (D := 1) he zero_lt_one)
  refine ⟨N₀, fun N _ _ hN f hf hnot ↦ ?_⟩
  have hlarge : 4 ≤ (N : Real) ^ e := by
    simpa only [Real.rpow_zero, mul_one, one_mul] using hN₀ N hN
  obtain ⟨m, hodd, hm, hmlower, hmupper⟩ := exists_odd_nat_between_half hlarge
  obtain ⟨R, B, a, b, hs, hR, hB, hl, hmass, hfourier⟩ :=
    quadratic_nonuniformity_affine_frequencies N f alpha hα hαone hf hnot
  have hml : m ≤ R.length := by exact_mod_cast hmupper.trans hl
  obtain ⟨P, D, hPs, hP, hPl, hDB, hDP, hmass'⟩ :=
    R.dense_short_cover B ((alpha / 2) ^ (12359 : Nat)) m hR hs hm hml (by positivity) hB hmass
  have hNreal : (1 : Real) ≤ N := by exact_mod_cast NeZero.pos N
  have hmsqrt : (m : Real) ≤ Real.sqrt N := by
    calc
      _ ≤ (N : Real) ^ e := hmupper
      _ ≤ (N : Real) ^ (1 / 2 : Real) := Real.rpow_le_rpow_of_exponent_le hNreal hehalf
      _ = _ := (Real.sqrt_eq_rpow _).symm
  exact ⟨m, P, D, a, b, hodd, hm, hmsqrt, hmlower, by rwa [hPs],
    hP, hPl, hDP, hmass', fun x hx ↦ hfourier x (hDB hx)⟩

end LeanProofs.GowersSzemeredi
