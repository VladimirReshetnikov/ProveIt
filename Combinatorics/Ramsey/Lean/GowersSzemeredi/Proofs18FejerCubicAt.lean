import GowersSzemeredi.Proofs18FejerCubicDiscrepancy

/-! The Fejér cubic chain at any square exponent (Notes L.7c, P4–P9).

The corpus derives the cubic function discrepancy bound
`fejer_cubic_function_discrepancy_bound` from the Fejér square extraction
`theorem_13_12_fejer_extraction_explicit`. Every step in between (the odd
square, cubic localization, the many prime models, the twisted partition and
the untwisting) fixes the exponent
`fejerCubicLocalizationExponent α = (1/2)^((2/α)^(2^53))`. That double
exponential becomes the discrepancy exponent σ of degree three.

None of those steps uses the shape of the exponent. Here the chain starts
from an abstract square extraction:
* `FejerSquareAt α e T`: above `T`, a cubically non-uniform disc-valued
  function has a Fejér square of side at least `N^e`;
* `FejerOddSquareAt α e T`: the odd-square form consumed by the Section 17
  localization.

The chain ends in `FejerSquareAt.functionDiscrepancyBound`:
`FunctionDiscrepancyBound 3 α β σ T'` with the corpus's β and with
`σ = phaseInverseExponent 3 (e·κ)`, where `κ` is the corpus local count
exponent. The corpus bound is the instance at `fejerSquareAt_corpus`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

/-- A Fejér square extraction at exponent `e` above `T`. -/
def FejerSquareAt (alpha e T : Real) : Prop :=
  ∀ (N : Nat) [NeZero N] [Fact N.Prime], T ≤ N →
    ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
    ∃ P Q : ModAP N, ∃ B : Finset (Pair N), ∃ phi : Pair N → ZMod N,
      P.step != 0 ∧ P.step = Q.step ∧ P.IsProper ∧ Q.IsProper ∧ P.length = Q.length ∧
      (N : Real) ^ e ≤ P.length ∧
      B ⊆ P.carrier.product Q.carrier ∧
      (alpha / 2) ^ ((2 : Nat) ^ 42) * P.length * Q.length ≤ B.card ∧
      BilinearOn (P.carrier.product Q.carrier) phi ∧
      ∀ z, z ∈ B → alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖

/-- An odd Fejér square extraction at exponent `e` above `T`. -/
def FejerOddSquareAt (alpha e T : Real) : Prop :=
  ∀ (N : Nat) [NeZero N] [Fact N.Prime], T ≤ N →
    ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
    ∃ m : Nat, ∃ P Q : ModAP N, ∃ B : Finset (Pair N), ∃ phi : Pair N → ZMod N,
      Odd m ∧ 0 < m ∧ (m : Real) ≤ Real.sqrt N ∧ (N : Real) ^ e / 2 ≤ m ∧
      P.step != 0 ∧ P.step = Q.step ∧ P.IsProper ∧ Q.IsProper ∧ P.length = m ∧ Q.length = m ∧
      B ⊆ P.carrier.product Q.carrier ∧
      (alpha / 2) ^ ((2 : Nat) ^ 42) / 4 * m * m ≤ B.card ∧
      BilinearOn (P.carrier.product Q.carrier) phi ∧
      ∀ z, z ∈ B → alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖

/-- The corpus extraction is an instance. -/
theorem fejerSquareAt_corpus {alpha : Real} (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    FejerSquareAt alpha (section13SquareExponent ((alpha / 2) ^ (4207554485 : Nat)))
      (section13FourierThreshold alpha) :=
  theorem_13_12_fejer_extraction_explicit alpha hα hαone

/-- A smaller exponent is weaker. -/
theorem FejerSquareAt.mono {alpha e e' T : Real} (h : FejerSquareAt alpha e T) (he : e' ≤ e) :
    FejerSquareAt alpha e' (max 1 T) := by
  intro N _ _ hN f hf hnot
  obtain ⟨P, Q, B, phi, h1, h2, h3, h4, h5, hsize, h7, h8, h9, h10⟩ :=
    h N ((le_max_right _ _).trans hN) f hf hnot
  have hN1 : (1 : Real) ≤ N := (le_max_left _ _).trans hN
  exact ⟨P, Q, B, phi, h1, h2, h3, h4, h5,
    (Real.rpow_le_rpow_of_exponent_le hN1 he).trans hsize, h7, h8, h9, h10⟩

/-- **The odd square** at any exponent in `(0, 1/2]`. -/
theorem FejerSquareAt.oddSquare {alpha e T : Real} (h : FejerSquareAt alpha e T)
    (hα : 0 < alpha) (he : 0 < e) (hehalf : e ≤ 1 / 2) :
    FejerOddSquareAt alpha e (max T (positivePowerThreshold 4 1 e)) := by
  intro N _ _ hN f hf hnot
  have hlarge : 4 ≤ (N : Real) ^ e := by
    have h4 := positivePowerThreshold_spec zero_lt_one he
      ((le_max_right _ _).trans hN : positivePowerThreshold 4 1 e ≤ (N : Real))
    simpa only [one_mul] using h4
  obtain ⟨m, hmodd, hmpos, hmlower, hmupper⟩ := exists_odd_nat_between_half hlarge
  obtain ⟨S, T, D, psi, hSs, hST, hS, hT, hlen, hsize, hD, hmass, hbil, hfourier⟩ :=
    h N ((le_max_left _ _).trans hN) f hf hnot
  have hmS : m ≤ S.length := by exact_mod_cast hmupper.trans hsize
  have hmT : m ≤ T.length := by omega
  have hTstep : T.step != 0 := by rwa [← hST]
  obtain ⟨mu, hmu, hagree⟩ := hbil
  have hbilD : BilinearOn D psi := ⟨mu, hmu, fun z hz => hagree z (hD hz)⟩
  obtain ⟨P, Q, B, hPs, hQs, hP, hQ, hPl, hQl, hBD, hbox, hmass', _⟩ :=
    bilinear_square_of_integer_step_fit S T D psi ((alpha / 2) ^ ((2 : Nat) ^ 42)) 1 m
      hS hT hTstep (by simpa only [Nat.cast_one, one_mul] using hST.symm)
      (by omega) hmpos (by simpa only [one_mul] using hmS) hmT (by positivity) hD hmass hbilD
  have hNreal : (1 : Real) ≤ N := by exact_mod_cast NeZero.pos N
  have hmsqrt : (m : Real) ≤ Real.sqrt N := by
    calc
      _ ≤ (N : Real) ^ e := hmupper
      _ ≤ (N : Real) ^ (1 / 2 : Real) := Real.rpow_le_rpow_of_exponent_le hNreal hehalf
      _ = _ := (Real.sqrt_eq_rpow _).symm
  refine ⟨m, P, Q, B, mu, hmodd, hmpos, hmsqrt, hmlower, ?_, hPs.trans hQs.symm,
    hP, hQ, hPl, hQl, hbox, hmass', ⟨mu, hmu, fun _ _ => rfl⟩, ?_⟩
  · rwa [hPs]
  · intro z hz
    rw [← hagree z (hD (hBD hz))]
    exact hfourier z (hBD hz)

/-- **Cubic localization** (Section 17) at any odd-square exponent. -/
theorem FejerOddSquareAt.localized {alpha e T : Real} (h : FejerOddSquareAt alpha e T)
    (hα : 0 < alpha) :
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], T ≤ N →
      ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
      ∃ phi : ZMod N → ZMod N, ∃ M l : Nat, ∃ Q : Fin M → ModAP N,
        PolynomialOn 3 Finset.univ phi ∧
        IsPartition (fun i => (Q i).carrier) Finset.univ ∧
        (∀ i, (Q i).IsProper ∧ ((Q i).length = l ∨ (Q i).length = l + 1)) ∧
        (N : Real) ^ e / 12 ≤ l ∧
        (∀ i, ((Q i).length : Real) ≤ Real.sqrt N) ∧
        ¬ UniformOnPartition (phaseTwist f phi) 2
          ((2 : Real) ^ (-(58 : Int)) * alpha ^ 2 * (alpha / 2) ^ ((2 : Nat) ^ 42)) Q (l + 1) := by
  intro N _ _ hN f hf hnot
  obtain ⟨m, P, R, B, psi, hmodd, hmpos, hmsqrt, hsize, hPs, hPR, hP, hR,
    hPl, hRl, hB, hmass, hbil, hfourier⟩ := h N hN f hf hnot
  obtain ⟨mu, hmu, hagree⟩ := hbil
  let delta := (alpha / 2) ^ ((2 : Nat) ^ 42) / 4
  let rho := delta * alpha ^ 2 / 4
  let S := fourierSquareBox P R hPR
  let sigma : Point N 2 → ZMod N := fun x => mu ((fourierSquareEquiv N).symm x)
  have hrho : 0 < rho := by dsimp [rho, delta]; positivity
  have hlarge : ∀ z, z ∈ B → alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (mu z)‖ := by
    intro z hz
    rw [← hagree z (hB hz)]
    exact hfourier z hz
  have henergy := fourierSquare_energy P R hPR B f mu alpha delta hα.le hB hmass hlarge
  obtain ⟨phi, M, l, Q, hpoly, hpartition, hproper, hlength, hupper, hnonuniform⟩ :=
    proposition_17_7_with_upper N 2 m f S sigma rho hrho (by omega) hmodd
      (fourierSquareBox_width P R hPR hPl hRl)
      (fourierSquareBox_axis_length P R hPR hPl hRl) hPs hmsqrt hf hmu.to_multilinear henergy
  have hconstant : (2 : Real) ^ (-(2 * (2 + 1) ^ 3 : Int)) * rho =
      (2 : Real) ^ (-(58 : Int)) * alpha ^ 2 * (alpha / 2) ^ ((2 : Nat) ^ 42) := by
    dsimp [rho, delta]
    generalize (alpha / 2) ^ ((2 : Nat) ^ 42) = a
    norm_num
    ring
  refine ⟨phi, M, l, Q, hpoly, hpartition, hproper, ?_, ?_, ?_⟩
  · norm_num only [Nat.cast_ofNat] at hlength
    linarith only [hsize, hlength]
  · intro i
    exact (by exact_mod_cast hupper i : ((Q i).length : Real) ≤ m).trans hmsqrt
  · simpa only [Nat.cast_ofNat, hconstant] using hnonuniform

def fejerCubicPrimeModelThresholdAt (e T₀ T : Real) : Real :=
  max 256 (max T₀ (positivePowerThreshold (12 * max 2 T) 1 e))

/-- **Many comparable prime models** at any odd-square exponent. -/
theorem FejerOddSquareAt.manyPrimeModels {alpha e T₀ : Real} (h : FejerOddSquareAt alpha e T₀)
    (T : Real) (hα : 0 < alpha) (he : 0 < e) :
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], fejerCubicPrimeModelThresholdAt e T₀ T ≤ N →
      ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
      ∃ phi : ZMod N → ZMod N, ∃ K l : Nat, ∃ Q : Fin K → ModAP N,
        PolynomialOn 3 Finset.univ phi ∧
        IsPartition (fun i => (Q i).carrier) Finset.univ ∧
        (∀ i, (Q i).IsProper ∧ ((Q i).length = l ∨ (Q i).length = l + 1)) ∧
        (N : Real) ^ e / 12 ≤ l ∧
        ∃ B : Finset (Fin K),
          fejerCubicLocalizedMassParameter alpha * N < ∑ i ∈ B, ((Q i).carrier.card : Real) ∧
          ∀ i ∈ B, ∃ M : Nat, ∃ hM : M.Prime,
            letI : NeZero M := ⟨hM.ne_zero⟩
            T ≤ (M : Real) ∧ 4 * (Q i).length < M ∧ M ≤ 8 * (Q i).length ∧
            (M : Real) ≤ (N : Real) / 2 ∧
            DiscValued (intervalExtension M ((Q i).pullbackFunction (phaseTwist f phi))) ∧
            ¬ UniformOfDegree (intervalExtension M ((Q i).pullbackFunction (phaseTwist f phi)))
              (fejerCubicLocalQuadraticParameter alpha) 2 := by
  let beta := (2 : Real) ^ (-(58 : Int)) * alpha ^ 2 * (alpha / 2) ^ ((2 : Nat) ^ 42)
  have hβ : 0 < beta := by dsimp [beta]; positivity
  intro N _ _ hN f hf hnot
  have hNloc : T₀ ≤ (N : Real) := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  obtain ⟨phi, K, l, Q, hpoly, hpart, hproper, hlength, hupper, hfail⟩ :=
    h.localized hα N hNloc f hf hnot
  have hlarge : 12 * max 2 T ≤ (N : Real) ^ e := by
    simpa only [one_mul] using positivePowerThreshold_spec zero_lt_one he
      ((le_max_right _ _).trans ((le_max_right _ _).trans hN) :
        positivePowerThreshold (12 * max 2 T) 1 e ≤ (N : Real))
  have hlmax : max 2 T ≤ (l : Real) := by linarith only [hlarge, hlength]
  have hl : 2 ≤ l := by exact_mod_cast ((le_max_left 2 T).trans hlmax)
  have hlT : T ≤ (l : Real) := (le_max_right 2 T).trans hlmax
  have hNreal : (256 : Real) ≤ N := (le_max_left _ _).trans hN
  have hroot0 := Real.sqrt_nonneg (N : Real)
  have hrootsq := Real.sq_sqrt (Nat.cast_nonneg N : (0 : Real) ≤ N)
  have hroot : 16 ≤ Real.sqrt N := by nlinarith only [hNreal, hroot0, hrootsq]
  have hrootprod := mul_nonneg hroot0 (sub_nonneg.mpr hroot)
  have hrootupper : 8 * Real.sqrt N ≤ (N : Real) / 2 := by nlinarith only [hrootsq, hrootprod]
  have hgeom (i : Fin K) : 2 ≤ (Q i).length ∧ (Q i).length ≤ l + 1 ∧
      (2 + 2) * (Q i).length ≤ N := by
    have hU := hupper i
    have hs : (4 : Real) * (Q i).length ≤ N := by nlinarith only [hU, hrootupper, hNreal]
    have hs' : 4 * (Q i).length ≤ N := by exact_mod_cast hs
    rcases (hproper i).2 with hi | hi <;> omega
  obtain ⟨B, hmass, hB⟩ := partition_nonuniformity_prime_models
    (phaseTwist f phi) Q beta (phaseTwist_discValued hf phi) hβ.le
    (by omega) hpart (fun i => (hproper i).1) hgeom hfail
  have hmassparam : beta / 2 = fejerCubicLocalizedMassParameter alpha := by
    dsimp [beta, fejerCubicLocalizedMassParameter]
    generalize (alpha / 2) ^ ((2 : Nat) ^ 42) = a
    norm_num
    ring
  have hparam : (beta / 2) / (2 * (2 + 2 : Nat) : Real) ^ (2 + 2) =
      fejerCubicLocalQuadraticParameter alpha := by
    dsimp [beta, fejerCubicLocalQuadraticParameter]
    generalize (alpha / 2) ^ ((2 : Nat) ^ 42) = a
    norm_num
    ring
  refine ⟨phi, K, l, Q, hpoly, hpart, hproper, hlength, B, ?_, ?_⟩
  · simpa only [hmassparam] using hmass
  · intro i hi
    obtain ⟨M, hM, hMlow, hMup, hdisc, hnew⟩ := hB i hi
    letI : NeZero M := ⟨hM.ne_zero⟩
    have hM8 : M ≤ 8 * (Q i).length := by omega
    have hMhalf : (M : Real) ≤ (N : Real) / 2 := by
      have hMr : (M : Real) ≤ 8 * (Q i).length := by exact_mod_cast hM8
      have hU := hupper i
      nlinarith only [hMr, hU, hrootupper]
    have hlM : l ≤ M := by
      have hli : l ≤ (Q i).length := by rcases (hproper i).2 with h | h <;> omega
      omega
    refine ⟨M, hM, hlT.trans (by exact_mod_cast hlM), hMlow, hM8, hMhalf, hdisc, ?_⟩
    simpa only [hparam] using hnew

def fejerCubicTwistedThresholdAt (alpha e T₀ : Real) : Real :=
  fejerCubicPrimeModelThresholdAt e T₀
    (max 4 (quadraticExponentialThreshold (fejerCubicLocalQuadraticParameter alpha)))

/-- **The twisted discrepancy partition** at any odd-square exponent. -/
theorem FejerOddSquareAt.twistedDiscrepancy {alpha e T₀ : Real} (h : FejerOddSquareAt alpha e T₀)
    (hα : 0 < alpha) (hαone : alpha ≤ 1) (he : 0 < e) :
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], fejerCubicTwistedThresholdAt alpha e T₀ ≤ (N : Real) →
      ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
      ∃ phi : ZMod N → ZMod N, ∃ l J : Nat, ∃ R : Fin J → ModAP N,
        PolynomialOn 3 Finset.univ phi ∧
        (N : Real) ^ e / 12 ≤ l ∧
        IsPartition (fun j => (R j).carrier) Finset.univ ∧
        (∀ j, (R j).IsProper) ∧
        (J : Real) ≤ fejerCubicLocalCountConstant alpha * N /
          (l : Real) ^ fejerCubicLocalCountExponent alpha ∧
        fejerCubicTwistedDiscrepancyParameter alpha * N ≤
          ∑ j, ‖∑ x ∈ (R j).carrier, phaseTwist f phi x‖ := by
  let a := fejerCubicLocalQuadraticParameter alpha
  let b := quadraticDiscrepancyParameter a
  have ha : 0 < a := fejerCubicLocalQuadraticParameter_pos hα
  have haone : a ≤ 1 := fejerCubicLocalQuadraticParameter_le_one hα.le hαone
  have hb : 0 < b := by dsimp [b, quadraticDiscrepancyParameter]; positivity
  obtain ⟨ht, htone⟩ := fejerCubicLocalCountExponent_bounds hα hαone
  intro N _ _ hN f hf hnot
  obtain ⟨phi, K, l, Q, hpoly, hQ, hproper, hlength, B, hmass, hB⟩ :=
    h.manyPrimeModels (max 4 (quadraticExponentialThreshold a)) hα he N hN f hf hnot
  have hNr : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hlpos : (0 : Real) < l :=
    (by positivity : 0 < (N : Real) ^ e / 12).trans_le hlength
  have hl : 1 ≤ l := by
    have hh : 0 < l := by exact_mod_cast hlpos
    omega
  have hσ : 0 ≤ quadraticDiscrepancyExponent a := by
    change 0 < quadraticDiscrepancyExponent a / 16 at ht
    linarith only [ht]
  have hσ16 : quadraticDiscrepancyExponent a ≤ 16 := by
    change quadraticDiscrepancyExponent a / 16 ≤ 1 at htone
    linarith only [htone]
  have hmodels (i : Fin K) (hi : i ∈ B) : ∃ M : Nat, ∃ hM : M.Prime,
      letI : NeZero M := ⟨hM.ne_zero⟩
      4 ≤ M ∧ (Q i).length ≤ M ∧ quadraticExponentialThreshold a ≤ (M : Real) ∧
      (M : Real) ≤ 8 * (Q i).length ∧
      ¬ UniformOfDegree (intervalExtension M ((Q i).pullbackFunction (phaseTwist f phi))) a 2 := by
    obtain ⟨M, hM, hT, hMlow, hMup, _, _, hnon⟩ := hB i hi
    letI : NeZero M := ⟨hM.ne_zero⟩
    refine ⟨M, hM, ?_, by omega, (le_max_right _ _).trans hT, ?_, hnon⟩
    · exact_mod_cast ((le_max_left _ _).trans hT : (4 : Real) ≤ M)
    · exact_mod_cast hMup
  obtain ⟨J, R, hR, hp, hc, hd⟩ :=
    (quadratic_function_discrepancy_bound ha haone).selected_prime_model_partition
      hb.le hσ hσ16 (by norm_num : (0 : Real) ≤ 8)
      (phaseTwist f phi) (phaseTwist_discValued hf phi) Q B hQ (fun i => (hproper i).1) hl
      (fun i => by rcases (hproper i).2 with hi | hi <;> omega) hmodels
  refine ⟨phi, l, J, R, hpoly, hlength, hR, hp, hc, ?_⟩
  have hm := mul_le_mul_of_nonneg_left hmass.le hb.le
  have hm' : fejerCubicTwistedDiscrepancyParameter alpha * N ≤
      b * ∑ i ∈ B, ((Q i).carrier.card : Real) := by
    change (fejerCubicLocalizedMassParameter alpha * b) * N ≤ _
    nlinarith only [hm]
  exact hm'.trans hd

/-- The common-cell-length count as a power of the modulus, at any exponent. -/
theorem fejer_cubic_twisted_count_power_at {alpha e : Real} (hα : 0 < alpha)
    (hαone : alpha ≤ 1) {N l J : Nat} [NeZero N]
    (hl : (N : Real) ^ e / 12 ≤ l)
    (hcount : (J : Real) ≤ fejerCubicLocalCountConstant alpha * N /
      (l : Real) ^ fejerCubicLocalCountExponent alpha) :
    (J : Real) ≤ fejerCubicTwistedCountConstant alpha *
      (N : Real) ^ (1 - e * fejerCubicLocalCountExponent alpha) := by
  let t := fejerCubicLocalCountExponent alpha
  let D := fejerCubicLocalCountConstant alpha
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have ht : 0 < t := (fejerCubicLocalCountExponent_bounds hα hαone).1
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hbase : 0 < (N : Real) ^ e / 12 := by positivity
  have hpow := Real.rpow_le_rpow hbase.le hl ht.le
  calc
    (J : Real) ≤ D * N / (l : Real) ^ t := hcount
    _ ≤ D * N / ((N : Real) ^ e / 12) ^ t :=
      div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hbase t) hpow
    _ = fejerCubicTwistedCountConstant alpha * (N : Real) ^ (1 - e * t) := by
      rw [Real.div_rpow (Real.rpow_nonneg hN.le _) (by norm_num : (0 : Real) ≤ 12),
        ← Real.rpow_mul hN.le, Real.rpow_sub hN, Real.rpow_one]
      change D * N / ((N : Real) ^ (e * t) / (12 : Real) ^ t) =
        (D * (12 : Real) ^ t) * ((N : Real) / (N : Real) ^ (e * t))
      field_simp

/-- The degree-three discrepancy exponent from a square exponent `e`. -/
def fejerCubicDiscrepancyExponentAt (alpha e : Real) : Real :=
  phaseInverseExponent 3 (e * fejerCubicLocalCountExponent alpha)

def fejerCubicInverseThresholdAt (alpha e T₀ : Real) : Real :=
  max (fejerCubicTwistedThresholdAt alpha e T₀)
    (positivePowerThreshold
      (phaseInverseConstant 3 (fejerCubicTwistedDiscrepancyParameter alpha)
        (fejerCubicTwistedCountConstant alpha)) 1
      (fejerCubicDiscrepancyExponentAt alpha e))

/-- **The cubic function discrepancy bound** from an odd square at exponent `e`. -/
theorem FejerOddSquareAt.functionDiscrepancyBound {alpha e T₀ : Real}
    (h : FejerOddSquareAt alpha e T₀) (hα : 0 < alpha) (hαone : alpha ≤ 1) (he : 0 < e) :
    FunctionDiscrepancyBound 3 alpha (fejerCubicDiscrepancyParameter alpha)
      (fejerCubicDiscrepancyExponentAt alpha e) (fejerCubicInverseThresholdAt alpha e T₀) := by
  let et := e * fejerCubicLocalCountExponent alpha
  let beta := fejerCubicTwistedDiscrepancyParameter alpha
  let D := fejerCubicTwistedCountConstant alpha
  have het : 0 < et := mul_pos he (fejerCubicLocalCountExponent_bounds hα hαone).1
  have hβ : 0 < beta := by
    have h2 := fejerCubicDiscrepancyParameter_pos hα
    change 0 < beta / 2 at h2
    linarith only [h2]
  have hD : 0 < D := by
    have h1 := lt_of_lt_of_le zero_lt_one (le_max_left (1 : Real)
      (2 * boundaryRefinementConstant (1 / 16) * (8 : Real) ^ (1 - fejerCubicLocalCountExponent alpha)))
    dsimp [D, fejerCubicTwistedCountConstant, fejerCubicLocalCountConstant]
    positivity
  intro N _ _ hN f hf hnot
  obtain ⟨phi, l, K, Q, hpoly, hlength, hQ, _, hcount, hdis⟩ :=
    h.twistedDiscrepancy hα hαone he N ((le_max_left _ _).trans hN) f hf hnot
  have hcount' : (K : Real) ≤ D * (N : Real) ^ (1 - et) :=
    fejer_cubic_twisted_count_power_at hα hαone hlength hcount
  exact polynomial_phase_inverse_partition (by omega : 1 ≤ 3) het hβ hD f hf
    Q (fun _ => phi) (fun _ => hpoly) hQ hcount' hdis ((le_max_right _ _).trans hN)

/-- **From a square extraction to the cubic discrepancy bound**, at any
square exponent in `(0, 1/2]`. -/
theorem FejerSquareAt.functionDiscrepancyBound {alpha e T : Real} (h : FejerSquareAt alpha e T)
    (hα : 0 < alpha) (hαone : alpha ≤ 1) (he : 0 < e) (hehalf : e ≤ 1 / 2) :
    FunctionDiscrepancyBound 3 alpha (fejerCubicDiscrepancyParameter alpha)
      (fejerCubicDiscrepancyExponentAt alpha e)
      (fejerCubicInverseThresholdAt alpha e (max T (positivePowerThreshold 4 1 e))) :=
  (h.oddSquare hα he hehalf).functionDiscrepancyBound hα hαone he

end LeanProofs.GowersSzemeredi
