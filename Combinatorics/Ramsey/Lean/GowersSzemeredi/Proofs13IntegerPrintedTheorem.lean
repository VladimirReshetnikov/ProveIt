import GowersSzemeredi.Proofs13IntegerSquareBounds

/-! Theorem 13.12 with genuine integer representatives, the printed
length and density bounds, and no extra modulus threshold. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem ModAP.step_ne_zero_of_proper_two {N : Nat} [NeZero N] (P : ModAP N)
    (hP : P.IsProper) (hlen : 2 ≤ P.length) : P.step ≠ 0 := by
  classical
  intro hzero
  have hinj := section5IndexPoint_injective_on_range P hP
  have h01 : section5IndexPoint P 0 = section5IndexPoint P 1 := by
    simp only [section5IndexPoint, hzero, mul_zero, add_zero]
  have h := hinj (Finset.mem_range.mpr (by omega : 0 < P.length))
    (Finset.mem_range.mpr (by omega : 1 < P.length)) h01
  omega

theorem theorem_13_12_integer_all_prime {N : Nat} [NeZero N] [Fact N.Prime]
    (alpha : Real) (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (f : ZMod N → Complex) (hf : DiscValued f) (hnot : ¬ UniformOfDegree f alpha 3) :
    ∃ P Q : ModAP N, ∃ B : Finset (Pair N), ∃ phi : Pair N → ZMod N,
      P.step ≠ 0 ∧ P.step = Q.step ∧ P.HasIntegerRepresentatives ∧
      Q.HasIntegerRepresentatives ∧ P.length = Q.length ∧
      (N : Real) ^ ((1 / 2 : Real) ^ ((1 / alpha) ^ ((2 : Nat) ^ 70))) ≤ P.length ∧
      B ⊆ P.carrier.product Q.carrier ∧
      (alpha / 2) ^ ((2 : Nat) ^ 76) * P.length * Q.length ≤ B.card ∧
      BilinearOn (P.carrier.product Q.carrier) phi ∧
      ∀ z, z ∈ B → alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖ := by
  classical
  by_cases hnear : 333 / 334 < alpha
  · exact theorem_13_12_integer_near_one alpha hnear ha1 f hf hnot
  have hau : alpha ≤ 1023 / 1024 := by linarith only [hnear]
  by_cases hsmall : (N : Real) ^ ((1 / 2 : Real) ^ ((1 / alpha) ^ ((2 : Nat) ^ 70))) ≤ 2
  · exact theorem_13_12_integer_small alpha ha ha1 hsmall f hf hnot
  have hN : Real.exp (Real.exp ((2 / alpha) ^ ((2 : Nat) ^ 54))) ≤ N := by
    by_contra h
    exact hsmall (section13_printed_width_small_below_threshold ha hau (le_of_not_ge h))
  obtain ⟨P, R, B, phi, _, hstep, hP, hR, hlen, hsize, hB, hmass, hbil, hfourier⟩ :=
    theorem_13_12_fejer_double_exponential alpha ha ha1 N hN f hf hnot
  let e := (1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 53))
  let epsilon := (1 / 2 : Real) ^ ((1 / alpha) ^ ((2 : Nat) ^ 70))
  let delta := (alpha / 2) ^ ((2 : Nat) ^ 42)
  let m := ⌈(N : Real) ^ epsilon⌉₊
  have hn : (1 : Real) ≤ N := by exact_mod_cast NeZero.pos N
  have hd : 0 < delta := pow_pos (by positivity) _
  have he : 0 < e := Real.rpow_pos_of_pos (by norm_num) _
  have heps : 0 < epsilon := Real.rpow_pos_of_pos (by norm_num) _
  obtain ⟨hgap, hthreshold⟩ := section13_integer_extraction_parameter_bounds ha hau
  have hlarge : 32 ≤ delta * (N : Real) ^ (e / 4) :=
    positivePowerThreshold_spec hd (by positivity) (hthreshold.trans hN)
  have hfit : (m : Real) ≤ delta * Real.sqrt P.length / 16 :=
    integer_square_width_absorption hn hd heps.le hgap hlarge hsize
  have hwidth : 2 < (N : Real) ^ epsilon := lt_of_not_ge hsmall
  have hmreal : 2 < (m : Real) := hwidth.trans_le (Nat.le_ceil _)
  have hm : 2 < m := by exact_mod_cast hmreal
  have hraw : 4 ≤ P.length := integer_square_raw_length_four hn heps.le hgap hwidth hsize
  obtain ⟨Q, T, E, hQ, hT, hQT, hQlen, hTlen, hQN, hTN, hQP, hTR, hEB, hE, hmassE⟩ :=
    dense_common_step_integer_square P R hP hR hlen hstep hraw B delta hd hB hmass
      m (by omega) hfit
  have hQrep := Q.toModAP_hasIntegerRepresentatives hQ hQN
  have hTrep := T.toModAP_hasIntegerRepresentatives hT hTN
  have hQmodlen : (Q.toModAP N).length = m := hQlen
  have hTmodlen : (T.toModAP N).length = m := hTlen
  have hcoef : (alpha / 2) ^ ((2 : Nat) ^ 76) ≤ delta / 16 :=
    power_density_sixteen_loss (by positivity) (by linarith only [ha1]) (by norm_num)
  refine ⟨Q.toModAP N, T.toModAP N, E, phi,
    (Q.toModAP N).step_ne_zero_of_proper_two hQrep.isProper (by rw [hQmodlen]; omega),
    congrArg (fun d : Nat => (d : ZMod N)) hQT, hQrep, hTrep,
    hQmodlen.trans hTmodlen.symm, ?_, hE, ?_, ?_, ?_⟩
  · rw [hQmodlen]
    exact Nat.le_ceil _
  · rw [hQmodlen, hTmodlen]
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef
      (Nat.cast_nonneg m)) (Nat.cast_nonneg m)).trans hmassE
  · obtain ⟨mu, hmu, hagree⟩ := hbil
    refine ⟨mu, hmu, fun z hz => hagree z ?_⟩
    exact Finset.product_subset_product hQP hTR hz
  · exact fun z hz => hfourier z (hEB hz)

def theorem_13_12_integer_representatives : Prop :=
  ∀ alpha : Real, 0 < alpha → alpha ≤ 1 →
    ∀ (N : Nat) [NeZero N] [Fact N.Prime],
      ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
        ∃ P Q : ModAP N, ∃ B : Finset (Pair N), ∃ phi : Pair N → ZMod N,
          P.step ≠ 0 ∧ P.step = Q.step ∧ P.HasIntegerRepresentatives ∧
          Q.HasIntegerRepresentatives ∧ P.length = Q.length ∧
          (N : Real) ^ ((1 / 2 : Real) ^ ((1 / alpha) ^ ((2 : Nat) ^ 70))) ≤ P.length ∧
          B ⊆ P.carrier.product Q.carrier ∧
          (alpha / 2) ^ ((2 : Nat) ^ 76) * P.length * Q.length ≤ B.card ∧
          BilinearOn (P.carrier.product Q.carrier) phi ∧
          ∀ z, z ∈ B → alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖

theorem theorem_13_12_integer_representatives_holds : theorem_13_12_integer_representatives := by
  intro alpha ha ha1 N _ _ f hf hnot
  exact theorem_13_12_integer_all_prime alpha ha ha1 f hf hnot

end LeanProofs.GowersSzemeredi
