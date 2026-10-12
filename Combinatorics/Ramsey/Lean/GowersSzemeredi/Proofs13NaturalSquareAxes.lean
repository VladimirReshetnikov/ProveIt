import GowersSzemeredi.Proofs13IntegerPrintedTheorem

/-! The printed Fourier square with two actual natural-number axes sharing
one positive integer step. Equality of modular steps and separate integer
representatives are weaker than this explicit geometric certificate. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

private theorem naturalAxis_isProper_of_step_pos (P : NatAP) (hp : 0 < P.step) : P.IsProper := by
  classical
  refine ⟨hp, ?_⟩
  unfold NatAP.carrier
  rw [Finset.card_image_of_injective]
  · simp
  · intro i j hij
    apply Fin.ext
    exact Nat.mul_right_cancel hp (Nat.add_left_cancel hij)

theorem NatAP.carrier_subset_range_of_terms (P : NatAP) {N : Nat}
    (h : ∀ i : Nat, i < P.length → P.start + i * P.step < N) :
    P.carrier ⊆ Finset.range N := by
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_range.mpr (h i i.isLt)

theorem NatAP.bounded_axis_certificate (P : NatAP) {N : Nat}
    (hp : 0 < P.step)
    (hN : ∀ i : Nat, i < P.length → P.start + i * P.step < N) :
    P.IsProper ∧ P.carrier ⊆ Finset.range N :=
  ⟨naturalAxis_isProper_of_step_pos P hp, P.carrier_subset_range_of_terms hN⟩

theorem adjacentIntegerAP_nat_properties {N : Nat} [NeZero N]
    (hN : 2 ≤ N) (x : ZMod N) :
    (adjacentIntegerAP x).IsProper ∧ (adjacentIntegerAP x).carrier ⊆ Finset.range N := by
  refine ⟨naturalAxis_isProper_of_step_pos _ (by simp [adjacentIntegerAP]), ?_⟩
  apply NatAP.carrier_subset_range_of_terms
  intro i hi
  change i < 2 at hi
  change min x.val (N - 2) + i * 1 < N
  have := min_le_right x.val (N - 2)
  omega

/-- An explicit positive-step square certificate, preserving all printed
width, density, bilinear and Fourier conditions. -/
def NaturalFourierSquare {N : Nat} [NeZero N]
    (alpha : Real) (f : ZMod N → Complex) : Prop :=
  ∃ P Q : NatAP, ∃ B : Finset (Pair N), ∃ phi : Pair N → ZMod N,
    P.IsProper ∧ Q.IsProper ∧ P.step = Q.step ∧
    (P.step : ZMod N) ≠ 0 ∧ P.length = Q.length ∧
    P.carrier ⊆ Finset.range N ∧ Q.carrier ⊆ Finset.range N ∧
    (N : Real) ^ ((1 / 2 : Real) ^ ((1 / alpha) ^ ((2 : Nat) ^ 70))) ≤ P.length ∧
    B ⊆ (P.toModAP N).carrier.product (Q.toModAP N).carrier ∧
    (alpha / 2) ^ ((2 : Nat) ^ 76) * P.length * Q.length ≤ B.card ∧
    BilinearOn ((P.toModAP N).carrier.product (Q.toModAP N).carrier) phi ∧
    ∀ z, z ∈ B → alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖

theorem theorem_13_12_natural_small {N : Nat} [NeZero N] [Fact N.Prime]
    (alpha : Real) (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hsize : (N : Real) ^ ((1 / 2 : Real) ^ ((1 / alpha) ^ ((2 : Nat) ^ 70))) ≤ 2)
    (f : ZMod N → Complex) (hf : DiscValued f) (hnot : ¬ UniformOfDegree f alpha 3) :
    NaturalFourierSquare alpha f := by
  classical
  have hN : 2 ≤ N := (Fact.out : Nat.Prime N).two_le
  obtain ⟨z, r, hlarge⟩ := cubic_nonuniformity_large_second_fourier alpha ha ha1 f hf hnot
  let P := adjacentIntegerAP z.1
  let Q := adjacentIntegerAP z.2
  let B : Finset (Pair N) := {z}
  let phi : Pair N → ZMod N := fun _ => r
  refine ⟨P, Q, B, phi, (adjacentIntegerAP_nat_properties hN _).1,
    (adjacentIntegerAP_nat_properties hN _).1, rfl, ?_, rfl,
    (adjacentIntegerAP_nat_properties hN _).2, (adjacentIntegerAP_nat_properties hN _).2,
    hsize, ?_, ?_, ?_, ?_⟩
  · simp [P, adjacentIntegerAP]
  · intro w hw
    have hwz : w = z := Finset.mem_singleton.mp hw
    subst w
    exact Finset.mem_product.mpr ⟨adjacentIntegerAP_mem hN _, adjacentIntegerAP_mem hN _⟩
  · have hhalf : alpha / 2 ≤ (1 / 2 : Real) := by linarith only [ha1]
    have hgamma1 : alpha / 2 ≤ 1 := by linarith only [ha1]
    have hcoef : (alpha / 2) ^ ((2 : Nat) ^ 76) ≤ (1 / 4 : Real) := by
      have hexp : 2 ≤ (2 : Nat) ^ 76 := by
        have h := Nat.lt_two_pow_self (n := 76)
        omega
      calc
        _ ≤ (alpha / 2) ^ (2 : Nat) :=
          pow_le_pow_of_le_one (by positivity) hgamma1 hexp
        _ ≤ (1 / 2 : Real) ^ (2 : Nat) := pow_le_pow_left₀ (by positivity) hhalf _
        _ = 1 / 4 := by norm_num
    change (alpha / 2) ^ ((2 : Nat) ^ 76) * (2 : Real) * 2 ≤ (B.card : Real)
    simp only [B, Finset.card_singleton, Nat.cast_one]
    exact (show ∀ b : Real, b ≤ 1 / 4 → b * 2 * 2 ≤ 1 from by
      intro b hb; linarith only [hb]) _ hcoef
  · exact ⟨phi, ⟨r, 0, 0, 0, by intro w; simp [phi]⟩, fun _ _ => rfl⟩
  · intro w hw
    have hwz : w = z := Finset.mem_singleton.mp hw
    subst w
    exact hlarge

theorem theorem_13_12_natural_near_one {N : Nat} [NeZero N] [Fact N.Prime]
    (alpha : Real) (hnear : 333 / 334 < alpha) (ha1 : alpha ≤ 1)
    (f : ZMod N → Complex) (hf : DiscValued f) (hnot : ¬ UniformOfDegree f alpha 3) :
    NaturalFourierSquare alpha f := by
  classical
  have ha : 0 < alpha := by linarith only [hnear]
  have hmean : 1 - (1 - alpha) ≤ endpointCubeMean f 4 := by
    have hgt := lt_of_not_ge ((uniformOfDegree_iff_endpointCubeMean (d := 3) f alpha).not.mp hnot)
    linarith only [hgt]
  obtain ⟨c, B, hmass, hfourier⟩ := endpoint_global_fourier f hf (1 - alpha) hmean
  let P : NatAP := ⟨0, 1, N⟩
  have hP : P.IsProper := naturalAxis_isProper_of_step_pos P (by simp [P])
  have hPN : P.carrier ⊆ Finset.range N := P.carrier_subset_range_of_terms
    (by intro i hi; simpa only [P, zero_add, mul_one] using hi)
  have hPuniv : (P.toModAP N).carrier = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro y
    exact Finset.mem_image.mpr ⟨⟨y.val, ZMod.val_lt y⟩, Finset.mem_univ _, by
      simp [P, NatAP.toModAP]⟩
  let phi : Pair N → ZMod N := fun z => c * z.1 * z.2
  refine ⟨P, P, B, phi, hP, hP, rfl, by simp [P], rfl, hPN, hPN,
    ?_, ?_, ?_, ?_, ?_⟩
  · have he : (1 / 2 : Real) ^ ((1 / alpha) ^ ((2 : Nat) ^ 70)) ≤ 1 :=
      Real.rpow_le_one (by norm_num) (by norm_num) (by positivity)
    exact (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast NeZero.pos N) he).trans_eq
      (by rw [Real.rpow_one])
  · rw [hPuniv]
    intro z _
    simp [Finset.product]
  · have hcoef : (alpha / 2) ^ ((2 : Nat) ^ 76) ≤ (1 / 256 : Real) := by
      have hE : 8 ≤ (2 : Nat) ^ 76 := by have h := Nat.lt_two_pow_self (n := 76); omega
      calc
        _ ≤ (alpha / 2) ^ (8 : Nat) :=
          pow_le_pow_of_le_one (by positivity) (by linarith only [ha1]) hE
        _ ≤ (1 / 2 : Real) ^ (8 : Nat) :=
          pow_le_pow_left₀ (by positivity) (by linarith only [ha1]) _
        _ = 1 / 256 := by norm_num
    have hcoefficient : (alpha / 2) ^ ((2 : Nat) ^ 76) ≤ 1 - 332 * (1 - alpha) :=
      (show ∀ a b : Real, 333 / 334 < a → b ≤ 1 / 256 → b ≤ 1 - 332 * (1 - a) from by
        intro a b h1 h2; linarith only [h1, h2]) _ _ hnear hcoef
    change (alpha / 2) ^ ((2 : Nat) ^ 76) * (N : Real) * N ≤ B.card
    calc
      _ = (alpha / 2) ^ ((2 : Nat) ^ 76) * (N : Real) ^ 2 := by rw [pow_two, mul_assoc]
      _ ≤ (1 - 332 * (1 - alpha)) * (N : Real) ^ 2 :=
        mul_le_mul_of_nonneg_right hcoefficient (sq_nonneg _)
      _ ≤ _ := hmass
  · exact ⟨phi, ⟨0, 0, 0, c, by intro z; simp [phi]⟩, fun _ _ => rfl⟩
  · intro z hz
    have hcoefficient : alpha / 2 ≤ 3 / 4 - 4 * (1 - alpha) := by linarith only [hnear, ha1]
    have hscaled := mul_le_mul_of_nonneg_right hcoefficient (Nat.cast_nonneg N : (0 : Real) ≤ N)
    have hgood := hfourier z hz
    change alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (c * z.1 * z.2)‖
    nlinarith only [hscaled, hgood]

theorem theorem_13_12_natural_all_prime {N : Nat} [NeZero N] [Fact N.Prime]
    (alpha : Real) (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (f : ZMod N → Complex) (hf : DiscValued f) (hnot : ¬ UniformOfDegree f alpha 3) :
    NaturalFourierSquare alpha f := by
  classical
  by_cases hnear : 333 / 334 < alpha
  · exact theorem_13_12_natural_near_one alpha hnear ha1 f hf hnot
  have hau : alpha ≤ 1023 / 1024 := by linarith only [hnear]
  by_cases hsmall : (N : Real) ^ ((1 / 2 : Real) ^ ((1 / alpha) ^ ((2 : Nat) ^ 70))) ≤ 2
  · exact theorem_13_12_natural_small alpha ha ha1 hsmall f hf hnot
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
  refine ⟨Q, T, E, phi, hQ, hT, hQT,
    (Q.toModAP N).step_ne_zero_of_proper_two hQrep.isProper (by rw [hQmodlen]; omega),
    hQlen.trans hTlen.symm, hQN, hTN, ?_, hE, ?_, ?_, ?_⟩
  · rw [hQlen]
    exact Nat.le_ceil _
  · rw [hQlen, hTlen]
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef
      (Nat.cast_nonneg m)) (Nat.cast_nonneg m)).trans hmassE
  · obtain ⟨mu, hmu, hagree⟩ := hbil
    refine ⟨mu, hmu, fun z hz => hagree z ?_⟩
    exact Finset.product_subset_product hQP hTR hz
  · exact fun z hz => hfourier z (hEB hz)

/-- The explicit natural-axis certificate implies the previous modular
statement, including separate integer representatives and its common step. -/
theorem NaturalFourierSquare.to_modular {N : Nat} [NeZero N]
    {alpha : Real} {f : ZMod N → Complex} (h : NaturalFourierSquare alpha f) :
    ∃ P Q : ModAP N, ∃ B : Finset (Pair N), ∃ phi : Pair N → ZMod N,
      P.step ≠ 0 ∧ P.step = Q.step ∧ P.HasIntegerRepresentatives ∧
      Q.HasIntegerRepresentatives ∧ P.length = Q.length ∧
      (N : Real) ^ ((1 / 2 : Real) ^ ((1 / alpha) ^ ((2 : Nat) ^ 70))) ≤ P.length ∧
      B ⊆ P.carrier.product Q.carrier ∧
      (alpha / 2) ^ ((2 : Nat) ^ 76) * P.length * Q.length ≤ B.card ∧
      BilinearOn (P.carrier.product Q.carrier) phi ∧
      ∀ z, z ∈ B → alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖ := by
  obtain ⟨P, Q, B, phi, hP, hQ, hstep, hnonzero, hlen, hPN, hQN,
    hwidth, hB, hmass, hbil, hfourier⟩ := h
  exact ⟨P.toModAP N, Q.toModAP N, B, phi, hnonzero,
    congrArg (fun d : Nat ↦ (d : ZMod N)) hstep,
    P.toModAP_hasIntegerRepresentatives hP hPN,
    Q.toModAP_hasIntegerRepresentatives hQ hQN,
    hlen, hwidth, hB, hmass, hbil, hfourier⟩

def theorem_13_12_natural_axes : Prop :=
  ∀ alpha : Real, 0 < alpha → alpha ≤ 1 →
    ∀ (N : Nat) [NeZero N] [Fact N.Prime],
      ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
        NaturalFourierSquare alpha f

theorem theorem_13_12_natural_axes_holds : theorem_13_12_natural_axes := by
  intro alpha ha ha1 N _ _ f hf hnot
  exact theorem_13_12_natural_all_prime alpha ha ha1 f hf hnot

end LeanProofs.GowersSzemeredi
