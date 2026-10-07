import GowersSzemeredi.Proofs13ExplicitFourierExponent

/-! Odd, square-root-sized Fourier squares for localized phase removal. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Filter

/-- Rounding down to an odd integer loses at most a factor two above four. -/
theorem exists_odd_nat_between_half {x : Real} (hx : 4 ≤ x) :
    ∃ m : Nat, Odd m ∧ 0 < m ∧ x / 2 ≤ m ∧ (m : Real) ≤ x := by
  let n := Nat.floor x
  have hn : 4 ≤ n := Nat.le_floor hx
  let m := 2 * ((n - 1) / 2) + 1
  have hmod := Nat.mod_lt (n - 1) (by omega : 0 < 2)
  have hdiv := Nat.div_add_mod (n - 1) 2
  have hmn : m ≤ n := by dsimp [m]; omega
  have hnm : n ≤ m + 1 := by dsimp [m]; omega
  have hnmR : (n : Real) ≤ (m : Real) + 1 := by exact_mod_cast hnm
  have hxupper : x < (n : Real) + 1 := Nat.lt_floor_add_one x
  refine ⟨m, ⟨(n - 1) / 2, rfl⟩, by dsimp [m]; omega, ?_, ?_⟩
  · linarith only [hx, hxupper, hnmR]
  · exact (by exact_mod_cast hmn : (m : Real) ≤ n).trans (Nat.floor_le (by linarith only [hx]))

/-- The explicit Fourier extraction exponent lies in (0,1/2]. -/
theorem section13_explicit_exponent_bounds {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    0 < (1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 88)) ∧
      (1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 88)) ≤ 1 / 2 := by
  refine ⟨Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
  have ht : (1 : Real) ≤ 2 / alpha := (le_div_iff₀ hα).mpr (by linarith only [hαone])
  have hexp := one_le_pow₀ ht (n := (2 : Nat) ^ 88)
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge
    (by norm_num : (0 : Real) < 1 / 2) (by norm_num : (1 / 2 : Real) ≤ 1) hexp

/-- The complete Fourier square can be chosen with an odd common side at
most sqrt(N), retaining half the length lower bound and one quarter of the
relative density. These are the geometric hypotheses of Proposition 17.7. -/
theorem theorem_13_12_odd_square :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 → ∃ N₀ : Nat,
      ∀ (N : Nat) [NeZero N] [Fact N.Prime], N₀ ≤ N →
        ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
        ∃ m : Nat, ∃ P Q : ModAP N, ∃ B : Finset (Pair N), ∃ phi : Pair N → ZMod N,
          Odd m ∧ 0 < m ∧ (m : Real) ≤ Real.sqrt N ∧
          (N : Real) ^ ((1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 88))) / 2 ≤ m ∧
          P.step != 0 ∧ P.step = Q.step ∧ P.IsProper ∧ Q.IsProper ∧ P.length = m ∧ Q.length = m ∧
          B ⊆ P.carrier.product Q.carrier ∧
          (alpha / 2) ^ ((2 : Nat) ^ 76) / 4 * m * m ≤ B.card ∧
          BilinearOn (P.carrier.product Q.carrier) phi ∧
          ∀ z, z ∈ B → alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖ := by
  intro alpha hα hαone
  let e := (1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 88))
  obtain ⟨he, hehalf⟩ := section13_explicit_exponent_bounds hα hαone
  obtain ⟨N₁, hN₁⟩ := theorem_13_12_with_explicit_bound alpha hα hαone
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (eventually_nat_mul_rpow_le (C := 4) (D := 1) he zero_lt_one)
  refine ⟨max N₁ N₂, fun N _ _ hN f hf hnot => ?_⟩
  have hlarge : 4 ≤ (N : Real) ^ e := by
    simpa only [Real.rpow_zero, mul_one, one_mul] using hN₂ N (by omega)
  obtain ⟨m, hmodd, hmpos, hmlower, hmupper⟩ := exists_odd_nat_between_half hlarge
  obtain ⟨S, T, D, psi, hSs, hST, hS, hT, hlen, hsize, hD, hmass, hbil, hfourier⟩ :=
    hN₁ N (by omega) f hf hnot
  have hmS : m ≤ S.length := by exact_mod_cast hmupper.trans hsize
  have hmT : m ≤ T.length := by omega
  have hTstep : T.step != 0 := by rwa [← hST]
  obtain ⟨mu, hmu, hagree⟩ := hbil
  have hbilD : BilinearOn D psi := ⟨mu, hmu, fun z hz => hagree z (hD hz)⟩
  obtain ⟨P, Q, B, hPs, hQs, hP, hQ, hPl, hQl, hBD, hbox, hmass', _⟩ :=
    bilinear_square_of_integer_step_fit S T D psi ((alpha / 2) ^ ((2 : Nat) ^ 76)) 1 m
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

end LeanProofs.GowersSzemeredi
