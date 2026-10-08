import GowersSzemeredi.Proofs05ModularApproximation
import OAI.Combinatorics.Progressions.Polynomial.PolynomialCoordinatePartition

/-! Transfer the already audited upstream Schmidt recurrence theorem to the
centered modular norm used in Gowers's Section 16. For each fixed degree,
the exponent is quadratic in the number of simultaneous coefficients.
The degree constants are existential. This supplies a recurrence input;
the minimum-width multilinear-box partition still requires a bridge. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem centered_monomial_of_integer_approximation {N q k : Nat} [NeZero N]
    (a : ZMod N) (b : Int) {R : Real}
    (h : |(q : Real) ^ k * ((a.valMinAbs : Real) / N) - b| < R) :
    (centeredAbs ((q : ZMod N) ^ k * a) : Real) < R * N := by
  let E : Int := (q : Int) ^ k * a.valMinAbs - b * N
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hcast : (E : ZMod N) = (q : ZMod N) ^ k * a := by
    simp [E, ZMod.coe_valMinAbs]
  have hE : (E : Real) = N * ((q : Real) ^ k * ((a.valMinAbs : Real) / N) - b) := by
    dsimp [E]
    push_cast
    field_simp
  have hcenter : (centeredAbs (E : ZMod N) : Real) ≤ (E.natAbs : Real) := by
    exact_mod_cast recurrence_centeredAbs_intCast_le (N := N) E
  rw [hcast] at hcenter
  calc
    _ ≤ (E.natAbs : Real) := hcenter
    _ = |(E : Real)| := by simp
    _ = N * |(q : Real) ^ k * ((a.valMinAbs : Real) / N) - b| := by
      rw [hE, abs_mul, abs_of_pos hN]
    _ < N * R := mul_lt_mul_of_pos_left h hN
    _ = R * N := mul_comm _ _

/-- A fixed degree admits polynomial dependence on the number of modular
coefficients. The constants are existential and do not give a box partition. -/
theorem simultaneous_modular_monomial_recurrence (j : Nat) :
    ∃ (K : Real) (p : Nat), 1 ≤ K ∧ 0 < p ∧
      ∀ (N : Nat) [NeZero N] (ι : Type) [Fintype ι]
        (a : ι → ZMod N) (M : Nat) (R : Real), 0 < R → R ≤ 1 →
        (K * ((Fintype.card ι : Real) + 1) / R) ^
          (p * (Fintype.card ι + 1) ^ 2) ≤ M →
        ∃ q : Nat, 0 < q ∧ q ≤ M ∧ ∀ i,
          (centeredAbs ((q : ZMod N) ^ (j + 1) * a i) : Real) < R * N := by
  obtain ⟨K, p, hK, hp, hrec⟩ := OAI.Erdos3.simultaneous_monomial_recurrence j
  refine ⟨K, p, hK, hp, ?_⟩
  intro N _ ι _ a M R hR hR1 hM
  obtain ⟨q, hq, hqM, b, hb⟩ :=
    hrec ι (fun i => (a i).valMinAbs / (N : Real)) M R hR hR1 hM
  exact ⟨q, hq, hqM, fun i => centered_monomial_of_integer_approximation (a i) (b i) (hb i)⟩

end LeanProofs.GowersSzemeredi
