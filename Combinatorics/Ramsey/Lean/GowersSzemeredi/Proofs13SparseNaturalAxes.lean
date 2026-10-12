import GowersSzemeredi.Proofs13NaturalSquareAxes
import GowersSzemeredi.Proofs13IntegerSparseSquare

/-! The one-point square regime with explicit natural axes and a shared
positive integer step, including the printed contextual Corollary13.10. -/
set_option autoImplicit false
set_option maxRecDepth 20000
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem intervalThrough_nat_properties {N m x : Nat} (hmN : m ≤ N) :
    (intervalThrough N m x).IsProper ∧
      (intervalThrough N m x).carrier ⊆ Finset.range N := by
  apply NatAP.bounded_axis_certificate _ (by simp [intervalThrough])
  intro i hi
  change i < m at hi
  change min x (N - m) + i * 1 < N
  have := min_le_right x (N - m)
  omega

/-- The explicit integer-axis construction works over every nonzero modulus.
The shared ordinary common difference is exactly one. -/
theorem natural_square_of_one_point_budget {N : Nat} [NeZero N]
    (D : Finset (Pair N)) (phi : Pair N → ZMod N)
    (hD : D.Nonempty) (hbilinear : BilinearOn D phi) (m : Nat)
    (hm : 0 < m) (hmN : m ≤ N) (delta : Real) (hbudget : delta * m * m ≤ 1) :
    ∃ P Q : NatAP, ∃ E : Finset (Pair N),
      P.IsProper ∧ Q.IsProper ∧ P.step = 1 ∧ Q.step = 1 ∧
      P.length = m ∧ Q.length = m ∧ P.carrier ⊆ Finset.range N ∧
      Q.carrier ⊆ Finset.range N ∧ E ⊆ D ∧
      E ⊆ (P.toModAP N).carrier.product (Q.toModAP N).carrier ∧
      delta * P.length * Q.length ≤ E.card ∧ BilinearOn E phi := by
  classical
  obtain ⟨z, hz⟩ := hD
  let P := intervalThrough N m z.1.val
  let Q := intervalThrough N m z.2.val
  have hsub : ({z} : Finset (Pair N)) ⊆ D := by simpa using hz
  refine ⟨P, Q, {z}, (intervalThrough_nat_properties hmN).1,
    (intervalThrough_nat_properties hmN).1, rfl, rfl, rfl, rfl,
    (intervalThrough_nat_properties hmN).2, (intervalThrough_nat_properties hmN).2,
    hsub, ?_, ?_, ?_⟩
  · intro w hw
    have hwz : w = z := Finset.mem_singleton.mp hw
    subst w
    exact Finset.mem_product.mpr
      ⟨intervalThrough_contains z.1 hm hmN, intervalThrough_contains z.2 hm hmN⟩
  · simpa only [P, Q, intervalThrough, Finset.card_singleton, Nat.cast_one] using hbudget
  · obtain ⟨mu, hmu, hagree⟩ := hbilinear
    exact ⟨mu, hmu, fun w hw ↦ hagree w (hsub hw)⟩

theorem corollary_13_10_printed_natural_of_one_point_budget {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (E : Stage135Data N) (G : Stage137Data N)
    (H : Stage138Data N) (J : Stage139Data N)
    (h139 : IsStage139DataPrinted S E G H J)
    (hgeometry : Stage139ConstructionGeometry G J)
    (hbudget : (2 : Real) ^ (-(86 : Int)) * S.alpha ^ 416 *
      Nat.sqrt J.U.length * Nat.sqrt J.U.length ≤ 1) :
    ∃ P Q : NatAP, ∃ E' : Finset (Pair N),
      P.IsProper ∧ Q.IsProper ∧ P.step = 1 ∧ Q.step = 1 ∧
      P.length = Q.length ∧ P.carrier ⊆ Finset.range N ∧ Q.carrier ⊆ Finset.range N ∧
      (J.U.length : Real) ^ ((1 : Real) / 2) - 1 ≤ P.length ∧
      E' ⊆ J.D ∧ E' ⊆ (P.toModAP N).carrier.product (Q.toModAP N).carrier ∧
      (2 : Real) ^ (-(86 : Int)) * S.alpha ^ 416 * P.length * Q.length ≤
        E'.card ∧ BilinearOn E' S.phi := by
  have hGpos := hgeometry.2.1
  have hUpos : 0 < J.U.length := by
    have hpos : (0 : Real) < J.U.length :=
      (Real.rpow_pos_of_pos (by exact_mod_cast hGpos) _).trans_le h139.2.2.2.2.1
    exact_mod_cast hpos
  have hDpos : (0 : Real) < J.D.card := lt_of_lt_of_le (by
    have hα := S.alpha_pos
    have hG : (0 : Real) < G.S.length := by exact_mod_cast hGpos
    have hU : (0 : Real) < J.U.length := by exact_mod_cast hUpos
    positivity) h139.2.2.2.2.2.2.1
  have hUN : J.U.length ≤ N := by
    rw [← h139.2.1]
    simpa only [ZMod.card] using Finset.card_le_univ J.U.carrier
  obtain ⟨P, Q, E', hP, hQ, hPs, hQs, hPl, hQl, hPN, hQN, hsub, hbox, hmass, hbilinear⟩ :=
    natural_square_of_one_point_budget J.D S.phi
      (Finset.card_pos.mp (by exact_mod_cast hDpos)) h139.2.2.2.2.2.2.2
      (Nat.sqrt J.U.length) (Nat.sqrt_pos.mpr hUpos)
      ((Nat.sqrt_le_self _).trans hUN) _ hbudget
  refine ⟨P, Q, E', hP, hQ, hPs, hQs, hPl.trans hQl.symm, hPN, hQN, ?_,
    hsub, hbox, hmass, hbilinear⟩
  rw [hPl, ← Real.sqrt_eq_rpow]
  have := Real.real_sqrt_le_nat_sqrt_succ (a := J.U.length)
  linarith only [this]

theorem corollary_13_10_printed_natural_small_modulus {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (E : Stage135Data N) (G : Stage137Data N)
    (H : Stage138Data N) (J : Stage139Data N)
    (h139 : IsStage139DataPrinted S E G H J)
    (hgeometry : Stage139ConstructionGeometry G J)
    (hN : (N : Real) ≤ (2 : Real) ^ 86 * S.alpha ^ (-(416 : Int))) :
    ∃ P Q : NatAP, ∃ E' : Finset (Pair N),
      P.IsProper ∧ Q.IsProper ∧ P.step = 1 ∧ Q.step = 1 ∧
      P.length = Q.length ∧ P.carrier ⊆ Finset.range N ∧ Q.carrier ⊆ Finset.range N ∧
      (J.U.length : Real) ^ ((1 : Real) / 2) - 1 ≤ P.length ∧
      E' ⊆ J.D ∧ E' ⊆ (P.toModAP N).carrier.product (Q.toModAP N).carrier ∧
      (2 : Real) ^ (-(86 : Int)) * S.alpha ^ 416 * P.length * Q.length ≤
        E'.card ∧ BilinearOn E' S.phi := by
  apply corollary_13_10_printed_natural_of_one_point_budget S E G H J h139 hgeometry
  let K : Real := (2 : Real) ^ (-(86 : Int)) * S.alpha ^ 416
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hα := S.alpha_pos
  have hcancel : K * ((2 : Real) ^ 86 * S.alpha ^ (-(416 : Int))) = 1 := by
    dsimp [K]
    norm_num [zpow_neg, zpow_natCast]
    field_simp
  have hUN : J.U.length ≤ N := by
    rw [← h139.2.1]
    simpa only [ZMod.card] using Finset.card_le_univ J.U.carrier
  have hsqrt : Nat.sqrt J.U.length * Nat.sqrt J.U.length ≤ N :=
    (Nat.sqrt_le J.U.length).trans hUN
  change K * (Nat.sqrt J.U.length : Real) * Nat.sqrt J.U.length ≤ 1
  calc
    _ = K * ((Nat.sqrt J.U.length * Nat.sqrt J.U.length : Nat) : Real) := by push_cast; ring
    _ ≤ K * N := mul_le_mul_of_nonneg_left (by exact_mod_cast hsqrt) hK
    _ ≤ K * ((2 : Real) ^ 86 * S.alpha ^ (-(416 : Int))) :=
      mul_le_mul_of_nonneg_left hN hK
    _ = 1 := hcancel

end LeanProofs.GowersSzemeredi
