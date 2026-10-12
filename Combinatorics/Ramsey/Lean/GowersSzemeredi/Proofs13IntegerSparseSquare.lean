import GowersSzemeredi.Proofs13PrintedSquareBounds
import GowersSzemeredi.Proofs05IntegerRepresentatives

/-! Ordinary integer squares when their density budget is at most one point.
The construction works over every modulus at least two and retains any
prescribed side length up to the modulus. -/
set_option autoImplicit false
set_option maxRecDepth 20000
noncomputable section
namespace LeanProofs.GowersSzemeredi

def intervalThrough (N m x : Nat) : NatAP :=
  ⟨min x (N - m), 1, m⟩

theorem intervalThrough_integer {N m x : Nat} (hmN : m ≤ N) :
    ((intervalThrough N m x).toModAP N).HasIntegerRepresentatives := by
  apply NatAP.toModAP_hasIntegerRepresentatives_of_bound
  · exact Nat.zero_lt_one
  · intro i hi
    change i < m at hi
    change min x (N - m) + i * 1 < N
    have := min_le_right x (N - m)
    omega

theorem intervalThrough_contains {N m : Nat} [NeZero N] (x : ZMod N)
    (hm : 0 < m) (hmN : m ≤ N) :
    x ∈ ((intervalThrough N m x.val).toModAP N).carrier := by
  classical
  let a := min x.val (N - m)
  have ha : a ≤ x.val := min_le_left _ _
  have hi : x.val - a < m := by
    have hx := x.val_lt
    by_cases h : x.val ≤ N - m
    · simp [a, min_eq_left h, hm]
    · dsimp [a]
      rw [min_eq_right (le_of_not_ge h)]
      omega
  refine Finset.mem_image.mpr ⟨⟨x.val - a, hi⟩, Finset.mem_univ _, ?_⟩
  simp only [NatAP.toModAP, intervalThrough, Nat.cast_one]
  rw [mul_one, ← Nat.cast_add, show min x.val (N - m) + (x.val - a) = x.val by omega]
  exact ZMod.natCast_zmod_val x

/-- One point suffices for the entire requested density whenever `delta*m²≤1`.
Both output axes have genuine integer representatives, common step one and
exactly the prescribed side length. No field hypothesis is required. -/
theorem integer_square_of_one_point_budget {N : Nat} [NeZero N]
    (hN : 2 ≤ N) (D : Finset (Pair N)) (phi : Pair N → ZMod N)
    (hD : D.Nonempty) (hbilinear : BilinearOn D phi) (m : Nat)
    (hm : 0 < m) (hmN : m ≤ N) (delta : Real)
    (hbudget : delta * m * m ≤ 1) :
    ∃ V W : ModAP N, ∃ E : Finset (Pair N),
      V.step != 0 ∧ V.step = W.step ∧ V.HasIntegerRepresentatives ∧
      W.HasIntegerRepresentatives ∧ V.length = m ∧ W.length = m ∧
      E ⊆ D ∧ E ⊆ V.carrier.product W.carrier ∧
      delta * V.length * W.length ≤ E.card ∧ BilinearOn E phi := by
  classical
  obtain ⟨z, hz⟩ := hD
  let V := (intervalThrough N m z.1.val).toModAP N
  let W := (intervalThrough N m z.2.val).toModAP N
  have hsub : ({z} : Finset (Pair N)) ⊆ D := by simpa using hz
  refine ⟨V, W, {z}, ?_, rfl, intervalThrough_integer hmN,
    intervalThrough_integer hmN, rfl, rfl, hsub, ?_, ?_, ?_⟩
  · simp only [V, NatAP.toModAP, intervalThrough, Nat.cast_one]
    have hne : (1 : ZMod N) ≠ 0 := by
      intro h
      have hv := congrArg ZMod.val h
      simp only [ZMod.val_one_eq_one_mod, ZMod.val_zero,
        Nat.mod_eq_of_lt (by omega : 1 < N)] at hv
      norm_num at hv
    exact bne_iff_ne.mpr hne
  · intro w hw
    have hwz : w = z := Finset.mem_singleton.mp hw
    subst w
    exact Finset.mem_product.mpr
      ⟨intervalThrough_contains z.1 hm hmN, intervalThrough_contains z.2 hm hmN⟩
  · simpa only [V, W, NatAP.toModAP, intervalThrough, Finset.card_singleton,
      Nat.cast_one] using hbudget
  · obtain ⟨mu, hmu, hagree⟩ := hbilinear
    exact ⟨mu, hmu, fun w hw ↦ hagree w (hsub hw)⟩

/-- Corollary 13.10 with its exact printed numerical bounds and ordinary
integer geometry whenever the requested density can be supplied by one point. -/
theorem corollary_13_10_printed_integer_of_one_point_budget {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (E : Stage135Data N) (G : Stage137Data N)
    (H : Stage138Data N) (J : Stage139Data N)
    (h139 : IsStage139DataPrinted S E G H J)
    (hgeometry : Stage139ConstructionGeometry G J)
    (hbudget : (2 : Real) ^ (-(86 : Int)) * S.alpha ^ 416 *
      Nat.sqrt J.U.length * Nat.sqrt J.U.length ≤ 1) :
    ∃ V W : ModAP N, ∃ E' : Finset (Pair N),
      V.step != 0 ∧ V.step = W.step ∧ V.HasIntegerRepresentatives ∧
      W.HasIntegerRepresentatives ∧ V.length = W.length ∧
      (J.U.length : Real) ^ ((1 : Real) / 2) - 1 ≤ V.length ∧
      E' ⊆ J.D ∧ E' ⊆ V.carrier.product W.carrier ∧
      (2 : Real) ^ (-(86 : Int)) * S.alpha ^ 416 * V.length * W.length ≤
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
  obtain ⟨V, W, E', hVs, hstep, hV, hW, hVl, hWl, hsub, hbox, hmass, hbilinear⟩ :=
    integer_square_of_one_point_budget (Fact.out : N.Prime).two_le J.D S.phi
      (Finset.card_pos.mp (by exact_mod_cast hDpos)) h139.2.2.2.2.2.2.2
      (Nat.sqrt J.U.length) (Nat.sqrt_pos.mpr hUpos)
      ((Nat.sqrt_le_self _).trans hUN) _ hbudget
  refine ⟨V, W, E', hVs, hstep, hV, hW, hVl.trans hWl.symm, ?_,
    hsub, hbox, hmass, hbilinear⟩
  rw [hVl, ← Real.sqrt_eq_rpow]
  have := Real.real_sqrt_le_nat_sqrt_succ (a := J.U.length)
  linarith only [this]

/-- The one-point condition is automatic throughout an explicit modulus
range. The original density and side bounds both retain integer geometry. -/
theorem corollary_13_10_printed_integer_small_modulus {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (E : Stage135Data N) (G : Stage137Data N)
    (H : Stage138Data N) (J : Stage139Data N)
    (h139 : IsStage139DataPrinted S E G H J)
    (hgeometry : Stage139ConstructionGeometry G J)
    (hN : (N : Real) ≤ (2 : Real) ^ 86 * S.alpha ^ (-(416 : Int))) :
    ∃ V W : ModAP N, ∃ E' : Finset (Pair N),
      V.step != 0 ∧ V.step = W.step ∧ V.HasIntegerRepresentatives ∧
      W.HasIntegerRepresentatives ∧ V.length = W.length ∧
      (J.U.length : Real) ^ ((1 : Real) / 2) - 1 ≤ V.length ∧
      E' ⊆ J.D ∧ E' ⊆ V.carrier.product W.carrier ∧
      (2 : Real) ^ (-(86 : Int)) * S.alpha ^ 416 * V.length * W.length ≤
        E'.card ∧ BilinearOn E' S.phi := by
  apply corollary_13_10_printed_integer_of_one_point_budget S E G H J h139 hgeometry
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
