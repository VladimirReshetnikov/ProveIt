import GowersSzemeredi.Proofs16GlobalGraphCover

/-! Positive real iteration parameters do not suffice in Lemma 16.8. -/

noncomputable section
set_option maxRecDepth 10000
open scoped BigOperators ZMod
namespace LeanProofs.GowersSzemeredi

/-- A globally multilinear graph admits every positive diagonal parameter
`gamma = s`, even when the iteration parameter is less than one. -/
theorem IsMultilinear.multiplyLinearFunction_diagonal {N k : Nat} [NeZero N]
    {phi : Point N k → ZMod N} (hphi : IsMultilinear phi)
    (B : Finset (Point N k)) {s : Real} (hs : 0 < s) :
    MultiplyLinearFunction s s B phi := by
  classical
  intro theta ht ht1 P hP
  have hbase : s * (s⁻¹ * theta) = theta := by
    rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
  have hc : 0 < multipleC (s⁻¹ * theta) s k := by
    unfold multipleC
    rw [hbase]
    positivity
  have hc1 : multipleC (s⁻¹ * theta) s k ≤ 1 := by
    unfold multipleC
    rw [hbase]
    exact pow_le_one₀ ht.le ht1
  have ha : 0 < (multipleC (s⁻¹ * theta) s k) ^ s := Real.rpow_pos_of_pos hc _
  have ha1 : (multipleC (s⁻¹ * theta) s k) ^ s ≤ 1 :=
    Real.rpow_le_one hc.le hc1 hs.le
  have hq : 1 ≤ (multipleQ (s⁻¹ * theta) s k) ^ s := by
    apply Real.one_le_rpow _ hs.le
    unfold multipleQ
    exact (one_le_inv₀ hc).mpr hc1
  refine ⟨1, 1, P.carrier, fun _ => P, fun _ _ => phi,
    Finset.Subset.rfl, ?_, ?_, fun _ => hP, ?_, ?_, fun _ _ => hphi, ?_⟩
  · have hn : (0 : Real) ≤ P.carrier.card := by positivity
    nlinarith
  · constructor
    · intro x
      simp
    · intro i j hij
      exact ((bne_iff_ne.mp hij) (Subsingleton.elim i j)).elim
  · simpa only [Nat.cast_one] using hq
  · intro j
    by_cases hw : P.width = 0
    · simp only [hw, Nat.cast_zero, Real.zero_rpow ha.ne', le_refl]
    · have hw1 : (1 : Real) ≤ P.width := by exact_mod_cast (show 1 ≤ P.width by omega)
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hw1 ha1
  · intro j x hxQ hxH y hxy
    obtain ⟨z, _, hz⟩ := Finset.mem_image.mp hxy
    have hx : z = x := congrArg Prod.fst hz
    have hy := congrArg Prod.snd hz
    exact ⟨0, by simpa only [hx] using hy.symm⟩

namespace PositiveIteration

private def lemma168Gamma (i : Fin 2) :
    Finset (Point 2 1 × ZMod 2) :=
  partialGraph Finset.univ (fun _ => (i.val : ZMod 2))

private def lemma168Box : Box 2 1 where
  axis := fun _ => modInterval 2 0 1
  commonDiff := 1
  axis_step := by intro i; rfl

private def lemma168Point : Point 2 1 := fun _ => 0

private lemma lemma168Point_mem_box : lemma168Point ∈ lemma168Box.carrier := by
  classical
  simp [lemma168Point, lemma168Box, Box.carrier, modInterval, ModAP.carrier]

private lemma lemma168_pair_mem (x : Point 2 1) (i : Fin 2) :
    (x, (i.val : ZMod 2)) ∈ section16FinsetUnion lemma168Gamma := by
  classical
  rw [section16FinsetUnion, Finset.mem_biUnion]
  refine ⟨i, Finset.mem_univ i, ?_⟩
  rw [lemma168Gamma, partialGraph, Finset.mem_image]
  exact ⟨x, Finset.mem_univ x, rfl⟩

/-- Two constant graphs refute the real-parameter variant even with `s > 0`.
Take `D = 2^(2^9)` and `gamma = s = 1/(8D)`. At loss one half, the union
would require two graphs while its graph budget is only `4^(1/4) < 2`. -/
theorem counterexample : ¬ lemma_16_8_with_positive_iteration := by
  classical
  intro h
  let D : Nat := 2 ^ (2 ^ (1 + 8))
  have hD : 0 < (D : Real) := by
    have h : 0 < D := Nat.pow_pos (by decide)
    exact_mod_cast h
  let s : Real := (8 * (D : Real))⁻¹
  have hs : 0 < s := by dsimp [s]; positivity
  have hGamma : ∀ i, MultiplyLinear s s (lemma168Gamma i) := by
    intro i
    exact (isMultilinear_constant (i.val : ZMod 2)).multiplyLinearFunction_diagonal
      Finset.univ hs
  have hunion := h.1 2 0 2 s s lemma168Gamma hs hGamma
  obtain ⟨M, q, H, Q, mu, hHP, hHcard, hpartition, hproper, hq, hwidth,
      hmultilinear, hcover⟩ := hunion (1 / 2 : Real) (by norm_num) (by norm_num) lemma168Box
      (by intro i; simp [lemma168Box, ModAP.IsProper, modInterval, ModAP.carrier])
  have hcontrol : multipleQ ((2 * s)⁻¹ * (1 / 2)) s 1 = (4 : Real) ^ D := by
    unfold multipleQ multipleC
    change ((s * ((2 * s)⁻¹ * (1 / 2))) ^ D)⁻¹ = _
    have heq : s * ((2 * s)⁻¹ * (1 / 2)) = (1 / 4 : Real) := by
      field_simp
      <;> ring
    rw [heq, ← inv_pow]
    norm_num
  have hbudget : (multipleQ ((2 * s)⁻¹ * (1 / 2)) s 1) ^ (2 * s) < 2 := by
    rw [hcontrol, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 4)]
    have hexp : (D : Real) * (2 * s) = (1 / 4 : Real) := by
      dsimp [s]
      field_simp
      <;> ring
    rw [hexp]
    have hlt := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : Real) < 4)
      (by norm_num : (1 / 4 : Real) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at hlt
    have hsqrt : Real.sqrt 4 = 2 := by
      have hsq := Real.sq_sqrt (by norm_num : (0 : Real) ≤ 4)
      have hn := Real.sqrt_nonneg 4
      nlinarith
    simpa only [hsqrt] using hlt
  have hqTwo : q < 2 := by
    have hq' : (q : Real) < 2 := hq.trans_lt hbudget
    exact_mod_cast hq'
  have hcarrierPos : (0 : Real) < lemma168Box.carrier.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨lemma168Point, lemma168Point_mem_box⟩
  have hHpos : 0 < H.card := by
    have hhalf : (0 : Real) < (1 - (1 / 2 : Real)) * lemma168Box.carrier.card :=
      mul_pos (by norm_num) hcarrierPos
    exact_mod_cast lt_of_lt_of_le hhalf hHcard
  obtain ⟨x, hxH⟩ := Finset.card_pos.mp hHpos
  obtain ⟨j, hxQ⟩ := (hpartition.1 x).mp (hHP hxH)
  obtain ⟨i0, hi0⟩ := hcover j x hxQ hxH 0 (lemma168_pair_mem x 0)
  obtain ⟨i1, hi1⟩ := hcover j x hxQ hxH 1 (lemma168_pair_mem x 1)
  have hi : i0 = i1 := by apply Fin.ext; omega
  have hzeroOne : (0 : ZMod 2) = 1 := by rw [hi0, hi, ← hi1]
  norm_num at hzeroOne

end PositiveIteration

/-- The assertion fails for positive real iteration counts below one. -/
theorem lemma_16_8_positive_iteration_counterexample :
    ¬ lemma_16_8_with_positive_iteration := PositiveIteration.counterexample

end LeanProofs.GowersSzemeredi
