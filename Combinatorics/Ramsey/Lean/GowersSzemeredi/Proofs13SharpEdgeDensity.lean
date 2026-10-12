import GowersSzemeredi.Proofs13DenseEdgeModels

/-! Sharp vertical-edge counting recovers the original printed extraction
mass at every height whose actual edge density is at most one sixth. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section13_height_count_le_edge_power_fifteen {N : Nat} [NeZero N]
    (A : Finset (Pair N)) (h : ZMod N) :
    arrangementCountAtHeight 8 A h ≤ (verticalEdgeDomain A h).card ^ 15 * N := by
  classical
  let T := {x : Fin 16 → Section13Edges A h //
    HasEqualHalfSums (k := 8) (fun i ↦ (section13VerticalDomain A h).index (x i))}
  let Code := (Fin 15 → Section13Edges A h) × ZMod N
  let encode : T → Code := fun x ↦ (fun i ↦ x.val i.succ, (x.val 0).val.2)
  have hinj : Function.Injective encode := by
    intro x y hxy
    have htail (i : Fin 15) : x.val i.succ = y.val i.succ :=
      congrFun (congrArg Prod.fst hxy) i
    have hxall : (fun i ↦ (x.val i).val.1) = (fun i ↦ (y.val i).val.1) := by
      apply stage135_additive_ext x.property y.property
      intro i
      exact congrArg (fun z : Section13Edges A h ↦ z.val.1) (htail i)
    apply Subtype.ext
    funext i
    apply Subtype.ext
    refine Prod.ext (congrFun hxall i) ?_
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact congrArg (fun code : Code ↦ code.2) hxy
    · exact congrArg (fun z : Section13Edges A h ↦ z.val.2) (htail j)
  have hcount : arrangementCountAtHeight 8 A h = Fintype.card T := by
    rw [← section13_domain_additive_count]
    unfold domainAdditiveTupleCount countWhere
    rw [Finset.filter_congr_decidable, ← Fintype.card_subtype]
  calc
    _ = Fintype.card T := hcount
    _ ≤ Fintype.card Code := Fintype.card_le_of_injective encode hinj
    _ = (verticalEdgeDomain A h).card ^ 15 * N := by
      simp [Code, Fintype.card_coe]

/-- The strong-height arrangement lower bound controls the fifteenth power
of the actual edge density, much more sharply than its previous linear bound. -/
theorem section13_strong_height_edge_power_fifteen {N : Nat} [NeZero N]
    (S : Section13Context N) (h : ZMod N) (hh : IsStrongHeight S h) :
    S.alpha ^ 32 / 16 ≤ section13EdgeDensity S h ^ 15 := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hbound : (section13C S h : Real) ≤
      ((verticalEdgeDomain S.A h).card : Real) ^ 15 * N := by
    exact_mod_cast section13_height_count_le_edge_power_fifteen S.A h
  apply le_of_mul_le_mul_right (a := (N : Real) ^ 31) _ (pow_pos hN _)
  calc
    _ = S.alpha ^ 32 * (N : Real) ^ 31 / 16 := by ring
    _ ≤ section13C S h := hh.1
    _ ≤ ((verticalEdgeDomain S.A h).card : Real) ^ 15 * N := hbound
    _ = section13EdgeDensity S h ^ 15 * (N : Real) ^ 31 := by
      rw [section13_edge_density_card]
      ring

/-- A convenient integral-power consequence avoids root notation. -/
theorem section13_strong_height_edge_density_cubic {N : Nat} [NeZero N]
    (S : Section13Context N) (h : ZMod N) (hh : IsStrongHeight S h) :
    S.alpha ^ 3 / 2 ≤ section13EdgeDensity S h := by
  have hpow : S.alpha ^ 45 ≤ S.alpha ^ 32 :=
    pow_le_pow_of_le_one S.alpha_pos.le S.alpha_at_most_one (by omega)
  have hleft : (S.alpha ^ 3 / 2) ^ 15 ≤ S.alpha ^ 32 / 16 := by
    calc
      _ = S.alpha ^ 45 / (2 : Real) ^ 15 := by ring
      _ ≤ S.alpha ^ 32 / (2 : Real) ^ 15 :=
        div_le_div_of_nonneg_right hpow (by positivity)
      _ ≤ S.alpha ^ 32 / 16 := div_le_div_of_nonneg_left
        (pow_nonneg S.alpha_pos.le _) (by norm_num) (by norm_num)
  exact le_of_pow_le_pow_left₀ (by decide : (15 : Nat) ≠ 0)
    (section13_edge_density_bounds S h hh).1.le
    (hleft.trans (section13_strong_height_edge_power_fifteen S h hh))

/-- The checked corrected extraction already gives the much stronger
`2^-22*alpha^21` mass, once the sharper arrangement count is retained. -/
theorem section13_sharp_small_edge_model {N : Nat} [NeZero N]
    (S : Section13Context N) (h : ZMod N) (hh : IsStrongHeight S h)
    (hβsixth : section13EdgeDensity S h ≤ 1 / 6) :
    let beta := section13EdgeDensity S h
    let K := domainLargeSpectrum (section13VerticalDomain S.A h)
      (section10Lambda beta * N * N)
    ∃ Y : Finset (Pair N), ∃ psi : ZMod N → ZMod N,
      Y ⊆ verticalEdgeDomain S.A h ∧
      (2 : Real) ^ (-(22 : Int)) * S.alpha ^ 21 * (N : Real) ^ 2 ≤ Y.card ∧
      HasBohrDifferenceModel (section13EdgeIndexDomain N) (verticalPhiDifference S.phi h)
        K (section10Zeta beta) Y psi := by
  have hβ := (section13_edge_density_bounds S h hh).1
  obtain ⟨Y, psi, hsub, hmass, hmodel⟩ := section13_good_height_bohr_model S h hh.2
    (section13EdgeDensity S h) hβ hβsixth (section13_edge_density_card S h)
  refine ⟨Y, psi, hsub, ?_, hmodel⟩
  have hα := S.alpha_pos
  have hb : S.alpha ^ 3 / 2 ≤ section13EdgeDensity S h :=
    section13_strong_height_edge_density_cubic S h hh
  have hprod : (S.alpha ^ 3 / 2) ^ 7 ≤ section13EdgeDensity S h ^ 7 :=
    pow_le_pow_left₀ (by positivity) hb _
  have hcoef : (2 : Real) ^ (-(22 : Int)) * S.alpha ^ 21 ≤
      (S.alpha ^ 3 / 2) ^ 7 / 20000 := by
    norm_num [zpow_neg]
    have hp : 0 ≤ S.alpha ^ 21 := pow_nonneg hα.le _
    nlinarith only [hp]
  calc
    _ ≤ ((S.alpha ^ 3 / 2) ^ 7 / 20000) * (N : Real) ^ 2 :=
      mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
    _ ≤ (section13EdgeDensity S h ^ 7 / 20000) * (N : Real) ^ 2 :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hprod (by norm_num)) (sq_nonneg _)
    _ = section13EdgeDensity S h ^ 6 * (verticalEdgeDomain S.A h).card / 20000 := by
      rw [section13_edge_density_card]
      ring
    _ ≤ Y.card := hmass

/-- Recover the original printed mass at a common spectrum and radius,
without using the stronger unverified original Theorem 10.13 claim. -/
theorem section13_printed_uniform_height_model_small_edge {N : Nat} [NeZero N]
    (S : Section13Context N) (h : ZMod N) (hh : IsStrongHeight S h)
    (hβsixth : section13EdgeDensity S h ≤ 1 / 6) :
    let a := S.alpha ^ 32 / 16
    let K := domainLargeSpectrum (section13VerticalDomain S.A h) (section10Lambda a * N * N)
    ∃ Y : Finset (Pair N), ∃ psi : ZMod N → ZMod N,
      Y ⊆ verticalEdgeDomain S.A h ∧
      (2 : Real) ^ (-(26 : Int)) * S.alpha ^ 128 * (N : Real) ^ 2 ≤ Y.card ∧
      HasBohrDifferenceModel (section13EdgeIndexDomain N) (verticalPhiDifference S.phi h)
        K (section10Zeta a) Y psi := by
  classical
  let a : Real := S.alpha ^ 32 / 16
  let beta := section13EdgeDensity S h
  have hbounds := section13_edge_density_bounds S h hh
  have ha : 0 < a := by dsimp [a]; have := S.alpha_pos; positivity
  have hβone : beta ≤ 1 := hbounds.2.2.trans S.alpha_at_most_one
  obtain ⟨Y, psi, hY, hmass, hmodel⟩ := section13_sharp_small_edge_model S h hh hβsixth
  refine ⟨Y, psi, hY, ?_, ?_⟩
  · have hpow : S.alpha ^ 128 ≤ S.alpha ^ 21 :=
      pow_le_pow_of_le_one S.alpha_pos.le S.alpha_at_most_one (by omega)
    have hc : (2 : Real) ^ (-(26 : Int)) * S.alpha ^ 128 ≤
        (2 : Real) ^ (-(22 : Int)) * S.alpha ^ 21 :=
      mul_le_mul (by norm_num) hpow (by positivity) (by positivity)
    exact (mul_le_mul_of_nonneg_right hc (sq_nonneg _)).trans hmass
  · apply bohr_difference_model_restrict _ _ _ _ _ _ _ _ hmodel
    apply bohr_domain_mono ?_ (section10Zeta_mono ha hbounds.2.1 hβone)
    intro r hr
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hlam : section10Lambda a ≤ section10Lambda beta := by
      unfold section10Lambda
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow ha.le hbounds.2.1 (by norm_num)) (by positivity)
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hlam (Nat.cast_nonneg N)) (Nat.cast_nonneg N)).trans
      (Finset.mem_filter.mp hr).2

end LeanProofs.GowersSzemeredi
