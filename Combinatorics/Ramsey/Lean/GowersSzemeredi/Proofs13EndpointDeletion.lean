import GowersSzemeredi.Proofs13QuadraticRecurrence
import GowersSzemeredi.Proofs16Slicing

/-! Endpoint deletion in the quadratic recurrence step, including the
explicit length condition needed to retain the strong-height density. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Delete the first and last indexed points of a modular progression. -/
def ModAP.interior {N : Nat} (P : ModAP N) : ModAP N where
  start := P.start + P.step
  step := P.step
  length := P.length - 2

/-- An interior point and both adjacent points belong to the original cell. -/
theorem ModAP.interior_neighbors {N : Nat} (P : ModAP N) {x : ZMod N}
    (hx : x ∈ P.interior.carrier) :
    x ∈ P.carrier ∧ x + P.step ∈ P.carrier ∧ x - P.step ∈ P.carrier := by
  classical
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  have hi : i.val < P.length - 2 := i.isLt
  refine ⟨?_, ?_, ?_⟩
  · apply Finset.mem_image.mpr
    refine ⟨⟨i.val + 1, by omega⟩, Finset.mem_univ _, ?_⟩
    dsimp [ModAP.interior]
    push_cast
    ring
  · apply Finset.mem_image.mpr
    refine ⟨⟨i.val + 2, by omega⟩, Finset.mem_univ _, ?_⟩
    dsimp [ModAP.interior]
    push_cast
    ring
  · apply Finset.mem_image.mpr
    refine ⟨⟨i.val, by omega⟩, Finset.mem_univ _, ?_⟩
    dsimp [ModAP.interior]
    ring

theorem ModAP.interior_subset {N : Nat} (P : ModAP N) :
    P.interior.carrier ⊆ P.carrier := fun _ hx => (P.interior_neighbors hx).1

/-- Removing endpoints preserves properness even when the interior is empty. -/
theorem ModAP.interior_isProper {N : Nat} (P : ModAP N) (hP : P.IsProper) :
    P.interior.IsProper := by
  classical
  have hcard : (Finset.univ.image (fun i : Fin P.length =>
      P.start + (i : Nat) * P.step)).card = (Finset.univ : Finset (Fin P.length)).card := by
    simpa only [ModAP.IsProper, ModAP.carrier, Finset.card_univ, Fintype.card_fin] using hP
  have hinj := Finset.card_image_iff.mp hcard
  unfold ModAP.IsProper ModAP.carrier
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro i _ j _ hij
    let i' : Fin P.length := ⟨i.val + 1, by have := i.isLt; dsimp [ModAP.interior] at this; omega⟩
    let j' : Fin P.length := ⟨j.val + 1, by have := j.isLt; dsimp [ModAP.interior] at this; omega⟩
    have heq : P.start + (i'.val : ZMod N) * P.step =
        P.start + (j'.val : ZMod N) * P.step := by
      dsimp [i', j']
      dsimp [ModAP.interior] at hij
      push_cast
      linear_combination hij
    have hfin : i' = j' := hinj (Finset.mem_univ _) (Finset.mem_univ _) heq
    apply Fin.ext
    have hval := congrArg Fin.val hfin
    dsimp [i', j'] at hval
    omega

/-- At most two actual points are removed from a proper progression. -/
theorem ModAP.card_sdiff_interior_le_two {N : Nat} (P : ModAP N) (hP : P.IsProper) :
    (P.carrier \ P.interior.carrier).card ≤ 2 := by
  rw [Finset.card_sdiff_of_subset P.interior_subset, hP, P.interior_isProper hP]
  dsimp [ModAP.interior]
  omega

/-- The strong-height count loses at most two when the endpoints are deleted. -/
theorem stage135_critical_count_interior {N : Nat} [NeZero N]
    (S : Section13Context N) (D : Stage134Data N) (Q : ModAP N) (hQ : Q.IsProper) :
    (criticalHeights S D ⟨Q⟩).card ≤ (criticalHeights S D ⟨Q.interior⟩).card + 2 := by
  classical
  let A := criticalHeights S D ⟨Q⟩
  let B := criticalHeights S D ⟨Q.interior⟩
  have hBA : B ⊆ A := by
    intro h hh
    simp only [B, A, criticalHeights, Finset.mem_filter, Finset.mem_inter] at hh ⊢
    exact ⟨⟨Q.interior_subset hh.1.1, hh.1.2⟩, hh.2⟩
  have hdiff : A \ B ⊆ Q.carrier \ Q.interior.carrier := by
    intro h hh
    obtain ⟨ha, hb⟩ := Finset.mem_sdiff.mp hh
    simp only [A, criticalHeights, Finset.mem_filter, Finset.mem_inter] at ha
    refine Finset.mem_sdiff.mpr ⟨ha.1.1, ?_⟩
    intro hi
    apply hb
    simp only [B, criticalHeights, Finset.mem_filter, Finset.mem_inter]
    exact ⟨⟨hi, ha.1.2⟩, ha.2⟩
  have hd := (Finset.card_le_card hdiff).trans (Q.card_sdiff_interior_le_two hQ)
  have hc := Finset.card_sdiff_add_card_eq_card hBA
  change A.card ≤ B.card + 2
  omega

/-- The printed weakening from density 1/16 to 1/20 is valid once the
pre-trimming cell has alpha^32 times its length at least 160. -/
theorem stage135_interior_density_of_weight {N : Nat} [NeZero N]
    (S : Section13Context N) (D : Stage134Data N) (Q : ModAP N)
    (hQ : Q.IsProper)
    (hweight : S.alpha ^ 32 * (N : Real) ^ 31 * Q.length / 8 ≤
      (goodHeightWeight S (Q.carrier ∩ D.H) : Real))
    (hlarge : 160 ≤ S.alpha ^ 32 * (Q.length : Real)) :
    S.alpha ^ 32 * Q.interior.length / 20 ≤
      (criticalHeights S D ⟨Q.interior⟩).card := by
  have hbefore := stage135_critical_count_of_weight S D Q hQ hweight
  have hafter : ((criticalHeights S D ⟨Q⟩).card : Real) ≤
      ((criticalHeights S D ⟨Q.interior⟩).card : Real) + 2 := by
    exact_mod_cast stage135_critical_count_interior S D Q hQ
  have hlength : (Q.interior.length : Real) ≤ Q.length := by
    exact_mod_cast Nat.sub_le Q.length 2
  have hm := mul_le_mul_of_nonneg_left hlength (pow_nonneg S.alpha_pos.le 32)
  linarith only [hbefore, hafter, hlarge, hm]

/-- A quadratic polynomial in the ambient height variable. -/
def stage135AmbientQuadratic {N : Nat} (a b h : ZMod N) : ZMod N :=
  a * (4 : ZMod N)⁻¹ * h ^ 2 + b * (2 : ZMod N)⁻¹ * h

/-- Diameter control on a full cell gives the required affine smallness
at every point of its interior, with the same common step. -/
theorem stage135_interior_small_affine {N : Nat} [NeZero N]
    (hprime : N.Prime) (hodd : N != 2) (Q : ModAP N) (a b : ZMod N) (s : Real)
    (hdiam : diameterAtMostReal (Q.carrier.image (stage135AmbientQuadratic a b)) s)
    {h : ZMod N} (hh : h ∈ Q.interior.carrier) :
    (centeredAbs ((a * h + b) * Q.interior.step) : Real) ≤ s := by
  classical
  obtain ⟨_, hp, hm⟩ := Q.interior_neighbors hh
  have hid := stage135Quadratic_symmetric_difference hprime hodd
    (modInterval N 0 N) a b h Q.step
  simp only [stage135Quadratic, stage135ModPoint, modInterval, mul_one, zero_add] at hid
  change stage135AmbientQuadratic a b (h + Q.step) -
    stage135AmbientQuadratic a b (h - Q.step) = (a * h + b) * Q.step at hid
  change (centeredAbs ((a * h + b) * Q.step) : Real) ≤ s
  rw [← hid]
  exact hdiam.centeredAbs_sub_le (Finset.mem_image.mpr ⟨_, hp, rfl⟩)
    (Finset.mem_image.mpr ⟨_, hm, rfl⟩)

/-- Trim a sufficiently long weighted quadratic cell to obtain all of the
Stage 13.5 conclusions, retaining the prescribed common difference. -/
theorem stage135_of_weighted_quadratic_cell {N : Nat} [NeZero N]
    (hprime : N.Prime) (hodd : N != 2)
    (S : Section13Context N) (D : Stage134Data N) (Q : ModAP N)
    (hQ : Q.IsProper) (hstep : Q.step != 0) (hsub : Q.carrier ⊆ D.P.carrier)
    (htwo : 2 ≤ Q.length)
    (hlength : (D.P.length : Real) ^ ((1 : Real) / (2 : Real) ^ (12 * D.q)) / 2 + 2 ≤
      Q.length)
    (hlarge : 160 ≤ S.alpha ^ 32 * (Q.length : Real))
    (hweight : S.alpha ^ 32 * (N : Real) ^ 31 * Q.length / 8 ≤
      (goodHeightWeight S (Q.carrier ∩ D.H) : Real))
    (hdiam : ∀ i, diameterAtMostReal
      (Q.carrier.image (stage135AmbientQuadratic (D.a i) (D.b i)))
      ((D.P.length : Real) ^ (-((1 : Real) / (2 : Real) ^ (11 * D.q))) * N)) :
    ∃ E : Stage135Data N, IsStage135Data S D E := by
  refine ⟨⟨Q.interior⟩, hstep, Q.interior_isProper hQ,
    Q.interior_subset.trans hsub, ?_, ?_, ?_⟩
  · change _ ≤ ((Q.length - 2 : Nat) : Real)
    rw [Nat.cast_sub htwo, Nat.cast_ofNat]
    linarith only [hlength]
  · intro i h hh
    exact stage135_interior_small_affine hprime hodd Q (D.a i) (D.b i) _ (hdiam i) hh
  · exact stage135_interior_density_of_weight S D Q hQ hweight hlarge

end LeanProofs.GowersSzemeredi
