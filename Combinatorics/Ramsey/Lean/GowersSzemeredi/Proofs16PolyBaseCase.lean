import GowersSzemeredi.Proofs16RegimeSplitting
import GowersSzemeredi.Proofs16BaseCaseLongBoxTransport

/-! Polynomial controls for one-dimensional Freiman families.

`MultiplyLinear gamma r` fixes its control functions. `MultiplyLinearWith`
allows arbitrary ones, and `MultiplyLinear` is the special case with the
source's functions (`multiplyLinear_iff_with`, definitional).

The main theorem sharpens the base case of Theorem 16.2. A one-dimensional
relation contained in the union of `q` order-eight Freiman graphs has, for
every loss `sigma`, covers by at most `3*q` multilinear graphs on cells of
width at least `width^E(sigma)`, where `E(sigma)` is polynomial in `sigma`
(up to a logarithm), and the graph count does not depend on `sigma`.

On each box the graphs that are sparse there (index density below `sigma/q`)
are deleted, at total cost `sigma`. All the remaining graphs are linearized
*simultaneously* by one application of Corollary 7.11, whose exponent is
inversely proportional to the number of graphs, not exponentially small in
it. Boxes below the Corollary 7.11 threshold are covered exactly by the
coarse relation cover. This is the input needed to avoid the exponential
compounding of sequential refinements in the two-dimensional lift. -/
set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

open BaseCase

/-- The Corollary 7.11 exponent with deletion density `sigma/q` and `q` graphs. -/
def polyBaseCorExponent (q : Nat) (sigma : Real) : Real :=
  (2 : Real) ^ (-(14 : Real)) * (sigma / q) ^ 2 * (q : Real)⁻¹

/-- The Corollary 7.11 size threshold `1024*pi/(sigma/q)`. -/
def polyBaseThreshold (q : Nat) (sigma : Real) : Real :=
  1024 * Real.pi / (sigma / q)

/-- The width exponent: the Corollary 7.11 exponent scaled so that boxes
below the threshold have target width at most two. -/
def polyBaseExponent (q : Nat) (sigma : Real) : Real :=
  polyBaseCorExponent q sigma * Real.log 2 / Real.log (polyBaseThreshold q sigma)

section Parameters

variable {q : Nat} {sigma : Real}

theorem polyBase_loss_pos (hq : 0 < q) (hs : 0 < sigma) : 0 < sigma / (q : Real) := by positivity

theorem polyBase_loss_le_one (hq : 0 < q) (hs1 : sigma ≤ 1) :
    sigma / (q : Real) ≤ 1 := by
  have hq1 : (1 : Real) ≤ q := by exact_mod_cast hq
  rw [div_le_one (by linarith)]
  linarith

theorem polyBaseCorExponent_pos (hq : 0 < q) (hs : 0 < sigma) :
    0 < polyBaseCorExponent q sigma := by
  have := polyBase_loss_pos hq hs
  unfold polyBaseCorExponent
  positivity

theorem polyBaseThreshold_ge_four (hq : 0 < q) (hs : 0 < sigma) (hs1 : sigma ≤ 1) :
    4 ≤ polyBaseThreshold q sigma := by
  have hη := polyBase_loss_pos hq hs
  have hη1 := polyBase_loss_le_one hq hs1
  have hpi := Real.pi_gt_three
  unfold polyBaseThreshold
  rw [le_div_iff₀ hη]
  nlinarith

theorem polyBaseExponent_pos (hq : 0 < q) (hs : 0 < sigma) (hs1 : sigma ≤ 1) :
    0 < polyBaseExponent q sigma := by
  have ha := polyBaseCorExponent_pos hq hs
  have hΛ := polyBaseThreshold_ge_four hq hs hs1
  have hlog : 0 < Real.log (polyBaseThreshold q sigma) := Real.log_pos (by linarith)
  unfold polyBaseExponent
  positivity

theorem polyBaseExponent_le_half (hq : 0 < q) (hs : 0 < sigma) (hs1 : sigma ≤ 1) :
    polyBaseExponent q sigma ≤ polyBaseCorExponent q sigma / 2 := by
  have ha := polyBaseCorExponent_pos hq hs
  have hΛ := polyBaseThreshold_ge_four hq hs hs1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : 2 * Real.log 2 ≤ Real.log (polyBaseThreshold q sigma) := by
    have h := Real.log_le_log (by norm_num) hΛ
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : Real) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith
  have hlog : 0 < Real.log (polyBaseThreshold q sigma) := by linarith
  unfold polyBaseExponent
  rw [div_le_iff₀ hlog]
  nlinarith

/-- Below the threshold the target width is at most two. -/
theorem polyBase_small_width {W : Real} (hW : 0 ≤ W) (hq : 0 < q) (hs : 0 < sigma)
    (hs1 : sigma ≤ 1) (hsmall : W ^ polyBaseCorExponent q sigma ≤ polyBaseThreshold q sigma) :
    W ^ polyBaseExponent q sigma ≤ 2 := by
  have ha := polyBaseCorExponent_pos hq hs
  have hΛ := polyBaseThreshold_ge_four hq hs hs1
  have hlog : 0 < Real.log (polyBaseThreshold q sigma) := Real.log_pos (by linarith)
  set a := polyBaseCorExponent q sigma
  set Λ := polyBaseThreshold q sigma
  have hexp : polyBaseExponent q sigma = a * (Real.log 2 / Real.log Λ) := by
    unfold polyBaseExponent
    ring
  rw [hexp, Real.rpow_mul hW]
  calc (W ^ a) ^ (Real.log 2 / Real.log Λ)
      ≤ Λ ^ (Real.log 2 / Real.log Λ) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hW a) hsmall (by positivity)
    _ = 2 := by
        rw [Real.rpow_def_of_pos (by linarith), mul_div_cancel₀ _ hlog.ne',
          Real.exp_log (by norm_num)]

end Parameters

/-- **Polynomial base case.** A one-dimensional relation inside the union of
`q` order-eight Freiman graphs is multiply linear with graph count `3*q`,
independent of the loss, and width exponent `polyBaseExponent q`. -/
theorem section16_freiman_family_poly_cover {N q : Nat} [NeZero N] [Fact N.Prime]
    (hq : 0 < q) (B : Fin q → Finset (Point N 1)) (phi : Fin q → Point N 1 → ZMod N)
    (hfreiman : ∀ i, FreimanHom 8 (pointOneDomain (B i)) (pointOneMap (phi i)))
    (Gamma : Finset (Point N 1 × ZMod N))
    (hcover : Gamma ⊆ section16FinsetUnion (fun i => partialGraph (B i) (phi i))) :
    MultiplyLinearWith (fun _ => ((3 ^ 1 * q : Nat) : Real)) (polyBaseExponent q) Gamma := by
  intro sigma hs hs1 P hP
  -- Every point carries at most `q` values.
  have hmem : ∀ z ∈ Gamma, ∃ i, z.1 ∈ B i ∧ z.2 = phi i z.1 := fun z hz => by
    obtain ⟨i, -, hzi⟩ := Finset.mem_biUnion.mp (hcover hz)
    exact ⟨i, (mem_partialGraph_one (B i) (phi i) z.1 z.2).1 hzi⟩
  have hfib : ∀ x : Point N 1, (Gamma.filter fun z => z.1 = x).card ≤ q := by
    intro x
    refine (Finset.card_le_card (t := Finset.univ.image fun i : Fin q => (x, phi i x))
      fun z hz => ?_).trans (Finset.card_image_le.trans (by simp))
    obtain ⟨hzG, rfl⟩ := Finset.mem_filter.mp hz
    obtain ⟨i, -, hzi⟩ := hmem z hzG
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, Prod.ext rfl hzi.symm⟩
  set W : Real := (P.width : Real) with hW_def
  have hW0 : 0 ≤ W := Nat.cast_nonneg _
  have hη := polyBase_loss_pos hq hs
  have hη1 := polyBase_loss_le_one hq hs1
  have ha := polyBaseCorExponent_pos hq hs
  have hΛ := polyBaseThreshold_ge_four hq hs hs1
  have hE := polyBaseExponent_pos hq hs hs1
  have hEa := polyBaseExponent_le_half hq hs hs1
  have hE1 : polyBaseExponent q sigma ≤ 1 := by
    have h2 : (2 : Real) ^ (-(14 : Real)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    have : polyBaseCorExponent q sigma ≤ 1 := mul_le_one₀ (mul_le_one₀ h2 (by positivity)
      (pow_le_one₀ hη.le hη1)) (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast hq))
    linarith
  -- The width of the whole box is enough.
  have hWE : W ^ polyBaseExponent q sigma ≤ W := by
    rcases Nat.eq_zero_or_pos P.width with h0 | h0
    · rw [hW_def, h0]; simp [Real.zero_rpow hE.ne']
    · exact (Real.rpow_le_rpow_of_exponent_le (by rw [hW_def]; exact_mod_cast h0) hE1).trans_eq
        (Real.rpow_one W)
  by_cases hbig : polyBaseThreshold q sigma < W ^ polyBaseCorExponent q sigma
  swap
  · -- Small boxes: the exact coarse cover.
    push Not at hbig
    obtain ⟨L, R, mu, hpart, hproper, hwidth, hmu, hcov⟩ :=
      section16_coarse_relation_cover (by norm_num : 0 < 1) Gamma q hfib P hP
    refine ⟨L, 3 ^ 1 * q, P.carrier, R, mu, Finset.Subset.refl _,
      mul_le_of_le_one_left (Nat.cast_nonneg _) (by linarith), hpart, hproper, le_rfl,
      fun j => le_trans ?_ (Nat.cast_le.mpr (hwidth j)), hmu,
      fun j x hx _ y hy => hcov j x hx y hy⟩
    push_cast
    exact le_min (polyBase_small_width hW0 hq hs hs1 hbig) hWE
  -- Large boxes.
  have hX4 : 4 < W ^ polyBaseCorExponent q sigma := lt_of_le_of_lt hΛ hbig
  have hW1 : 1 ≤ W := not_lt.mp fun hlt => by linarith [Real.rpow_le_one hW0 hlt.le ha.le]
  -- Delete the graphs that are sparse in this box.
  let I : Finset (Fin q) := Finset.univ.filter fun i =>
    sigma / (q : Real) * W ≤ ((boxOneIndexDomain P (B i)).card : Real)
  let U := (Finset.univ.filter (· ∉ I)).biUnion fun i => B i ∩ P.carrier
  let H : Finset (Point N 1) := P.carrier \ U
  have hHU : ∀ x ∈ H, ∀ i, x ∈ B i → i ∈ I := fun x hx i hxB => by
    by_contra hi
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hi⟩, Finset.mem_inter.mpr ⟨hxB, (Finset.mem_sdiff.mp hx).1⟩⟩)
  have hHmass : (1 - sigma) * (P.carrier.card : Real) ≤ H.card := by
    have hterm : ∀ i ∈ Finset.univ.filter (· ∉ I),
        ((B i ∩ P.carrier).card : Real) ≤ sigma / q * W := fun i hi => by
      rw [← boxOneIndexDomain_card P hP (B i)]
      exact (not_le.mp fun h => (Finset.mem_filter.mp hi).2
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)).le
    have h1 : (P.carrier.card : Real) ≤ H.card + U.card := by
      exact_mod_cast Finset.card_le_card_sdiff_add_card
    have h2 : (U.card : Real) ≤
        ∑ i ∈ Finset.univ.filter (· ∉ I), ((B i ∩ P.carrier).card : Real) := by
      exact_mod_cast Finset.card_biUnion_le
    have h3 := Finset.sum_le_card_nsmul _ _ _ hterm
    have h4 : ((Finset.univ.filter (· ∉ I)).card : Real) * (sigma / q * W) ≤
        q * (sigma / q * W) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.card_filter_le _ _).trans (by simp))
        (by positivity)
    have hq0 : (q : Real) ≠ 0 := by positivity
    have h5 : (q : Real) * (sigma / q * W) = sigma * W := by field_simp
    have hPcard : (P.carrier.card : Real) = W := by
      rw [hW_def]; exact_mod_cast boxOne_card_eq_width P hP
    rw [nsmul_eq_mul] at h3
    rw [hPcard] at h1 ⊢
    linarith
  by_cases hIempty : I.card = 0
  · -- No graph is dense in this box: no point of `H` carries a value.
    refine ⟨1, 0, H, fun _ => P, fun _ i => i.elim0, Finset.sdiff_subset, hHmass,
      ⟨fun x => by simp, fun i j hij => absurd (Subsingleton.elim i j) (bne_iff_ne.mp hij)⟩,
      fun _ => hP, by simp, fun _ => hWE, fun _ i => i.elim0, fun j x _ hxH y hxy => ?_⟩
    obtain ⟨i, hxB, -⟩ := hmem (x, y) hxy
    exact absurd (Finset.card_pos.mpr ⟨i, hHU x hxH i hxB⟩) (by omega)
  -- Simultaneous linearization of the dense graphs.
  have hq'pos : 0 < I.card := Nat.pos_of_ne_zero hIempty
  let q' := I.card
  let e : Fin q' → Fin q := fun i' => (I.equivFin.symm i').1
  let R := boxOneIndexAP P
  let A' : Fin q' → Finset Int := fun i' => boxOneIndexDomain P (B (e i'))
  let psi : Fin q' → Int → ZMod N := fun i' => boxOneIndexMap P (phi (e i'))
  set X : Real := W ^ polyBaseCorExponent q sigma with hX
  let m := Nat.floor X
  have hm2 : 2 ≤ m := Nat.le_floor (by push_cast; linarith)
  have hXle : X ≤ (R.length : Real) ^
      ((2 : Real) ^ (-(14 : Real)) * (sigma / q) ^ 2 * (q' : Real)⁻¹) :=
    Real.rpow_le_rpow_of_exponent_le hW1 (mul_le_mul_of_nonneg_left (inv_anti₀
      (by exact_mod_cast hq'pos) (by exact_mod_cast (Finset.card_le_univ I).trans (by simp)))
      (by positivity))
  obtain ⟨M, S, hSpart, hSproper, -, hSlinear⟩ :=
    corollary_7_11_holds N q' m R A' psi (sigma / q) hq'pos (by omega) hη
      (by rw [← Nat.cast_pos (α := Real)]; exact one_pos.trans_le hW1) (boxOneIndexAP_proper P)
      (fun i' => ⟨boxOneIndexDomain_subset P (B (e i')),
        (Finset.mem_filter.mp (I.equivFin.symm i').2).2,
        boxOneIndex_freiman P (B (e i')) (phi (e i')) (hfreiman (e i'))⟩)
      ((Nat.floor_le (by positivity)).trans hXle) (hbig.trans_le hXle)
  have hSsub (j : Fin M) : (S j).carrier ⊆ R.carrier := hSpart.cell_subset j
  have hQproper (j : Fin M) : (indexCellBox P (S j)).IsProper :=
    indexCellBox_proper P hP (S j) (hSproper j).1 (hSsub j)
  have hlen (j : Fin M) : m ≤ (S j).length := by rcases (hSproper j).2 with h | h <;> omega
  choose c d hcd using fun (j : Fin M) (i' : Fin q') => hSlinear i' j
  let mu : Fin M → Fin q → Point N 1 → ZMod N := fun j i =>
    if hi : i ∈ I then indexCellAffine P (S j) (c j (I.equivFin ⟨i, hi⟩))
      (d j (I.equivFin ⟨i, hi⟩)) else fun _ => 0
  refine ⟨M, q, H, fun j => indexCellBox P (S j), mu, Finset.sdiff_subset, hHmass,
    indexCells_partition P hP S hSpart, hQproper, by push_cast; linarith, fun j => ?_,
    fun j i => ?_, fun j x hxQ hxH y hxy => ?_⟩
  · -- the cell widths
    have hsq : (W ^ polyBaseExponent q sigma) ^ 2 ≤ X := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hW0, hX]
      exact Real.rpow_le_rpow_of_exponent_le hW1 (by push_cast; linarith)
    have hy : W ^ polyBaseExponent q sigma ≤ X - 1 := by
      nlinarith [Real.rpow_nonneg hW0 (polyBaseExponent q sigma)]
    have hmj : (m : Real) ≤ (S j).length := by exact_mod_cast hlen j
    simp only [indexCellBox_width]
    linarith [Nat.lt_floor_add_one X]
  · -- the maps are multilinear
    simp only [mu]
    split_ifs
    exacts [indexCellAffine_multilinear P (S j) _ _, isMultilinear_constant 0]
  · -- the cover
    obtain ⟨i, hxB, hy⟩ := hmem (x, y) hxy
    dsimp only at hxB hy
    have hiI := hHU x hxH i hxB
    simp only [indexCellBox_carrier] at hxQ
    obtain ⟨z, hzS, rfl⟩ := Finset.mem_image.mp hxQ
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hzS
    have hei : e (I.equivFin ⟨i, hiI⟩) = i :=
      congrArg Subtype.val (I.equivFin.symm_apply_apply ⟨i, hiI⟩)
    have hvalue := hcd j (I.equivFin ⟨i, hiI⟩) t
      (Finset.mem_filter.mpr ⟨hSsub j hzS, hei.symm ▸ hxB⟩)
    have hstepNe : ((S j).step : ZMod N) * (P.axis 0).step ≠ 0 :=
      proper_modAP_step_ne_zero_of_two_le ((indexCellBox P (S j)).axis 0) (hQproper j 0)
        (by simpa [indexCellBox] using hm2.trans (hlen j))
    refine ⟨i, ?_⟩
    simp only [mu, dif_pos hiI]
    rw [hy, indexCellAffine_value P (S j) _ _ t hstepNe, ← hvalue]
    simp only [psi, boxOneIndexMap, hei]

end LeanProofs.GowersSzemeredi
