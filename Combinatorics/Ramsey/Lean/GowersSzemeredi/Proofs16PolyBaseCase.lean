import GowersSzemeredi.Proofs16BaseCaseLongBoxCover
import GowersSzemeredi.Proofs16RegimeSplitting

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

/-- Multiple multilinearity with arbitrary graph-count and width-exponent
control functions of the requested loss. -/
def MultiplyLinearWith {N k : Nat} [NeZero N] (Qb Eb : Real → Real)
    (Gamma : Finset (Point N k × ZMod N)) : Prop :=
  ∀ theta : Real, 0 < theta → theta ≤ 1 → ∀ P : Box N k, P.IsProper →
    ∃ M q : Nat, ∃ H : Finset (Point N k), ∃ Q : Fin M → Box N k,
      ∃ mu : Fin M → Fin q → Point N k → ZMod N,
        H ⊆ P.carrier ∧ (1 - theta) * P.carrier.card ≤ H.card ∧
        IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
        (q : Real) ≤ Qb theta ∧
        (∀ j, (P.width : Real) ^ (Eb theta) ≤ (Q j).width) ∧
        (∀ j i, IsMultilinear (mu j i)) ∧
        ∀ j x, x ∈ (Q j).carrier → x ∈ H → ∀ y,
          (x, y) ∈ Gamma → ∃ i, y = mu j i x

/-- The source's multiple multilinearity is the instance with its own
control functions. -/
theorem multiplyLinear_iff_with {N k : Nat} [NeZero N] (gamma r : Real)
    (Gamma : Finset (Point N k × ZMod N)) :
    MultiplyLinear gamma r Gamma ↔
      MultiplyLinearWith (fun theta => (multipleQ (r⁻¹ * theta) gamma k) ^ r)
        (fun theta => (multipleC (r⁻¹ * theta) gamma k) ^ r) Gamma :=
  Iff.rfl

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

theorem polyBase_loss_pos (hq : 0 < q) (hs : 0 < sigma) : 0 < sigma / (q : Real) := by
  have : (0 : Real) < q := by exact_mod_cast hq
  positivity

theorem polyBase_loss_le_one (hq : 0 < q) (hs1 : sigma ≤ 1) (hs : 0 < sigma) :
    sigma / (q : Real) ≤ 1 := by
  have hq1 : (1 : Real) ≤ q := by exact_mod_cast hq
  rw [div_le_one (by linarith)]
  linarith

theorem polyBaseCorExponent_pos (hq : 0 < q) (hs : 0 < sigma) :
    0 < polyBaseCorExponent q sigma := by
  have := polyBase_loss_pos hq hs
  have hq0 : (0 : Real) < q := by exact_mod_cast hq
  unfold polyBaseCorExponent
  positivity

theorem polyBaseThreshold_ge_four (hq : 0 < q) (hs : 0 < sigma) (hs1 : sigma ≤ 1) :
    4 ≤ polyBaseThreshold q sigma := by
  have hη := polyBase_loss_pos hq hs
  have hη1 := polyBase_loss_le_one hq hs1 hs
  have hpi := Real.pi_gt_three
  unfold polyBaseThreshold
  rw [le_div_iff₀ hη]
  nlinarith

theorem polyBaseExponent_pos (hq : 0 < q) (hs : 0 < sigma) (hs1 : sigma ≤ 1) :
    0 < polyBaseExponent q sigma := by
  have ha := polyBaseCorExponent_pos hq hs
  have hΛ := polyBaseThreshold_ge_four hq hs hs1
  have hlog : 0 < Real.log (polyBaseThreshold q sigma) := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
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
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
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
  classical
  intro sigma hs hs1 P hP
  -- Every point carries at most `q` values.
  have hmem : ∀ z ∈ Gamma, ∃ i, z.1 ∈ B i ∧ z.2 = phi i z.1 := by
    intro z hz
    have hz' := hcover hz
    rw [section16FinsetUnion, Finset.mem_biUnion] at hz'
    obtain ⟨i, -, hzi⟩ := hz'
    exact ⟨i, (mem_partialGraph_one (B i) (phi i) z.1 z.2).1 hzi⟩
  have hfib : ∀ x : Point N 1, (Gamma.filter fun z => z.1 = x).card ≤ q := by
    intro x
    have hsub : Gamma.filter (fun z => z.1 = x) ⊆
        (Finset.univ : Finset (Fin q)).image (fun i => (x, phi i x)) := by
      intro z hz
      obtain ⟨hzG, hzx⟩ := Finset.mem_filter.mp hz
      obtain ⟨i, -, hzi⟩ := hmem z hzG
      refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, Prod.ext ?_ ?_⟩
      · exact hzx.symm
      · show phi i x = z.2
        rw [hzi, hzx]
    calc (Gamma.filter fun z => z.1 = x).card
        ≤ ((Finset.univ : Finset (Fin q)).image (fun i => (x, phi i x))).card :=
          Finset.card_le_card hsub
      _ ≤ (Finset.univ : Finset (Fin q)).card := Finset.card_image_le
      _ = q := by simp
  set W : Real := (P.width : Real) with hW_def
  have hW0 : 0 ≤ W := Nat.cast_nonneg _
  have hη := polyBase_loss_pos hq hs
  have hη1 := polyBase_loss_le_one hq hs1 hs
  have ha := polyBaseCorExponent_pos hq hs
  have hΛ := polyBaseThreshold_ge_four hq hs hs1
  have hE := polyBaseExponent_pos hq hs hs1
  have hEa := polyBaseExponent_le_half hq hs hs1
  have hcard0 : (0 : Real) ≤ (P.carrier.card : Real) := Nat.cast_nonneg _
  by_cases hbig : polyBaseThreshold q sigma < W ^ polyBaseCorExponent q sigma
  swap
  · -- Small boxes: the exact coarse cover.
    push Not at hbig
    obtain ⟨L, R, mu, hpart, hproper, hwidth, hmu, hcov⟩ :=
      section16_coarse_relation_cover (by norm_num : 0 < 1) Gamma q hfib P hP
    refine ⟨L, 3 ^ 1 * q, P.carrier, R, mu, Finset.Subset.refl _, ?_, hpart, hproper,
      le_rfl, ?_, hmu, fun j x hx _ y hy => hcov j x hx y hy⟩
    · nlinarith [mul_nonneg hs.le hcard0]
    · intro j
      have hmin : W ^ polyBaseExponent q sigma ≤ ((min 2 P.width : Nat) : Real) := by
        rcases Nat.lt_or_ge P.width 2 with hlt | hge
        · rw [min_eq_right hlt.le]
          rcases (by omega : P.width = 0 ∨ P.width = 1) with h0 | h1
          · rw [hW_def, h0]
            simp [Real.zero_rpow hE.ne']
          · rw [hW_def, h1]
            simp
        · rw [min_eq_left hge]
          exact_mod_cast polyBase_small_width hW0 hq hs hs1 hbig
      exact hmin.trans (by exact_mod_cast hwidth j)
  -- Large boxes.
  have hX4 : 4 < W ^ polyBaseCorExponent q sigma := lt_of_le_of_lt hΛ hbig
  have hW1 : 1 ≤ W := by
    by_contra hlt
    push Not at hlt
    have := Real.rpow_le_one hW0 hlt.le ha.le
    linarith
  let I : Finset (Fin q) := Finset.univ.filter fun i =>
    sigma / (q : Real) * W ≤ ((boxOneIndexDomain P (B i)).card : Real)
  let H : Finset (Point N 1) := P.carrier.filter fun x => ∀ i, i ∉ I → x ∉ B i
  have hHsub : H ⊆ P.carrier := Finset.filter_subset _ _
  have hPcard : (P.carrier.card : Real) = W := by
    rw [hW_def]
    exact_mod_cast boxOne_card_eq_width P hP
  have hHmass : (1 - sigma) * (P.carrier.card : Real) ≤ H.card := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := P.carrier) (fun x => ∀ i, i ∉ I → x ∉ B i)
    have hbad : ((P.carrier.filter fun x => ¬ ∀ i, i ∉ I → x ∉ B i).card : Real) ≤
        sigma * W := by
      have hsub : (P.carrier.filter fun x => ¬ ∀ i, i ∉ I → x ∉ B i) ⊆
          (Finset.univ.filter fun i => i ∉ I).biUnion (fun i => B i ∩ P.carrier) := by
        intro x hx
        obtain ⟨hxP, hx⟩ := Finset.mem_filter.mp hx
        push Not at hx
        obtain ⟨i, hiI, hxB⟩ := hx
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiI⟩,
          Finset.mem_inter.mpr ⟨hxB, hxP⟩⟩
      have hle : ((P.carrier.filter fun x => ¬ ∀ i, i ∉ I → x ∉ B i).card : Real) ≤
          ∑ i ∈ Finset.univ.filter (fun i => i ∉ I), ((B i ∩ P.carrier).card : Real) := by
        exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      have hterm : ∀ i ∈ Finset.univ.filter (fun i => i ∉ I),
          ((B i ∩ P.carrier).card : Real) ≤ sigma / (q : Real) * W := by
        intro i hi
        have hiI := (Finset.mem_filter.mp hi).2
        have hnot : ¬ (sigma / (q : Real) * W ≤ ((boxOneIndexDomain P (B i)).card : Real)) := by
          intro h
          exact hiI (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        rw [← boxOneIndexDomain_card P hP (B i)]
        push Not at hnot
        exact hnot.le
      have hsum := Finset.sum_le_sum hterm
      rw [Finset.sum_const, nsmul_eq_mul] at hsum
      have hcount : ((Finset.univ.filter fun i : Fin q => i ∉ I).card : Real) ≤ q := by
        exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
      have hq0 : (0 : Real) < q := by exact_mod_cast hq
      calc _ ≤ _ := hle
        _ ≤ _ := hsum
        _ ≤ (q : Real) * (sigma / (q : Real) * W) :=
            mul_le_mul_of_nonneg_right hcount (by positivity)
        _ = sigma * W := by field_simp [hq0.ne']
    have hsplitR : (H.card : Real) +
        ((P.carrier.filter fun x => ¬ ∀ i, i ∉ I → x ∉ B i).card : Real) =
        (P.carrier.card : Real) := by exact_mod_cast hsplit
    rw [hPcard] at hsplitR ⊢
    nlinarith
  by_cases hIempty : I.card = 0
  · -- No graph is dense in this box: no point of `H` carries a value.
    have hIe : I = ∅ := Finset.card_eq_zero.mp hIempty
    refine ⟨1, 0, H, fun _ => P, fun _ i => i.elim0, hHsub, hHmass, ?_, fun _ => hP,
      ?_, ?_, fun _ i => i.elim0, ?_⟩
    · constructor
      · intro x
        simp
      · intro i j hij
        exact ((bne_iff_ne.mp hij) (Subsingleton.elim i j)).elim
    · show ((0 : Nat) : Real) ≤ ((3 ^ 1 * q : Nat) : Real)
      exact_mod_cast Nat.zero_le _
    · intro _
      show W ^ polyBaseExponent q sigma ≤ W
      have hE1 : polyBaseExponent q sigma ≤ 1 := by
        have : polyBaseCorExponent q sigma ≤ 1 := by
          unfold polyBaseCorExponent
          have hq1 : (1 : Real) ≤ q := by exact_mod_cast hq
          have hsq : (sigma / q) ^ 2 ≤ 1 := pow_le_one₀ hη.le hη1
          have hinv : (q : Real)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq1
          have h2 : (2 : Real) ^ (-(14 : Real)) ≤ 1 :=
            Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
          calc (2 : Real) ^ (-(14 : Real)) * (sigma / q) ^ 2 * (q : Real)⁻¹
              ≤ 1 * 1 * 1 := by gcongr
            _ = 1 := by norm_num
        linarith
      calc W ^ polyBaseExponent q sigma ≤ W ^ (1 : Real) :=
            Real.rpow_le_rpow_of_exponent_le hW1 hE1
        _ = W := Real.rpow_one W
    · intro j x _ hxH y hxy
      obtain ⟨i, hxB, -⟩ := hmem (x, y) hxy
      dsimp only at hxB
      have hall := (Finset.mem_filter.mp hxH).2
      exact ((hall i (by simp [hIe])) hxB).elim
  -- Simultaneous linearization of the dense graphs.
  have hq'pos : 0 < I.card := Nat.pos_of_ne_zero hIempty
  let q' := I.card
  let e : Fin q' → Fin q := fun i' => (I.equivFin.symm i').1
  have he_mem : ∀ i', e i' ∈ I := fun i' => (I.equivFin.symm i').2
  let R := boxOneIndexAP P
  let A' : Fin q' → Finset Int := fun i' => boxOneIndexDomain P (B (e i'))
  let psi : Fin q' → Int → ZMod N := fun i' => boxOneIndexMap P (phi (e i'))
  set X : Real := W ^ polyBaseCorExponent q sigma with hX
  let m := Nat.floor X
  have hm2 : 2 ≤ m := Nat.le_floor (by push_cast; linarith)
  have hm : 0 < m := by omega
  have hRlen : (R.length : Real) = W := rfl
  have hRpos : 0 < R.length := by
    have : (0 : Real) < R.length := by rw [hRlen]; linarith
    exact_mod_cast this
  have hq'q : q' ≤ q := (Finset.card_le_univ I).trans (by simp)
  have hexp' : polyBaseCorExponent q sigma ≤
      (2 : Real) ^ (-(14 : Real)) * (sigma / q) ^ 2 * (q' : Real)⁻¹ := by
    unfold polyBaseCorExponent
    have hq'0 : (0 : Real) < q' := by exact_mod_cast hq'pos
    have hinv : (q : Real)⁻¹ ≤ (q' : Real)⁻¹ :=
      inv_anti₀ hq'0 (by exact_mod_cast hq'q)
    have hc : 0 ≤ (2 : Real) ^ (-(14 : Real)) * (sigma / q) ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left hinv hc
  have hXle : X ≤ (R.length : Real) ^
      ((2 : Real) ^ (-(14 : Real)) * (sigma / q) ^ 2 * (q' : Real)⁻¹) := by
    rw [hRlen, hX]
    exact Real.rpow_le_rpow_of_exponent_le hW1 hexp'
  have hmBound : (m : Real) ≤ (R.length : Real) ^
      ((2 : Real) ^ (-(14 : Real)) * (sigma / q) ^ 2 * (q' : Real)⁻¹) :=
    (Nat.floor_le (by positivity)).trans hXle
  have hcorLarge : 1024 * Real.pi / (sigma / q) < (R.length : Real) ^
      ((2 : Real) ^ (-(14 : Real)) * (sigma / q) ^ 2 * (q' : Real)⁻¹) := by
    have h : polyBaseThreshold q sigma < X := hbig
    unfold polyBaseThreshold at h
    exact lt_of_lt_of_le h hXle
  have hAvec : ∀ i', A' i' ⊆ R.carrier ∧
      sigma / q * R.length ≤ (A' i').card ∧ FreimanHom 8 (A' i') (psi i') := by
    intro i'
    refine ⟨boxOneIndexDomain_subset P (B (e i')), ?_, ?_⟩
    · rw [hRlen]
      exact (Finset.mem_filter.mp (he_mem i')).2
    · exact boxOneIndex_freiman P (B (e i')) (phi (e i')) (hfreiman (e i'))
  obtain ⟨M, S, hSpart, hSproper, _hSstep, hSlinear⟩ :=
    corollary_7_11_holds N q' m R A' psi (sigma / q) hq'pos hm hη hRpos
      (boxOneIndexAP_proper P) hAvec hmBound hcorLarge
  have hSsub (j : Fin M) : (S j).carrier ⊆ R.carrier := hSpart.cell_subset j
  have hQproper (j : Fin M) : (indexCellBox P (S j)).IsProper :=
    indexCellBox_proper P hP (S j) (hSproper j).1 (hSsub j)
  choose c d hcd using fun (j : Fin M) (i' : Fin q') => hSlinear i' j
  let Q : Fin M → Box N 1 := fun j => indexCellBox P (S j)
  let mu : Fin M → Fin q → Point N 1 → ZMod N := fun j i =>
    if hi : i ∈ I then indexCellAffine P (S j) (c j (I.equivFin ⟨i, hi⟩))
      (d j (I.equivFin ⟨i, hi⟩)) else fun _ => 0
  refine ⟨M, q, H, Q, mu, hHsub, hHmass, indexCells_partition P hP S hSpart, hQproper,
    ?_, ?_, ?_, ?_⟩
  · show (q : Real) ≤ ((3 ^ 1 * q : Nat) : Real)
    have hq0 : (0 : Real) ≤ q := Nat.cast_nonneg _
    push_cast
    linarith
  · intro j
    have hmj : m ≤ (S j).length := by
      rcases (hSproper j).2 with h | h <;> omega
    have hwidthM : W ^ polyBaseExponent q sigma ≤ m := by
      have hyNonneg : 0 ≤ W ^ polyBaseExponent q sigma := by positivity
      have hsq : (W ^ polyBaseExponent q sigma) ^ 2 ≤ X := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hW0, hX]
        apply Real.rpow_le_rpow_of_exponent_le hW1
        push_cast
        linarith
      have hy : W ^ polyBaseExponent q sigma ≤ X - 1 := by nlinarith
      have hfloor : X < (m : Real) + 1 := Nat.lt_floor_add_one X
      linarith
    show W ^ polyBaseExponent q sigma ≤ ((indexCellBox P (S j)).width : Real)
    rw [indexCellBox_width]
    exact hwidthM.trans (by exact_mod_cast hmj)
  · intro j i
    by_cases hi : i ∈ I
    · simp only [mu, dif_pos hi]
      exact indexCellAffine_multilinear P (S j) _ _
    · simp only [mu, dif_neg hi]
      exact isMultilinear_constant 0
  · intro j x hxQ hxH y hxy
    obtain ⟨i, hxB, hy⟩ := hmem (x, y) hxy
    dsimp only at hxB hy
    have hiI : i ∈ I := by
      by_contra hiI
      exact (Finset.mem_filter.mp hxH).2 i hiI hxB
    set i' := I.equivFin ⟨i, hiI⟩ with hi'
    have hei : e i' = i := by
      show (I.equivFin.symm i').1 = i
      rw [hi', Equiv.symm_apply_apply]
    refine ⟨i, ?_⟩
    simp only [mu, dif_pos hiI]
    rw [← hi']
    change x ∈ (indexCellBox P (S j)).carrier at hxQ
    rw [indexCellBox_carrier] at hxQ
    obtain ⟨z, hzS, hzx⟩ := Finset.mem_image.mp hxQ
    rw [IntAP.carrier] at hzS
    obtain ⟨t, _ht, htz⟩ := Finset.mem_image.mp hzS
    have hzx' : boxOneIntPoint P ((S j).start + ((t : Nat) * (S j).step : Nat)) = x :=
      (congrArg (boxOneIntPoint P) htz).trans hzx
    have hzA : (S j).start + ((t : Nat) * (S j).step : Nat) ∈ A' i' := by
      change (S j).start + ((t : Nat) * (S j).step : Nat) ∈
        boxOneIndexDomain P (B (e i'))
      rw [boxOneIndexDomain, Finset.mem_filter]
      refine ⟨hSsub j ?_, ?_⟩
      · rw [IntAP.carrier]
        exact Finset.mem_image.mpr ⟨t, _ht, rfl⟩
      · rw [hzx', hei]
        exact hxB
    have hvalue : psi i' ((S j).start + ((t : Nat) * (S j).step : Nat)) =
        c j i' * (t : Nat) + d j i' := hcd j i' t hzA
    have hm2j : 2 ≤ (S j).length := by
      rcases (hSproper j).2 with h | h <;> omega
    have hstepNe : ((S j).step : ZMod N) * (P.axis 0).step ≠ 0 := by
      exact proper_modAP_step_ne_zero_of_two_le ((indexCellBox P (S j)).axis 0)
        (hQproper j 0) (by simpa [indexCellBox] using hm2j)
    rw [hy, ← hzx', indexCellAffine_value P (S j) (c j i') (d j i') t hstepNe]
    rw [← hvalue]
    simp only [psi, boxOneIndexMap, hei]

end LeanProofs.GowersSzemeredi
