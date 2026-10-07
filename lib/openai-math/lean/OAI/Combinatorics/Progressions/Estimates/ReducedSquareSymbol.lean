import OAI.Combinatorics.Progressions.Polynomial.SquarePolynomialCoordinates

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t : ℕ}
  (F : NilpotentLieFiltration L s)

theorem quotientLie_mem_iff (I : LieIdeal ℚ L) (hI : F.layer (t + 1) ≤ I.toSubmodule)
    (j : ℕ) (x : L) :
    lieQuotientMap I x ∈ (F.quotientLie I hI).layer j ↔ x ∈ F.layer j ⊔ I.toSubmodule := by
  change x ∈ ((F.layer j).map I.toSubmodule.mkQ).comap I.toSubmodule.mkQ ↔ _
  rw [Submodule.comap_map_mkQ, sup_comm]

noncomputable def quotientGradedMap (I : LieIdeal ℚ L) (hI : F.layer (t + 1) ≤ I.toSubmodule) :
    F.AssociatedGraded →ₗ⁅ℚ⁆ (F.quotientLie I hI).AssociatedGraded :=
  F.associatedGradedMap (F.quotientLie I hI) (lieQuotientMap I)
    (fun _ _ hx => F.quotientLie_mem I hI hx)

@[simp] theorem quotientGradedMap_piece (I : LieIdeal ℚ L) (hI : F.layer (t + 1) ≤ I.toSubmodule)
    (j : ℕ) (x : F.layer j) :
    F.quotientGradedMap I hI (F.associatedGradedPieceMap j x) =
      (F.quotientLie I hI).associatedGradedPieceMap j
        ⟨lieQuotientMap I x, F.quotientLie_mem I hI x.property⟩ :=
  F.associatedGradedMap_piece _ _ _ j x

theorem quotientGradedMap_piece_eq_zero_iff (I : LieIdeal ℚ L)
    (hI : F.layer (t + 1) ≤ I.toSubmodule) (j : ℕ) (x : F.layer j) :
    F.quotientGradedMap I hI (F.associatedGradedPieceMap j x) = 0 ↔
      (x : L) ∈ F.layer (j + 1) ⊔ I.toSubmodule := by
  rw [F.quotientGradedMap_piece, associatedGradedPieceMap_eq_zero_iff,
    F.quotientLie_mem_iff]

variable (F : NilpotentLieFiltration L (s + 1))

noncomputable def quotientTopGradedMap : F.AssociatedGraded →ₗ⁅ℚ⁆ F.quotientTop.AssociatedGraded :=
  F.quotientGradedMap (F.layerIdeal (s + 1)) le_rfl

theorem quotientTopGradedMap_piece_eq_zero_iff (j : ℕ) (hj : j ≤ s) (x : F.layer j) :
    F.quotientTopGradedMap (F.associatedGradedPieceMap j x) = 0 ↔ (x : L) ∈ F.layer (j + 1) := by
  have hle : (F.layerIdeal (s + 1)).toSubmodule ≤ F.layer (j + 1) :=
    F.antitone (Nat.add_le_add_right hj 1)
  have h := F.quotientGradedMap_piece_eq_zero_iff (F.layerIdeal (s + 1)) (t := s) le_rfl j x
  rw [sup_eq_left.mpr hle] at h
  convert h using 1
  rfl

theorem quotientTopGradedMap_top (x : F.layer (s + 1)) :
    F.quotientTopGradedMap (F.associatedGradedPieceMap (s + 1) x) = 0 := by
  apply (F.quotientGradedMap_piece_eq_zero_iff (F.layerIdeal (s + 1)) le_rfl (s + 1) x).mpr
  exact (show (F.layerIdeal (s + 1)).toSubmodule ≤
    F.layer (s + 1 + 1) ⊔ (F.layerIdeal (s + 1)).toSubmodule from le_sup_right) x.property

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem mem_normalizedRelative_iff_firstJet (w : σ → ℕ) (p : F.adaptedLieSubalgebra w) :
    p ∈ F.normalizedRelativeSubmodule w ↔
      F.filteredFirstJetMap w p ∈ F.normalizedFirstJetKernel w := by
  change (p ∈ F.shiftedAdaptedIdeal w ∧ coefficients p.val 0 ∈ F.layer 2) ↔
    (F.polynomialSymbolMap w p = 0 ∧ (F.layer 2).mkQ (coefficients p.val 0) = 0)
  rw [F.polynomialSymbolMap_eq_zero_iff]
  constructor
  · rintro ⟨hp, hc⟩
    exact ⟨hp, (Submodule.Quotient.mk_eq_zero _).mpr hc⟩
  · rintro ⟨hp, hc⟩
    exact ⟨hp, (Submodule.Quotient.mk_eq_zero _).mp hc⟩

theorem normalizedRelative_mem_of_firstJet_eq (w : σ → ℕ) {p q : F.adaptedLieSubalgebra w}
    (hp : p ∈ F.normalizedRelativeSubmodule w)
    (hpq : F.filteredFirstJetMap w p = F.filteredFirstJetMap w q) :
    q ∈ F.normalizedRelativeSubmodule w := by
  rw [F.mem_normalizedRelative_iff_firstJet] at hp ⊢
  rw [← hpq]
  exact hp

variable (h : σ → ℚ) (e m : L)
  (p : F.adaptedLieSubalgebra (fun _ : σ => 1))

theorem normalizedRelativeLog_shifted :
    F.normalizedRelativeLog h e m p ∈ F.shiftedAdaptedIdeal (fun _ : σ => 1) := by
  apply (F.polynomialSymbolMap_eq_zero_iff (fun _ => 1) _).mp
  change F.polynomialSymbolMap (fun _ => 1)
    (lieBCH s (F.normalizedShiftAdapted h (-e) (-m) p) (-p)) = 0
  rw [map_lieBCH, map_neg]
  have he : F.polynomialSymbolMap (fun _ => 1) (F.normalizedShiftAdapted h (-e) (-m) p) =
      F.polynomialSymbolMap (fun _ => 1) p := by
    apply (F.polynomialSymbolMap_eq_iff (fun _ => 1) _ _).mpr
    exact F.normalizedShiftLog_sub_coefficient_mem (fun _ => 1) (by simp) h (-e) (-m)
      ((F.mem_adaptedSubmodule (fun _ => 1) _).mp p.property)
  rw [he]
  exact congrArg NilpotentLieBCHGroup.coord
    (mul_inv_cancel (⟨F.polynomialSymbolMap (fun _ => 1) p⟩ :
      F.PolynomialSymbolGroup (fun _ : σ => 1)))

theorem normalizedRelativeLog_horizontal
    (hzero : coefficients (normalizedShiftLog s h (-e) (-m) p.val - p.val) 0 ∈ F.layer 2) :
    coefficients (F.normalizedRelativeLog h e m p).val 0 ∈ F.layer 2 := by
  apply (lieQuotientMap_eq_zero (F.layerIdeal 2) _).mp
  rw [← eval_zero_eq_coefficient]
  change lieQuotientMap (F.layerIdeal 2)
    (eval (0 : σ → ℚ) ((F.adaptedLieSubalgebra (fun _ => 1)).incl
      (lieBCH s (F.normalizedShiftAdapted h (-e) (-m) p) (-p)))) = 0
  rw [map_lieBCH, eval_lieBCH, F.horizontal_bch, map_neg, map_neg, map_neg]
  have hz := (lieQuotientMap_eq_zero (F.layerIdeal 2) _).mpr hzero
  rw [← eval_zero_eq_coefficient, map_sub, map_sub] at hz
  rw [sub_eq_add_neg] at hz
  exact hz

theorem normalizedRelativeLog_mem
    (hzero : coefficients (normalizedShiftLog s h (-e) (-m) p.val - p.val) 0 ∈ F.layer 2) :
    F.normalizedRelativeLog h e m p ∈ F.normalizedRelativeSubmodule (fun _ : σ => 1) :=
  ⟨F.normalizedRelativeLog_shifted h e m p, F.normalizedRelativeLog_horizontal h e m p hzero⟩

variable [Fintype σ]

noncomputable def differentiatedRelativeLog : F.adaptedLieSubalgebra (fun _ : σ => 1) :=
  F.adaptedLogDerivative h p - F.adaptedConstant (fun _ => 1) e -
    dualAdjoint (⟨p⟩ : (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
      (F.adaptedConstant (fun _ => 1) m)

theorem differentiatedRelativeLog_mem
    (hzero : coefficients (normalizedShiftLog s h (-e) (-m) p.val - p.val) 0 ∈ F.layer 2) :
    F.differentiatedRelativeLog h e m p ∈ F.normalizedRelativeSubmodule (fun _ : σ => 1) :=
  F.normalizedRelative_mem_of_firstJet_eq (fun _ => 1)
    (F.normalizedRelativeLog_mem h e m p hzero) (F.filteredFirstJet_normalizedRelativeLog h e m p)

theorem normalizedRelative_square_symbol
    (hzero : coefficients (normalizedShiftLog s h (-e) (-m) p.val - p.val) 0 ∈ F.layer 2) :
    F.relativeSquareSymbolMap (fun _ => 1) (by simp)
        ⟨F.normalizedRelativeLog h e m p, F.normalizedRelativeLog_mem h e m p hzero⟩ =
      F.relativeSquareSymbolMap (fun _ => 1) (by simp)
        ⟨F.differentiatedRelativeLog h e m p, F.differentiatedRelativeLog_mem h e m p hzero⟩ := by
  apply (F.relativeSquareSymbolMap_eq_iff (fun _ => 1) (by simp) _ _).mpr
  exact F.filteredFirstJet_normalizedRelativeLog h e m p

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

noncomputable def reducedSquareGradedDiagonalPiece (j : ℕ) :
    F.layer j →ₗ[ℚ] F.squareFiltration.quotientTop.AssociatedGraded :=
  F.squareFiltration.quotientTopGradedMap.toLinearMap.comp (F.squareGradedDiagonalPiece j)

noncomputable def reducedSquareGradedRelativePiece (j : ℕ) (hj : 1 ≤ j) :
    F.layer (j + 1) →ₗ[ℚ] F.squareFiltration.quotientTop.AssociatedGraded :=
  F.squareFiltration.quotientTopGradedMap.toLinearMap.comp (F.squareGradedRelativePiece j hj)

theorem reducedSquareGradedDiagonalPiece_eq_zero_iff (j : ℕ) (hj : j ≤ s) (x : F.layer j) :
    F.reducedSquareGradedDiagonalPiece j x = 0 ↔ (x : L) ∈ F.layer (j + 1) := by
  change F.squareFiltration.quotientTopGradedMap
    (F.squareFiltration.associatedGradedPieceMap j (F.squareDiagonalLayer j x)) = 0 ↔ _
  rw [F.squareFiltration.quotientTopGradedMap_piece_eq_zero_iff j hj]
  exact (F.squareFiltration.associatedGradedPieceMap_eq_zero_iff j _).symm.trans
    (F.squareGradedDiagonalPiece_eq_zero_iff j x)

theorem reducedSquareGradedRelativePiece_eq_zero_iff (j : ℕ) (hpos : 1 ≤ j) (hj : j ≤ s)
    (x : F.layer (j + 1)) :
    F.reducedSquareGradedRelativePiece j hpos x = 0 ↔ (x : L) ∈ F.layer (j + 2) := by
  change F.squareFiltration.quotientTopGradedMap
    (F.squareFiltration.associatedGradedPieceMap j (F.squareRelativeLayer j hpos x)) = 0 ↔ _
  rw [F.squareFiltration.quotientTopGradedMap_piece_eq_zero_iff j hj]
  exact (F.squareFiltration.associatedGradedPieceMap_eq_zero_iff j _).symm.trans
    (F.squareGradedRelativePiece_eq_zero_iff j hpos x)

theorem reducedSquareGradedRelative_top_injective (hs : 1 ≤ s) :
    Function.Injective (F.reducedSquareGradedRelativePiece s hs) := by
  intro x y hxy
  have hz : F.reducedSquareGradedRelativePiece s hs (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have h := (F.reducedSquareGradedRelativePiece_eq_zero_iff s hs le_rfl (x - y)).mp hz
  apply Subtype.ext
  apply sub_eq_zero.mp
  simpa only [Submodule.coe_sub, F.terminal, Submodule.mem_bot] using h

theorem reducedSquareGradedDiagonal_top (x : F.layer (s + 1)) :
    F.reducedSquareGradedDiagonalPiece (s + 1) x = 0 :=
  F.squareFiltration.quotientTopGradedMap_top (F.squareDiagonalLayer (s + 1) x)

theorem reducedSquareGradedDiagonal_lie (i j : ℕ) (x : F.layer i) (y : F.layer j) :
    ⁅F.reducedSquareGradedDiagonalPiece i x, F.reducedSquareGradedDiagonalPiece j y⁆ =
      F.reducedSquareGradedDiagonalPiece (i + j)
        ⟨⁅(x : L), (y : L)⁆, F.lie_mem x.property y.property⟩ := by
  exact (F.squareFiltration.quotientTopGradedMap.map_lie _ _).symm.trans
    (congrArg F.squareFiltration.quotientTopGradedMap (F.squareGradedDiagonalPiece_lie i j x y))

theorem reducedSquareGradedDiagonal_relative_lie (i j : ℕ) (hj : 1 ≤ j)
    (x : F.layer i) (y : F.layer (j + 1)) :
    ⁅F.reducedSquareGradedDiagonalPiece i x, F.reducedSquareGradedRelativePiece j hj y⁆ =
      F.reducedSquareGradedRelativePiece (i + j) (by omega)
        ⟨⁅(x : L), (y : L)⁆, by simpa only [Nat.add_assoc] using F.lie_mem x.property y.property⟩ := by
  exact (F.squareFiltration.quotientTopGradedMap.map_lie _ _).symm.trans
    (congrArg F.squareFiltration.quotientTopGradedMap (F.squareGradedDiagonal_relative_lie i j hj x y))

theorem reducedSquareGradedRelative_lie (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j)
    (x : F.layer (i + 1)) (y : F.layer (j + 1)) :
    ⁅F.reducedSquareGradedRelativePiece i hi x, F.reducedSquareGradedRelativePiece j hj y⁆ = 0 := by
  exact (F.squareFiltration.quotientTopGradedMap.map_lie _ _).symm.trans
    ((congrArg F.squareFiltration.quotientTopGradedMap
      (F.squareGradedRelativePiece_lie_eq_zero i j hi hj x y)).trans
        (map_zero F.squareFiltration.quotientTopGradedMap))

noncomputable def reducedSquareGradedRelativeSubalgebra :
    LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded :=
  F.squareGradedRelativeSubalgebra.map F.squareFiltration.quotientTopGradedMap

theorem reducedSquareGradedRelativeSubalgebra_lie_eq_zero
    {x y : F.squareFiltration.quotientTop.AssociatedGraded}
    (hx : x ∈ F.reducedSquareGradedRelativeSubalgebra)
    (hy : y ∈ F.reducedSquareGradedRelativeSubalgebra) : ⁅x, y⁆ = 0 := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact (F.squareFiltration.quotientTopGradedMap.map_lie a b).symm.trans
    ((congrArg F.squareFiltration.quotientTopGradedMap
      (F.squareGradedRelative_lie_eq_zero ha hb)).trans (map_zero F.squareFiltration.quotientTopGradedMap))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

theorem square_relative_diagonal_factorization
    (r : F.squareFiltration.adaptedLieSubalgebra w) (q p : F.adaptedLieSubalgebra w)
    (y : F.normalizedRelativeSubmodule w)
    (hf : F.squareFstPolynomialMap w r = q) (hs : F.squareSndPolynomialMap w r = p)
    (hy : y.val = lieBCH s q (-p)) :
    r = lieBCH s (F.relativeSquareLift w hw y) (F.squareDiagonalPolynomialMap w p) := by
  apply F.square_polynomial_ext w
  · rw [hf, map_lieBCH, F.squareFstPolynomialMap_relative, F.squareFstPolynomialMap_diagonal, hy]
    have he : ((⟨q⟩ : (F.adaptedPolynomialFiltration w).Group) * ⟨p⟩⁻¹) * ⟨p⟩ = ⟨q⟩ := by group
    exact (congrArg NilpotentLieBCHGroup.coord he).symm
  · rw [hs, map_lieBCH, F.squareSndPolynomialMap_relative, F.squareSndPolynomialMap_diagonal]
    exact (lieBCH_zero_left (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot p).symm

variable [Fintype σ] (h : σ → ℚ) (e m : L)
  (p : F.adaptedLieSubalgebra (fun _ : σ => 1))

theorem normalized_square_symbol_factorization
    (hzero : coefficients (normalizedShiftLog s h (-e) (-m) p.val - p.val) 0 ∈ F.layer 2)
    (r : F.squareFiltration.adaptedLieSubalgebra (fun _ : σ => 1))
    (hf : F.squareFstPolynomialMap (fun _ => 1) r = F.normalizedShiftAdapted h (-e) (-m) p)
    (hs : F.squareSndPolynomialMap (fun _ => 1) r = p) :
    F.squareFiltration.polynomialSymbolMap (fun _ => 1) r =
      lieBCH s
        (F.relativeSquareSymbolMap (fun _ => 1) (by simp)
          ⟨F.differentiatedRelativeLog h e m p, F.differentiatedRelativeLog_mem h e m p hzero⟩)
        (F.squareDiagonalSymbolMap (fun _ => 1) (F.polynomialSymbolMap (fun _ => 1) p)) := by
  have hr := F.square_relative_diagonal_factorization (fun _ => 1) (by simp) r
    (F.normalizedShiftAdapted h (-e) (-m) p) p
    ⟨F.normalizedRelativeLog h e m p, F.normalizedRelativeLog_mem h e m p hzero⟩ hf hs rfl
  rw [hr, map_lieBCH]
  change lieBCH s
    (F.relativeSquareSymbolMap (fun _ => 1) (by simp)
      ⟨F.normalizedRelativeLog h e m p, F.normalizedRelativeLog_mem h e m p hzero⟩)
    (F.squareFiltration.polynomialSymbolMap (fun _ => 1) (F.squareDiagonalPolynomialMap (fun _ => 1) p)) = _
  rw [F.normalizedRelative_square_symbol h e m p hzero, F.squareDiagonalSymbolMap_symbol]

theorem exists_normalized_square_symbol_factorization
    (hzero : coefficients (normalizedShiftLog s h (-e) (-m) p.val - p.val) 0 ∈ F.layer 2) :
    ∃ r : F.squareFiltration.adaptedLieSubalgebra (fun _ : σ => 1),
      F.squareFstPolynomialMap (fun _ => 1) r = F.normalizedShiftAdapted h (-e) (-m) p ∧
      F.squareSndPolynomialMap (fun _ => 1) r = p ∧
      F.squareFiltration.polynomialSymbolMap (fun _ => 1) r =
        lieBCH s
          (F.relativeSquareSymbolMap (fun _ => 1) (by simp)
            ⟨F.differentiatedRelativeLog h e m p, F.differentiatedRelativeLog_mem h e m p hzero⟩)
          (F.squareDiagonalSymbolMap (fun _ => 1) (F.polynomialSymbolMap (fun _ => 1) p)) := by
  obtain ⟨r, hr, hf, hs⟩ := F.exists_normalized_shift_square (fun _ => 1) (by simp) h (-e) (-m)
    p.val ((F.mem_adaptedSubmodule (fun _ => 1) _).mp p.property) hzero
  let r' : F.squareFiltration.adaptedLieSubalgebra (fun _ : σ => 1) :=
    ⟨r, (F.squareFiltration.mem_adaptedSubmodule (fun _ => 1) _).mpr hr⟩
  have hf' : F.squareFstPolynomialMap (fun _ => 1) r' = F.normalizedShiftAdapted h (-e) (-m) p :=
    Subtype.ext hf
  have hs' : F.squareSndPolynomialMap (fun _ => 1) r' = p := Subtype.ext hs
  exact ⟨r', hf', hs', F.normalized_square_symbol_factorization h e m p hzero r' hf' hs'⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (h : σ → ℚ)

theorem adaptedLogDerivative_sub_mem {p q : F.adaptedLieSubalgebra (fun _ : σ => 1)}
    (hpq : F.polynomialSymbolMap (fun _ => 1) p = F.polynomialSymbolMap (fun _ => 1) q) :
    F.adaptedLogDerivative h p - F.adaptedLogDerivative h q ∈
      F.shiftedPolynomialIdeal (fun _ : σ => 1) 2 := by
  have hd : p - q ∈ F.shiftedPolynomialIdeal (fun _ : σ => 1) 1 :=
    (F.polynomialSymbolMap_eq_iff (fun _ => 1) p q).mp hpq
  have hbracket : ∀ x ∈ F.shiftedPolynomialIdeal (fun _ : σ => 1) 1,
      ∀ y ∈ F.shiftedPolynomialIdeal (fun _ : σ => 1) 1,
        ⁅x, y⁆ ∈ F.shiftedPolynomialIdeal (fun _ : σ => 1) 2 := by
    intro x hx y hy
    exact F.shiftedPolynomialIdeal_lie_mem (fun _ => 1) (i := 1) (j := 1) hx hy
  apply dualLogDerivative_sub_mem _ _ hbracket
    (F.adaptedPolynomialJet h p) (F.adaptedPolynomialJet h q)
  · rw [F.adaptedPolynomialJet_tangent]
    exact F.directionalDerivative_mem_next h p
  · rw [F.adaptedPolynomialJet_tangent]
    exact F.directionalDerivative_mem_next h q
  · constructor
    · simpa only [map_sub, F.adaptedPolynomialJet_base] using hd
    · have ht := F.adaptedDirectionalDerivative_mem_shifted h 1 hd
      rw [map_sub] at ht
      simpa only [map_sub, F.adaptedPolynomialJet_tangent] using ht

omit [Fintype σ] in
theorem adaptedAdjointConstant_sub_mem {p q : F.adaptedLieSubalgebra (fun _ : σ => 1)}
    (hpq : F.polynomialSymbolMap (fun _ => 1) p = F.polynomialSymbolMap (fun _ => 1) q)
    {m n : L} (hmn : m - n ∈ F.layer 2) :
    dualAdjoint (⟨p⟩ : (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
        (F.adaptedConstant (fun _ => 1) m) -
      dualAdjoint (⟨q⟩ : (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
        (F.adaptedConstant (fun _ => 1) n) ∈ F.shiftedPolynomialIdeal (fun _ : σ => 1) 2 := by
  have hd : p - q ∈ F.shiftedPolynomialIdeal (fun _ : σ => 1) 1 :=
    (F.polynomialSymbolMap_eq_iff (fun _ => 1) p q).mp hpq
  have hbracket : ∀ x ∈ F.shiftedPolynomialIdeal (fun _ : σ => 1) 1,
      ∀ y ∈ F.shiftedPolynomialIdeal (fun _ : σ => 1) 1,
        ⁅x, y⁆ ∈ F.shiftedPolynomialIdeal (fun _ : σ => 1) 2 := by
    intro x hx y hy
    exact F.shiftedPolynomialIdeal_lie_mem (fun _ => 1) (i := 1) (j := 1) hx hy
  apply dualAdjoint_sub_mem _ _ hbracket _ _ _ _
    (F.adaptedConstant_mem_shiftedIdeal (fun _ => 1) m)
    (F.adaptedConstant_mem_shiftedIdeal (fun _ => 1) n) hd
  change F.adaptedConstantLieHom (fun _ : σ => 1) m - F.adaptedConstantLieHom (fun _ => 1) n ∈ _
  rw [← map_sub]
  exact F.adaptedConstant_mem_shiftedPolynomialIdeal (fun _ => 1) 2 hmn

theorem filteredFirstJet_logDerivative_eq {p q : F.adaptedLieSubalgebra (fun _ : σ => 1)}
    (hpq : F.polynomialSymbolMap (fun _ => 1) p = F.polynomialSymbolMap (fun _ => 1) q) :
    F.filteredFirstJetMap (fun _ => 1) (F.adaptedLogDerivative h p) =
      F.filteredFirstJetMap (fun _ => 1) (F.adaptedLogDerivative h q) := by
  rw [← sub_eq_zero, ← map_sub]
  exact (F.filteredFirstJetMap_eq_zero_iff (fun _ => 1) _).mpr (F.adaptedLogDerivative_sub_mem h hpq)

noncomputable def symbolLogDerivative (x : F.PolynomialSymbol (fun _ : σ => 1)) :
    F.FilteredFirstJet (fun _ : σ => 1) :=
  F.filteredFirstJetMap (fun _ => 1)
    (F.adaptedLogDerivative h (Classical.choose (F.polynomialSymbolMap_surjective (fun _ => 1) x)))

@[simp] theorem symbolLogDerivative_map (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.symbolLogDerivative h (F.polynomialSymbolMap (fun _ => 1) p) =
      F.filteredFirstJetMap (fun _ => 1) (F.adaptedLogDerivative h p) :=
  F.filteredFirstJet_logDerivative_eq h (Classical.choose_spec
    (F.polynomialSymbolMap_surjective (fun _ => 1) (F.polynomialSymbolMap (fun _ => 1) p)))

noncomputable def symbolAdjointConstant (x : F.PolynomialSymbol (fun _ : σ => 1)) (m : L) :
    F.FilteredFirstJet (fun _ : σ => 1) :=
  F.filteredFirstJetMap (fun _ => 1)
    (dualAdjoint (⟨Classical.choose (F.polynomialSymbolMap_surjective (fun _ => 1) x)⟩ :
      (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group) (F.adaptedConstant (fun _ => 1) m))

omit [Fintype σ] in
@[simp] theorem symbolAdjointConstant_map (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) (m : L) :
    F.symbolAdjointConstant (F.polynomialSymbolMap (fun _ => 1) p) m =
      F.filteredFirstJetMap (fun _ => 1)
        (dualAdjoint (⟨p⟩ : (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
          (F.adaptedConstant (fun _ => 1) m)) := by
  change F.filteredFirstJetMap (fun _ => 1) _ = F.filteredFirstJetMap (fun _ => 1) _
  rw [← sub_eq_zero, ← map_sub]
  apply (F.filteredFirstJetMap_eq_zero_iff (fun _ => 1) _).mpr
  exact F.adaptedAdjointConstant_sub_mem (Classical.choose_spec
    (F.polynomialSymbolMap_surjective (fun _ => 1) (F.polynomialSymbolMap (fun _ => 1) p))) (by simp)

theorem normalizedRelativeLog_symbol_formula (e m : L)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.filteredFirstJetMap (fun _ => 1) (F.normalizedRelativeLog h e m p) =
      F.symbolLogDerivative h (F.polynomialSymbolMap (fun _ => 1) p) -
        F.filteredFirstJetMap (fun _ => 1) (F.adaptedConstant (fun _ => 1) e) -
        F.symbolAdjointConstant (F.polynomialSymbolMap (fun _ => 1) p) m := by
  rw [F.symbolLogDerivative_map, F.symbolAdjointConstant_map,
    F.filteredFirstJet_normalizedRelativeLog, map_sub, map_sub]

theorem differentiatedRelativeLog_firstJet_eq
    {p q : F.adaptedLieSubalgebra (fun _ : σ => 1)}
    (hpq : F.polynomialSymbolMap (fun _ => 1) p = F.polynomialSymbolMap (fun _ => 1) q)
    {e e' m m' : L} (he : e - e' ∈ F.layer 2) (hm : m - m' ∈ F.layer 2) :
    F.filteredFirstJetMap (fun _ => 1) (F.differentiatedRelativeLog h e m p) =
      F.filteredFirstJetMap (fun _ => 1) (F.differentiatedRelativeLog h e' m' q) := by
  change F.filteredFirstJetMap (fun _ => 1) (_ - _ - _) =
    F.filteredFirstJetMap (fun _ => 1) (_ - _ - _)
  rw [map_sub, map_sub, map_sub, map_sub, F.filteredFirstJet_logDerivative_eq h hpq,
    F.filteredFirstJet_constant_eq (fun _ => 1) he]
  congr 1
  rw [← sub_eq_zero, ← map_sub]
  exact (F.filteredFirstJetMap_eq_zero_iff (fun _ => 1) _).mpr (F.adaptedAdjointConstant_sub_mem hpq hm)

theorem normalizedRelative_square_symbol_congr
    {p q : F.adaptedLieSubalgebra (fun _ : σ => 1)}
    (hpq : F.polynomialSymbolMap (fun _ => 1) p = F.polynomialSymbolMap (fun _ => 1) q)
    {e e' m m' : L} (he : e - e' ∈ F.layer 2) (hm : m - m' ∈ F.layer 2)
    (hpzero : coefficients (normalizedShiftLog s h (-e) (-m) p.val - p.val) 0 ∈ F.layer 2)
    (hqzero : coefficients (normalizedShiftLog s h (-e') (-m') q.val - q.val) 0 ∈ F.layer 2) :
    F.relativeSquareSymbolMap (fun _ => 1) (by simp)
        ⟨F.normalizedRelativeLog h e m p, F.normalizedRelativeLog_mem h e m p hpzero⟩ =
      F.relativeSquareSymbolMap (fun _ => 1) (by simp)
        ⟨F.normalizedRelativeLog h e' m' q, F.normalizedRelativeLog_mem h e' m' q hqzero⟩ := by
  apply (F.relativeSquareSymbolMap_eq_iff (fun _ => 1) (by simp) _ _).mpr
  exact (F.filteredFirstJet_normalizedRelativeLog h e m p).trans
    ((F.differentiatedRelativeLog_firstJet_eq h hpq he hm).trans
      (F.filteredFirstJet_normalizedRelativeLog h e' m' q).symm)

theorem normalized_square_symbol_congr
    {p q : F.adaptedLieSubalgebra (fun _ : σ => 1)}
    (hpq : F.polynomialSymbolMap (fun _ => 1) p = F.polynomialSymbolMap (fun _ => 1) q)
    {e e' m m' : L} (he : e - e' ∈ F.layer 2) (hm : m - m' ∈ F.layer 2)
    (hpzero : coefficients (normalizedShiftLog s h (-e) (-m) p.val - p.val) 0 ∈ F.layer 2)
    (hqzero : coefficients (normalizedShiftLog s h (-e') (-m') q.val - q.val) 0 ∈ F.layer 2)
    (r r' : F.squareFiltration.adaptedLieSubalgebra (fun _ : σ => 1))
    (hrf : F.squareFstPolynomialMap (fun _ => 1) r = F.normalizedShiftAdapted h (-e) (-m) p)
    (hrs : F.squareSndPolynomialMap (fun _ => 1) r = p)
    (hrf' : F.squareFstPolynomialMap (fun _ => 1) r' = F.normalizedShiftAdapted h (-e') (-m') q)
    (hrs' : F.squareSndPolynomialMap (fun _ => 1) r' = q) :
    F.squareFiltration.polynomialSymbolMap (fun _ => 1) r =
      F.squareFiltration.polynomialSymbolMap (fun _ => 1) r' := by
  rw [F.normalized_square_symbol_factorization h e m p hpzero r hrf hrs,
    F.normalized_square_symbol_factorization h e' m' q hqzero r' hrf' hrs']
  apply congrArg₂ (lieBCH s)
  · apply (F.relativeSquareSymbolMap_eq_iff (fun _ => 1) (by simp) _ _).mpr
    exact F.differentiatedRelativeLog_firstJet_eq h hpq he hm
  · rw [hpq]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)

noncomputable def reducedSquarePolynomialMap :
    F.squareFiltration.adaptedLieSubalgebra w →ₗ⁅ℚ⁆
      F.squareFiltration.quotientTop.adaptedLieSubalgebra w :=
  F.squareFiltration.filteredPolynomialMap F.squareFiltration.quotientTop
    (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1)))
    (fun _ _ hx => F.squareFiltration.quotientLie_mem _ le_rfl hx) w

noncomputable def reducedSquareSymbolMap :
    F.squareFiltration.PolynomialSymbol w →ₗ⁅ℚ⁆ F.squareFiltration.quotientTop.PolynomialSymbol w :=
  F.squareFiltration.filteredPolynomialSymbolMap F.squareFiltration.quotientTop
    (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1)))
    (fun _ _ hx => F.squareFiltration.quotientLie_mem _ le_rfl hx) w

@[simp] theorem reducedSquareSymbolMap_symbol (r : F.squareFiltration.adaptedLieSubalgebra w) :
    F.reducedSquareSymbolMap w (F.squareFiltration.polynomialSymbolMap w r) =
      F.squareFiltration.quotientTop.polynomialSymbolMap w (F.reducedSquarePolynomialMap w r) := rfl

theorem reducedSquareSymbolMap_lieBCH (x y : F.squareFiltration.PolynomialSymbol w) :
    F.reducedSquareSymbolMap w (lieBCH (s + 1) x y) =
      lieBCH s (F.reducedSquareSymbolMap w x) (F.reducedSquareSymbolMap w y) :=
  map_lieBCH_of_nilpotent_steps (F.reducedSquareSymbolMap w)
    (F.squareFiltration.polynomialSymbol_lowerCentralSeries_eq_bot w)
    (F.squareFiltration.quotientTop.polynomialSymbol_lowerCentralSeries_eq_bot w) x y

variable [Fintype σ] (h : σ → ℚ) (e m : L)
  (p : F.adaptedLieSubalgebra (fun _ : σ => 1))

theorem normalized_reduced_square_symbol_factorization
    (hzero : coefficients (normalizedShiftLog (s + 1) h (-e) (-m) p.val - p.val) 0 ∈ F.layer 2)
    (r : F.squareFiltration.adaptedLieSubalgebra (fun _ : σ => 1))
    (hf : F.squareFstPolynomialMap (fun _ => 1) r = F.normalizedShiftAdapted h (-e) (-m) p)
    (hs : F.squareSndPolynomialMap (fun _ => 1) r = p) :
    F.squareFiltration.quotientTop.polynomialSymbolMap (fun _ => 1)
        (F.reducedSquarePolynomialMap (fun _ => 1) r) =
      lieBCH s
        (F.reducedSquareSymbolMap (fun _ => 1)
          (F.relativeSquareSymbolMap (fun _ => 1) (by simp)
            ⟨F.differentiatedRelativeLog h e m p, F.differentiatedRelativeLog_mem h e m p hzero⟩))
        (F.reducedSquareSymbolMap (fun _ => 1)
          (F.squareDiagonalSymbolMap (fun _ => 1) (F.polynomialSymbolMap (fun _ => 1) p))) := by
  have hh := congrArg (F.reducedSquareSymbolMap (fun _ => 1))
    (F.normalized_square_symbol_factorization h e m p hzero r hf hs)
  rw [F.reducedSquareSymbolMap_symbol, F.reducedSquareSymbolMap_lieBCH] at hh
  exact hh

end Erdos3.NilpotentLieFiltration

end

end OAI
