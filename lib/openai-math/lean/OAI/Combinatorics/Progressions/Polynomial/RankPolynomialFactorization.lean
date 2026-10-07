import OAI.Combinatorics.Progressions.Linear.RankHorizontalSymbol
import OAI.Combinatorics.Progressions.Nilpotent.LinearBCHAbelian

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include hlayers

theorem adaptedBasis_weight_pos (i : ι) : 0 < ω i := by
  by_contra hi
  have hb : b i ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  have hz := (F.mem_layer_iff_basis_coordinates b ω hlayers 1 (b i)).mp hb i (by omega)
  simp at hz

theorem adaptedBasis_weight_le_step (i : ι) : ω i ≤ s := by
  by_contra hi
  have hb : b i ∈ F.layer (s + 1) := by
    rw [hlayers]
    exact Submodule.subset_span ⟨i, (show s + 1 ≤ ω i by omega), rfl⟩
  rw [F.terminal, Submodule.mem_bot] at hb
  exact b.ne_zero i hb

theorem polynomialSymbolBasis_bracket [DecidableEq σ] (w : σ → ℕ) (u v z : SymbolBasisIndex w ω) :
    (F.polynomialSymbolBasis b ω hlayers w).repr
      ⁅F.polynomialSymbolBasis b ω hlayers w u, F.polynomialSymbolBasis b ω hlayers w v⁆ z =
      if u.val.1 + v.val.1 = z.val.1 then b.repr ⁅b u.val.2, b v.val.2⁆ z.val.2 else 0 := by
  classical
  let lift (x : SymbolBasisIndex w ω) : F.adaptedLieSubalgebra w :=
    F.adaptedMonomialBasis b ω hlayers w ⟨x.val, x.property.le⟩
  have hlift (x : SymbolBasisIndex w ω) :
      (lift x : VectorPolynomial σ ℚ L) = monomial x.val.1 (b x.val.2) :=
    F.adaptedMonomialBasis_coe b ω hlayers w _
  have hbracket : (⁅lift u, lift v⁆ : F.adaptedLieSubalgebra w).val =
      monomial (u.val.1 + v.val.1) ⁅b u.val.2, b v.val.2⁆ := by
    change ⁅(lift u : VectorPolynomial σ ℚ L), (lift v : VectorPolynomial σ ℚ L)⁆ = _
    rw [hlift, hlift, lie_monomial]
  rw [F.polynomialSymbolBasis_apply b ω hlayers w u,
    F.polynomialSymbolBasis_apply b ω hlayers w v, ← LieHom.map_lie,
    F.polynomialSymbolBasis_repr_map]
  change b.repr (coefficients ((⁅lift u, lift v⁆ : F.adaptedLieSubalgebra w) :
    VectorPolynomial σ ℚ L) z.val.1) z.val.2 = _
  rw [hbracket, coefficients_monomial]
  by_cases h : u.val.1 + v.val.1 = z.val.1 <;> simp [h]

theorem polynomialSymbolBasis_bracket_height (w : σ → ℕ) {H : ℕ} (hH : 1 ≤ H)
    (hb : ∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H)
    (u v z : SymbolBasisIndex w ω) :
    RationalHeightLE ((F.polynomialSymbolBasis b ω hlayers w).repr
      ⁅F.polynomialSymbolBasis b ω hlayers w u, F.polynomialSymbolBasis b ω hlayers w v⁆ z) H := by
  classical
  rw [F.polynomialSymbolBasis_bracket]
  split_ifs
  · exact hb _ _ _
  · exact rationalHeightLE_zero hH

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped BigOperators

variable {σ ι : Type*} (w : σ → ℕ) (ω : ι → ℕ) (s : ℕ)
  (hw : ∀ i, 0 < w i) (hω : ∀ i, ω i ≤ s)

include hw hω

theorem symbolBasisIndex_degree_le (z : SymbolBasisIndex w ω) :
    z.val.1.sum (fun _ n => n) ≤ s := by
  apply le_trans ?_ (z.property.le.trans (hω z.val.2))
  simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
  exact Finset.sum_le_sum (fun i _ => Nat.le_mul_of_pos_right _ (hw i))

noncomputable def symbolBasisCode (z : SymbolBasisIndex w ω) :
    (Σ n : Fin (s + 1), Fin n.val → σ) × ι :=
  (⟨⟨z.val.1.toMultiset.toList.length, by
      rw [Multiset.length_toList, Finsupp.card_toMultiset]
      exact Nat.lt_succ_of_le (symbolBasisIndex_degree_le w ω s hw hω z)⟩,
    z.val.1.toMultiset.toList.get⟩, z.val.2)

theorem symbolBasisCode_injective : Function.Injective (symbolBasisCode w ω s hw hω) := by
  classical
  intro z u h
  have hi := congrArg (fun t : (Σ n : Fin (s + 1), Fin n.val → σ) × ι => t.2) h
  change z.val.2 = u.val.2 at hi
  have hl := congrArg (fun t : (Σ n : Fin (s + 1), Fin n.val → σ) × ι => List.ofFn t.1.2) h
  change List.ofFn z.val.1.toMultiset.toList.get = List.ofFn u.val.1.toMultiset.toList.get at hl
  rw [List.ofFn_get, List.ofFn_get] at hl
  have hm := congrArg (fun t : List σ => (t : Multiset σ)) hl
  rw [Multiset.coe_toList, Multiset.coe_toList] at hm
  apply Subtype.ext
  apply Prod.ext _ hi
  ext i
  have hh := congrArg (fun t : Multiset σ => t.count i) hm
  simpa only [Finsupp.count_toMultiset] using hh

variable [Fintype σ] [Fintype ι]

theorem symbolBasisIndex_finite : Finite (SymbolBasisIndex w ω) :=
  Finite.of_injective (symbolBasisCode w ω s hw hω) (symbolBasisCode_injective w ω s hw hω)

@[instance_reducible] noncomputable def symbolBasisIndexFintype : Fintype (SymbolBasisIndex w ω) := by
  let : Finite (SymbolBasisIndex w ω) := symbolBasisIndex_finite w ω s hw hω
  exact Fintype.ofFinite _

theorem symbolBasisIndex_card_le [Fintype (SymbolBasisIndex w ω)] :
    Fintype.card (SymbolBasisIndex w ω) ≤ Fintype.card ι * (s + 1) * (Fintype.card σ + 1) ^ s := by
  have hc := Fintype.card_le_of_injective (symbolBasisCode w ω s hw hω)
    (symbolBasisCode_injective w ω s hw hω)
  simp only [Fintype.card_prod, Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin] at hc
  apply hc.trans
  calc
    (∑ n : Fin (s + 1), Fintype.card σ ^ n.val) * Fintype.card ι ≤
        (∑ _ : Fin (s + 1), (Fintype.card σ + 1) ^ s) * Fintype.card ι := by
      apply Nat.mul_le_mul_right
      apply Finset.sum_le_sum
      intro n _
      exact (Nat.pow_le_pow_left (Nat.le_succ _) _).trans
        (Nat.pow_le_pow_right (by omega) (Nat.le_of_lt_succ n.isLt))
    _ = _ := by simp; ring

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include hlayers

omit hω in
theorem polynomialSymbol_finiteDimensional : FiniteDimensional ℚ (F.PolynomialSymbol w) := by
  let : Fintype (SymbolBasisIndex w ω) := symbolBasisIndexFintype w ω s hw
    (F.adaptedBasis_weight_le_step b ω hlayers)
  exact (F.polynomialSymbolBasis b ω hlayers w).finiteDimensional_of_finite

omit hω in
theorem polynomialSymbol_finrank_le :
    finrank ℚ (F.PolynomialSymbol w) ≤ Fintype.card ι * (s + 1) * (Fintype.card σ + 1) ^ s := by
  let : Fintype (SymbolBasisIndex w ω) := symbolBasisIndexFintype w ω s hw
    (F.adaptedBasis_weight_le_step b ω hlayers)
  rw [finrank_eq_card_basis (F.polynomialSymbolBasis b ω hlayers w)]
  exact symbolBasisIndex_card_le w ω s hw (F.adaptedBasis_weight_le_step b ω hlayers)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def polynomialSymbolFiltration (w : σ → ℕ) :
    NilpotentLieFiltration (F.PolynomialSymbol w) s :=
  (F.adaptedPolynomialFiltration w).quotientLie (F.shiftedAdaptedIdeal w) (by
    rw [(F.adaptedPolynomialFiltration w).terminal]
    exact bot_le)

theorem polynomialSymbolFiltration_layer (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (j : ℕ) :
    (F.polynomialSymbolFiltration w).layer j =
      Submodule.span ℚ (F.polynomialSymbolBasis b ω hlayers w ''
        {z : SymbolBasisIndex w ω | j ≤ ω z.val.2}) := by
  apply le_antisymm
  · rintro x ⟨p, hp, rfl⟩
    rw [basis_mem_span_image_iff]
    intro z hz
    change (F.polynomialSymbolBasis b ω hlayers w).repr (F.polynomialSymbolMap w p) z = 0
    rw [F.polynomialSymbolBasis_repr_map]
    exact (F.mem_layer_iff_basis_coordinates b ω hlayers j _).mp (hp z.val.1) z.val.2 hz
  · apply Submodule.span_le.mpr
    rintro _ ⟨z, hz, rfl⟩
    let p := F.adaptedMonomialBasis b ω hlayers w ⟨z.val, z.property.le⟩
    refine ⟨p, ?_, ?_⟩
    · change (p : VectorPolynomial σ ℚ L) ∈ F.polynomialLayer j
      change (F.adaptedMonomialBasis b ω hlayers w ⟨z.val, z.property.le⟩ :
        VectorPolynomial σ ℚ L) ∈ F.polynomialLayer j
      rw [F.adaptedMonomialBasis_coe]
      apply F.monomial_mem_polynomialLayer
      rw [hlayers]
      exact Submodule.subset_span ⟨z.val.2, hz, rfl⟩
    · exact (F.polynomialSymbolBasis_apply b ω hlayers w z).symm

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

abbrev AdaptedBasisIndex {σ ι : Type*} (w : σ → ℕ) (ω : ι → ℕ) :=
  {z : (σ →₀ ℕ) × ι // Finsupp.weight w z.1 ≤ ω z.2}

section Structure

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem adaptedMonomialBasis_bracket [DecidableEq σ] (u v z : AdaptedBasisIndex w ω) :
    (F.adaptedMonomialBasis b ω hlayers w).repr
      ⁅F.adaptedMonomialBasis b ω hlayers w u, F.adaptedMonomialBasis b ω hlayers w v⁆ z =
      if u.val.1 + v.val.1 = z.val.1 then b.repr ⁅b u.val.2, b v.val.2⁆ z.val.2 else 0 := by
  classical
  rw [F.adaptedMonomialBasis_repr]
  change b.repr (coefficients
    ⁅(F.adaptedMonomialBasis b ω hlayers w u : VectorPolynomial σ ℚ L),
      (F.adaptedMonomialBasis b ω hlayers w v : VectorPolynomial σ ℚ L)⁆ z.val.1) z.val.2 = _
  rw [F.adaptedMonomialBasis_coe, F.adaptedMonomialBasis_coe, lie_monomial, coefficients_monomial]
  by_cases h : u.val.1 + v.val.1 = z.val.1
  · simp only [h, Finsupp.single_eq_same, ite_true]
  · simp only [Finsupp.single_eq_of_ne (Ne.symm h), map_zero, Finsupp.zero_apply, h, ite_false]

theorem adaptedMonomialBasis_bracket_height {H : ℕ} (hH : 1 ≤ H)
    (hb : ∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) :
    ∀ i j k, RationalHeightLE ((F.adaptedMonomialBasis b ω hlayers w).repr
      ⁅F.adaptedMonomialBasis b ω hlayers w i, F.adaptedMonomialBasis b ω hlayers w j⁆ k) H := by
  classical
  intro i j k
  rw [F.adaptedMonomialBasis_bracket]
  split_ifs
  · exact hb _ _ _
  · exact rationalHeightLE_zero hH

end Structure

section Dimension

variable {σ ι : Type*} (w : σ → ℕ) (ω : ι → ℕ) (s : ℕ)
  (hw : ∀ i, 0 < w i) (hω : ∀ i, ω i ≤ s)

include hw hω

theorem adaptedBasisIndex_degree_le (z : AdaptedBasisIndex w ω) :
    z.val.1.sum (fun _ n => n) ≤ s := by
  apply le_trans ?_ (z.property.trans (hω z.val.2))
  simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
  exact Finset.sum_le_sum (fun i _ => Nat.le_mul_of_pos_right _ (hw i))

noncomputable def adaptedBasisCode (z : AdaptedBasisIndex w ω) :
    (Σ n : Fin (s + 1), Fin n.val → σ) × ι :=
  (⟨⟨z.val.1.toMultiset.toList.length, by
      rw [Multiset.length_toList, Finsupp.card_toMultiset]
      exact Nat.lt_succ_of_le (adaptedBasisIndex_degree_le w ω s hw hω z)⟩,
    z.val.1.toMultiset.toList.get⟩, z.val.2)

theorem adaptedBasisCode_injective : Function.Injective (adaptedBasisCode w ω s hw hω) := by
  classical
  intro z u h
  have hi := congrArg (fun t : (Σ n : Fin (s + 1), Fin n.val → σ) × ι => t.2) h
  change z.val.2 = u.val.2 at hi
  have hl := congrArg (fun t : (Σ n : Fin (s + 1), Fin n.val → σ) × ι => List.ofFn t.1.2) h
  change List.ofFn z.val.1.toMultiset.toList.get = List.ofFn u.val.1.toMultiset.toList.get at hl
  rw [List.ofFn_get, List.ofFn_get] at hl
  have hm := congrArg (fun t : List σ => (t : Multiset σ)) hl
  rw [Multiset.coe_toList, Multiset.coe_toList] at hm
  apply Subtype.ext
  apply Prod.ext _ hi
  ext i
  have hh := congrArg (fun t : Multiset σ => t.count i) hm
  simpa only [Finsupp.count_toMultiset] using hh

variable [Fintype σ] [Fintype ι]

theorem adaptedBasisIndex_finite : Finite (AdaptedBasisIndex w ω) :=
  Finite.of_injective (adaptedBasisCode w ω s hw hω) (adaptedBasisCode_injective w ω s hw hω)

@[instance_reducible] noncomputable def adaptedBasisIndexFintype : Fintype (AdaptedBasisIndex w ω) := by
  let : Finite (AdaptedBasisIndex w ω) := adaptedBasisIndex_finite w ω s hw hω
  exact Fintype.ofFinite _

theorem adaptedBasisIndex_card_le [Fintype (AdaptedBasisIndex w ω)] :
    Fintype.card (AdaptedBasisIndex w ω) ≤ Fintype.card ι * (s + 1) * (Fintype.card σ + 1) ^ s := by
  have hc := Fintype.card_le_of_injective (adaptedBasisCode w ω s hw hω)
    (adaptedBasisCode_injective w ω s hw hω)
  simp only [Fintype.card_prod, Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin] at hc
  apply hc.trans
  calc
    (∑ n : Fin (s + 1), Fintype.card σ ^ n.val) * Fintype.card ι ≤
        (∑ _ : Fin (s + 1), (Fintype.card σ + 1) ^ s) * Fintype.card ι := by
      apply Nat.mul_le_mul_right
      apply Finset.sum_le_sum
      intro n _
      exact (Nat.pow_le_pow_left (Nat.le_succ _) _).trans
        (Nat.pow_le_pow_right (by omega) (Nat.le_of_lt_succ n.isLt))
    _ = _ := by simp; ring

end Dimension
end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem symbol_dimension_bound_le_power (s d m : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hm : (m : ℝ) ≤ p) :
    ((d * (s + 1) * (m + 1) ^ s : ℕ) : ℝ) ≤ (p + (s + 2)) ^ (s + 2) := by
  push_cast
  have ht : 0 ≤ p + ((s : ℝ) + 2) := by positivity
  calc
    (d : ℝ) * ((s : ℝ) + 1) * ((m : ℝ) + 1) ^ s ≤
        (p + ((s : ℝ) + 2)) * (p + ((s : ℝ) + 2)) * (p + ((s : ℝ) + 2)) ^ s := by
      apply mul_le_mul _ (pow_le_pow_left₀ (by positivity) (by linarith) s) (by positivity)
        (mul_nonneg ht ht)
      exact mul_le_mul (by linarith) (by linarith) (by positivity) ht
    _ = (p + ((s : ℝ) + 2)) ^ (s + 2) := by ring

theorem exists_symbol_bch_coordinate_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      ∃ P : SymbolBasisIndex w ω → MvPolynomial (Fin 2 × SymbolBasisIndex w ω) ℚ,
        (∀ (a b' : F.PolynomialSymbol w) k,
          MvPolynomial.aeval (fun xi : Fin 2 × SymbolBasisIndex w ω =>
            (F.polynomialSymbolBasis b ω hlayers w).repr (![a, b'] xi.1) xi.2) (P k) =
              (F.polynomialSymbolBasis b ω hlayers w).repr (lieBCH s a b') k) ∧
        (∀ k, (P k).totalDegree ≤ s) ∧
        ∀ k α, (((P k).coeff α).num.natAbs : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          (((P k).coeff α).den : ℝ) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨c, _, hc⟩ := exists_bchCoordinateHeight_exp_budget s
  let R : Polynomial ℕ := ((Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2) + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget R
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hlayers w hw H p hH hp hι hσ hHp hb
  let : Fintype (SymbolBasisIndex w ω) :=
    symbolBasisIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hlayers)
  let B := F.polynomialSymbolBasis b ω hlayers w
  let q : ℝ := (p + (s + 2)) ^ (s + 2)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    apply (show p ≤ p + (s + 2 : ℝ) from le_add_of_nonneg_right (by positivity)).trans
    simpa only [pow_one] using pow_le_pow_right₀
      (show (1 : ℝ) ≤ p + (s + 2) by have := Nat.cast_nonneg (α := ℝ) s; linarith)
      (show 1 ≤ s + 2 by omega)
  have hdim : (Fintype.card (SymbolBasisIndex w ω) : ℝ) ≤ q := by
    exact (Nat.cast_le.mpr (symbolBasisIndex_card_le w ω s hw
      (F.adaptedBasis_weight_le_step b ω hlayers))).trans
      (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)
  have hstruct : ∀ i j k, RationalHeightLE (lieStructureConstants B i j k) H :=
    F.polynomialSymbolBasis_bracket_height b ω hlayers w hH hb
  have hcost := hc (Fintype.card (SymbolBasisIndex w ω)) H q hq hdim
    (hHp.trans (Real.exp_le_exp.mpr hpq))
  have hpoly : (q + c) ^ c ≤ (p + C) ^ C := by
    simpa [R, q, Polynomial.eval₂_pow] using hbound p hp
  have hheight := hcost.trans (Real.exp_le_exp.mpr hpoly)
  refine ⟨bchCoordinatePolynomial (lieStructureConstants B) s,
    bchCoordinatePolynomial_eval B s, bchCoordinatePolynomial_totalDegree _ s, ?_⟩
  intro k α
  have h := bchCoordinatePolynomial_height (lieStructureConstants B) hstruct s k α
  exact ⟨(Nat.cast_le.mpr h.1).trans hheight, (Nat.cast_le.mpr h.2).trans hheight⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def polynomialOrbitCoordinates (w : σ → ℕ) :
    F.PolynomialOrbit w ≃* (F.adaptedPolynomialFiltration w).Group where
  toFun g := ⟨⟨g.log, g.property⟩⟩
  invFun g := ⟨⟨g.coord.val⟩, g.coord.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' g h := by
    apply NilpotentLieBCHGroup.ext
    apply Subtype.ext
    exact (map_lieBCH (F.adaptedLieSubalgebra w).incl s
      (⟨g.log, g.property⟩ : F.adaptedLieSubalgebra w)
      (⟨h.log, h.property⟩ : F.adaptedLieSubalgebra w)).symm

@[simp] theorem polynomialOrbitCoordinates_log (w : σ → ℕ) (g : F.PolynomialOrbit w) :
    ((F.polynomialOrbitCoordinates w g).coord : VectorPolynomial σ ℚ L) = g.log := rfl

@[simp] theorem polynomialOrbitCoordinates_symm_log (w : σ → ℕ)
    (g : (F.adaptedPolynomialFiltration w).Group) :
    (F.polynomialOrbitCoordinates w |>.symm g).log = g.coord.val := rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

noncomputable def rankCoefficientOrbitHom (hs : 1 ≤ s) (w : σ → ℕ) (α : σ →₀ ℕ) :
    F.associatedDegree.PolynomialOrbit w →* Multiplicative (F.HigherHorizontal (Finsupp.weight w α)) where
  toFun g := Multiplicative.ofAdd (F.higherHorizontalCoefficient w α
    (F.associatedDegree.polynomialOrbitCoordinates w g).coord)
  map_one' := by
    change Multiplicative.ofAdd (F.higherHorizontalCoefficient w α 0) = 1
    rw [map_zero]
    rfl
  map_mul' g h := by
    change Multiplicative.ofAdd (F.higherHorizontalCoefficient w α
      (F.associatedDegree.polynomialOrbitCoordinates w (g * h)).coord) =
      Multiplicative.ofAdd (F.higherHorizontalCoefficient w α
        (F.associatedDegree.polynomialOrbitCoordinates w g).coord +
        F.higherHorizontalCoefficient w α (F.associatedDegree.polynomialOrbitCoordinates w h).coord)
    rw [map_mul]
    exact congrArg Multiplicative.ofAdd (linearMap_lieBCH_eq_add
      (F.higherHorizontalCoefficient w α) (F.higherHorizontalCoefficient_lie w α) hs _ _)

theorem rankCoefficientOrbitHom_eq_iff (hs : 1 ≤ s) (w : σ → ℕ) (α : σ →₀ ℕ)
    (g h : F.associatedDegree.PolynomialOrbit w) :
    F.rankCoefficientOrbitHom hs w α g = F.rankCoefficientOrbitHom hs w α h ↔
      coefficients g.log α - coefficients h.log α ∈ F.layer (Finsupp.weight w α) 2 :=
  F.higherHorizontalMk_eq _ _ _

theorem rankCoefficientOrbitHom_eq_one_iff (hs : 1 ≤ s) (w : σ → ℕ) (α : σ →₀ ℕ)
    (g : F.associatedDegree.PolynomialOrbit w) :
    F.rankCoefficientOrbitHom hs w α g = 1 ↔
      coefficients g.log α ∈ F.layer (Finsupp.weight w α) 2 := by
  have h := F.rankCoefficientOrbitHom_eq_iff hs w α g 1
  simpa only [map_one, show (1 : F.associatedDegree.PolynomialOrbit w).log = 0 from rfl,
    map_zero, Finsupp.zero_apply, sub_zero] using h

theorem polynomialOrbit_mul_coefficient_sub_mem_rank_two
    (hs : 1 ≤ s) (w : σ → ℕ) (α : σ →₀ ℕ)
    (g h : F.associatedDegree.PolynomialOrbit w) :
    coefficients (g * h).log α - (coefficients g.log α + coefficients h.log α) ∈
      F.layer (Finsupp.weight w α) 2 := by
  let q := F.associatedDegree.polynomialOrbitCoordinates w
  have hmap := congrArg Multiplicative.toAdd (map_mul (F.rankCoefficientOrbitHom hs w α) g h)
  change F.higherHorizontalMk (Finsupp.weight w α) (F.rankLayerCoefficient w α (q (g * h)).coord) =
    F.higherHorizontalMk (Finsupp.weight w α) (F.rankLayerCoefficient w α (q g).coord) +
      F.higherHorizontalMk (Finsupp.weight w α) (F.rankLayerCoefficient w α (q h).coord) at hmap
  rw [← map_add] at hmap
  exact (F.higherHorizontalMk_eq _ _ _).mp hmap

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open VectorPolynomial

theorem exists_polynomialOrbit_factorization_rank_two
    {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
    (F : DegreeRankLieFiltration L s r) (hs : 1 ≤ s) (w : σ → ℕ)
    (α : ι → σ →₀ ℕ) (g E A U Q : F.associatedDegree.PolynomialOrbit w)
    (hg : F.associatedDegree.polynomialOrbitEval w 0 g = 1)
    (hE : F.associatedDegree.polynomialOrbitEval w 0 E = 1)
    (hA : F.associatedDegree.polynomialOrbitEval w 0 A = 1)
    (hU : F.associatedDegree.polynomialOrbitEval w 0 U = 1)
    (hQ : F.associatedDegree.polynomialOrbitEval w 0 Q = 1)
    (hcoeff : ∀ i, coefficients g.log (α i) -
      (coefficients E.log (α i) + coefficients A.log (α i) +
        coefficients U.log (α i) + coefficients Q.log (α i)) ∈
          F.layer (Finsupp.weight w (α i)) 2) :
    ∃ K : F.associatedDegree.PolynomialOrbit w,
      F.associatedDegree.polynomialOrbitEval w 0 K = 1 ∧ E * A * K * U * Q = g ∧
      ∀ i, coefficients K.log (α i) ∈ F.layer (Finsupp.weight w (α i)) 2 := by
  let K := A⁻¹ * E⁻¹ * g * Q⁻¹ * U⁻¹
  have hhom (i : ι) :
      F.rankCoefficientOrbitHom hs w (α i) g =
        F.rankCoefficientOrbitHom hs w (α i) E * F.rankCoefficientOrbitHom hs w (α i) A *
          F.rankCoefficientOrbitHom hs w (α i) U * F.rankCoefficientOrbitHom hs w (α i) Q := by
    let z (v : F.associatedDegree.PolynomialOrbit w) :=
      F.rankLayerCoefficient w (α i) (F.associatedDegree.polynomialOrbitCoordinates w v).coord
    change F.higherHorizontalMk _ (z g) =
      F.higherHorizontalMk _ (z E) + F.higherHorizontalMk _ (z A) +
        F.higherHorizontalMk _ (z U) + F.higherHorizontalMk _ (z Q)
    rw [← map_add, ← map_add, ← map_add]
    exact (F.higherHorizontalMk_eq _ _ _).mpr (hcoeff i)
  refine ⟨K, ?_, ?_, ?_⟩
  · simp only [K, map_mul, map_inv, hg, hE, hA, hU, hQ, inv_one, one_mul]
  · dsimp only [K]
    group
  · intro i
    apply (F.rankCoefficientOrbitHom_eq_one_iff hs w (α i) K).mp
    simp only [K, map_mul, map_inv]
    rw [hhom i]
    group

end Erdos3.DegreeRankLieFiltration

end

end OAI
