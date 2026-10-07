import OAI.Combinatorics.Progressions.Estimates.NativeRationalRepresentatives

namespace OAI

section

namespace Erdos3

theorem finite_card_real_grid_box {ι : Type*} [Fintype ι]
    (S : Set (ι → ℝ)) (l N : ℕ) (hl : 0 < l) {B : ℝ}
    (hgrid : S ⊆ realDenominatorGrid l)
    (hbound : ∀ x ∈ S, ∀ i, |x i| ≤ B)
    (hN : (l : ℝ) * B ≤ N) :
    S.Finite ∧ S.ncard ≤ (2 * N + 1) ^ Fintype.card ι := by
  classical
  let z : S → ι → ℤ := fun x => Classical.choose (hgrid x.property)
  have hz (x : S) (i : ι) : (z x i : ℝ) = (l : ℝ) * x.val i :=
    congrFun (Classical.choose_spec (hgrid x.property)) i
  have hzi (x : S) (i : ι) : z x i ∈ Set.Icc (-(N : ℤ)) N := by
    have hb : |(z x i : ℝ)| ≤ (N : ℝ) := by
      rw [hz, abs_mul, abs_of_nonneg (Nat.cast_nonneg l)]
      exact (mul_le_mul_of_nonneg_left (hbound x x.property i) (Nat.cast_nonneg l)).trans hN
    apply abs_le.mp
    exact_mod_cast hb
  let f : S → (ι → Set.Icc (-(N : ℤ)) N) := fun x i => ⟨z x i, hzi x i⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    funext i
    have hi : z x i = z y i := congrArg Subtype.val (congrFun hxy i)
    apply mul_left_cancel₀ (show (l : ℝ) ≠ 0 by exact_mod_cast hl.ne')
    rw [← hz, ← hz, hi]
  let : Finite S := Finite.of_injective f hf
  have hcardI : Fintype.card (Set.Icc (-(N : ℤ)) N) = 2 * N + 1 := by
    have h := Int.card_fintype_Icc_of_le (-(N : ℤ)) N (show -(N : ℤ) ≤ N + 1 by omega)
    omega
  refine ⟨Set.toFinite S, ?_⟩
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_fun, hcardI] using hc

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_bounded_native_grid_enumeration
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (m : ℕ) (hm : 0 < m)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ n : ℕ, 0 < n ∧ n ≤ (2 * ⌈(m : ℝ) * B⌉₊ + 1) ^ d ∧
      ∃ rep : Fin n → D.RealGroup,
        (∀ j, (∀ i, |(D.basis.baseChange ℝ).repr (rep j).coord i| ≤ B) ∧
          (D.basis.baseChange ℝ).equivFun (rep j).coord ∈ realDenominatorGrid m) ∧
        ∀ g : D.RealGroup,
          (∀ i, |(D.basis.baseChange ℝ).repr g.coord i| ≤ B) →
          (D.basis.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid m →
          ∃ j, g = rep j := by
  classical
  let A : Set (Fin d → ℝ) :=
    {x | (∀ i, |x i| ≤ B) ∧ x ∈ realDenominatorGrid m}
  obtain ⟨hAfin, hAcard⟩ := finite_card_real_grid_box A m ⌈(m : ℝ) * B⌉₊ hm
    (fun _ hx => hx.2) (fun _ hx => hx.1) (Nat.le_ceil _)
  let S : Set D.RealGroup :=
    {g | (∀ i, |(D.basis.baseChange ℝ).repr g.coord i| ≤ B) ∧
      (D.basis.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid m}
  let f : D.RealGroup → (Fin d → ℝ) :=
    fun g => (D.basis.baseChange ℝ).equivFun g.coord
  have hf : Function.Injective f := by
    intro g h hgh
    apply NilpotentLieBCHGroup.ext
    exact (D.basis.baseChange ℝ).equivFun.injective hgh
  have hmaps : Set.MapsTo f S A := by
    intro g hg
    exact ⟨by simpa only [f, Basis.equivFun_apply] using hg.1, hg.2⟩
  have hSfin : S.Finite := Set.Finite.of_injOn hmaps hf.injOn hAfin
  have hScard : S.ncard ≤ (2 * ⌈(m : ℝ) * B⌉₊ + 1) ^ d := by
    exact (Set.ncard_le_ncard_of_injOn f hmaps hf.injOn hAfin).trans
      (by simpa only [Fintype.card_fin] using hAcard)
  let : Fintype S := hSfin.fintype
  have hone : (1 : D.RealGroup) ∈ S := by
    constructor
    · simpa only [coord_one, map_zero, Finsupp.zero_apply, abs_zero] using
        fun _ : Fin d => hB
    · change (D.basis.baseChange ℝ).equivFun (0 : ℝ ⊗[ℚ] L) ∈ _
      rw [map_zero]
      exact ⟨0, by ext i; simp⟩
  let : Nonempty S := ⟨⟨1, hone⟩⟩
  let e := Fintype.equivFin S
  refine ⟨Fintype.card S, Fintype.card_pos, ?_, fun j => (e.symm j).val,
    fun j => (e.symm j).property, ?_⟩
  · simpa only [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using hScard
  · intro g hbound hgrid
    let x : S := ⟨g, hbound, hgrid⟩
    exact ⟨e x, (congrArg Subtype.val (e.symm_apply_apply x)).symm⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

structure NativeGridRightDictionary
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (inputDenominator : ℕ) (B : ℝ) where
  denominator : ℕ
  count : ℕ
  denominator_pos : 0 < denominator
  count_pos : 0 < count
  denominator_bound : (denominator : ℝ) ≤ B
  count_bound : (count : ℝ) ≤ B
  representative : Fin count → D.RealGroup
  representative_bounds : ∀ j,
    (∀ i, |(D.basis.baseChange ℝ).repr (representative j).coord i| ≤ B) ∧
    (D.basis.baseChange ℝ).equivFun (representative j).coord ∈
      realDenominatorGrid denominator
  cover : ∀ g : D.RealGroup,
    (D.basis.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid inputDenominator →
    ∃ j : Fin count, ∃ γ ∈ D.realLattice, g = representative j * γ

namespace NativeGridRightDictionary

theorem labeling
    {X L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d m : ℕ} {B : ℝ}
    {D : RationalFilteredNilmanifold L s d}
    (dictionary : NativeGridRightDictionary D m B) (rightAt : X → D.RealGroup)
    (hgrid : ∀ x, (D.basis.baseChange ℝ).equivFun (rightAt x).coord ∈
      realDenominatorGrid m) :
    ∃ label : X → Fin dictionary.count, ∀ x,
      (∃ γ ∈ D.realLattice, rightAt x = dictionary.representative (label x) * γ) ∧
      ∀ g : D.RealGroup,
        (QuotientGroup.mk (g * rightAt x) : D.Space) =
          QuotientGroup.mk (g * dictionary.representative (label x)) := by
  classical
  choose label γ hγ heq using fun x => dictionary.cover (rightAt x) (hgrid x)
  refine ⟨label, fun x => ⟨⟨γ x, hγ x, heq x⟩, ?_⟩⟩
  intro g
  rw [heq x, ← mul_assoc]
  exact QuotientGroup.mk_mul_of_mem _ (hγ x)

end NativeGridRightDictionary

theorem exists_native_grid_right_dictionary (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p →
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.exp p →
      Nonempty (NativeGridRightDictionary D m (Real.exp ((p + C) ^ C))) := by
  obtain ⟨a, _, hrep⟩ := exists_native_rational_representatives s
  let P : Polynomial ℕ :=
    (Polynomial.X + (Polynomial.X + Polynomial.C a) ^ a + 7) ^ 7
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p hp hD m hm hmp
  obtain ⟨q, hq, hqp, hreps⟩ := hrep D p hp hD m hm hmp
  let t := p + (p + a) ^ a
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by
    dsimp [t]
    exact le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have hat : (p + a) ^ a ≤ t := by dsimp [t]; linarith
  have htbox : t ≤ (t + 2) ^ 2 := le_power_budget ht (by decide)
  have hboxcount : (t + 2) ^ 2 ≤ (t + 7) ^ 7 :=
    (pow_le_pow_left₀ (by linarith) (by linarith : t + 2 ≤ t + 7) 2).trans
      (pow_le_pow_right₀ (by linarith : 1 ≤ t + 7) (by decide : 2 ≤ 7))
  have hcountC : (t + 7) ^ 7 ≤ (p + C) ^ C := by
    simpa [P, t, Polynomial.eval₂_pow] using hbudget p hp
  have hboxC := hboxcount.trans hcountC
  have haC := hat.trans (htbox.trans hboxC)
  obtain ⟨n, hn, hncount, rep, hrepbounds, hcover⟩ :=
    exists_bounded_native_grid_enumeration D q hq (Real.exp_pos ((t + 2) ^ 2)).le
  have hnexp : (n : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    apply (Nat.cast_le.mpr hncount).trans
    have hcount := grid_box_count_le_exp 2 d q (by decide) ht (hD.1.trans hpt)
      (hqp.trans (Real.exp_le_exp.mpr hat))
    norm_num at hcount
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      using hcount.trans (Real.exp_le_exp.mpr hcountC)
  refine ⟨{
    denominator := q
    count := n
    denominator_pos := hq
    count_pos := hn
    denominator_bound := hqp.trans (Real.exp_le_exp.mpr haC)
    count_bound := hnexp
    representative := rep
    representative_bounds := fun j =>
      ⟨fun i => ((hrepbounds j).1 i).trans (Real.exp_le_exp.mpr hboxC), (hrepbounds j).2⟩
    cover := ?_
  }⟩
  intro g hg
  obtain ⟨r, hr, hrgrid, γ, hγ, heq⟩ := (hreps g hg).1
  obtain ⟨j, hj⟩ := hcover r
    (fun i => (hr i).trans (Real.exp_le_exp.mpr (hat.trans htbox))) hrgrid
  exact ⟨j, γ, hγ, by simpa only [hj] using heq⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
