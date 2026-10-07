import OAI.Combinatorics.Progressions.Nilpotent.RationalBCHProducts

namespace OAI

section

namespace Erdos3

theorem finite_card_real_grid_box {ι : Type*} [Fintype ι]
    (S : Set (ι → ℝ)) (m N : ℕ) (hm : 0 < m) {B : ℝ}
    (hgrid : S ⊆ realDenominatorGrid m)
    (hbound : ∀ x ∈ S, ∀ i, |x i| ≤ B)
    (hN : (m : ℝ) * B ≤ N) :
    S.Finite ∧ S.ncard ≤ (2 * N + 1) ^ Fintype.card ι := by
  classical
  let z : S → ι → ℤ := fun x => Classical.choose (hgrid x.property)
  have hz (x : S) (i : ι) : (m : ℝ) * x.val i = (z x i : ℝ) :=
    (congrFun (Classical.choose_spec (hgrid x.property)) i).symm
  have hzi (x : S) (i : ι) : z x i ∈ Set.Icc (-(N : ℤ)) N := by
    have hb : |(z x i : ℝ)| ≤ (N : ℝ) := by
      rw [← hz x i, abs_mul, abs_of_nonneg (Nat.cast_nonneg m)]
      exact (mul_le_mul_of_nonneg_left (hbound x x.property i) (Nat.cast_nonneg m)).trans hN
    apply abs_le.mp
    exact_mod_cast hb
  let f : S → (ι → Set.Icc (-(N : ℤ)) N) := fun x i => ⟨z x i, hzi x i⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    funext i
    have hi : z x i = z y i := congrArg Subtype.val (congrFun hxy i)
    apply mul_left_cancel₀ (show (m : ℝ) ≠ 0 by exact_mod_cast hm.ne')
    rw [hz, hz, hi]
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

namespace Erdos3

private theorem real_grid_shifted_integer_bound {m N : ℕ} {B x c : ℝ} {z : ℤ}
    (hz : (m : ℝ) * x = z) (hxc : |x - c| ≤ B) (hN : (m : ℝ) * B ≤ N) :
    |((z - ⌊(m : ℝ) * c⌋ : ℤ) : ℝ)| ≤ (N : ℝ) + 1 := by
  have hfloor : |(m : ℝ) * c - (⌊(m : ℝ) * c⌋ : ℤ)| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (Int.floor_le _))]
    linarith [Int.lt_floor_add_one ((m : ℝ) * c)]
  calc
    _ = |(m : ℝ) * (x - c) + ((m : ℝ) * c - (⌊(m : ℝ) * c⌋ : ℤ))| := by
      push_cast
      rw [← hz]
      congr 1
      ring
    _ ≤ |(m : ℝ) * (x - c)| + |(m : ℝ) * c - (⌊(m : ℝ) * c⌋ : ℤ)| := abs_add_le _ _
    _ ≤ (m : ℝ) * B + 1 := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg m)]
      exact add_le_add (mul_le_mul_of_nonneg_left hxc (Nat.cast_nonneg m)) hfloor
    _ ≤ _ := by linarith

theorem finite_card_real_grid_window {ι : Type*} [Fintype ι]
    (S : Set (ι → ℝ)) (m N : ℕ) (hm : 0 < m) (center : ι → ℝ) {B : ℝ}
    (hgrid : S ⊆ realDenominatorGrid m)
    (hwindow : ∀ x ∈ S, ∀ i, |x i - center i| ≤ B)
    (hN : (m : ℝ) * B ≤ N) :
    S.Finite ∧ S.ncard ≤ (2 * N + 3) ^ Fintype.card ι := by
  classical
  let z : S → ι → ℤ := fun x => Classical.choose (hgrid x.property)
  have hz (x : S) (i : ι) : (m : ℝ) * x.val i = (z x i : ℝ) :=
    (congrFun (Classical.choose_spec (hgrid x.property)) i).symm
  let shift : ι → ℤ := fun i => ⌊(m : ℝ) * center i⌋
  have hzi (x : S) (i : ι) :
      z x i - shift i ∈ Set.Icc (-((N : ℤ) + 1)) ((N : ℤ) + 1) := by
    have hb := real_grid_shifted_integer_bound (hz x i) (hwindow x x.property i) hN
    apply abs_le.mp
    exact_mod_cast hb
  let f : S → (ι → Set.Icc (-((N : ℤ) + 1)) ((N : ℤ) + 1)) :=
    fun x i => ⟨z x i - shift i, hzi x i⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    funext i
    have hi : z x i - shift i = z y i - shift i := congrArg Subtype.val (congrFun hxy i)
    have hi' : z x i = z y i := by omega
    apply mul_left_cancel₀ (show (m : ℝ) ≠ 0 by exact_mod_cast hm.ne')
    rw [hz, hz, hi']
  let : Finite S := Finite.of_injective f hf
  have hcardI : Fintype.card (Set.Icc (-((N : ℤ) + 1)) ((N : ℤ) + 1)) = 2 * N + 3 := by
    have h := Int.card_fintype_Icc_of_le (-((N : ℤ) + 1)) ((N : ℤ) + 1)
      (show -((N : ℤ) + 1) ≤ (N : ℤ) + 1 + 1 by omega)
    omega
  refine ⟨Set.toFinite S, ?_⟩
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_fun, hcardI] using hc

theorem exists_real_grid_window_enumeration {ι : Type*} [Fintype ι]
    (m : ℕ) (hm : 0 < m) (center : ι → ℝ) (B : ℝ) :
    ∃ n : ℕ, n ≤ (2 * ⌈(m : ℝ) * B⌉₊ + 3) ^ Fintype.card ι ∧
      ∃ candidate : Fin n → ι → ℝ,
        (∀ j, candidate j ∈ realDenominatorGrid m ∧ ∀ i, |candidate j i - center i| ≤ B) ∧
        ∀ x : ι → ℝ, x ∈ realDenominatorGrid m →
          (∀ i, |x i - center i| ≤ B) → ∃ j, candidate j = x := by
  classical
  let S : Set (ι → ℝ) := {x | x ∈ realDenominatorGrid m ∧ ∀ i, |x i - center i| ≤ B}
  obtain ⟨hSfin, hScard⟩ := finite_card_real_grid_window S m ⌈(m : ℝ) * B⌉₊ hm center
    (fun _ hx => hx.1) (fun _ hx => hx.2) (Nat.le_ceil _)
  let : Fintype S := hSfin.fintype
  let e := Fintype.equivFin S
  refine ⟨Fintype.card S, ?_, fun j => (e.symm j).val, fun j => (e.symm j).property, ?_⟩
  · simpa only [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using hScard
  · intro x hx hxbound
    let v : S := ⟨x, hx, hxbound⟩
    exact ⟨e v, congrArg Subtype.val (e.symm_apply_apply v)⟩

end Erdos3

end

section

namespace Erdos3

theorem exists_scalar_rational_grid_window (q : ℕ) (hq : 0 < q) (c B : ℝ) :
    ∃ S : Finset ℚ, S.card ≤ 2 * ⌈(q : ℝ) * B⌉₊ + 3 ∧
      ∀ r : ℚ, r ∈ S ↔
        (∃ z : ℤ, (r : ℝ) = (z : ℝ) / q) ∧ |(r : ℝ) - c| ≤ B := by
  classical
  let S : Set ℚ := {r | (∃ z : ℤ, (r : ℝ) = (z : ℝ) / q) ∧ |(r : ℝ) - c| ≤ B}
  let f : ℚ → Unit → ℝ := fun r _ => r
  let V : Set (Unit → ℝ) := f '' S
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hgrid : V ⊆ realDenominatorGrid q := by
    rintro v ⟨r, ⟨⟨z, hz⟩, _⟩, rfl⟩
    refine ⟨fun _ => z, ?_⟩
    funext i
    change (z : ℝ) = (q : ℝ) * (r : ℝ)
    rw [hz]
    field_simp
  have hwindow : ∀ v ∈ V, ∀ i, |v i - c| ≤ B := by
    rintro v ⟨r, hr, rfl⟩ i
    exact hr.2
  obtain ⟨hVfin, hVcard⟩ := finite_card_real_grid_window V q ⌈(q : ℝ) * B⌉₊ hq
    (fun _ => c) hgrid hwindow (Nat.le_ceil _)
  have hinj : Function.Injective f := by
    intro r t h
    have hr : (r : ℝ) = (t : ℝ) := congrFun h ()
    exact_mod_cast hr
  have hmaps : Set.MapsTo f S V := fun r hr => ⟨r, hr, rfl⟩
  have hSfin : S.Finite := Set.Finite.of_injOn hmaps hinj.injOn hVfin
  have hcard : S.ncard ≤ 2 * ⌈(q : ℝ) * B⌉₊ + 3 := by
    have h := (Set.ncard_le_ncard_of_injOn f hmaps hinj.injOn hVfin).trans hVcard
    simpa only [Fintype.card_unit, pow_one] using h
  refine ⟨hSfin.toFinset, ?_, ?_⟩
  · simpa only [Set.ncard_eq_toFinset_card S hSfin] using hcard
  · intro r
    exact hSfin.mem_toFinset

end Erdos3

end

section

namespace Erdos3

theorem real_grid_window_count_le_exp (d m : ℕ) {B p : ℝ}
    (hp : 0 ≤ p) (hB0 : 0 ≤ B) (hd : (d : ℝ) ≤ p)
    (hm : (m : ℝ) ≤ Real.exp p) (hB : B ≤ Real.exp p) :
    (((2 * ⌈(m : ℝ) * B⌉₊ + 3) ^ d : ℕ) : ℝ) ≤ Real.exp ((p + 3) ^ 3) := by
  have hprod : (m : ℝ) * B ≤ Real.exp (2 * p) := by
    simpa only [two_mul, Real.exp_add] using
      mul_le_mul hm hB hB0 (Real.exp_nonneg p)
  have hceil := (Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg m) hB0)).le
  have hone : 1 ≤ Real.exp (2 * p) := Real.one_le_exp (by linarith)
  have hseven : (7 : ℝ) ≤ Real.exp 6 := by linarith [Real.add_one_le_exp (6 : ℝ)]
  have hbase : ((2 * ⌈(m : ℝ) * B⌉₊ + 3 : ℕ) : ℝ) ≤ Real.exp (2 * p + 6) := by
    rw [Real.exp_add]
    push_cast
    have h := mul_le_mul_of_nonneg_left hseven (Real.exp_nonneg (2 * p))
    nlinarith
  rw [Nat.cast_pow]
  calc
    _ ≤ (Real.exp (2 * p + 6)) ^ d := pow_le_pow_left₀ (Nat.cast_nonneg _) hbase _
    _ = Real.exp ((d : ℝ) * (2 * p + 6)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (p * (2 * p + 6)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hd (by positivity))
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hp (sq_nonneg p)]

theorem exists_real_grid_window_enumeration_exp {ι : Type*} [Fintype ι]
    (m : ℕ) (hm : 0 < m) (center : ι → ℝ) {B p : ℝ}
    (hp : 0 ≤ p) (hB0 : 0 ≤ B) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hmp : (m : ℝ) ≤ Real.exp p) (hB : B ≤ Real.exp p) :
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp ((p + 3) ^ 3) ∧
      ∃ candidate : Fin n → ι → ℝ,
        (∀ j, candidate j ∈ realDenominatorGrid m ∧ ∀ i, |candidate j i - center i| ≤ B) ∧
        ∀ x : ι → ℝ, x ∈ realDenominatorGrid m →
          (∀ i, |x i - center i| ≤ B) → ∃ j, candidate j = x := by
  obtain ⟨n, hn, candidate, hmem, hcover⟩ := exists_real_grid_window_enumeration m hm center B
  exact ⟨n, (Nat.cast_le.mpr hn).trans
    (real_grid_window_count_le_exp (Fintype.card ι) m hp hB0 hd hmp hB), candidate, hmem, hcover⟩

theorem exists_uniform_real_grid_window_enumeration (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type*} [Fintype ι] (m : ℕ), 0 < m →
      ∀ (center : ι → ℝ) (B p : ℝ), 0 ≤ p → 0 ≤ B → (Fintype.card ι : ℝ) ≤ p →
      (m : ℝ) ≤ Real.exp ((p + a) ^ a) → B ≤ Real.exp ((p + a) ^ a) →
      ∃ n : ℕ, (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ candidate : Fin n → ι → ℝ,
          (∀ j, candidate j ∈ realDenominatorGrid m ∧ ∀ i, |candidate j i - center i| ≤ B) ∧
          ∀ x : ι → ℝ, x ∈ realDenominatorGrid m →
            (∀ i, |x i - center i| ≤ B) → ∃ j, candidate j = x := by
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + (Polynomial.X + Polynomial.C a) ^ a + 3) ^ 3)
  refine ⟨C, hC, ?_⟩
  intro ι _ m hm center B p hp hB0 hd hmcap hBcap
  let q := p + (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := le_add_of_nonneg_right (by positivity)
  have haq : (p + a) ^ a ≤ q := le_add_of_nonneg_left hp
  obtain ⟨n, hn, candidate, hmem, hcover⟩ := exists_real_grid_window_enumeration_exp m hm center
    hq hB0 (hd.trans hpq) (hmcap.trans (Real.exp_le_exp.mpr haq))
    (hBcap.trans (Real.exp_le_exp.mpr haq))
  refine ⟨n, hn.trans (Real.exp_le_exp.mpr ?_), candidate, hmem, hcover⟩
  simpa [q, Polynomial.eval₂_pow] using hbudget p hp

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup
open Module

variable {ι L G : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  [LieAlgebra ℝ L] [Group G]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem exists_bounded_kernel_grid_enumeration [IsScalarTower ℚ ℝ L] (b : Basis ι ℝ L)
    (π : NilpotentLieBCHGroup L s hnil →* G) (m N : ℕ) (hm : 0 < m)
    {B : ℝ} (hB : 0 ≤ B) (hN : (m : ℝ) * B ≤ N) :
    ∃ n : ℕ, 0 < n ∧ n ≤ (2 * N + 1) ^ Fintype.card ι ∧
      ∃ center : Fin n → NilpotentLieBCHGroup L s hnil,
        (∀ j, π (center j) = 1 ∧ (∀ i, |b.repr (center j).coord i| ≤ B) ∧
          b.equivFun (center j).coord ∈ realDenominatorGrid m) ∧
        ∀ g : NilpotentLieBCHGroup L s hnil, π g = 1 →
          (∀ i, |b.repr g.coord i| ≤ B) →
          b.equivFun g.coord ∈ realDenominatorGrid m → ∃ j, center j = g := by
  classical
  let A : Set (ι → ℝ) := {x | x ∈ realDenominatorGrid m ∧ ∀ i, |x i| ≤ B}
  obtain ⟨hAfin, hAcard⟩ := finite_card_real_grid_box A m N hm
    (fun _ hx => hx.1) (fun _ hx => hx.2) hN
  let S : Set (NilpotentLieBCHGroup L s hnil) :=
    {g | π g = 1 ∧ (∀ i, |b.repr g.coord i| ≤ B) ∧
      b.equivFun g.coord ∈ realDenominatorGrid m}
  let f : NilpotentLieBCHGroup L s hnil → (ι → ℝ) := fun g => b.equivFun g.coord
  have hf : Function.Injective f := by
    intro g h hgh
    apply NilpotentLieBCHGroup.ext
    exact b.equivFun.injective hgh
  have hmaps : Set.MapsTo f S A := by
    intro g hg
    exact ⟨hg.2.2, by simpa only [f, Basis.equivFun_apply] using hg.2.1⟩
  have hSfin : S.Finite := Set.Finite.of_injOn hmaps hf.injOn hAfin
  have hScard : S.ncard ≤ (2 * N + 1) ^ Fintype.card ι :=
    (Set.ncard_le_ncard_of_injOn f hmaps hf.injOn hAfin).trans hAcard
  let : Fintype S := hSfin.fintype
  have hone : (1 : NilpotentLieBCHGroup L s hnil) ∈ S := by
    refine ⟨map_one π, ?_, ?_⟩
    · simpa only [coord_one, map_zero, Finsupp.zero_apply, abs_zero] using fun _ : ι => hB
    · simpa only [coord_one, map_zero] using realDenominatorGrid_zero (ι := ι) m
  let : Nonempty S := ⟨⟨1, hone⟩⟩
  let e := Fintype.equivFin S
  refine ⟨Fintype.card S, Fintype.card_pos, ?_, fun j => (e.symm j).val,
    fun j => (e.symm j).property, ?_⟩
  · simpa only [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using hScard
  · intro g hmark hbound hgrid
    let x : S := ⟨g, hmark, hbound, hgrid⟩
    exact ⟨e x, congrArg Subtype.val (e.symm_apply_apply x)⟩

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

private theorem real_grid_integer_box_count_bound (d m : ℕ) {B p : ℝ}
    (hp : 0 ≤ p) (hB0 : 0 ≤ B) (hd : (d : ℝ) ≤ p)
    (hm : (m : ℝ) ≤ Real.exp p) (hB : B ≤ Real.exp p) :
    (((2 * ⌈(m : ℝ) * B⌉₊ + 1) ^ d : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
  have hprod : (m : ℝ) * B ≤ Real.exp (2 * p) := by
    simpa only [two_mul, Real.exp_add] using
      mul_le_mul hm hB hB0 (Real.exp_nonneg p)
  have hceil := (Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg m) hB0)).le
  have hone : 1 ≤ Real.exp (2 * p) := Real.one_le_exp (by linarith)
  have hfive : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hbase : ((2 * ⌈(m : ℝ) * B⌉₊ + 1 : ℕ) : ℝ) ≤ Real.exp (2 * p + 4) := by
    rw [Real.exp_add]
    push_cast
    have h := mul_le_mul_of_nonneg_left hfive (Real.exp_nonneg (2 * p))
    nlinarith
  rw [Nat.cast_pow]
  calc
    _ ≤ (Real.exp (2 * p + 4)) ^ d := pow_le_pow_left₀ (Nat.cast_nonneg _) hbase _
    _ = Real.exp ((d : ℝ) * (2 * p + 4)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (p * (2 * p + 4)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hd (by positivity))
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hp (sq_nonneg p)]

namespace NilpotentLieBCHGroup
open Module

variable {ι L G : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L] [Group G]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem exists_bounded_kernel_grid_enumeration_exp (b : Basis ι ℝ L)
    (π : NilpotentLieBCHGroup L s hnil →* G) (m : ℕ) (hm : 0 < m)
    {B p : ℝ} (hp : 0 ≤ p) (hB0 : 0 ≤ B) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hmp : (m : ℝ) ≤ Real.exp p) (hB : B ≤ Real.exp p) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + 2) ^ 3) ∧
      ∃ center : Fin n → NilpotentLieBCHGroup L s hnil,
        (∀ j, π (center j) = 1 ∧ (∀ i, |b.repr (center j).coord i| ≤ B) ∧
          b.equivFun (center j).coord ∈ realDenominatorGrid m) ∧
        ∀ g : NilpotentLieBCHGroup L s hnil, π g = 1 →
          (∀ i, |b.repr g.coord i| ≤ B) →
          b.equivFun g.coord ∈ realDenominatorGrid m → ∃ j, center j = g := by
  obtain ⟨n, hn, hcard, center, hcenters, hcover⟩ :=
    exists_bounded_kernel_grid_enumeration b π m ⌈(m : ℝ) * B⌉₊ hm hB0 (Nat.le_ceil _)
  refine ⟨n, hn, ?_, center, hcenters, hcover⟩
  exact (Nat.cast_le.mpr hcard).trans
    (real_grid_integer_box_count_bound (Fintype.card ι) m hp hB0 hd hmp hB)

theorem exists_uniform_bounded_kernel_grid_enumeration (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L G : Type*} [Fintype ι]
      [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L] [Group G]
      {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
      (b : Basis ι ℝ L) (π : NilpotentLieBCHGroup L s hnil →* G)
      (m : ℕ), 0 < m → ∀ (B p : ℝ), 0 ≤ p → 0 ≤ B →
      (Fintype.card ι : ℝ) ≤ p →
      (m : ℝ) ≤ Real.exp ((p + a) ^ a) → B ≤ Real.exp ((p + a) ^ a) →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ center : Fin n → NilpotentLieBCHGroup L s hnil,
          (∀ j, π (center j) = 1 ∧ (∀ i, |b.repr (center j).coord i| ≤ B) ∧
            b.equivFun (center j).coord ∈ realDenominatorGrid m) ∧
          ∀ g : NilpotentLieBCHGroup L s hnil, π g = 1 →
            (∀ i, |b.repr g.coord i| ≤ B) →
            b.equivFun g.coord ∈ realDenominatorGrid m → ∃ j, center j = g := by
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + (Polynomial.X + Polynomial.C a) ^ a + 2) ^ 3)
  refine ⟨C, hC, ?_⟩
  intro ι L G _ _ _ _ _ _ s hnil b π m hm B p hp hB0 hd hmcap hBcap
  let q := p + (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := le_add_of_nonneg_right (by positivity)
  have haq : (p + a) ^ a ≤ q := le_add_of_nonneg_left hp
  obtain ⟨n, hn, hcard, center, hcenters, hcover⟩ :=
    exists_bounded_kernel_grid_enumeration_exp b π m hm hq hB0 (hd.trans hpq)
      (hmcap.trans (Real.exp_le_exp.mpr haq)) (hBcap.trans (Real.exp_le_exp.mpr haq))
  refine ⟨n, hn, hcard.trans (Real.exp_le_exp.mpr ?_), center, hcenters, hcover⟩
  simpa [q, Polynomial.eval₂_pow] using hbudget p hp

end NilpotentLieBCHGroup
end Erdos3

end

end OAI
