/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.SlicedSourceAccuracy
import OAI.Combinatorics.Progressions.Geometry.CoordinateTreeOutside
import OAI.Combinatorics.Progressions.Lattices.ResiduePrimeDensityError

namespace OAI

section

namespace Erdos3

noncomputable def affineStabilityTolerance (T : ℝ) : ℝ := Real.exp (-(T + 4))

noncomputable def affineIncrementTolerance (L T : ℝ) : ℝ := Real.exp (-(L + T + 4))

theorem affineComparisonTolerance_bounds {L T level : ℝ}
    (hT : 0 ≤ T) (hlower : Real.exp (-L) ≤ level) :
    0 < Real.exp (-T) ∧ Real.exp (-T) ≤ 1 ∧
    (Real.exp (-T))⁻¹ ≤ Real.exp T ∧ 0 < level ∧
    0 < affineStabilityTolerance T ∧ affineStabilityTolerance T ≤ Real.exp (-T) / 8 ∧
    0 < affineIncrementTolerance L T ∧ affineIncrementTolerance L T ≤ level * Real.exp (-T) / 8 := by
  refine ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (by linarith), ?_,
    (Real.exp_pos _).trans_le hlower, Real.exp_pos _, ?_, Real.exp_pos _, ?_⟩
  · simp only [Real.exp_neg, inv_inv, le_refl]
  · exact exp_neg_le_exp_neg_div_eight le_rfl
  · calc
      affineIncrementTolerance L T ≤ Real.exp (-(L + T)) / 8 := exp_neg_le_exp_neg_div_eight le_rfl
      _ ≤ level * Real.exp (-T) / 8 := by
        rw [neg_add, Real.exp_add]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hlower (Real.exp_pos _).le) (by norm_num)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem modEq_nat_lcm_iff (m n : ℕ) (a b : ℤ) :
    a ≡ b [ZMOD (m.lcm n : ℤ)] ↔ a ≡ b [ZMOD (m : ℤ)] ∧ a ≡ b [ZMOD (n : ℤ)] := by
  constructor
  · intro h
    exact ⟨h.of_dvd (by exact_mod_cast Nat.dvd_lcm_left m n),
      h.of_dvd (by exact_mod_cast Nat.dvd_lcm_right m n)⟩
  · rintro ⟨hm, hn⟩
    exact Int.modEq_iff_dvd.mpr (Int.coe_lcm_dvd hm.dvd hn.dvd)

theorem residuePrimeCoordinate_constraints_lcm {ι σ : Type*} [DecidableEq ι]
    (M : ℕ) (a u z : σ → ℤ) (q : ι → ℕ)
    (hcop : Pairwise (fun i j => (q i).Coprime (q j)))
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i))
    (huM : ∀ j, u j ≡ a j [ZMOD (M : ℤ)])
    (hux : ∀ i ∈ I, (fun j => (u j : ZMod (q i))) = x i) :
    ((∀ j, z j ≡ a j [ZMOD (M : ℤ)]) ∧
      (∀ i ∈ I, (fun j => (z j : ZMod (q i))) = x i)) ↔
    ∀ j, z j ≡ u j [ZMOD (M.lcm (∏ i ∈ I, q i) : ℤ)] := by
  constructor
  · rintro ⟨hzM, hzx⟩ j
    apply (modEq_nat_lcm_iff M (∏ i ∈ I, q i) (z j) (u j)).mpr
    refine ⟨(hzM j).trans (huM j).symm, ?_⟩
    apply (modEq_selected_prod_iff q hcop I (z j) (u j)).mpr
    intro i hi
    apply (ZMod.intCast_eq_intCast_iff (z j) (u j) (q i)).mp
    exact congrFun ((hzx i hi).trans (hux i hi).symm) j
  · intro hz
    have hparts := fun j => (modEq_nat_lcm_iff M (∏ i ∈ I, q i) (z j) (u j)).mp (hz j)
    refine ⟨fun j => (hparts j).1.trans (huM j), ?_⟩
    intro i hi
    calc
      (fun j => (z j : ZMod (q i))) = (fun j => (u j : ZMod (q i))) := by
        funext j
        exact (ZMod.intCast_eq_intCast_iff (z j) (u j) (q i)).mpr
          ((modEq_selected_prod_iff q hcop I (z j) (u j)).mp (hparts j).2 i hi)
      _ = x i := hux i hi

noncomputable def residuePrimeCoordinateCell_lcmEquiv {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (hcop : Pairwise (fun i j => (q i).Coprime (q j)))
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) (u : ResiduePrimeCoordinateCell lo N M a q I x) :
    ResiduePrimeCoordinateCell lo N M a q I x ≃
      IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M.lcm (∏ i ∈ I, q i) : ℤ))
        (fun j => (u.val j).val) := by
  let uv := fun j => (u.val j).val
  have huM : ∀ j, uv j ≡ a j [ZMOD (M : ℤ)] :=
    fun j => (Finset.mem_filter.mp (u.val j).property).2
  have hc := fun z => residuePrimeCoordinate_constraints_lcm M a uv z q hcop I x huM u.property
  exact {
    toFun := fun z j => ⟨(z.val j).val, Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp (z.val j).property).1,
        (hc _).mp ⟨fun k => (Finset.mem_filter.mp (z.val k).property).2, z.property⟩ j⟩⟩
    invFun := fun z => ⟨fun j => ⟨(z j).val, Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp (z j).property).1,
        ((hc _).mpr (fun k => (Finset.mem_filter.mp (z k).property).2)).1 j⟩⟩,
      ((hc _).mpr (fun k => (Finset.mem_filter.mp (z k).property).2)).2⟩
    left_inv := fun z => by apply Subtype.ext; funext j; apply Subtype.ext; rfl
    right_inv := fun z => by funext j; apply Subtype.ext; rfl }

theorem residuePrimeCoordinateMean_lcm {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (hcop : Pairwise (fun i j => (q i).Coprime (q j)))
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) (u : ResiduePrimeCoordinateCell lo N M a q I x) :
    residuePrimeCoordinateMean f lo N M a q I x =
      physicalResidueMean f lo N (M.lcm (∏ i ∈ I, q i)) (fun j => (u.val j).val) := by
  classical
  exact Fintype.expect_equiv (residuePrimeCoordinateCell_lcmEquiv lo N M a q hcop I x u)
    _ _ (fun _ => rfl)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem primeCoordinateProduct_le_exp {ι : Type*} [DecidableEq ι]
    (q : ι → ℕ) (I : Finset ι) (p : ℝ) (hq : ∀ i, (q i : ℝ) ≤ Real.exp p) :
    ((∏ i ∈ I, q i : ℕ) : ℝ) ≤ Real.exp (p * I.card) := by
  rw [Nat.cast_prod]
  calc
    (∏ i ∈ I, (q i : ℝ)) ≤ ∏ _i ∈ I, Real.exp p :=
      Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun i _ => hq i)
    _ = Real.exp ((I.card : ℝ) * p) := by rw [Finset.prod_const, Real.exp_nat_mul]
    _ = Real.exp (p * I.card) := by rw [mul_comm]

theorem residuePrimeModulus_le_exp {ι : Type*} [DecidableEq ι]
    (q : ι → ℕ) (hqpos : ∀ i, 0 < q i) (I : Finset ι) (M : ℕ) (hM : 0 < M)
    (A B D : ℝ) (hB : 0 ≤ B) (hmodulus : (M : ℝ) ≤ Real.exp A)
    (hq : ∀ i, (q i : ℝ) ≤ Real.exp B) (hcard : (I.card : ℝ) ≤ D) :
    ((M.lcm (∏ i ∈ I, q i) : ℕ) : ℝ) ≤ Real.exp (A + B * D) := by
  have hp := primeCoordinateProduct_le_exp q I B hq
  have hp' := hp.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hcard hB))
  have hprodpos : 0 < ∏ i ∈ I, q i := Finset.prod_pos (fun i _ => hqpos i)
  have hlcm : ((M.lcm (∏ i ∈ I, q i) : ℕ) : ℝ) ≤ (M : ℝ) * ((∏ i ∈ I, q i : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.mul_pos hM hprodpos) (Nat.lcm_dvd_mul M _)
  calc
    _ ≤ (M : ℝ) * ((∏ i ∈ I, q i : ℕ) : ℝ) := hlcm
    _ ≤ Real.exp A * Real.exp (B * D) := mul_le_mul hmodulus hp' (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (A + B * D) := (Real.exp_add _ _).symm

theorem residuePrimeCell_log_cost {ι σ : Type*} [DecidableEq ι]
    (H N : σ → ℕ) (lo u : σ → ℤ) (M : ℕ) (hM : 0 < M)
    (q : ι → ℕ) (hqpos : ∀ i, 0 < q i) (I : Finset ι) (A B C D : ℝ)
    (hB : 0 ≤ B) (hmodulus : (M : ℝ) ≤ Real.exp A) (hq : ∀ i, (q i : ℝ) ≤ Real.exp B)
    (hcard : (I.card : ℝ) ≤ D) (hwidth : ∀ j, Real.exp (-C) * (H j : ℝ) ≤ (N j : ℝ))
    (hlarge : ∀ j, Real.exp (C + (A + B * D) + 2) ≤ (H j : ℝ)) :
    ResidueSliceLogCostLE H lo N (M.lcm (∏ i ∈ I, q i)) u (C + (A + B * D) + 2) := by
  have hpositive : 0 < M.lcm (∏ i ∈ I, q i) := by
    exact Nat.pos_of_ne_zero (Nat.lcm_ne_zero hM.ne' (Finset.prod_pos (fun i _ => hqpos i)).ne')
  apply residueSliceLogCostLE_of_bounds H N lo u _ C (A + B * D) hpositive
    (residuePrimeModulus_le_exp q hqpos I M hM A B D hB hmodulus hq hcard) hwidth
  intro j
  calc
    Real.exp (A + B * D + 2) = Real.exp (-C) * Real.exp (C + (A + B * D) + 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-C) * (H j : ℝ) := mul_le_mul_of_nonneg_left (hlarge j) (Real.exp_pos _).le
    _ ≤ (N j : ℝ) := hwidth j

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def residuePrimeCoordinateOutsideEquiv {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (hcop : Pairwise (fun i j => (q i).Coprime (q j)))
    (K : Finset ι) (base : ∀ i, σ → ZMod (q i))
    (u : ResiduePrimeCoordinateCell lo N M a q K base)
    (S : Finset {i // i ∉ K}) (x : ∀ i, σ → ZMod (q i)) (hx : ∀ i ∈ K, x i = base i) :
    ResiduePrimeCoordinateCell lo N M a q (K ∪ S.image Subtype.val) x ≃
      ResiduePrimeCoordinateCell lo N (M.lcm (∏ i ∈ K, q i)) (fun j => (u.val j).val)
        (fun i : {i // i ∉ K} => q i.val) S (fun i => x i.val) := by
  let uv := fun j => (u.val j).val
  have huM : ∀ j, uv j ≡ a j [ZMOD (M : ℤ)] :=
    fun j => (Finset.mem_filter.mp (u.val j).property).2
  have hux : ∀ i ∈ K, (fun j => (uv j : ZMod (q i))) = x i :=
    fun i hi => (u.property i hi).trans (hx i hi).symm
  have hc := fun z => residuePrimeCoordinate_constraints_lcm M a uv z q hcop K x huM hux
  exact {
    toFun := fun z => ⟨fun j => ⟨(z.val j).val, Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp (z.val j).property).1,
        (hc _).mp ⟨fun k => (Finset.mem_filter.mp (z.val k).property).2,
          fun i hi => z.property i (Finset.mem_union_left _ hi)⟩ j⟩⟩,
      fun i hi => z.property i.val (Finset.mem_union_right K (Finset.mem_image.mpr ⟨i, hi, rfl⟩))⟩
    invFun := fun z => ⟨fun j => ⟨(z.val j).val, Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp (z.val j).property).1,
        ((hc _).mpr (fun k => (Finset.mem_filter.mp (z.val k).property).2)).1 j⟩⟩, by
      intro i hi
      rcases Finset.mem_union.mp hi with hi | hi
      · exact ((hc _).mpr (fun k => (Finset.mem_filter.mp (z.val k).property).2)).2 i hi
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
        exact z.property j hj⟩
    left_inv := fun z => by apply Subtype.ext; funext j; apply Subtype.ext; rfl
    right_inv := fun z => by apply Subtype.ext; funext j; apply Subtype.ext; rfl }

theorem residuePrimeCoordinateMean_outside {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (hcop : Pairwise (fun i j => (q i).Coprime (q j)))
    (K : Finset ι) (base : ∀ i, σ → ZMod (q i))
    (u : ResiduePrimeCoordinateCell lo N M a q K base)
    (S : Finset {i // i ∉ K}) (x : ∀ i, σ → ZMod (q i)) (hx : ∀ i ∈ K, x i = base i) :
    residuePrimeCoordinateMean f lo N M a q (K ∪ S.image Subtype.val) x =
      residuePrimeCoordinateMean f lo N (M.lcm (∏ i ∈ K, q i)) (fun j => (u.val j).val)
        (fun i : {i // i ∉ K} => q i.val) S (fun i => x i.val) := by
  classical
  exact Fintype.expect_equiv (residuePrimeCoordinateOutsideEquiv lo N M a q hcop K base u S x hx)
    _ _ (fun _ => rfl)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def ResidueSliceUpperComparison {σ : Type*} [Fintype σ] [DecidableEq σ]
    (h g : (σ → ℤ) → ℂ) (parent : σ → ℤ) (H : σ → ℕ) (P level ε : ℝ) : Prop :=
  ∀ (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (u : σ → ℤ), 0 < M →
    PhysicalSubbox parent H lo N → ResidueSliceLogCostLE H lo N M u P →
    (physicalResidueMean h lo N M u).re ≤ level * (physicalResidueMean g lo N M u).re + ε

theorem ResidueSliceUpperComparison.on_prime_cell {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    {h g : (σ → ℤ) → ℂ} {parent lo a : σ → ℤ} {H N : σ → ℕ} {P level ε : ℝ}
    (hupper : ResidueSliceUpperComparison h g parent H P level ε)
    (hbox : PhysicalSubbox parent H lo N) (M : ℕ) (hM : 0 < M)
    (q : ι → ℕ) (hqpos : ∀ i, 0 < q i) (hcop : Pairwise (fun i j => (q i).Coprime (q j)))
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i))
    (hcost : ∀ u : σ → ℤ, ResidueSliceLogCostLE H lo N (M.lcm (∏ i ∈ I, q i)) u P)
    (hne : Nonempty (ResiduePrimeCoordinateCell lo N M a q I x)) :
    (residuePrimeCoordinateMean h lo N M a q I x).re ≤
      level * (residuePrimeCoordinateMean g lo N M a q I x).re + ε := by
  obtain ⟨u⟩ := hne
  have hpositive : 0 < M.lcm (∏ i ∈ I, q i) :=
    Nat.pos_of_ne_zero (Nat.lcm_ne_zero hM.ne' (Finset.prod_pos (fun i _ => hqpos i)).ne')
  have hslice := hupper lo N _ (fun j => (u.val j).val) hpositive hbox (hcost _)
  rw [residuePrimeCoordinateMean_lcm h lo N M a q hcop I x u,
    residuePrimeCoordinateMean_lcm g lo N M a q hcop I x u]
  exact hslice

theorem ResiduePrimeCoordinateStable.refinement_upper_bound {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
    {r : ℕ} {δ level ε : ℝ} {I : Finset ι} {x : ∀ i, σ → ZMod (q i)}
    (hstable : ResiduePrimeCoordinateStable g lo N M a q r δ I x) (hlevel : 0 ≤ level)
    (J : Finset ι) (hIJ : Disjoint I J) (hJ : J.card ≤ r)
    (y : ∀ i, σ → ZMod (q i)) (hxy : ∀ i ∈ I, y i = x i)
    (hne : Nonempty (ResiduePrimeCoordinateCell lo N M a q (I ∪ J) y))
    (hupper : (residuePrimeCoordinateMean h lo N M a q (I ∪ J) y).re ≤
      level * (residuePrimeCoordinateMean g lo N M a q (I ∪ J) y).re + ε) :
    (residuePrimeCoordinateMean h lo N M a q (I ∪ J) y).re ≤
      level * (residuePrimeCoordinateMean g lo N M a q I x).re + ε + level * δ := by
  have hs := hstable J hIJ hJ y hxy hne
  have hr := (Complex.abs_re_le_norm (residuePrimeCoordinateMean g lo N M a q I x -
    residuePrimeCoordinateMean g lo N M a q (I ∪ J) y)).trans hs
  rw [Complex.sub_re] at hr
  have hmean : (residuePrimeCoordinateMean g lo N M a q (I ∪ J) y).re ≤
      (residuePrimeCoordinateMean g lo N M a q I x).re + δ := by
    have hh := (abs_le.mp hr).1
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hmean hlevel
  nlinarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem ResiduePrimeCoordinateStable.of_outside {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (hcop : Pairwise (fun i j => (q i).Coprime (q j)))
    (K : Finset ι) (base : ∀ i, σ → ZMod (q i))
    (u : ResiduePrimeCoordinateCell lo N M a q K base)
    (r : ℕ) (δ : ℝ) (S : Finset {i // i ∉ K})
    (x : ∀ i, σ → ZMod (q i)) (hx : ∀ i ∈ K, x i = base i)
    (hstable : ResiduePrimeCoordinateStable f lo N (M.lcm (∏ i ∈ K, q i))
      (fun j => (u.val j).val) (fun i : {i // i ∉ K} => q i.val) r δ S (fun i => x i.val)) :
    ResiduePrimeCoordinateStable f lo N M a q r δ (K ∪ S.image Subtype.val) x := by
  classical
  intro J hdisjoint hcard y hagree hnonempty
  let J' : Finset {i // i ∉ K} := J.subtype (fun i => i ∉ K)
  have hout : ∀ i ∈ J, i ∉ K := by
    intro i hi hK
    exact Finset.disjoint_left.mp hdisjoint (Finset.mem_union_left _ hK) hi
  have himage : J'.image Subtype.val = J := by
    ext i
    constructor
    · intro hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_subtype.mp hj
    · intro hi
      exact Finset.mem_image.mpr ⟨⟨i, hout i hi⟩, Finset.mem_subtype.mpr hi, rfl⟩
  have hcard' : J'.card ≤ r := by
    have heq : J'.card = J.card := by
      rw [← himage, Finset.card_image_of_injective J' Subtype.val_injective]
    exact heq ▸ hcard
  have hdisjoint' : Disjoint S J' := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact Finset.disjoint_left.mp hdisjoint
      (Finset.mem_union_right K (Finset.mem_image.mpr ⟨i, hi, rfl⟩)) (Finset.mem_subtype.mp hj)
  have hbasey : ∀ i ∈ K, y i = base i :=
    fun i hi => (hagree i (Finset.mem_union_left _ hi)).trans (hx i hi)
  have hunion : (K ∪ S.image Subtype.val) ∪ J = K ∪ (S ∪ J').image Subtype.val := by
    rw [Finset.image_union, himage, Finset.union_assoc]
  have hnonempty' : Nonempty (ResiduePrimeCoordinateCell lo N (M.lcm (∏ i ∈ K, q i))
      (fun j => (u.val j).val) (fun i : {i // i ∉ K} => q i.val) (S ∪ J') (fun i => y i.val)) := by
    rw [hunion] at hnonempty
    obtain ⟨z⟩ := hnonempty
    exact ⟨residuePrimeCoordinateOutsideEquiv lo N M a q hcop K base u (S ∪ J') y hbasey z⟩
  rw [residuePrimeCoordinateMean_outside f lo N M a q hcop K base u S x hx, hunion,
    residuePrimeCoordinateMean_outside f lo N M a q hcop K base u (S ∪ J') y hbasey]
  apply hstable J' hdisjoint' hcard' (fun i => y i.val) _ hnonempty'
  intro i hi
  exact hagree i.val (Finset.mem_union_right K (Finset.mem_image.mpr ⟨i, hi, rfl⟩))

theorem ResiduePrimeCoordinateStable.lift_outside {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (hcop : Pairwise (fun i j => (q i).Coprime (q j)))
    (K : Finset ι) (base : ∀ i, σ → ZMod (q i))
    (u : ResiduePrimeCoordinateCell lo N M a q K base)
    (r : ℕ) (δ : ℝ) (S : Finset {i // i ∉ K})
    (x : ∀ i : {i // i ∉ K}, σ → ZMod (q i.val))
    (hstable : ResiduePrimeCoordinateStable f lo N (M.lcm (∏ i ∈ K, q i))
      (fun j => (u.val j).val) (fun i : {i // i ∉ K} => q i.val) r δ S x) :
    ResiduePrimeCoordinateStable f lo N M a q r δ (K ∪ S.image Subtype.val)
      (CoordinateDecisionTree.outsideAssignment K base x) := by
  apply ResiduePrimeCoordinateStable.of_outside f lo N M a q hcop K base u r δ S
    (CoordinateDecisionTree.outsideAssignment K base x)
  · intro i hi
    simp only [CoordinateDecisionTree.outsideAssignment, hi, dite_true]
  · have heq : (fun i : {i // i ∉ K} =>
        CoordinateDecisionTree.outsideAssignment K base x i.val) = x := by
      funext i
      simp only [CoordinateDecisionTree.outsideAssignment, i.property, dite_false]
    rw [heq]
    exact hstable

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem primeCoordinate_error_le_exp {ι σ : Type*} [DecidableEq ι] [Fintype σ]
    (moduli : ι → ℕ) (L : σ → ℕ) (R : ℕ) (B C D : ℝ) (hB : 0 ≤ B)
    (hmoduli : ∀ i, (moduli i : ℝ) ≤ Real.exp B)
    (hdim : (Fintype.card σ : ℝ) ≤ Real.exp C)
    (hlength : ∀ k, Real.exp (B * R + D + C + 1) ≤ (L k : ℝ))
    (S : Finset ι) (hS : S.card ≤ R) :
    2 * (∑ k, ((∏ i ∈ S, moduli i : ℕ) : ℝ) / L k) ≤ Real.exp (-D) := by
  have hprod : ((∏ i ∈ S, moduli i : ℕ) : ℝ) ≤ Real.exp (B * R) :=
    (primeCoordinateProduct_le_exp moduli S B hmoduli).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hS) hB))
  have hterm (k : σ) : ((∏ i ∈ S, moduli i : ℕ) : ℝ) / L k ≤ Real.exp (-D - C - 1) := by
    have hL : (0 : ℝ) < L k := (Real.exp_pos _).trans_le (hlength k)
    apply (div_le_iff₀ hL).mpr
    calc
      _ ≤ Real.exp (B * R) := hprod
      _ = Real.exp (-D - C - 1) * Real.exp (B * R + D + C + 1) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hlength k) (Real.exp_pos _).le
  have hs := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset σ)) => hterm k)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ 2 * ((Fintype.card σ : ℝ) * Real.exp (-D - C - 1)) := mul_le_mul_of_nonneg_left hs (by norm_num)
    _ ≤ Real.exp 1 * (Real.exp C * Real.exp (-D - C - 1)) :=
      mul_le_mul htwo (mul_le_mul_of_nonneg_right hdim (Real.exp_pos _).le)
        (by positivity) (Real.exp_pos _).le
    _ = Real.exp (-D) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

theorem residuePrimeDensity_close_of_lengths {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a))
    (moduli : ι → ℕ) [∀ i, NeZero (moduli i)] (hM : 0 < M)
    (hcop : ∀ i, M.Coprime (moduli i)) (hpair : Pairwise (fun i l => (moduli i).Coprime (moduli l)))
    (R : ℕ) (B C D η : ℝ) (hB : 0 ≤ B) (hη : η ≤ 1) (herror : Real.exp (-D) ≤ η)
    (hmoduli : ∀ i, (moduli i : ℝ) ≤ Real.exp B) (hdim : (Fintype.card σ : ℝ) ≤ Real.exp C)
    (hlength : ∀ k, Real.exp (B * R + D + C + 1) ≤
      (residueIndexLength (lo k) (lo k + N k) M (a k) : ℝ)) :
    ProductMarginalsClose (primeCoordinateReference (σ := σ) moduli)
      (residuePrimeCoordinateDensity lo N M a hne moduli (fun _ => 1)) η R := by
  have herr (S : Finset ι) (hS : S.card ≤ R) :=
    (primeCoordinate_error_le_exp moduli (fun k => residueIndexLength (lo k) (lo k + N k) M (a k))
      R B C D hB hmoduli hdim hlength S hS).trans herror
  apply residuePrimeCoordinateDensity_productMarginalsClose lo N M a hne moduli hM hcop hpair R η
  · intro S hS
    have he := herr S hS
    linarith
  · exact herr

end Erdos3

end

section

namespace Erdos3

theorem ResidueSliceUpperComparison.restrict_budget_and_error {I : Type*}
    [Fintype I] [DecidableEq I] {h g : (I → ℤ) → ℂ} {lo : I → ℤ} {N : I → ℕ}
    {originalBudget referenceBudget level originalError referenceError : ℝ}
    (hupper : ResidueSliceUpperComparison h g lo N originalBudget level originalError)
    (hbudget : referenceBudget ≤ originalBudget) (herror : originalError ≤ referenceError) :
    ResidueSliceUpperComparison h g lo N referenceBudget level referenceError := by
  intro cellLo cellN M a hM hsub hcost
  exact (hupper cellLo cellN M a hM hsub (hcost.mono hbudget)).trans (by linarith)

theorem ResidueSliceUpperComparison.from_exponential_budget {I : Type*}
    [Fintype I] [DecidableEq I] {h g : (I → ℤ) → ℂ} {lo : I → ℤ} {N : I → ℕ}
    {originalBudget referenceBudget level densityLog tail : ℝ}
    (hupper : ResidueSliceUpperComparison h g lo N originalBudget level (Real.exp (-originalBudget)))
    (hbudget : referenceBudget ≤ originalBudget) (hprecision : densityLog + tail + 4 ≤ originalBudget) :
    ResidueSliceUpperComparison h g lo N referenceBudget level (affineIncrementTolerance densityLog tail) := by
  exact hupper.restrict_budget_and_error hbudget (Real.exp_le_exp.mpr (by linarith))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem not_residueSliceUpperComparison_iff_exists_residue_slice
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    {h g : (σ → ℤ) → ℂ} {parent : σ → ℤ} {H : σ → ℕ} {P level ε : ℝ} :
    ¬ ResidueSliceUpperComparison h g parent H P level ε ↔
      ∃ (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (u : σ → ℤ),
        0 < M ∧ PhysicalSubbox parent H lo N ∧ ResidueSliceLogCostLE H lo N M u P ∧
          ε < (physicalResidueMean h lo N M u).re -
            level * (physicalResidueMean g lo N M u).re := by
  classical
  simp only [ResidueSliceUpperComparison, not_forall, not_le]
  constructor
  · rintro ⟨lo, N, M, u, hM, hbox, hcost, hscore⟩
    exact ⟨lo, N, M, u, hM, hbox, hcost, by linarith⟩
  · rintro ⟨lo, N, M, u, hM, hbox, hcost, hscore⟩
    exact ⟨lo, N, M, u, hM, hbox, hcost, by linarith⟩

theorem exists_residue_slice_of_not_upper
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    {h g : (σ → ℤ) → ℂ} {parent : σ → ℤ} {H : σ → ℕ} {P level ε : ℝ}
    (hfailure : ¬ ResidueSliceUpperComparison h g parent H P level ε) :
    ∃ (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (u : σ → ℤ),
      0 < M ∧ PhysicalSubbox parent H lo N ∧ ResidueSliceLogCostLE H lo N M u P ∧
        ε < (physicalResidueMean h lo N M u).re -
          level * (physicalResidueMean g lo N M u).re :=
  not_residueSliceUpperComparison_iff_exists_residue_slice.mp hfailure

theorem ResidueSliceLogCostLE.lengths_pos {σ : Type*}
    {H N : σ → ℕ} {lo u : σ → ℤ} {M : ℕ} {P : ℝ}
    (hcost : ResidueSliceLogCostLE H lo N M u P) (hH : ∀ j, 0 < H j) :
    ∀ j, 0 < residueIndexLength (lo j) (lo j + N j) M (u j) := by
  intro j
  have hp : (0 : ℝ) < Real.exp (-P) * (H j : ℝ) :=
    mul_pos (Real.exp_pos _) (Nat.cast_pos.mpr (hH j))
  exact Nat.cast_pos.mp (hp.trans_le (hcost j))

theorem ResidueSliceLogCostLE.nonempty {σ : Type*}
    {H N : σ → ℕ} {lo u : σ → ℤ} {M : ℕ} {P : ℝ}
    (hcost : ResidueSliceLogCostLE H lo N M u P) (hH : ∀ j, 0 < H j) (hM : 0 < M) :
    Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) u) := by
  classical
  have hpos := hcost.lengths_pos hH
  have hne (j : σ) : Nonempty ↥(Finset.filter (fun x => x ≡ u j [ZMOD (M : ℤ)])
      (Finset.Ico (lo j) (lo j + N j))) := by
    have hj := hpos j
    rw [residueIndexLength_eq_card _ _ _ _ (Nat.cast_pos.mpr hM)] at hj
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hj
    exact ⟨⟨x, hx⟩⟩
  exact ⟨fun j => Classical.choice (hne j)⟩

theorem exists_nonempty_residue_slice_of_not_upper
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    {h g : (σ → ℤ) → ℂ} {parent : σ → ℤ} {H : σ → ℕ} {P level ε : ℝ}
    (hε : 0 ≤ ε) (hfailure : ¬ ResidueSliceUpperComparison h g parent H P level ε) :
    ∃ (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (u : σ → ℤ),
      0 < M ∧ PhysicalSubbox parent H lo N ∧ ResidueSliceLogCostLE H lo N M u P ∧
        Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) u) ∧
        (∀ j, 0 < residueIndexLength (lo j) (lo j + N j) M (u j)) ∧
        ε < (physicalResidueMean h lo N M u).re -
          level * (physicalResidueMean g lo N M u).re := by
  classical
  obtain ⟨lo, N, M, u, hM, hbox, hcost, hscore⟩ := exists_residue_slice_of_not_upper hfailure
  have hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) u) := by
    by_contra hempty
    have := not_nonempty_iff.mp hempty
    have hh : physicalResidueMean h lo N M u = 0 := by simp [physicalResidueMean]
    have hg : physicalResidueMean g lo N M u = 0 := by simp [physicalResidueMean]
    rw [hh, hg] at hscore
    simp only [Complex.zero_re, mul_zero, sub_zero] at hscore
    exact (not_lt_of_ge hε) hscore
  refine ⟨lo, N, M, u, hM, hbox, hcost, hne, ?_, hscore⟩
  exact integerResidueBox_lengths_pos _ _ _ _ (fun _ => Nat.cast_pos.mpr hM) hne

end Erdos3

end

end OAI
