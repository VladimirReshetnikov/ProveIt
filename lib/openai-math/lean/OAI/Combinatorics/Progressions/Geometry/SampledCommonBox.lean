/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Dynamics.ProductCutoffExponentialBudget
import OAI.Combinatorics.Progressions.Estimates.CommonStrideGowersTransfer
import OAI.Combinatorics.Progressions.Estimates.FiniteCommonStrideFamily
import OAI.Combinatorics.Progressions.Estimates.SampledCommonSlice
import OAI.Combinatorics.Progressions.Lattices.IntegerBoxCoordinateEquiv

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem commonStrideCount_exp_bound {p : ℝ} (hp : 0 ≤ p) :
    (⌈2 / Real.exp (-p)⌉₊ : ℝ) ≤ Real.exp (p + 2) := by
  rw [Real.exp_neg, div_inv_eq_mul]
  have hceil := (Nat.ceil_lt_add_one (show 0 ≤ 2 * Real.exp p by positivity)).le
  have h1 := Real.one_le_exp hp
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  calc
    _ ≤ 3 * Real.exp p := by linarith
    _ ≤ Real.exp 2 * Real.exp p := mul_le_mul_of_nonneg_right h3 (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, add_comm]

theorem exists_dense_box_inner_family {I : Type*} [Fintype I] [DecidableEq I]
    {p : ℝ} (hp : 0 ≤ p) (N : I → ℕ) :
    ∃ D : Finset (Finset (I → ℤ)),
      (D.card : ℝ) ≤ Real.exp ((5 * p + 20) * Fintype.card I + p + 2) ∧
      (∀ A ∈ D, ∃ (c : I → ℤ) (m : ℕ) (H : I → ℕ),
        0 < m ∧ m ≤ ⌈2 / Real.exp (-p)⌉₊ ∧ A = commonStrideBox c m H) ∧
      ∀ (c : I → ℤ) (m : ℕ) (H : I → ℕ), 0 < m → (∀ i, 0 < H i) →
        (∀ i, integerProgressionSupport (c i) m (H i) ⊆ Finset.Ico (0 : ℤ) (N i)) →
        (∀ i, Real.exp (-p) * N i ≤ (H i : ℝ)) →
        ∃ A ∈ D, A.Nonempty ∧ A ⊆ commonStrideBox c m H ∧
          2 * (1 - (A.card : ℝ) / (commonStrideBox c m H).card) ≤
            Fintype.card I * Real.exp (-p) := by
  classical
  choose C hcount hshape hcover using fun i => exists_finite_inner_interval_family hp (N i)
  let M := ⌈2 / Real.exp (-p)⌉₊
  let D := finiteCommonStrideFamily M C
  have hprod : (∏ i, ((C i).card : ℝ)) ≤ Real.exp ((4 * p + 18) * Fintype.card I) := by
    calc
      _ ≤ ∏ _i : I, Real.exp (4 * p + 18) :=
        Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun i _ => hcount i)
      _ = _ := by
        rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
        congr 1
        ring
  refine ⟨D, ?_, fun A hA => finiteCommonStrideFamily_shape M C hshape hA, ?_⟩
  · calc
      (D.card : ℝ) ≤ (M : ℝ) ^ (Fintype.card I + 1) * ∏ i, ((C i).card : ℝ) := by
        exact_mod_cast finiteCommonStrideFamily_card M C
      _ ≤ Real.exp (p + 2) ^ (Fintype.card I + 1) *
          Real.exp ((4 * p + 18) * Fintype.card I) :=
        mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) (commonStrideCount_exp_bound hp) _)
          hprod (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _)) (by positivity)
      _ = _ := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        push_cast
        ring
  · intro c m H hm hH hsub hdense
    obtain ⟨d, r, a, hd, hdM, hcoord⟩ := exists_bounded_common_stride_reindex N H c hm hH
      (Real.exp_pos _) (Real.exp_le_one_iff.mpr (by linarith)) hsub hdense
    choose S hSC hSn hSsub hShalf hSerr using fun i =>
      hcover i (a i) (H i) (hcoord i).2.1 (hH i) (hdense i)
    let Aaxis (i : I) := (S i).image (fun x => (r i : ℤ) + d * x)
    let A := Fintype.piFinset Aaxis
    have hg (i : I) : Function.Injective (fun x : ℤ => (r i : ℤ) + d * x) := by
      intro x y he
      exact mul_left_cancel₀ (by exact_mod_cast hd.ne' : (d : ℤ) ≠ 0) (add_left_cancel he)
    have hAsub (i : I) : Aaxis i ⊆ integerProgressionSupport (c i) m (H i) := by
      rw [(hcoord i).2.2]
      exact Finset.image_subset_image (hSsub i)
    have hB (i : I) : (integerProgressionSupport (c i) m (H i)).Nonempty := by
      apply Finset.card_pos.mp
      simpa only [card_integerProgressionSupport _ _ _ hm] using hH i
    refine ⟨A, mem_finiteCommonStrideFamily M C hd hdM r (fun i => (hcoord i).1) S hSC,
      Fintype.piFinset_nonempty.mpr (fun i => (hSn i).image _),
      Fintype.piFinset_subset _ _ hAsub, ?_⟩
    have hloss := piFinset_inner_normalized_loss Aaxis
      (fun i => integerProgressionSupport (c i) m (H i)) hB hAsub
      (fun _ => Real.exp (-p)) (fun i => by
        simpa only [Aaxis, Finset.card_image_of_injective _ (hg i),
          card_integerProgressionSupport _ _ _ hm] using hSerr i)
    simpa only [A, commonStrideBox, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hloss

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

def IsDenseCommonStrideBox {I : Type*} [Fintype I] [DecidableEq I]
    (N : I → ℕ) (p : ℝ) (A : Finset (I → ℤ)) : Prop :=
  ∃ (c : I → ℤ) (m : ℕ) (H : I → ℕ), 0 < m ∧ (∀ i, 0 < H i) ∧
    (∀ i, integerProgressionSupport (c i) m (H i) ⊆ Finset.Ico (0 : ℤ) (N i)) ∧
    (∀ i, Real.exp (-p) * N i ≤ (H i : ℝ)) ∧ A = commonStrideBox c m H

theorem IsDenseCommonStrideBox.nonempty {I : Type*} [Fintype I] [DecidableEq I]
    {N : I → ℕ} {p : ℝ} {A : Finset (I → ℤ)} (h : IsDenseCommonStrideBox N p A) :
    A.Nonempty := by
  obtain ⟨c, m, H, hm, hH, _, _, rfl⟩ := h
  exact commonStrideBox_nonempty c hm H hH

theorem exists_finite_site_box_inner_family {I T : Type*} [Fintype I] [DecidableEq I]
    [Fintype T] (e : T → I → ℤ) (he : Function.Injective e) {p : ℝ} (hp : 0 ≤ p) (N : I → ℕ) :
    ∃ C : Finset (Finset T),
      (C.card : ℝ) ≤ Real.exp ((5 * p + 20) * Fintype.card I + p + 2) ∧
      (∀ A ∈ C, A.Nonempty → ∃ (c : I → ℤ) (m : ℕ) (H : I → ℕ),
        0 < m ∧ (∀ i, 0 < H i) ∧ A.image e = commonStrideBox c m H) ∧
      ∀ S : Finset T, IsDenseCommonStrideBox N p (S.image e) →
        ∃ A ∈ C, A.Nonempty ∧ A ⊆ S ∧
          2 * (1 - (A.card : ℝ) / S.card) ≤ Fintype.card I * Real.exp (-p) := by
  obtain ⟨D, hD, hshape, hcover⟩ := exists_dense_box_inner_family hp N
  refine ⟨finiteSiteInnerFamily e D, ?_, ?_, ?_⟩
  · exact (show ((finiteSiteInnerFamily e D).card : ℝ) ≤ D.card by
      exact_mod_cast finiteSiteInnerFamily_card e D).trans hD
  · intro A hA hAn
    obtain ⟨c, m, H, hm, _, heq⟩ := hshape (A.image e) (finiteSiteInnerFamily_image_mem e D hA)
    have hBn : (commonStrideBox c m H).Nonempty := heq ▸ hAn.image e
    have haxis := Fintype.piFinset_nonempty.mp hBn
    refine ⟨c, m, H, hm, ?_, heq⟩
    intro i
    have hcard := (haxis i).card_pos
    simpa only [card_integerProgressionSupport _ _ _ hm] using hcard
  · intro S hS
    obtain ⟨c, m, H, hm, hH, hsub, hdense, heq⟩ := hS
    obtain ⟨A, hAD, hAn, hAS, hloss⟩ := hcover c m H hm hH hsub hdense
    have hAS' : A ⊆ S.image e := by rw [heq]; exact hAS
    have hAall : A ⊆ Finset.univ.image e := hAS'.trans (Finset.image_subset_image (Finset.subset_univ S))
    have hcard := finiteSitePreimage_card e he A hAall
    refine ⟨finiteSitePreimage e A, mem_finiteSiteInnerFamily e D hAD hAall,
      Finset.card_pos.mp (by rw [hcard]; exact hAn.card_pos),
      finiteSitePreimage_subset e he A S hAS', ?_⟩
    rw [← heq, Finset.card_image_of_injective _ he] at hloss
    simpa only [hcard] using hloss

end Erdos3

end

section

namespace Erdos3

theorem commonStridePoint_coordinateEquiv {X Y : Type*} (e : X ≃ Y)
    (c : X → ℤ) (m : ℕ) (x : X → ℤ) :
    integerPointCoordinateEquiv e (commonStridePoint c m x) =
      commonStridePoint (integerPointCoordinateEquiv e c) m
        (integerPointCoordinateEquiv e x) := rfl

theorem commonStrideIndex_coordinateEquiv {X Y : Type*} (e : X ≃ Y)
    (c : X → ℤ) (m : ℕ) (x : X → ℤ) :
    integerPointCoordinateEquiv e (commonStrideIndex c m x) =
      commonStrideIndex (integerPointCoordinateEquiv e c) m
        (integerPointCoordinateEquiv e x) := rfl

theorem commonStrideBox_map_coordinateEquiv {X Y : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : X ≃ Y) (c : X → ℤ) (m : ℕ) (H : X → ℕ) :
    (commonStrideBox c m H).map (integerPointCoordinateEquiv e).toEmbedding =
      commonStrideBox (integerPointCoordinateEquiv e c) m
        (coordinateReindexedSides e H) := by
  classical
  ext y
  rw [Finset.mem_map_equiv]
  simp only [commonStrideBox, Fintype.mem_piFinset]
  change (∀ i, y (e i) ∈ integerProgressionSupport (c i) m (H i)) ↔
    ∀ j, y j ∈ integerProgressionSupport (c (e.symm j)) m (H (e.symm j))
  constructor
  · intro h j
    simpa only [Equiv.apply_symm_apply] using h (e.symm j)
  · intro h i
    simpa only [Equiv.symm_apply_apply] using h (e i)

theorem commonStrideBox_image_coordinateEquiv {X Y : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : X ≃ Y) (c : X → ℤ) (m : ℕ) (H : X → ℕ) :
    (commonStrideBox c m H).image (integerPointCoordinateEquiv e) =
      commonStrideBox (integerPointCoordinateEquiv e c) m
        (coordinateReindexedSides e H) := by
  simpa only [Finset.map_eq_image, Equiv.coe_toEmbedding] using
    commonStrideBox_map_coordinateEquiv e c m H

theorem IsDenseCommonStrideBox.coordinateEquiv {X Y : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : X ≃ Y) {N : X → ℕ} {p : ℝ} {A : Finset (X → ℤ)}
    (h : IsDenseCommonStrideBox N p A) :
    IsDenseCommonStrideBox (coordinateReindexedSides e N) p
      (A.image (integerPointCoordinateEquiv e)) := by
  obtain ⟨c, m, H, hm, hH, hsub, hdense, rfl⟩ := h
  refine ⟨integerPointCoordinateEquiv e c, m, coordinateReindexedSides e H,
    hm, fun j => hH (e.symm j), fun j => hsub (e.symm j),
    fun j => hdense (e.symm j), commonStrideBox_image_coordinateEquiv e c m H⟩

theorem IsDenseCommonStrideBox.coordinateEquiv_map {X Y : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : X ≃ Y) {N : X → ℕ} {p : ℝ} {A : Finset (X → ℤ)}
    (h : IsDenseCommonStrideBox N p A) :
    IsDenseCommonStrideBox (coordinateReindexedSides e N) p
      (A.map (integerPointCoordinateEquiv e).toEmbedding) := by
  simpa only [Finset.map_eq_image, Equiv.coe_toEmbedding] using h.coordinateEquiv e

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def denseBoxGowersTransferCost (j n : ℕ) (p q : ℝ) : ℝ :=
  (q + (2 * p + 6) * n + 1) * (2 ^ (j + 2) * n + 1 : ℕ) + ((n + 3) * n : ℕ)

theorem denseBox_gowers_transfer (j : ℕ) {I : Type*} [Fintype I] [DecidableEq I]
    (N : I → ℕ) [∀ i, NeZero (N i)] {A : Finset (I → ℤ)} {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hA : IsDenseCommonStrideBox N p A)
    (f : (I → ℤ) → ℂ) (hf : ∀ x ∈ integerBox N, ‖f x‖ ≤ 1)
    (hnorm : Real.exp (-q) ≤ finiteSupportGowersNorm (j + 2) A f) :
    Real.exp (-denseBoxGowersTransferCost j (Fintype.card I) p q) ≤
      finiteSupportGowersNorm (j + 2) (integerBox N) f := by
  obtain ⟨c, m, H, hm, hH, hsub, hdense, rfl⟩ := hA
  obtain ⟨d, r, a, hd, hdmax, hrepr⟩ := exists_bounded_common_stride_reindex N H c hm hH
    (Real.exp_pos (-p)) (Real.exp_le_one_iff.mpr (by linarith)) hsub hdense
  let b : I → ℤ := fun i => (r i : ℤ) + (d : ℤ) * a i
  have hsame (i) : integerProgressionSupport (c i) m (H i) =
      integerProgressionSupport (b i) d (H i) := by
    exact (hrepr i).2.2.trans (integerProgressionSupport_reindex (r i) d (a i) (H i)).symm
  have hsameBox : commonStrideBox c m H = commonStrideBox b d H := by
    unfold commonStrideBox
    exact congrArg Fintype.piFinset (funext hsame)
  have hdexp : (d : ℝ) ≤ Real.exp (p + 2) :=
    (Nat.cast_le.mpr hdmax).trans (commonStrideCount_exp_bound hp)
  have hsub' (i) : integerProgressionSupport (b i) d (H i) ⊆ Finset.Ico (0 : ℤ) (N i) := by
    rw [← hsame i]
    exact hsub i
  have hdense' (i) : Real.exp (-(p + 2)) * N i ≤ (H i : ℝ) :=
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (Nat.cast_nonneg _)).trans
      (hdense i)
  have hratio := product_box_volume_ratio_exp N H (fun i => NeZero.pos _) hd
    (show 0 ≤ p + 2 by linarith) hdexp hdense'
  have hlocal : Real.exp (-q) ≤ finiteSupportGowersNorm (j + 2) (integerBox H)
      (fun x => f (commonStridePoint b d x)) := by
    rw [← finiteSupportGowersNorm_commonStride (j + 2) b hd H f, ← hsameBox]
    exact hnorm
  let Q := q + (2 * (p + 2) + 2) * Fintype.card I
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hlarge : Real.exp (-Q) ≤ ((∏ i, H i : ℕ) : ℝ) /
      ((∏ i, 4 * (d * N i) : ℕ) : ℝ) *
        finiteSupportGowersNorm (j + 2) (integerBox H)
          (fun x => f (commonStridePoint b d x)) := by
    calc
      _ = Real.exp (-((2 * (p + 2) + 2) * Fintype.card I)) * Real.exp (-q) := by
        rw [← Real.exp_add]
        congr 1
        dsimp only [Q]
        ring
      _ ≤ _ := mul_le_mul hratio hlocal (Real.exp_nonneg _) (by positivity)
  have htransfer := commonStride_gowers_transfer j N H b hd hH hsub' f hf
    (Real.exp_pos (-Q)) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hQ)) hlarge
  have hbudget := (productCutoff_transfer_exp j (Fintype.card I) hQ).trans htransfer
  have hcost : (Q + 1) * ((2 ^ (j + 2) * Fintype.card I + 1 : ℕ) : ℝ) +
      (((Fintype.card I + 3) * Fintype.card I : ℕ) : ℝ) =
      denseBoxGowersTransferCost j (Fintype.card I) p q := by
    dsimp only [denseBoxGowersTransferCost, Q]
    ring
  rwa [hcost] at hbudget

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_common_sampled_box {Ω T X I : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype T] [Nonempty T] [Fintype I] [DecidableEq I]
    {J : Ω → Type*} [∀ z, Nonempty (J z)]
    (μ : FiniteProbabilityWeights Ω) (F : Ω → T → X)
    (S : ∀ z, J z → Finset T) (w : ∀ z, J z → T → ℂ)
    (e : T → I → ℤ) (he : Function.Injective e) {p : ℝ} (hp : 0 ≤ p) (N : I → ℕ)
    (hslice : ∀ z j, IsDenseCommonStrideBox N p ((S z j).image e))
    (hw : ∀ z j t, ‖w z j t‖ ≤ 1) (v : X → ℂ) (hv : ∀ x, ‖v x‖ ≤ 1)
    {α ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 ≤ ρ)
    (hlarge : ε + Fintype.card I * Real.exp (-p) + ρ < α)
    (hmean : α ≤ sampledSliceSeminorm μ F S w v) :
    ∃ A : Finset T, A.Nonempty ∧
      (∃ (c : I → ℤ) (m : ℕ) (H : I → ℕ),
        0 < m ∧ (∀ i, 0 < H i) ∧ A.image e = commonStrideBox c m H) ∧
      ∃ G : Finset Ω, ∃ j : ∀ z, J z,
        Real.exp (-((5 * p + 20) * Fintype.card I + p + 2)) *
          (α - ε - Fintype.card I * Real.exp (-p) - ρ) ≤ μ.mass G ∧
        ∀ z ∈ G, A ⊆ S z (j z) ∧
          2 * (1 - (A.card : ℝ) / (S z (j z)).card) ≤ Fintype.card I * Real.exp (-p) ∧
          ρ ≤ ‖𝔼 t ∈ A, v (F z t) * w z (j z) t‖ := by
  obtain ⟨C, hcount, hshape, hcover⟩ := exists_finite_site_box_inner_family e he hp N
  have hS (z) (j) : (S z j).Nonempty := Finset.image_nonempty.mp (hslice z j).nonempty
  have hsize (z) (j) : (Fintype.card T : ℝ) / (S z j).card ≤ Fintype.card T :=
    div_le_self (Nat.cast_nonneg _) (by exact_mod_cast (hS z j).card_pos)
  obtain ⟨A, hAC, hAn, G, j, hmass, hlocal⟩ := exists_common_inner_sampled_slice μ F S w
    hS hsize hw v hv C hε hρ hlarge (fun z j => hcover (S z j) (hslice z j)) hmean
  refine ⟨A, hAn, hshape A hAC hAn, G, j, ?_, hlocal⟩
  have hcard : (0 : ℝ) < C.card := by exact_mod_cast C.card_pos.mpr ⟨A, hAC⟩
  have hfrac := div_le_div_of_nonneg_left
    (show 0 ≤ α - ε - Fintype.card I * Real.exp (-p) - ρ by linarith) hcard hcount
  have h := hfrac.trans hmass
  simpa only [div_eq_mul_inv, ← Real.exp_neg, mul_comm] using h

end Erdos3

end

end OAI
