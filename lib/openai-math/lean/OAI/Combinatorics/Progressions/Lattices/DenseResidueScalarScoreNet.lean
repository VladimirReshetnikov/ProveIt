/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.DenseProductCardDeficit
import OAI.Combinatorics.Progressions.Estimates.RelativeChildSliceGeometry
import OAI.Combinatorics.Progressions.Lattices.DenseResidueMeshExponentialBudget
import OAI.Combinatorics.Progressions.Sampling.RelativeSliceScalarMeshScore

namespace OAI

section

namespace Erdos3

abbrev DenseResidueSliceNetCode (X : Type*) (Q K : ℕ) :=
  Fin (Q + 1) × (X → Fin (Q + 1)) × (X → Fin (K + 1)) × (X → Fin (K + 1))

namespace DenseResidueSliceNetCode

variable {X : Type*} {Q K : ℕ}

def stride (c : DenseResidueSliceNetCode X Q K) : ℕ := c.1.val

def start (M : ℕ) (c : DenseResidueSliceNetCode X Q K) (i : X) : ℕ :=
  (c.2.1 i).val + c.stride * (M * (c.2.2.1 i).val)

def length (M : ℕ) (c : DenseResidueSliceNetCode X Q K) (i : X) : ℕ :=
  M * (c.2.2.2 i).val - M * (c.2.2.1 i).val

def Valid (N : X → ℕ) (H : ℝ) (M : ℕ) (c : DenseResidueSliceNetCode X Q K) : Prop :=
  0 < c.stride ∧
    (∀ i j, j < c.length M i → c.start M i + c.stride * j < N i) ∧
    ∀ i, H / 2 ≤ (c.length M i : ℝ)

def fullParent (N : X → ℕ) : ResidueBoxSlice N 1 where
  start _ := 0
  length := N
  inside i j hj := by simpa using hj

noncomputable def realize (N : X → ℕ) (H : ℝ) (M : ℕ)
    (c : DenseResidueSliceNetCode X Q K) : Σ q, ResidueBoxSlice N q := by
  classical
  exact if h : c.Valid N H M then
    ⟨c.stride, ⟨c.start M, c.length M, h.2.1⟩⟩ else ⟨1, fullParent N⟩

theorem realize_spec (N : X → ℕ) (H : ℝ) (M : ℕ)
    (hH : 0 < H) (hN : ∀ i, H ≤ (N i : ℝ)) (hQ : 1 ≤ Q)
    (c : DenseResidueSliceNetCode X Q K) :
    0 < (c.realize N H M).1 ∧ (c.realize N H M).1 ≤ Q ∧
      ∀ i, H / 2 ≤ ((c.realize N H M).2.length i : ℝ) := by
  classical
  let P (z : Σ q, ResidueBoxSlice N q) : Prop :=
    0 < z.1 ∧ z.1 ≤ Q ∧ ∀ i, H / 2 ≤ (z.2.length i : ℝ)
  change P (c.realize N H M)
  unfold realize
  split_ifs with hc
  · exact ⟨hc.1, Nat.le_of_lt_succ c.1.isLt, hc.2.2⟩
  · refine ⟨by norm_num, hQ, ?_⟩
    intro i
    change H / 2 ≤ (N i : ℝ)
    linarith [hN i]

theorem card [Fintype X] [DecidableEq X] (Q K : ℕ) :
    Fintype.card (DenseResidueSliceNetCode X Q K) =
      (Q + 1) * ((Q + 1) * (K + 1) ^ 2) ^ Fintype.card X := by
  simp only [DenseResidueSliceNetCode, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  rw [mul_pow, ← pow_mul, Nat.mul_comm 2 _, pow_mul]
  ring

def meshCode {N : X → ℕ} {q : ℕ} (S : ResidueBoxSlice N q)
    (hq : 0 < q) (hqQ : q ≤ Q) (M : ℕ) (hM : 0 < M)
    (hlen : ∀ i, 2 * M < S.length i) (hbox : ∀ i, N i ≤ K * M) :
    DenseResidueSliceNetCode X Q K :=
  ⟨⟨q, Nat.lt_succ_of_le hqQ⟩,
    (fun i => ⟨S.start i % q, (Nat.mod_lt _ hq).trans_le (Nat.le_succ_of_le hqQ)⟩),
    (fun i => ⟨S.start i / q / M + 1, Nat.lt_succ_of_le
      ((denseResidueMeshInterval_code_bound (S.start i / q) (S.length i) M K hM (hlen i)
        ((S.residueIndex_endpoint_le hq (fun j => by have := hlen j; omega) i).trans
          (hbox i))).1)⟩),
    (fun i => ⟨(S.start i / q + S.length i) / M, Nat.lt_succ_of_le
      ((denseResidueMeshInterval_code_bound (S.start i / q) (S.length i) M K hM (hlen i)
        ((S.residueIndex_endpoint_le hq (fun j => by have := hlen j; omega) i).trans
          (hbox i))).2)⟩)⟩

theorem meshCode_valid {N : X → ℕ} {q : ℕ} (S : ResidueBoxSlice N q)
    (hq : 0 < q) (hqQ : q ≤ Q) (M : ℕ) (hM : 0 < M)
    (hlen : ∀ i, 2 * M < S.length i) (hbox : ∀ i, N i ≤ K * M)
    (H : ℝ) (h4 : (4 * M : ℕ) ≤ H) (hH : ∀ i, H ≤ (S.length i : ℝ)) :
    (meshCode S hq hqQ M hM hlen hbox).Valid N H M := by
  refine ⟨hq, ?_, ?_⟩
  · exact (S.meshRounded hq M hM hlen).inside
  · intro i
    change H / 2 ≤ ((S.meshRounded hq M hM hlen).length i : ℝ)
    obtain ⟨offset, _, hcontained, hloss⟩ := S.meshRounded_contained hq M hM hlen
    have hi : S.length i ≤ (S.meshRounded hq M hM hlen).length i + 2 * M := by
      have := hcontained i
      have := hloss i
      omega
    have hiR : (S.length i : ℝ) ≤ (S.meshRounded hq M hM hlen).length i + 2 * (M : ℝ) := by
      exact_mod_cast hi
    have h4R : 4 * (M : ℝ) ≤ H := by exact_mod_cast h4
    linarith [hH i]

theorem realize_meshCode {N : X → ℕ} {q : ℕ} (S : ResidueBoxSlice N q)
    (hq : 0 < q) (hqQ : q ≤ Q) (M : ℕ) (hM : 0 < M)
    (hlen : ∀ i, 2 * M < S.length i) (hbox : ∀ i, N i ≤ K * M)
    (H : ℝ) (h4 : (4 * M : ℕ) ≤ H) (hH : ∀ i, H ≤ (S.length i : ℝ)) :
    (meshCode S hq hqQ M hM hlen hbox).realize N H M =
      ⟨q, S.meshRounded hq M hM hlen⟩ := by
  classical
  rw [realize, dite_eq_left (meshCode_valid S hq hqQ M hM hlen hbox H h4 hH)]
  rfl

theorem exists_realize_meshRounded {N : X → ℕ} {q : ℕ} (S : ResidueBoxSlice N q)
    (hq : 0 < q) (hqQ : q ≤ Q) (M : ℕ) (hM : 0 < M)
    (hbox : ∀ i, N i ≤ K * M) (H : ℝ) (h4 : (4 * M : ℕ) ≤ H)
    (hH : ∀ i, H ≤ (S.length i : ℝ)) :
    ∃ (hlen : ∀ i, 2 * M < S.length i) (c : DenseResidueSliceNetCode X Q K),
      c.realize N H M = ⟨q, S.meshRounded hq M hM hlen⟩ := by
  have hlen (i : X) : 2 * M < S.length i := by
    have h4R : 4 * (M : ℝ) ≤ H := by exact_mod_cast h4
    have hMR : (0 : ℝ) < M := by exact_mod_cast hM
    have hi : 2 * (M : ℝ) < S.length i := by linarith [hH i]
    exact_mod_cast hi
  exact ⟨hlen, meshCode S hq hqQ M hM hlen hbox,
    realize_meshCode S hq hqQ M hM hlen hbox H h4 hH⟩

end DenseResidueSliceNetCode
end Erdos3

end

section

namespace Erdos3

private theorem denseResidueCode_card_exp_bound (n Q K : ℕ) (T : ℝ)
    (hQ : ((Q + 1 : ℕ) : ℝ) ≤ Real.exp T)
    (hK : ((K + 1 : ℕ) : ℝ) ≤ Real.exp T) :
    (Fintype.card (DenseResidueSliceNetCode (Fin n) Q K) : ℝ) ≤
      Real.exp (((1 + 3 * n : ℕ) : ℝ) * T) := by
  rw [DenseResidueSliceNetCode.card, Fintype.card_fin]
  push_cast
  calc
    (Q + 1 : ℝ) * ((Q + 1 : ℝ) * (K + 1 : ℝ) ^ 2) ^ n ≤
        Real.exp T * (Real.exp T * (Real.exp T) ^ 2) ^ n := by
      push_cast at hQ hK
      gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      push_cast
      ring

theorem exists_denseResidueScalarNet_power_budget (n : ℕ) {C : ℝ} (hC : 1 ≤ C) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ (b δ ε : ℝ), 0 ≤ b →
      Real.exp (-b) ≤ δ → δ ≤ 1 → Real.exp (-b) ≤ ε → ε ≤ 1 →
      let Q := ⌈2 / δ⌉₊
      let K := denseResidueMeshCap n δ ε C
      Real.log (Fintype.card (DenseResidueSliceNetCode (Fin n) Q K) : ℝ) ≤ (b + 2) ^ E ∧
      (Fintype.card (DenseResidueSliceNetCode (Fin n) Q K) : ℝ) ≤ Real.exp ((b + 2) ^ E) ∧
      ((Q + 1 : ℕ) : ℝ) ≤ Real.exp ((b + 2) ^ E) ∧
      ((K + 1 : ℕ) : ℝ) ≤ Real.exp ((b + 2) ^ E) ∧
      16 * ((n : ℝ) + 1) / (ε * δ) ≤ Real.exp ((b + 2) ^ E) ∧
      (δ / 2)⁻¹ ≤ Real.exp ((b + 2) ^ E) ∧
      2 * C ≤ Real.exp ((b + 2) ^ E) ∧
      4 * C / δ ≤ Real.exp ((b + 2) ^ E) ∧
      (∀ L : ℝ, Real.exp ((b + 2) ^ E) ≤ L → 4 ≤ δ * L) ∧
      ∀ ρ : ℝ, Real.exp (-b) ≤ ρ →
        Real.log (2 * (Fintype.card (DenseResidueSliceNetCode (Fin n) Q K) : ℝ) / ρ) ≤
          (b + 2) ^ E := by
  obtain ⟨A, _, hmesh⟩ := exists_denseResidueMesh_exponential_budget n hC
  let P : Polynomial ℕ := Polynomial.C (1 + 3 * n) *
    (Polynomial.C A + 2 * Polynomial.X) + Polynomial.X + 2
  obtain ⟨E, hE, hP⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨E, hE, ?_⟩
  intro b δ ε hb hδ hδ1 hε hε1 Q K
  obtain ⟨hQ, hK, hL⟩ := hmesh b δ ε hb hδ hδ1 hε hε1
  let T := (A : ℝ) + 2 * b
  let U := ((1 + 3 * n : ℕ) : ℝ) * T
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hTU : T ≤ U := by
    dsimp only [U]
    exact le_mul_of_one_le_left hT (by exact_mod_cast (show 1 ≤ 1 + 3 * n by omega))
  have hcost : U + b + 2 ≤ (b + 2) ^ E := by
    simpa [P, U, T] using hP b hb
  have hUcost : U ≤ (b + 2) ^ E := by linarith
  have hTcost := hTU.trans hUcost
  have hcard : (Fintype.card (DenseResidueSliceNetCode (Fin n) Q K) : ℝ) ≤ Real.exp U :=
    denseResidueCode_card_exp_bound n Q K T hQ hK
  have hcardpos : 0 < (Fintype.card (DenseResidueSliceNetCode (Fin n) Q K) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (DenseResidueSliceNetCode (Fin n) Q K))
  have hcardFinal := hcard.trans (Real.exp_le_exp.mpr hUcost)
  have hQFinal := hQ.trans (Real.exp_le_exp.mpr hTcost)
  have hKFinal := hK.trans (Real.exp_le_exp.mpr hTcost)
  have hLFinal := hL.trans (Real.exp_le_exp.mpr hTcost)
  have hδpos := (Real.exp_pos (-b)).trans_le hδ
  have hεpos := (Real.exp_pos (-b)).trans_le hε
  have hC0 : 0 ≤ C := by linarith
  have hhalf : (δ / 2)⁻¹ ≤ Real.exp ((b + 2) ^ E) := by
    rw [inv_div]
    exact (Nat.le_ceil (2 / δ)).trans
      ((by exact_mod_cast Nat.le_succ Q : (Q : ℝ) ≤ (Q + 1 : ℕ)).trans hQFinal)
  have hfour : 4 * C / δ ≤ Real.exp ((b + 2) ^ E) := by
    have harg : 16 * ((n : ℝ) + 1) * C / (ε * δ) ≤ ((K + 1 : ℕ) : ℝ) := by
      have hceil := Nat.le_ceil (16 * ((n : ℝ) + 1) * C / (ε * δ))
      dsimp only [K, denseResidueMeshCap]
      push_cast
      linarith
    apply (le_trans ?_ harg).trans hKFinal
    calc
      4 * C / δ ≤ 4 * C / (ε * δ) :=
        div_le_div_of_nonneg_left (by positivity) (mul_pos hεpos hδpos)
          (mul_le_of_le_one_left hδpos.le hε1)
      _ ≤ 16 * ((n : ℝ) + 1) * C / (ε * δ) := by
        apply div_le_div_of_nonneg_right _ (mul_nonneg hεpos.le hδpos.le)
        nlinarith [Nat.cast_nonneg (α := ℝ) n, mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hC0]
  have htwo : 2 * C ≤ Real.exp ((b + 2) ^ E) := by
    apply (le_trans ?_ hfour)
    apply (le_div_iff₀ hδpos).mpr
    nlinarith [mul_le_mul_of_nonneg_left hδ1 (by positivity : 0 ≤ 2 * C)]
  have hlarge (L : ℝ) (hLL : Real.exp ((b + 2) ^ E) ≤ L) : 4 ≤ δ * L := by
    have hbound := (div_le_iff₀ (mul_pos hεpos hδpos)).mp (hLFinal.trans hLL)
    have hLpos := (Real.exp_pos _).trans_le hLL
    have hεL := mul_le_of_le_one_left (mul_nonneg hδpos.le hLpos.le) hε1
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  refine ⟨(Real.log_le_iff_le_exp hcardpos).mpr hcardFinal, hcardFinal,
    hQFinal, hKFinal, hLFinal, hhalf, htwo, hfour, hlarge, ?_⟩
  intro ρ hρ
  have hρpos := (Real.exp_pos (-b)).trans_le hρ
  have hinv : ρ⁻¹ ≤ Real.exp b := by
    apply (inv_le_iff_one_le_mul₀' hρpos).mpr
    calc
      1 = Real.exp (-b) * Real.exp b := by rw [← Real.exp_add]; simp
      _ ≤ ρ * Real.exp b := mul_le_mul_of_nonneg_right hρ (Real.exp_nonneg _)
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  calc
    2 * (Fintype.card (DenseResidueSliceNetCode (Fin n) Q K) : ℝ) / ρ ≤
        Real.exp 2 * Real.exp U * Real.exp b := by
      rw [div_eq_mul_inv]
      gcongr
      linarith [Real.add_one_le_exp (2 : ℝ)]
    _ = Real.exp (U + b + 2) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp ((b + 2) ^ E) := Real.exp_le_exp.mpr hcost

end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {X : Type*} [Fintype X] [DecidableEq X] {N : X → ℕ} {q : ℕ}

noncomputable def fullSliceSupport (S : ResidueBoxSlice N q) : Finset (integerBox N) :=
  Finset.univ.image S.fullSlicePointInIntegerBox

theorem fullSlicePointInIntegerBox_injective (S : ResidueBoxSlice N q) (hq : 0 < q) :
    Function.Injective S.fullSlicePointInIntegerBox := by
  intro u v he
  funext i
  apply Fin.ext
  have hi := congrArg (fun x : integerBox N => x.val i) he
  change ((S.start i + q * (u i).val : ℕ) : ℤ) =
    ((S.start i + q * (v i).val : ℕ) : ℤ) at hi
  have hi' : S.start i + q * (u i).val = S.start i + q * (v i).val := by
    exact_mod_cast hi
  exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_left_cancel hi')

theorem fullSliceSupport_card (S : ResidueBoxSlice N q) (hq : 0 < q) :
    S.fullSliceSupport.card = ∏ i, S.length i := by
  rw [fullSliceSupport, Finset.card_image_of_injective _
    (fullSlicePointInIntegerBox_injective S hq)]
  simp only [Finset.card_univ, Fintype.card_pi, Fintype.card_fin]

theorem fullSliceSupport_nonempty (S : ResidueBoxSlice N q)
    (hlen : ∀ i, 0 < S.length i) : S.fullSliceSupport.Nonempty := by
  let u : ∀ i, Fin (S.length i) := fun i => ⟨0, hlen i⟩
  exact ⟨S.fullSlicePointInIntegerBox u, Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩⟩

theorem fullSliceLaw_mean_eq_support (S : ResidueBoxSlice N q)
    (hlen : ∀ i, 0 < S.length i) (hq : 0 < q) (f : integerBox N → ℝ) :
    (S.fullSliceLaw hlen).mean f = 𝔼 x ∈ S.fullSliceSupport, f x := by
  rw [fullSliceLaw_mean, fullSliceSupport,
    Finset.expect_image (fullSlicePointInIntegerBox_injective S hq).injOn]

theorem fullSliceSupport_subset (S T : ResidueBoxSlice N q) (offset : X → ℕ)
    (hstart : ∀ i, T.start i = S.start i + q * offset i)
    (hlength : ∀ i, offset i + T.length i ≤ S.length i) :
    T.fullSliceSupport ⊆ S.fullSliceSupport := by
  intro x hx
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
  let v : ∀ i, Fin (S.length i) := fun i =>
    ⟨offset i + (u i).val, by have := (u i).isLt; have := hlength i; omega⟩
  apply Finset.mem_image.mpr
  refine ⟨v, Finset.mem_univ _, ?_⟩
  apply Subtype.ext
  funext i
  simp only [fullSlicePointInIntegerBox, point, v, hstart, Nat.mul_add, Nat.add_assoc]

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {X : Type*} [Fintype X] [DecidableEq X] {N : X → ℕ} {q : ℕ}

theorem fullSliceLaw_mean_sub_le_of_coordinate_deficit
    (S T : ResidueBoxSlice N q) (hq : 0 < q)
    (hlenS : ∀ i, 0 < S.length i) (hlenT : ∀ i, 0 < T.length i)
    (offset : X → ℕ) (hstart : ∀ i, T.start i = S.start i + q * offset i)
    (hlength : ∀ i, offset i + T.length i ≤ S.length i)
    (η : ℝ) (hdeficit : ∀ i,
      ((S.length i - T.length i : ℕ) : ℝ) / (S.length i : ℝ) ≤ η)
    (f : integerBox N → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    |(S.fullSliceLaw hlenS).mean f - (T.fullSliceLaw hlenT).mean f| ≤
      2 * (Fintype.card X : ℝ) * η := by
  have hsub := fullSliceSupport_subset S T offset hstart hlength
  have hcard := Finset.card_le_card hsub
  have hcardpos : (0 : ℝ) < S.fullSliceSupport.card := by
    exact_mod_cast (fullSliceSupport_nonempty S hlenS).card_pos
  have hside (i) : T.length i ≤ S.length i := by have := hlength i; omega
  have hproduct := denseProductNatCardDeficit_le_card_mul S.length T.length
    hlenS hside η hdeficit
  have hratio : ((S.fullSliceSupport.card - T.fullSliceSupport.card : ℕ) : ℝ) /
      (S.fullSliceSupport.card : ℝ) ≤ (Fintype.card X : ℝ) * η := by
    rw [Nat.cast_sub hcard, sub_div, div_self (ne_of_gt hcardpos)]
    simpa only [fullSliceSupport_card S hq, fullSliceSupport_card T hq] using hproduct
  rw [fullSliceLaw_mean_eq_support S hlenS hq, fullSliceLaw_mean_eq_support T hlenT hq]
  have hmean := abs_expect_parent_sub_subset_le_abs S.fullSliceSupport T.fullSliceSupport
    (fullSliceSupport_nonempty T hlenT) hsub f (fun x _ => hf x)
  exact hmean.trans (by
    simpa only [mul_div_assoc, mul_assoc] using mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 2))

theorem fullSliceLaw_mean_sub_le_of_length_loss
    (S T : ResidueBoxSlice N q) (hq : 0 < q)
    (hlenS : ∀ i, 0 < S.length i) (hlenT : ∀ i, 0 < T.length i)
    (offset : X → ℕ) (hstart : ∀ i, T.start i = S.start i + q * offset i)
    (hlength : ∀ i, offset i + T.length i ≤ S.length i)
    {H M : ℝ} (hH : 0 < H) (hM : 0 ≤ M)
    (hLower : ∀ i, H ≤ (S.length i : ℝ))
    (hLoss : ∀ i, ((S.length i - T.length i : ℕ) : ℝ) ≤ 2 * M)
    (f : integerBox N → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    |(S.fullSliceLaw hlenS).mean f - (T.fullSliceLaw hlenT).mean f| ≤
      4 * (Fintype.card X : ℝ) * M / H := by
  have hdeficit (i) : ((S.length i - T.length i : ℕ) : ℝ) / (S.length i : ℝ) ≤
      2 * M / H := by
    exact (div_le_div_of_nonneg_right (hLoss i) (Nat.cast_nonneg _)).trans
      (div_le_div_of_nonneg_left (by positivity) hH (hLower i))
  have h := fullSliceLaw_mean_sub_le_of_coordinate_deficit S T hq hlenS hlenT
    offset hstart hlength (2 * M / H) hdeficit f hf
  convert h using 1
  ring

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem fullSliceLaw_sigma_congr
    {X : Type*} [Fintype X] [DecidableEq X] {N : X → ℕ}
    (S T : Σ q, ResidueBoxSlice N q) (h : S = T)
    (hS : ∀ i, 0 < S.2.length i) (hT : ∀ i, 0 < T.2.length i) :
    S.2.fullSliceLaw hS = T.2.fullSliceLaw hT := by
  cases h
  rfl

theorem exists_denseResidueSliceLaw_net
    (X : Type*) [Fintype X] [DecidableEq X]
    {δ ε C : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hC : 1 ≤ C) :
    let Q := ⌈2 / δ⌉₊
    let K := denseResidueMeshCap (Fintype.card X) δ ε C
    ∀ L : ℝ, 16 * ((Fintype.card X : ℝ) + 1) / (ε * δ) ≤ L →
    ∀ N : X → ℕ, (∀ i, L ≤ (N i : ℝ) ∧ (N i : ℝ) ≤ C * L) →
    ∃ (stride : DenseResidueSliceNetCode X Q K → ℕ)
      (slices : ∀ c, ResidueBoxSlice N (stride c))
      (hlen : ∀ c i, 0 < (slices c).length i),
      (∀ c, 0 < stride c ∧ stride c ≤ Q) ∧
      (∀ c i, δ * L / 2 ≤ ((slices c).length i : ℝ)) ∧
      ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ 2 / δ →
      ∀ (S : ResidueBoxSlice N q) (hS : ∀ i, 0 < S.length i),
        (∀ i, δ * (N i : ℝ) ≤ (S.length i : ℝ)) →
      ∃ c : DenseResidueSliceNetCode X Q K,
        ∀ (f : integerBox N → ℝ), (∀ x, |f x| ≤ 1) →
          |(S.fullSliceLaw hS).mean f - ((slices c).fullSliceLaw (hlen c)).mean f| ≤ ε / 2 := by
  intro Q K L hL N hN
  have hLpos : 0 < L :=
    (div_pos (by positivity) (mul_pos hε hδ)).trans_le hL
  have hH : 0 < δ * L := mul_pos hδ hLpos
  have hNlower : ∀ i, δ * L ≤ (N i : ℝ) :=
    fun i => (mul_le_of_le_one_left hLpos.le hδ₁).trans (hN i).1
  have hQ : 1 ≤ Q := by
    apply Nat.one_le_iff_ne_zero.mpr
    exact ne_of_gt (Nat.ceil_pos.mpr (div_pos (by norm_num) hδ))
  let M := denseResidueMeshStep (Fintype.card X) δ ε L
  obtain ⟨hM, hcover, herror, htrim, hfour⟩ :=
    denseResidueMesh_budget (Fintype.card X) hδ hε hε₁ hC hL
  have hbox : ∀ i, N i ≤ K * M := by
    intro i
    exact_mod_cast (hN i).2.trans hcover
  have hfour' : ((4 * M : ℕ) : ℝ) ≤ δ * L := by exact_mod_cast hfour
  let family (c : DenseResidueSliceNetCode X Q K) := c.realize N (δ * L) M
  have hspec (c : DenseResidueSliceNetCode X Q K) :=
    c.realize_spec N (δ * L) M hH hNlower hQ
  have hlen (c : DenseResidueSliceNetCode X Q K) (i : X) :
      0 < (family c).2.length i := by
    exact_mod_cast (half_pos hH).trans_le ((hspec c).2.2 i)
  refine ⟨fun c => (family c).1, fun c => (family c).2, hlen,
    (fun c => ⟨(hspec c).1, (hspec c).2.1⟩), (fun c => (hspec c).2.2), ?_⟩
  intro q hq hqbound S hS hdense
  have hqQ : q ≤ Q := by
    exact_mod_cast hqbound.trans (Nat.le_ceil (2 / δ))
  have hSlower : ∀ i, δ * L ≤ (S.length i : ℝ) :=
    fun i => (mul_le_mul_of_nonneg_left (hN i).1 hδ.le).trans (hdense i)
  obtain ⟨hround, c, hc⟩ :=
    DenseResidueSliceNetCode.exists_realize_meshRounded S hq hqQ M hM hbox (δ * L)
      hfour' hSlower
  refine ⟨c, ?_⟩
  intro f hf
  obtain ⟨offset, hstart, hlength, hloss⟩ := S.meshRounded_contained hq M hM hround
  have hcompare := S.fullSliceLaw_mean_sub_le_of_length_loss
    (S.meshRounded hq M hM hround) hq hS (S.meshRounded_length_pos hq M hM hround)
    offset hstart hlength hH (Nat.cast_nonneg M) hSlower
    (fun i => by exact_mod_cast hloss i) f hf
  have herr := hcompare.trans herror
  have hlaw := fullSliceLaw_sigma_congr (family c)
    ⟨q, S.meshRounded hq M hM hround⟩ hc (hlen c)
    (S.meshRounded_length_pos hq M hM hround)
  rw [hlaw]
  exact herr

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem exists_denseResidueScalarScore_net
    (J : Type*) [Fintype J] [DecidableEq J] [Nonempty J]
    {density accuracy ratio : ℝ} (hdensity : 0 < density) (hdensity₁ : density ≤ 1)
    (haccuracy : 0 < accuracy) (haccuracy₁ : accuracy ≤ 1) (hratio : 1 ≤ ratio) :
    let Q := ⌈2 / density⌉₊
    let K := denseResidueMeshCap (Fintype.card J) density accuracy ratio
    ∀ L : ℝ, 16 * ((Fintype.card J : ℝ) + 1) / (accuracy * density) ≤ L →
    ∀ N : J → ℕ, (∀ i, L ≤ (N i : ℝ) ∧ (N i : ℝ) ≤ ratio * L) →
    ∃ (stride : DenseResidueSliceNetCode J Q K → ℕ)
      (slices : ∀ c, ResidueBoxSlice N (stride c))
      (hlen : ∀ c i, 0 < (slices c).length i),
      (∀ c, 0 < stride c ∧ stride c ≤ Q) ∧
      (∀ c i, density * L / 2 ≤ ((slices c).length i : ℝ)) ∧
      ∀ {X : Type*} [Fintype X] {s d : ℕ} (P : PolynomialPatch X s d)
        (f : (X → ℤ) → ℝ) (parent : X → ℤ) (H : X → ℕ)
        (frame : Option J × X → ℤ),
      (∀ u : integerBox N, smoothAffineSample u.val frame ∈ translatedIntegerBox parent H) →
      (∀ x ∈ translatedIntegerBox parent H, f x ∈ Set.Icc (0 : ℝ) 1) →
      ∀ {τ Λ gain : ℝ}, 0 < τ → τ ≤ 1 / 2 → Λ ∈ Set.Icc (0 : ℝ) 1 →
      ∀ (q : ℕ), 0 < q → ∀ (original : ResidueBoxSlice N q)
        (hOriginal : ∀ j, 0 < original.length j),
      (∀ j, density * (N j : ℝ) ≤ original.length j) →
      gain ≤ (original.fullSliceLaw hOriginal).mean (fun u =>
        (f (smoothAffineSample u.val frame) - Λ) *
          P.value (fun i => (smoothAffineSample u.val frame i : ℝ))) →
      ∃ c, gain - accuracy / 2 ≤ rectangularScalarDiscrepancy parent H
        (fun x => ((f x * P.value (fun i => (x i : ℝ)) : ℝ) : ℂ))
        (fun x => (P.value (fun i => (x i : ℝ)) : ℂ))
        (relativeScalarPassageSlack τ) ((1 - τ) * Λ) (stride c)
        (fun j => ((slices c).start j : ℤ)) 0 (fun j => ((slices c).length j : ℤ))
        (fun j => by change (0 : ℤ) < ((slices c).length j : ℤ); exact_mod_cast hlen c j)
        frame := by
  intro Q K L hL N hN
  obtain ⟨stride, slices, hlen, hstride, hlength, hnet⟩ :=
    exists_denseResidueSliceLaw_net J hdensity hdensity₁ haccuracy haccuracy₁ hratio L hL N hN
  refine ⟨stride, slices, hlen, hstride, hlength, ?_⟩
  intro X _ s d P f parent H frame hinside hf τ Λ gain hτ hτhalf hΛ
    q hq original hOriginal hdense hscore
  have hLpos : 0 < L :=
    (div_pos (by positivity) (mul_pos haccuracy hdensity)).trans_le hL
  have hprod := (div_le_iff₀ (mul_pos haccuracy hdensity)).mp hL
  have hacc : L * (accuracy * density) ≤ L * density := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left hdensity.le haccuracy₁) hLpos.le
  have htwo : 2 ≤ density * L := by
    have hn : (0 : ℝ) ≤ Fintype.card J := Nat.cast_nonneg _
    nlinarith
  let j := Classical.choice (inferInstance : Nonempty J)
  have hlenj : 2 ≤ original.length j := by
    exact_mod_cast htwo.trans
      ((mul_le_mul_of_nonneg_left (hN j).1 hdensity.le).trans (hdense j))
  have hqbound : (q : ℝ) ≤ 2 / density :=
    (original.stride_lt_two_div_density hq hlenj hdensity (hdense j)).le
  obtain ⟨c, hc⟩ := hnet q hq hqbound original hOriginal hdense
  exact ⟨c, relativeSlice_scalar_mesh_score original hOriginal (slices c) (hlen c)
    P f parent H frame hinside hf hτ hτhalf hΛ hscore hc⟩

end Erdos3

end

end OAI
