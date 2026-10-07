import GowersSzemeredi.Proofs07BalogSzemeredi
import GowersSzemeredi.Proofs07FreimanGAP
import OAI.Combinatorics.Progressions.Lattices.FreimanAffineBox

/-!
# Theorems 7.1 and 7.2: Freiman's theorem and the Balog–Szemerédi theorem

Gowers quotes both theorems without proof. They are proved here from the
vendored subset of the openai/math Lean library (`lib/openai-math`, Apache-2.0;
see its README), which supplies

* `exists_dense_cyclic_model` and `exists_dense_cyclic_model_of_integer_vectors`:
  a set with small difference set has a large subset that is Freiman
  isomorphic of order eight to a dense subset of a cyclic group;
* `exists_bounded_affine_box_of_cyclic_model`: a Croot–Sisask/Sanders-type
  Bogolyubov argument then puts a large subset into `base + Φ(box)` for an
  additive map `Φ` from a symmetric integer box of bounded rank and of size
  at most the modulus.

Theorem 7.1 then follows from Ruzsa's covering lemma (Mathlib): a bounded
number of translates of `F - F` covers `A`, and each translate adds one axis
of length two. Theorem 7.2 follows from the already proved quantitative
Balog–Szemerédi reduction, Proposition 7.3. All constants depend only on the
doubling constant (respectively on `c0`), never on the set or the ambient
dimension, exactly as the catalogue statements require.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise
open Finset

namespace LeanProofs.GowersSzemeredi

namespace FreimanClosure

open OAI.Erdos3.FreimanModel OAI.Erdos3.CyclicCrootSisask

/-- The density parameter `p = log (32 K^16)` of an order-eight dense model. -/
def modelLog (K : ℝ) : ℝ := Real.log (32 * K ^ 16)

/-- The logarithmic size loss of the Bogolyubov box. -/
def boxLoss (K : ℝ) : ℝ := quarticBogolyubovProgressionConstant * (modelLog K + 1) ^ 8

/-- The rank bound of the Bogolyubov box. -/
def rankBound (K : ℝ) : ℝ := 2 + quarticBogolyubovConstant * (modelLog K + 1) ^ 4

theorem modelLog_nonneg {K : ℝ} (hK : 1 ≤ K) : 0 ≤ modelLog K := by
  unfold modelLog
  apply Real.log_nonneg
  have : (1 : ℝ) ≤ K ^ 16 := one_le_pow₀ hK
  linarith

/-- The density conclusion of the dense cyclic model at order eight, in the
form required by the Bogolyubov box. -/
theorem density_of_model {K : ℝ} (hK : 1 ≤ K) {N : ℕ} (hN : 0 < N) (B : Finset (ZMod N))
    (h : (4 * ((8 : ℕ) : ℝ) * K ^ (2 * 8))⁻¹ ≤ (B.card : ℝ) / N) :
    Real.exp (-modelLog K) * N ≤ (B.card : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : (0 : ℝ) < 32 * K ^ 16 := by positivity
  have hexp : Real.exp (-modelLog K) = (32 * K ^ 16)⁻¹ := by
    rw [modelLog, Real.exp_neg, Real.exp_log hpos]
  rw [hexp]
  have h' : (32 * K ^ 16)⁻¹ ≤ (B.card : ℝ) / N := by
    have : (4 * ((8 : ℕ) : ℝ) * K ^ (2 * 8)) = 32 * K ^ 16 := by norm_num
    rw [this] at h
    exact h
  exact (le_div_iff₀ hNpos).mp h'

/-- Inverting the size bound of the Bogolyubov box. -/
theorem card_le_exp_mul {E a b : ℝ} (h : Real.exp (-E) * a ≤ b) : a ≤ Real.exp E * b := by
  have h' := mul_le_mul_of_nonneg_left h (Real.exp_pos E).le
  rwa [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at h'

/-! ## Theorem 7.1 -/

/-- The number of translates in Ruzsa's covering step. -/
def coverBound (K : ℝ) : ℝ := 16 * K * Real.exp (boxLoss K)

/-- The dimension bound in Theorem 7.1. -/
def freimanDim (K : ℝ) : ℕ := ⌊rankBound K⌋₊ + ⌊coverBound K⌋₊

/-- The size constant in Theorem 7.1. -/
def freimanSize (K : ℝ) : ℝ := 2 ^ freimanDim K * (2 * K ^ 16)

theorem freimanSize_pos {K : ℝ} (hK : 1 ≤ K) : 0 < freimanSize K := by
  unfold freimanSize
  have : (0 : ℝ) < K := by linarith
  positivity

/-- Freiman's theorem for a set whose sum and difference sets are both small. -/
theorem hasFreimanCover_of_small {K : ℝ} (hK : 1 ≤ K) (A : Finset ℤ) (hA : A.Nonempty)
    (hdiff : ((A - A).card : ℝ) ≤ K * A.card) (hsum : ((A + A).card : ℝ) ≤ K * A.card) :
    HasFreimanCover A (freimanDim K) (freimanSize K) := by
  classical
  have hK0 : 0 < K := by linarith
  obtain ⟨N, A', B, f, hN, hA'ne, hA'A, hsize, hBne, _hB, _hBcard, hf, hNsize, hdens⟩ :=
    exists_dense_cyclic_model A hA hK0 hdiff 8 (by norm_num)
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨F, hFA', hFne, hFsize, r, R, Φ, base, hr, hprod, _hinj, hFsub⟩ :=
    exists_bounded_affine_box_of_cyclic_model A' hA'ne B hBne f hf (modelLog_nonneg hK)
      (density_of_model hK hN B hdens)
  have hFA : F ⊆ A := hFA'.trans hA'A
  -- Ruzsa covering: `A` is covered by few translates of `F - F`.
  have hcov : ((A + F).card : ℝ) ≤ coverBound K * F.card := by
    have h1 : (A + F).card ≤ (A + A).card :=
      Finset.card_le_card (Finset.add_subset_add_left hFA)
    have h2 : (A.card : ℝ) ≤ 16 * A'.card := by
      have h : A.card ≤ 16 * A'.card := by simpa using hsize
      exact_mod_cast h
    have h3 : (A'.card : ℝ) ≤ Real.exp (boxLoss K) * F.card := card_le_exp_mul hFsize
    calc ((A + F).card : ℝ) ≤ (A + A).card := by exact_mod_cast h1
      _ ≤ K * A.card := hsum
      _ ≤ K * (16 * (Real.exp (boxLoss K) * F.card)) := by
          gcongr
          linarith
      _ = coverBound K * F.card := by unfold coverBound; ring
  obtain ⟨X, _hXA, hXcard, hAX⟩ := Finset.ruzsa_covering_add hFne hcov
  have hXne : X.Nonempty := by
    obtain ⟨a, ha⟩ := hA
    obtain ⟨x, hx, _, _, _⟩ := Finset.mem_add.mp (hAX ha)
    exact ⟨x, hx⟩
  let P₁ := posBoxGAP Φ (fun i => 2 * R i) 0
  let P₂ := finsetGAP X hXne
  refine ⟨P₁.sum P₂, ?_, GeneralizedAP.sum_step_pos (posBoxGAP_pos _ _ _)
    (finsetGAP_pos _ _), ?_, ?_⟩
  · -- dimension
    change r + X.card ≤ freimanDim K
    have hr' : r ≤ ⌊rankBound K⌋₊ := Nat.le_floor hr
    have hX' : X.card ≤ ⌊coverBound K⌋₊ := Nat.le_floor hXcard
    unfold freimanDim
    omega
  · -- formal size
    have hP₁ : P₁.size ≤ 2 ^ r * N := by
      change ∏ i, (2 * (2 * R i) + 1) ≤ 2 ^ r * N
      calc ∏ i, (2 * (2 * R i) + 1) ≤ ∏ i : Fin r, (2 * (2 * R i + 1)) :=
            Finset.prod_le_prod' fun i _ => by omega
        _ = 2 ^ r * ∏ i, (2 * R i + 1) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ 2 ^ r * N := Nat.mul_le_mul_left _ hprod
    have hsizeNat : (P₁.sum P₂).size ≤ 2 ^ (r + X.card) * N := by
      rw [GeneralizedAP.sum_size, finsetGAP_size, pow_add]
      calc P₁.size * 2 ^ X.card ≤ 2 ^ r * N * 2 ^ X.card := Nat.mul_le_mul_right _ hP₁
        _ = 2 ^ r * 2 ^ X.card * N := by ring
    have hdim : r + X.card ≤ freimanDim K := by
      have hr' : r ≤ ⌊rankBound K⌋₊ := Nat.le_floor hr
      have hX' : X.card ≤ ⌊coverBound K⌋₊ := Nat.le_floor hXcard
      unfold freimanDim
      omega
    have hpow : (2 : ℝ) ^ (r + X.card) ≤ 2 ^ freimanDim K :=
      pow_le_pow_right₀ (by norm_num) hdim
    have hN' : (N : ℝ) ≤ 2 * K ^ (2 * 8) * A.card := hNsize
    calc ((P₁.sum P₂).size : ℝ) ≤ (2 : ℝ) ^ (r + X.card) * N := by exact_mod_cast hsizeNat
      _ ≤ 2 ^ freimanDim K * (2 * K ^ (2 * 8) * A.card) :=
          mul_le_mul hpow hN' (by positivity) (by positivity)
      _ = freimanSize K * A.card := by unfold freimanSize; ring
  · -- covering
    intro a ha
    obtain ⟨x, hx, d, hd, rfl⟩ := Finset.mem_add.mp (hAX ha)
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_sub.mp hd
    obtain ⟨xu, hxu, rfl⟩ := hFsub u hu
    obtain ⟨xv, hxv, rfl⟩ := hFsub v hv
    have hz : ∀ i, |(xu - xv) i| ≤ ((2 * R i : ℕ) : ℤ) := by
      intro i
      have h1 := abs_le.mp (hxu i)
      have h2 := abs_le.mp (hxv i)
      rw [abs_le]
      push_cast
      simp only [Pi.sub_apply]
      constructor <;> linarith
    have hmem := GeneralizedAP.add_mem_sum (mem_posBoxGAP Φ (fun i => 2 * R i) 0 (xu - xv) hz)
      (mem_finsetGAP X hXne hx)
    have heq : 0 + Φ (xu - xv) + x = x + (base + Φ xu - (base + Φ xv)) := by
      rw [map_sub]
      abel
    rw [heq] at hmem
    exact hmem

end FreimanClosure

open FreimanClosure in
/-- **Theorem 7.1 (Freiman)**, both forms. -/
theorem theorem_7_1_holds : theorem_7_1 := by
  intro C hC
  set K : ℝ := max 1 (max C (C ^ 2)) with hKdef
  have hK1 : 1 ≤ K := le_max_left _ _
  have hCK : C ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hC2K : C ^ 2 ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨freimanDim K, freimanSize K, freimanSize_pos hK1, fun A hA => ⟨fun hsum => ?_,
    fun hdiff => ?_⟩⟩
  · have hApos : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
    have h1 : ((A - A).card : ℝ) * A.card ≤ ((A + A).card : ℝ) * (A + A).card := by
      exact_mod_cast Finset.ruzsa_triangle_inequality_sub_add_add A A A
    have h2 : ((A + A).card : ℝ) * (A + A).card ≤ (C * A.card) * (C * A.card) :=
      mul_le_mul hsum hsum (by positivity) (by positivity)
    have hdiff : ((A - A).card : ℝ) ≤ K * A.card := by
      have h3 : ((A - A).card : ℝ) * A.card ≤ (C ^ 2 * A.card) * A.card := by nlinarith
      have h4 := le_of_mul_le_mul_right h3 hApos
      nlinarith
    exact hasFreimanCover_of_small hK1 A hA hdiff (hsum.trans (by nlinarith))
  · have hApos : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
    have h1 : ((A + A).card : ℝ) * A.card ≤ ((A - A).card : ℝ) * (A - A).card := by
      exact_mod_cast Finset.ruzsa_triangle_inequality_add_sub_sub A A A
    have h2 : ((A - A).card : ℝ) * (A - A).card ≤ (C * A.card) * (C * A.card) :=
      mul_le_mul hdiff hdiff (by positivity) (by positivity)
    have hsum : ((A + A).card : ℝ) ≤ K * A.card := by
      have h3 : ((A + A).card : ℝ) * A.card ≤ (C ^ 2 * A.card) * A.card := by nlinarith
      have h4 := le_of_mul_le_mul_right h3 hApos
      nlinarith
    exact hasFreimanCover_of_small hK1 A hA (hdiff.trans (by nlinarith)) hsum

/-! ## Theorem 7.2 -/

namespace FreimanClosure

/-- The doubling constant produced by Proposition 7.3 at energy `c0`. -/
def bsDoubling (c0 : ℝ) : ℝ :=
  max 1 (((2 : ℝ) ^ (38 : ℕ) * c0 ^ (-(24 : ℝ))) / ((2 : ℝ) ^ (-(20 : ℝ)) * c0 ^ 12))

theorem one_le_bsDoubling (c0 : ℝ) : 1 ≤ bsDoubling c0 := le_max_left _ _

/-- The density constant in Theorem 7.2. -/
def bsDensity (c0 : ℝ) : ℝ :=
  Real.exp (-boxLoss (bsDoubling c0)) / 16 * ((2 : ℝ) ^ (-(20 : ℝ)) * c0 ^ 12)

/-- The size constant in Theorem 7.2. -/
def bsSize (c0 : ℝ) : ℝ := 2 * bsDoubling c0 ^ 16

end FreimanClosure

open FreimanClosure OAI.Erdos3.FreimanModel in
/-- **Theorem 7.2 (Balog–Szemerédi).** -/
theorem theorem_7_2_holds : theorem_7_2 := by
  intro c0 hc0
  have hK1 := one_le_bsDoubling c0
  have hK0 : 0 < bsDoubling c0 := by linarith
  have ha : 0 < (2 : ℝ) ^ (-(20 : ℝ)) * c0 ^ 12 := by positivity
  refine ⟨bsDensity c0, bsSize c0, ⌊rankBound (bsDoubling c0)⌋₊, by unfold bsDensity; positivity,
    by unfold bsSize; positivity, fun D A hA henergy => ?_⟩
  classical
  have hApos : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  obtain ⟨A'', hA''A, hA''size, hA''diff⟩ := proposition_7_3_holds D A c0 hc0 henergy
  have hA''pos : (0 : ℝ) < A''.card := lt_of_lt_of_le (by positivity) hA''size
  have hA''ne : A''.Nonempty := Finset.card_pos.mp (by exact_mod_cast hA''pos)
  -- the small difference set of `A''`
  have hsmall : ((A'' - A'').card : ℝ) ≤ bsDoubling c0 * A''.card := by
    have hb : 0 < (2 : ℝ) ^ (38 : ℕ) * c0 ^ (-(24 : ℝ)) := by positivity
    have hAle : (A.card : ℝ) ≤ A''.card / ((2 : ℝ) ^ (-(20 : ℝ)) * c0 ^ 12) := by
      rw [le_div_iff₀ ha]
      linarith
    calc ((A'' - A'').card : ℝ) ≤ (2 : ℝ) ^ (38 : ℕ) * c0 ^ (-(24 : ℝ)) * A.card := hA''diff
      _ ≤ (2 : ℝ) ^ (38 : ℕ) * c0 ^ (-(24 : ℝ)) *
            (A''.card / ((2 : ℝ) ^ (-(20 : ℝ)) * c0 ^ 12)) := by gcongr
      _ = ((2 : ℝ) ^ (38 : ℕ) * c0 ^ (-(24 : ℝ))) / ((2 : ℝ) ^ (-(20 : ℝ)) * c0 ^ 12) *
            A''.card := by ring
      _ ≤ bsDoubling c0 * A''.card := by
          gcongr
          exact le_max_right _ _
  obtain ⟨N, J, B, f, hN, hJne, hJA, hJsize, hBne, _hB, _hBcard, hf, hNsize, hdens⟩ :=
    exists_dense_cyclic_model_of_integer_vectors A'' hA''ne hK0 hsmall 8 (by norm_num)
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨F, hFJ, _hFne, hFsize, r, R, Φ, base, hr, hprod, _hinj, hFsub⟩ :=
    exists_bounded_affine_box_of_cyclic_model J hJne B hBne f hf (modelLog_nonneg hK1)
      (density_of_model hK1 hN B hdens)
  refine ⟨boxGAP Φ R base, Nat.le_floor hr, boxGAP_length_pos Φ R base, ?_, ?_⟩
  · -- formal size
    rw [boxGAP_size]
    have hN' : (N : ℝ) ≤ 2 * bsDoubling c0 ^ (2 * 8) * A''.card := hNsize
    have hA''le : (A''.card : ℝ) ≤ A.card := by exact_mod_cast Finset.card_le_card hA''A
    calc ((∏ i, (2 * R i + 1) : ℕ) : ℝ) ≤ N := by exact_mod_cast hprod
      _ ≤ 2 * bsDoubling c0 ^ (2 * 8) * A''.card := hN'
      _ ≤ 2 * bsDoubling c0 ^ (2 * 8) * A.card := by gcongr
      _ = bsSize c0 * A.card := by unfold bsSize; ring
  · -- density of `A` in the progression
    have hFsub' : F ⊆ A ∩ (boxGAP Φ R base).carrier := by
      intro a haF
      refine Finset.mem_inter.mpr ⟨hA''A (hJA (hFJ haF)), ?_⟩
      obtain ⟨x, hx, rfl⟩ := hFsub a haF
      exact mem_boxGAP Φ R base x hx
    have hJ : (A''.card : ℝ) ≤ 16 * J.card := by
      have h : A''.card ≤ 16 * J.card := by simpa using hJsize
      exact_mod_cast h
    calc bsDensity c0 * A.card
        = Real.exp (-boxLoss (bsDoubling c0)) / 16 *
            (((2 : ℝ) ^ (-(20 : ℝ)) * c0 ^ 12) * A.card) := by unfold bsDensity; ring
      _ ≤ Real.exp (-boxLoss (bsDoubling c0)) / 16 * A''.card := by
          gcongr
      _ ≤ Real.exp (-boxLoss (bsDoubling c0)) * J.card := by
          have he := (Real.exp_pos (-boxLoss (bsDoubling c0))).le
          nlinarith
      _ ≤ F.card := hFsize
      _ ≤ ((A ∩ (boxGAP Φ R base).carrier).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hFsub'

end LeanProofs.GowersSzemeredi
