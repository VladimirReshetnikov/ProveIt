import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Topology.Algebra.InfiniteSum.Real
import OAI.Combinatorics.Progressions.Fourier.RationalLiftCharacterTwist
import OAI.Combinatorics.Progressions.Results.Basic

namespace OAI

section

namespace Erdos3

open scoped NNReal

structure TriangularSlots (d : ℕ) where
  center : (Fin d → ℝ) → Fin d → ℝ
  lower : ∀ i x y, (∀ j, j < i → x j = y j) → center x i = center y i

namespace TriangularSlots

variable {d : ℕ}

def residual (A : TriangularSlots d) (b : Fin d → ℤ) : Fin d → ℝ :=
  fun i => (b i : ℝ) - A.center (fun j => (b j : ℝ)) i

theorem integer_unique (A : TriangularSlots d) {b c : Fin d → ℤ} {r t : ℝ}
    (hgap : r + t < 1)
    (hb : ∀ i, |A.residual b i| ≤ r) (hc : ∀ i, |A.residual c i| ≤ t) : b = c := by
  have hall : ∀ n : ℕ, ∀ i : Fin d, i.val = n → b i = c i := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hi
      have hcenter : A.center (fun j => (b j : ℝ)) i = A.center (fun j => (c j : ℝ)) i := by
        apply A.lower
        intro j hj
        have hjn : j.val < n := by simpa only [Fin.lt_def, ← hi] using hj
        rw [ih j.val hjn j rfl]
      have heq : ((b i - c i : ℤ) : ℝ) = A.residual b i - A.residual c i := by
        simp only [residual, Int.cast_sub, hcenter]
        ring
      have habs : |((b i - c i : ℤ) : ℝ)| < 1 := by
        rw [heq]
        exact (abs_sub _ _).trans_lt ((add_le_add (hb i) (hc i)).trans_lt hgap)
      have hl : (-1 : ℤ) < b i - c i := by exact_mod_cast (abs_lt.mp habs).1
      have hr : b i - c i < (1 : ℤ) := by exact_mod_cast (abs_lt.mp habs).2
      omega
  exact funext (fun i => hall i.val i rfl)

end TriangularSlots

structure PatchKernel (d : ℕ) where
  value : (Fin d → ℝ) → ℝ
  nonneg : ∀ x, 0 ≤ value x
  le_one : ∀ x, value x ≤ 1
  support : ∀ x, value x ≠ 0 → ∀ i, |x i| ≤ 1 / 4
  lip : ℝ≥0
  lipschitz : LipschitzWith lip value

namespace TriangularSlots

variable {d : ℕ} (A : TriangularSlots d) (Φ : PatchKernel d)

theorem contributing_unique {b c : Fin d → ℤ}
    (hb : Φ.value (A.residual b) ≠ 0) (hc : Φ.value (A.residual c) ≠ 0) : b = c :=
  A.integer_unique (by norm_num) (Φ.support _ hb) (Φ.support _ hc)

noncomputable def patchValue : ℝ := ∑' b : Fin d → ℤ, Φ.value (A.residual b)

theorem patchValue_eq_of_nonzero {b : Fin d → ℤ} (hb : Φ.value (A.residual b) ≠ 0) :
    A.patchValue Φ = Φ.value (A.residual b) := by
  apply tsum_eq_single b
  intro c hcb
  by_contra hc
  exact hcb (A.contributing_unique Φ hc hb)

theorem patchValue_eq_zero (h : ∀ b : Fin d → ℤ, Φ.value (A.residual b) = 0) :
    A.patchValue Φ = 0 := by
  simp only [patchValue, h, tsum_zero]

theorem patchValue_eq_at_residual {b : Fin d → ℤ}
    (hb : ∀ i, |A.residual b i| ≤ 1 / 4) :
    A.patchValue Φ = Φ.value (A.residual b) := by
  apply tsum_eq_single b
  intro c hcb
  by_contra hc
  exact hcb (A.integer_unique (by norm_num) (Φ.support _ hc) hb)

theorem patchValue_dist_le (Ψ : PatchKernel d) {δ : ℝ} (hδ : 0 ≤ δ)
    (herror : ∀ z, dist (Φ.value z) (Ψ.value z) ≤ δ) :
    dist (A.patchValue Φ) (A.patchValue Ψ) ≤ δ := by
  by_cases h : ∃ b : Fin d → ℤ, Φ.value (A.residual b) ≠ 0 ∨ Ψ.value (A.residual b) ≠ 0
  · obtain ⟨b, hb⟩ := h
    have hres : ∀ i, |A.residual b i| ≤ 1 / 4 := hb.elim (Φ.support _) (Ψ.support _)
    rw [A.patchValue_eq_at_residual Φ hres, A.patchValue_eq_at_residual Ψ hres]
    exact herror _
  · have hΦ : ∀ b, Φ.value (A.residual b) = 0 := by
      intro b
      by_contra hb
      exact h ⟨b, Or.inl hb⟩
    have hΨ : ∀ b, Ψ.value (A.residual b) = 0 := by
      intro b
      by_contra hb
      exact h ⟨b, Or.inr hb⟩
    rw [A.patchValue_eq_zero Φ hΦ, A.patchValue_eq_zero Ψ hΨ, dist_self]
    exact hδ

theorem patchValue_mem_Icc : A.patchValue Φ ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases h : ∃ b : Fin d → ℤ, Φ.value (A.residual b) ≠ 0
  · obtain ⟨b, hb⟩ := h
    rw [A.patchValue_eq_of_nonzero Φ hb]
    exact ⟨Φ.nonneg _, Φ.le_one _⟩
  · have hz : ∀ b : Fin d → ℤ, Φ.value (A.residual b) = 0 := by simpa using h
    rw [A.patchValue_eq_zero Φ hz]
    exact ⟨le_rfl, zero_le_one⟩

end TriangularSlots

end Erdos3

end

section

namespace Erdos3.TriangularSlots

variable {d : ℕ}

theorem patchValue_dist_of_residuals_close (A B : TriangularSlots d) (Φ : PatchKernel d)
    {ε : ℝ} (hε : 0 ≤ ε) (hsmall : ε < 1 / 4)
    (hclose : ∀ b, Φ.value (A.residual b) ≠ 0 ∨ Φ.value (B.residual b) ≠ 0 →
      dist (A.residual b) (B.residual b) ≤ ε) :
    dist (A.patchValue Φ) (B.patchValue Φ) ≤ Φ.lip * ε := by
  have hbound (b) (hb : Φ.value (A.residual b) ≠ 0 ∨ Φ.value (B.residual b) ≠ 0) :
      ∀ i, |A.residual b i| ≤ 1 / 4 + ε := by
    intro i
    rcases hb with hb | hb
    · exact (Φ.support _ hb i).trans (by linarith)
    · have hd := (dist_le_pi_dist (A.residual b) (B.residual b) i).trans
        (hclose b (Or.inr hb))
      rw [Real.dist_eq] at hd
      have htriangle : |A.residual b i| ≤
          |A.residual b i - B.residual b i| + |B.residual b i| := by
        simpa only [sub_add_cancel] using
          abs_add_le (A.residual b i - B.residual b i) (B.residual b i)
      linarith [Φ.support _ hb i]
  by_cases h : ∃ b, Φ.value (A.residual b) ≠ 0 ∨ Φ.value (B.residual b) ≠ 0
  · obtain ⟨b, hb⟩ := h
    have hunique (c) (hc : Φ.value (A.residual c) ≠ 0 ∨ Φ.value (B.residual c) ≠ 0) : c = b :=
      A.integer_unique (by linarith : (1 / 4 + ε) + (1 / 4 + ε) < 1) (hbound c hc) (hbound b hb)
    have hA : A.patchValue Φ = Φ.value (A.residual b) := by
      apply tsum_eq_single b
      intro c hcb
      by_contra hc
      exact hcb (hunique c (Or.inl hc))
    have hB : B.patchValue Φ = Φ.value (B.residual b) := by
      apply tsum_eq_single b
      intro c hcb
      by_contra hc
      exact hcb (hunique c (Or.inr hc))
    rw [hA, hB]
    exact (Φ.lipschitz.dist_le_mul _ _).trans
      (mul_le_mul_of_nonneg_left (hclose b hb) Φ.lip.coe_nonneg)
  · have hA (b) : Φ.value (A.residual b) = 0 := by
      by_contra hb
      exact h ⟨b, Or.inl hb⟩
    have hB (b) : Φ.value (B.residual b) = 0 := by
      by_contra hb
      exact h ⟨b, Or.inr hb⟩
    rw [A.patchValue_eq_zero Φ hA, B.patchValue_eq_zero Φ hB, dist_self]
    exact mul_nonneg Φ.lip.coe_nonneg hε

end Erdos3.TriangularSlots

end

section

namespace Erdos3

variable {D E : ℕ}

def slotPrefix {R : Type*} (x : Fin (D + E) → R) : Fin D → R :=
  fun i => x (i.castAdd E)

def slotSuffix {R : Type*} (x : Fin (D + E) → R) : Fin E → R :=
  fun i => x (i.natAdd D)

@[simp] theorem slotPrefix_append {R : Type*} (b : Fin D → R) (c : Fin E → R) :
    slotPrefix (Fin.append b c) = b := by ext i; simp [slotPrefix]

@[simp] theorem slotSuffix_append {R : Type*} (b : Fin D → R) (c : Fin E → R) :
    slotSuffix (Fin.append b c) = c := by ext i; simp [slotSuffix]

theorem append_slotPrefix_slotSuffix {R : Type*} (x : Fin (D + E) → R) :
    Fin.append (slotPrefix x) (slotSuffix x) = x := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [slotPrefix, slotSuffix]

namespace TriangularSlots

def append (A : TriangularSlots D) (B : (Fin D → ℝ) → TriangularSlots E) :
    TriangularSlots (D + E) where
  center x := Fin.append (A.center (slotPrefix x)) ((B (slotPrefix x)).center (slotSuffix x))
  lower i := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · intro x y hxy
      simp only [Fin.append_left]
      apply A.lower
      intro k hkj
      exact hxy (k.castAdd E) (by simpa only [Fin.lt_def, Fin.val_castAdd] using hkj)
    · intro x y hxy
      simp only [Fin.append_right]
      have hp : slotPrefix x = slotPrefix y := by
        ext k
        exact hxy (k.castAdd E) (by simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]; omega)
      rw [hp]
      apply (B (slotPrefix y)).lower
      intro k hkj
      exact hxy (k.natAdd D) (by simpa only [Fin.lt_def, Fin.val_natAdd, Nat.add_lt_add_iff_left] using hkj)

theorem append_residual (A : TriangularSlots D) (B : (Fin D → ℝ) → TriangularSlots E)
    (b : Fin D → ℤ) (c : Fin E → ℤ) :
    (A.append B).residual (Fin.append b c) =
      Fin.append (A.residual b) ((B (fun i => (b i : ℝ))).residual c) := by
  have hp : slotPrefix (D := D) (E := E) (fun j => ((Fin.append b c j : ℤ) : ℝ)) =
      fun i => (b i : ℝ) := by ext i; simp [slotPrefix]
  have hs : slotSuffix (D := D) (E := E) (fun j => ((Fin.append b c j : ℤ) : ℝ)) =
      fun i => (c i : ℝ) := by ext i; simp [slotSuffix]
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [residual, append, hp, hs]

end TriangularSlots

theorem dist_append_same_left_le (z : Fin D → ℝ) (x y : Fin E → ℝ) :
    dist (Fin.append z x) (Fin.append z y) ≤ dist x y := by
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp
  · simpa only [Fin.append_right] using dist_le_pi_dist x y j

theorem dist_append_same_right_le (x y : Fin D → ℝ) (z : Fin E → ℝ) :
    dist (Fin.append x z) (Fin.append y z) ≤ dist x y := by
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [Fin.append_left] using dist_le_pi_dist x y j
  · simp

namespace PatchKernel

def freeze (Φ : PatchKernel (D + E)) (z : Fin D → ℝ) : PatchKernel E where
  value y := Φ.value (Fin.append z y)
  nonneg y := Φ.nonneg _
  le_one y := Φ.le_one _
  support y hy i := by simpa using Φ.support _ hy (i.natAdd D)
  lip := Φ.lip
  lipschitz := LipschitzWith.of_dist_le_mul (fun x y =>
    (Φ.lipschitz.dist_le_mul _ _).trans
      (mul_le_mul_of_nonneg_left (dist_append_same_left_le z x y) Φ.lip.coe_nonneg))

theorem freeze_value_dist_le (Φ : PatchKernel (D + E)) (x y : Fin D → ℝ)
    (z : Fin E → ℝ) :
    dist ((Φ.freeze x).value z) ((Φ.freeze y).value z) ≤ Φ.lip * dist x y :=
  (Φ.lipschitz.dist_le_mul _ _).trans
    (mul_le_mul_of_nonneg_left (dist_append_same_right_le x y z) Φ.lip.coe_nonneg)

end PatchKernel

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem rationalLiftCharacterTwistLip_le_exp {m : ℕ}
    (M : ℕ) (hM : 0 < M) (a : Fin m → ℤ) (p q : ℝ)
    (hm : (m : ℝ) ≤ Real.exp p) (ha : ∀ i, |(a i : ℝ)| ≤ Real.exp q) :
    (rationalLiftCharacterTwistLip M a : ℝ) ≤ Real.exp (p + q + 8) := by
  have hpi : 2 * Real.pi ≤ Real.exp (8 : ℝ) := by
    linarith [Real.pi_lt_four, Real.add_one_le_exp (8 : ℝ)]
  calc
    _ ≤ 2 * Real.pi * m * Real.exp q := rationalLiftCharacterTwistLip_le M hM a _ ha
    _ ≤ Real.exp 8 * Real.exp p * Real.exp q := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hpi hm (Nat.cast_nonneg m) (Real.exp_nonneg _)) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem rationalLiftCharacterTwistLip_le_exp_of_dim {m : ℕ}
    (M : ℕ) (hM : 0 < M) (a : Fin m → ℤ) (p q : ℝ)
    (hm : (m : ℝ) ≤ p) (ha : ∀ i, |(a i : ℝ)| ≤ Real.exp q) :
    (rationalLiftCharacterTwistLip M a : ℝ) ≤ Real.exp (p + q + 8) :=
  rationalLiftCharacterTwistLip_le_exp M hM a p q
    (hm.trans (by linarith [Real.add_one_le_exp p])) ha

theorem rationalLift_major_product_eq {U : Type*} {m : ℕ}
    (M : ℕ) (hM : 0 < M) (a : Fin m → ℤ) (c : Fin m → ℝ)
    (Ψ : PatchKernel m) (F : MvPolynomial (U ⊕ Fin m) ℝ)
    (A : Fin m → MvPolynomial U ℝ) (x : U → ℤ) (β : Fin m → ℤ)
    (z : ℂ) :
    (Real.fourierChar ((∑ i, (a i : ℝ) *
      (MvPolynomial.eval (fun j => (x j : ℝ)) (A i) + c i)) / (M : ℝ)) : ℂ) *
      (Ψ.value (fun i => MvPolynomial.eval (fun j => (x j : ℝ)) (A i) - (β i : ℝ)) : ℂ) *
      (Real.fourierChar (MvPolynomial.eval
        (fun j => ((Sum.elim x β j : ℤ) : ℝ)) F) : ℂ) * z =
    rationalLiftCharacterTwist M a c
      (fun i => MvPolynomial.eval (fun j => (x j : ℝ)) (A i) - (β i : ℝ))
      (fun i => (β i : ZMod M)) *
      (Ψ.value (fun i => MvPolynomial.eval (fun j => (x j : ℝ)) (A i) - (β i : ℝ)) : ℂ) *
      (Real.fourierChar (MvPolynomial.eval
        (fun j => ((Sum.elim x β j : ℤ) : ℝ)) F) : ℂ) * z := by
  rw [rationalLiftCharacterTwist_residual M hM]

theorem rationalLift_major_mean_eq {U : Type*} {m : ℕ}
    (M : ℕ) (hM : 0 < M) (a : Fin m → ℤ) (c : Fin m → ℝ)
    (S : Finset (U → ℤ)) (Ψ : PatchKernel m) (F : MvPolynomial (U ⊕ Fin m) ℝ)
    (A : Fin m → MvPolynomial U ℝ) (β : (U → ℤ) → Fin m → ℤ)
    (R : (U → ℤ) → ℂ) :
    (𝔼 x ∈ S,
      (Real.fourierChar ((∑ i, (a i : ℝ) *
        (MvPolynomial.eval (fun j => (x j : ℝ)) (A i) + c i)) / (M : ℝ)) : ℂ) *
      (Ψ.value (fun i => MvPolynomial.eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ)) : ℂ) *
      (Real.fourierChar (MvPolynomial.eval
        (fun j => ((Sum.elim x (β x) j : ℤ) : ℝ)) F) : ℂ) * R x) =
    (𝔼 x ∈ S,
      rationalLiftCharacterTwist M a c
        (fun i => MvPolynomial.eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ))
        (fun i => (β x i : ZMod M)) *
      (Ψ.value (fun i => MvPolynomial.eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ)) : ℂ) *
      (Real.fourierChar (MvPolynomial.eval
        (fun j => ((Sum.elim x (β x) j : ℤ) : ℝ)) F) : ℂ) * R x) := by
  apply Finset.expect_congr rfl
  intro x _
  exact rationalLift_major_product_eq M hM a c Ψ F A x (β x) (R x)

theorem rationalLift_major_correlation_data {U : Type*} {m : ℕ}
    (M : ℕ) (hM : 0 < M) (a : Fin m → ℤ) (c : Fin m → ℝ)
    (p q : ℝ) (hm : (m : ℝ) ≤ p) (ha : ∀ i, |(a i : ℝ)| ≤ Real.exp q)
    (S : Finset (U → ℤ)) (Ψ : PatchKernel m) (F : MvPolynomial (U ⊕ Fin m) ℝ)
    (A : Fin m → MvPolynomial U ℝ) (β : (U → ℤ) → Fin m → ℤ)
    (R : (U → ℤ) → ℂ) (ρ : ℝ)
    (hcorr : ρ ≤ ‖𝔼 x ∈ S,
      (Real.fourierChar ((∑ i, (a i : ℝ) *
        (MvPolynomial.eval (fun j => (x j : ℝ)) (A i) + c i)) / (M : ℝ)) : ℂ) *
      (Ψ.value (fun i => MvPolynomial.eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ)) : ℂ) *
      (Real.fourierChar (MvPolynomial.eval
        (fun j => ((Sum.elim x (β x) j : ℤ) : ℝ)) F) : ℂ) * R x‖) :
    (∀ y r, ‖rationalLiftCharacterTwist M a c y r‖ = 1) ∧
    (∀ r, LipschitzWith (rationalLiftCharacterTwistLip M a)
      (fun y => rationalLiftCharacterTwist M a c y r)) ∧
    (rationalLiftCharacterTwistLip M a : ℝ) ≤ Real.exp (p + q + 8) ∧
    ρ ≤ ‖𝔼 x ∈ S,
      rationalLiftCharacterTwist M a c
        (fun i => MvPolynomial.eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ))
        (fun i => (β x i : ZMod M)) *
      (Ψ.value (fun i => MvPolynomial.eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ)) : ℂ) *
      (Real.fourierChar (MvPolynomial.eval
        (fun j => ((Sum.elim x (β x) j : ℤ) : ℝ)) F) : ℂ) * R x‖ := by
  refine ⟨rationalLiftCharacterTwist_norm M a c, rationalLiftCharacterTwist_lipschitz M a c,
    rationalLiftCharacterTwistLip_le_exp_of_dim M hM a p q hm ha, ?_⟩
  rwa [← rationalLift_major_mean_eq M hM a c S Ψ F A β R]

end Erdos3

end

section

namespace Erdos3

theorem stable_sort_symm_lt {n : ℕ} (w : Fin n → ℕ) {i j : Fin n}
    (hij : i < j) (hw : w i ≤ w j) :
    (Tuple.sort w).symm i < (Tuple.sort w).symm j := by
  by_contra h
  have hji : (Tuple.sort w).symm j < (Tuple.sort w).symm i :=
    lt_of_le_of_ne (le_of_not_gt h) (fun he => hij.ne ((Tuple.sort w).symm.injective he.symm))
  have hwji := Tuple.monotone_sort w hji.le
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at hwji
  have htie := (Tuple.eq_sort_iff.mp (rfl : Tuple.sort w = Tuple.sort w)).2
    _ _ hji (by simpa only [Equiv.apply_symm_apply] using le_antisymm hwji hw)
  simp only [Equiv.apply_symm_apply] at htie
  exact (lt_asymm hij htie)

structure SlotInterleaving (D E : ℕ) where
  perm : Equiv.Perm (Fin (D + E))
  left_strictMono : StrictMono (fun i : Fin D => perm.symm (i.castAdd E))
  right_strictMono : StrictMono (fun i : Fin E => perm.symm (i.natAdd D))

namespace SlotInterleaving

variable {D E : ℕ}

def left (I : SlotInterleaving D E) (i : Fin D) : Fin (D + E) :=
  I.perm.symm (i.castAdd E)

def right (I : SlotInterleaving D E) (i : Fin E) : Fin (D + E) :=
  I.perm.symm (i.natAdd D)

def fill (I : SlotInterleaving D E) {R : Type*} (x : Fin D → R) (y : Fin E → R) :
    Fin (D + E) → R := fun k => Fin.append x y (I.perm k)

@[simp] theorem fill_left (I : SlotInterleaving D E) {R : Type*}
    (x : Fin D → R) (y : Fin E → R) (i : Fin D) : I.fill x y (I.left i) = x i := by
  simp [fill, left]

@[simp] theorem fill_right (I : SlotInterleaving D E) {R : Type*}
    (x : Fin D → R) (y : Fin E → R) (i : Fin E) : I.fill x y (I.right i) = y i := by
  simp [fill, right]

theorem cases (I : SlotInterleaving D E) {p : Fin (D + E) → Prop}
    (hl : ∀ i, p (I.left i)) (hr : ∀ i, p (I.right i)) (k : Fin (D + E)) : p k := by
  rw [← I.perm.symm_apply_apply k]
  exact Fin.addCases hl hr (I.perm k)

theorem fill_restrict (I : SlotInterleaving D E) {R : Type*} (x : Fin (D + E) → R) :
    I.fill (fun i => x (I.left i)) (fun i => x (I.right i)) = x := by
  funext k
  apply I.cases (p := fun k => I.fill (fun i => x (I.left i))
    (fun i => x (I.right i)) k = x k) _ _ k <;> intro i <;> simp

def sorted (w : Fin D → ℕ) (v : Fin E → ℕ) (hw : Monotone w) (hv : Monotone v) :
    SlotInterleaving D E where
  perm := Tuple.sort (Fin.append w v)
  left_strictMono i j hij := stable_sort_symm_lt _
    (by simpa only [Fin.lt_def, Fin.val_castAdd] using hij)
    (by simpa using hw hij.le)
  right_strictMono i j hij := stable_sort_symm_lt _ (by simpa using hij)
    (by simpa using hv hij.le)

theorem sorted_weight_mono (w : Fin D → ℕ) (v : Fin E → ℕ)
    (hw : Monotone w) (hv : Monotone v) :
    Monotone ((sorted w v hw hv).fill w v) := Tuple.monotone_sort _

end SlotInterleaving

theorem dist_restrict_coordinates_le {d n : ℕ} (f : Fin d → Fin n)
    (x y : Fin n → ℝ) : dist (fun i => x (f i)) (fun i => y (f i)) ≤ dist x y := by
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  exact dist_le_pi_dist x y (f i)

end Erdos3

end

section

namespace Erdos3

namespace TriangularSlots

variable {D E : ℕ}

theorem patchValue_freeze_dist_le (A : TriangularSlots E) (Φ : PatchKernel (D + E))
    (x y : Fin D → ℝ) :
    dist (A.patchValue (Φ.freeze x)) (A.patchValue (Φ.freeze y)) ≤ Φ.lip * dist x y :=
  A.patchValue_dist_le _ _ (mul_nonneg Φ.lip.coe_nonneg dist_nonneg)
    (Φ.freeze_value_dist_le x y)

theorem contributing_prefix_eq (A : TriangularSlots D)
    (B : (Fin D → ℝ) → TriangularSlots E) (Φ : PatchKernel (D + E))
    (b : Fin D → ℤ) (hb : ∀ i, |A.residual b i| ≤ 1 / 3)
    {v : Fin (D + E) → ℤ} (hv : Φ.value ((A.append B).residual v) ≠ 0) :
    slotPrefix v = b := by
  have hr := A.append_residual B (slotPrefix v) (slotSuffix v)
  rw [append_slotPrefix_slotSuffix] at hr
  have hp : ∀ i, |A.residual (slotPrefix v) i| ≤ 1 / 4 := by
    intro i
    have h := Φ.support _ hv (i.castAdd E)
    simpa only [hr, Fin.append_left] using h
  exact A.integer_unique (by norm_num) hp hb

theorem patchValue_append_eq (A : TriangularSlots D)
    (B : (Fin D → ℝ) → TriangularSlots E) (Φ : PatchKernel (D + E))
    (b : Fin D → ℤ) (hb : ∀ i, |A.residual b i| ≤ 1 / 3) :
    (A.append B).patchValue Φ =
      (B (fun i => (b i : ℝ))).patchValue (Φ.freeze (A.residual b)) := by
  by_cases h : ∃ v : Fin (D + E) → ℤ, Φ.value ((A.append B).residual v) ≠ 0
  · obtain ⟨v, hv⟩ := h
    have hp := A.contributing_prefix_eq B Φ b hb hv
    have hvform : Fin.append b (slotSuffix v) = v := by
      rw [← hp, append_slotPrefix_slotSuffix]
    have heq : Φ.value ((A.append B).residual v) =
        (Φ.freeze (A.residual b)).value ((B (fun i => (b i : ℝ))).residual (slotSuffix v)) := by
      rw [← hvform, A.append_residual]
      simp only [slotSuffix_append]
      rfl
    rw [(A.append B).patchValue_eq_of_nonzero Φ hv,
      (B (fun i => (b i : ℝ))).patchValue_eq_of_nonzero _ (by rwa [← heq]), heq]
  · have hz : ∀ v, Φ.value ((A.append B).residual v) = 0 := by simpa using h
    have ht : ∀ c, (Φ.freeze (A.residual b)).value
        ((B (fun i => (b i : ℝ))).residual c) = 0 := by
      intro c
      have heq := hz (Fin.append b c)
      simpa only [A.append_residual, PatchKernel.freeze] using heq
    rw [(A.append B).patchValue_eq_zero Φ hz,
      (B (fun i => (b i : ℝ))).patchValue_eq_zero _ ht]

theorem patchValue_freeze_prefix (A : TriangularSlots D)
    (B : (Fin D → ℝ) → TriangularSlots E) (Φ : PatchKernel (D + E))
    (b : Fin D → ℤ) (z : Fin D → ℝ) {ε : ℝ}
    (hz : ∀ i, |z i| ≤ 1 / 4) (hε : ε < 1 / 12)
    (hclose : dist (A.residual b) z ≤ ε) :
    dist ((A.append B).patchValue Φ)
      ((B (fun i => (b i : ℝ))).patchValue (Φ.freeze z)) ≤ Φ.lip * ε := by
  have hb : ∀ i, |A.residual b i| ≤ 1 / 3 := by
    intro i
    have hcoord := (dist_le_pi_dist (A.residual b) z i).trans hclose
    rw [Real.dist_eq] at hcoord
    have htriangle : |A.residual b i| ≤ |A.residual b i - z i| + |z i| := by
      simpa only [sub_add_cancel] using abs_add_le (A.residual b i - z i) (z i)
    linarith [hz i]
  rw [A.patchValue_append_eq B Φ b hb]
  exact (patchValue_freeze_dist_le _ Φ _ _).trans
    (mul_le_mul_of_nonneg_left hclose Φ.lip.coe_nonneg)

end TriangularSlots

end Erdos3

end

section

namespace Erdos3.TriangularSlots

variable {D E d : ℕ}

@[ext] theorem ext {A B : TriangularSlots d}
    (h : ∀ x i, A.center x i = B.center x i) : A = B := by
  have hc : A.center = B.center := funext (fun x => funext (h x))
  cases A
  cases B
  cases hc
  rfl

def takePrefix (A : TriangularSlots (D + E)) : TriangularSlots D where
  center x i := A.center (Fin.append x 0) (i.castAdd E)
  lower i x y hxy := by
    apply A.lower
    intro j
    refine Fin.addCases (fun k hj => ?_) (fun k hj => ?_) j
    · simp only [Fin.append_left]
      apply hxy
      simpa only [Fin.lt_def, Fin.val_castAdd] using hj
    · simp only [Fin.append_right]

def dropPrefix (A : TriangularSlots (D + E)) (b : Fin D → ℝ) : TriangularSlots E where
  center x i := A.center (Fin.append b x) (i.natAdd D)
  lower i x y hxy := by
    apply A.lower
    intro j
    refine Fin.addCases (fun k hj => ?_) (fun k hj => ?_) j
    · simp only [Fin.append_left]
    · simp only [Fin.append_right]
      apply hxy
      simpa only [Fin.lt_def, Fin.val_natAdd, Nat.add_lt_add_iff_left] using hj

theorem append_take_drop (A : TriangularSlots (D + E)) :
    A.takePrefix.append A.dropPrefix = A := by
  apply ext
  intro x i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [append, takePrefix, Fin.append_left]
    apply A.lower
    intro k
    refine Fin.addCases (fun l hk => ?_) (fun l hk => ?_) k
    · simp [slotPrefix]
    · have hbad : D + l.val < j.val := by simpa only [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd] using hk
      omega
  · simp only [append, dropPrefix, Fin.append_right, append_slotPrefix_slotSuffix]

theorem takePrefix_residual (A : TriangularSlots (D + E)) (v : Fin (D + E) → ℤ) :
    A.takePrefix.residual (slotPrefix v) = slotPrefix (A.residual v) := by
  have h := A.takePrefix.append_residual A.dropPrefix (slotPrefix v) (slotSuffix v)
  rw [append_take_drop, append_slotPrefix_slotSuffix] at h
  have hp := congrArg slotPrefix h
  simpa only [slotPrefix_append] using hp.symm

end Erdos3.TriangularSlots

end

section

namespace Erdos3

variable {D E : ℕ}

namespace TriangularSlots

def interleave (A : TriangularSlots D) (B : TriangularSlots E)
    (I : SlotInterleaving D E) : TriangularSlots (D + E) where
  center x := I.fill (A.center (fun i => x (I.left i)))
    (B.center (fun i => x (I.right i)))
  lower k x y h := by
    apply I.cases (p := fun k =>
      (∀ j, j < k → x j = y j) →
      I.fill (A.center (fun i => x (I.left i))) (B.center (fun i => x (I.right i))) k =
      I.fill (A.center (fun i => y (I.left i))) (B.center (fun i => y (I.right i))) k) _ _ k h
    · intro i hi
      simp only [SlotInterleaving.fill_left]
      exact A.lower i _ _ (fun j hj => hi _ (I.left_strictMono hj))
    · intro i hi
      simp only [SlotInterleaving.fill_right]
      exact B.lower i _ _ (fun j hj => hi _ (I.right_strictMono hj))

@[simp] theorem interleave_residual_left (A : TriangularSlots D) (B : TriangularSlots E)
    (I : SlotInterleaving D E) (z : Fin (D + E) → ℤ) (i : Fin D) :
    (A.interleave B I).residual z (I.left i) = A.residual (fun j => z (I.left j)) i := by
  simp [residual, interleave]

@[simp] theorem interleave_residual_right (A : TriangularSlots D) (B : TriangularSlots E)
    (I : SlotInterleaving D E) (z : Fin (D + E) → ℤ) (i : Fin E) :
    (A.interleave B I).residual z (I.right i) = B.residual (fun j => z (I.right j)) i := by
  simp [residual, interleave]

end TriangularSlots

namespace PatchKernel

def product (Φ : PatchKernel D) (Ψ : PatchKernel E) (I : SlotInterleaving D E) :
    PatchKernel (D + E) where
  value x := Φ.value (fun i => x (I.left i)) * Ψ.value (fun i => x (I.right i))
  nonneg x := mul_nonneg (Φ.nonneg _) (Ψ.nonneg _)
  le_one x := (mul_le_of_le_one_left (Ψ.nonneg _) (Φ.le_one _)).trans (Ψ.le_one _)
  support x hx := by
    have hl := Φ.support _ (mul_ne_zero_iff.mp hx).1
    have hr := Ψ.support _ (mul_ne_zero_iff.mp hx).2
    exact I.cases hl hr
  lip := Φ.lip + Ψ.lip
  lipschitz := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    let x₁ := fun i => x (I.left i)
    let x₂ := fun i => x (I.right i)
    let y₁ := fun i => y (I.left i)
    let y₂ := fun i => y (I.right i)
    have hl : dist (Φ.value x₁) (Φ.value y₁) ≤ Φ.lip * dist x y :=
      (Φ.lipschitz.dist_le_mul _ _).trans
        (mul_le_mul_of_nonneg_left (dist_restrict_coordinates_le I.left x y) Φ.lip.coe_nonneg)
    have hr : dist (Ψ.value x₂) (Ψ.value y₂) ≤ Ψ.lip * dist x y :=
      (Ψ.lipschitz.dist_le_mul _ _).trans
        (mul_le_mul_of_nonneg_left (dist_restrict_coordinates_le I.right x y) Ψ.lip.coe_nonneg)
    have h₁ : dist (Φ.value x₁ * Ψ.value x₂) (Φ.value y₁ * Ψ.value x₂) ≤
        dist (Φ.value x₁) (Φ.value y₁) := by
      rw [Real.dist_eq, ← sub_mul, abs_mul, abs_of_nonneg (Ψ.nonneg _)]
      exact mul_le_of_le_one_right (abs_nonneg _) (Ψ.le_one _)
    have h₂ : dist (Φ.value y₁ * Ψ.value x₂) (Φ.value y₁ * Ψ.value y₂) ≤
        dist (Ψ.value x₂) (Ψ.value y₂) := by
      rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg (Φ.nonneg _)]
      exact mul_le_of_le_one_left (abs_nonneg _) (Φ.le_one _)
    exact (dist_triangle _ (Φ.value y₁ * Ψ.value x₂) _).trans
      ((add_le_add (h₁.trans hl) (h₂.trans hr)).trans_eq (by simp [add_mul]))

@[simp] theorem product_lip (Φ : PatchKernel D) (Ψ : PatchKernel E)
    (I : SlotInterleaving D E) : (Φ.product Ψ I).lip = Φ.lip + Ψ.lip := rfl

@[simp] theorem product_value_fill (Φ : PatchKernel D) (Ψ : PatchKernel E)
    (I : SlotInterleaving D E) (x : Fin D → ℝ) (y : Fin E → ℝ) :
    (Φ.product Ψ I).value (I.fill x y) = Φ.value x * Ψ.value y := by
  simp [product]

end PatchKernel

namespace TriangularSlots

theorem interleave_kernel_residual (A : TriangularSlots D) (B : TriangularSlots E)
    (Φ : PatchKernel D) (Ψ : PatchKernel E) (I : SlotInterleaving D E)
    (z : Fin (D + E) → ℤ) :
    (Φ.product Ψ I).value ((A.interleave B I).residual z) =
      Φ.value (A.residual (fun j => z (I.left j))) *
      Ψ.value (B.residual (fun j => z (I.right j))) := by
  simp [PatchKernel.product]

theorem interleave_patchValue (A : TriangularSlots D) (B : TriangularSlots E)
    (Φ : PatchKernel D) (Ψ : PatchKernel E) (I : SlotInterleaving D E) :
    (A.interleave B I).patchValue (Φ.product Ψ I) = A.patchValue Φ * B.patchValue Ψ := by
  classical
  by_cases hA : ∃ b, Φ.value (A.residual b) ≠ 0
  · obtain ⟨b, hb⟩ := hA
    by_cases hB : ∃ c, Ψ.value (B.residual c) ≠ 0
    · obtain ⟨c, hc⟩ := hB
      have hz : (Φ.product Ψ I).value ((A.interleave B I).residual (I.fill b c)) ≠ 0 := by
        simpa [interleave_kernel_residual] using mul_ne_zero hb hc
      rw [(A.interleave B I).patchValue_eq_of_nonzero _ hz,
        A.patchValue_eq_of_nonzero _ hb, B.patchValue_eq_of_nonzero _ hc]
      simp [interleave_kernel_residual]
    · have hc : ∀ c, Ψ.value (B.residual c) = 0 := by simpa using hB
      rw [B.patchValue_eq_zero _ hc, mul_zero]
      apply patchValue_eq_zero
      intro z
      rw [interleave_kernel_residual, hc, mul_zero]
  · have hb : ∀ b, Φ.value (A.residual b) = 0 := by simpa using hA
    rw [A.patchValue_eq_zero _ hb, zero_mul]
    apply patchValue_eq_zero
    intro z
    rw [interleave_kernel_residual, hb, zero_mul]

end TriangularSlots

end Erdos3

end

section

namespace Erdos3.TriangularSlots

variable {D E : ℕ}

theorem factorized_patchValue_at_lift
    (A : TriangularSlots D) (B : (Fin D → ℤ) → TriangularSlots E)
    (T : TriangularSlots (D + E)) (Φ : PatchKernel D) (Ψ : PatchKernel E)
    (K : PatchKernel (D + E)) (I : SlotInterleaving D E)
    (hterm : ∀ z, K.value (T.residual z) =
      Φ.value (A.residual (fun j => z (I.left j))) *
      Ψ.value ((B (fun j => z (I.left j))).residual (fun j => z (I.right j))))
    (b : Fin D → ℤ) (hb : ∀ i, |A.residual b i| ≤ 1 / 3) :
    T.patchValue K = Φ.value (A.residual b) * (B b).patchValue Ψ := by
  have hleft (z : Fin (D + E) → ℤ)
      (hz : Φ.value (A.residual (fun j => z (I.left j))) ≠ 0) :
      (fun j => z (I.left j)) = b :=
    A.integer_unique (by norm_num) (Φ.support _ hz) hb
  by_cases hφ : Φ.value (A.residual b) = 0
  · rw [hφ, zero_mul]
    apply T.patchValue_eq_zero K
    intro z
    rw [hterm]
    by_cases hz : Φ.value (A.residual (fun j => z (I.left j))) = 0
    · rw [hz, zero_mul]
    · rw [hleft z hz, hφ, zero_mul]
  · by_cases hc : ∃ c, Ψ.value ((B b).residual c) ≠ 0
    · obtain ⟨c, hc⟩ := hc
      have hz : K.value (T.residual (I.fill b c)) ≠ 0 := by
        simpa only [hterm, SlotInterleaving.fill_left, SlotInterleaving.fill_right] using
          mul_ne_zero hφ hc
      rw [T.patchValue_eq_of_nonzero K hz, (B b).patchValue_eq_of_nonzero Ψ hc, hterm]
      simp only [SlotInterleaving.fill_left, SlotInterleaving.fill_right]
    · have hc : ∀ c, Ψ.value ((B b).residual c) = 0 := by simpa using hc
      rw [(B b).patchValue_eq_zero Ψ hc, mul_zero]
      apply T.patchValue_eq_zero K
      intro z
      rw [hterm]
      by_cases hz : Φ.value (A.residual (fun j => z (I.left j))) = 0
      · rw [hz, zero_mul]
      · rw [hleft z hz, hc, mul_zero]

theorem factorized_patchValue
    (A : TriangularSlots D) (B : (Fin D → ℤ) → TriangularSlots E)
    (T : TriangularSlots (D + E)) (Φ : PatchKernel D) (Ψ : PatchKernel E)
    (K : PatchKernel (D + E)) (I : SlotInterleaving D E)
    (hterm : ∀ z, K.value (T.residual z) =
      Φ.value (A.residual (fun j => z (I.left j))) *
      Ψ.value ((B (fun j => z (I.left j))).residual (fun j => z (I.right j)))) :
    T.patchValue K = ∑' b, Φ.value (A.residual b) * (B b).patchValue Ψ := by
  classical
  by_cases h : ∃ b, Φ.value (A.residual b) ≠ 0
  · obtain ⟨b, hb⟩ := h
    rw [A.factorized_patchValue_at_lift B T Φ Ψ K I hterm b
      (fun i => (Φ.support _ hb i).trans (by norm_num))]
    symm
    apply tsum_eq_single b
    intro c hcb
    have hc : Φ.value (A.residual c) = 0 := by
      by_contra hc
      exact hcb (A.contributing_unique Φ hc hb)
    rw [hc, zero_mul]
  · have hzero : ∀ b, Φ.value (A.residual b) = 0 := by simpa using h
    rw [T.patchValue_eq_zero K (fun z => by rw [hterm, hzero, zero_mul])]
    simp only [hzero, zero_mul, tsum_zero]

end Erdos3.TriangularSlots

end

end OAI
