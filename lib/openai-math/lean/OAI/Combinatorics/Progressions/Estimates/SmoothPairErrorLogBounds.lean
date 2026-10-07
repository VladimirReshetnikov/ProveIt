import OAI.Combinatorics.Progressions.Dynamics.JointPivotProfileBudget
import OAI.Combinatorics.Progressions.Lattices.CellResidueCorrelation
import OAI.Combinatorics.Progressions.Sampling.SmoothPairPhysicalGrid

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem uniform_pair_sum {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (f : X → Y → ℝ) :
    (Fintype.card X : ℝ) * Fintype.card Y *
        (FiniteProbabilityWeights.uniform X).mean
          (fun x => (FiniteProbabilityWeights.uniform Y).mean (f x)) = ∑ x, ∑ y, f x y := by
  simp_rw [FiniteProbabilityWeights.uniform_mean, Fintype.expect_eq_sum_div_card, ← Finset.sum_div]
  have hX : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hY : (Fintype.card Y : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp [hX, hY]

theorem uniform_joint_residual_bound {X Y A B R : Type*}
    [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    [Fintype A] [Fintype B] [Fintype R] [Nonempty R]
    [DecidableEq A] [DecidableEq B] [DecidableEq R]
    (C : X → A) (D : Y → B) (F : X → R) (G : Y → R)
    (e : X → ℝ) (d : Y → ℝ) (joint k : X → Y → ℝ) (cell : A → B → R → ℝ)
    {V delta gamma L K epsilon zeta : ℝ} (hV : 0 < V)
    (hdelta : 0 ≤ delta) (hL : 0 ≤ L) (hepsilon : 0 ≤ epsilon) (hzeta : 0 ≤ zeta)
    (hp : ∀ r, (FiniteProbabilityWeights.uniform X).eventProbability (fun x => F x = r) ≤
      K / Fintype.card R)
    (hq : ∀ r, (FiniteProbabilityWeights.uniform Y).eventProbability (fun y => G y = r) ≤
      K / Fintype.card R)
    (he : ∀ a r, |finiteCellResidueMean (FiniteProbabilityWeights.uniform X) C F e a r| ≤
      (finiteCellWeights (FiniteProbabilityWeights.uniform X) C).weight a * delta / Fintype.card R)
    (hd : ∀ b r, |finiteCellResidueMean (FiniteProbabilityWeights.uniform Y) D G d b r| ≤
      (finiteCellWeights (FiniteProbabilityWeights.uniform Y) D).weight b * gamma / Fintype.card R)
    (hcell : ∀ a b r, |cell a b r| ≤ L)
    (hoff : ∀ x y, F x ≠ G y → joint x y = 0)
    (hpoint : ∀ x y, F x = G y →
      |V * joint x y - (Fintype.card R : ℝ) * k x y| ≤ Fintype.card R * epsilon)
    (hgrid : ∀ x y, F x = G y → |k x y - cell (C x) (D y) (F x)| ≤ zeta) :
    |∑ x, ∑ y, joint x y * e x * d y| ≤
      ((Fintype.card X : ℝ) * Fintype.card Y / V) *
        (L * delta * gamma + (epsilon + zeta) * (K / 2 *
          ((FiniteProbabilityWeights.uniform X).mean (fun x => e x ^ 2) +
           (FiniteProbabilityWeights.uniform Y).mean (fun y => d y ^ 2)))) := by
  let p := FiniteProbabilityWeights.uniform X
  let q := FiniteProbabilityWeights.uniform Y
  let N : ℝ := Fintype.card R
  let a : X → Y → ℝ := fun x y => V * joint x y / N
  have hN : 0 < N := by dsimp only [N]; exact_mod_cast Fintype.card_pos
  have hnear (x : X) (y : Y) (h : F x = G y) : |a x y - k x y| ≤ epsilon := by
    have hid : a x y - k x y = (V * joint x y - N * k x y) / N := by
      dsimp only [a]
      field_simp [hN.ne']
    rw [hid, abs_div, abs_of_pos hN]
    apply (div_le_iff₀ hN).mpr
    exact (hpoint x y h).trans_eq (mul_comm _ _)
  have happrox (x : X) (y : Y) (h : F x = G y) :
      |a x y - cell (C x) (D y) (F x)| ≤ epsilon + zeta :=
    (abs_sub_le (a x y) (k x y) (cell (C x) (D y) (F x))).trans
      (add_le_add (hnear x y h) (hgrid x y h))
  have hmain := finite_cell_kernel_correlation p q C D F G e d a cell
    hdelta hL (add_nonneg hepsilon hzeta) hp hq he hd hcell happrox
  have hpoint' (x : X) (y : Y) :
      N * (if F x = G y then a x y * e x * d y else 0) = V * (joint x y * e x * d y) := by
    by_cases h : F x = G y
    · simp only [h, ite_true, a]
      field_simp
    · simp [h, hoff x y h]
  have hscaled : N * p.mean (fun x => q.mean (fun y => if F x = G y then a x y * e x * d y else 0)) =
      V * p.mean (fun x => q.mean (fun y => joint x y * e x * d y)) := by
    calc
      _ = p.mean (fun x => q.mean (fun y => N *
          (if F x = G y then a x y * e x * d y else 0))) := by
        simp only [q.mean_const_mul, p.mean_const_mul]
      _ = _ := by simp only [hpoint', q.mean_const_mul, p.mean_const_mul]
  have hsum := uniform_pair_sum (fun x y => joint x y * e x * d y)
  have hid : (∑ x, ∑ y, joint x y * e x * d y) =
      ((Fintype.card X : ℝ) * Fintype.card Y / V) *
        (N * p.mean (fun x => q.mean (fun y => if F x = G y then a x y * e x * d y else 0))) := by
    rw [hscaled]
    change _ = _ * (V * (FiniteProbabilityWeights.uniform X).mean
      (fun x => (FiniteProbabilityWeights.uniform Y).mean (fun y => joint x y * e x * d y)))
    rw [← mul_assoc, div_mul_cancel₀ _ hV.ne']
    exact hsum.symm
  rw [hid, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (Fintype.card X : ℝ) * Fintype.card Y / V)]
  exact mul_le_mul_of_nonneg_left hmain (by positivity)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem smoothSource_pair_kernel_reduction {J I A B R : Type*}
    [Fintype J] [Fintype I] [Fintype A] [Fintype B] [Fintype R] [Nonempty R]
    [DecidableEq A] [DecidableEq B] [DecidableEq R]
    (a S : Option J × I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (t u : J → ℤ) (T U : Finset (I → ℤ)) [Nonempty T] [Nonempty U]
    (e d : (I → ℤ) → ℝ) (heoff : ∀ x ∉ T, e x = 0) (hdoff : ∀ y ∉ U, d y = 0)
    (C : T → A) (D : U → B) (F : T → R) (G : U → R)
    (k : T → U → ℝ) (cell : A → B → R → ℝ)
    {V delta gamma L K epsilon zeta : ℝ} (hV : 0 < V)
    (hdelta : 0 ≤ delta) (hL : 0 ≤ L) (hepsilon : 0 ≤ epsilon) (hzeta : 0 ≤ zeta)
    (hp : ∀ r, (FiniteProbabilityWeights.uniform T).eventProbability (fun x => F x = r) ≤
      K / Fintype.card R)
    (hq : ∀ r, (FiniteProbabilityWeights.uniform U).eventProbability (fun y => G y = r) ≤
      K / Fintype.card R)
    (he : ∀ c r, |finiteCellResidueMean (FiniteProbabilityWeights.uniform T) C F (fun x => e x.val) c r| ≤
      (finiteCellWeights (FiniteProbabilityWeights.uniform T) C).weight c * delta / Fintype.card R)
    (hd : ∀ c r, |finiteCellResidueMean (FiniteProbabilityWeights.uniform U) D G (fun y => d y.val) c r| ≤
      (finiteCellWeights (FiniteProbabilityWeights.uniform U) D).weight c * gamma / Fintype.card R)
    (hcell : ∀ c c' r, |cell c c' r| ≤ L)
    (hoff : ∀ x : T, ∀ y : U, F x ≠ G y →
      ((shiftedSmoothProductPMF a S hS hZ).map (smoothAffinePairRows t u)
        (affinePairRowsOfLocations (x.val, y.val))).toReal = 0)
    (hpoint : ∀ x : T, ∀ y : U, F x = G y →
      |V * ((shiftedSmoothProductPMF a S hS hZ).map (smoothAffinePairRows t u)
        (affinePairRowsOfLocations (x.val, y.val))).toReal -
          (Fintype.card R : ℝ) * k x y| ≤ Fintype.card R * epsilon)
    (hgrid : ∀ x y, F x = G y → |k x y - cell (C x) (D y) (F x)| ≤ zeta) :
    |(smoothSourceFiniteWeights a S hS hZ).mean
      (fun z => e (smoothAffineSample t z.val) * d (smoothAffineSample u z.val))| ≤
      ((T.card : ℝ) * U.card / V) *
        (L * delta * gamma + (epsilon + zeta) * (K / 2 *
          ((FiniteProbabilityWeights.uniform T).mean (fun x => e x.val ^ 2) +
           (FiniteProbabilityWeights.uniform U).mean (fun y => d y.val ^ 2)))) := by
  rw [smoothSource_pair_correlation a S hS hZ t u T U e d heoff hdoff]
  have h := uniform_joint_residual_bound C D F G (fun x => e x.val) (fun y => d y.val)
    (fun x y => ((shiftedSmoothProductPMF a S hS hZ).map (smoothAffinePairRows t u)
      (affinePairRowsOfLocations (x.val, y.val))).toReal) k cell
    hV hdelta hL hepsilon hzeta hp hq he hd hcell hoff hpoint hgrid
  have hsum (f : (I → ℤ) → (I → ℤ) → ℝ) :
      (∑ x : T, ∑ y : U, f x.val y.val) = ∑ x ∈ T, ∑ y ∈ U, f x y := by
    have hi (x : I → ℤ) : (∑ y : U, f x y.val) = ∑ y ∈ U, f x y :=
      Finset.sum_coe_sort U (f x)
    simp_rw [hi]
    exact Finset.sum_coe_sort T (fun x => ∑ y ∈ U, f x y)
  rw [hsum (fun x y => ((shiftedSmoothProductPMF a S hS hZ).map (smoothAffinePairRows t u)
    (affinePairRowsOfLocations (x, y))).toReal * e x * d y)] at h
  simpa only [Fintype.card_coe, mul_assoc] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem fullSmoothPairError_nonneg {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ δ : ℝ) (hδ : 0 ≤ δ) :
    0 ≤ fullSmoothPairError n k Q C κ δ := by
  have he := smoothPairProbabilityError_nonneg k Q C κ δ hδ
  have hc : 0 ≤ smoothPairProbabilityCap k Q C κ := by
    unfold smoothPairProbabilityCap
    positivity
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) he)
    (pow_nonneg (add_nonneg hc he) _)

theorem canonical_smooth_pair_correlation {J I A B : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    (H : I → ℝ) {L C κ δ : ℝ} (Q : ℕ) (hH : ∀ i, 0 < H i)
    (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : ∀ j, |(t j : ℝ) / L| ≤ C) (hu : ∀ j, |(u j : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|)
    (hQ : affinePairModulus t u ≤ Q)
    (hmesh : ∀ i, ((u k - t k).natAbs : ℝ) * L / H i ≤ δ)
    (hsmall : (4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k}) * smoothPairRowLipschitz k * δ ≤ 1 / 2)
    (b : Option J × I → ℤ)
    (hZ : 0 < shiftedSmoothProductMass (fun z => (b z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1))
    (T U : Finset (I → ℤ)) [Nonempty T] [Nonempty U]
    (e d : (I → ℤ) → ℝ) (heoff : ∀ x ∉ T, e x = 0) (hdoff : ∀ y ∉ U, d y = 0)
    (P : T → A) (R : U → B) (cell : A → B → (I → ZMod (affinePairModulus t u)) → ℝ)
    {alpha beta cap mass zeta : ℝ} (halpha : 0 ≤ alpha) (hcap : 0 ≤ cap) (hzeta : 0 ≤ zeta)
    (hp : ∀ r, (FiniteProbabilityWeights.uniform T).eventProbability
      (fun x => integerVectorResidue (affinePairModulus t u) x.val = r) ≤
      mass / (affinePairModulus t u : ℝ) ^ Fintype.card I)
    (hq : ∀ r, (FiniteProbabilityWeights.uniform U).eventProbability
      (fun y => integerVectorResidue (affinePairModulus t u) y.val = r) ≤
      mass / (affinePairModulus t u : ℝ) ^ Fintype.card I)
    (he : ∀ c r, |finiteCellResidueMean (FiniteProbabilityWeights.uniform T) P
      (fun x => integerVectorResidue (affinePairModulus t u) x.val) (fun x => e x.val) c r| ≤
      (finiteCellWeights (FiniteProbabilityWeights.uniform T) P).weight c * alpha /
        (affinePairModulus t u : ℝ) ^ Fintype.card I)
    (hd : ∀ c r, |finiteCellResidueMean (FiniteProbabilityWeights.uniform U) R
      (fun y => integerVectorResidue (affinePairModulus t u) y.val) (fun y => d y.val) c r| ≤
      (finiteCellWeights (FiniteProbabilityWeights.uniform U) R).weight c * beta /
        (affinePairModulus t u : ℝ) ^ Fintype.card I)
    (hcell : ∀ c c' r, |cell c c' r| ≤ cap)
    (hgrid : ∀ x : T, ∀ y : U,
      integerVectorResidue (affinePairModulus t u) x.val = integerVectorResidue (affinePairModulus t u) y.val →
      |shiftedPairLocationKernel t u k hne H L hH (zero_lt_one.trans_le hL) b x.val y.val -
        cell (P x) (R y) (integerVectorResidue (affinePairModulus t u) x.val)| ≤ zeta) :
    |(smoothSourceFiniteWeights (fun z => (b z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1)
      (fun z => smoothPairCoefficientScale_pos (hH z.2) (zero_lt_one.trans_le hL) z.1) hZ).mean
      (fun z => e (smoothAffineSample t z.val) * d (smoothAffineSample u z.val))| ≤
      ((T.card : ℝ) * U.card / ∏ i, H i ^ 2) *
        (cap * alpha * beta + (fullSmoothPairError (Fintype.card I) k Q C κ δ + zeta) * (mass / 2 *
          ((FiniteProbabilityWeights.uniform T).mean (fun x => e x.val ^ 2) +
           (FiniteProbabilityWeights.uniform U).mean (fun y => d y.val ^ 2)))) := by
  let : NeZero (affinePairModulus t u) := ⟨(affinePairModulus_pos t u k hne).ne'⟩
  have hV : (0 : ℝ) < ∏ i, H i ^ 2 :=
    Finset.prod_pos (fun i _ => pow_pos (hH i) _)
  refine smoothSource_pair_kernel_reduction
    (fun z => (b z : ℝ)) (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1)
    (fun z => smoothPairCoefficientScale_pos (hH z.2) (zero_lt_one.trans_le hL) z.1) hZ
    t u T U e d heoff hdoff P R
    (fun x => integerVectorResidue (affinePairModulus t u) x.val)
    (fun y => integerVectorResidue (affinePairModulus t u) y.val)
    (fun x y => shiftedPairLocationKernel t u k hne H L hH (zero_lt_one.trans_le hL) b x.val y.val)
    cell hV halpha hcap (fullSmoothPairError_nonneg _ k Q C κ δ hδ) hzeta
    ?_ ?_ ?_ ?_ hcell ?_ ?_ hgrid
  · simpa only [integerVectorResidue_card, Nat.cast_pow] using hp
  · simpa only [integerVectorResidue_card, Nat.cast_pow] using hq
  · simpa only [integerVectorResidue_card, Nat.cast_pow] using he
  · simpa only [integerVectorResidue_card, Nat.cast_pow] using hd
  · intro x y hxy
    rw [affinePairPMF_zero_off_residue _ t u x.val y.val hxy, ENNReal.toReal_zero]
  · intro x y hxy
    simpa only [integerVectorResidue_card, Nat.cast_pow] using
      canonical_pair_point_error t u k hne H Q hH hL hC hκ hδ hδ1 ht hu hgap hQ hmesh hsmall
        b hZ x.val y.val hxy

end Erdos3

end

section

namespace Erdos3

noncomputable def smoothPairErrorCoefficient {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ : ℝ) : ℝ := fullSmoothPairError n k Q C κ 1

theorem smoothPairErrorCoefficient_nonneg {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ : ℝ) : 0 ≤ smoothPairErrorCoefficient n k Q C κ :=
  fullSmoothPairError_nonneg n k Q C κ 1 zero_le_one

theorem smoothPairProbabilityError_mul {J : Type*} [Fintype J] [DecidableEq J]
    (k : J) (Q : ℕ) (C κ δ : ℝ) :
    smoothPairProbabilityError k Q C κ δ = smoothPairProbabilityError k Q C κ 1 * δ := by
  simp only [smoothPairProbabilityError, mul_one]

theorem fullSmoothPairError_le_linear {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    fullSmoothPairError n k Q C κ δ ≤ smoothPairErrorCoefficient n k Q C κ * δ := by
  have hE := smoothPairProbabilityError_nonneg k Q C κ 1 zero_le_one
  have hcap : 0 ≤ smoothPairProbabilityCap k Q C κ := by unfold smoothPairProbabilityCap; positivity
  have hEd : 0 ≤ smoothPairProbabilityError k Q C κ 1 * δ := mul_nonneg hE hδ
  have hle : smoothPairProbabilityError k Q C κ 1 * δ ≤ smoothPairProbabilityError k Q C κ 1 := by
    nlinarith
  unfold fullSmoothPairError smoothPairErrorCoefficient
  rw [smoothPairProbabilityError_mul k Q C κ δ]
  calc
    _ ≤ n * (smoothPairProbabilityError k Q C κ 1 * δ) *
        (smoothPairProbabilityCap k Q C κ + smoothPairProbabilityError k Q C κ 1) ^ n :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (add_nonneg hcap hEd) (add_le_add le_rfl hle) n)
        (mul_nonneg (Nat.cast_nonneg _) hEd)
    _ = _ := by unfold fullSmoothPairError; ring

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem smoothPairRowLipschitz_le_exp (k : J) {P : ℝ} (hP : 0 ≤ P)
    (hcard : (Fintype.card J : ℝ) ≤ Real.exp P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) :
    (smoothPairRowLipschitz k : ℝ) ≤ Real.exp (2 * P + 3) := by
  have hd : (Fintype.card {j : J // j ≠ k} : ℝ) ≤ Fintype.card J := by
    exact_mod_cast Fintype.card_subtype_le (fun j : J => j ≠ k)
  have h1 : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have h3 : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have hsum : (Fintype.card {j : J // j ≠ k} : ℝ) + 2 ≤ Real.exp (P + 3) := by
    rw [Real.exp_add]
    nlinarith
  simp only [smoothPairRowLipschitz, NNReal.coe_mul, Nat.cast_add, Nat.cast_ofNat]
  calc
    _ ≤ Real.exp (P + 3) * Real.exp P := mul_le_mul hsum hprofile (by positivity) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem smoothPairScaleRatio_le_exp {C κ P : ℝ}
    (hC0 : 0 ≤ C) (hκ0 : 0 < κ) (hC : C ≤ Real.exp P) (hκ : κ⁻¹ ≤ Real.exp P) :
    4 * C / κ ≤ Real.exp (2 * P + 4) := by
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  rw [div_eq_mul_inv]
  calc
    _ ≤ Real.exp 4 * Real.exp P * Real.exp P := by gcongr
    _ = _ := by simp only [← Real.exp_add]; congr 1; ring

theorem smoothPairQuadraticFactor_le_exp (k : J) {C κ P : ℝ}
    (hC0 : 0 ≤ C) (hκ0 : 0 < κ) (hC : C ≤ Real.exp P) (hκ : κ⁻¹ ≤ Real.exp P)
    (hpow : (2 : ℝ) ^ Fintype.card {j : J // j ≠ k} ≤ Real.exp P) :
    2 * (4 * C / κ) ^ 2 * 2 ^ Fintype.card {j : J // j ≠ k} ≤ Real.exp (5 * P + 10) := by
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hU := smoothPairScaleRatio_le_exp hC0 hκ0 hC hκ
  calc
    _ ≤ Real.exp 2 * (Real.exp (2 * P + 4)) ^ 2 * Real.exp P := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul]; simp only [← Real.exp_add]; congr 1; ring

theorem smoothPairProbabilityCap_le_exp (k : J) (Q : ℕ) {C κ P : ℝ}
    (hP : 0 ≤ P) (hC0 : 0 ≤ C) (hκ0 : 0 < κ)
    (hQ : (Q : ℝ) ≤ Real.exp P) (hC : C ≤ Real.exp P) (hκ : κ⁻¹ ≤ Real.exp P)
    (hpow : (2 : ℝ) ^ Fintype.card {j : J // j ≠ k} ≤ Real.exp P) :
    smoothPairProbabilityCap k Q C κ ≤ Real.exp (6 * P + 11) := by
  have hfactor := smoothPairQuadraticFactor_le_exp k hC0 hκ0 hC hκ hpow
  have hproduct : (Q : ℝ) * (2 * (4 * C / κ) ^ 2 * 2 ^ Fintype.card {j : J // j ≠ k}) ≤
      Real.exp (6 * P + 10) := by
    calc
      _ ≤ Real.exp P * Real.exp (5 * P + 10) := mul_le_mul hQ hfactor (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ ≤ Real.exp ((6 * P + 10) + 1) := one_add_le_exp_succ (by linarith) hproduct
    _ = _ := by congr 1; ring

theorem smoothPairKernelBaseCap_le_exp (k : J) {C κ P : ℝ}
    (hP : 0 ≤ P) (hC0 : 0 ≤ C) (hκ0 : 0 < κ) (hC : C ≤ Real.exp P) (hκ : κ⁻¹ ≤ Real.exp P)
    (hpow : (2 : ℝ) ^ Fintype.card {j : J // j ≠ k} ≤ Real.exp P) :
    (smoothPairKernelBaseCap k C κ : ℝ) ≤ Real.exp (5 * P + 11) := by
  apply coe_toNNReal_le_exp
  calc
    _ ≤ Real.exp ((5 * P + 10) + 1) := one_add_le_exp_succ (by linarith)
      (smoothPairQuadraticFactor_le_exp k hC0 hκ0 hC hκ hpow)
    _ = _ := by congr 1; ring

theorem smoothPairKernelBaseLip_le_exp (k : J) {C κ P : ℝ}
    (hC0 : 0 ≤ C) (hκ0 : 0 < κ) (hC : C ≤ Real.exp P) (hκ : κ⁻¹ ≤ Real.exp P)
    (hrow : (smoothPairRowLipschitz k : ℝ) ≤ Real.exp P)
    (hpow : (2 : ℝ) ^ Fintype.card {j : J // j ≠ k} ≤ Real.exp P) :
    (smoothPairKernelBaseLip k C κ : ℝ) ≤ Real.exp (8 * P + 14) := by
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hU := smoothPairScaleRatio_le_exp hC0 hκ0 hC hκ
  apply coe_toNNReal_le_exp
  calc
    _ ≤ Real.exp 2 * (Real.exp (2 * P + 4)) ^ 3 * Real.exp P * Real.exp P := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul]; simp only [← Real.exp_add]; congr 1; ring

theorem smoothPairKernelCap_le_exp (n : ℕ) (k : J) {C κ P : ℝ}
    (hP : 0 ≤ P) (hC0 : 0 ≤ C) (hκ0 : 0 < κ) (hC : C ≤ Real.exp P) (hκ : κ⁻¹ ≤ Real.exp P)
    (hpow : (2 : ℝ) ^ Fintype.card {j : J // j ≠ k} ≤ Real.exp P) :
    (smoothPairKernelCap n k C κ : ℝ) ≤ Real.exp ((n : ℝ) * (5 * P + 11)) := by
  simpa only [smoothPairKernelCap, NNReal.coe_pow, Real.exp_nat_mul] using
    pow_le_pow_left₀ (NNReal.coe_nonneg (smoothPairKernelBaseCap k C κ))
      (smoothPairKernelBaseCap_le_exp k hP hC0 hκ0 hC hκ hpow) n

theorem smoothPairKernelLip_le_exp (n : ℕ) (k : J) {C κ P : ℝ}
    (hP : 0 ≤ P) (hC0 : 0 ≤ C) (hκ0 : 0 < κ)
    (hn : (n : ℝ) ≤ Real.exp P) (hC : C ≤ Real.exp P) (hκ : κ⁻¹ ≤ Real.exp P)
    (hrow : (smoothPairRowLipschitz k : ℝ) ≤ Real.exp P)
    (hpow : (2 : ℝ) ^ Fintype.card {j : J // j ≠ k} ≤ Real.exp P) :
    (smoothPairKernelLip n k C κ : ℝ) ≤ Real.exp ((n : ℝ) * (5 * P + 11) + 9 * P + 14) := by
  have hbase := smoothPairKernelBaseLip_le_exp k hC0 hκ0 hC hκ hrow hpow
  have hcap := smoothPairKernelCap_le_exp n k hP hC0 hκ0 hC hκ hpow
  simp only [smoothPairKernelLip, NNReal.coe_mul, NNReal.coe_natCast]
  calc
    _ ≤ Real.exp P * Real.exp (8 * P + 14) * Real.exp ((n : ℝ) * (5 * P + 11)) := by gcongr
    _ = _ := by simp only [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem smoothPair_pivot_card (k : J) : Fintype.card {j : J // j ≠ k} = Fintype.card J - 1 := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]

theorem smoothPairRowLipschitz_pivot (k l : J) : smoothPairRowLipschitz k = smoothPairRowLipschitz l := by
  simp only [smoothPairRowLipschitz, smoothPair_pivot_card]

theorem smoothPairProbabilityError_pivot (k l : J) (Q : ℕ) (C κ δ : ℝ) :
    smoothPairProbabilityError k Q C κ δ = smoothPairProbabilityError l Q C κ δ := by
  simp only [smoothPairProbabilityError, smoothPair_pivot_card, smoothPairRowLipschitz_pivot k l]

theorem smoothPairProbabilityCap_pivot (k l : J) (Q : ℕ) (C κ : ℝ) :
    smoothPairProbabilityCap k Q C κ = smoothPairProbabilityCap l Q C κ := by
  simp only [smoothPairProbabilityCap, smoothPair_pivot_card]

theorem fullSmoothPairError_pivot (n : ℕ) (k l : J) (Q : ℕ) (C κ δ : ℝ) :
    fullSmoothPairError n k Q C κ δ = fullSmoothPairError n l Q C κ δ := by
  simp only [fullSmoothPairError, smoothPairProbabilityCap_pivot k l, smoothPairProbabilityError_pivot k l]

theorem smoothPairKernelCap_pivot (n : ℕ) (k l : J) (C κ : ℝ) :
    smoothPairKernelCap n k C κ = smoothPairKernelCap n l C κ := by
  simp only [smoothPairKernelCap, smoothPairKernelBaseCap, smoothPair_pivot_card]

theorem smoothPairKernelLip_pivot (n : ℕ) (k l : J) (C κ : ℝ) :
    smoothPairKernelLip n k C κ = smoothPairKernelLip n l C κ := by
  simp only [smoothPairKernelLip, smoothPairKernelCap_pivot n k l, smoothPairKernelBaseLip,
    smoothPair_pivot_card, smoothPairRowLipschitz_pivot k l]

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

noncomputable def smoothPairRowErrorLog (d : ℕ) (P : ℝ) : ℝ :=
  (16 + 4 * d) * P + 16 * d + 48

theorem smoothPairRowErrorLog_nonneg (d : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ smoothPairRowErrorLog d P := by
  unfold smoothPairRowErrorLog
  positivity

theorem smoothPairProbabilityError_one_le_exp (k : J) (Q : ℕ) {C κ P : ℝ}
    (hP : 0 ≤ P) (hC0 : 0 ≤ C) (hκ0 : 0 < κ)
    (hQ : (Q : ℝ) ≤ Real.exp P) (hC : C ≤ Real.exp P) (hκ : κ⁻¹ ≤ Real.exp P)
    (hcard : (Fintype.card J : ℝ) ≤ Real.exp P)
    (hrow : (smoothPairRowLipschitz k : ℝ) ≤ Real.exp P) :
    smoothPairProbabilityError k Q C κ 1 ≤
      Real.exp (smoothPairRowErrorLog (Fintype.card {j : J // j ≠ k}) P) := by
  have hlift : Real.exp P ≤ Real.exp (2 * P + 4) := Real.exp_le_exp.mpr (by linarith)
  have hV : (Fintype.card J : ℝ) * C ≤ Real.exp (2 * P + 4) := by
    calc
      _ ≤ Real.exp P * Real.exp P := mul_le_mul hcard hC hC0 (Real.exp_nonneg _)
      _ = Real.exp (2 * P) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have h1 : (1 : ℝ) ≤ Real.exp (2 * P + 4) := Real.one_le_exp_iff.mpr (by linarith)
  have h := normalizedFiberErrorConstant_le_exp 2 (Fintype.card {j : J // j ≠ k})
    (smoothPairRowLipschitz k) (by linarith : 0 ≤ 2 * P + 4)
    (Nat.cast_nonneg Q) (by positivity) (by positivity) (by norm_num) (by norm_num)
    (hQ.trans hlift) (smoothPairScaleRatio_le_exp hC0 hκ0 hC hκ) hV h1 h1 (hrow.trans hlift)
  simp only [smoothPairProbabilityError, mul_one]
  apply h.trans_eq
  congr 1
  unfold smoothPairRowErrorLog
  ring

noncomputable def smoothPairErrorLog (n d : ℕ) (P : ℝ) : ℝ :=
  P + smoothPairRowErrorLog d P + n * (smoothPairRowErrorLog d P + 6 * P + 12)

theorem smoothPairErrorLog_nonneg (n d : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ smoothPairErrorLog n d P := by
  have hr := smoothPairRowErrorLog_nonneg d hP
  unfold smoothPairErrorLog
  positivity

theorem smoothPairErrorCoefficient_le_exp (n : ℕ) (k : J) (Q : ℕ) {C κ P : ℝ}
    (hP : 0 ≤ P) (hC0 : 0 ≤ C) (hκ0 : 0 < κ)
    (hn : (n : ℝ) ≤ Real.exp P) (hQ : (Q : ℝ) ≤ Real.exp P)
    (hC : C ≤ Real.exp P) (hκ : κ⁻¹ ≤ Real.exp P)
    (hcard : (Fintype.card J : ℝ) ≤ Real.exp P)
    (hrow : (smoothPairRowLipschitz k : ℝ) ≤ Real.exp P)
    (hpow : (2 : ℝ) ^ Fintype.card {j : J // j ≠ k} ≤ Real.exp P) :
    smoothPairErrorCoefficient n k Q C κ ≤
      Real.exp (smoothPairErrorLog n (Fintype.card {j : J // j ≠ k}) P) := by
  let d := Fintype.card {j : J // j ≠ k}
  have hr := smoothPairProbabilityError_one_le_exp k Q hP hC0 hκ0 hQ hC hκ hcard hrow
  have hc := smoothPairProbabilityCap_le_exp k Q hP hC0 hκ0 hQ hC hκ hpow
  have hsum : smoothPairProbabilityCap k Q C κ + smoothPairProbabilityError k Q C κ 1 ≤
      Real.exp (smoothPairRowErrorLog d P + 6 * P + 12) := by
    have hh := add_le_exp_add_one (by linarith : 0 ≤ 6 * P + 11)
      (smoothPairRowErrorLog_nonneg d hP) hc hr
    apply hh.trans_eq
    congr 1
    ring
  have hr0 := smoothPairProbabilityError_nonneg k Q C κ 1 zero_le_one
  have hc0 : 0 ≤ smoothPairProbabilityCap k Q C κ := by unfold smoothPairProbabilityCap; positivity
  unfold smoothPairErrorCoefficient fullSmoothPairError
  calc
    _ ≤ Real.exp P * Real.exp (smoothPairRowErrorLog d P) *
        (Real.exp (smoothPairRowErrorLog d P + 6 * P + 12)) ^ n := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul]
      simp only [← Real.exp_add]
      congr 1

theorem smoothPairMeshCoefficient_le_exp (k : J) {P : ℝ}
    (hrow : (smoothPairRowLipschitz k : ℝ) ≤ Real.exp P) :
    (4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k}) * smoothPairRowLipschitz k ≤
      Real.exp (4 * (2 + (Fintype.card {j : J // j ≠ k} : ℝ)) + P) := by
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  calc
    _ ≤ (Real.exp 4) ^ (2 + Fintype.card {j : J // j ≠ k}) * Real.exp P := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast; congr 1; ring

end Erdos3

end

end OAI
