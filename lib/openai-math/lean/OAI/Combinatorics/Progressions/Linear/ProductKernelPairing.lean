import OAI.Combinatorics.Progressions.Probability.CylinderJointMass

namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProbabilityWeights

theorem mean_pi_fin_cons {n : ℕ} {X : Fin (n + 1) → Type*} [∀ i, Fintype (X i)]
    (p : ∀ i, FiniteProbabilityWeights (X i)) (f : (∀ i, X i) → ℝ) :
    (pi p).mean f = (p 0).mean (fun a =>
      (pi (fun i : Fin n => p i.succ)).mean (fun y => f (Fin.cons a y))) := by
  have h := congrArg Complex.re (complexMean_pi_fin_cons p (fun x => (f x : ℂ)))
  simpa only [complexMean_re, Complex.ofReal_re] using h

theorem mean_empty_tuple {X : Fin 0 → Type*} [∀ i, Fintype (X i)]
    (p : FiniteProbabilityWeights (∀ i, X i)) (f : (∀ i, X i) → ℝ) :
    p.mean f = f (fun i => Fin.elim0 i) := by
  have hf : f = fun _ => f (fun i => Fin.elim0 i) := by
    funext x
    exact congrArg f (Subsingleton.elim _ _)
  rw [hf, p.mean_const]

end FiniteProbabilityWeights

noncomputable def productMatrixApply {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X Y : ι → Type*} [∀ i, Fintype (Y i)] (A : ∀ i, X i → Y i → ℝ)
    (f : (∀ i, Y i) → ℝ) (x : ∀ i, X i) : ℝ := ∑ y, (∏ i, A i (x i) (y i)) * f y

theorem productMatrixApply_empty {X Y : Fin 0 → Type*} [∀ i, Fintype (Y i)]
    (A : ∀ i, X i → Y i → ℝ) (f : (∀ i, Y i) → ℝ) (x : ∀ i, X i) :
    productMatrixApply A f x = f (fun i => Fin.elim0 i) := by
  classical
  simp only [productMatrixApply, Fin.prod_univ_zero, one_mul, Fintype.sum_unique]
  congr 1

theorem productMatrixApply_fin_cons {n : ℕ} {X Y : Fin (n + 1) → Type*}
    [∀ i, Fintype (Y i)] (A : ∀ i, X i → Y i → ℝ) (f : (∀ i, Y i) → ℝ)
    (x : X 0) (u : ∀ i : Fin n, X i.succ) :
    productMatrixApply A f (Fin.cons x u) = ∑ y : Y 0, A 0 x y *
      productMatrixApply (fun i : Fin n => A i.succ) (fun v => f (Fin.cons y v)) u := by
  simp only [productMatrixApply, sum_dependent_fin_cons, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_succ, Finset.mul_sum, mul_assoc]

theorem productMatrixApply_sq_le_fin {n : ℕ} {X Y : Fin n → Type*}
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (A : ∀ i, X i → Y i → ℝ) (C : Fin n → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hA : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (∑ y, A i x y * f y) ^ 2) ≤
      C i * (ν i).mean (fun y => f y ^ 2)) (f : (∀ i, Y i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => productMatrixApply A f x ^ 2) ≤
      (∏ i, C i) * (FiniteProbabilityWeights.pi ν).mean (fun y => f y ^ 2) := by
  induction n with
  | zero =>
      simp only [productMatrixApply_empty, Fin.prod_univ_zero, one_mul,
        FiniteProbabilityWeights.mean_const, FiniteProbabilityWeights.mean_empty_tuple]
      exact le_rfl
  | succ n ih =>
      rw [FiniteProbabilityWeights.mean_pi_fin_cons]
      simp_rw [productMatrixApply_fin_cons]
      rw [FiniteProbabilityWeights.mean_comm]
      calc
        _ ≤ (FiniteProbabilityWeights.pi (fun i : Fin n => μ i.succ)).mean
            (fun x => C 0 * (ν 0).mean (fun y =>
              productMatrixApply (fun i : Fin n => A i.succ) (fun v => f (Fin.cons y v)) x ^ 2)) :=
          FiniteProbabilityWeights.mean_mono _ (fun x => hA 0 _)
        _ = C 0 * (ν 0).mean (fun y =>
            (FiniteProbabilityWeights.pi (fun i : Fin n => μ i.succ)).mean
              (fun x => productMatrixApply (fun i : Fin n => A i.succ) (fun v => f (Fin.cons y v)) x ^ 2)) := by
          rw [FiniteProbabilityWeights.mean_const_mul, FiniteProbabilityWeights.mean_comm]
        _ ≤ C 0 * (ν 0).mean (fun y => (∏ i : Fin n, C i.succ) *
            (FiniteProbabilityWeights.pi (fun i : Fin n => ν i.succ)).mean
              (fun v => f (Fin.cons y v) ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ (hC 0)
          apply FiniteProbabilityWeights.mean_mono
          intro y
          exact ih (fun i => μ i.succ) (fun i => ν i.succ) (fun i => A i.succ)
            (fun i => C i.succ) (fun i => hC i.succ) (fun i => hA i.succ) (fun v => f (Fin.cons y v))
        _ = _ := by
          rw [FiniteProbabilityWeights.mean_const_mul, Fin.prod_univ_succ,
            FiniteProbabilityWeights.mean_pi_fin_cons]
          ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

omit [∀ i, Fintype (X i)] in
theorem productMatrixApply_reindex (A : ∀ i, X i → Y i → ℝ) (e : κ ≃ ι)
    (f : (∀ i, Y i) → ℝ) (x : ∀ i, X i) :
    productMatrixApply A f x = productMatrixApply (fun j => A (e j))
      (fun y => f (Equiv.piCongrLeft Y e y)) (fun j => x (e j)) := by
  classical
  unfold productMatrixApply
  apply Fintype.sum_equiv (Equiv.piCongrLeft Y e).symm
  intro y
  simp only [Equiv.apply_symm_apply, Equiv.piCongrLeft_symm_apply]
  rw [e.prod_comp (fun i => A i (x i) (y i))]

omit [Fintype κ] [DecidableEq κ] in
theorem productMatrixApply_sq_le (μ : ∀ i, FiniteProbabilityWeights (X i))
    (ν : ∀ i, FiniteProbabilityWeights (Y i)) (A : ∀ i, X i → Y i → ℝ)
    (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hA : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (∑ y, A i x y * f y) ^ 2) ≤
      C i * (ν i).mean (fun y => f y ^ 2)) (f : (∀ i, Y i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => productMatrixApply A f x ^ 2) ≤
      (∏ i, C i) * (FiniteProbabilityWeights.pi ν).mean (fun y => f y ^ 2) := by
  let e := (Fintype.equivFin ι).symm
  let eY := Equiv.piCongrLeft Y e
  have hh := productMatrixApply_sq_le_fin (fun j => μ (e j)) (fun j => ν (e j))
    (fun j => A (e j)) (fun j => C (e j)) (fun j => hC (e j)) (fun j => hA (e j))
    (fun y => f (eY y))
  have hleft := productMean_reindex μ e
    (fun x => productMatrixApply (fun j => A (e j)) (fun y => f (eY y)) x ^ 2)
  rw [← hleft] at hh
  have heval (x : ∀ i, X i) : productMatrixApply (fun j => A (e j))
      (fun y => f (eY y)) (fun j => x (e j)) = productMatrixApply A f x :=
    (productMatrixApply_reindex A e f x).symm
  simp_rw [heval] at hh
  have hright := productMean_reindex ν e (fun y => f (eY y) ^ 2)
  have he (y : ∀ i, Y i) : eY (fun j => y (e j)) = y := eY.apply_symm_apply y
  simp_rw [he] at hright
  rw [← hright, e.prod_comp C] at hh
  exact hh

omit [Fintype κ] [DecidableEq κ] in
theorem productMatrixApply_pairing_sq_le (μ : ∀ i, FiniteProbabilityWeights (X i))
    (ν : ∀ i, FiniteProbabilityWeights (Y i)) (A : ∀ i, X i → Y i → ℝ)
    (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hA : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (∑ y, A i x y * f y) ^ 2) ≤
      C i * (ν i).mean (fun y => f y ^ 2))
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    ((FiniteProbabilityWeights.pi μ).mean (fun x => w x * productMatrixApply A f x)) ^ 2 ≤
      (∏ i, C i) * (FiniteProbabilityWeights.pi μ).mean (fun x => w x ^ 2) *
        (FiniteProbabilityWeights.pi ν).mean (fun y => f y ^ 2) := by
  have hc := (FiniteProbabilityWeights.pi μ).mean_mul_sq_le w (productMatrixApply A f)
  have ht := productMatrixApply_sq_le μ ν A C hC hA f
  have he := mul_le_mul_of_nonneg_left ht ((FiniteProbabilityWeights.pi μ).mean_nonneg (fun x => sq_nonneg (w x)))
  exact (hc.trans he).trans_eq (by ring)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def productPairCoordinates {ι : Type*} (X Y : ι → Type*) :
    (∀ i, X i × Y i) ≃ (∀ i, X i) × (∀ i, Y i) where
  toFun z := (fun i => (z i).1, fun i => (z i).2)
  invFun z := fun i => (z.1 i, z.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

theorem productJoint_mean (μ : ∀ i, FiniteProbabilityWeights (X i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i))
    (F : (∀ i, X i) → (∀ i, Y i) → ℝ) :
    (FiniteProbabilityWeights.pi (fun i => (μ i).joint (K i))).mean
      (fun z => F (fun i => (z i).1) (fun i => (z i).2)) =
      (FiniteProbabilityWeights.pi μ).mean
        (fun x => (FiniteProbabilityWeights.pi (fun i => K i (x i))).mean (F x)) := by
  calc
    _ = ∑ z : (∀ i, X i) × (∀ i, Y i),
        (∏ i, (μ i).weight (z.1 i)) * (∏ i, (K i (z.1 i)).weight (z.2 i)) * F z.1 z.2 := by
      apply Fintype.sum_equiv (productPairCoordinates X Y)
      intro z
      change (∏ i, (μ i).weight (z i).1 * (K i (z i).1).weight (z i).2) * _ = _
      rw [Finset.prod_mul_distrib]
      rfl
    _ = _ := by
      simp only [Fintype.sum_prod_type, FiniteProbabilityWeights.mean,
        FiniteProbabilityWeights.pi, Finset.mul_sum, mul_assoc]

theorem productCouplingPairing_ofKernel (μ : ∀ i, FiniteProbabilityWeights (X i))
    (ν : ∀ i, FiniteProbabilityWeights (Y i)) (K : ∀ i, X i → FiniteProbabilityWeights (Y i))
    (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productCouplingPairing (fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)) w f =
      (FiniteProbabilityWeights.pi μ).mean
        (fun x => w x * productMatrixApply (fun i x y => (K i x).weight y) f x) := by
  change (FiniteProbabilityWeights.pi (fun i => (μ i).joint (K i))).mean
    (fun z => w (fun i => (z i).1) * f (fun i => (z i).2)) = _
  rw [productJoint_mean μ K (fun x y => w x * f y)]
  simp only [FiniteProbabilityWeights.mean_const_mul]
  rfl

end Erdos3

end

end OAI
