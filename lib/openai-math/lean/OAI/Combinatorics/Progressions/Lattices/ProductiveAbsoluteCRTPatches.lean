import Mathlib.LinearAlgebra.Matrix.ToLin
import OAI.Combinatorics.Progressions.Polynomial.AbsoluteCRTPolynomialPatch

namespace OAI

section

namespace Erdos3

namespace IntegerVectorAPFree

variable {I J : Type*} {k : ℕ}

theorem mono {A B : Set (I → ℤ)} (hA : IntegerVectorAPFree A k) (hBA : B ⊆ A) :
    IntegerVectorAPFree B k := by
  intro a d hd
  obtain ⟨i, hi⟩ := hA a d hd
  exact ⟨i, fun h => hi (hBA h)⟩

theorem affine_preimage {A : Set (J → ℤ)} (hA : IntegerVectorAPFree A k)
    (hk : 2 ≤ k) (L : (I → ℤ) →+ (J → ℤ)) (b : J → ℤ)
    (domain : Set (I → ℤ))
    (hinj : Set.InjOn (fun x => b + L x) domain) :
    IntegerVectorAPFree (domain ∩ (fun x => b + L x) ⁻¹' A) k := by
  intro a d hd
  by_contra! h
  have ha : a ∈ domain := by simpa using (h ⟨0, by omega⟩).1
  have had : a + d ∈ domain := by simpa using (h ⟨1, by omega⟩).1
  have hLd : L d ≠ 0 := by
    intro hzero
    have he : b + L (a + d) = b + L a := by simp [hzero]
    have he' : a + d = a := hinj had ha he
    apply hd
    exact add_left_cancel (show a + d = a + 0 by simpa using he')
  obtain ⟨i, hi⟩ := hA (b + L a) (L d) hLd
  apply hi
  have hp := (h i).2
  simpa only [Set.mem_preimage, map_add, map_zsmul, add_assoc] using hp

end IntegerVectorAPFree

namespace BooleanCubeKernel

theorem joint_sample_progression_free {K X : Type*} [Fintype K]
    {A : Set (X → ℤ)} {k : ℕ} (hA : IntegerVectorAPFree A k) (hk : 2 ≤ k)
    (z : (X → ℤ) × (Option K × X → ℤ)) (domain : Set (K → ℤ))
    (hinj : Set.InjOn (fun x => jointIntegerPhysicalSite x z) domain) :
    IntegerVectorAPFree (domain ∩ (fun x => jointIntegerPhysicalSite x z) ⁻¹' A) k := by
  classical
  let L : (K → ℤ) →+ (X → ℤ) :=
    (Matrix.of (fun i j => z.2 (some j,i))).mulVecLin.toAddMonoidHom
  let b : X → ℤ := fun i => z.1 i + z.2 (none,i)
  have he (x : K → ℤ) : jointIntegerPhysicalSite x z = b + L x := by
    funext i
    change z.1 i + (z.2 (none,i) + ∑ j, x j * z.2 (some j,i)) =
      (z.1 i + z.2 (none,i)) + ∑ j, z.2 (some j,i) * x j
    rw [← add_assoc]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h := hA.affine_preimage hk L b domain (by simpa only [he] using hinj)
  simpa only [he] using h

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

namespace IntegerVectorAPFree

theorem affine_residue_support {K X : Type*} {k : ℕ}
    (f : (X → ℤ) → ℝ) (hfree : IntegerVectorAPFree (Function.support f) k)
    (hk : 2 ≤ k) (N : K → ℕ) (L : (K → ℤ) →+ (X → ℤ)) (b : X → ℤ)
    (hinj : Function.Injective (fun u => b + L (residueBoxIntegerPoint N u))) :
    IntegerVectorAPFree
      (residueBoxIntegerPoint N ''
        Function.support (fun u => f (b + L (residueBoxIntegerPoint N u)))) k := by
  have hi : Set.InjOn (fun x => b + L x) (Set.range (residueBoxIntegerPoint N)) := by
    intro x hx y hy hxy
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hy
    exact congrArg (residueBoxIntegerPoint N) (hinj hxy)
  apply (hfree.affine_preimage hk L b (Set.range (residueBoxIntegerPoint N)) hi).mono
  rintro x ⟨u, hu, rfl⟩
  exact ⟨⟨u, rfl⟩, hu⟩

end IntegerVectorAPFree

namespace BooleanCubeKernel

theorem joint_residue_sample_progression_free {K X : Type*} [Fintype K] {k : ℕ}
    (f : (X → ℤ) → ℝ) (hfree : IntegerVectorAPFree (Function.support f) k)
    (hk : 2 ≤ k) (N : K → ℕ)
    (z : (X → ℤ) × (Option K × X → ℤ))
    (hinj : Function.Injective
      (fun u => jointIntegerPhysicalSite (residueBoxIntegerPoint N u) z)) :
    IntegerVectorAPFree
      (residueBoxIntegerPoint N '' Function.support
        (fun u => f (jointIntegerPhysicalSite (residueBoxIntegerPoint N u) z))) k := by
  have hi : Set.InjOn (fun x => jointIntegerPhysicalSite x z)
      (Set.range (residueBoxIntegerPoint N)) := by
    intro x hx y hy hxy
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hy
    exact congrArg (residueBoxIntegerPoint N) (hinj hxy)
  apply (joint_sample_progression_free hfree hk z
    (Set.range (residueBoxIntegerPoint N)) hi).mono
  rintro x ⟨u, hu, rfl⟩
  exact ⟨⟨u, rfl⟩, hu⟩

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem PolynomialPatch.positive_score_target_lt_one {σ Ω : Type*} [Fintype Ω]
    {s d : ℕ} (P : PolynomialPatch σ s d) (t : Ω → σ → ℝ) (f : Ω → ℝ)
    (hf : ∀ x, f x ≤ 1) {b : ℝ}
    (hscore : 0 < 𝔼 x, (f x - b) * P.value (t x)) : b < 1 := by
  by_contra h
  have hb : 1 ≤ b := le_of_not_gt h
  have hnonpos : (𝔼 x, (f x - b) * P.value (t x)) ≤ 0 := by
    calc
      _ ≤ 𝔼 _x : Ω, (0 : ℝ) := Finset.expect_le_expect
        (fun x _ => mul_nonpos_of_nonpos_of_nonneg
          (by linarith [hf x]) (P.value_mem_Icc _).1)
      _ = 0 := by simp
  exact (not_lt_of_ge hnonpos) hscore

theorem exists_absolute_crt_threshold_rule {J : Type*} [Fintype J] [DecidableEq J]
    [Nonempty J] (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi : ℝ, 0 < xi ∧
      ∀ {p a : ℝ}, 2 ≤ p → Real.exp (-p) ≤ a →
      ∀ (N : J → ℕ) [∀ j, NeZero (N j)] [NeZero (∏ j, N j)],
        (∀ j, (N j).Prime) → Function.Injective N →
        (∀ j, Real.exp ((p + 2) ^ C) ≤ N j) →
        ∀ f : ((j : J) → ZMod (N j)) → ℝ,
          (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) → a ≤ (𝔼 x, f x) →
          IntegerVectorAPFree (residueBoxIntegerPoint N '' Function.support f) k →
          (1 + xi) * a < 1 ∧ ∃ d : ℕ, ∃ P : PolynomialPatch J (k - 2) d,
            (d : ℝ) ≤ (p + 2) ^ C ∧
            (P.kernel.lip : ℝ) + 1 ≤ Real.exp ((p + 2) ^ C) ∧
            Real.exp (-((p + 2) ^ C)) ≤
              (𝔼 x, (f x - (1 + xi) * a) * P.value (fun j => ((x j).val : ℝ))) := by
  obtain ⟨C, hC, xi, hxi, hpatch⟩ := exists_absolute_crt_patch (J := J) k hk
  refine ⟨C, hC, xi, hxi, ?_⟩
  intro p a hp ha N _ _ hprime hinj hsize f hf hmean hfree
  let alpha := 𝔼 x, f x
  have halpha : 0 < alpha := (Real.exp_pos (-p)).trans_le (ha.trans hmean)
  have hlog : Real.log (1 / alpha) ≤ p := by
    rw [one_div, Real.log_inv]
    have h := Real.log_le_log (Real.exp_pos (-p)) (ha.trans hmean)
    rw [Real.log_exp] at h
    linarith
  obtain ⟨d, P, hcost, hscore⟩ := hpatch N hprime hinj f halpha hp hlog hsize hf rfl hfree
  have hlognonneg : 0 ≤ Real.log (2 + (P.kernel.lip : ℝ)) :=
    Real.log_nonneg (by linarith [P.kernel.lip.coe_nonneg])
  have hlip : Real.log (2 + (P.kernel.lip : ℝ)) ≤ (p + 2) ^ C := by
    linarith [Nat.cast_nonneg (α := ℝ) d]
  have hscore' : Real.exp (-((p + 2) ^ C)) ≤
      (𝔼 x, (f x - (1 + xi) * a) * P.value (fun j => ((x j).val : ℝ))) := by
    apply hscore.trans
    apply Finset.expect_le_expect
    intro x _
    apply mul_le_mul_of_nonneg_right _ (P.value_mem_Icc _).1
    have h := mul_le_mul_of_nonneg_left hmean (show 0 ≤ 1 + xi by linarith)
    dsimp only [alpha] at *
    linarith
  refine ⟨P.positive_score_target_lt_one _ f (fun x => (hf x).2)
    ((Real.exp_pos _).trans_le hscore'), d, P, by linarith, ?_, hscore'⟩
  · have h := Real.exp_le_exp.mpr hlip
    rw [Real.exp_log (by positivity : 0 < 2 + (P.kernel.lip : ℝ))] at h
    linarith

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem exists_productive_absolute_crt_patches
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J] (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi : ℝ, 0 < xi ∧
      ∀ {H X : Type*} [Fintype H] (productive : Finset H), productive.Nonempty →
      ∀ {p a : ℝ}, 2 ≤ p → Real.exp (-p) ≤ a →
      ∀ (N : J → ℕ) [∀ j, NeZero (N j)] [NeZero (∏ j, N j)],
        (∀ j, (N j).Prime) → Function.Injective N →
        (∀ j, Real.exp ((p + 2) ^ C) ≤ N j) →
      ∀ (f : (X → ℤ) → ℝ) (z : H → (X → ℤ) × (Option J × X → ℤ)),
        (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) →
        IntegerVectorAPFree (Function.support f) k →
        (∀ h ∈ productive, Function.Injective
          (fun u => BooleanCubeKernel.jointIntegerPhysicalSite (residueBoxIntegerPoint N u) (z h))) →
        (∀ h ∈ productive, a ≤ 𝔼 u,
          f (BooleanCubeKernel.jointIntegerPhysicalSite (residueBoxIntegerPoint N u) (z h))) →
      (1 + xi) * a < 1 ∧
      ∃ (d : H → ℕ) (patch : ∀ h : H, PolynomialPatch J (k - 2) (d h)),
        (∀ h : H,
          (d h : ℝ) ≤ (p + 2) ^ C ∧
          ((patch h).kernel.lip : ℝ) + 1 ≤ Real.exp ((p + 2) ^ C)) ∧
        ∀ h ∈ productive, Real.exp (-((p + 2) ^ C)) ≤
            𝔼 u, (f (BooleanCubeKernel.jointIntegerPhysicalSite (residueBoxIntegerPoint N u) (z h)) -
              (1 + xi) * a) * (patch h).value (fun j => ((u j).val : ℝ)) := by
  obtain ⟨C, hC, xi, hxi, habsolute⟩ := exists_absolute_crt_threshold_rule (J := J) k hk
  refine ⟨C, hC, xi, hxi, ?_⟩
  intro H X _ productive hne p a hp ha N _ _ hprime hinj hsize f z hf hfree hzinj hmean
  have hpatch (h : productive) := habsolute hp ha N hprime hinj hsize
    (fun u => f (BooleanCubeKernel.jointIntegerPhysicalSite (residueBoxIntegerPoint N u) (z h)))
    (fun _ => hf _) (hmean h h.property)
    (BooleanCubeKernel.joint_residue_sample_progression_free f hfree (by omega) N (z h)
      (hzinj h h.property))
  obtain ⟨h0, hh0⟩ := hne
  refine ⟨(hpatch ⟨h0,hh0⟩).1, ?_⟩
  choose d patch hcost using fun h => (hpatch h).2
  let chosen (h : H) : productive := if hh : h ∈ productive then ⟨h,hh⟩ else ⟨h0,hh0⟩
  refine ⟨fun h => d (chosen h), fun h => patch (chosen h),
    fun h => ⟨(hcost (chosen h)).1, (hcost (chosen h)).2.1⟩, ?_⟩
  intro h hh
  have hchosen : chosen h = ⟨h,hh⟩ := by simp [chosen, hh]
  dsimp only
  rw [hchosen]
  exact (hcost ⟨h,hh⟩).2.2

end Erdos3

end

end OAI
