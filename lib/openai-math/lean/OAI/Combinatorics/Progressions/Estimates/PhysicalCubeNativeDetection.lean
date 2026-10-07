import OAI.Combinatorics.Progressions.Geometry.PhysicalSupportedCubes
import OAI.Combinatorics.Progressions.Probability.CubeMixtureNativeDetection

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem conjugationPower_twice (n : ℕ) (z : ℂ) :
    conjugationPower n (conjugationPower n z) = z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change star (conjugationPower n (star (conjugationPower n z))) = z
    rw [conjugationPower_star, ih, star_star]

namespace BooleanCubeKernel

def vertexFinsetEquiv (j : ℕ) : (Fin j → Bool) ≃ Finset (Fin j) where
  toFun ω := Finset.univ.filter (fun i => ω i)
  invFun s := fun i => decide (i ∈ s)
  left_inv ω := by funext i; simp
  right_inv s := by ext i; simp

theorem vertexFinsetEquiv_card {j : ℕ} (ω : Fin j → Bool) :
    (vertexFinsetEquiv j ω).card = booleanWeight ω := by
  simp only [vertexFinsetEquiv, Equiv.coe_fn_mk, booleanWeight]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

theorem physical_twisted_cube_product {X : Type*} (j : ℕ)
    (f : (X → ℤ) → ℂ) (twist : Finset (Fin j) → (X → ℤ) → ℂ)
    (u : X → (Unit ⊕ Fin j) → ℤ) :
    (∏ s, conjugationPower s.card (f (physicalCubeVertexValue u s)) *
      twist s (physicalCubeVertexValue u s)) =
    mixedCubeProduct (fun ω x => f x * conjugationPower (booleanWeight ω)
      (twist (vertexFinsetEquiv j ω) x))
      (physicalCubeParametersEquiv X j u).1 (physicalCubeParametersEquiv X j u).2 := by
  rw [← (vertexFinsetEquiv j).prod_comp]
  apply Finset.prod_congr rfl
  intro ω _
  rw [vertexFinsetEquiv_card]
  change conjugationPower (booleanWeight ω)
      (f (physicalCubeVertexValue u (Finset.univ.filter (fun i => ω i)))) *
      twist (vertexFinsetEquiv j ω) (physicalCubeVertexValue u (Finset.univ.filter (fun i => ω i))) = _
  rw [physicalCubeParametersEquiv_vertex, map_mul, conjugationPower_twice]

theorem physical_twisted_cube_mean {X : Type*} (j : ℕ)
    (Q : Finset (X → ℤ)) (f : (X → ℤ) → ℂ)
    (twist : Finset (Fin j) → (X → ℤ) → ℂ) :
    (𝔼 cube : SupportedCube j (Q : Set (X → ℤ)),
      let u := (physicalCubeParametersEquiv X j).symm cube.val
      ∏ s, conjugationPower s.card (f (physicalCubeVertexValue u s)) *
        twist s (physicalCubeVertexValue u s)) =
      normalizedSupportedCubeSum j Q (fun ω x => f x *
        conjugationPower (booleanWeight ω) (twist (vertexFinsetEquiv j ω) x)) := by
  simp_rw [physical_twisted_cube_product, Equiv.apply_symm_apply]
  simp only [normalizedSupportedCubeSum, supportedCubeSum, Fintype.expect_eq_sum_div_card,
    Nat.card_eq_fintype_card]

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

noncomputable def integerSelfSiteTest {X : Type*} (q : ℕ) (f : (X → ℤ) → ℂ)
    (site : Finset (Fin q)) (y : X → ℝ) : ℂ :=
  conjugationPower site.card (f (fun x => ⌊y x⌋))

theorem integerSelfSiteTest_norm_le {X : Type*} (q : ℕ) (f : (X → ℤ) → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (site : Finset (Fin q)) (y : X → ℝ) :
    ‖integerSelfSiteTest q f site y‖ ≤ 1 := by
  rw [integerSelfSiteTest, conjugationPower_norm]
  exact hf _

theorem physicalCubeSiteTest_self_joint {X K : Type*} [Fintype K] (q : ℕ)
    (f : (X → ℤ) → ℂ) (root : K → ℤ) (D : Matrix (Fin q) K ℤ)
    (base : X → ℤ) (z : Option K × X → ℤ) :
    physicalCubeSiteTest (integerSelfSiteTest q f) (physicalCubeRootDifferences root D base z) =
      mixedCubeProduct (fun _ t => f (jointIntegerPhysicalSite t (base, z))) D root := by
  simp only [physicalCubeSiteTest, integerSelfSiteTest, Int.floor_intCast]
  rw [← (vertexFinsetEquiv q).prod_comp]
  apply Finset.prod_congr rfl
  intro ω _
  rw [vertexFinsetEquiv_card]
  change conjugationPower (booleanWeight ω) (f (physicalCubeVertexValue
    (physicalCubeRootDifferences root D base z) (vertexFinsetEquiv q ω))) =
      conjugationPower (booleanWeight ω) (f (jointIntegerPhysicalSite (root + cubeShift D ω) (base, z)))
  congr 2
  have hroot : integerAffineCube root D (vertexFinsetEquiv q ω) = root + cubeShift D ω := by
    funext k
    simp only [integerAffineCube, vertexFinsetEquiv, Equiv.coe_fn_mk,
      cubeShift, Pi.add_apply, Finset.sum_apply, Finset.sum_filter, ite_apply, Pi.zero_apply]
  funext x
  change physicalCubeRootDifferences root D base z x (.inl ()) +
    ∑ i ∈ vertexFinsetEquiv q ω, physicalCubeRootDifferences root D base z x (.inr i) = _
  rw [physicalCubeRootDifferences_vertex, hroot]

theorem normalizedSupportedCubeSum_joint {X K : Type*} [Fintype K] (q : ℕ)
    (Q : Finset (K → ℤ)) (f : (X → ℤ) → ℂ)
    (base : X → ℤ) (z : Option K × X → ℤ) :
    normalizedSupportedCubeSum q Q (fun _ t => f (jointIntegerPhysicalSite t (base, z))) =
      𝔼 cube : SupportedCube q (Q : Set (K → ℤ)),
        physicalCubeSiteTest (integerSelfSiteTest q f)
          (physicalCubeRootDifferences cube.val.2 cube.val.1 base z) := by
  calc
    _ = (𝔼 cube : SupportedCube q (Q : Set (K → ℤ)),
        mixedCubeProduct (fun _ t => f (jointIntegerPhysicalSite t (base, z))) cube.val.1 cube.val.2) := by
      simp only [normalizedSupportedCubeSum, supportedCubeSum,
        Fintype.expect_eq_sum_div_card, Nat.card_eq_fintype_card]
    _ = _ := Finset.expect_congr rfl (fun cube _ =>
      (physicalCubeSiteTest_self_joint q f cube.val.2 cube.val.1 base z).symm)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators

theorem commonStridePoint_cube {K : Type*} (q : ℕ) (c root : K → ℤ) (d : ℕ)
    (D : Fin q → K → ℤ) (ω : Fin q → Bool) :
    commonStridePoint c d (root + cubeShift D ω) =
      commonStridePoint c d root + cubeShift (fun j k => (d : ℤ) * D j k) ω := by
  funext k
  simp only [commonStridePoint, cubeShift, Pi.add_apply, Finset.sum_apply]
  rw [mul_add, Finset.mul_sum]
  rw [add_assoc]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  cases ω j <;> simp only [Bool.false_eq_true, ↓reduceIte,
    Pi.zero_apply, mul_zero]

theorem mixedCubeProduct_commonStride {K : Type*} (q : ℕ) (c root : K → ℤ) (d : ℕ)
    (D : Fin q → K → ℤ) (F : (Fin q → Bool) → (K → ℤ) → ℂ) :
    mixedCubeProduct (fun ω u => F ω (commonStridePoint c d u)) D root =
      mixedCubeProduct F (fun j k => (d : ℤ) * D j k) (commonStridePoint c d root) := by
  unfold mixedCubeProduct
  apply Finset.prod_congr rfl
  intro ω _
  dsimp only
  rw [commonStridePoint_cube]

theorem commonStride_normalized_cube_source {K X : Type*} [Fintype K] [DecidableEq K]
    (q : ℕ) (H : K → ℕ) (hH : ∀ k, 0 < H k) (c : K → ℤ) (d : ℕ)
    (f : (X → ℤ) → ℂ) (base : X → ℤ) (z : Option K × X → ℤ) :
    normalizedSupportedCubeSum q (integerBox H)
        (fun _ u => f (jointIntegerPhysicalSite (commonStridePoint c d u) (base, z))) =
      (FiniteProbabilityWeights.pi (fun k => integerScalarCubeWeights (Fin q) (H k) (hH k))).complexMean
        (fun u => physicalCubeSiteTest (integerSelfSiteTest q f)
          (physicalCubeRootDifferences
            (commonStridePoint c d (fun k => (u k none : ℤ)))
            (fun j k => (d : ℤ) * (u k (some j) : ℤ)) base z)) := by
  rw [normalizedSupportedCubeSum_eq_scalarProduct H hH]
  congr 1
  funext u
  exact (mixedCubeProduct_commonStride q c (fun k => (u k none : ℤ)) d
    (fun j k => (u k (some j) : ℤ)) (fun _ t => f (jointIntegerPhysicalSite t (base, z)))).trans
    (physicalCubeSiteTest_self_joint q f _ _ base z).symm

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_native_partner_of_physical_cube_mixture (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {n : ℕ} (N : Fin n → ℕ) [∀ i, NeZero (N i)]
      {I : Type*} [Fintype I] (p : ℝ), 0 ≤ p → (n : ℝ) ≤ p →
      ∀ (f : (Fin n → ℤ) → ℂ) (c : I → ℂ)
        (twist : I → Finset (Fin (s + 1)) → (Fin n → ℤ) → ℂ),
      (∀ x ∈ integerBox N, ‖f x‖ ≤ 1) →
      (∀ i ω x, x ∈ integerBox N → ‖twist i ω x‖ ≤ 1) →
      (∑ i, ‖c i‖) ≤ Real.exp p →
      ∀ z : ℂ, Real.exp (-p) ≤ z.re →
      ‖z - ∑ i, c i * (𝔼 cube : SupportedCube (s + 1) (integerBox N : Set ((Fin n) → ℤ)),
        let u := (physicalCubeParametersEquiv (Fin n) (s + 1)).symm cube.val
        ∏ ω, conjugationPower ω.card (f (physicalCubeVertexValue u ω)) *
          twist i ω (physicalCubeVertexValue u ω))‖ ≤ Real.exp (-p) / 2 →
      ∃ (i : I) (V : NativeSampleCorrelation (fun _ : Fin n => 1) s ((p + 2) ^ C)
        (integerBox N) id (fun x => f x * twist i ∅ x)),
        V.test.normBound ≤ 1 ∧
        Real.exp (-((p + 2) ^ C)) ≤
          ‖𝔼 x ∈ integerBox N, f x * star (star (twist i ∅ x) * V.test.eval x)‖ := by
  obtain ⟨C, hC, hdetect⟩ := exists_native_partner_of_cube_mixture s hs
  refine ⟨C, hC, ?_⟩
  intro n N _ I _ p hp hn f c twist hf htwist hc z hz herr
  simp_rw [physical_twisted_cube_mean] at herr
  have ht : ∀ i ω x, x ∈ integerBox N →
      ‖conjugationPower (booleanWeight ω) (twist i (vertexFinsetEquiv (s + 1) ω) x)‖ ≤ 1 := by
    intro i ω x hx
    rw [conjugationPower_norm]
    exact htwist i _ x hx
  have h := hdetect N p hp hn f c
    (fun i ω x => conjugationPower (booleanWeight ω) (twist i (vertexFinsetEquiv (s + 1) ω) x))
    hf ht hc z hz herr (fun _ => false)
  have hweight : booleanWeight (fun _ : Fin (s + 1) => false) = 0 := by
    simp [booleanWeight]
  have hsite : vertexFinsetEquiv (s + 1) (fun _ => false) = ∅ := by
    ext i
    simp [vertexFinsetEquiv]
  rw [hweight, hsite] at h
  exact h

end Erdos3

end

end OAI
