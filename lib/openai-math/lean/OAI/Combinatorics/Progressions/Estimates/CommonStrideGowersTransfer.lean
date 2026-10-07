import OAI.Combinatorics.Progressions.Geometry.CommonStrideCoordinates
import OAI.Combinatorics.Progressions.Geometry.FiniteSupportCutoffTransfer

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem integerProgression_image_zmod {m M : ℕ} (hm : 0 < m) (hmM : m ∣ M)
    (c : ℤ) (H : ℕ) (y : ZMod M) :
    y ∈ (integerProgressionSupport c m H).image (fun x : ℤ => (x : ZMod M)) ↔
      y ∈ cyclicInterval (c : ZMod M) (m * H) ∧
        ZMod.castHom hmM (ZMod m) y = (c : ZMod m) := by
  constructor
  · rintro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hlo, hhi, hr⟩ := (mem_integerProgressionSupport_iff c m H hm x).mp hx
    refine ⟨?_, ?_⟩
    · apply Finset.mem_image.mpr
      refine ⟨(x - c).toNat, Finset.mem_range.mpr ?_, ?_⟩
      · have he : ((x - c).toNat : ℤ) = x - c := Int.toNat_of_nonneg (by omega)
        omega
      · have he : ((x - c).toNat : ℤ) = x - c := Int.toNat_of_nonneg (by omega)
        have hc := congrArg (fun z : ℤ => (z : ZMod M)) he
        push_cast at hc
        rw [hc]
        ring
    · simpa only [map_intCast] using hr
  · rintro ⟨hy, hr⟩
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hy
    have hnlt := Finset.mem_range.mp hn
    have hz : (n : ZMod m) = 0 := by
      simpa only [map_add, map_intCast, map_natCast, add_eq_left] using hr
    apply Finset.mem_image.mpr
    refine ⟨c + n, (mem_integerProgressionSupport_iff c m H hm _).mpr ?_, by push_cast; rfl⟩
    refine ⟨by omega, by omega, ?_⟩
    simp only [Int.cast_add, Int.cast_natCast, hz, add_zero]

variable {I : Type*} [Fintype I] [DecidableEq I]

def productResidueHom (N : I → ℕ) (m : ℕ) (hmN : ∀ i, m ∣ N i) :
    (∀ i, ZMod (N i)) →+ (I → ZMod m) where
  toFun x i := ZMod.castHom (hmN i) (ZMod m) (x i)
  map_zero' := by funext i; exact map_zero _
  map_add' x y := by funext i; exact map_add _ _ _

def productZmodReduction (N : I → ℕ) : (I → ℤ) →+ (∀ i, ZMod (N i)) where
  toFun x i := x i
  map_zero' := by funext i; exact Int.cast_zero
  map_add' x y := by funext i; exact Int.cast_add _ _

theorem commonStrideBox_image_zmod (N : I → ℕ) (c : I → ℤ) (m : ℕ) (H : I → ℕ)
    (hm : 0 < m) (hmN : ∀ i, m ∣ N i) (y : ∀ i, ZMod (N i)) :
    y ∈ (commonStrideBox c m H).image (productZmodReduction N) ↔
      y ∈ cyclicProductBox N (fun i => (c i : ZMod (N i))) (fun i => m * H i) ∧
        productResidueHom N m hmN y = fun i => (c i : ZMod m) := by
  have he : (commonStrideBox c m H).image (productZmodReduction N) =
      Fintype.piFinset (fun i => (integerProgressionSupport (c i) m (H i)).image
        (fun x : ℤ => (x : ZMod (N i)))) := by
    exact (Fintype.piFinset_image (fun i (x : ℤ) => (x : ZMod (N i))) _).symm
  rw [he, Fintype.mem_piFinset]
  simp only [integerProgression_image_zmod hm (hmN _), cyclicProductBox, Fintype.mem_piFinset,
    productResidueHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, funext_iff, forall_and]

end Erdos3

end

section

namespace Erdos3

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] [DecidableEq B]

theorem finiteSupportGowersNorm_image_map (j : ℕ) (φ : A →+ B) (Q : Finset A)
    (hφ : ReflectsPairSums φ (Q : Set A)) (f : B → ℂ) :
    finiteSupportGowersNorm j (Q.image φ) f =
      finiteSupportGowersNorm j Q (fun x => f (φ x)) := by
  calc
    _ = finiteSupportGowersNorm j (Q.image φ)
        (imageExtension φ Q (fun x => f (φ x))) := by
      apply finiteSupportGowersNorm_congr_on
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact (imageExtension_apply hφ.injOn (fun x => f (φ x)) hx).symm
    _ = _ := finiteSupportGowersNorm_imageExtension hφ j _

variable {I : Type*} [Fintype I] [DecidableEq I]

def coordinateStrideHom (d : ℤ) : (I → ℤ) →+ (I → ℤ) where
  toFun x i := d * x i
  map_zero' := by funext i; exact mul_zero d
  map_add' x y := by funext i; exact mul_add _ _ _

omit [Fintype I] [DecidableEq I] in
theorem coordinateStrideHom_injective {d : ℤ} (hd : d ≠ 0) :
    Function.Injective (coordinateStrideHom (I := I) d) := by
  intro x y h
  funext i
  exact mul_left_cancel₀ hd (congrFun h i)

omit [Fintype I] [DecidableEq I] in
theorem coordinateStrideHom_reflectsPairSums {d : ℤ} (hd : d ≠ 0) (Q : Set (I → ℤ)) :
    ReflectsPairSums (coordinateStrideHom d) Q := by
  intro a _ b _ c _ e _ h
  apply coordinateStrideHom_injective hd
  simpa only [map_add] using h

theorem finiteSupportGowersNorm_commonStride (q : ℕ) (c : I → ℤ)
    {d : ℕ} (hd : 0 < d) (H : I → ℕ) (f : (I → ℤ) → ℂ) :
    finiteSupportGowersNorm q (commonStrideBox c d H) f =
      finiteSupportGowersNorm q (integerBox H) (fun x => f (commonStridePoint c d x)) := by
  have he : commonStrideBox c d H =
      translateSupport c ((integerBox H).image (coordinateStrideHom (d : ℤ))) := by
    rw [commonStrideBox_eq_image]
    simp only [translateSupport, Finset.image_image]
    rfl
  rw [he, finiteSupportGowersNorm_translate]
  exact finiteSupportGowersNorm_image_map q (coordinateStrideHom (d : ℤ)) (integerBox H)
    (coordinateStrideHom_reflectsPairSums (by exact_mod_cast hd.ne') _) _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem commonStride_gowers_transfer (j : ℕ) (N H : I → ℕ) [∀ i, NeZero (N i)]
    (c : I → ℤ) {d : ℕ} (hd : 0 < d) (hH : ∀ i, 0 < H i)
    (hsub : ∀ i, integerProgressionSupport (c i) d (H i) ⊆ Finset.Ico (0 : ℤ) (N i))
    (f : (I → ℤ) → ℂ) (hf : ∀ x ∈ integerBox N, ‖f x‖ ≤ 1)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hlarge : η ≤ ((∏ i, H i : ℕ) : ℝ) / ((∏ i, 4 * (d * N i) : ℕ) : ℝ) *
      finiteSupportGowersNorm (j + 2) (integerBox H)
        (fun x => f (commonStridePoint c d x))) :
    (η / 2) ^ (2 ^ (j + 2) * Fintype.card I + 1) /
      (4 * (Fintype.card I + 1)) ^ Fintype.card I ≤
        finiteSupportGowersNorm (j + 2) (integerBox N) f := by
  let M : I → ℕ := fun i => 4 * (d * N i)
  let : NeZero d := ⟨hd.ne'⟩
  let : ∀ i, NeZero (M i) := fun i => inferInstanceAs (NeZero (4 * (d * N i)))
  have hdiv (i) : d ∣ M i := ⟨4 * N i, by dsimp only [M]; ring⟩
  have hQP : commonStrideBox c d H ⊆ integerBox N := by
    intro x hx
    exact (mem_integerBox N x).mpr (fun i => Finset.mem_Ico.mp
      (hsub i ((Fintype.mem_piFinset.mp hx) i)))
  have hembed : ReflectsPairSums (productZmodReduction M) (integerBox N : Set (I → ℤ)) := by
    change ReflectsPairSums (boxReduction (fun i => d * N i)) _
    apply (boxReduction_reflectsPairSums (fun i => d * N i)).mono
    intro x hx
    apply (mem_integerBox _ x).mpr
    intro i
    have hi := (mem_integerBox N x).mp hx i
    have hN : N i ≤ d * N i := by nlinarith
    exact ⟨hi.1, hi.2.trans_le (by exact_mod_cast hN)⟩
  apply finiteSupport_product_fiber_transfer M j (productZmodReduction M) (integerBox N)
    (commonStrideBox c d H) (commonStrideBox_nonempty c hd H hH) hQP hembed
    (productResidueHom M d hdiv) (fun i => (c i : ZMod d))
    (fun i => (c i : ZMod (M i))) (fun i => d * H i)
    (commonStrideBox_image_zmod M c d H hd hdiv) f hf hη hη1
  simpa only [commonStrideBox_card c hd H, Fintype.card_pi, ZMod.card,
    finiteSupportGowersNorm_commonStride (j + 2) c hd H f] using hlarge

end Erdos3

end

end OAI
