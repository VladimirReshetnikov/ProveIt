import OAI.Combinatorics.Progressions.Geometry.SupportedCubeEquivTransport

namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] [DecidableEq A]

def translateSupport (a : A) (Q : Finset A) : Finset A := Q.image (fun x ↦ a + x)

theorem mem_translateSupport (a : A) (Q : Finset A) (x : A) :
    x ∈ translateSupport a Q ↔ x - a ∈ Q := by
  rw [translateSupport, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨x - a, hx, by abel⟩

theorem card_translateSupport (a : A) (Q : Finset A) : (translateSupport a Q).card = Q.card :=
  Finset.card_image_of_injective Q (fun _ _ h ↦ add_left_cancel h)

def supportedCubeTranslateEquiv (j : ℕ) (Q : Finset A) (a : A) :
    SupportedCube j (Q : Set A) ≃ SupportedCube j (translateSupport a Q : Set A) where
  toFun p := ⟨(p.val.1, a + p.val.2), fun ω ↦ by
    apply (mem_translateSupport a Q _).mpr
    simpa only [Finset.mem_coe, add_sub_cancel_left, add_assoc, add_sub_cancel_right] using p.property ω⟩
  invFun p := ⟨(p.val.1, p.val.2 - a), fun ω ↦ by
    have h := (mem_translateSupport a Q _).mp (p.property ω)
    simpa only [Finset.mem_coe, sub_add_eq_add_sub] using h⟩
  left_inv p := by
    apply Subtype.ext
    change (p.val.1, (a + p.val.2) - a) = p.val
    apply Prod.ext
    · rfl
    · simp
  right_inv p := by
    apply Subtype.ext
    change (p.val.1, a + (p.val.2 - a)) = p.val
    apply Prod.ext
    · rfl
    · simp

theorem card_supportedCube_translate (j : ℕ) (Q : Finset A) (a : A) :
    Nat.card (SupportedCube j (translateSupport a Q : Set A)) =
      Nat.card (SupportedCube j (Q : Set A)) :=
  (Nat.card_congr (supportedCubeTranslateEquiv j Q a)).symm

omit [DecidableEq A] in
theorem mixedCubeProduct_translate {j : ℕ} (F : (Fin j → Bool) → A → ℂ)
    (a : A) (ds : Fin j → A) (x : A) :
    mixedCubeProduct F ds (a + x) = mixedCubeProduct (fun ω y ↦ F ω (a + y)) ds x := by
  simp only [mixedCubeProduct, add_assoc]

theorem supportedCubeSum_translate (j : ℕ) (Q : Finset A) (a : A)
    (F : (Fin j → Bool) → A → ℂ) :
    supportedCubeSum j (translateSupport a Q : Set A) F =
      supportedCubeSum j (Q : Set A) (fun ω x ↦ F ω (a + x)) := by
  symm
  apply Fintype.sum_equiv (supportedCubeTranslateEquiv j Q a)
  intro p
  exact (mixedCubeProduct_translate F a p.val.1 p.val.2).symm

theorem finiteSupportGowersNorm_translate (j : ℕ) (Q : Finset A) (a : A) (f : A → ℂ) :
    finiteSupportGowersNorm j (translateSupport a Q) f =
      finiteSupportGowersNorm j Q (fun x ↦ f (a + x)) := by
  simp only [finiteSupportGowersNorm, supportedCubeSum_translate, card_supportedCube_translate]

theorem ReflectsPairSums.translate {φ : A →+ B} {Q : Finset A}
    (hφ : ReflectsPairSums φ (Q : Set A)) (a : A) :
    ReflectsPairSums φ (translateSupport a Q : Set A) := by
  intro b hb c hc d hd e he hrel
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp he
  simp only [map_add] at hrel
  have hr : φ x + φ y = φ z + φ w := by
    apply add_left_cancel (a := φ a + φ a)
    calc
      _ = (φ a + φ x) + (φ a + φ y) := by abel
      _ = (φ a + φ z) + (φ a + φ w) := hrel
      _ = _ := by abel
  have hsum := hφ x hx y hy z hz w hw hr
  calc
    (a + x) + (a + y) = (a + a) + (x + y) := by abel
    _ = (a + a) + (z + w) := by rw [hsum]
    _ = _ := by abel

end Erdos3

end

end OAI
