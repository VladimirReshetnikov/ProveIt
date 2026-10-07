import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Exponent

namespace OAI

section

namespace Erdos3

theorem finiteCharacter_exponent (G : Type*) [AddCommGroup G] [Finite G] :
    Monoid.exponent (AddChar G ℂ) = AddMonoid.exponent G := by
  apply Nat.dvd_antisymm
  · apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro χ
    ext x
    rw [AddChar.pow_apply, ← AddChar.map_nsmul_eq_pow, AddMonoid.exponent_nsmul_eq_zero]
    exact χ.map_zero_eq_one
  · apply AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero
    intro x
    apply AddChar.forall_apply_eq_zero.mp
    intro χ
    rw [AddChar.map_nsmul_eq_pow]
    have h := congrArg (fun ψ : AddChar G ℂ => ψ x) (Monoid.pow_exponent_eq_one χ)
    exact h

theorem exists_character_order_eq_exponent (G : Type*) [AddCommGroup G] [Finite G] :
    ∃ χ : AddChar G ℂ, orderOf χ = AddMonoid.exponent G := by
  obtain ⟨χ, hχ⟩ := Monoid.exists_orderOf_eq_exponent
    (G := AddChar G ℂ) Monoid.ExponentExists.of_finite
  exact ⟨χ, hχ.trans (finiteCharacter_exponent G)⟩

end Erdos3

end

section

namespace Erdos3

def characterPullback {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) : AddChar H ℂ →* AddChar G ℂ where
  toFun χ := χ.compAddMonoidHom f
  map_one' := rfl
  map_mul' _ _ := rfl

theorem characterPullback_order {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) (hf : Function.Surjective f) (χ : AddChar H ℂ) :
    orderOf (characterPullback f χ) = orderOf χ :=
  orderOf_injective (characterPullback f) (AddChar.compAddMonoidHom_injective_left f hf) χ

end Erdos3

end

section

namespace Erdos3

def zmodPiReduction {I : Type*} {n m : ℕ} (h : m ∣ n) :
    (I → ZMod n) →+ (I → ZMod m) :=
  AddMonoidHom.piMap fun _ => (ZMod.castHom h (ZMod m)).toAddMonoidHom

@[simp] theorem zmodPiReduction_apply {I : Type*} {n m : ℕ} (h : m ∣ n)
    (x : I → ZMod n) (i : I) :
    zmodPiReduction h x i = ZMod.castHom h (ZMod m) (x i) := rfl

theorem zmodPiReduction_surjective {I : Type*} {n m : ℕ} (h : m ∣ n) :
    Function.Surjective (zmodPiReduction (I := I) h) := by
  intro y
  choose x hx using fun i => ZMod.castHom_surjective h (y i)
  exact ⟨x, funext hx⟩

theorem zmodPiReduction_kernel_nsmul {I : Type*} {n m : ℕ} [NeZero n]
    (h : m ∣ n) (x : I → ZMod n) (hx : zmodPiReduction h x = 0) :
    ∃ y : I → ZMod n, m • y = x := by
  have hdvd (i : I) : m ∣ (x i).val := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    have hi := congrFun hx i
    simpa only [zmodPiReduction_apply, ZMod.castHom_apply, ZMod.cast_eq_val,
      Pi.zero_apply] using hi
  choose w hw using hdvd
  refine ⟨fun i => (w i : ZMod n), ?_⟩
  funext i
  change m • (w i : ZMod n) = x i
  rw [nsmul_eq_mul, ← Nat.cast_mul, ← hw i, ZMod.natCast_zmod_val]

theorem zmodPiReduction_kernel_character {I : Type*} {n m : ℕ} [NeZero n]
    (h : m ∣ n) (χ : AddChar (I → ZMod n) ℂ) (hχ : χ ^ m = 1)
    (x : I → ZMod n) (hx : zmodPiReduction h x = 0) : χ x = 1 := by
  obtain ⟨y, hy⟩ := zmodPiReduction_kernel_nsmul h x hx
  rw [← hy, AddChar.map_nsmul_eq_pow]
  exact congrArg (fun ψ : AddChar (I → ZMod n) ℂ => ψ y) hχ

theorem exists_zmodPiReduction_character {I : Type*} {n m : ℕ} [NeZero n]
    (h : m ∣ n) (χ : AddChar (I → ZMod n) ℂ) (hχ : χ ^ m = 1) :
    ∃ ψ : AddChar (I → ZMod m) ℂ,
      characterPullback (zmodPiReduction h) ψ = χ ∧ orderOf ψ = orderOf χ := by
  let q := zmodPiReduction (I := I) h
  let f := q.toMultiplicative
  have hf : Function.Surjective f := zmodPiReduction_surjective h
  let g := χ.toMonoidHom.toHomUnits
  have hker : f.ker ≤ g.ker := by
    intro x hx
    apply Units.ext
    change χ x.toAdd = 1
    exact zmodPiReduction_kernel_character h χ hχ x.toAdd hx
  let lifted := f.liftOfSurjective hf ⟨g, hker⟩
  let ψ : AddChar (I → ZMod m) ℂ :=
    AddChar.toMonoidHomEquiv.symm ((Units.coeHom ℂ).comp lifted)
  have heq : characterPullback q ψ = χ := by
    apply AddChar.ext
    intro x
    change (lifted (f (Multiplicative.ofAdd x)) : ℂ) = χ x
    simp only [lifted, MonoidHom.liftOfSurjective,
      MonoidHom.liftOfRightInverse_comp_apply]
    rfl
  refine ⟨ψ, heq, ?_⟩
  rw [← characterPullback_order q (zmodPiReduction_surjective h) ψ, heq]

theorem exists_primePower_character_descent {I : Type*} {p A a : ℕ}
    [NeZero (p ^ A)] (ha : a ≤ A) (χ : AddChar (I → ZMod (p ^ A)) ℂ)
    (hχ : orderOf χ = p ^ a) :
    ∃ ψ : AddChar (I → ZMod (p ^ a)) ℂ,
      characterPullback (zmodPiReduction (pow_dvd_pow p ha)) ψ = χ ∧
      orderOf ψ = p ^ a := by
  have hpow : χ ^ (p ^ a) = 1 := by
    rw [← hχ]
    exact pow_orderOf_eq_one χ
  obtain ⟨ψ, hψ, hord⟩ := exists_zmodPiReduction_character (pow_dvd_pow p ha) χ hpow
  exact ⟨ψ, hψ, hord.trans hχ⟩

end Erdos3

end

section

namespace Erdos3

theorem zmod_character_order_dvd {I : Type*} {N : ℕ}
    (χ : AddChar (I → ZMod N) ℂ) : orderOf χ ∣ N := by
  apply orderOf_dvd_of_pow_eq_one
  ext x
  rw [AddChar.pow_apply, ← AddChar.map_nsmul_eq_pow]
  have hx : N • x = 0 := by
    funext i
    simp only [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]
  rw [hx, AddChar.map_zero_eq_one, AddChar.one_apply]

theorem zmod_character_order_pos {I : Type*} {N : ℕ} [NeZero N]
    (χ : AddChar (I → ZMod N) ℂ) : 0 < orderOf χ := by
  apply Nat.pos_of_ne_zero
  intro hz
  have hdvd := zmod_character_order_dvd χ
  rw [hz, zero_dvd_iff] at hdvd
  exact NeZero.ne N hdvd

theorem exists_characterOrder_descent {I : Type*} {N : ℕ} [NeZero N]
    (χ : AddChar (I → ZMod N) ℂ) :
    ∃ ψ : AddChar (I → ZMod (orderOf χ)) ℂ,
      characterPullback (zmodPiReduction (zmod_character_order_dvd χ)) ψ = χ ∧
      orderOf ψ = orderOf χ ∧
      (∀ x, χ x = ψ (zmodPiReduction (zmod_character_order_dvd χ) x)) ∧
      ∀ b : I → ℤ, χ (fun i => (b i : ZMod N)) =
        ψ (fun i => (b i : ZMod (orderOf χ))) := by
  obtain ⟨ψ, hpull, horder⟩ := exists_zmodPiReduction_character
    (zmod_character_order_dvd χ) χ (pow_orderOf_eq_one χ)
  have hpoint (x : I → ZMod N) :
      χ x = ψ (zmodPiReduction (zmod_character_order_dvd χ) x) :=
    (congrArg (fun η : AddChar (I → ZMod N) ℂ => η x) hpull).symm
  refine ⟨ψ, hpull, horder, hpoint, ?_⟩
  intro b
  have hred : zmodPiReduction (zmod_character_order_dvd χ)
      (fun i => (b i : ZMod N)) = (fun i => (b i : ZMod (orderOf χ))) := by
    funext i
    exact map_intCast (ZMod.castHom (zmod_character_order_dvd χ) (ZMod (orderOf χ))) (b i)
  rw [hpoint, hred]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem stdAddChar_mul_modulus_ratio {n m d : ℕ} [NeZero n] [NeZero m] [NeZero d]
    (h : m ∣ n) (hn : n = m * d) (x : ZMod n) :
    ZMod.stdAddChar ((d : ZMod n) * x) =
      ZMod.stdAddChar (ZMod.castHom h (ZMod m) x) := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  rw [← Int.cast_natCast d, ← Int.cast_mul, ZMod.stdAddChar_coe,
    map_intCast, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  rw [hn, Nat.cast_mul]
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  field_simp

theorem stdAddChar_primePower_scaling {p A a : ℕ} [NeZero p]
    (ha : a ≤ A) (x : ZMod (p ^ A)) :
    ZMod.stdAddChar (((p ^ (A - a) : ℕ) : ZMod (p ^ A)) * x) =
      ZMod.stdAddChar (ZMod.castHom (pow_dvd_pow p ha) (ZMod (p ^ a)) x) :=
  stdAddChar_mul_modulus_ratio (pow_dvd_pow p ha) (pow_mul_pow_sub p ha).symm x

theorem stdAddChar_primePower_row_scaling {I : Type*} [Fintype I]
    {p A a : ℕ} [NeZero p] (ha : a ≤ A)
    (coeff : I → ZMod (p ^ a)) (x : I → ZMod (p ^ A)) :
    ZMod.stdAddChar (∑ i,
      ((p ^ (A - a) : ℕ) : ZMod (p ^ A)) * ((coeff i).val : ZMod (p ^ A)) * x i) =
    ZMod.stdAddChar (∑ i, coeff i * zmodPiReduction (pow_dvd_pow p ha) x i) := by
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [stdAddChar_primePower_scaling ha]
  congr 1
  simp only [map_sum, map_mul, map_natCast, ZMod.natCast_zmod_val,
    zmodPiReduction_apply]

end Erdos3

end

end OAI
