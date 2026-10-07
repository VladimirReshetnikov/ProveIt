import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import OAI.Combinatorics.Progressions.Estimates.FiniteProductImageDecay

namespace OAI

section

namespace Erdos3
open scoped BigOperators

theorem zmodAddEquiv_apply_eq_std {q : ℕ} [NeZero q] (a x : ZMod q) :
    AddChar.zmodAddEquiv a x = ZMod.stdAddChar (a * x) := by
  rfl

theorem exists_zmod_character_row {I : Type*} [Fintype I] [DecidableEq I]
    {q : ℕ} [NeZero q] (χ : AddChar (I → ZMod q) ℂ) :
    ∃ coeff : I → ZMod q, ∀ x, χ x = ZMod.stdAddChar (∑ i, coeff i * x i) := by
  choose coeff hcoeff using fun i => AddChar.zmodAddEquiv.surjective
    (finiteProductCharacterCoordinate χ i)
  refine ⟨coeff, ?_⟩
  intro x
  have h := congrArg (fun ψ : AddChar (I → ZMod q) ℂ => ψ x)
    (finiteProductCharacter_decomposition χ)
  calc
    χ x = ∏ i, finiteProductCharacterCoordinate χ i (x i) := h.symm
    _ = ∏ i, ZMod.stdAddChar (coeff i * x i) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [← hcoeff i, zmodAddEquiv_apply_eq_std]
    _ = ZMod.stdAddChar (∑ i, coeff i * x i) := by
      exact (map_sum ZMod.stdAddChar.toAddMonoidHom (fun i => coeff i * x i) Finset.univ).symm

theorem primePower_character_row_primitive {I : Type*} [Fintype I]
    {p a : ℕ} (hp : p.Prime) (ha : 0 < a) [NeZero (p ^ a)]
    (χ : AddChar (I → ZMod (p ^ a)) ℂ) (coeff : I → ZMod (p ^ a))
    (hrow : ∀ x, χ x = ZMod.stdAddChar (∑ i, coeff i * x i))
    (horder : orderOf χ = p ^ a) : ∃ i, IsUnit (coeff i) := by
  classical
  by_contra! hunit
  have hdiv (i : I) : p ∣ (coeff i).val := by
    by_contra hh
    apply hunit i
    rw [← ZMod.natCast_zmod_val (coeff i)]
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp ha).mpr hh
  have hkill (i : I) : (p ^ (a - 1) : ℕ) * coeff i = (0 : ZMod (p ^ a)) := by
    obtain ⟨b, hb⟩ := hdiv i
    rw [← ZMod.natCast_zmod_val (coeff i), hb, ← Nat.cast_mul,
      ← Nat.mul_assoc, ← pow_succ, Nat.sub_add_cancel (by omega)]
    simp only [Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have hpow : χ ^ (p ^ (a - 1)) = 1 := by
    ext x
    rw [AddChar.pow_apply, ← AddChar.map_nsmul_eq_pow, hrow, AddChar.one_apply]
    have hz : (∑ i, coeff i * ((p ^ (a - 1)) • x) i) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      simp only [Pi.smul_apply, nsmul_eq_mul]
      rw [mul_left_comm, ← mul_assoc, hkill, zero_mul]
    rw [hz, AddChar.map_zero_eq_one]
  have hdvd := orderOf_dvd_of_pow_eq_one hpow
  rw [horder] at hdvd
  have hle := Nat.le_of_dvd (pow_pos hp.pos _) hdvd
  have hlt : p ^ (a - 1) < p ^ a := Nat.pow_lt_pow_right hp.one_lt (by omega)
  omega

theorem exists_primePower_character_primitive_row {I : Type*} [Fintype I]
    {p a : ℕ} (hp : p.Prime) (ha : 0 < a) [NeZero (p ^ a)]
    (χ : AddChar (I → ZMod (p ^ a)) ℂ) (horder : orderOf χ = p ^ a) :
    ∃ coeff : I → ZMod (p ^ a), (∃ i, IsUnit (coeff i)) ∧
      ∀ x, χ x = ZMod.stdAddChar (∑ i, coeff i * x i) := by
  classical
  obtain ⟨coeff, hcoeff⟩ := exists_zmod_character_row χ
  exact ⟨coeff, primePower_character_row_primitive hp ha χ coeff hcoeff horder, hcoeff⟩

theorem primePower_primitive_row_cast {I : Type*} {p a b : ℕ} (hab : b ≤ a)
    (coeff : I → ZMod (p ^ a)) (hcoeff : ∃ i, IsUnit (coeff i)) :
    ∃ i, IsUnit (ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ b)) (coeff i)) := by
  obtain ⟨i, hi⟩ := hcoeff
  exact ⟨i, hi.map (ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ b)))⟩

theorem exists_primePower_character_conductor_row {I : Type*} [Fintype I]
    {p A a : ℕ} (hp : p.Prime) (ha : a ≤ A) [NeZero (p ^ A)] [NeZero (p ^ a)]
    (χ : AddChar (I → ZMod (p ^ A)) ℂ) (horder : orderOf χ = p ^ a) :
    ∃ coeff : I → ZMod (p ^ a),
      (0 < a → ∀ {b : ℕ} (hab : b ≤ a),
        ∃ i, IsUnit (ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ b)) (coeff i))) ∧
      ∀ x, χ x = ZMod.stdAddChar
        (∑ i, coeff i * ZMod.castHom (pow_dvd_pow p ha) (ZMod (p ^ a)) (x i)) := by
  classical
  obtain ⟨ψ, hψ, hord⟩ := exists_primePower_character_descent ha χ horder
  obtain ⟨coeff, hcoeff⟩ := exists_zmod_character_row ψ
  refine ⟨coeff, ?_, ?_⟩
  · intro ha0 b hab
    exact primePower_primitive_row_cast hab coeff
      (primePower_character_row_primitive hp ha0 ψ coeff hcoeff hord)
  · intro x
    calc
      χ x = ψ (zmodPiReduction (pow_dvd_pow p ha) x) :=
        (congrArg (fun θ : AddChar (I → ZMod (p ^ A)) ℂ => θ x) hψ).symm
      _ = _ := hcoeff _

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators

theorem exists_primePower_tagged_conductor_rows
    {Tag : Type*} [Fintype Tag] [DecidableEq Tag]
    {I : Tag → Type*} [∀ j, Fintype (I j)]
    {p A : ℕ} [NeZero p] (hp : p.Prime)
    (χ : AddChar (∀ j, I j → ZMod (p ^ A)) ℂ) :
    ∃ (depth : Tag → ℕ) (hdepth : ∀ j, depth j ≤ A)
      (coeff : ∀ j, I j → ZMod (p ^ depth j)),
      (∀ j, orderOf (finiteProductCharacterCoordinate χ j) = p ^ depth j) ∧
      (∀ j, 0 < depth j → ∀ {b : ℕ} (hb : b ≤ depth j),
        ∃ i, IsUnit (ZMod.castHom (pow_dvd_pow p hb) (ZMod (p ^ b)) (coeff j i))) ∧
      (∀ j (x : I j → ZMod (p ^ A)), finiteProductCharacterCoordinate χ j x =
        ZMod.stdAddChar (∑ i, coeff j i *
          ZMod.castHom (pow_dvd_pow p (hdepth j)) (ZMod (p ^ depth j)) (x i))) ∧
      ∀ x, χ x = ∏ j, ZMod.stdAddChar (∑ i, coeff j i *
        ZMod.castHom (pow_dvd_pow p (hdepth j)) (ZMod (p ^ depth j)) (x j i)) := by
  classical
  have hkill : ∀ j (x : I j → ZMod (p ^ A)), (p ^ A) • x = 0 := by
    intro j x
    ext i
    simp only [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]
  have horderDiv (j : Tag) : orderOf (finiteProductCharacterCoordinate χ j) ∣ p ^ A :=
    finiteProductCharacterCoordinate_order_dvd χ (fun _ => p ^ A) hkill j
  choose depth hdepth horder using fun j => (Nat.dvd_prime_pow hp).mp (horderDiv j)
  choose coeff hcoeff hrow using fun j =>
    exists_primePower_character_conductor_row hp (hdepth j)
      (finiteProductCharacterCoordinate χ j) (horder j)
  refine ⟨depth, hdepth, coeff, horder, hcoeff, hrow, ?_⟩
  intro x
  calc
    χ x = ∏ j, finiteProductCharacterCoordinate χ j (x j) :=
      (congrArg (fun θ : AddChar (∀ j, I j → ZMod (p ^ A)) ℂ => θ x)
        (finiteProductCharacter_decomposition χ)).symm
    _ = _ := Finset.prod_congr rfl (fun j _ => hrow j (x j))

theorem exists_primePower_tagged_ambient_rows
    {Tag : Type*} [Fintype Tag] [DecidableEq Tag]
    {I : Tag → Type*} [∀ j, Fintype (I j)]
    {p A : ℕ} [NeZero p] (hp : p.Prime)
    (χ : AddChar (∀ j, I j → ZMod (p ^ A)) ℂ) :
    ∃ (depth : Tag → ℕ) (hdepth : ∀ j, depth j ≤ A)
      (coeff : ∀ j, I j → ZMod (p ^ A)),
      (∀ j, orderOf (finiteProductCharacterCoordinate χ j) = p ^ depth j) ∧
      (∀ j, 0 < depth j → ∀ {b : ℕ} (hb : b ≤ depth j),
        ∃ i, IsUnit (ZMod.castHom (pow_dvd_pow p (hb.trans (hdepth j)))
          (ZMod (p ^ b)) (coeff j i))) ∧
      ∀ x, χ x = ZMod.stdAddChar
        (∑ j, ((p ^ (A - depth j) : ℕ) : ZMod (p ^ A)) * ∑ i, coeff j i * x j i) := by
  classical
  obtain ⟨depth, hdepth, c, horder, hunit, hrow, hphase⟩ :=
    exists_primePower_tagged_conductor_rows hp χ
  let coeff := fun j i => ((c j i).val : ZMod (p ^ A))
  refine ⟨depth, hdepth, coeff, horder, ?_, ?_⟩
  · intro j hj b hb
    obtain ⟨i, hi⟩ := hunit j hj hb
    refine ⟨i, ?_⟩
    simpa only [coeff, map_natCast, ZMod.castHom_apply, ZMod.cast_eq_val] using hi
  · intro x
    rw [hphase]
    calc
      _ = ∏ j, ZMod.stdAddChar
          (((p ^ (A - depth j) : ℕ) : ZMod (p ^ A)) * ∑ i, coeff j i * x j i) := by
        apply Finset.prod_congr rfl
        intro j _
        simpa only [coeff, zmodPiReduction_apply, mul_assoc, ← Finset.mul_sum] using
          (stdAddChar_primePower_row_scaling (hdepth j) (c j) (x j)).symm
      _ = ZMod.stdAddChar (∑ j, ((p ^ (A - depth j) : ℕ) : ZMod (p ^ A)) *
          ∑ i, coeff j i * x j i) :=
        (map_sum ZMod.stdAddChar.toAddMonoidHom
          (fun j => ((p ^ (A - depth j) : ℕ) : ZMod (p ^ A)) *
            ∑ i, coeff j i * x j i) Finset.univ).symm

end Erdos3

end

end OAI
