import Mathlib.Algebra.Algebra.NonUnitalSubalgebra
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3
variable {A B : Type*} [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]

def truncatedSeriesCon (A : Type*) [Ring A] (s : ℕ) : RingCon (PowerSeries A) where
  r f g := ∀ n, n ≤ s → PowerSeries.coeff n f = PowerSeries.coeff n g
  iseqv := ⟨fun _ _ _ => rfl, fun h n hn => (h n hn).symm,
    fun h₁ h₂ n hn => (h₁ n hn).trans (h₂ n hn)⟩
  add' hf hg n hn := by rw [map_add, map_add, hf n hn, hg n hn]
  mul' hf hg n hn := by
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro ij hij
    have he := Finset.mem_antidiagonal.mp hij
    rw [hf ij.1 (by omega), hg ij.2 (by omega)]

abbrev TruncatedSeries (A : Type*) [Ring A] (s : ℕ) := (truncatedSeriesCon A s).Quotient

noncomputable def truncatedSeriesMk (s : ℕ) : PowerSeries A →ₐ[ℚ] TruncatedSeries A s :=
  (truncatedSeriesCon A s).mkₐ ℚ

theorem truncatedSeriesMk_surjective (s : ℕ) :
    Function.Surjective (truncatedSeriesMk (A := A) s) :=
  (truncatedSeriesCon A s).mkₐ_surjective

theorem truncatedSeriesMk_eq_iff (s : ℕ) (f g : PowerSeries A) :
    truncatedSeriesMk s f = truncatedSeriesMk s g ↔
      ∀ n, n ≤ s → PowerSeries.coeff n f = PowerSeries.coeff n g :=
  (truncatedSeriesCon A s).eq

noncomputable def truncatedSeriesCoeff (s n : ℕ) (hn : n ≤ s) :
    TruncatedSeries A s →ₗ[ℚ] A where
  toFun := Quotient.lift (PowerSeries.coeff n) (fun _ _ h => h n hn)
  map_add' p q := by
    obtain ⟨f, rfl⟩ := truncatedSeriesMk_surjective s p
    obtain ⟨g, rfl⟩ := truncatedSeriesMk_surjective s q
    exact map_add (PowerSeries.coeff n) f g
  map_smul' r p := by
    obtain ⟨f, rfl⟩ := truncatedSeriesMk_surjective s p
    exact PowerSeries.coeff_smul n f r

@[simp] theorem truncatedSeriesCoeff_mk (s n : ℕ) (hn : n ≤ s) (f : PowerSeries A) :
    truncatedSeriesCoeff s n hn (truncatedSeriesMk s f) = PowerSeries.coeff n f := rfl

theorem truncatedSeries_ext {s : ℕ} {p q : TruncatedSeries A s}
    (h : ∀ n (hn : n ≤ s), truncatedSeriesCoeff s n hn p = truncatedSeriesCoeff s n hn q) :
    p = q := by
  obtain ⟨f, rfl⟩ := truncatedSeriesMk_surjective s p
  obtain ⟨g, rfl⟩ := truncatedSeriesMk_surjective s q
  exact (truncatedSeriesMk_eq_iff s f g).mpr h

noncomputable def seriesConstantCoeff : PowerSeries A →ₐ[ℚ] A :=
  { PowerSeries.constantCoeff with
    commutes' r := by
      change PowerSeries.constantCoeff (PowerSeries.C (algebraMap ℚ A r)) = _
      exact PowerSeries.constantCoeff_C _ }

noncomputable def truncatedSeriesConstantCoeff (s : ℕ) : TruncatedSeries A s →ₐ[ℚ] A :=
  (truncatedSeriesCon A s).liftₐ seriesConstantCoeff (by
    intro f g h
    change PowerSeries.constantCoeff f = PowerSeries.constantCoeff g
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using h 0 (Nat.zero_le s))

@[simp] theorem truncatedSeriesConstantCoeff_mk (s : ℕ) (f : PowerSeries A) :
    truncatedSeriesConstantCoeff s (truncatedSeriesMk s f) = PowerSeries.constantCoeff f := rfl

noncomputable def truncatedSeriesMap (s : ℕ) (φ : A →ₐ[ℚ] B) :
    TruncatedSeries A s →ₐ[ℚ] TruncatedSeries B s :=
  (truncatedSeriesCon A s).liftₐ ((truncatedSeriesMk s).comp (PowerSeries.mapAlgHom φ)) (by
    intro f g h
    apply (truncatedSeriesMk_eq_iff s _ _).mpr
    intro n hn
    change φ (PowerSeries.coeff n f) = φ (PowerSeries.coeff n g)
    rw [h n hn])

@[simp] theorem truncatedSeriesMap_mk (s : ℕ) (φ : A →ₐ[ℚ] B) (f : PowerSeries A) :
    truncatedSeriesMap s φ (truncatedSeriesMk s f) =
      truncatedSeriesMk s (PowerSeries.mapAlgHom φ f) := rfl

@[simp] theorem truncatedSeriesCoeff_map (s n : ℕ) (hn : n ≤ s) (φ : A →ₐ[ℚ] B)
    (p : TruncatedSeries A s) :
    truncatedSeriesCoeff s n hn (truncatedSeriesMap s φ p) =
      φ (truncatedSeriesCoeff s n hn p) := by
  obtain ⟨f, rfl⟩ := truncatedSeriesMk_surjective s p
  simp [PowerSeries.mapAlgHom_apply]

@[simp] theorem truncatedSeriesConstantCoeff_map (s : ℕ) (φ : A →ₐ[ℚ] B)
    (p : TruncatedSeries A s) :
    truncatedSeriesConstantCoeff s (truncatedSeriesMap s φ p) =
      φ (truncatedSeriesConstantCoeff s p) := by
  obtain ⟨f, rfl⟩ := truncatedSeriesMk_surjective s p
  change PowerSeries.constantCoeff (PowerSeries.map φ.toRingHom f) = _
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff]
  rfl

noncomputable def truncatedSeriesPositive (s : ℕ) : NonUnitalSubalgebra ℚ (TruncatedSeries A s) where
  carrier := {p | truncatedSeriesConstantCoeff s p = 0}
  zero_mem' := map_zero _
  add_mem' hp hq := by
    change truncatedSeriesConstantCoeff s _ = 0 at hp hq ⊢
    rw [map_add, hp, hq, zero_add]
  smul_mem' r p hp := by
    change truncatedSeriesConstantCoeff s _ = 0 at hp ⊢
    rw [map_smul, hp, smul_zero]
  mul_mem' hp hq := by
    change truncatedSeriesConstantCoeff s _ = 0 at hp hq ⊢
    rw [map_mul, hp, hq, zero_mul]

@[simp] theorem mem_truncatedSeriesPositive {s : ℕ} {p : TruncatedSeries A s} :
    p ∈ truncatedSeriesPositive s ↔ truncatedSeriesConstantCoeff s p = 0 := Iff.rfl

theorem truncatedSeriesPositive_pow {s : ℕ} {p : TruncatedSeries A s}
    (hp : p ∈ truncatedSeriesPositive s) : p ^ (s + 1) = 0 := by
  obtain ⟨f, rfl⟩ := truncatedSeriesMk_surjective s p
  change PowerSeries.constantCoeff f = 0 at hp
  rw [← map_pow, ← map_zero (truncatedSeriesMk s)]
  apply (truncatedSeriesMk_eq_iff s _ _).mpr
  intro n hn
  rw [map_zero]
  apply PowerSeries.coeff_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast (Nat.lt_succ_of_le hn))
    (PowerSeries.le_order_pow_of_constantCoeff_eq_zero (s + 1) hp)

theorem truncatedSeriesPositive_nilpotent {s : ℕ} {p : TruncatedSeries A s}
    (hp : p ∈ truncatedSeriesPositive s) : IsNilpotent p :=
  ⟨s + 1, truncatedSeriesPositive_pow hp⟩

theorem truncatedSeriesMap_positive (s : ℕ) (φ : A →ₐ[ℚ] B)
    {p : TruncatedSeries A s} (hp : p ∈ truncatedSeriesPositive s) :
    truncatedSeriesMap s φ p ∈ truncatedSeriesPositive s := by
  rw [mem_truncatedSeriesPositive, truncatedSeriesConstantCoeff_map,
    mem_truncatedSeriesPositive.mp hp, map_zero]

end Erdos3

end

end OAI
