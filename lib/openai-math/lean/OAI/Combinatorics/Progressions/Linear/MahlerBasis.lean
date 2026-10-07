import Mathlib.Analysis.Convex.Gauge
import Mathlib.LinearAlgebra.FreeModule.PID

namespace OAI

section

namespace Erdos3.IntegerBasisReduction.Mahler

open scoped BigOperators
open Module

abbrev IntegralPoint (n : ℕ) := Fin n → ℤ

def integralEmbed {n : ℕ} (x : IntegralPoint n) : Fin n → ℝ :=
  fun i ↦ (x i : ℝ)

@[simp]
theorem integralEmbed_zero {n : ℕ} :
    integralEmbed (0 : IntegralPoint n) = 0 := by
  ext i
  simp [integralEmbed]

@[simp]
theorem integralEmbed_add {n : ℕ} (x y : IntegralPoint n) :
    integralEmbed (x + y) = integralEmbed x + integralEmbed y := by
  ext i
  simp [integralEmbed]

@[simp]
theorem integralEmbed_zsmul {n : ℕ} (a : ℤ) (x : IntegralPoint n) :
    integralEmbed (a • x) = (a : ℝ) • integralEmbed x := by
  ext i
  simp [integralEmbed]

def AdmitsIndependent {n : ℕ} (p : Seminorm ℝ (Fin n → ℝ))
    (k : ℕ) (r : ℝ) : Prop :=
  ∃ v : Fin k → IntegralPoint n,
    LinearIndependent ℝ (fun j ↦ integralEmbed (v j)) ∧
      ∀ j, p (integralEmbed (v j)) ≤ r

noncomputable def successiveMinimum {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (i : Fin n) : ℝ :=
  sInf {r : ℝ | AdmitsIndependent p (i.val + 1) r}

theorem AdmitsIndependent.mono {n k : ℕ}
    {p : Seminorm ℝ (Fin n → ℝ)} {r R : ℝ}
    (h : AdmitsIndependent p k r) (hrR : r ≤ R) :
    AdmitsIndependent p k R := by
  obtain ⟨v, hvli, hvr⟩ := h
  exact ⟨v, hvli, fun j ↦ (hvr j).trans hrR⟩

theorem AdmitsIndependent.nonneg {n k : ℕ}
    {p : Seminorm ℝ (Fin n → ℝ)} {r : ℝ}
    (hk : 0 < k) (h : AdmitsIndependent p k r) : 0 ≤ r := by
  obtain ⟨v, _hvli, hvr⟩ := h
  exact (apply_nonneg p (integralEmbed (v ⟨0, hk⟩))).trans (hvr ⟨0, hk⟩)

theorem successiveMinimum_nonneg {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (i : Fin n) :
    0 ≤ successiveMinimum p i := by
  rw [successiveMinimum]
  exact Real.sInf_nonneg fun _r hr ↦
    hr.nonneg (Nat.succ_pos i.val)

theorem successiveMinimum_le_of_admits {n : ℕ}
    {p : Seminorm ℝ (Fin n → ℝ)} {i : Fin n} {r : ℝ}
    (h : AdmitsIndependent p (i.val + 1) r) :
    successiveMinimum p i ≤ r := by
  rw [successiveMinimum]
  exact csInf_le
    ⟨0, fun R hR ↦ hR.nonneg (Nat.succ_pos i.val)⟩ h

noncomputable def mahlerFactor {n : ℕ} (i : Fin n) : ℝ :=
  if i.val = 0 then 1 else (i.val + 1 : ℝ) / 2

@[simp]
theorem mahlerFactor_zero {n : ℕ} (i : Fin n) (hi : i.val = 0) :
    mahlerFactor i = 1 := by
  simp [mahlerFactor, hi]

theorem mahlerFactor_of_pos {n : ℕ} (i : Fin n) (hi : 0 < i.val) :
    mahlerFactor i = (i.val + 1 : ℝ) / 2 := by
  simp [mahlerFactor, Nat.ne_of_gt hi]

theorem mahlerFactor_nonneg {n : ℕ} (i : Fin n) :
    0 ≤ mahlerFactor i := by
  by_cases hi : i.val = 0
  · rw [mahlerFactor_zero i hi]
    positivity
  · rw [mahlerFactor_of_pos i (Nat.pos_of_ne_zero hi)]
    positivity

theorem mahlerFactor_le_rank {n : ℕ} (i : Fin n) :
    mahlerFactor i ≤ (n : ℝ) := by
  by_cases hi : i.val = 0
  · rw [mahlerFactor_zero i hi]
    exact_mod_cast (show 1 ≤ n by omega)
  · rw [mahlerFactor_of_pos i (Nat.pos_of_ne_zero hi)]
    have hin : i.val + 1 ≤ n := i.isLt
    have hin' : (i.val + 1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hin
    nlinarith [show (0 : ℝ) ≤ n by positivity]

def IsDefinite {n : ℕ} (p : Seminorm ℝ (Fin n → ℝ)) : Prop :=
  ∀ x, p x = 0 → x = 0

theorem isDefinite_gaugeSeminorm {n : ℕ} {s : Set (Fin n → ℝ)}
    (hs₀ : Balanced ℝ s) (hs₁ : Convex ℝ s) (hs₂ : Absorbent ℝ s)
    (hb : Bornology.IsVonNBounded ℝ s) :
    IsDefinite (gaugeSeminorm hs₀ hs₁ hs₂) := by
  intro x hx
  exact (gauge_eq_zero hs₂ hb).mp hx

def IsMahlerBasis {n : ℕ} (p : Seminorm ℝ (Fin n → ℝ))
    (b : Basis (Fin n) ℤ (IntegralPoint n)) : Prop :=
  ∀ i, p (integralEmbed (b i)) ≤
    mahlerFactor i * successiveMinimum p i

def MahlerBasisStatement : Prop :=
  ∀ (n : ℕ) (p : Seminorm ℝ (Fin n → ℝ)),
    IsDefinite p →
      ∃ b : Basis (Fin n) ℤ (IntegralPoint n), IsMahlerBasis p b

theorem exists_isMahlerBasis_zero (p : Seminorm ℝ (Fin 0 → ℝ)) :
    ∃ b : Basis (Fin 0) ℤ (IntegralPoint 0), IsMahlerBasis p b := by
  refine ⟨Pi.basisFun ℤ (Fin 0), ?_⟩
  intro i
  exact Fin.elim0 i

theorem exists_isMahlerBasis_one (p : Seminorm ℝ (Fin 1 → ℝ)) :
    ∃ b : Basis (Fin 1) ℤ (IntegralPoint 1), IsMahlerBasis p b := by
  let b : Basis (Fin 1) ℤ (IntegralPoint 1) := Pi.basisFun ℤ (Fin 1)
  let u : IntegralPoint 1 := b 0
  have hu_real : integralEmbed u = Pi.basisFun ℝ (Fin 1) 0 := by
    ext j
    fin_cases j
    simp [u, b, integralEmbed]
  have hu_ne : integralEmbed u ≠ 0 := by
    rw [hu_real]
    exact (Pi.basisFun ℝ (Fin 1)).ne_zero 0
  have hadmits :
      AdmitsIndependent p 1 (p (integralEmbed u)) := by
    refine ⟨fun _ ↦ u, ?_, fun _ ↦ le_rfl⟩
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have hgj : g 0 = 0 := by
      by_contra hg0
      apply hu_ne
      have hsmul : g 0 • integralEmbed u = 0 := by
        simpa using hg
      exact (smul_eq_zero.mp hsmul).resolve_left hg0
    simpa [Subsingleton.elim j 0] using hgj
  refine ⟨b, ?_⟩
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rw [mahlerFactor_zero (0 : Fin 1) rfl, one_mul]
  change p (integralEmbed u) ≤ successiveMinimum p 0
  rw [successiveMinimum]
  refine le_csInf ⟨p (integralEmbed u), hadmits⟩ ?_
  intro r hr
  obtain ⟨v, hvli, hvr⟩ := hr
  let z : ℤ := v 0 0
  have hz : z ≠ 0 := by
    intro hz0
    have hv0 : integralEmbed (v 0) = 0 := by
      ext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      change ((v 0 0 : ℤ) : ℝ) = 0
      exact_mod_cast hz0
    exact (hvli.ne_zero 0) hv0
  have hv_eq : integralEmbed (v 0) = (z : ℝ) • integralEmbed u := by
    ext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simp [integralEmbed, u, b, z]
  have hzabs_int : (1 : ℤ) ≤ |z| := by
    have : (0 : ℤ) < |z| := abs_pos.mpr hz
    omega
  have hzabs_real : (1 : ℝ) ≤ |(z : ℝ)| := by
    exact_mod_cast hzabs_int
  calc
    p (integralEmbed u) ≤ |(z : ℝ)| * p (integralEmbed u) := by
      nlinarith [apply_nonneg p (integralEmbed u)]
    _ = p ((z : ℝ) • integralEmbed u) := by
      rw [map_smul_eq_mul, Real.norm_eq_abs]
    _ = p (integralEmbed (v 0)) := by rw [hv_eq]
    _ ≤ r := hvr 0

theorem IsMahlerBasis.first {n : ℕ} {p : Seminorm ℝ (Fin n → ℝ)}
    {b : Basis (Fin n) ℤ (IntegralPoint n)} (hb : IsMahlerBasis p b)
    (i : Fin n) (hi : i.val = 0) :
    p (integralEmbed (b i)) ≤ successiveMinimum p i := by
  simpa [IsMahlerBasis, mahlerFactor, hi] using hb i

theorem IsMahlerBasis.later {n : ℕ} {p : Seminorm ℝ (Fin n → ℝ)}
    {b : Basis (Fin n) ℤ (IntegralPoint n)} (hb : IsMahlerBasis p b)
    (i : Fin n) (hi : 0 < i.val) :
    p (integralEmbed (b i)) ≤
      (i.val + 1 : ℝ) / 2 * successiveMinimum p i := by
  simpa [IsMahlerBasis, mahlerFactor, Nat.ne_of_gt hi] using hb i

theorem IsMahlerBasis.le_rank_mul_successiveMinimum {n : ℕ}
    {p : Seminorm ℝ (Fin n → ℝ)}
    {b : Basis (Fin n) ℤ (IntegralPoint n)} (hb : IsMahlerBasis p b)
    (i : Fin n) :
    p (integralEmbed (b i)) ≤ (n : ℝ) * successiveMinimum p i := by
  exact (hb i).trans <| mul_le_mul_of_nonneg_right
    (mahlerFactor_le_rank i) (successiveMinimum_nonneg p i)

theorem seminorm_sum_le {n : ℕ} {E : Type*} [AddCommGroup E]
    [Module ℝ E] (p : Seminorm ℝ E) (a : Fin n → ℝ) (e : Fin n → E) :
    p (∑ i, a i • e i) ≤ ∑ i, |a i| * p (e i) := by
  calc
    p (∑ i, a i • e i) ≤ ∑ i, p (a i • e i) :=
      Finset.le_sum_of_subadditive p (by simp)
        (fun x y ↦ map_add_le_add p x y) Finset.univ (fun i ↦ a i • e i)
    _ = ∑ i, |a i| * p (e i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul_eq_mul]
      exact congrArg (fun t : ℝ ↦ t * p (e i)) (Real.norm_eq_abs (a i))

theorem seminorm_sum_basis_le {n : ℕ} {E : Type*} [AddCommGroup E]
    [Module ℝ E] (p : Seminorm ℝ E) (a : Fin n → ℝ) (e : Fin n → E)
    (M : ℝ) (hM : ∀ i, |a i| * p (e i) ≤ M) :
    p (∑ i, a i • e i) ≤ (n : ℝ) * M := by
  refine (seminorm_sum_le p a e).trans ?_
  calc
    (∑ i, |a i| * p (e i)) ≤ ∑ _i : Fin n, M :=
      Finset.sum_le_sum fun i _ ↦ hM i
    _ = (n : ℝ) * M := by simp

theorem seminorm_sum_integralBasis_le {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ))
    (b : Basis (Fin n) ℤ (IntegralPoint n)) (a : Fin n → ℝ)
    (M : ℝ)
    (hM : ∀ i, |a i| * p (integralEmbed (b i)) ≤ M) :
    p (∑ i, a i • integralEmbed (b i)) ≤ (n : ℝ) * M :=
  seminorm_sum_basis_le p a (fun i ↦ integralEmbed (b i)) M hM

theorem IsMahlerBasis.seminorm_sum_le {n : ℕ}
    {p : Seminorm ℝ (Fin n → ℝ)}
    {b : Basis (Fin n) ℤ (IntegralPoint n)} (hb : IsMahlerBasis p b)
    (a : Fin n → ℝ) :
    p (∑ i, a i • integralEmbed (b i)) ≤
      ∑ i, |a i| *
        (mahlerFactor i * successiveMinimum p i) := by
  refine (Erdos3.IntegerBasisReduction.Mahler.seminorm_sum_le
    p a (fun i ↦ integralEmbed (b i))).trans ?_
  exact Finset.sum_le_sum fun i _ ↦
    mul_le_mul_of_nonneg_left (hb i) (abs_nonneg _)

end Erdos3.IntegerBasisReduction.Mahler

end

end OAI
