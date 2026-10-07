-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
import Mathlib
import Mathlib.LinearAlgebra.FreeModule.PID
import OAI.Compat.Core

namespace OAI


namespace Erdos3.BohrLattice.Primitive

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

def IsPrimitive (z : ι → ℤ) : Prop :=
  ∃ u : ι → ℤ, ∑ i, u i * z i = 1

theorem IsPrimitive.ne_zero {z : ι → ℤ} (hz : IsPrimitive z) : z ≠ 0 := by
  rintro rfl
  simp [IsPrimitive] at hz

def content (z : ι → ℤ) : ℤ := Finset.univ.gcd z

theorem content_dvd (z : ι → ℤ) (i : ι) : content z ∣ z i := by
  exact Finset.gcd_dvd (Finset.mem_univ i)

theorem content_ne_zero {z : ι → ℤ} (hz : z ≠ 0) : content z ≠ 0 := by
  rw [content, Finset.gcd_ne_zero_iff]
  simpa [funext_iff] using hz

def divideContent (z : ι → ℤ) : ι → ℤ := fun i => z i / content z

theorem content_mul_divideContent (z : ι → ℤ) (i : ι) :
    content z * divideContent z i = z i := by
  rw [mul_comm]
  exact Int.ediv_mul_cancel (content_dvd z i)

omit [Fintype ι] in
theorem exists_bezout_finset (s : Finset ι) (z : ι → ℤ) :
    ∃ u : ι → ℤ, ∑ i ∈ s, u i * z i = s.gcd z := by
  classical
  induction s using Finset.induction with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨u, hu⟩ := ih
      let A : ℤ := Int.gcdA (z a) (s.gcd z)
      let B : ℤ := Int.gcdB (z a) (s.gcd z)
      refine ⟨fun i => if i = a then A else B * u i, ?_⟩
      rw [Finset.sum_insert ha, Finset.gcd_insert]
      simp only [ite_eq_left]
      have hsum :
          (∑ i ∈ s, (if i = a then A else B * u i) * z i) =
            B * s.gcd z := by
        calc
          (∑ i ∈ s, (if i = a then A else B * u i) * z i) =
              ∑ i ∈ s, B * (u i * z i) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [ite_eq_right (by intro hia; subst i; exact ha hi)]
                ring
          _ = B * ∑ i ∈ s, u i * z i := by
                rw [Finset.mul_sum]
          _ = B * s.gcd z := by rw [hu]
      rw [hsum]
      dsimp [A, B]
      rw [mul_comm B, mul_comm (Int.gcdA (z a) (s.gcd z))]
      exact (Int.gcd_eq_gcd_ab (z a) (s.gcd z)).symm

theorem isPrimitive_of_content_eq_one {z : ι → ℤ} (hz : content z = 1) :
    IsPrimitive z := by
  obtain ⟨u, hu⟩ := exists_bezout_finset Finset.univ z
  have hu' : ∑ i, u i * z i = content z := by
    simpa [content] using hu
  exact ⟨u, hu'.trans hz⟩

theorem divideContent_primitive {z : ι → ℤ} (hz : z ≠ 0) :
    IsPrimitive (divideContent z) := by
  apply isPrimitive_of_content_eq_one
  rw [content]
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    push Not at h
    exact hz (funext h)
  exact Finset.gcd_div_eq_one (Finset.mem_univ i) hi

theorem divideContent_ne_zero {z : ι → ℤ} (hz : z ≠ 0) :
    divideContent z ≠ 0 := (divideContent_primitive hz).ne_zero

end Erdos3.BohrLattice.Primitive


namespace Erdos3.BohrLattice.PrimitiveExtension

open scoped BigOperators
open Module

noncomputable section

def dotLinear {n : ℕ} (u : Fin n → ℤ) : (Fin n → ℤ) →ₗ[ℤ] ℤ where
  toFun z := ∑ i, u i * z i
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [smul_eq_mul, Pi.smul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [mul_left_comm]

@[simp] theorem dotLinear_apply {n : ℕ} (u z : Fin n → ℤ) :
    dotLinear u z = ∑ i, u i * z i := rfl

theorem isPrimitive_of_minimal_gauge {n : ℕ} (z : Fin n → ℤ)
    (hz : z ≠ 0) (μ : (Fin n → ℤ) → ℝ)
    (hμpos : ∀ x ≠ 0, 0 < μ x)
    (hμhom : ∀ (c : ℤ), 0 < c → ∀ x, μ (c • x) = (c : ℝ) * μ x)
    (hmin : ∀ x ≠ 0, μ z ≤ μ x) :
    Erdos3.BohrLattice.Primitive.IsPrimitive z := by
  let c : ℤ := Erdos3.BohrLattice.Primitive.content z
  have hc0 : 0 ≤ c := by
    have hn := Finset.normalize_gcd (s := Finset.univ) (f := z)
    have habs : |c| = c := by
      rw [Int.abs_eq_normalize]
      exact hn
    rw [← habs]
    exact abs_nonneg c
  have hcne : c ≠ 0 := Erdos3.BohrLattice.Primitive.content_ne_zero hz
  have hcpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hcne)
  suffices hc : c = 1 by
    apply Erdos3.BohrLattice.Primitive.isPrimitive_of_content_eq_one
    exact hc
  by_contra hc
  have hc2 : (2 : ℤ) ≤ c := by omega
  let z' : Fin n → ℤ := Erdos3.BohrLattice.Primitive.divideContent z
  have hz' : z' ≠ 0 := Erdos3.BohrLattice.Primitive.divideContent_ne_zero hz
  have hz_eq : z = c • z' := by
    funext i
    exact (Erdos3.BohrLattice.Primitive.content_mul_divideContent z i).symm
  have hscale : μ z = (c : ℝ) * μ z' := by
    rw [hz_eq]
    exact hμhom c hcpos z'
  have hle : μ z ≤ μ z' := hmin z' hz'
  have hz'pos : 0 < μ z' := hμpos z' hz'
  have hc2r : (2 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc2
  rw [hscale] at hle
  nlinarith

theorem exists_basis_zero_eq_of_isPrimitive {n : ℕ} (hn : 0 < n)
    (z : Fin n → ℤ) (hz : Erdos3.BohrLattice.Primitive.IsPrimitive z) :
    ∃ b : Basis (Fin n) ℤ (Fin n → ℤ), b ⟨0, hn⟩ = z := by
  obtain ⟨u, hu⟩ := hz
  let f : (Fin n → ℤ) →ₗ[ℤ] ℤ := dotLinear u
  have hfz : f z = 1 := by
    simpa [f, dotLinear] using hu
  let K : Submodule ℤ (Fin n → ℤ) := LinearMap.ker f
  let kb := K.basisOfPid (Pi.basisFun ℤ (Fin n))
  let k : ℕ := kb.1
  let bK : Basis (Fin k) ℤ K := kb.2
  have hli : ∀ (c : ℤ), ∀ x ∈ K, c • z + x = 0 → c = 0 := by
    intro c x hx hzero
    have hx0 : f x = 0 := by
      exact (LinearMap.mem_ker.mp hx)
    have h : f (c • z + x) = f 0 := congr_arg f hzero
    rw [map_add, map_smul, hfz, hx0, map_zero] at h
    simpa using h
  have hsp : ∀ x : Fin n → ℤ, ∃ c : ℤ, x + c • z ∈ K := by
    intro x
    refine ⟨-f x, ?_⟩
    apply LinearMap.mem_ker.mpr
    rw [map_add, map_smul, hfz]
    simp
  let b' : Basis (Fin (k + 1)) ℤ (Fin n → ℤ) :=
    Basis.mkFinCons z bK hli hsp
  have hb'0 : b' 0 = z := by
    simp [b', Basis.coe_mkFinCons]
  have hkn : k + 1 = n := by
    have hc := Fintype.card_congr (b'.indexEquiv (Pi.basisFun ℤ (Fin n)))
    simpa using hc
  let b : Basis (Fin n) ℤ (Fin n → ℤ) := b'.reindex (finCongr hkn)
  refine ⟨b, ?_⟩
  simp only [b, Basis.reindex_apply]
  have hzero : (finCongr hkn).symm ⟨0, hn⟩ = (0 : Fin (k + 1)) := by
    apply Fin.ext
    rfl
  rw [hzero, hb'0]

def zspanCoordEquiv {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (b : Basis (Fin n) ℝ E) :
    Submodule.span ℤ (Set.range b) ≃ₗ[ℤ] (Fin n → ℤ) :=
  (b.restrictScalars ℤ).repr.trans (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n))

def zspanBasis {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (b : Basis (Fin n) ℝ E) :
    Basis (Fin n) ℤ (Submodule.span ℤ (Set.range b)) :=
  b.restrictScalars ℤ

@[simp] theorem zspanBasis_apply_coe {E : Type*} [AddCommGroup E] [Module ℝ E]
    {n : ℕ} (b : Basis (Fin n) ℝ E) (i : Fin n) :
    ((zspanBasis b i : Submodule.span ℤ (Set.range b)) : E) = b i := by
  exact b.restrictScalars_apply ℤ i

@[simp] theorem zspanCoordEquiv_apply {E : Type*} [AddCommGroup E] [Module ℝ E]
    {n : ℕ} (b : Basis (Fin n) ℝ E)
    (x : Submodule.span ℤ (Set.range b)) (i : Fin n) :
    zspanCoordEquiv b x i = (b.restrictScalars ℤ).repr x i := by
  rfl

theorem shortest_zspan_vector_primitive_and_extends
    {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ} (hn : 0 < n)
    (b : Basis (Fin n) ℝ E)
    (v : Submodule.span ℤ (Set.range b)) (hv : v ≠ 0)
    (μ : Submodule.span ℤ (Set.range b) → ℝ)
    (hμpos : ∀ x ≠ 0, 0 < μ x)
    (hμhom : ∀ (c : ℤ), 0 < c → ∀ x, μ (c • x) = (c : ℝ) * μ x)
    (hmin : ∀ x ≠ 0, μ v ≤ μ x) :
    Erdos3.BohrLattice.Primitive.IsPrimitive (zspanCoordEquiv b v) ∧
      ∃ B : Basis (Fin n) ℤ (Submodule.span ℤ (Set.range b)),
        B ⟨0, hn⟩ = v := by
  let e := zspanCoordEquiv b
  let z : Fin n → ℤ := e v
  have hz : z ≠ 0 := by
    intro hz0
    apply hv
    apply e.injective
    simpa [z] using hz0
  let ν : (Fin n → ℤ) → ℝ := fun x => μ (e.symm x)
  have hνpos : ∀ x ≠ 0, 0 < ν x := by
    intro x hx
    apply hμpos
    simpa using e.symm.injective.ne hx
  have hνhom : ∀ (c : ℤ), 0 < c → ∀ x, ν (c • x) = (c : ℝ) * ν x := by
    intro c hc x
    dsimp [ν]
    rw [map_smul]
    exact hμhom c hc (e.symm x)
  have hνmin : ∀ x ≠ 0, ν z ≤ ν x := by
    intro x hx
    dsimp [ν, z]
    rw [e.symm_apply_apply]
    apply hmin
    simpa using e.symm.injective.ne hx
  have hzprim : Erdos3.BohrLattice.Primitive.IsPrimitive z :=
    isPrimitive_of_minimal_gauge z hz ν hνpos hνhom hνmin
  refine ⟨hzprim, ?_⟩
  obtain ⟨B, hB⟩ := exists_basis_zero_eq_of_isPrimitive hn z hzprim
  refine ⟨B.map e.symm, ?_⟩
  rw [Basis.map_apply, hB]
  exact e.symm_apply_apply v

end

end Erdos3.BohrLattice.PrimitiveExtension

end OAI
